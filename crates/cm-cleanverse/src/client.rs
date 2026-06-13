use crate::types::{
    ApassVerification, CcpPreCheckRequest, CcpPreCheckResult, TokenTransferRequest,
    TokenTransferResult,
};
use reqwest::Client;
use resilient_call::{retry, with_timeout, ResilienceError, RetryPolicy};
use serde::{Deserialize, Serialize};
use std::time::Duration;
use thiserror::Error;
use uuid::Uuid;

/// Connect + read timeout for every live Cleanverse call. Without this a hung
/// API would block the payment agent indefinitely. Enforced both on the
/// reqwest client (defense in depth) and via `resilient_call::with_timeout`
/// around each attempt.
const HTTP_TIMEOUT: Duration = Duration::from_secs(30);
/// Total attempts (initial + retries) for transient errors. Backoff schedule
/// and full jitter are owned by `resilient_call::RetryPolicy`.
const MAX_ATTEMPTS: u32 = 3;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CleanverseMode {
    Mock,
    Sandbox,
}

#[derive(Debug, Clone)]
pub struct CleanverseConfig {
    pub mode: CleanverseMode,
    pub api_base: String,
    pub api_key: Option<String>,
}

impl CleanverseConfig {
    pub fn from_env() -> Self {
        let mode = match std::env::var("CLEANVERSE_MODE")
            .unwrap_or_else(|_| "mock".into())
            .to_lowercase()
            .as_str()
        {
            "sandbox" | "live" => CleanverseMode::Sandbox,
            _ => CleanverseMode::Mock,
        };
        Self {
            mode,
            api_base: std::env::var("CLEANVERSE_API_BASE")
                .unwrap_or_else(|_| "https://sandbox.api.cleanverse.com/v3".into()),
            api_key: std::env::var("CLEANVERSE_API_KEY").ok(),
        }
    }
}

#[derive(Debug, Error)]
pub enum CleanverseError {
    #[error("http error: {0}")]
    Http(#[from] reqwest::Error),
    #[error("api error: {0}")]
    Api(String),
    #[error("encode error: {0}")]
    Encode(#[source] serde_json::Error),
}

pub struct CleanverseClient {
    config: CleanverseConfig,
    http: Client,
}

impl CleanverseClient {
    pub fn new(config: CleanverseConfig) -> Self {
        let http = Client::builder()
            .timeout(HTTP_TIMEOUT)
            .connect_timeout(HTTP_TIMEOUT)
            .build()
            .unwrap_or_else(|_| Client::new());
        Self { config, http }
    }

    pub fn mode(&self) -> CleanverseMode {
        self.config.mode
    }

    pub async fn verify_apass(&self, wallet: &str) -> Result<ApassVerification, CleanverseError> {
        if self.config.mode == CleanverseMode::Mock {
            return Ok(ApassVerification {
                wallet: wallet.to_string(),
                verified: wallet.starts_with("0x"),
                identity_id: Some(format!("apass-mock-{}", &wallet[..wallet.len().min(10)])),
                kyc_tier: Some("tier2".into()),
                message: "mock A-Pass verification".into(),
            });
        }

        #[derive(Serialize)]
        struct Req<'a> {
            wallet: &'a str,
        }
        #[derive(Deserialize)]
        struct Resp {
            verified: bool,
            identity_id: Option<String>,
            kyc_tier: Option<String>,
            message: Option<String>,
        }

        let resp: Resp = self
            .post("/apass/verify", &Req { wallet }, None)
            .await?;
        Ok(ApassVerification {
            wallet: wallet.to_string(),
            verified: resp.verified,
            identity_id: resp.identity_id,
            kyc_tier: resp.kyc_tier,
            message: resp.message.unwrap_or_else(|| "A-Pass verified".into()),
        })
    }

    pub async fn ccp_pre_check(
        &self,
        req: &CcpPreCheckRequest,
    ) -> Result<CcpPreCheckResult, CleanverseError> {
        if self.config.mode == CleanverseMode::Mock {
            let blocked = req.to_wallet.eq_ignore_ascii_case("0xdead000000000000000000000000000000000001");
            return Ok(CcpPreCheckResult {
                passed: !blocked,
                ccp_reference: format!("ccp-mock-{}", Uuid::new_v4()),
                travel_rule_status: if blocked {
                    "blocked".into()
                } else {
                    "cleared".into()
                },
                blocked_reason: if blocked {
                    Some("sanctions match (mock)".into())
                } else {
                    None
                },
            });
        }

        let resp: CcpPreCheckResult = self.post("/ccp/pre-check", req, None).await?;
        Ok(resp)
    }

    pub async fn transfer_a_token(
        &self,
        req: &TokenTransferRequest,
    ) -> Result<TokenTransferResult, CleanverseError> {
        if self.config.mode == CleanverseMode::Mock {
            return Ok(TokenTransferResult {
                success: true,
                tx_hash: Some(format!("0xmock{:064x}", Uuid::new_v4().as_u128())),
                a_token_reference: format!("atoken-mock-{}", Uuid::new_v4()),
                message: "mock A-Token transfer on Monad testnet".into(),
            });
        }

        // Deterministic idempotency key derived from the mandate id so that a
        // retry after a network timeout cannot trigger a second on-chain
        // transfer: the Cleanverse API dedupes on this key.
        let idempotency_key = format!("mandate-{}", req.mandate_id);
        let resp: TokenTransferResult = self
            .post("/atoken/transfer", req, Some(&idempotency_key))
            .await?;
        Ok(resp)
    }

    async fn post<T: Serialize, R: for<'de> Deserialize<'de>>(
        &self,
        path: &str,
        body: &T,
        idempotency_key: Option<&str>,
    ) -> Result<R, CleanverseError> {
        let url = format!("{}{}", self.config.api_base.trim_end_matches('/'), path);
        let body_json = serde_json::to_value(body).map_err(CleanverseError::Encode)?;

        // Exponential backoff + full jitter and the retry/timeout wrappers are
        // provided by `resilient-call`; the closure is re-run per attempt so
        // each retry rebuilds a fresh request. The Idempotency-Key header makes
        // those retries safe even if a prior attempt reached the server before
        // the connection failed/timed out.
        let policy = RetryPolicy::with_max_attempts(MAX_ATTEMPTS)
            .base_delay(Duration::from_millis(200))
            .max_delay(Duration::from_secs(4));

        let attempt = || async {
            let mut req = self.http.post(&url).json(&body_json);
            if let Some(key) = &self.config.api_key {
                req = req.header("Authorization", format!("Bearer {key}"));
            }
            if let Some(idem) = idempotency_key {
                req = req.header("Idempotency-Key", idem);
            }

            // Bound each individual attempt with the typed timeout wrapper in
            // addition to the reqwest client-level timeout.
            with_timeout(
                async {
                    let resp = req.send().await?;
                    let status = resp.status();
                    if status.is_success() {
                        return resp.json::<R>().await.map_err(CleanverseError::Http);
                    }
                    let text = resp.text().await.unwrap_or_default();
                    Err(CleanverseError::Api(format!("{status}: {text}")))
                },
                HTTP_TIMEOUT,
            )
            .await
            // Flatten the timeout wrapper's error into our domain error so the
            // classifier sees a single `CleanverseError`.
            .map_err(|e| match e {
                ResilienceError::Timeout(d) => {
                    CleanverseError::Api(format!("attempt timed out after {d:?}"))
                }
                ResilienceError::Terminal(inner) | ResilienceError::Exhausted { source: inner, .. } => inner,
            })
        };

        retry(attempt, &policy, Self::is_retryable)
            .await
            .map_err(|e| match e {
                ResilienceError::Timeout(d) => {
                    CleanverseError::Api(format!("timed out after {d:?}"))
                }
                ResilienceError::Terminal(inner) | ResilienceError::Exhausted { source: inner, .. } => inner,
            })
    }

    /// Retry transient server-side failures (5xx / 429) and network-level
    /// errors (timeout, connect, send); surface 4xx business errors and
    /// decode failures immediately.
    fn is_retryable(err: &CleanverseError) -> bool {
        match err {
            CleanverseError::Http(e) => e.is_timeout() || e.is_connect() || e.is_request(),
            CleanverseError::Api(msg) => {
                msg.starts_with("attempt timed out")
                    || msg.starts_with("5")
                    || msg.starts_with("429")
            }
            CleanverseError::Encode(_) => false,
        }
    }
}
