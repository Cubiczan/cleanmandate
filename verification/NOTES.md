# cleanmandate — Lean 4 verification notes

Model: `verification/Mandate.lean` (Lean 4.34.1, core library only, compiles
with plain `lean Mandate.lean`, exit 0; one cosmetic `if_pos` deprecation
warning). Axiom audit on headline theorems: at most `propext`, `Quot.sound`
— no `sorry`/`admit`/custom axioms. No source files were modified.

**Correction to the expected shape, from the code:** `cm-core`'s `mandate.rs`
is types-only. There is *no* mandate lifecycle in the data layer — no status
field on `AgentMandate`, no expiry, no revocation, no spend ledger. The
"lifecycle" is the per-call pipeline in `cm-executor` plus the `cm-policy`
and `cm-chp` gates. The model follows that reality.

## Theorem → source mapping

### §1 Policy — `MandatePolicy::evaluate`, crates/cm-policy/src/lib.rs ll. 67–119

| Theorem | Claim | Source |
|---|---|---|
| `policyAllowed` (def) | The six checks in code order; `allowed ⟺ violations.is_empty()` | ll. 67–119 |
| `policyAllowed_caps` | allowed ⇒ amount ≤ max_single_transfer ∧ amount ≤ mandate daily_cap | ll. 71–83 |
| `policyAllowed_lists` | allowed ⇒ asset ∈ allowed_assets ∧ chain ∈ allowed_chains | ll. 85–93 |
| `policyAllowed_recipient` | allowed ∧ allowlist ≠ [] ⇒ recipient ∈ allowlist | ll. 95–104 |
| `recipient_irrelevant_of_empty_allowlist` | allowlist = [] ⇒ recipient can be swapped freely | default `vec![]`, l. 26; guard l. 95 |
| `issuedAt_irrelevant_policy` | `issued_at` does not affect the decision | field def only, cm-core/src/mandate.rs ll. 41–54 |
| `beneficiaryWallet_irrelevant_policy` | travel-rule beneficiary wallet does not affect the decision | mandate.rs l. 23; never compared anywhere |
| `daily_caps_not_cumulative` ⚠ | Same mandate passes repeatedly; 2 reps break its own daily cap, 9 reps break `max_daily_agent_spend_usd` (25 000) | `max_daily_agent_spend_usd` defined l. 10, defaulted l. 22, **never read in `evaluate`** |
| `negative_amount_allowed` ⚠ | amount = −500 is `allowed` | parse `unwrap_or(0.0)` l. 69; no positivity check |
| `zero_amount_allowed` ⚠ | amount = 0 (the unparseable-string case) is `allowed` | l. 69 |
| `arbitrary_recipient_allowed_default` ⚠ | default policy allows recipient `"0xattacker"` | ll. 95–104 + default l. 26 |

### §2 CHP gate — crates/cm-chp/src/lib.rs

| Theorem | Claim | Source |
|---|---|---|
| `chpEvaluate_policy_fail` | policy_passed = false ⇒ error (no decision) | ll. 64–68 |
| `chpBranch_middle`, `chpBranch_human` | Branch characterisations (factored form) | ll. 75–95 |
| `middle_band_auto_locked` ⚠ | auto_below < amount < human_threshold ⇒ allowed ∧ Locked ∧ approvals = quorum — with **no approval input to the function** | fall-through branch ll. 88–95; defaults ll. 47–55 |
| `at_human_threshold` | amount ≥ human_threshold ⇒ Open ∧ ¬allowed ∧ requires_human (`>=` boundary) | l. 72 |
| `at_auto_boundary` | amount ≤ auto_below (and < human threshold) ⇒ auto-Locked (`<=` boundary) | l. 73 |
| `locked_approvals_fabricated` ⚠ | every Locked outcome of `evaluate` has approvals = quorum_required **by construction** | ll. 76, 91: `approvals` is *assigned* `quorum_required` |
| `approve_rejected_terminal` | `principal_approve` on Rejected is a no-op denial | ll. 111–117 |
| `approve_twice_meets_quorum_two` ⚠ | two `principal_approve` calls satisfy quorum 2 — the function takes **no identity argument**, so caller distinctness is inexpressible | signature l. 110; `saturating_add` l. 118 |
| `approve_resurrects_released` ⚠ | `principal_approve` flips Released → Locked (quorum 1) | only Rejected is guarded, l. 111 |
| `approve_on_locked_stays_allowed` ⚠ | approving a Locked lock succeeds again and increments to 2 | ll. 118–126 |
| `approve_quorum_zero` ⚠ | quorum_required = 0 ⇒ one call locks an unapproved open lock | ll. 118–121 |

### §3 Executor pipeline — `MandateExecutor::pay`, crates/cm-executor/src/lib.rs ll. 93–262

| Theorem | Claim | Source |
|---|---|---|
| `payOutcome` (def) | A-Pass → policy → CCP → CHP → ChpReview / dry-run Completed / transfer Completed-or-Failed | ll. 104–262 |
| `completed_gates` | Completed ⇒ A-Pass ∧ policy ∧ CCP ∧ CHP-allowed all passed | gate order ll. 104–158 |
| `chp_review_of_human_band` | human band (earlier gates green) ⇒ `ChpReview` status | ll. 158–181 |
| `dry_run_sample` ⚠ | dry-run returns `Completed` with transfer outcome `false` — `Completed` does not imply a payment occurred | ll. 183–209 |
| `pay_repeatable_over_caps` ⚠ | the identical call completes twice; cumulative 2× breaks the mandate daily cap, 9× the policy daily cap — `pay` keeps no state between calls | whole fn; no spend store exists in any crate |
| `negative_amount_completes` ⚠ | amount −500 completes the full pipeline | §1+§2 composition |
| `issuedAt_irrelevant_pay` | pipeline outcome identical for any `issued_at` — no gate reads a clock | no time source in cm-policy/cm-chp/cm-executor |
| `beneficiaryWallet_irrelevant_pay` | pipeline outcome independent of travel-rule beneficiary wallet | never compared to `recipient_wallet` |

### §4 Audit ledger — crates/cm-core/src/audit.rs

| Theorem | Claim | Source |
|---|---|---|
| `recordEvent_isPrefix` | `record` only appends; prior events are a prefix | ll. 55–92, 111–122 |
| `recordEvent_length` | each record adds exactly one event | ll. 111–122 |

## Findings (⚠ = proved counterexample in the model)

1. **There is no cumulative spend tracking anywhere (F1).** The "daily cap"
   in policy is a per-call comparison of one amount against the cap.
   `max_daily_agent_spend_usd` is dead configuration — defined and defaulted
   but never read by `evaluate`. `pay()` is stateless, so the same mandate
   re-pays indefinitely (`pay_repeatable_over_caps`, `daily_caps_not_cumulative`).
2. **The CHP quorum is fabricated by the gate itself (F2).** In both Locked
   branches, `evaluate` *writes* `approvals := quorum_required`. The entire
   middle band ($1,000 < amount < $5,000 at defaults) auto-locks with zero
   human involvement while reporting a satisfied quorum
   (`middle_band_auto_locked`, `locked_approvals_fabricated`).
3. **`principal_approve` is unauthenticated and unreachable (F3).** It takes
   no identity, key, or signature; `ChpLock` has no approver field; and it
   has **zero call sites** — the CLI exposes only Pay/Export/Validate/Status.
   A mandate that lands in `ChpReview` can never be completed by the shipped
   binary. Distinct-approver quorum is unenforceable (`approve_twice_meets_quorum_two`).
4. **`principal_approve` is not terminal-safe (F4).** Only `Rejected` is
   guarded: it resurrects `Released → Locked` and happily re-approves a
   `Locked` lock (`approve_resurrects_released`, `approve_on_locked_stays_allowed`).
5. **No expiry, no revocation (F5).** `issued_at` is never read; no gate
   consults a clock; there is no revoke path in any crate. A mandate is
   valid forever (`issuedAt_irrelevant_pay`).
6. **The mandate itself is unauthenticated input (F6).** It is a plain JSON
   file read by the CLI; no signature covers its fields (principal, agent,
   recipient, amount, cap are all claims). The only identity check in the
   pipeline is the external A-Pass lookup on `principal_wallet`.
7. **Recipient binding is opt-in and off by default (F7).** Empty
   `recipient_allowlist` (the default) disables the check entirely, and the
   Travel Rule `beneficiary_wallet` is never compared to `recipient_wallet`
   (`arbitrary_recipient_allowed_default`, `beneficiaryWallet_irrelevant_pay`).
8. **Amount parsing fails open (F8).** `amount.parse().unwrap_or(0.0)` in
   both gates: a garbage amount string becomes 0 and passes; negative
   amounts pass every check and complete the pipeline
   (`negative_amount_allowed`, `zero_amount_allowed`, `negative_amount_completes`).
9. **Dry-run reports `Completed` (F9)** — indistinguishable in status from
   a real settlement; only `tx_hash: None` tells them apart (`dry_run_sample`).
10. **The CHP gate's policy guard is decorative in the pipeline (F10).**
    The executor calls `chp.evaluate(mandate, true)` with a hardcoded
    `policy_passed = true` (cm-executor l. 139). Safe today only because
    policy was checked immediately above.
11. **`MandateStatus` is mostly fiction (F11).** Of its 9 variants, only
    `ChpReview`, `Completed`, `Failed` are ever constructed (cm-executor
    ll. 175, 204, 255–257). Draft/PolicyCheck/CcpPending/AwaitingPrincipal/
    Executing/Rejected have no producers; no mandate object ever transitions.
12. **The audit ledger has no tamper evidence (F12).** Events carry a
    per-event content hash but **no previous-hash link**; the HMAC signature
    is `Option` (absent when `CLEANVERSE…`/signing key is unset); `read_all`
    (ll. 94–109) parses without recomputing hashes or checking signatures,
    and no verify function exists in the workspace. Deleting or reordering
    lines is undetectable. (Contrast the linked-chain pattern used by the
    CHP-family ledgers elsewhere in the triage set.)
13. **quorum_required = 0 degenerates everything (F13)** — `evaluate`
    reports a 0-approval quorum as satisfied and one approve call locks
    (`approve_quorum_zero`). No config validation rejects it.

## Modelling choices & limits

- Money: Rust `f64` (parsed from `String`) → model `Int` (whole dollars).
  Parse failure is the amount = 0 case (proved separately). Float rounding
  and NaN behaviour are abstracted away — NaN amounts would make every Rust
  comparison false and pass the caps too, which only strengthens F8.
- `eq_ignore_ascii_case` → model assumes pre-lowercased strings.
- u8 `saturating_add` on approvals → model `Nat` (differs only above 255).
- A-Pass / CCP / A-Token are abstract booleans, exactly as `pay()` consumes
  them; their internal correctness (Cleanverse API) is out of scope.
- Ids, reason strings, and memo/travel-rule fields no gate reads are dropped
  from the model — except `beneficiaryWallet` and `issuedAt`, which are kept
  precisely to prove they are unread.
- The audit section models only the append structure: there is no chain or
  verify predicate in the code to model (F12).
