/-
  CleanMandate — Lean 4 verification model
  =========================================
  Models the spending-mandate pipeline of the Rust workspace in
  ~/workspace/cubiczan-repos/cleanmandate:

    * `cm-policy`  — `MandatePolicy::evaluate`      (crates/cm-policy/src/lib.rs)
    * `cm-chp`     — `ChpGate::evaluate` / `principal_approve`
                                                  (crates/cm-chp/src/lib.rs)
    * `cm-executor`— `MandateExecutor::pay`        (crates/cm-executor/src/lib.rs)
    * `cm-core`    — `AgentMandate`, `AuditLedger` (crates/cm-core/src/*.rs)

  Core library only. Compile with:  lean Mandate.lean
  No `sorry` / `admit` / custom axioms.

  Modelling conventions (see NOTES.md for the full list):
  * Money: Rust uses `f64` parsed from a `String` (`parse().unwrap_or(0.0)`).
    The model works over `Int` (whole dollars) and takes the mandate's
    amount as already parsed; parse failure / garbage is the `0` case,
    which is modelled explicitly. Float rounding is abstracted away.
  * String comparisons in Rust are `eq_ignore_ascii_case`; the model
    assumes all strings are pre-lowercased, so plain equality/membership
    is the case-insensitive comparison on normalised values.
  * External services (A-Pass, CCP, A-Token transfer) are abstract
    boolean outcomes, exactly as `pay()` consumes them.
-/

namespace CleanMandate

/-! ## 1. Mandates and policy (cm-core mandate.rs, cm-policy lib.rs) -/

/-- An agent mandate, restricted to the fields any gate actually reads
    (plus two fields no gate reads, kept to *prove* they are unread).
    Field sources: `AgentMandate` (mandate.rs ll. 41–54) and
    `TravelRulePayload` (ll. 19–27). -/
structure Mandate where
  amount : Int             -- mandate.rs: `amount: String`, parsed in the gates
  asset : String           -- lowercased (Rust compares case-insensitively)
  chain : String
  recipient : String       -- `recipient_wallet`
  dailyCap : Int           -- `daily_cap_usd`
  originatorName : String  -- travel_rule.originator_name
  beneficiaryName : String -- travel_rule.beneficiary_name
  beneficiaryWallet : String -- travel_rule.beneficiary_wallet — never compared to `recipient`
  issuedAt : String        -- `issued_at` — never read by any gate
  deriving DecidableEq, Repr

/-- `MandatePolicy` (cm-policy/src/lib.rs ll. 7–15). -/
structure Policy where
  maxSingle : Int        -- max_single_transfer_usd
  maxDailyAgent : Int    -- max_daily_agent_spend_usd — see `maxDailyAgent_unused`
  allowedAssets : List String
  allowedChains : List String
  recipientAllowlist : List String
  requireTravelRule : Bool
  deriving Repr

/-- `MandatePolicy::default` (cm-policy/src/lib.rs ll. 19–30). -/
def defaultPolicy : Policy where
  maxSingle := 10000
  maxDailyAgent := 25000
  allowedAssets := ["a-usdc", "usdc"]
  allowedChains := ["monad", "monad-testnet"]
  recipientAllowlist := []
  requireTravelRule := true

/-- `MandatePolicy::evaluate` (cm-policy/src/lib.rs ll. 67–119), as the
    boolean `allowed = violations.is_empty()`. The six checks, in code
    order: single-transfer cap, per-mandate daily cap (a *single* amount
    compared against the cap — no running total exists), asset allowlist,
    chain allowlist, recipient allowlist (only if non-empty), travel-rule
    names (only if required). -/
def policyAllowed (p : Policy) (m : Mandate) : Bool :=
  (m.amount ≤ p.maxSingle) &&
  (m.amount ≤ m.dailyCap) &&
  p.allowedAssets.contains m.asset &&
  p.allowedChains.contains m.chain &&
  (p.recipientAllowlist.isEmpty || p.recipientAllowlist.contains m.recipient) &&
  (!p.requireTravelRule || (m.originatorName != "" && m.beneficiaryName != ""))

/-! ### What the policy does guarantee (per single mandate) -/

/-- An allowed mandate respects both caps — for that one transfer. -/
theorem policyAllowed_caps {p : Policy} {m : Mandate}
    (h : policyAllowed p m = true) :
    m.amount ≤ p.maxSingle ∧ m.amount ≤ m.dailyCap := by
  unfold policyAllowed at h
  have h1 := Bool.and_eq_true_iff.mp h
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have h3 := Bool.and_eq_true_iff.mp h2.1
  have h4 := Bool.and_eq_true_iff.mp h3.1
  have h5 := Bool.and_eq_true_iff.mp h4.1
  exact ⟨of_decide_eq_true h5.1, of_decide_eq_true h5.2⟩

/-- An allowed mandate's asset and chain are on the allowlists. -/
theorem policyAllowed_lists {p : Policy} {m : Mandate}
    (h : policyAllowed p m = true) :
    m.asset ∈ p.allowedAssets ∧ m.chain ∈ p.allowedChains := by
  unfold policyAllowed at h
  have h1 := Bool.and_eq_true_iff.mp h
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have h3 := Bool.and_eq_true_iff.mp h2.1
  have h4 := Bool.and_eq_true_iff.mp h3.1
  exact ⟨List.contains_iff_mem.mp h4.2, List.contains_iff_mem.mp h3.2⟩

/-- The recipient is checked only when the allowlist is non-empty. -/
theorem policyAllowed_recipient {p : Policy} {m : Mandate}
    (h : policyAllowed p m = true) (hne : p.recipientAllowlist ≠ []) :
    m.recipient ∈ p.recipientAllowlist := by
  unfold policyAllowed at h
  have h1 := Bool.and_eq_true_iff.mp h
  have h2 := Bool.and_eq_true_iff.mp h1.1
  rcases Bool.or_eq_true_iff.mp h2.2 with hempty | hmem
  · cases hl : p.recipientAllowlist with
    | nil => exact absurd hl hne
    | cons x xs => rw [hl] at hempty; simp at hempty
  · exact List.contains_iff_mem.mp hmem

/-- With an empty recipient allowlist (the shipped default), the
    recipient is *irrelevant* to the policy decision: swapping in any
    other recipient preserves allowedness. (`recipient_allowlist: vec![]`
    in `MandatePolicy::default`, lib.rs l. 26; check at ll. 95–104 is
    guarded by `!is_empty()`.) -/
theorem recipient_irrelevant_of_empty_allowlist {p : Policy}
    (hempty : p.recipientAllowlist = []) (m : Mandate) (r : String) :
    policyAllowed p { m with recipient := r } = policyAllowed p m := by
  unfold policyAllowed
  rw [hempty]
  simp

/-- `issued_at` is never read: two mandates differing only in
    `issued_at` get identical policy outcomes. There is no expiry
    anywhere in the workspace (grep: `issued_at` occurs only at its
    definition, mandate.rs l. 52). -/
theorem issuedAt_irrelevant_policy (p : Policy) (m : Mandate) (s : String) :
    policyAllowed p { m with issuedAt := s } = policyAllowed p m := rfl

/-- The travel-rule beneficiary *wallet* is never compared to the
    recipient wallet: it is not read by the policy at all (only the
    beneficiary *name* is checked for non-emptiness). A mandate whose
    travel-rule beneficiary is a different wallet than the actual
    recipient passes identically. -/
theorem beneficiaryWallet_irrelevant_policy (p : Policy) (m : Mandate) (w : String) :
    policyAllowed p { m with beneficiaryWallet := w } = policyAllowed p m := rfl

/-! ### Counterexamples: what the policy does not guarantee -/

/-- A concrete, otherwise-compliant mandate used in the examples.
    Mirrors examples/mandates/vendor-payment.json, scaled to $3,000 —
    deliberately in the CHP "middle band" (see §2). -/
def sampleMandate : Mandate where
  amount := 3000
  asset := "usdc"
  chain := "monad"
  recipient := "0xvendor"
  dailyCap := 3000
  originatorName := "Acme Corp Treasury"
  beneficiaryName := "CloudHost SaaS Ltd"
  beneficiaryWallet := "0xvendor"
  issuedAt := "2026-06-07T12:00:00Z"

/-- `max_daily_agent_spend_usd` is dead configuration: it is defined
    (lib.rs l. 10) and defaulted to 25,000 (l. 22) but `evaluate` never
    consults it, and `evaluate` is a pure per-mandate predicate with no
    spend state. The same mandate therefore passes every gate on every
    repetition, and cumulative spend is unbounded: here 2 repetitions
    already break the mandate's own daily cap (2 × 3000 > 3000) and 9
    repetitions break the policy's daily agent cap (9 × 3000 > 25000) —
    while each individual spend is fully "allowed". -/
theorem daily_caps_not_cumulative :
    policyAllowed defaultPolicy sampleMandate = true ∧
    2 * sampleMandate.amount > sampleMandate.dailyCap ∧
    9 * sampleMandate.amount > defaultPolicy.maxDailyAgent := by
  refine ⟨by decide, by decide, by decide⟩

/-- Unparseable amounts become `0.0` (`parse().unwrap_or(0.0)`,
    cm-policy l. 69, cm-chp l. 71) and negative amounts are never
    rejected (no positivity check exists). A mandate with amount −500
    passes the policy outright. -/
theorem negative_amount_allowed :
    policyAllowed defaultPolicy { sampleMandate with amount := -500 } = true := by
  decide

/-- …and so does the garbage-amount case, amount = 0. -/
theorem zero_amount_allowed :
    policyAllowed defaultPolicy { sampleMandate with amount := 0 } = true := by
  decide

/-- Under the default policy (empty recipient allowlist) literally any
    recipient passes — including one that appears nowhere in the
    mandate's travel-rule payload. -/
theorem arbitrary_recipient_allowed_default :
    policyAllowed defaultPolicy { sampleMandate with recipient := "0xattacker" } = true := by
  decide

/-! ## 2. The CHP gate (cm-chp/src/lib.rs)

`ChpGate::evaluate` (ll. 63–103) rejects when `policy_passed` is false;
otherwise it *computes* a lock. Note what it never does: it never
receives, requests, or counts an actual approval. In both `Locked`
branches it writes `approvals := quorum_required` itself (ll. 76, 91). -/

inductive ChpState where
  | open | locked | released | rejected
  deriving DecidableEq, Repr

/-- `ChpConfig` (cm-chp/src/lib.rs ll. 41–45). -/
structure ChpConfig where
  quorum : Nat          -- quorum_required
  humanThreshold : Int  -- human_threshold_usd
  autoBelow : Int       -- auto_approve_below_usd
  deriving Repr

/-- `ChpConfig::default` (ll. 47–55): quorum 1, human ≥ 5000, auto ≤ 1000. -/
def defaultChp : ChpConfig where
  quorum := 1
  humanThreshold := 5000
  autoBelow := 1000

/-- `ChpLock` (ll. 18–25), minus the ids/reason (never inspected). -/
structure ChpLock where
  state : ChpState
  quorumRequired : Nat
  approvals : Nat
  deriving DecidableEq, Repr

/-- `ChpDecision` (ll. 27–31). -/
structure ChpDecision where
  allowed : Bool
  requiresHuman : Bool
  lock : ChpLock
  deriving DecidableEq, Repr

private theorem decide_false_of_not {p : Prop} [Decidable p] (h : ¬ p) :
    decide p = false :=
  Bool.eq_false_of_ne_true (fun ht => h (of_decide_eq_true ht))

/-- The branch structure of `ChpGate::evaluate`, factored on the two
    booleans the code computes (ll. 71–95):
    `requires_human = amount >= human_threshold`,
    `auto = amount <= auto_approve_below`. -/
def chpBranch (cfg : ChpConfig) (requiresHuman auto : Bool) : ChpDecision :=
  if auto && !requiresHuman then
    { allowed := true, requiresHuman := requiresHuman,
      lock := ⟨.locked, cfg.quorum, cfg.quorum⟩ }
  else if requiresHuman then
    { allowed := false, requiresHuman := requiresHuman,
      lock := ⟨.open, cfg.quorum, 0⟩ }
  else
    { allowed := true, requiresHuman := requiresHuman,
      lock := ⟨.locked, cfg.quorum, cfg.quorum⟩ }

/-- `ChpGate::evaluate` under `policy_passed = true`. -/
def chpCore (cfg : ChpConfig) (amount : Int) : ChpDecision :=
  chpBranch cfg (decide (amount ≥ cfg.humanThreshold))
    (decide (amount ≤ cfg.autoBelow))

/-- `ChpGate::evaluate` (ll. 63–68): a failed policy is an error, not a
    decision. (The executor only ever passes `true` — lib.rs l. 139 of
    cm-executor — after checking policy itself.) -/
def chpEvaluate (cfg : ChpConfig) (amount : Int) (policyPassed : Bool) :
    Option ChpDecision :=
  if policyPassed then some (chpCore cfg amount) else none

theorem chpEvaluate_policy_fail (cfg : ChpConfig) (amt : Int) :
    chpEvaluate cfg amt false = none := rfl

/-- Middle band, factored form: neither auto nor human-required, yet the
    lock comes out `Locked` with a full set of "approvals". -/
theorem chpBranch_middle (cfg : ChpConfig) :
    chpBranch cfg false false =
      { allowed := true, requiresHuman := false,
        lock := ⟨.locked, cfg.quorum, cfg.quorum⟩ } := rfl

/-- Human band, factored form: `Open`, no approvals, not allowed —
    regardless of the auto flag. -/
theorem chpBranch_human (cfg : ChpConfig) (auto : Bool) :
    (chpBranch cfg true auto).allowed = false ∧
    (chpBranch cfg true auto).lock.state = .open ∧
    (chpBranch cfg true auto).lock.approvals = 0 := by
  cases auto <;> exact ⟨rfl, rfl, rfl⟩

/-- **Middle-band auto-lock.** With `auto_approve_below < amount <
    human_threshold`, `evaluate` returns an allowed, Locked decision
    whose approval count equals the quorum — although the function has
    no approval input at all. Under the default config this is every
    amount in (1000, 5000). The "quorum" is fabricated by the gate
    itself (ll. 88–95, the fall-through branch). -/
theorem middle_band_auto_locked {cfg : ChpConfig} {amt : Int}
    (h1 : cfg.autoBelow < amt) (h2 : amt < cfg.humanThreshold) :
    (chpCore cfg amt).allowed = true ∧
    (chpCore cfg amt).lock.state = .locked ∧
    (chpCore cfg amt).lock.approvals = cfg.quorum := by
  unfold chpCore
  have hr : (decide (amt ≥ cfg.humanThreshold)) = false :=
    decide_false_of_not (by omega)
  have ha : (decide (amt ≤ cfg.autoBelow)) = false :=
    decide_false_of_not (by omega)
  rw [hr, ha]
  exact ⟨rfl, rfl, rfl⟩

/-- At exactly the human threshold the gate does require a human
    (the comparison is `>=`, lib.rs l. 72). -/
theorem at_human_threshold {cfg : ChpConfig} {amt : Int}
    (h : amt ≥ cfg.humanThreshold) :
    (chpCore cfg amt).allowed = false ∧
    (chpCore cfg amt).lock.state = .open ∧
    (chpCore cfg amt).requiresHuman = true := by
  unfold chpCore
  have hr : (decide (amt ≥ cfg.humanThreshold)) = true := decide_eq_true h
  rw [hr]
  cases ha : (decide (amt ≤ cfg.autoBelow)) <;> exact ⟨rfl, rfl, rfl⟩

/-- At exactly the auto-approve bound (and below the human threshold)
    the gate auto-locks (the comparison is `<=`, lib.rs l. 73). -/
theorem at_auto_boundary {cfg : ChpConfig} {amt : Int}
    (h1 : amt ≤ cfg.autoBelow) (h2 : amt < cfg.humanThreshold) :
    (chpCore cfg amt).allowed = true ∧
    (chpCore cfg amt).lock.state = .locked := by
  unfold chpCore
  have hr : (decide (amt ≥ cfg.humanThreshold)) = false :=
    decide_false_of_not (by omega)
  have ha : (decide (amt ≤ cfg.autoBelow)) = true := decide_eq_true h1
  rw [hr, ha]
  exact ⟨rfl, rfl⟩

/-- Everywhere, a Locked outcome of `evaluate` carries
    `approvals = quorum_required` by construction — the count is written
    by the gate, never earned. -/
theorem locked_approvals_fabricated {cfg : ChpConfig} {amt : Int}
    (h : (chpCore cfg amt).lock.state = .locked) :
    (chpCore cfg amt).lock.approvals = cfg.quorum ∧
    (chpCore cfg amt).allowed = true := by
  unfold chpCore at h ⊢
  cases hr : (decide (amt ≥ cfg.humanThreshold)) with
  | true =>
      rw [hr] at h
      have hst := (chpBranch_human cfg (decide (amt ≤ cfg.autoBelow))).2.1
      rw [hst] at h
      simp at h
  | false =>
      cases ha : (decide (amt ≤ cfg.autoBelow)) <;> exact ⟨rfl, rfl⟩

/-! ### `principal_approve` (cm-chp/src/lib.rs ll. 110–127)

The only approval entry point. It takes **no identity argument** — no
principal key, no signature, not even a name — so the model needs no
caller parameter either. Its only state guard is `Rejected`. -/

/-- `ChpGate::principal_approve`, faithful to ll. 110–127 (u8 saturation
    abstracted to Nat; the reason string is never inspected). -/
def principalApprove (lock : ChpLock) : ChpDecision :=
  if lock.state = .rejected then
    { allowed := false, requiresHuman := true, lock }
  else
    let approvals' := lock.approvals + 1
    let state' := if decide (approvals' ≥ lock.quorumRequired) then .locked
      else lock.state
    { allowed := decide (state' = .locked),
      requiresHuman := !(decide (state' = .locked)),
      lock := ⟨state', lock.quorumRequired, approvals'⟩ }

theorem approve_rejected_terminal (lock : ChpLock)
    (h : lock.state = .rejected) :
    (principalApprove lock).allowed = false ∧
    (principalApprove lock).lock = lock := by
  unfold principalApprove
  rw [if_pos h]
  exact ⟨rfl, rfl⟩

/-- Two calls to `principal_approve` satisfy a quorum of 2. Since the
    function has no caller identity, these can be the same caller twice
    — nothing in the code can tell the difference (there is not even an
    approver field on `ChpLock`). -/
theorem approve_twice_meets_quorum_two :
    (principalApprove (principalApprove ⟨.open, 2, 0⟩).lock).allowed = true ∧
    (principalApprove (principalApprove ⟨.open, 2, 0⟩).lock).lock.state
      = .locked := by
  decide

/-- Resurrection: approving a `Released` lock flips it back to `Locked`
    (with the default quorum of 1) — `principal_approve` guards only
    `Rejected`, so terminal states other than Rejected are not
    absorbing. -/
theorem approve_resurrects_released :
    (principalApprove ⟨.released, 1, 0⟩).lock.state = .locked ∧
    (principalApprove ⟨.released, 1, 0⟩).allowed = true := by
  decide

/-- Approving an already-`Locked` lock also "succeeds" and keeps
    incrementing the count — there is no already-decided error. -/
theorem approve_on_locked_stays_allowed :
    (principalApprove ⟨.locked, 1, 1⟩).allowed = true ∧
    (principalApprove ⟨.locked, 1, 1⟩).lock.approvals = 2 := by
  decide

/-- With `quorum_required = 0`, a single approval call locks an open
    lock whose approval count was 0 — and in `evaluate` the middle/auto
    branches report `approvals = 0` as a satisfied quorum
    (`locked_approvals_fabricated` with `cfg.quorum = 0`). -/
theorem approve_quorum_zero :
    (principalApprove ⟨.open, 0, 0⟩).lock.state = .locked := by
  decide

/-! ## 3. The executor pipeline (cm-executor/src/lib.rs)

`MandateExecutor::pay` (ll. 93–262) is a *stateless* function of the
mandate and the external services' answers: it keeps no per-mandate
state, no spend totals, and never reads a clock. Statuses it can
return: `ChpReview`, `Completed`, `Failed` (plus `Err(Blocked)`).
Five of the nine `MandateStatus` variants (Draft, PolicyCheck,
CcpPending, AwaitingPrincipal, Executing, Rejected — six, in fact) are
never constructed anywhere in the workspace. -/

/-- The statuses `pay` can produce (Blocked = the `Err` path). -/
inductive PayStatus where
  | blocked | chpReview | completed | failed
  deriving DecidableEq, Repr

/-- The external services' answers, abstracted to the booleans `pay`
    consumes: A-Pass verified, CCP passed, A-Token transfer success. -/
structure GateOutcomes where
  apass : Bool
  ccp : Bool
  transfer : Bool
  deriving DecidableEq, Repr

/-- `MandateExecutor::pay`, decision structure (ll. 104–262): A-Pass →
    policy → CCP → CHP → (human? return ChpReview) → (dry-run?
    Completed without transferring) → transfer → Completed/Failed. -/
def payOutcome (p : Policy) (cfg : ChpConfig) (m : Mandate)
    (g : GateOutcomes) (dryRun : Bool) : PayStatus :=
  if !g.apass then .blocked
  else if !policyAllowed p m then .blocked
  else if !g.ccp then .blocked
  else
    let d := chpCore cfg m.amount
    if d.requiresHuman && !d.allowed then .chpReview
    else if dryRun then .completed
    else if g.transfer then .completed else .failed

/-- All gates, as one predicate — note every conjunct is a function of
    the single mandate and the services' current answers. Nothing
    accumulates. -/
def gatePasses (p : Policy) (cfg : ChpConfig) (m : Mandate)
    (g : GateOutcomes) : Bool :=
  g.apass && policyAllowed p m && g.ccp && (chpCore cfg m.amount).allowed

/-- A Completed outcome implies every gate passed. -/
theorem completed_gates {p : Policy} {cfg : ChpConfig} {m : Mandate}
    {g : GateOutcomes} {dryRun : Bool}
    (h : payOutcome p cfg m g dryRun = .completed) :
    g.apass = true ∧ policyAllowed p m = true ∧ g.ccp = true ∧
    (chpCore cfg m.amount).allowed = true := by
  unfold payOutcome at h
  by_cases hap : g.apass = true
  · by_cases hpol : policyAllowed p m = true
    · by_cases hccp : g.ccp = true
      · have hd : (chpCore cfg m.amount).allowed = true := by
          cases ha : (chpCore cfg m.amount).allowed with
          | true => rfl
          | false =>
              exfalso
              -- allowed=false only happens in the human branch, where
              -- requiresHuman=true; the outcome would be chpReview.
              have hreq : (chpCore cfg m.amount).requiresHuman = true := by
                unfold chpCore at ha ⊢
                cases hr : (decide (m.amount ≥ cfg.humanThreshold)) with
                | false =>
                    cases ha2 : (decide (m.amount ≤ cfg.autoBelow)) <;>
                      simp [chpBranch, hr, ha2] at ha
                | true => simp [chpBranch]
              simp [hap, hpol, hccp, hreq, ha] at h
        exact ⟨hap, hpol, hccp, hd⟩
      · simp [hap, hpol, hccp] at h
    · simp [hap, hpol] at h
  · simp [hap] at h

/-- In the human band the pipeline stops at `ChpReview` (given the
    earlier gates pass). Note there is no continuation: the CLI has no
    approve command and `principal_approve` has no call sites in the
    workspace, so this outcome is terminal in practice. -/
theorem chp_review_of_human_band {p : Policy} {cfg : ChpConfig}
    {m : Mandate} {g : GateOutcomes} {dryRun : Bool}
    (hband : m.amount ≥ cfg.humanThreshold)
    (hap : g.apass = true) (hpol : policyAllowed p m = true)
    (hccp : g.ccp = true) :
    payOutcome p cfg m g dryRun = .chpReview := by
  have hd := at_human_threshold hband
  simp [payOutcome, hap, hpol, hccp, hd.1, hd.2.2]

/-- A dry run reports `Completed` **without any transfer occurring**:
    in `dry_run_sample` the transfer outcome is `false` and is never
    consulted — the `Completed` status does not imply a payment
    happened (cm-executor ll. 183–209). -/
theorem dry_run_sample :
    payOutcome defaultPolicy defaultChp sampleMandate
      ⟨true, true, false⟩ true = .completed := by
  decide

/-- **Repeatability / no cumulative cap, end to end.** `pay` has no
    memory: the same mandate with the same service answers completes
    again, identically. Two completions move 2 × 3000 = 6000 against a
    mandate daily cap of 3000; nine move 27000 against the policy's
    (never-consulted) daily agent cap of 25000. -/
theorem pay_repeatable_over_caps :
    payOutcome defaultPolicy defaultChp sampleMandate
        ⟨true, true, true⟩ false = .completed ∧
    payOutcome defaultPolicy defaultChp sampleMandate
        ⟨true, true, true⟩ false = .completed ∧
    2 * sampleMandate.amount > sampleMandate.dailyCap ∧
    9 * sampleMandate.amount > defaultPolicy.maxDailyAgent := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- A negative-amount mandate completes the full pipeline (policy and
    CHP both pass it; see `negative_amount_allowed`). Whatever the
    downstream API does with a negative transfer, nothing in this
    workspace stops it. -/
theorem negative_amount_completes :
    payOutcome defaultPolicy defaultChp { sampleMandate with amount := -500 }
      ⟨true, true, true⟩ false = .completed := by
  decide

/-- `issued_at` is irrelevant to the pipeline outcome, for any two
    timestamps — there is no expiry check to model because no code
    reads the field or a clock. -/
theorem issuedAt_irrelevant_pay (p : Policy) (cfg : ChpConfig)
    (m : Mandate) (g : GateOutcomes) (dryRun : Bool) (s : String) :
    payOutcome p cfg { m with issuedAt := s } g dryRun
      = payOutcome p cfg m g dryRun := rfl

/-- Same for the travel-rule beneficiary wallet vs. the recipient:
    the pipeline outcome cannot depend on whether they match. -/
theorem beneficiaryWallet_irrelevant_pay (p : Policy) (cfg : ChpConfig)
    (m : Mandate) (g : GateOutcomes) (dryRun : Bool) (w : String) :
    payOutcome p cfg { m with beneficiaryWallet := w } g dryRun
      = payOutcome p cfg m g dryRun := rfl

/-! ## 4. The audit ledger (cm-core/src/audit.rs)

`AuditLedger::record` (ll. 55–92) appends one JSON line per event.
An event's `content_hash` covers only that event; there is **no
previous-hash field** (contrast the CHP ledger pattern), the signature
is `Option` (absent when no signing key is configured), and `read_all`
(ll. 94–109) parses lines without recomputing any hash or checking any
signature — the workspace contains no verification function for the
ledger at all. The one structural property the code does have: -/

/-- A trace event, restricted to its fields (audit.rs ll. 29–40). Note
    the absence of any link to a predecessor event. -/
structure TraceEvent where
  phase : String
  agent : String
  action : String
  mandateId : Option Nat
  contentHash : String
  signature : Option String
  deriving DecidableEq, Repr

/-- `record` + `append` (ll. 83, 111–122): append-only at the API. -/
def recordEvent (ledger : List TraceEvent) (e : TraceEvent) :
    List TraceEvent :=
  ledger ++ [e]

/-- Appending never rewrites history: the old ledger is a prefix. -/
theorem recordEvent_isPrefix (l : List TraceEvent) (e : TraceEvent) :
    l <+: recordEvent l e :=
  ⟨[e], rfl⟩

/-- Unsigned events are first-class: `record` takes no key parameter
    in its success path — with `signing_key = None` every event is
    recorded with `signature = none`, indistinguishably structured
    from signed ones. Modelled by the fact that `recordEvent` neither
    requires nor produces a signature. (The tamper-evidence gap —
    deletion/reordering of lines is undetectable because events carry
    no chain link and `read_all` verifies nothing — is a code-absence
    finding; see NOTES.md.) -/
theorem recordEvent_length (l : List TraceEvent) (e : TraceEvent) :
    (recordEvent l e).length = l.length + 1 := by
  simp [recordEvent]

end CleanMandate
