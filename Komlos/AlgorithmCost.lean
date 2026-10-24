/-
# A concrete counted bit-cost model of the paper's algorithm

`Komlos/Runtime.lean` packages the runtime half of Theorem 1.1 as the Prop
`DiscrepancyRuntimeBound`, and `Komlos/RuntimeBound.lean` proves it for
`WellScaled` cost models conditional on signing existence
(`BoolSigningExists`), while refuting the unconditional `∀ c` statement
(`not_theorem11WithRuntime`). What was missing is a *concrete* model of
the paper's algorithm whose bit-cost can actually be counted. This file
supplies it.

## Contents

* `WalkStep`: an inductive describing the per-round operations of the
  paper's algorithm — batch sampling of candidate signings, Gram /
  resolvent evaluation, Sherman–Morrison rank-one inverse updates,
  augmented-block queries (equation 4.5), guard checks, grid rounding of
  the maintained rational state, and full inverse recomputations. Each
  constructor carries its size parameters, and `WalkStep.bitCost` gives
  the literal counted bit-cost in terms of the `BitCostModel` fields and
  the operation counts of `Komlos/DynamicMaintenance.lean`.
* `totalBitCost`: the counted bit-cost summed over a walk transcript
  `steps : List WalkStep`.
* `WalkStep.DimOK`: dimension admissibility — Gram matrices are at most
  `n × n` and augmented matrices have order at most `2n`.
* `WalkProfile` / `WalkProfile.ofList`: the count profile of a
  transcript (updates, recomputations, block queries, Gram evaluations,
  guard checks, sampled signs, rounded entries), and `profileBound`, the
  per-class closed-form bound.
* `totalBitCost_le_profileBound`: the counted total fits `profileBound`.
* `WalkBudget`: the parameter-count hypotheses under which the walk is
  near matrix-multiplication time — at most `Λ` expensive operations of
  each class, `n·Λ` sampled signs, `n²·Λ` rounded entries, and the
  rebuild schedule `R·n ≤ T`. These are the paper's count estimates;
  they are hypotheses because the walk analysis is not yet formalized.
* `totalBitCost_le_envelope`: under `WellScaled`, `WalkBudget`, and
  `Λ ≤ (1 + log δ⁻¹)²`, the counted bit-cost is at most `48` times
  `runtimeEnvelope c m n B l` — the `n^ω`-style envelope, i.e. near
  matrix-multiplication time up to an explicit constant. The
  inverse-maintenance share is handled by `maintenanceTotalOps_le`.
* `algorithmCostModel`: a concrete `BitCostModel` — schoolbook rational
  arithmetic (`add`/`cmp` linear, `mul`/`div` quadratic in the bit size)
  and matrix multiplication charged `⌈n^ω⌉·B` at leading constant `2` —
  with proofs of `WellScaled` and of `DiscrepancyRuntimeBound`
  conditional on `BoolSigningExists`.
* `Theorem11WithRuntime'`: the corrected statement quantifying only over
  `WellScaled` models, proved from signing existence and witnessed by
  the concrete model.

## Status

* **Proved:** all cost arithmetic, the step/profile bounds, the envelope
  estimate, well-scaledness of the concrete model, and the conditional
  runtime theorems. No `sorry`, no new axioms.
* **Hypotheses, not proved:** `WalkBudget` (the paper's parameter-count
  estimates relative to the polylog budget `Λ`), the dimension
  admissibility of the transcript, and `BoolSigningExists` (the
  discrepancy existence supplied by the walk assembly).
* The `48` in `totalBitCost_le_envelope` is an explicit constant in the
  sense of `O(·)`; the paper's `Õ` absorbs it.
-/

import Komlos.RuntimeBound
import Komlos.DynamicMaintenance

namespace Komlos

open scoped BigOperators

/-! ## The per-round operations of the walk -/

/-- The elementary per-round operations of the paper's algorithm.

* `batchSample k`: draw a batch of `k` candidate signs / directions
  (Section 4's completion sampling); charged `k` multiply–compare pairs.
* `gramResolvent k`: evaluate a `k × k` Gram matrix and a resolvent
  quadratic form; charged as two `k × k` matrix products.
* `rankOneUpdate`: one Sherman–Morrison rank-one update of the cached
  inverse (`DynamicInverseState.update`), charged `rankOneUpdateOps`.
* `blockQuery k`: one column query on the order-`k` augmented matrix
  `A(Q)` of `augmentedMatrix`, charged `blockQueryOps`.
* `guardCheck`: the nonsingularity guard `1 + v ⬝ᵥ (Inv *ᵥ u) ≠ 0`,
  charged `guardCheckOps`.
* `gridRound e`: round `e` maintained rational entries to the grid
  `1/s` (`roundToGrid x s = round (x * s) / s`), charged a multiply, a
  divide, an add and a compare per entry.
* `recompute`: a full inverse recomputation, charged `recomputeOps`
  (one `matmulCost`). -/
inductive WalkStep where
  | batchSample : ℕ → WalkStep
  | gramResolvent : ℕ → WalkStep
  | rankOneUpdate : WalkStep
  | blockQuery : ℕ → WalkStep
  | guardCheck : WalkStep
  | gridRound : ℕ → WalkStep
  | recompute : WalkStep

namespace WalkStep

/-- The counted bit-cost of one walk step in ambient dimension `n` with
entry bit size `B`, in terms of the `BitCostModel` fields and the
operation counts of `Komlos/DynamicMaintenance.lean`. -/
def bitCost : WalkStep → BitCostModel → ℕ → ℕ → ℕ
  | .batchSample k, c, _, B => k * (c.mulCost B + c.cmpCost B)
  | .gramResolvent k, c, _, B => 2 * c.matmulCost k B
  | .rankOneUpdate, c, n, B => rankOneUpdateOps c n B
  | .blockQuery k, c, _, B => blockQueryOps c k B
  | .guardCheck, c, n, B => guardCheckOps c n B
  | .gridRound e, c, _, B =>
      e * (c.mulCost B + c.divCost B + c.addCost B + c.cmpCost B)
  | .recompute, c, n, B => recomputeOps c n B

/-- A step is dimension-admissible for ambient dimension `n` when its
carried size parameters stay inside the ambient budgets: Gram/resolvent
matrices are at most `n × n`, and augmented block matrices have order at
most `2n` (they are `(s + 2k)`-dimensional with `s, k ≤ n`). -/
def DimOK : WalkStep → ℕ → Prop
  | .gramResolvent k, n => k ≤ n
  | .blockQuery k, n => k ≤ 2 * n
  | _, _ => True

/-- Per-step count contributions used to group the total cost by
operation class. -/
def updatesOf : WalkStep → ℕ | .rankOneUpdate => 1 | _ => 0
def recomputesOf : WalkStep → ℕ | .recompute => 1 | _ => 0
def queriesOf : WalkStep → ℕ | .blockQuery _ => 1 | _ => 0
def gramsOf : WalkStep → ℕ | .gramResolvent _ => 1 | _ => 0
def guardsOf : WalkStep → ℕ | .guardCheck => 1 | _ => 0
def samplesOf : WalkStep → ℕ | .batchSample k => k | _ => 0
def entriesOf : WalkStep → ℕ | .gridRound e => e | _ => 0

/-- Per-step real-valued accounted bound: each step's counted `bitCost`
is dominated by this expression (`bitCost_le_accountedBound`). The
maintenance classes keep the literal `ℕ` operation counts cast to `ℝ`
so that they can be fed into `maintenanceTotalOps_le`. -/
noncomputable def accountedBound : WalkStep → BitCostModel → ℕ → ℕ → ℝ
  | .batchSample k, c, _, B => 2 * c.scalarConst * (k : ℝ) * (B : ℝ) ^ 2
  | .gramResolvent _, c, n, B =>
      2 * c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ)
  | .rankOneUpdate, c, n, B => (rankOneUpdateOps c n B : ℝ)
  | .blockQuery _, c, n, B => 8 * c.scalarConst * (n : ℝ) ^ 2 * (B : ℝ) ^ 2
  | .guardCheck, c, n, B => 6 * c.scalarConst * (n : ℝ) ^ 2 * (B : ℝ) ^ 2
  | .gridRound e, c, _, B => 4 * c.scalarConst * (e : ℝ) * (B : ℝ) ^ 2
  | .recompute, c, n, B => (recomputeOps c n B : ℝ)

/-- Each admissible step's counted bit-cost fits its accounted bound.
This is where the `BitCostModel` field bounds, the quadratic operation
bounds of `DynamicMaintenance`, and the dimension admissibility are
consumed. -/
theorem bitCost_le_accountedBound (s : WalkStep) (c : BitCostModel)
    {n B : ℕ} (hn : 1 ≤ n) (hB : 1 ≤ B) (hdim : s.DimOK n) :
    (s.bitCost c n B : ℝ) ≤ s.accountedBound c n B := by
  have hs := c.scalarConst_nonneg
  have hBR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hBB : (B : ℝ) ≤ (B : ℝ) ^ 2 :=
    le_self_pow₀ hBR (by decide : (2 : ℕ) ≠ 0)
  have hmul : (c.mulCost B : ℝ) ≤ c.scalarConst * (B : ℝ) ^ 2 :=
    c.mulCost_le B
  have hdiv : (c.divCost B : ℝ) ≤ c.scalarConst * (B : ℝ) ^ 2 :=
    c.divCost_le B
  have hadd : (c.addCost B : ℝ) ≤ c.scalarConst * (B : ℝ) ^ 2 :=
    (c.addCost_le B).trans (mul_le_mul_of_nonneg_left hBB hs)
  have hcmp : (c.cmpCost B : ℝ) ≤ c.scalarConst * (B : ℝ) ^ 2 :=
    (c.cmpCost_le B).trans (mul_le_mul_of_nonneg_left hBB hs)
  cases s with
  | batchSample k =>
      simp only [bitCost, accountedBound]
      push_cast
      calc (k : ℝ) * ((c.mulCost B : ℝ) + (c.cmpCost B : ℝ))
          ≤ (k : ℝ) * (c.scalarConst * (B : ℝ) ^ 2 +
              c.scalarConst * (B : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left (add_le_add hmul hcmp)
              (Nat.cast_nonneg _)
        _ = 2 * c.scalarConst * k * (B : ℝ) ^ 2 := by ring
  | gramResolvent k =>
      simp only [bitCost, accountedBound]
      have hk : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdim
      have hpow : (k : ℝ) ^ c.ω ≤ (n : ℝ) ^ c.ω :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hk
          (le_trans (by norm_num) c.two_le_ω)
      have h2 : (2 : ℝ) * (c.matmulCost k B : ℝ) ≤
          2 * (c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ)) := by
        have h1 : (c.matmulCost k B : ℝ) ≤
            c.matmulLeadingConst * (k : ℝ) ^ c.ω * (B : ℝ) :=
          c.matmulCost_le k B
        have h2a : c.matmulLeadingConst * (k : ℝ) ^ c.ω * (B : ℝ) ≤
            c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow c.matmulLeadingConst_nonneg)
            (Nat.cast_nonneg _)
        linarith
      push_cast
      linarith
  | rankOneUpdate => simp [bitCost, accountedBound]
  | blockQuery k =>
      simp only [bitCost, accountedBound]
      have hk : (k : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hdim
      have hk2 : (k : ℝ) ^ 2 ≤ (2 * (n : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hk 2
      calc (blockQueryOps c k B : ℝ)
          ≤ 2 * c.scalarConst * (k : ℝ) ^ 2 * (B : ℝ) ^ 2 :=
            blockQueryOps_le c k B hB
        _ ≤ 2 * c.scalarConst * (2 * (n : ℝ)) ^ 2 * (B : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hk2
                (mul_nonneg (by norm_num) hs)) (sq_nonneg _)
        _ = 8 * c.scalarConst * (n : ℝ) ^ 2 * (B : ℝ) ^ 2 := by ring
  | guardCheck =>
      simpa [bitCost, accountedBound] using
        guardCheckOps_quadratic c n B hn hB
  | gridRound e =>
      simp only [bitCost, accountedBound]
      push_cast
      calc (e : ℝ) * ((c.mulCost B : ℝ) + (c.divCost B : ℝ) +
              (c.addCost B : ℝ) + (c.cmpCost B : ℝ))
          ≤ (e : ℝ) * (c.scalarConst * (B : ℝ) ^ 2 +
              c.scalarConst * (B : ℝ) ^ 2 + c.scalarConst * (B : ℝ) ^ 2 +
              c.scalarConst * (B : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left
              (add_le_add (add_le_add (add_le_add hmul hdiv) hadd) hcmp)
              (Nat.cast_nonneg _)
        _ = 4 * c.scalarConst * e * (B : ℝ) ^ 2 := by ring
  | recompute => simp [bitCost, accountedBound]

end WalkStep

/-- Total counted bit-cost of a walk transcript: the sum of the per-step
bit-costs. -/
def totalBitCost (c : BitCostModel) (n B : ℕ) (steps : List WalkStep) : ℕ :=
  (steps.map (WalkStep.bitCost · c n B)).sum

/-! ## The count profile and the per-class bound -/

/-- The operation-count profile of a walk transcript. -/
structure WalkProfile where
  /-- Number of Sherman–Morrison rank-one updates. -/
  updates : ℕ
  /-- Number of full inverse recomputations. -/
  recomputes : ℕ
  /-- Number of augmented-block queries. -/
  queries : ℕ
  /-- Number of Gram/resolvent evaluations. -/
  grams : ℕ
  /-- Number of guard checks. -/
  guards : ℕ
  /-- Total number of sampled candidate signs across all batches. -/
  samples : ℕ
  /-- Total number of grid-rounded entries. -/
  entries : ℕ

/-- The profile of a transcript: each field is the corresponding count
summed over the step list. -/
def WalkProfile.ofList (steps : List WalkStep) : WalkProfile where
  updates := (steps.map WalkStep.updatesOf).sum
  recomputes := (steps.map WalkStep.recomputesOf).sum
  queries := (steps.map WalkStep.queriesOf).sum
  grams := (steps.map WalkStep.gramsOf).sum
  guards := (steps.map WalkStep.guardsOf).sum
  samples := (steps.map WalkStep.samplesOf).sum
  entries := (steps.map WalkStep.entriesOf).sum

/-- The per-class accounted bound, as a closed form in the profile:
`T` rank-one updates and `R` recomputations at the literal `ℕ` costs,
`G` Gram evaluations at `2·matmulLeadingConst·n^ω·B`, block queries at
`8·scalarConst·n²·B²`, guards at `6·scalarConst·n²·B²`, sampled signs at
`2·scalarConst·B²` each, and rounded entries at `4·scalarConst·B²`. -/
noncomputable def profileBound (c : BitCostModel) (n B : ℕ)
    (p : WalkProfile) : ℝ :=
  (p.updates : ℝ) * (rankOneUpdateOps c n B : ℝ) +
  (p.recomputes : ℝ) * (recomputeOps c n B : ℝ) +
  (p.grams : ℝ) *
    (2 * c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ)) +
  (p.queries : ℝ) * (8 * c.scalarConst * (n : ℝ) ^ 2 * (B : ℝ) ^ 2) +
  (p.guards : ℝ) * (6 * c.scalarConst * (n : ℝ) ^ 2 * (B : ℝ) ^ 2) +
  2 * c.scalarConst * (p.samples : ℝ) * (B : ℝ) ^ 2 +
  4 * c.scalarConst * (p.entries : ℝ) * (B : ℝ) ^ 2

/-- The profile bound splits over a cons: the head contributes exactly
its `accountedBound`. -/
theorem profileBound_ofList_cons (c : BitCostModel) (n B : ℕ)
    (s : WalkStep) (rest : List WalkStep) :
    profileBound c n B (WalkProfile.ofList (s :: rest)) =
      s.accountedBound c n B +
        profileBound c n B (WalkProfile.ofList rest) := by
  cases s <;>
    simp only [WalkProfile.ofList, profileBound, WalkStep.accountedBound,
      WalkStep.updatesOf, WalkStep.recomputesOf, WalkStep.queriesOf,
      WalkStep.gramsOf, WalkStep.guardsOf, WalkStep.samplesOf,
      WalkStep.entriesOf, List.map_cons, List.sum_cons] <;>
    push_cast <;>
    ring

/-- **Counted cost bound.** For a dimension-admissible transcript, the
total counted bit-cost fits the per-class closed form `profileBound`. -/
theorem totalBitCost_le_profileBound (c : BitCostModel) {n B : ℕ}
    (hn : 1 ≤ n) (hB : 1 ≤ B) (steps : List WalkStep)
    (hdim : ∀ s ∈ steps, s.DimOK n) :
    (totalBitCost c n B steps : ℝ) ≤
      profileBound c n B (WalkProfile.ofList steps) := by
  induction steps with
  | nil =>
      simp [totalBitCost, profileBound, WalkProfile.ofList]
  | cons s rest ih =>
      have hle := s.bitCost_le_accountedBound c hn hB
        (hdim s List.mem_cons_self)
      have hih := ih (fun t ht => hdim t (List.mem_cons_of_mem _ ht))
      have hcast : (totalBitCost c n B (s :: rest) : ℝ) =
          (s.bitCost c n B : ℝ) + (totalBitCost c n B rest : ℝ) := by
        simp [totalBitCost]
      calc (totalBitCost c n B (s :: rest) : ℝ)
          = (s.bitCost c n B : ℝ) + (totalBitCost c n B rest : ℝ) := hcast
        _ ≤ s.accountedBound c n B +
              profileBound c n B (WalkProfile.ofList rest) :=
            add_le_add hle hih
        _ = profileBound c n B (WalkProfile.ofList (s :: rest)) :=
            (profileBound_ofList_cons c n B s rest).symm

/-! ## The parameter-count budget and the envelope theorem -/

/-- The parameter-count budget under which a transcript's counted cost
is near matrix-multiplication time. `Λ` plays the role of the
polylogarithmic budget — instantiated by `(1 + log δ⁻¹)²` in
`totalBitCost_le_envelope`. Each field is a count estimate of the kind
the paper's walk analysis supplies (Section 5 / Appendix E); they are
hypotheses, not proved facts about the transcript. -/
structure WalkBudget (p : WalkProfile) (n : ℕ) (Λ : ℝ) : Prop where
  /-- Amortized rebuild schedule: at most one full recomputation per `n`
  rank-one updates (Appendix E). -/
  rebuild : (p.recomputes : ℝ) * (n : ℝ) ≤ (p.updates : ℝ)
  /-- At most `Λ` lazy rank-one updates in total. -/
  updates_le : (p.updates : ℝ) ≤ Λ
  /-- At most `Λ` augmented-block queries. -/
  queries_le : (p.queries : ℝ) ≤ Λ
  /-- At most `Λ` Gram/resolvent evaluations. -/
  grams_le : (p.grams : ℝ) ≤ Λ
  /-- At most `Λ` guard checks. -/
  guards_le : (p.guards : ℝ) ≤ Λ
  /-- At most `n·Λ` sampled candidate signs across all batches. -/
  samples_le : (p.samples : ℝ) ≤ (n : ℝ) * Λ
  /-- At most `n²·Λ` rounded grid entries in total (the maintained
  `n × n` state is re-rounded each of `Λ` rounds). -/
  entries_le : (p.entries : ℝ) ≤ (n : ℝ) ^ 2 * Λ

/-- **The counted runtime bound.** Under `WellScaled` and the
parameter-count budget `WalkBudget` with `Λ ≤ (1 + log δ⁻¹)²`, the
total counted bit-cost of a dimension-admissible transcript is at most
`48` times the runtime envelope
`matmulLeadingConst·(m + n)^ω·B²·(1 + log δ⁻¹)²`: near
matrix-multiplication time with an explicit constant. The maintenance
share (initialization, updates, amortized recomputations) is bounded by
`maintenanceTotalOps_le`. -/
theorem totalBitCost_le_envelope (c : BitCostModel) (hs : c.WellScaled)
    {m n B : ℕ} (hn : 1 ≤ n) (hB : 1 ≤ B)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {l : ℝ} (_hl : 0 ≤ l) (hΛl : Λ ≤ (1 + l) ^ 2)
    (steps : List WalkStep)
    (hdim : ∀ s ∈ steps, s.DimOK n)
    (hbud : WalkBudget (WalkProfile.ofList steps) n Λ) :
    (totalBitCost c n B steps : ℝ) ≤
      48 * runtimeEnvelope c m n B l := by
  set p := WalkProfile.ofList steps with hp
  have hR := hbud.rebuild
  have hT := hbud.updates_le
  have hQ := hbud.queries_le
  have hG := hbud.grams_le
  have hGC := hbud.guards_le
  have hS := hbud.samples_le
  have hE := hbud.entries_le
  have hω0 : (0 : ℝ) ≤ c.ω := le_trans (by norm_num) c.two_le_ω
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg _
  have hBR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hBB : (B : ℝ) ≤ (B : ℝ) ^ 2 :=
    le_self_pow₀ hBR (by decide : (2 : ℕ) ≠ 0)
  have hs0 : (0 : ℝ) ≤ c.scalarConst := c.scalarConst_nonneg
  have hL0 : (0 : ℝ) ≤ c.matmulLeadingConst := c.matmulLeadingConst_nonneg
  have hmn1 : (1 : ℝ) ≤ (m : ℝ) + n := by
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    linarith
  have hmn0 : (0 : ℝ) ≤ (m : ℝ) + n := le_trans zero_le_one hmn1
  have hΛnn : (0 : ℝ) ≤ Λ := by linarith
  have hM0 : (0 : ℝ) ≤ ((m : ℝ) + n) ^ c.ω := Real.rpow_nonneg hmn0 _
  have hnω : (n : ℝ) ^ c.ω ≤ ((m : ℝ) + n) ^ c.ω :=
    Real.rpow_le_rpow hn0 (by linarith) hω0
  have hn2ω : (n : ℝ) ^ 2 ≤ ((m : ℝ) + n) ^ c.ω := by
    have h1 : (n : ℝ) ^ 2 ≤ ((m : ℝ) + n) ^ 2 :=
      pow_le_pow_left₀ hn0 (by linarith) 2
    have h2 : ((m : ℝ) + n) ^ 2 ≤ ((m : ℝ) + n) ^ c.ω := by
      rw [← Real.rpow_two]
      exact_mod_cast c.rpow_two_le_rpow_ω (n := m + n) (by omega)
    exact h1.trans h2
  have hn1ω : (n : ℝ) ≤ ((m : ℝ) + n) ^ c.ω :=
    (le_self_pow₀ hnR (by decide : (2 : ℕ) ≠ 0)).trans hn2ω
  -- A `C·(envelope/Λ)` share fits `C` envelopes.
  have hfac : ∀ C : ℝ, 0 ≤ C →
      C * (c.matmulLeadingConst * ((m : ℝ) + n) ^ c.ω * (B : ℝ) ^ 2 * Λ) ≤
        C * runtimeEnvelope c m n B l := by
    intro C hC
    have hbase : (0 : ℝ) ≤
        c.matmulLeadingConst * ((m : ℝ) + n) ^ c.ω * (B : ℝ) ^ 2 := by
      positivity
    unfold runtimeEnvelope
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hΛl hbase) hC
  -- Generic per-class bound: a unit accounted cost `C·scalarConst·X·B²`
  -- applied `q ≤ Y·Λ` times, with `X·Y ≤ (m + n)^ω`, fits `C` envelopes.
  have hclass : ∀ (C q X Y : ℝ), 0 ≤ C → 0 ≤ X → 0 ≤ Y →
      X * Y ≤ ((m : ℝ) + n) ^ c.ω → q ≤ Y * Λ →
      q * (C * c.scalarConst * X * (B : ℝ) ^ 2) ≤
        C * runtimeEnvelope c m n B l := by
    intro C q X Y hC hX hY hXY hqY
    have hsXY : c.scalarConst * (X * Y) ≤
        c.matmulLeadingConst * ((m : ℝ) + n) ^ c.ω :=
      (mul_le_mul_of_nonneg_right hs (mul_nonneg hX hY)).trans
        (mul_le_mul_of_nonneg_left hXY hL0)
    have htot : (Y * Λ) * (C * c.scalarConst * X * (B : ℝ) ^ 2) ≤
        C * (c.matmulLeadingConst * ((m : ℝ) + n) ^ c.ω * (B : ℝ) ^ 2 * Λ) := by
      calc (Y * Λ) * (C * c.scalarConst * X * (B : ℝ) ^ 2)
          = C * (B : ℝ) ^ 2 * (c.scalarConst * (X * Y)) * Λ := by ring
        _ ≤ C * (B : ℝ) ^ 2 *
              (c.matmulLeadingConst * ((m : ℝ) + n) ^ c.ω) * Λ := by
            apply mul_le_mul_of_nonneg_right _ hΛnn
            exact mul_le_mul_of_nonneg_left hsXY (by positivity)
        _ = _ := by ring
    calc q * (C * c.scalarConst * X * (B : ℝ) ^ 2)
        ≤ (Y * Λ) * (C * c.scalarConst * X * (B : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hqY (by positivity)
      _ ≤ C * (c.matmulLeadingConst * ((m : ℝ) + n) ^ c.ω * (B : ℝ) ^ 2 * Λ) :=
          htot
      _ ≤ C * runtimeEnvelope c m n B l := hfac C hC
  -- The maintenance share: init + `T` updates + `R` amortized recomputes.
  have hMaintOps :
      ((maintenanceTotalOps c n B p.updates p.recomputes : ℕ) : ℝ) ≤
        maintenanceEnvelope c n B p.updates :=
    maintenanceTotalOps_le c n B p.updates p.recomputes hn hB hR
  have hMaint : maintenanceEnvelope c n B p.updates ≤
      26 * runtimeEnvelope c m n B l := by
    have h1 : 12 * c.scalarConst * (B : ℝ) ≤
        12 * c.matmulLeadingConst * (B : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs (by norm_num)) hB0
    have hLB : c.matmulLeadingConst ≤ c.matmulLeadingConst * (B : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hBR hL0
    have hcoef : c.matmulLeadingConst + 12 * c.scalarConst * (B : ℝ) ≤
        13 * c.matmulLeadingConst * (B : ℝ) := by linarith
    have hTnn : (0 : ℝ) ≤ (p.updates : ℝ) + 1 := by positivity
    have hT1 : (p.updates : ℝ) + 1 ≤ 2 * Λ := by linarith
    have h13L : (0 : ℝ) ≤ 13 * c.matmulLeadingConst * (B : ℝ) := by positivity
    have h13Λ : (0 : ℝ) ≤ 13 * c.matmulLeadingConst * (B : ℝ) * (2 * Λ) := by
      positivity
    have hpow0 : (0 : ℝ) ≤ (n : ℝ) ^ c.ω := Real.rpow_nonneg hn0 _
    have e1 : (c.matmulLeadingConst + 12 * c.scalarConst * (B : ℝ)) *
          ((p.updates : ℝ) + 1) * (n : ℝ) ^ c.ω * (B : ℝ) ≤
        (13 * c.matmulLeadingConst * (B : ℝ)) * (2 * Λ) *
          ((m : ℝ) + n) ^ c.ω * (B : ℝ) := by
      calc (c.matmulLeadingConst + 12 * c.scalarConst * (B : ℝ)) *
            ((p.updates : ℝ) + 1) * (n : ℝ) ^ c.ω * (B : ℝ)
          = ((c.matmulLeadingConst + 12 * c.scalarConst * (B : ℝ)) *
              ((p.updates : ℝ) + 1) * (n : ℝ) ^ c.ω) * (B : ℝ) := by ring
        _ ≤ ((13 * c.matmulLeadingConst * (B : ℝ)) * (2 * Λ) *
              ((m : ℝ) + n) ^ c.ω) * (B : ℝ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul (mul_le_mul hcoef hT1 hTnn h13L) hnω hpow0 h13Λ)
              hB0
        _ = _ := by ring
    have e2 : (13 * c.matmulLeadingConst * (B : ℝ)) * (2 * Λ) *
          ((m : ℝ) + n) ^ c.ω * (B : ℝ) ≤
        26 * runtimeEnvelope c m n B l := by
      calc (13 * c.matmulLeadingConst * (B : ℝ)) * (2 * Λ) *
            ((m : ℝ) + n) ^ c.ω * (B : ℝ)
          = 26 * (c.matmulLeadingConst * ((m : ℝ) + n) ^ c.ω *
              (B : ℝ) ^ 2 * Λ) := by ring
        _ ≤ 26 * runtimeEnvelope c m n B l := hfac 26 (by norm_num)
    unfold maintenanceEnvelope
    exact e1.trans e2
  -- Gram / resolvent evaluations.
  have hGram : (p.grams : ℝ) *
      (2 * c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ)) ≤
      2 * runtimeEnvelope c m n B l := by
    have hinner : 2 * c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ) ≤
        2 * c.matmulLeadingConst * ((m : ℝ) + n) ^ c.ω * (B : ℝ) ^ 2 := by
      calc 2 * c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ)
          = 2 * c.matmulLeadingConst * ((n : ℝ) ^ c.ω * (B : ℝ)) := by ring
        _ ≤ 2 * c.matmulLeadingConst *
              (((m : ℝ) + n) ^ c.ω * (B : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hnω hBB hB0 hM0) (by positivity)
        _ = _ := by ring
    calc (p.grams : ℝ) *
          (2 * c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ))
        ≤ Λ * (2 * c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ)) :=
          mul_le_mul_of_nonneg_right hG (by positivity)
      _ ≤ Λ * (2 * c.matmulLeadingConst * ((m : ℝ) + n) ^ c.ω * (B : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hinner hΛnn
      _ = 2 * (c.matmulLeadingConst * ((m : ℝ) + n) ^ c.ω * (B : ℝ) ^ 2 * Λ) :=
          by ring
      _ ≤ 2 * runtimeEnvelope c m n B l := hfac 2 (by norm_num)
  -- Block queries, guard checks, sampled signs, rounded entries.
  have hQuery : (p.queries : ℝ) *
      (8 * c.scalarConst * (n : ℝ) ^ 2 * (B : ℝ) ^ 2) ≤
      8 * runtimeEnvelope c m n B l :=
    hclass 8 _ _ _ (by norm_num) (sq_nonneg _) zero_le_one
      (by simpa using hn2ω) (by simpa using hQ)
  have hGuard : (p.guards : ℝ) *
      (6 * c.scalarConst * (n : ℝ) ^ 2 * (B : ℝ) ^ 2) ≤
      6 * runtimeEnvelope c m n B l :=
    hclass 6 _ _ _ (by norm_num) (sq_nonneg _) zero_le_one
      (by simpa using hn2ω) (by simpa using hGC)
  have hSample : 2 * c.scalarConst * (p.samples : ℝ) * (B : ℝ) ^ 2 ≤
      2 * runtimeEnvelope c m n B l := by
    have := hclass 2 (p.samples : ℝ) 1 (n : ℝ) (by norm_num) zero_le_one
      hn0 (by simpa using hn1ω) hS
    calc 2 * c.scalarConst * (p.samples : ℝ) * (B : ℝ) ^ 2
        = (p.samples : ℝ) * (2 * c.scalarConst * 1 * (B : ℝ) ^ 2) := by ring
      _ ≤ 2 * runtimeEnvelope c m n B l := this
  have hEntry : 4 * c.scalarConst * (p.entries : ℝ) * (B : ℝ) ^ 2 ≤
      4 * runtimeEnvelope c m n B l := by
    have := hclass 4 (p.entries : ℝ) 1 ((n : ℝ) ^ 2) (by norm_num)
      zero_le_one (sq_nonneg _) (by simpa using hn2ω) hE
    calc 4 * c.scalarConst * (p.entries : ℝ) * (B : ℝ) ^ 2
        = (p.entries : ℝ) * (4 * c.scalarConst * 1 * (B : ℝ) ^ 2) := by ring
      _ ≤ 4 * runtimeEnvelope c m n B l := this
  -- The profile bound decomposes into the maintenance share plus the rest.
  have hsplit : profileBound c n B p ≤
      ((maintenanceTotalOps c n B p.updates p.recomputes : ℕ) : ℝ) +
        ((p.grams : ℝ) *
            (2 * c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ)) +
          (p.queries : ℝ) * (8 * c.scalarConst * (n : ℝ) ^ 2 * (B : ℝ) ^ 2) +
          (p.guards : ℝ) * (6 * c.scalarConst * (n : ℝ) ^ 2 * (B : ℝ) ^ 2) +
          2 * c.scalarConst * (p.samples : ℝ) * (B : ℝ) ^ 2 +
          4 * c.scalarConst * (p.entries : ℝ) * (B : ℝ) ^ 2) := by
    unfold profileBound maintenanceTotalOps
    push_cast
    linarith [c.matmulCost_nonneg n B]
  calc (totalBitCost c n B steps : ℝ)
      ≤ profileBound c n B p :=
        totalBitCost_le_profileBound c hn hB steps hdim
    _ ≤ ((maintenanceTotalOps c n B p.updates p.recomputes : ℕ) : ℝ) +
          ((p.grams : ℝ) *
              (2 * c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ)) +
            (p.queries : ℝ) *
              (8 * c.scalarConst * (n : ℝ) ^ 2 * (B : ℝ) ^ 2) +
            (p.guards : ℝ) *
              (6 * c.scalarConst * (n : ℝ) ^ 2 * (B : ℝ) ^ 2) +
            2 * c.scalarConst * (p.samples : ℝ) * (B : ℝ) ^ 2 +
            4 * c.scalarConst * (p.entries : ℝ) * (B : ℝ) ^ 2) := hsplit
    _ ≤ maintenanceEnvelope c n B p.updates +
          ((p.grams : ℝ) *
              (2 * c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ)) +
            (p.queries : ℝ) *
              (8 * c.scalarConst * (n : ℝ) ^ 2 * (B : ℝ) ^ 2) +
            (p.guards : ℝ) *
              (6 * c.scalarConst * (n : ℝ) ^ 2 * (B : ℝ) ^ 2) +
            2 * c.scalarConst * (p.samples : ℝ) * (B : ℝ) ^ 2 +
            4 * c.scalarConst * (p.entries : ℝ) * (B : ℝ) ^ 2) := by
        linarith [hMaintOps]
    _ ≤ 48 * runtimeEnvelope c m n B l := by
        linarith [hMaint, hGram, hQuery, hGuard, hSample, hEntry]

/-! ## The concrete algorithmic cost model -/

/-- **The concrete algorithmic cost model.** Schoolbook rational
arithmetic — `add`/`cmp` linear and `mul`/`div` quadratic in the operand
bit size — with matrix multiplication charged at `⌈n^ω⌉·B` bits and
leading constant `2`. The exponent `ω ≥ 2` stays abstract (the model is
valid for any matrix-multiplication algorithm of exponent `ω`); the
`+1` from the ceiling is absorbed into the leading constant `2` because
`n^ω ≥ 1` for `n ≥ 1`. -/
noncomputable def algorithmCostModel (ω : ℝ) (hω : 2 ≤ ω) : BitCostModel where
  ω := ω
  matmulLeadingConst := 2
  scalarConst := 1
  addCost := fun B => B
  mulCost := fun B => B ^ 2
  divCost := fun B => B ^ 2
  cmpCost := fun B => B
  matmulCost := fun n B => Nat.ceil ((n : ℝ) ^ ω) * B
  two_le_ω := hω
  matmulLeadingConst_nonneg := by norm_num
  scalarConst_nonneg := zero_le_one
  addCost_le := fun _ => by simp
  mulCost_le := fun _ => by simp
  divCost_le := fun _ => by simp
  cmpCost_le := fun _ => by simp
  matmulCost_le := fun n B => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hz : ((0 : ℕ) : ℝ) ^ ω = 0 := by
        rw [Nat.cast_zero]
        exact Real.zero_rpow (by linarith)
      rw [hz]
      simp
    · have h1 : (1 : ℝ) ≤ (n : ℝ) ^ ω :=
        Real.one_le_rpow (by exact_mod_cast hn) (by linarith)
      have hceil : (Nat.ceil ((n : ℝ) ^ ω) : ℝ) ≤ (n : ℝ) ^ ω + 1 :=
        (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)).le
      push_cast
      calc (Nat.ceil ((n : ℝ) ^ ω) : ℝ) * (B : ℝ)
          ≤ ((n : ℝ) ^ ω + 1) * (B : ℝ) :=
            mul_le_mul_of_nonneg_right hceil (Nat.cast_nonneg _)
        _ ≤ (2 * (n : ℝ) ^ ω) * (B : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
        _ = _ := by ring

/-- The concrete model is well-scaled: `scalarConst = 1 ≤ 2 =
matmulLeadingConst`. -/
theorem algorithmCostModel_wellScaled (ω : ℝ) (hω : 2 ≤ ω) :
    (algorithmCostModel ω hω).WellScaled :=
  show (1 : ℝ) ≤ 2 from by norm_num

/-- The counted walk cost for the concrete model fits `48` times its
runtime envelope — the concrete instantiation of
`totalBitCost_le_envelope`. -/
theorem totalBitCost_le_envelope_algorithm (ω : ℝ) (hω : 2 ≤ ω)
    {m n B : ℕ} (hn : 1 ≤ n) (hB : 1 ≤ B)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {l : ℝ} (hl : 0 ≤ l) (hΛl : Λ ≤ (1 + l) ^ 2)
    (steps : List WalkStep)
    (hdim : ∀ s ∈ steps, s.DimOK n)
    (hbud : WalkBudget (WalkProfile.ofList steps) n Λ) :
    (totalBitCost (algorithmCostModel ω hω) n B steps : ℝ) ≤
      48 * runtimeEnvelope (algorithmCostModel ω hω) m n B l :=
  totalBitCost_le_envelope _ (algorithmCostModel_wellScaled ω hω)
    hn hB hΛ hl hΛl steps hdim hbud

/-- **Conditional runtime theorem for the concrete model.** If Boolean
signings of discrepancy `< 99` always exist (`BoolSigningExists` — the
output of the paper's walk assembly), then `DiscrepancyRuntimeBound`
holds for `algorithmCostModel ω`: the verifier accepts the produced
signing and the accounted verification cost fits the envelope. -/
theorem discrepancyRuntimeBound_algorithmCostModel (ω : ℝ) (hω : 2 ≤ ω)
    (hex : BoolSigningExists) :
    DiscrepancyRuntimeBound (algorithmCostModel ω hω) :=
  discrepancyRuntimeBound_of_existence _
    (algorithmCostModel_wellScaled ω hω) hex

/-! ## The corrected `∀` runtime statement -/

/-- The corrected runtime statement of Theorem 1.1: the discrepancy and
runtime halves hold for every *well-scaled* bit-cost model. Unlike
`Theorem11WithRuntime` — refuted by `not_theorem11WithRuntime` because
badly-scaled models admit degenerate envelopes — this quantification is
the honest form of the theorem. -/
def Theorem11WithRuntime' : Prop :=
  ∀ c : BitCostModel, c.WellScaled → DiscrepancyRuntimeBound c

/-- `Theorem11WithRuntime'` is implied by signing existence: for every
well-scaled model, `discrepancyRuntimeBound_of_existence` supplies the
bound. The concrete `algorithmCostModel` witnesses that the
quantification is non-vacuous and applies to the model the algorithm
actually uses. -/
theorem theorem11WithRuntime' (hex : BoolSigningExists) :
    Theorem11WithRuntime' :=
  fun c hs => discrepancyRuntimeBound_of_existence c hs hex

/-- `Theorem11WithRuntime'` instantiated at the concrete model: together
with `algorithmCostModel_wellScaled`, the corrected statement yields the
runtime half of Theorem 1.1 for the algorithmic cost model. -/
theorem discrepancyRuntimeBound_concrete_of_theorem11WithRuntime'
    (h : Theorem11WithRuntime') (ω : ℝ) (hω : 2 ≤ ω) :
    DiscrepancyRuntimeBound (algorithmCostModel ω hω) :=
  h _ (algorithmCostModel_wellScaled ω hω)

#print axioms totalBitCost_le_envelope
#print axioms algorithmCostModel_wellScaled
#print axioms discrepancyRuntimeBound_algorithmCostModel
#print axioms theorem11WithRuntime'

end Komlos
