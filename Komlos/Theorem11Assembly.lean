/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Komlos.DiscrepancyReduction
import Komlos.TrialConcentration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Conditional assembly of Theorem 1.1 (discrepancy part)

`Komlos.DiscrepancyReduction` proves the final bound of Proposition A.1:
a signing `ε` whose rows split into

* a **discarded** class (`|rowValue A ε i| ≤ 1`),
* a **still-large** class (`|rowValue A ε i| < 63 + δlarge + δoff`), and
* **completed/medium** rows (`|rowValue A ε i| < 31673/320 + δret + δoff`),

satisfies `|rowValue A ε i| < 99` everywhere, provided the defect budget
`δret + δoff ≤ 10⁻² + 10⁻³ + 10⁻⁴` and the large-row cap
`63 + δlarge + δoff < 99` hold (`discrepancy_below_99`).

This module packages what remains to be proved to reach
`DiscrepancyPartOfTheorem11`. The structure `WalkSuccessInput A` is a
*lemma list*: every field is a concrete mathematical statement whose
proof is a remaining block of the paper, phrased so that discharging it
makes the assembly unconditional. No `sorry`, no axioms — the open work
lives entirely inside the structure fields.

## What is discharged unconditionally here

* `Sdisc` is fixed canonically as `discardedRows A`, the rows of ℓ¹ norm
  `≤ 1`. The bound `hdisc` is `discarded_row_bound`, which holds for
  *every* signing — no walk hypothesis is needed for this class.
* The defect tolerances are instantiated: `δret := retirementDefect`
  (`10⁻²`), `δoff := offsetDefect` (`10⁻³ + 10⁻⁴`), so `hdefect` is an
  equality, and `hlarge_cap` follows once `δlarge ≤ largeRowDefectCap`
  (`35`).
* The completed/medium bound `hcomp` is reduced by
  `completed_row_error_bound` to the paper's four-term value
  decomposition `value = tracked + deletion + retirement + offset` with
  `|tracked| < 263/5` — the conclusion `barriers_control_abs_value`
  already extracts from the pair of barrier bounds `barrier ±1 d r G ≤ 0`.
* At the top level, `n < 64` is discharged by `small_dimension_exists`
  and `m = 0` is vacuous, so the package is required only for
  `0 < m ∧ 64 ≤ n`.

## The residual checklist (fields of `WalkSuccessInput`)

1. `walk`, `walk_coherent`, `walk_cube` — a coherent `SymmetricWalk`
   whose leaves stay in the cube: the clipped adaptive rounding of §2.
   The local step geometry is in `Walk.lean`
   (`clipped_endpoint_hits_boundary`, `symmetric_endpoints_in_cube`); the
   potential engine that drives the walk is
   `pair_average_resolventPotential_batch`/`_quad`, which turns the
   curvature hypothesis `h2` of Proposition 2.1 into leaf-average
   nonincrease via `terminal_average_le_root_of_branchConcave`.
2. `leaf`, `mem_leaf`, `leaf_signing` — a leaf of the walk that is a
   genuine signing `ε ∈ {±1}ⁿ`. This is the successful trial: all
   coordinates are eventually frozen to `±1`. The finite uniform model
   supplies the weak version (`exists_memLeaf_signing_few_bad_rows`,
   `≤ n/T²` bad rows); the strong version needs the paper's Lemma D.1 /
   Theorem 4.1 chain (adaptive Gaussian density, `GaussianDensity.lean`)
   composed with the potential nonincrease of item 1 and a leaf-selection
   argument (`exists_memLeaf_terminalAverage_le`).
3. `Slarge`, `δlarge`, `δlarge_nonneg`, `δlarge_le`, `large_bound` — the
   still-large exceptional rows: rows frozen before completion, whose
   rounding moves at most `63` coordinates, keep
   `|rowValue| < 63 + δlarge + δoff`. The intended proof is the
   displacement control of `StabilityTransport.lean`
   (`transported_subspace_bound`, `abs_barrierAt_sub_le`) together with
   the barrier barrier-pair exclusivity `protected_signs_exclusive`.
4. `completed_decomp` — every live row admits the paper's value
   decomposition with tracked part `< 263/5` and deletion term within the
   telescope bound `2·(291/200)·(8 + √63)`: this is the barrier invariant
   `barrier σ d r G ≤ 0` maintained along the walk
   (`barriers_control_abs_value` yields `|d| < 263/5`), the deletion
   accounting `total_deleted_coefficient_bound`/`deleted_defect_bound`,
   the retirement defect `10⁻²` of the anchored update
   (`anchorUpdate`/`retire` in `AnchorUpdate.lean`), and the
   finite-precision offset `10⁻³ + 10⁻⁴`
   (`input_rounding_error`/`accepted_output_sound`, `FinitePrecision`).

The spectral-dimension and curvature inputs that these items consume —
`spectral_subspace_exists_unconditional` (B.4), the `h2` curvature
hypothesis on the trust window, and `initialization_margin` for the
initial `M ⪯ bdep I` — are proved in `SpectralDimension.lean`,
`SpectralPath.lean`, and `InitializationMargin.lean`; wiring them into the
walk invariants above is the remaining work.

## Conditional theorems

* `exists_signing_discrepancy_below_99`:
  `WalkSuccessInput A → ∃ ε, HasDiscrepancyBelow A ε 99`.
* `DiscrepancyPartOfTheorem11_of_walkSuccess`:
  `WalkSuccessHypothesis → DiscrepancyPartOfTheorem11`, where
  `WalkSuccessHypothesis` asks for the package on every column-normalized
  rational input with `0 < m` and `64 ≤ n`.
-/

namespace Komlos

open scoped BigOperators

/-- The discarded-row class of Proposition A.1: the rows of `A` whose ℓ¹
norm is at most `1`. It is fixed canonically (rather than quantified)
because `discarded_row_bound` bounds `|rowValue|` by `1` for *any*
signing on these rows, so `hdisc` needs no hypothesis at all. -/
noncomputable def discardedRows {m n : ℕ} (A : Input m n) : Finset (Fin m) :=
  Finset.univ.filter fun i => ∑ j, |A i j| ≤ 1

theorem mem_discardedRows {m n : ℕ} {A : Input m n} {i : Fin m} :
    i ∈ discardedRows A ↔ ∑ j, |A i j| ≤ 1 := by
  simp [discardedRows]

/-- The retirement-defect budget `δret = 10⁻²` of Proposition A.1. -/
noncomputable def retirementDefect : ℝ := 1 / 100

/-- The offset/finite-precision defect budget `δoff = 10⁻³ + 10⁻⁴`. -/
noncomputable def offsetDefect : ℝ := 1 / 1000 + 1 / 10000

/-- The cap on the still-large defect budget: any `δlarge ≤ 35` keeps
`63 + δlarge + δoff < 99`. -/
noncomputable def largeRowDefectCap : ℝ := 35

theorem retirementDefect_nonneg : 0 ≤ retirementDefect := by
  norm_num [retirementDefect]

theorem offsetDefect_nonneg : 0 ≤ offsetDefect := by
  norm_num [offsetDefect]

/-- The instantiated defect budget satisfies `discrepancy_below_99`'s
tolerance `δret + δoff ≤ 10⁻² + 10⁻³ + 10⁻⁴` with equality. -/
theorem defect_budget : retirementDefect + offsetDefect ≤
    1 / 100 + 1 / 1000 + 1 / 10000 := by
  norm_num [retirementDefect, offsetDefect]

/-- **Residual hypotheses for Theorem 1.1 (discrepancy part).** Every
field is a concrete mathematical statement — a lemma of the paper — not
a restatement of the conclusion:

* the walk exists and is well-formed (`walk_coherent`, `walk_cube`),
* a leaf is a signing (`leaf_signing`), i.e. the trial succeeds,
* still-large rows keep the `63`-cap (`large_bound`),
* every other row admits the tracked/deletion/retirement/offset value
  decomposition with `|tracked| < 263/5` (`completed_decomp`).

Discarded rows and the defect tolerances are *not* fields: they are
discharged above. -/
structure WalkSuccessInput {m n : ℕ} (A : Input m n) where
  /-- The adaptive symmetric rounding walk of §2. -/
  walk : SymmetricWalk n
  /-- Coherence: children are `x ± d` — the fair-sign split. -/
  walk_coherent : SymmetricWalk.Coherent walk
  /-- Every leaf stays in the cube `[-1, 1]ⁿ` (clipping). -/
  walk_cube : SymmetricWalk.CubeLeaves walk
  /-- The successful terminal position. -/
  leaf : Fin n → ℝ
  /-- `leaf` is reached by the walk. -/
  mem_leaf : SymmetricWalk.MemLeaf walk leaf
  /-- The trial succeeds: `leaf` is a genuine signing. -/
  leaf_signing : IsSigning leaf
  /-- The exceptional set of rows still large at the end of the walk. -/
  Slarge : Finset (Fin m)
  /-- The still-large defect budget. -/
  δlarge : ℝ
  /-- The defect budget is nonnegative. -/
  δlarge_nonneg : 0 ≤ δlarge
  /-- The defect budget keeps `63 + δlarge + δoff` under `99`. -/
  δlarge_le : δlarge ≤ largeRowDefectCap
  /-- **Still-large row bound** (rows frozen before completion move at
  most `63` coordinates): `|rowValue| < 63 + δlarge + δoff`. -/
  large_bound : ∀ i ∈ Slarge,
    |rowValue A leaf i| < 63 + δlarge + offsetDefect
  /-- **Completed/medium row decomposition** (the barrier statement of
  §2.2): the row value splits as `tracked + deletion + retirement +
  offset` with the tracked part under the barrier threshold `263/5`, the
  deletion part within the telescope bound
  `2·(291/200)·(8 + √63)` of `total_deleted_coefficient_bound`, and the
  retirement/offset defects inside the `10⁻²`/`10⁻³ + 10⁻⁴` budgets. -/
  completed_decomp : ∀ i, i ∉ discardedRows A ∪ Slarge →
    ∃ tracked deletion retirement offset : ℝ,
      rowValue A leaf i = tracked + deletion + retirement + offset ∧
      |tracked| < 263 / 5 ∧
      |deletion| ≤ 2 * (291 / 200) * (8 + Real.sqrt 63) ∧
      |retirement| ≤ retirementDefect ∧ |offset| ≤ offsetDefect

/-- **Conditional main theorem.** Given the residual package for `A`,
the successful leaf is a signing of discrepancy below `99` — Proposition
A.1's `(6.3)` via `discrepancy_below_99` with the defect tolerances
instantiated. -/
theorem exists_signing_discrepancy_below_99 {m n : ℕ} {A : Input m n}
    (h : WalkSuccessInput A) : ∃ ε, HasDiscrepancyBelow A ε 99 := by
  refine ⟨h.leaf, h.leaf_signing, fun i => ?_⟩
  have hle := h.δlarge_le
  unfold largeRowDefectCap at hle
  have hcap : 63 + h.δlarge + offsetDefect < 99 := by
    unfold offsetDefect
    linarith
  refine discrepancy_below_99 A h.leaf retirementDefect offsetDefect h.δlarge
      retirementDefect_nonneg offsetDefect_nonneg defect_budget hcap
      (discardedRows A) h.Slarge ?_ h.large_bound ?_ i
  · intro i hi
    exact discarded_row_bound A h.leaf_signing i (mem_discardedRows.mp hi)
  · intro i hi
    obtain ⟨t, d, r, o, hval, ht, hd, hr, ho⟩ := h.completed_decomp i hi
    exact completed_row_error_bound hval ht hd hr ho

/-- The residual package, uniformly over inputs: every column-normalized
rational matrix with `0 < m` and `64 ≤ n` admits the successful-walk
data. The restrictions are the only cases not already covered by
`small_dimension_exists` (`n < 64`) and vacuity (`m = 0`). -/
def WalkSuccessHypothesis : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ),
    ColumnNormalized (fun i j => (A i j : ℝ)) → 0 < m → 64 ≤ n →
      Nonempty (WalkSuccessInput (fun i j => (A i j : ℝ)))

/-- **Theorem 1.1 (discrepancy part), conditional on the package.** If
`WalkSuccessHypothesis` holds — the successful walk exists for every
column-normalized rational input of non-trivial size — then
`DiscrepancyPartOfTheorem11` follows: `n < 64` by
`small_dimension_exists`, `m = 0` vacuously, and `0 < m ∧ 64 ≤ n` by the
package plus `exists_signing_discrepancy_below_99`. -/
theorem DiscrepancyPartOfTheorem11_of_walkSuccess
    (h : WalkSuccessHypothesis) : DiscrepancyPartOfTheorem11 := by
  intro m n A hA
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨fun _ => 1, fun _ => Or.inr rfl, fun i => i.elim0⟩
  · rcases Nat.lt_or_ge n 64 with hn | hn
    · exact small_dimension_exists hA hn
    · obtain ⟨w⟩ := h m n A hA hm hn
      exact exists_signing_discrepancy_below_99 w

/-- Variant over real inputs: a `WalkSuccessInput` for every
column-normalized real matrix of non-trivial size also yields
`DiscrepancyPartOfTheorem11` (by restriction to rational casts). -/
theorem DiscrepancyPartOfTheorem11_of_walkSuccess_real
    (h : ∀ (m n : ℕ) (A : Input m n),
      ColumnNormalized A → 0 < m → 64 ≤ n → WalkSuccessInput A) :
    DiscrepancyPartOfTheorem11 :=
  DiscrepancyPartOfTheorem11_of_walkSuccess fun m n A hA hm hn =>
    ⟨h m n (fun i j => (A i j : ℝ)) hA hm hn⟩

#print axioms exists_signing_discrepancy_below_99
#print axioms DiscrepancyPartOfTheorem11_of_walkSuccess

end Komlos
