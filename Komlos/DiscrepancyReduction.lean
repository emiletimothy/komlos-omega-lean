import Komlos

/-!
# Deterministic discrepancy reduction (Proposition A.1 assembly)

The per-row estimates of `Komlos.lean` are assembled here into the
final bound of Proposition A.1: at a signing produced when the walk
completes, every row's discrepancy is strictly below

  `max {31673/320 + δret + δoff, 63 + δlarge + δoff, 1}`,

where the three branches correspond respectively to completed/medium
rows, still-large rows (whose rounding moves at most 63 coordinates),
and discarded input rows of ℓ¹-norm at most one.

The theorem is stated conditionally on per-class row bounds; discharging
those hypotheses is the business of the (not yet formalized) walk
invariants.  A corollary with the paper's defect tolerances
(`δret + δoff ≤ 10⁻² + 10⁻³ + 10⁻⁴`, `δlarge` small) gives the `< 99`
conclusion of Theorem 1.1.
-/

namespace Komlos

/-- **Proposition A.1 (final bound).** Rows are partitioned into a
discarded class with `|rowValue| ≤ 1`, a still-large class bounded by
`63 + δlarge + δoff`, and the remaining completed/medium rows bounded
by `31673/320 + δret + δoff`. -/
theorem deterministic_discrepancy_reduction {m n : ℕ}
    (A : Input m n) (ε : Fin n → ℝ) (δret δoff δlarge : ℝ)
    (hδret : 0 ≤ δret) (hδoff : 0 ≤ δoff)
    (Sdisc Slarge : Finset (Fin m))
    (hdisc : ∀ i ∈ Sdisc, |rowValue A ε i| ≤ 1)
    (hlarge : ∀ i ∈ Slarge, |rowValue A ε i| < 63 + δlarge + δoff)
    (hcomp : ∀ i, i ∉ Sdisc ∪ Slarge →
      |rowValue A ε i| < 31673 / 320 + δret + δoff)
    (i : Fin m) :
    |rowValue A ε i| <
      max (max (31673 / 320 + δret + δoff) (63 + δlarge + δoff)) 1 := by
  have hbase : (1 : ℝ) < 31673 / 320 + δret + δoff := by
    linarith [hδret, hδoff]
  by_cases hi1 : i ∈ Sdisc
  · exact lt_of_le_of_lt (hdisc i hi1)
      (hbase.trans_le (le_trans (le_max_left _ _) (le_max_left _ _)))
  · by_cases hi2 : i ∈ Slarge
    · exact (hlarge i hi2).trans_le
        (le_trans (le_max_right _ _) (le_max_left _ _))
    · exact (hcomp i (by simp [Finset.mem_union, hi1, hi2])).trans_le
        (le_trans (le_max_left _ _) (le_max_left _ _))

/-- The paper's `(6.3)` conclusion: with defect tolerances totaling at
most `10⁻² + 10⁻³ + 10⁻⁴` and large rows remaining below the bound,
the final discrepancy is below `99`. -/
theorem discrepancy_below_99 {m n : ℕ}
    (A : Input m n) (ε : Fin n → ℝ) (δret δoff δlarge : ℝ)
    (hδret : 0 ≤ δret) (hδoff : 0 ≤ δoff)
    (hdefect : δret + δoff ≤ 1 / 100 + 1 / 1000 + 1 / 10000)
    (hlarge_cap : 63 + δlarge + δoff < 99)
    (Sdisc Slarge : Finset (Fin m))
    (hdisc : ∀ i ∈ Sdisc, |rowValue A ε i| ≤ 1)
    (hlarge : ∀ i ∈ Slarge, |rowValue A ε i| < 63 + δlarge + δoff)
    (hcomp : ∀ i, i ∉ Sdisc ∪ Slarge →
      |rowValue A ε i| < 31673 / 320 + δret + δoff)
    (i : Fin m) :
    |rowValue A ε i| < 99 := by
  have h := deterministic_discrepancy_reduction A ε δret δoff δlarge
    hδret hδoff Sdisc Slarge hdisc hlarge hcomp i
  have hmax : max (max (31673 / 320 + δret + δoff)
      (63 + δlarge + δoff)) 1 < 99 := by
    refine max_lt (max_lt ?_ hlarge_cap) (by norm_num)
    linarith [final_constant_margin]
  exact h.trans hmax

end Komlos
