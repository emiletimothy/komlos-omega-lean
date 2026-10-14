import Komlos
import Komlos.Resolvent
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# The initialization margin (Appendix A)

To show that the initial spectral matrix satisfies `M ⪯ bdep I`,
Appendix A bounds the normalized row weight `f(r) = 2·ν(16 − H₀/r)/r²`
by its value at `r = Rmax = 291/200`.  The resulting certificate is the
purely arithmetic inequality

  `(1 + 733/727500)^10000 > 23634 > (1009/1000)·(2·119)/(bdep·Rmax²)`,

where `733/727500 = 2932/(291·20000)` comes from evaluating the barrier
`u = 16 − H₀/Rmax = −5864/291` inside `ν(u) = 119·(1 − u/20000)^(−10000)`.

The paper verifies the lower bound by truncating the binomial expansion
after 24 terms: "multiplying the 25 summands by 10³ and summing their
floors gives 23634835".  We certify the same statement: the term
sequence is defined recursively, matched to `Nat.choose`, and the
rational partial sum is evaluated by `decide` (kernel computation over
`ℚ`, no `native_decide`).
-/

namespace Komlos

/-- The `ℓ`-th term of the truncated binomial expansion of
`(1 + 733/727500)^10000`, defined recursively to keep the arithmetic
in `ℚ`. -/
def termSeq : ℕ → ℚ
  | 0 => 1
  | k + 1 =>
      termSeq k * ((10000 : ℚ) - k) * 733 / (727500 * ((k : ℚ) + 1))

/-- `termSeq ℓ` equals the `ℓ`-th binomial summand for `ℓ ≤ 10000`. -/
theorem termSeq_eq (ℓ : ℕ) (hℓ : ℓ ≤ 10000) :
    (termSeq ℓ : ℝ) =
      (Nat.choose 10000 ℓ : ℝ) * (733 / 727500 : ℝ) ^ ℓ := by
  induction ℓ with
  | zero => simp [termSeq]
  | succ k ih =>
      have hk : k ≤ 10000 := by omega
      have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
      have hch : ((Nat.choose 10000 (k + 1) : ℕ) : ℝ) =
          (Nat.choose 10000 k : ℝ) * ((10000 : ℝ) - k) / (k + 1) := by
        have h := Nat.choose_succ_right_eq 10000 k
        have h' : ((Nat.choose 10000 (k + 1) * (k + 1) : ℕ) : ℝ) =
            ((Nat.choose 10000 k * (10000 - k) : ℕ) : ℝ) :=
          congrArg Nat.cast h
        push_cast at h'
        rw [Nat.cast_sub hk] at h'
        norm_num only [Nat.cast_ofNat] at h'
        rw [eq_div_iff hk1]
        linarith [h']
      rw [termSeq]
      push_cast
      rw [ih hk, hch]
      field_simp
      ring

/-- The exact rational value of the 24-term partial sum exceeds 23634.
Computed by `norm_num` after unrolling the recursive term sequence. -/
theorem termSeq_partial_sum_lower :
    (23634 : ℚ) < ∑ ℓ ∈ Finset.range 25, termSeq ℓ := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [termSeq]

/-- The real cast of the partial sum bound. -/
theorem termSeq_partial_sum_lower_real :
    (23634 : ℝ) < ∑ ℓ ∈ Finset.range 25, (termSeq ℓ : ℝ) := by
  rw [← Rat.cast_sum]
  exact_mod_cast termSeq_partial_sum_lower

/-- **The initialization margin** `(1 + 733/727500)^10000 > 23634`. -/
theorem initialization_margin :
    (23634 : ℝ) < (1 + 733 / 727500) ^ 10000 := by
  have hterms : ∀ ℓ ∈ Finset.range 25,
      (termSeq ℓ : ℝ) ≤ (733 / 727500 : ℝ) ^ ℓ * (Nat.choose 10000 ℓ : ℝ) := by
    intro ℓ hℓ
    have hℓ' : ℓ ≤ 10000 := by
      have := Finset.mem_range.mp hℓ
      omega
    rw [termSeq_eq ℓ hℓ']
    apply le_of_eq
    ring
  have hpart := termSeq_partial_sum_lower_real
  calc (23634 : ℝ) < ∑ ℓ ∈ Finset.range 25, (termSeq ℓ : ℝ) := hpart
    _ ≤ ∑ ℓ ∈ Finset.range 25,
        (733 / 727500 : ℝ) ^ ℓ * (Nat.choose 10000 ℓ : ℝ) :=
      Finset.sum_le_sum hterms
    _ ≤ ∑ ℓ ∈ Finset.range 10001,
        (733 / 727500 : ℝ) ^ ℓ * (Nat.choose 10000 ℓ : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        exact Finset.mem_range.mpr
          ((Finset.mem_range.mp hx).trans (by norm_num))
      · intro i _ _
        exact mul_nonneg (pow_nonneg (by norm_num) _)
          (Nat.cast_nonneg _)
    _ = (733 / 727500 + 1 : ℝ) ^ 10000 := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = (1 + 733 / 727500 : ℝ) ^ 10000 := by rw [add_comm]

/-- The barrier value `16 − H₀/Rmax` appearing in the (A.2) bound. -/
theorem barrier_at_Rmax : (16 : ℝ) - (263 / 5) / (291 / 200) = -5864 / 291 := by
  norm_num

/-- `ν(−5864/291)` written with base `1 + 733/727500`. -/
theorem weight_at_barrier_Rmax :
    weight ((-5864 : ℝ) / 291) = 119 / (1 + 733 / 727500) ^ 10000 := by
  unfold weight
  rw [show (1 : ℝ) - (-5864 / 291) / 20000 = 1 + 733 / 727500 by norm_num]

/-- The (A.2) row bound at `r = Rmax`: `2·ν(16−H₀/Rmax)/Rmax²` is at
most `(1000/1009)·bdep`, using `(1+733/727500)^10000 > 23634`. -/
theorem row_weight_bound_at_Rmax :
    2 * weight ((-5864 : ℝ) / 291) / (291 / 200) ^ 2 ≤
      (1000 / 1009) * (3 / 625) := by
  rw [weight_at_barrier_Rmax]
  have h := initialization_margin
  calc 2 * (119 / (1 + 733 / 727500 : ℝ) ^ 10000) / (291 / 200) ^ 2
      ≤ 2 * (119 / 23634) / (291 / 200) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h.le
    _ ≤ (1000 / 1009) * (3 / 625) := by norm_num

end Komlos
