/-
# Finite-precision layer II: dyadic truncation toward zero

This module formalizes the *deterministic rounding operators* used by the
finite-precision implementation (Appendix F) of "The Komlós Problem in Near
Matrix-Multiplication Time" (Anand–Chen). It complements
`Komlos/FinitePrecision.lean`, which treats *nearest*-grid rounding
(`roundToGrid`) and *rounding down* (`floorToGrid`) on the grid `1/s`, by
providing the operator a fixed-point/`Int` implementation actually performs:
**truncation toward zero onto the dyadic grid `1/2^B`**.

## What is proved

* **`trunc` semantics.** `trunc q B = (⌊|q|·2^B⌋ / 2^B) · sgn(q)`, i.e. floor
  the scaled magnitude and restore the sign (`trunc`, `trunc_of_nonneg`,
  `trunc_of_nonpos`, `trunc_neg`). For `q ≥ 0` it coincides with
  `floorToGrid q (2^B)`; for `q ≤ 0` it is `-(floorToGrid (-q) (2^B))`.
* **Error bound.** `|q - trunc q B| < 1/2^B` (`abs_sub_trunc_lt`,
  `abs_sub_trunc`, `abs_sub_trunc_real` for the `Rat.cast` version), and
  truncation never increases magnitude (`abs_trunc_le`, `trunc_abs`).
* **Order.** `trunc · B` is monotone (`trunc_mono`), idempotent
  (`trunc_idem`), fixes every dyadic grid point `k/2^B` (`trunc_divInt`,
  `trunc_natCast_div`), preserves the sign of its argument
  (`trunc_nonneg`, `trunc_nonpos`, `trunc_ge_of_nonpos`), and preserves a
  *strict* sign once `|q| ≥ 1/2^B` (`one_div_pow_le_trunc`, `trunc_pos`,
  `trunc_le_neg_one_div_pow`, `trunc_eq_zero_iff`).
* **Vector/matrix versions.** `truncVec` and `truncMat` truncate entrywise
  with the same per-entry bound, monotonicity and idempotence
  (`truncVec_apply`, `abs_sub_truncVec`, `truncVec_mono`, `truncVec_idem`,
  `abs_sub_truncMat`, `truncMat_mono`, `truncMat_idem`, and the row `L¹`
  bound `truncMat_row_l1 : ∑ j, |A i j - truncMat A B i j| ≤ n/2^B`).
* **`ℓ∞` bookkeeping.** `vecInfNorm x` is the largest `|x i|` (junk `0` on
  `Fin 0`), with `abs_le_vecInfNorm`, `vecInfNorm_nonneg`, `vecInfNorm_le`,
  and `vecInfNorm_sub_truncVec_le : ‖x - truncVec x B‖∞ ≤ 1/2^B`.
* **Quadratic-form perturbation.** `quadForm M x = ∑ i j, x i M i j x j`
  (`= xᵀMx`, cf. `quadForm_eq_dotProduct`). The polarisation identity
  `xᵢxⱼ - yᵢyⱼ = ((xᵢ-yᵢ)(xⱼ+yⱼ) + (xᵢ+yᵢ)(xⱼ-yⱼ))/2` gives the entrywise
  bound `|xᵀMx - yᵀMy| ≤ ‖x-y‖∞ · ‖x+y‖∞ · ∑ᵢⱼ|Mᵢⱼ|`
  (`quadForm_sub_abs_le`), hence
  `|xᵀMx - (truncVec x)ᵀM(truncVec x)| ≤ 2^{-B} · ‖x+truncVec x‖∞ · ‖M‖₁`
  (`quadForm_truncVec_le`), specialised to the cube as
  `≤ 2^{1-B} · ∑ᵢⱼ|Mᵢⱼ|` (`quadForm_truncVec_le_of_cube`) and cast to `ℝ`
  (`quadForm_truncVec_le_real`). `quadForm_trunc_lower_bound` is the PSD
  corollary: a nonnegative truncated form certifies the original form up to
  the perturbation envelope.
* **Bit-size bookkeeping (App F).** Truncation keeps bit sizes bounded:
  `(trunc q B).den ∣ 2^B` (`trunc_den_dvd`), `|(trunc q B).num| ≤ |q|·2^B`
  (`trunc_num_abs_le`), `num.natAbs ≤ ⌊|q|·2^B⌋.toNat`
  (`trunc_num_natAbs_le`), and the headline bounds
  `ratBitSize (trunc q B) ≤ natBitSize q.num.natAbs + 2B + 1`
  (`ratBitSize_trunc_le'`) and
  `ratBitSize (trunc q B) ≤ ratBitSize q + 2B` (`ratBitSize_trunc_le_add`),
  with `inputBitSize (truncMat A B) ≤ inputBitSize A + m·n·2B`
  (`inputBitSize_truncMat_le`) for the matrix version.

All proofs are exact (over `ℚ`, with `Rat.cast` only at the `ℝ` boundary);
no `sorry`, no `native_decide`, no new axioms.
-/

import Komlos.FinitePrecision
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Log

namespace Komlos

open scoped BigOperators
open scoped Matrix

/-! ## `trunc`: truncation toward zero onto the dyadic grid `1 / 2 ^ B` -/

/-- Truncate `q : ℚ` **toward zero** to the dyadic grid with denominator
`2 ^ B`: take the floor of the scaled magnitude `|q| · 2 ^ B` and restore the
sign. For `q ≥ 0` this is `⌊q·2^B⌋ / 2^B` (i.e. `floorToGrid q (2^B)`); for
`q < 0` it is `⌈q·2^B⌉ / 2^B = -⌊(-q)·2^B⌋ / 2^B`. Truncating toward zero —
rather than rounding down — makes `trunc` an odd function (`trunc_neg`) that
never increases magnitude (`abs_trunc_le`), matching what a fixed-width
binary right-shift does to a signed mantissa. -/
def trunc (q : ℚ) (B : ℕ) : ℚ :=
  (⌊|q| * 2 ^ B⌋ : ℚ) / 2 ^ B * (if 0 ≤ q then 1 else -1)

/-- For `q ≥ 0`, truncation is just the floor of `q · 2^B` over `2^B` —
i.e. `trunc q B = floorToGrid q (2^B)`. -/
theorem trunc_of_nonneg {q : ℚ} (hq : 0 ≤ q) (B : ℕ) :
    trunc q B = (⌊q * 2 ^ B⌋ : ℚ) / 2 ^ B := by
  unfold trunc
  rw [abs_of_nonneg hq, ite_eq_left hq, mul_one]

/-- For `q ≤ 0`, truncation is minus the floor of the magnitude:
`trunc q B = -⌊(-q)·2^B⌋ / 2^B = ⌈q·2^B⌉ / 2^B`. -/
theorem trunc_of_nonpos {q : ℚ} (hq : q ≤ 0) (B : ℕ) :
    trunc q B = -((⌊(-q) * 2 ^ B⌋ : ℚ) / 2 ^ B) := by
  unfold trunc
  rw [abs_of_nonpos hq]
  rcases lt_or_eq_of_le hq with hlt | heq
  · rw [ite_eq_right (not_le.mpr hlt)]
    ring
  · subst heq
    simp

/-- The dyadic truncation is the `Rat.divInt` with denominator `2^B` and
numerator `sgn(q) · ⌊|q|·2^B⌋`. This is the key to the denominator and
numerator bounds used in bit-size bookkeeping. -/
theorem trunc_eq_divInt (q : ℚ) (B : ℕ) :
    trunc q B =
      Rat.divInt ((if 0 ≤ q then (1 : ℤ) else -1) * ⌊|q| * 2 ^ B⌋)
        ((2 ^ B : ℕ) : ℤ) := by
  rcases lt_or_ge q 0 with hq | hq
  · have hq' : ¬(0 ≤ q) := not_le.mpr hq
    have h : (if 0 ≤ q then (1 : ℤ) else -1) = -1 := ite_eq_right hq'
    rw [trunc_of_nonpos hq.le, h, abs_of_nonpos hq.le, Rat.divInt_eq_div]
    push_cast
    ring
  · have h : (if 0 ≤ q then (1 : ℤ) else -1) = 1 := ite_eq_left hq
    rw [trunc_of_nonneg hq, h, one_mul, abs_of_nonneg hq, Rat.divInt_eq_div]
    push_cast
    ring

/-- `trunc` is odd: `trunc (-q) B = -trunc q B`. -/
theorem trunc_neg (q : ℚ) (B : ℕ) : trunc (-q) B = -trunc q B := by
  unfold trunc
  rw [abs_neg]
  rcases lt_or_ge q 0 with hq | hq
  · have hnq : 0 ≤ -q := neg_nonneg.mpr hq.le
    rw [ite_eq_right (not_le.mpr hq), ite_eq_left hnq]
    ring
  · rcases eq_or_lt_of_le hq with hq0 | hpos
    · subst hq0
      simp
    · have hnq : ¬(0 ≤ -q) := not_le.mpr (neg_lt_zero.mpr hpos)
      rw [ite_eq_left hq, ite_eq_right hnq]
      ring

/-- The magnitude of `trunc q B` is `trunc |q| B`. -/
theorem trunc_abs (q : ℚ) (B : ℕ) : trunc |q| B = |trunc q B| := by
  have hnn : (0 : ℚ) ≤ |q| := abs_nonneg q
  have hfloor : (0 : ℚ) ≤ (⌊|q| * 2 ^ B⌋ : ℚ) / 2 ^ B := by
    apply div_nonneg _ (by positivity)
    exact_mod_cast Int.floor_nonneg.mpr
      (mul_nonneg hnn (by positivity : (0 : ℚ) ≤ 2 ^ B))
  have hsgn : |(if 0 ≤ q then (1 : ℚ) else -1)| = 1 := by
    rcases lt_or_ge q 0 with hq | hq
    · rw [ite_eq_right (not_le.mpr hq)]
      simp
    · rw [ite_eq_left hq]
      simp
  rw [trunc_of_nonneg hnn]
  unfold trunc
  rw [abs_mul, abs_of_nonneg hfloor, hsgn, mul_one]

/-- Truncation preserves nonnegativity. -/
theorem trunc_nonneg {q : ℚ} (hq : 0 ≤ q) (B : ℕ) : 0 ≤ trunc q B := by
  rw [trunc_of_nonneg hq]
  apply div_nonneg _ (by positivity)
  exact_mod_cast Int.floor_nonneg.mpr
    (mul_nonneg hq (by positivity : (0 : ℚ) ≤ 2 ^ B))

/-- Truncation preserves nonpositivity. -/
theorem trunc_nonpos {q : ℚ} (hq : q ≤ 0) (B : ℕ) : trunc q B ≤ 0 := by
  have hn : 0 ≤ -q := neg_nonneg.mpr hq
  have h : trunc q B = -trunc (-q) B := by rw [trunc_neg, neg_neg]
  rw [h]
  linarith [trunc_nonneg hn B]

/-- For `q ≥ 0`, truncation rounds down: `trunc q B ≤ q`. -/
theorem trunc_le_of_nonneg {q : ℚ} (hq : 0 ≤ q) (B : ℕ) : trunc q B ≤ q := by
  have hB : (0 : ℚ) < 2 ^ B := by positivity
  rw [trunc_of_nonneg hq]
  calc (⌊q * 2 ^ B⌋ : ℚ) / 2 ^ B ≤ (q * 2 ^ B) / 2 ^ B :=
        (div_le_div_iff_of_pos_right hB).mpr (Int.floor_le _)
    _ = q := mul_div_cancel_right₀ q hB.ne'

/-- The residual of a nonnegative truncation is the fractional part of
`q · 2^B` rescaled, hence strictly less than `1/2^B`. -/
theorem sub_trunc_lt_of_nonneg {q : ℚ} (hq : 0 ≤ q) (B : ℕ) :
    q - trunc q B < 1 / 2 ^ B := by
  have hB : (0 : ℚ) < 2 ^ B := by positivity
  rw [trunc_of_nonneg hq]
  have h : q - (⌊q * 2 ^ B⌋ : ℚ) / 2 ^ B = Int.fract (q * 2 ^ B) / 2 ^ B := by
    show q - (⌊q * 2 ^ B⌋ : ℚ) / 2 ^ B = (q * 2 ^ B - (⌊q * 2 ^ B⌋ : ℚ)) / 2 ^ B
    exact sub_div' hB.ne'
  rw [h]
  exact (div_lt_div_iff_of_pos_right hB).mpr (Int.fract_lt_one _)

/-- For `q ≤ 0`, truncation rounds up: `q ≤ trunc q B`. -/
theorem trunc_ge_of_nonpos {q : ℚ} (hq : q ≤ 0) (B : ℕ) : q ≤ trunc q B := by
  have hn : 0 ≤ -q := neg_nonneg.mpr hq
  have h := trunc_le_of_nonneg hn B
  rw [trunc_neg] at h
  linarith

/-- Truncation never increases magnitude: `|trunc q B| ≤ |q|`. -/
theorem abs_trunc_le (q : ℚ) (B : ℕ) : |trunc q B| ≤ |q| := by
  rcases le_total 0 q with hq | hq
  · rw [abs_of_nonneg (trunc_nonneg hq B), abs_of_nonneg hq]
    exact trunc_le_of_nonneg hq B
  · have hn : 0 ≤ -q := neg_nonneg.mpr hq
    rw [abs_of_nonpos (trunc_nonpos hq B), abs_of_nonpos hq, ← trunc_neg]
    exact trunc_le_of_nonneg hn B

/-- The strict two-sided truncation bound `|q - trunc q B| < 1/2^B`. The
error is *strictly* inside one grid cell because truncation takes the floor
of the scaled magnitude. -/
theorem abs_sub_trunc_lt (q : ℚ) (B : ℕ) : |q - trunc q B| < 1 / 2 ^ B := by
  rcases le_total 0 q with hq | hq
  · rw [abs_of_nonneg (sub_nonneg.mpr (trunc_le_of_nonneg hq B))]
    exact sub_trunc_lt_of_nonneg hq B
  · have hn : 0 ≤ -q := neg_nonneg.mpr hq
    have h : q - trunc q B = -((-q) - trunc (-q) B) := by
      rw [trunc_neg]
      ring
    rw [h, abs_neg, abs_of_nonneg (sub_nonneg.mpr (trunc_le_of_nonneg hn B))]
    exact sub_trunc_lt_of_nonneg hn B

/-- The two-sided truncation bound `|q - trunc q B| ≤ 1/2^B` over `ℚ`. -/
theorem abs_sub_trunc (q : ℚ) (B : ℕ) : |q - trunc q B| ≤ 1 / 2 ^ B :=
  (abs_sub_trunc_lt q B).le

/-- The truncation bound after `Rat.cast` to `ℝ`. -/
theorem abs_sub_trunc_real (q : ℚ) (B : ℕ) :
    |(q : ℝ) - (trunc q B : ℝ)| ≤ (1 : ℝ) / 2 ^ B := by
  have h := abs_sub_trunc q B
  calc |(q : ℝ) - (trunc q B : ℝ)|
      = ((|q - trunc q B| : ℚ) : ℝ) := by rw [← Rat.cast_sub, Rat.cast_abs]
    _ ≤ ((1 / 2 ^ B : ℚ) : ℝ) := by exact_mod_cast h
    _ = (1 : ℝ) / 2 ^ B := by norm_num

/-- `trunc · B` is monotone in its argument (the grid `B` is fixed). -/
theorem trunc_mono (B : ℕ) : Monotone fun q : ℚ => trunc q B := by
  intro x y hxy
  show trunc x B ≤ trunc y B
  rcases le_total x 0 with hx | hx
  · rcases le_total y 0 with hy | hy
    · rw [trunc_of_nonpos hx, trunc_of_nonpos hy]
      have hB : (0 : ℚ) < 2 ^ B := by positivity
      have hmul : (-y) * 2 ^ B ≤ (-x) * 2 ^ B :=
        mul_le_mul_of_nonneg_right (neg_le_neg hxy) hB.le
      have hf : ⌊(-y) * 2 ^ B⌋ ≤ ⌊(-x) * 2 ^ B⌋ := Int.floor_mono hmul
      rw [neg_le_neg_iff]
      exact (div_le_div_iff_of_pos_right hB).mpr (by exact_mod_cast hf)
    · exact (trunc_nonpos hx B).trans (trunc_nonneg hy B)
  · have hy : 0 ≤ y := hx.trans hxy
    rw [trunc_of_nonneg hx, trunc_of_nonneg hy]
    have hB : (0 : ℚ) < 2 ^ B := by positivity
    apply (div_le_div_iff_of_pos_right hB).mpr
    exact_mod_cast Int.floor_mono (mul_le_mul_of_nonneg_right hxy hB.le)

/-- `trunc` is idempotent: truncating a truncated value is a no-op. -/
theorem trunc_idem (q : ℚ) (B : ℕ) : trunc (trunc q B) B = trunc q B := by
  have hB : (0 : ℚ) < 2 ^ B := by positivity
  rcases le_total 0 q with hq | hq
  · have hnn : 0 ≤ trunc q B := trunc_nonneg hq B
    conv_lhs => rw [trunc_of_nonneg hnn]
    rw [trunc_of_nonneg hq, div_mul_cancel₀ _ hB.ne', Int.floor_intCast]
  · have hnq : 0 ≤ -q := neg_nonneg.mpr hq
    have hnp : trunc q B ≤ 0 := trunc_nonpos hq B
    have key : -trunc q B = (⌊(-q) * 2 ^ B⌋ : ℚ) / 2 ^ B := by
      rw [show -trunc q B = trunc (-q) B from (trunc_neg q B).symm,
        trunc_of_nonneg hnq]
    rw [trunc_of_nonpos hnp]
    conv_rhs => rw [trunc_of_nonpos hq]
    rw [key, div_mul_cancel₀ _ hB.ne', Int.floor_intCast]

/-- Dyadic grid points are fixed points: `trunc (k / 2^B) B = k / 2^B` for
every integer `k`. -/
theorem trunc_divInt (k : ℤ) (B : ℕ) :
    trunc ((k : ℚ) / 2 ^ B) B = (k : ℚ) / 2 ^ B := by
  have hB : (0 : ℚ) < 2 ^ B := by positivity
  rcases le_total 0 k with hk | hk
  · have hkq : (0 : ℚ) ≤ (k : ℚ) / 2 ^ B :=
      div_nonneg (by exact_mod_cast hk) hB.le
    rw [trunc_of_nonneg hkq, div_mul_cancel₀ _ hB.ne', Int.floor_intCast]
  · have hkq : (k : ℚ) / 2 ^ B ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hk) hB.le
    have hnn : (0 : ℚ) ≤ -((k : ℚ) / 2 ^ B) := neg_nonneg.mpr hkq
    have hpos : trunc (-((k : ℚ) / 2 ^ B)) B = -((k : ℚ) / 2 ^ B) := by
      rw [trunc_of_nonneg hnn, ← neg_div, div_mul_cancel₀ _ hB.ne',
        ← Int.cast_neg, Int.floor_intCast, Int.cast_neg]
    rw [show trunc ((k : ℚ) / 2 ^ B) B = -trunc (-((k : ℚ) / 2 ^ B)) B by
      rw [trunc_neg, neg_neg]]
    rw [hpos, neg_neg]

/-- Natural grid points `k / 2^B` are fixed points (the `k ≥ 0` case of
`trunc_divInt`). -/
theorem trunc_natCast_div (k : ℕ) (B : ℕ) :
    trunc ((k : ℚ) / 2 ^ B) B = (k : ℚ) / 2 ^ B := by
  have hB : (0 : ℚ) < 2 ^ B := by positivity
  have hkq : (0 : ℚ) ≤ (k : ℚ) / 2 ^ B := by positivity
  rw [trunc_of_nonneg hkq, div_mul_cancel₀ _ hB.ne', Int.floor_natCast]
  simp

/-- Sign preservation away from zero: if `q ≥ 1/2^B` then `trunc q B` is not
only positive but at least `1/2^B` (the truncation lands on or past the
first positive grid point). -/
theorem one_div_pow_le_trunc {q : ℚ} {B : ℕ} (hq : 1 / 2 ^ B ≤ q) :
    1 / 2 ^ B ≤ trunc q B := by
  have hB : (0 : ℚ) < 2 ^ B := by positivity
  have hq0 : 0 ≤ q := le_trans (by positivity) hq
  rw [trunc_of_nonneg hq0]
  have h1 : (1 : ℚ) ≤ q * 2 ^ B := by
    have h := mul_le_mul_of_nonneg_right hq hB.le
    rwa [one_div_mul_cancel hB.ne'] at h
  have hf : (1 : ℤ) ≤ ⌊q * 2 ^ B⌋ := Int.le_floor.mpr (by exact_mod_cast h1)
  calc (1 : ℚ) / 2 ^ B = ((1 : ℤ) : ℚ) / 2 ^ B := by norm_num
    _ ≤ (⌊q * 2 ^ B⌋ : ℚ) / 2 ^ B :=
        (div_le_div_iff_of_pos_right hB).mpr (by exact_mod_cast hf)

/-- Truncation preserves strict positivity once `q` reaches the first grid
cell: `1/2^B ≤ q` implies `0 < trunc q B`. -/
theorem trunc_pos {q : ℚ} {B : ℕ} (hq : 1 / 2 ^ B ≤ q) : 0 < trunc q B :=
  lt_of_lt_of_le (by positivity) (one_div_pow_le_trunc hq)

/-- The negative side: `q ≤ -1/2^B` implies `trunc q B ≤ -1/2^B`. -/
theorem trunc_le_neg_one_div_pow {q : ℚ} {B : ℕ} (hq : q ≤ -(1 / 2 ^ B)) :
    trunc q B ≤ -(1 / 2 ^ B) := by
  have h : (1 : ℚ) / 2 ^ B ≤ -q := by linarith
  have h2 := one_div_pow_le_trunc h
  rw [trunc_neg] at h2
  linarith

/-- Truncation is strictly negative once `q ≤ -1/2^B`. -/
theorem trunc_neg_of_le {q : ℚ} {B : ℕ} (hq : q ≤ -(1 / 2 ^ B)) :
    trunc q B < 0 :=
  lt_of_le_of_lt (trunc_le_neg_one_div_pow hq)
    (neg_lt_zero.mpr (by positivity : (0 : ℚ) < 1 / 2 ^ B))

/-- `trunc q B = 0` exactly when `q` lies strictly inside the zero grid cell
`(-1/2^B, 1/2^B)`. -/
theorem trunc_eq_zero_iff {q : ℚ} {B : ℕ} :
    trunc q B = 0 ↔ |q| < 1 / 2 ^ B := by
  have hB : (0 : ℚ) < 2 ^ B := by positivity
  rw [← abs_eq_zero, ← trunc_abs q B, trunc_of_nonneg (abs_nonneg q)]
  rw [div_eq_zero_iff]
  simp only [hB.ne', or_false, Int.cast_eq_zero]
  rw [Int.floor_eq_iff]
  simp only [Int.cast_zero, zero_add]
  constructor
  · rintro ⟨-, hlt⟩
    rwa [lt_div_iff₀ hB]
  · intro hlt
    refine ⟨mul_nonneg (abs_nonneg _) hB.le, ?_⟩
    rwa [lt_div_iff₀ hB] at hlt

/-! ## Entrywise truncation: `truncVec`, `truncMat` -/

/-- Entrywise dyadic truncation of a rational vector. -/
def truncVec {n : ℕ} (x : Fin n → ℚ) (B : ℕ) : Fin n → ℚ :=
  fun i => trunc (x i) B

@[simp]
theorem truncVec_apply {n : ℕ} (x : Fin n → ℚ) (B : ℕ) (i : Fin n) :
    truncVec x B i = trunc (x i) B := rfl

/-- Per-entry truncation error for vectors. -/
theorem abs_sub_truncVec {n : ℕ} (x : Fin n → ℚ) (B : ℕ) (i : Fin n) :
    |x i - truncVec x B i| ≤ 1 / 2 ^ B :=
  abs_sub_trunc _ _

/-- `truncVec` is monotone entrywise. -/
theorem truncVec_mono {n : ℕ} {x y : Fin n → ℚ} (B : ℕ)
    (h : ∀ i, x i ≤ y i) : ∀ i, truncVec x B i ≤ truncVec y B i :=
  fun i => trunc_mono B (h i)

/-- `truncVec` is idempotent entrywise. -/
theorem truncVec_idem {n : ℕ} (x : Fin n → ℚ) (B : ℕ) :
    truncVec (truncVec x B) B = truncVec x B := by
  funext i
  exact trunc_idem _ _

/-- Truncation never increases any entry magnitude. -/
theorem abs_truncVec_le {n : ℕ} (x : Fin n → ℚ) (B : ℕ) (i : Fin n) :
    |truncVec x B i| ≤ |x i| :=
  abs_trunc_le _ _

/-- `truncVec` preserves nonnegativity entrywise. -/
theorem truncVec_nonneg {n : ℕ} {x : Fin n → ℚ} (h : ∀ i, 0 ≤ x i) (B : ℕ) :
    ∀ i, 0 ≤ truncVec x B i :=
  fun i => trunc_nonneg (h i) B

/-- Entrywise dyadic truncation of a rational matrix. -/
def truncMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (B : ℕ) :
    Matrix (Fin m) (Fin n) ℚ :=
  fun i j => trunc (A i j) B

/-- Per-entry truncation error for matrices. -/
theorem abs_sub_truncMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (B : ℕ)
    (i : Fin m) (j : Fin n) : |A i j - truncMat A B i j| ≤ 1 / 2 ^ B :=
  abs_sub_trunc _ _

/-- `truncMat` is monotone entrywise. -/
theorem truncMat_mono {m n : ℕ} {A C : Matrix (Fin m) (Fin n) ℚ} (B : ℕ)
    (h : ∀ i j, A i j ≤ C i j) : ∀ i j, truncMat A B i j ≤ truncMat C B i j :=
  fun i j => trunc_mono B (h i j)

/-- `truncMat` is idempotent. -/
theorem truncMat_idem {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (B : ℕ) :
    truncMat (truncMat A B) B = truncMat A B := by
  ext i j
  exact trunc_idem _ _

/-- Row `L¹` error of the truncated matrix, over `ℚ`: at most `n/2^B`. -/
theorem truncMat_row_l1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (B : ℕ)
    (i : Fin m) : ∑ j, |A i j - truncMat A B i j| ≤ (n : ℚ) / 2 ^ B := by
  calc ∑ j, |A i j - truncMat A B i j| ≤ ∑ _j : Fin n, (1 / 2 ^ B : ℚ) :=
        Finset.sum_le_sum fun j _ => abs_sub_trunc _ _
    _ = n / 2 ^ B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_one_div]

/-! ## The `ℓ∞` norm of a finitely indexed rational vector -/

/-- The sup norm `‖x‖∞` of a rational vector over `Fin n`: the largest
`|x i|`, defined as `0` when `n = 0` (there are no coordinates). A `List`
fold is used so the definition stays computable and needs no `OrderBot` on
`ℚ`. -/
def vecInfNorm {n : ℕ} (x : Fin n → ℚ) : ℚ :=
  (List.finRange n).foldl (fun a i => max a |x i|) 0

private theorem foldl_max_bounds {ι : Type*} (l : List ι) (f : ι → ℚ)
    (b : ℚ) :
    b ≤ l.foldl (fun a i => max a (f i)) b ∧
      ∀ i ∈ l, f i ≤ l.foldl (fun a i => max a (f i)) b := by
  induction l generalizing b with
  | nil => exact ⟨le_refl _, fun i hi => by simp at hi⟩
  | cons i l ih =>
      obtain ⟨h1, h2⟩ := ih (max b (f i))
      rw [List.foldl_cons]
      exact ⟨le_trans (le_max_left _ _) h1, fun j hj => by
        rcases List.mem_cons.mp hj with rfl | hj
        · exact le_trans (le_max_right _ _) h1
        · exact h2 j hj⟩

theorem vecInfNorm_nonneg {n : ℕ} (x : Fin n → ℚ) : 0 ≤ vecInfNorm x :=
  (foldl_max_bounds _ _ _).1

/-- Each coordinate's magnitude is below the sup norm. -/
theorem abs_le_vecInfNorm {n : ℕ} (x : Fin n → ℚ) (i : Fin n) :
    |x i| ≤ vecInfNorm x :=
  (foldl_max_bounds _ _ _).2 i (List.mem_finRange _)

private theorem foldl_max_le_iff {ι : Type*} (l : List ι) (f : ι → ℚ)
    (b C : ℚ) :
    l.foldl (fun a i => max a (f i)) b ≤ C ↔ b ≤ C ∧ ∀ i ∈ l, f i ≤ C := by
  induction l generalizing b with
  | nil => simp
  | cons i l ih =>
      rw [List.foldl_cons, ih, max_le_iff]
      constructor
      · rintro ⟨⟨hb, hi⟩, hrest⟩
        refine ⟨hb, fun j hj => ?_⟩
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hi
        · exact hrest j hj
      · rintro ⟨hb, h⟩
        exact ⟨⟨hb, h i (List.mem_cons.mpr (Or.inl rfl))⟩, fun j hj =>
          h j (List.mem_cons.mpr (Or.inr hj))⟩

/-- The sup norm is below `C` iff every coordinate magnitude is. -/
theorem vecInfNorm_le {n : ℕ} (x : Fin n → ℚ) {C : ℚ} (hC : 0 ≤ C)
    (h : ∀ i, |x i| ≤ C) : vecInfNorm x ≤ C :=
  (foldl_max_le_iff _ _ _ _).mpr ⟨hC, fun i _ => h i⟩

/-- The `ℓ∞` distance between a vector and its truncation is below the grid
size `1/2^B`. -/
theorem vecInfNorm_sub_truncVec_le {n : ℕ} (x : Fin n → ℚ) (B : ℕ) :
    vecInfNorm (x - truncVec x B) ≤ 1 / 2 ^ B := by
  apply vecInfNorm_le _ (by positivity)
  intro i
  exact abs_sub_trunc _ _

/-! ## Quadratic forms under entrywise perturbation -/

/-- The entrywise `L¹` norm `∑ᵢⱼ |M i j|` of a rational matrix — the matrix
norm used in the perturbation bounds of Appendix F (it dominates both the
operator `∞`-norm and the max-entry norm). -/
def matSumNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : ℚ :=
  ∑ i, ∑ j, |M i j|

theorem matSumNorm_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    0 ≤ matSumNorm M :=
  Finset.sum_nonneg fun _i _ => Finset.sum_nonneg fun _j _ => abs_nonneg _

/-- The quadratic form `xᵀMx` of a rational matrix, as the double sum
`∑ᵢⱼ xᵢ Mᵢⱼ xⱼ`. -/
def quadForm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) : ℚ :=
  ∑ i, ∑ j, x i * M i j * x j

/-- `quadForm M x` is literally `x ⬝ᵥ (M *ᵥ x)`. -/
theorem quadForm_eq_dotProduct {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (x : Fin n → ℚ) : quadForm M x = x ⬝ᵥ (M *ᵥ x) := by
  unfold quadForm dotProduct
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The key perturbation bound: for `d` bounding `|xᵢ - yᵢ|` and `s`
bounding `|xᵢ + yᵢ|` coordinatewise,
`|xᵀMx - yᵀMy| ≤ d · s · ∑ᵢⱼ|Mᵢⱼ|`. This is the polarisation estimate
`xᵢxⱼ - yᵢyⱼ = ((xᵢ-yᵢ)(xⱼ+yⱼ) + (xᵢ+yᵢ)(xⱼ-yⱼ))/2` summed against `|Mᵢⱼ|`. -/
theorem quadForm_sub_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (x y : Fin n → ℚ) {d s : ℚ}
    (hdiff : ∀ i, |x i - y i| ≤ d) (hsum : ∀ i, |x i + y i| ≤ s) :
    |quadForm M x - quadForm M y| ≤ d * s * ∑ i, ∑ j, |M i j| := by
  have key : ∀ i j, |x i * x j - y i * y j| ≤ d * s := by
    intro i j
    have hd : 0 ≤ d := le_trans (abs_nonneg _) (hdiff i)
    have hs : 0 ≤ s := le_trans (abs_nonneg _) (hsum i)
    have hident : x i * x j - y i * y j =
        ((x i - y i) * (x j + y j) + (x i + y i) * (x j - y j)) / 2 := by ring
    have h1 : |(x i - y i) * (x j + y j)| ≤ d * s := by
      rw [abs_mul]
      exact mul_le_mul (hdiff i) (hsum j) (abs_nonneg _) hd
    have h2 : |(x i + y i) * (x j - y j)| ≤ s * d := by
      rw [abs_mul]
      exact mul_le_mul (hsum i) (hdiff j) (abs_nonneg _) hs
    calc |x i * x j - y i * y j|
        = |((x i - y i) * (x j + y j) + (x i + y i) * (x j - y j)) / 2| := by
          rw [hident]
      _ = |(x i - y i) * (x j + y j) + (x i + y i) * (x j - y j)| / 2 := by
          rw [abs_div]
          norm_num
      _ ≤ (d * s + s * d) / 2 := by
          apply (div_le_div_iff_of_pos_right (by norm_num : (0:ℚ) < 2)).mpr
          linarith [abs_add_le ((x i - y i) * (x j + y j))
            ((x i + y i) * (x j - y j))]
      _ = d * s := by ring
  have hdecomp : quadForm M x - quadForm M y =
      ∑ i, ∑ j, M i j * (x i * x j - y i * y j) := by
    unfold quadForm
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hdecomp]
  calc |∑ i, ∑ j, M i j * (x i * x j - y i * y j)|
      ≤ ∑ i, |∑ j, M i j * (x i * x j - y i * y j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |M i j * (x i * x j - y i * y j)| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |M i j| * (d * s) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (key i j) (abs_nonneg _)
    _ = ∑ i, (∑ j, |M i j|) * (d * s) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (Finset.sum_mul _ _ _).symm
    _ = (∑ i, ∑ j, |M i j|) * (d * s) := (Finset.sum_mul _ _ _).symm
    _ = d * s * ∑ i, ∑ j, |M i j| := mul_comm _ _

/-- The perturbation bound in sup-norm form:
`|xᵀMx - yᵀMy| ≤ ‖x-y‖∞ · ‖x+y‖∞ · ‖M‖_{∑|·|}`. -/
theorem quadForm_sub_abs_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (x y : Fin n → ℚ) :
    |quadForm M x - quadForm M y| ≤
      vecInfNorm (x - y) * vecInfNorm (x + y) * matSumNorm M :=
  quadForm_sub_le M x y (fun i => abs_le_vecInfNorm _ i)
    (fun i => abs_le_vecInfNorm _ i)

/-- Truncating the argument of a quadratic form perturbs it by at most
`2^{-B} · s · ∑ᵢⱼ|Mᵢⱼ|` whenever `s` bounds `|xᵢ + (truncVec x B)ᵢ|`. -/
theorem quadForm_truncVec_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (x : Fin n → ℚ) (B : ℕ) {s : ℚ}
    (hsum : ∀ i, |x i + truncVec x B i| ≤ s) :
    |quadForm M x - quadForm M (truncVec x B)| ≤
      (1 / 2 ^ B) * s * matSumNorm M :=
  quadForm_sub_le M x (truncVec x B) (fun _i => abs_sub_trunc _ _) hsum

/-- On the unit cube (`|xᵢ| ≤ 1`) the truncated quadratic form is within
`2^{1-B} · ∑ᵢⱼ|Mᵢⱼ|` of the original. -/
theorem quadForm_truncVec_le_of_cube {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (x : Fin n → ℚ) (B : ℕ) (hx : ∀ i, |x i| ≤ 1) :
    |quadForm M x - quadForm M (truncVec x B)| ≤
      (1 / 2 ^ B) * 2 * matSumNorm M := by
  apply quadForm_truncVec_le M x B
  intro i
  calc |x i + truncVec x B i| ≤ |x i| + |truncVec x B i| := abs_add_le _ _
    _ ≤ 1 + 1 := add_le_add (hx i) ((abs_truncVec_le x B i).trans (hx i))
    _ = 2 := by norm_num

/-- The `vecInfNorm` version: `‖x - truncVec x B‖∞ ≤ 1/2^B` directly feeds
the sup-norm perturbation bound. -/
theorem quadForm_truncVec_vecInfNorm_le {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) (B : ℕ) :
    |quadForm M x - quadForm M (truncVec x B)| ≤
      (1 / 2 ^ B) * vecInfNorm (x + truncVec x B) * matSumNorm M := by
  have h := quadForm_sub_abs_le M x (truncVec x B)
  have hd : vecInfNorm (x - truncVec x B) ≤ 1 / 2 ^ B :=
    vecInfNorm_sub_truncVec_le x B
  have h1 : vecInfNorm (x - truncVec x B) * vecInfNorm (x + truncVec x B) *
        matSumNorm M ≤
      (1 / 2 ^ B) * vecInfNorm (x + truncVec x B) * matSumNorm M :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hd (vecInfNorm_nonneg _))
      (matSumNorm_nonneg M)
  exact h.trans h1

/-- The quadratic form is `Rat.cast`-compatible: the cast equals the real
double sum. -/
theorem quadForm_cast {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (x : Fin n → ℚ) :
    ((quadForm M x : ℚ) : ℝ) =
      ∑ i, ∑ j, (x i : ℝ) * (M i j : ℝ) * (x j : ℝ) := by
  unfold quadForm
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  rfl

/-- The real-valued version of `quadForm_truncVec_le_of_cube`: on the unit
cube, truncating `x` moves `xᵀMx` by at most `2^{1-B} · ∑ᵢⱼ|Mᵢⱼ|` over `ℝ`. -/
theorem quadForm_truncVec_le_real {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    {x : Fin n → ℚ} (hx : ∀ i, |x i| ≤ 1) (B : ℕ) :
    |(∑ i, ∑ j, (x i : ℝ) * (M i j : ℝ) * (x j : ℝ)) -
        ∑ i, ∑ j, (truncVec x B i : ℝ) * (M i j : ℝ) *
          (truncVec x B j : ℝ)| ≤
      (1 : ℝ) / 2 ^ B * 2 * ∑ i, ∑ j, |(M i j : ℝ)| := by
  have h := quadForm_truncVec_le_of_cube M x B hx
  have h1 : |(∑ i, ∑ j, (x i : ℝ) * (M i j : ℝ) * (x j : ℝ)) -
        ∑ i, ∑ j, (truncVec x B i : ℝ) * (M i j : ℝ) *
          (truncVec x B j : ℝ)| =
      ((|quadForm M x - quadForm M (truncVec x B)| : ℚ) : ℝ) := by
    rw [← quadForm_cast, ← quadForm_cast, ← Rat.cast_sub, Rat.cast_abs]
  rw [h1]
  have h2 : ((1 / 2 ^ B * 2 * ∑ i, ∑ j, |M i j| : ℚ) : ℝ) =
      (1 : ℝ) / 2 ^ B * 2 * ∑ i, ∑ j, |(M i j : ℝ)| := by
    push_cast
    rfl
  calc ((|quadForm M x - quadForm M (truncVec x B)| : ℚ) : ℝ)
      ≤ ((1 / 2 ^ B * 2 * ∑ i, ∑ j, |M i j| : ℚ) : ℝ) := by exact_mod_cast h
    _ = (1 : ℝ) / 2 ^ B * 2 * ∑ i, ∑ j, |(M i j : ℝ)| := h2

/-- The PSD corollary: a nonnegative value of the truncated quadratic form
certifies the original form up to the perturbation envelope —
`xᵀMx ≥ -2^{-B} · s · ‖M‖` whenever `(truncVec x)ᵀM(truncVec x) ≥ 0`. -/
theorem quadForm_trunc_lower_bound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (x : Fin n → ℚ) (B : ℕ) {s : ℚ}
    (hsum : ∀ i, |x i + truncVec x B i| ≤ s)
    (hM : 0 ≤ quadForm M (truncVec x B)) :
    -(1 / 2 ^ B) * s * matSumNorm M ≤ quadForm M x := by
  have h := quadForm_truncVec_le M x B hsum
  rw [abs_le] at h
  linarith

/-! ## Bit-size bookkeeping for `trunc` -/

/-- The denominator of a truncated rational divides `2^B` — truncation stays
on the dyadic grid, which is what keeps the bit length controllable. -/
theorem trunc_den_dvd (q : ℚ) (B : ℕ) : (trunc q B).den ∣ 2 ^ B := by
  rw [trunc_eq_divInt]
  exact Int.natCast_dvd_natCast.mp (Rat.den_dvd _ _)

theorem trunc_den_le (q : ℚ) (B : ℕ) : (trunc q B).den ≤ 2 ^ B :=
  Nat.le_of_dvd (Nat.two_pow_pos B) (trunc_den_dvd q B)

/-- `natBitSize (2^B) = B + 1`. -/
theorem natBitSize_two_pow (B : ℕ) : natBitSize (2 ^ B) = B + 1 := by
  unfold natBitSize
  rw [Nat.log_pow Nat.one_lt_two]

/-- The denominator of `trunc q B` costs at most `B + 1` bits. -/
theorem natBitSize_trunc_den_le (q : ℚ) (B : ℕ) :
    natBitSize (trunc q B).den ≤ B + 1 := by
  calc natBitSize (trunc q B).den ≤ natBitSize (2 ^ B) :=
        natBitSize_mono (trunc_den_le q B)
    _ = B + 1 := natBitSize_two_pow B

/-- `|q| ≤ q.num.natAbs` as rationals: `|q| = |num|/den` and `den ≥ 1`. -/
theorem abs_le_num_natAbs (q : ℚ) : |q| ≤ (q.num.natAbs : ℚ) := by
  have hdpos : (0 : ℚ) < (((q.den : ℤ)) : ℚ) := by exact_mod_cast q.den_pos
  have hnum : (q.num : ℚ) = q * (((q.den : ℤ)) : ℚ) := by
    have h := Rat.num_divInt_den q
    rw [Rat.divInt_eq_div] at h
    exact (div_eq_iff hdpos.ne').mp h
  rw [Int.cast_natCast] at hnum
  have hden' : |(q.den : ℚ)| = (q.den : ℚ) :=
    abs_of_pos (Nat.cast_pos.mpr q.den_pos)
  have habs : (q.num.natAbs : ℚ) = |q| * (q.den : ℚ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, hnum, abs_mul, hden']
  rw [habs]
  conv_lhs => rw [← mul_one |q|]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg q)
  have h := Nat.succ_le_of_lt q.den_pos
  exact_mod_cast h

/-- The numerator of a truncated rational is controlled by the magnitude of
the input: `|(trunc q B).num| ≤ |q| · 2^B`. -/
theorem trunc_num_abs_le (q : ℚ) (B : ℕ) :
    ((trunc q B).num.natAbs : ℚ) ≤ |q| * 2 ^ B := by
  have hdpos : (0 : ℚ) < (((trunc q B).den : ℤ) : ℚ) := by
    exact_mod_cast (trunc q B).den_pos
  have hnum : ((trunc q B).num : ℚ) =
      trunc q B * (((trunc q B).den : ℤ) : ℚ) := by
    have h := Rat.num_divInt_den (trunc q B)
    rw [Rat.divInt_eq_div] at h
    exact (div_eq_iff hdpos.ne').mp h
  rw [Int.cast_natCast] at hnum
  have hden' : |((trunc q B).den : ℚ)| = ((trunc q B).den : ℚ) :=
    abs_of_pos (Nat.cast_pos.mpr (trunc q B).den_pos)
  have habs : ((trunc q B).num.natAbs : ℚ) =
      |trunc q B| * ((trunc q B).den : ℚ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, hnum, abs_mul, hden']
  have hdenle : ((trunc q B).den : ℚ) ≤ 2 ^ B := by
    exact_mod_cast trunc_den_le q B
  rw [habs]
  exact mul_le_mul (abs_trunc_le q B) hdenle (Nat.cast_nonneg _) (abs_nonneg _)

/-- The scaled floor `⌊|q|·2^B⌋` is nonnegative. -/
private theorem floor_abs_mul_pow_nonneg (q : ℚ) (B : ℕ) :
    0 ≤ ⌊|q| * 2 ^ B⌋ :=
  Int.floor_nonneg.mpr
    (mul_nonneg (abs_nonneg _) (by positivity : (0 : ℚ) ≤ 2 ^ B))

/-- Casting the `toNat` of the nonnegative scaled floor back to `ℚ`
recovers the floor. -/
private theorem floor_abs_toNat_cast (q : ℚ) (B : ℕ) :
    ((⌊|q| * 2 ^ B⌋).toNat : ℚ) = (⌊|q| * 2 ^ B⌋ : ℚ) := by
  have h := Int.toNat_of_nonneg (floor_abs_mul_pow_nonneg q B)
  have h' := congrArg (fun z : ℤ => (z : ℚ)) h
  rw [Int.cast_natCast] at h'
  exact h'

/-- The natural bound `(trunc q B).num.natAbs ≤ ⌊|q|·2^B⌋.toNat`. -/
theorem trunc_num_natAbs_le (q : ℚ) (B : ℕ) :
    (trunc q B).num.natAbs ≤ (⌊|q| * 2 ^ B⌋).toNat := by
  have h1 : ((trunc q B).num.natAbs : ℚ) ≤ |q| * 2 ^ B := trunc_num_abs_le q B
  have hnn : 0 ≤ ⌊|q| * 2 ^ B⌋ := floor_abs_mul_pow_nonneg q B
  have h' : ((trunc q B).num.natAbs : ℚ) < (⌊|q| * 2 ^ B⌋ : ℚ) + 1 :=
    lt_of_le_of_lt h1 (Int.lt_floor_add_one _)
  have h3 : (((trunc q B).num.natAbs : ℤ) : ℚ) <
      ((⌊|q| * 2 ^ B⌋ + 1 : ℤ) : ℚ) := by
    rw [Int.cast_natCast, Int.cast_add, Int.cast_one]
    exact h'
  have h6 : ((trunc q B).num.natAbs : ℤ) ≤ ⌊|q| * 2 ^ B⌋ :=
    Int.lt_add_one_iff.mp (Int.cast_lt.mp h3)
  omega

/-- `natBitSize (a · 2^B) = natBitSize a + B` for `a > 0`: multiplying by a
power of two shifts the binary length by exactly `B`. -/
theorem natBitSize_mul_two_pow {a : ℕ} (ha : 0 < a) (B : ℕ) :
    natBitSize (a * 2 ^ B) = natBitSize a + B := by
  have hlog : Nat.log 2 (a * 2 ^ B) = Nat.log 2 a + B := by
    refine Nat.log_eq_of_pow_le_of_lt_pow ?_ ?_
    · rw [pow_add]
      exact Nat.mul_le_mul (Nat.pow_log_le_self 2 ha.ne') le_rfl
    · rw [show Nat.log 2 a + B + 1 = Nat.log 2 a + 1 + B by omega, pow_add]
      exact (Nat.mul_lt_mul_right (Nat.two_pow_pos B)).mpr
        (Nat.lt_pow_succ_log_self Nat.one_lt_two a)
  unfold natBitSize
  rw [hlog]
  omega

/-- The `≤` form, also valid for `a = 0`. -/
theorem natBitSize_mul_two_pow_le {a : ℕ} (B : ℕ) :
    natBitSize (a * 2 ^ B) ≤ natBitSize a + B := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [natBitSize]
  · rw [natBitSize_mul_two_pow ha B]

/-- The scaled floor fits in the original numerator's magnitude times
`2^B`: `⌊|q|·2^B⌋.toNat ≤ q.num.natAbs · 2^B`. -/
theorem trunc_floor_toNat_le (q : ℚ) (B : ℕ) :
    (⌊|q| * 2 ^ B⌋).toNat ≤ q.num.natAbs * 2 ^ B := by
  have h1 : (⌊|q| * 2 ^ B⌋ : ℚ) ≤ |q| * 2 ^ B := Int.floor_le _
  have h2 : |q| * 2 ^ B ≤ (q.num.natAbs : ℚ) * 2 ^ B :=
    mul_le_mul_of_nonneg_right (abs_le_num_natAbs q) (by positivity)
  have h3 : ((⌊|q| * 2 ^ B⌋).toNat : ℚ) ≤ ((q.num.natAbs * 2 ^ B : ℕ) : ℚ) := by
    rw [floor_abs_toNat_cast]
    have h4 : ((q.num.natAbs * 2 ^ B : ℕ) : ℚ) = (q.num.natAbs : ℚ) * 2 ^ B := by
      push_cast
      rfl
    rw [h4]
    exact le_trans h1 h2
  exact_mod_cast h3

/-- Bit size of a truncated rational: the numerator needs at most the bits
of `⌊|q|·2^B⌋` and the denominator at most `B + 1` bits. -/
theorem ratBitSize_trunc_le (q : ℚ) (B : ℕ) :
    ratBitSize (trunc q B) ≤ natBitSize (⌊|q| * 2 ^ B⌋).toNat + (B + 1) := by
  unfold ratBitSize
  have h1 := natBitSize_mono (trunc_num_natAbs_le q B)
  have h2 := natBitSize_trunc_den_le q B
  omega

/-- The App F bit-size bound: truncating `q` to `B` dyadic bits costs at
most `natBitSize |q.num| + 2B + 1` bits — the denominator contributes `B+1`
and the scaled numerator at most `natBitSize |num| + B`. -/
theorem ratBitSize_trunc_le' (q : ℚ) (B : ℕ) :
    ratBitSize (trunc q B) ≤ natBitSize q.num.natAbs + 2 * B + 1 := by
  calc ratBitSize (trunc q B)
      ≤ natBitSize (⌊|q| * 2 ^ B⌋).toNat + (B + 1) :=
        ratBitSize_trunc_le q B
    _ ≤ natBitSize (q.num.natAbs * 2 ^ B) + (B + 1) :=
        Nat.add_le_add_right
          (natBitSize_mono (trunc_floor_toNat_le q B)) _
    _ ≤ natBitSize q.num.natAbs + 2 * B + 1 := by
        have := natBitSize_mul_two_pow_le (a := q.num.natAbs) (B := B)
        omega

/-- Headline form: `ratBitSize (trunc q B) ≤ ratBitSize q + 2B` —
truncating to `B` dyadic bits inflates the rational bit size by at most
`2B`. This is the per-entry bound behind the polynomial bit-size envelope
(`L_poly`) of Appendix F. -/
theorem ratBitSize_trunc_le_add (q : ℚ) (B : ℕ) :
    ratBitSize (trunc q B) ≤ ratBitSize q + 2 * B := by
  have h1 := ratBitSize_trunc_le' q B
  have h2 : natBitSize q.num.natAbs + 1 ≤ ratBitSize q := by
    unfold ratBitSize
    have := natBitSize_pos q.den
    omega
  omega

/-- Entrywise truncation inflates the input bit size of an `m × n` matrix by
at most `m · n · 2B`. -/
theorem inputBitSize_truncMat_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (B : ℕ) : inputBitSize (truncMat A B) ≤ inputBitSize A + m * n * (2 * B) := by
  calc inputBitSize (truncMat A B)
      = ∑ i, ∑ j, ratBitSize (trunc (A i j) B) := rfl
    _ ≤ ∑ i, ∑ j, (ratBitSize (A i j) + 2 * B) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          ratBitSize_trunc_le_add (A i j) B
    _ = inputBitSize A + m * n * (2 * B) := by
        unfold inputBitSize
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, Nat.nsmul_eq_mul]
        ring

end Komlos
