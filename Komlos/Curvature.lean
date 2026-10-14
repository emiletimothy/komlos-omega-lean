import Komlos.MatrixInverse
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Weight calculus and potential curvature

The weight function `weight u = 119 / (1 - u/20000)^10000` from equation (2.3),
its first two derivatives, derivative comparisons, and the relative-change
bounds used in the stability argument of Appendix B.
-/

namespace Komlos

open scoped BigOperators Matrix.Norms.Frobenius Topology
open Filter Matrix

/-! ## Weight derivatives -/

noncomputable def weightDeriv (u : ℝ) : ℝ :=
  (119 / 2) / (1 - u / 20000) ^ 10001

noncomputable def weightDeriv2 (u : ℝ) : ℝ :=
  (119 * 10001 / 40000) / (1 - u / 20000) ^ 10002

theorem hasDerivAt_weight {u : ℝ} (hu : (1 - u / 20000) ≠ 0) :
    HasDerivAt weight (weightDeriv u) u := by
  have hinner := (hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_id' u).div_const 20000)
  have hdiv := (hasDerivAt_const u (119 : ℝ)).div (hinner.pow 10000) (pow_ne_zero _ hu)
  apply hdiv.congr_deriv
  simp only [Pi.sub_apply, Pi.pow_apply]
  unfold weightDeriv
  generalize hw : 1 - u / 20000 = w
  have hwne : w ≠ 0 := by rw [← hw]; exact hu
  field_simp [hwne]
  try ring

theorem hasDerivAt_weightDeriv {u : ℝ} (hu : (1 - u / 20000) ≠ 0) :
    HasDerivAt weightDeriv (weightDeriv2 u) u := by
  have hinner := (hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_id' u).div_const 20000)
  have hdiv := (hasDerivAt_const u (119 / 2 : ℝ)).div (hinner.pow 10001) (pow_ne_zero _ hu)
  apply hdiv.congr_deriv
  simp only [Pi.sub_apply, Pi.pow_apply]
  unfold weightDeriv2
  generalize hw : 1 - u / 20000 = w
  have hwne : w ≠ 0 := by rw [← hw]; exact hu
  field_simp [hwne]
  try ring

theorem weightDeriv_eq {u : ℝ} (_hu : (1 - u / 20000) ≠ 0) :
    weightDeriv u = weight u / (2 * (1 - u / 20000)) := by
  unfold weightDeriv weight
  generalize hw : 1 - u / 20000 = w
  rw [pow_succ]
  field_simp
  try ring

theorem weightDeriv_nonneg {u : ℝ} (hu : u ≤ 0) : 0 ≤ weightDeriv u := by
  apply div_nonneg (by norm_num)
  exact pow_pos (by linarith) _ |>.le

theorem weightDeriv_pos {u : ℝ} (hu : u ≤ 0) : 0 < weightDeriv u := by
  apply div_pos (by norm_num)
  exact pow_pos (by linarith) _

theorem weightDeriv2_pos {u : ℝ} (hu : u ≤ 0) : 0 < weightDeriv2 u := by
  apply div_pos (by norm_num)
  exact pow_pos (by linarith) _

theorem weightDeriv_le_weight_half {u : ℝ} (hu : u ≤ 0) :
    weightDeriv u ≤ weight u / 2 := by
  have hw : (1 : ℝ) ≤ 1 - u / 20000 := by linarith
  rw [weightDeriv_eq (by linarith : (1 - u / 20000) ≠ 0)]
  calc
    weight u / (2 * (1 - u / 20000)) ≤ weight u / (2 * 1) := by
      apply div_le_div_of_nonneg_left (weight_pos hu).le (by norm_num)
      linarith
    _ = weight u / 2 := by ring_nf

theorem weightDeriv2_ratio {u : ℝ} (_hu : (1 - u / 20000) ≠ 0) :
    weightDeriv2 u = weightDeriv u * (10001 / 20000) / (1 - u / 20000) := by
  unfold weightDeriv2 weightDeriv
  generalize hw : 1 - u / 20000 = w
  rw [pow_succ]
  field_simp
  try ring

theorem weightDeriv2_le {u : ℝ} (hu : u ≤ 0) :
    weightDeriv2 u ≤ weightDeriv u * ((1 + 1 / 10000) / 2) := by
  have hw : (1 : ℝ) ≤ 1 - u / 20000 := by linarith
  rw [weightDeriv2_ratio (by linarith : (1 - u / 20000) ≠ 0), mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (weightDeriv_nonneg hu)
  calc
    (10001 / 20000) / (1 - u / 20000) = 10001 / (20000 * (1 - u / 20000)) := by
      rw [div_div]
    _ ≤ 10001 / (20000 * 1) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith
    _ = (1 + 1 / 10000) / 2 := by norm_num

/-! ## Relative weight change -/

theorem one_sub_inv_pow_le_exp (K : ℕ) {y : ℝ} (_hy0 : 0 ≤ y) (hy1 : y < 1) :
    ((1 - y)⁻¹) ^ K ≤ Real.exp (K * y / (1 - y)) := by
  have h1y : (0 : ℝ) < 1 - y := sub_pos.mpr hy1
  have hlog : -Real.log (1 - y) ≤ y / (1 - y) := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h1y)
    rw [Real.log_inv] at h
    have he : (1 - y)⁻¹ - 1 = y / (1 - y) := by field_simp; ring
    linarith
  have hpow : ((1 - y)⁻¹) ^ K = Real.exp (K * (-Real.log (1 - y))) := by
    conv_lhs => rw [← Real.exp_log (inv_pos.mpr h1y)]
    rw [Real.log_inv, ← Real.exp_nat_mul]
  rw [hpow]
  apply Real.exp_le_exp.mpr
  calc
    (K : ℝ) * (-Real.log (1 - y)) ≤ K * (y / (1 - y)) :=
      mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg K)
    _ = K * y / (1 - y) := (mul_div_assoc _ _ _).symm

/-- `(a / (b * c) ^ n)` splits into `a / b ^ n` times `(c⁻¹) ^ n`; no nonzero
hypotheses are needed since division is total. -/
theorem div_mul_pow {a b c : ℝ} (n : ℕ) :
    a / (b * c) ^ n = (a / b ^ n) * (c⁻¹) ^ n := by
  rw [mul_pow, inv_pow, inv_eq_one_div, div_mul_div_comm, mul_one]

theorem weight_relative_change {u δ : ℝ} (hδ : 0 ≤ δ) (hud : u + δ ≤ 0) :
    weight (u + δ) ≤ Real.exp (δ / 2) * weight u := by
  have hu : u ≤ 0 := by linarith
  set w := 1 - u / 20000 with hw
  set w' := 1 - (u + δ) / 20000 with hw'
  have hw1 : (1 : ℝ) ≤ w := by linarith
  have hw'1 : (1 : ℝ) ≤ w' := by linarith
  have hwpos : (0 : ℝ) < w := by linarith
  have hw'pos : (0 : ℝ) < w' := by linarith
  have hpos2w : (0 : ℝ) < 20000 * w := by linarith
  set y := δ / (20000 * w) with hy
  have hwy : w * y = δ / 20000 := by
    rw [hy]
    field_simp [hwpos.ne']
    try ring
  have hw'eq : w' = w * (1 - y) := by
    rw [hw', mul_sub, mul_one, hwy, hw]
    ring
  have hy0 : 0 ≤ y := div_nonneg hδ (by linarith)
  have hy1 : y < 1 := by
    rw [hy, div_lt_one hpos2w]
    have hdu : δ ≤ -u := by linarith
    have hw20000 : 20000 * w = 20000 - u := by rw [hw]; ring
    linarith
  have h1y : 1 - δ / (20000 * w) = w' / w := by
    have hw'eq' : w' = w * (1 - δ / (20000 * w)) := by
      rw [← hy]; exact hw'eq
    rw [hw'eq', ← hy]
    field_simp [hwpos.ne']
    try ring
  have hratio : weight (u + δ) = weight u * ((1 - y)⁻¹) ^ 10000 := by
    unfold weight
    rw [← hw, ← hw', hw'eq]
    exact div_mul_pow 10000
  have hexp : 10000 * y / (1 - y) = δ / (2 * w') := by
    rw [hy, h1y]
    field_simp [hwpos.ne', hw'pos.ne']
    try ring
  rw [hratio]
  calc
    weight u * ((1 - y)⁻¹) ^ 10000 ≤ weight u * Real.exp (10000 * y / (1 - y)) :=
      mul_le_mul_of_nonneg_left (one_sub_inv_pow_le_exp 10000 hy0 hy1)
        (weight_pos hu).le
    _ ≤ weight u * Real.exp (δ / 2) := by
      apply mul_le_mul_of_nonneg_left _ (weight_pos hu).le
      apply Real.exp_le_exp.mpr
      rw [hexp]
      apply div_le_div_of_nonneg_left hδ (by norm_num)
      linarith
    _ = Real.exp (δ / 2) * weight u := mul_comm _ _

theorem weightDeriv_relative_change {u δ : ℝ} (hδ : 0 ≤ δ) (hud : u + δ ≤ 0) :
    weightDeriv (u + δ) ≤ Real.exp (δ * 10001 / 20000) * weightDeriv u := by
  have hu : u ≤ 0 := by linarith
  set w := 1 - u / 20000 with hw
  set w' := 1 - (u + δ) / 20000 with hw'
  have hw1 : (1 : ℝ) ≤ w := by linarith
  have hw'1 : (1 : ℝ) ≤ w' := by linarith
  have hwpos : (0 : ℝ) < w := by linarith
  have hw'pos : (0 : ℝ) < w' := by linarith
  have hpos2w : (0 : ℝ) < 20000 * w := by linarith
  set y := δ / (20000 * w) with hy
  have hwy : w * y = δ / 20000 := by
    rw [hy]
    field_simp [hwpos.ne']
    try ring
  have hw'eq : w' = w * (1 - y) := by
    rw [hw', mul_sub, mul_one, hwy, hw]
    ring
  have hy0 : 0 ≤ y := div_nonneg hδ (by linarith)
  have hy1 : y < 1 := by
    rw [hy, div_lt_one hpos2w]
    have hdu : δ ≤ -u := by linarith
    have hw20000 : 20000 * w = 20000 - u := by rw [hw]; ring
    linarith
  have h1y : 1 - δ / (20000 * w) = w' / w := by
    have hw'eq' : w' = w * (1 - δ / (20000 * w)) := by
      rw [← hy]; exact hw'eq
    rw [hw'eq', ← hy]
    field_simp [hwpos.ne']
    try ring
  have hratio : weightDeriv (u + δ) = weightDeriv u * ((1 - y)⁻¹) ^ 10001 := by
    unfold weightDeriv
    rw [← hw, ← hw', hw'eq]
    exact div_mul_pow 10001
  have hexp : 10001 * y / (1 - y) = δ * 10001 / (20000 * w') := by
    rw [hy, h1y]
    field_simp [hwpos.ne', hw'pos.ne']
    try ring
  rw [hratio]
  calc
    weightDeriv u * ((1 - y)⁻¹) ^ 10001 ≤
        weightDeriv u * Real.exp (10001 * y / (1 - y)) :=
      mul_le_mul_of_nonneg_left (one_sub_inv_pow_le_exp 10001 hy0 hy1)
        (weightDeriv_pos hu).le
    _ ≤ weightDeriv u * Real.exp (δ * 10001 / 20000) := by
      apply mul_le_mul_of_nonneg_left _ (weightDeriv_pos hu).le
      apply Real.exp_le_exp.mpr
      rw [hexp]
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
      linarith
    _ = Real.exp (δ * 10001 / 20000) * weightDeriv u := mul_comm _ _

theorem weightDeriv2_relative_change {u δ : ℝ} (hδ : 0 ≤ δ) (hud : u + δ ≤ 0) :
    weightDeriv2 (u + δ) ≤ Real.exp (δ * 10002 / 20000) * weightDeriv2 u := by
  have hu : u ≤ 0 := by linarith
  set w := 1 - u / 20000 with hw
  set w' := 1 - (u + δ) / 20000 with hw'
  have hw1 : (1 : ℝ) ≤ w := by linarith
  have hw'1 : (1 : ℝ) ≤ w' := by linarith
  have hwpos : (0 : ℝ) < w := by linarith
  have hw'pos : (0 : ℝ) < w' := by linarith
  have hpos2w : (0 : ℝ) < 20000 * w := by linarith
  set y := δ / (20000 * w) with hy
  have hwy : w * y = δ / 20000 := by
    rw [hy]
    field_simp [hwpos.ne']
    try ring
  have hw'eq : w' = w * (1 - y) := by
    rw [hw', mul_sub, mul_one, hwy, hw]
    ring
  have hy0 : 0 ≤ y := div_nonneg hδ (by linarith)
  have hy1 : y < 1 := by
    rw [hy, div_lt_one hpos2w]
    have hdu : δ ≤ -u := by linarith
    have hw20000 : 20000 * w = 20000 - u := by rw [hw]; ring
    linarith
  have h1y : 1 - δ / (20000 * w) = w' / w := by
    have hw'eq' : w' = w * (1 - δ / (20000 * w)) := by
      rw [← hy]; exact hw'eq
    rw [hw'eq', ← hy]
    field_simp [hwpos.ne']
    try ring
  have hratio : weightDeriv2 (u + δ) = weightDeriv2 u * ((1 - y)⁻¹) ^ 10002 := by
    unfold weightDeriv2
    rw [← hw, ← hw', hw'eq]
    exact div_mul_pow 10002
  have hexp : 10002 * y / (1 - y) = δ * 10002 / (20000 * w') := by
    rw [hy, h1y]
    field_simp [hwpos.ne', hw'pos.ne']
    try ring
  rw [hratio]
  calc
    weightDeriv2 u * ((1 - y)⁻¹) ^ 10002 ≤
        weightDeriv2 u * Real.exp (10002 * y / (1 - y)) :=
      mul_le_mul_of_nonneg_left (one_sub_inv_pow_le_exp 10002 hy0 hy1)
        (weightDeriv2_pos hu).le
    _ ≤ weightDeriv2 u * Real.exp (δ * 10002 / 20000) := by
      apply mul_le_mul_of_nonneg_left _ (weightDeriv2_pos hu).le
      apply Real.exp_le_exp.mpr
      rw [hexp]
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
      linarith
    _ = Real.exp (δ * 10002 / 20000) * weightDeriv2 u := mul_comm _ _

/-! ## Two-sided weight stability (Appendix A)

The paper states that changing a nonpositive barrier by at most `a ≤ 1`
changes `ν`, `ν′`, `ν″` by factors `exp(O(a))`.  For `ν` the factor is
`exp(a/2)`; for `ν′` and `ν″` the exponents pick up `10001/20000` and
`10002/20000` respectively. -/

theorem weight_abs_change {u v a : ℝ} (hu : u ≤ 0) (hv : v ≤ 0)
    (ha : 0 ≤ a) (h : |v - u| ≤ a) :
    weight v ≤ Real.exp (a / 2) * weight u := by
  rcases le_total u v with huv | huv
  · have hδ : (0 : ℝ) ≤ v - u := by linarith
    have hstep := weight_relative_change hδ (by linarith : u + (v - u) ≤ 0)
    have hle : Real.exp ((v - u) / 2) ≤ Real.exp (a / 2) :=
      Real.exp_le_exp.mpr (by linarith [le_trans (le_abs_self (v - u)) h])
    calc weight v = weight (u + (v - u)) := by rw [show u + (v - u) = v by ring]
      _ ≤ Real.exp ((v - u) / 2) * weight u := hstep
      _ ≤ Real.exp (a / 2) * weight u :=
        mul_le_mul_of_nonneg_right hle (weight_pos hu).le
  · calc weight v ≤ weight u := weight_mono huv hu
      _ ≤ Real.exp (a / 2) * weight u :=
        le_mul_of_one_le_left (weight_pos hu).le
          (Real.one_le_exp (by linarith))

theorem weightDeriv_abs_change {u v a : ℝ} (hu : u ≤ 0) (hv : v ≤ 0)
    (ha : 0 ≤ a) (h : |v - u| ≤ a) :
    weightDeriv v ≤ Real.exp (a * 10001 / 20000) * weightDeriv u := by
  rcases le_total u v with huv | huv
  · have hδ : (0 : ℝ) ≤ v - u := by linarith
    have hstep := weightDeriv_relative_change hδ
      (by linarith : u + (v - u) ≤ 0)
    have hle : Real.exp ((v - u) * 10001 / 20000) ≤
        Real.exp (a * 10001 / 20000) :=
      Real.exp_le_exp.mpr (by linarith [le_trans (le_abs_self (v - u)) h])
    calc weightDeriv v = weightDeriv (u + (v - u)) := by rw [show u + (v - u) = v by ring]
      _ ≤ Real.exp ((v - u) * 10001 / 20000) * weightDeriv u := hstep
      _ ≤ Real.exp (a * 10001 / 20000) * weightDeriv u :=
        mul_le_mul_of_nonneg_right hle (weightDeriv_pos hu).le
  · calc weightDeriv v ≤ weightDeriv u := by
          apply (div_le_div_iff_of_pos_left (by norm_num : (0:ℝ) < 119 / 2)
            (pow_pos (by linarith : (0:ℝ) < 1 - v / 20000) _)
            (pow_pos (by linarith : (0:ℝ) < 1 - u / 20000) _)).mpr
          have hle : (1 - u / 20000) ≤ 1 - v / 20000 := by linarith
          exact pow_le_pow_left₀ (by linarith) hle _
      _ ≤ Real.exp (a * 10001 / 20000) * weightDeriv u :=
        le_mul_of_one_le_left (weightDeriv_nonneg hu)
          (Real.one_le_exp (by linarith))

theorem weightDeriv2_abs_change {u v a : ℝ} (hu : u ≤ 0) (hv : v ≤ 0)
    (ha : 0 ≤ a) (h : |v - u| ≤ a) :
    weightDeriv2 v ≤ Real.exp (a * 10002 / 20000) * weightDeriv2 u := by
  rcases le_total u v with huv | huv
  · have hδ : (0 : ℝ) ≤ v - u := by linarith
    have hstep := weightDeriv2_relative_change hδ
      (by linarith : u + (v - u) ≤ 0)
    have hle : Real.exp ((v - u) * 10002 / 20000) ≤
        Real.exp (a * 10002 / 20000) :=
      Real.exp_le_exp.mpr (by linarith [le_trans (le_abs_self (v - u)) h])
    calc weightDeriv2 v = weightDeriv2 (u + (v - u)) := by rw [show u + (v - u) = v by ring]
      _ ≤ Real.exp ((v - u) * 10002 / 20000) * weightDeriv2 u := hstep
      _ ≤ Real.exp (a * 10002 / 20000) * weightDeriv2 u :=
        mul_le_mul_of_nonneg_right hle (weightDeriv2_pos hu).le
  · calc weightDeriv2 v ≤ weightDeriv2 u := by
          apply (div_le_div_iff_of_pos_left (by norm_num :
              (0:ℝ) < 119 * 10001 / 40000)
            (pow_pos (by linarith : (0:ℝ) < 1 - v / 20000) _)
            (pow_pos (by linarith : (0:ℝ) < 1 - u / 20000) _)).mpr
          have hle : (1 - u / 20000) ≤ 1 - v / 20000 := by linarith
          exact pow_le_pow_left₀ (by linarith) hle _
      _ ≤ Real.exp (a * 10002 / 20000) * weightDeriv2 u :=
        le_mul_of_one_le_left (weightDeriv2_pos hu).le
          (Real.one_le_exp (by linarith))

/-! ## Resolvent potential along a linear batch path

For `A(t) = A + t·D` invertible in a neighborhood of `t₀`, the entrywise
inverse `R(t) = A(t)⁻¹` is differentiable (entries are rational functions of
`t`, since `det` and `adjugate` are polynomial in the entries), and implicit
differentiation of `R(t)·A(t) = 1` gives `R'(t₀) = -A(t₀)⁻¹ D A(t₀)⁻¹`.
This is the pathwise form of the derivative computations in (B.3). -/

/-- Entries of an affine matrix path are differentiable with derivative `D i j`. -/
theorem hasDerivAt_entry_add_smul {n : ℕ} (A D : Matrix (Fin n) (Fin n) ℝ)
    (t₀ : ℝ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (A + t • D) i j) (D i j) t₀ := by
  have heq : (fun t : ℝ => (A + t • D) i j) = fun t => A i j + t * D i j :=
    funext fun t => by rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [heq]
  show HasDerivAt ((fun _ : ℝ => A i j) + fun y => y * D i j) (D i j) t₀
  exact ((hasDerivAt_const t₀ (A i j)).add
    ((hasDerivAt_id' t₀).mul_const (D i j))).congr_deriv (by simp)

/-- The determinant of an entrywise-differentiable matrix path is
differentiable (Leibniz formula: a polynomial in the entries). -/
theorem differentiableAt_det {n : ℕ}
    (P : ℝ → Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ)
    (hP : ∀ i j, DifferentiableAt ℝ (fun t => P t i j) t₀) :
    DifferentiableAt ℝ (fun t => (P t).det) t₀ := by
  classical
  rw [show (fun t => (P t).det) = fun t =>
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i, P t (σ i) i from funext fun t => Matrix.det_apply' (P t)]
  apply DifferentiableAt.fun_sum
  intro σ _
  apply DifferentiableAt.const_mul
  suffices h : ∀ s : Finset (Fin n),
      DifferentiableAt ℝ (fun t => ∏ i ∈ s, P t (σ i) i) t₀ from h Finset.univ
  intro s
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [show (fun t => ∏ i ∈ insert a s, P t (σ i) i) =
          fun t => P t (σ a) a * ∏ i ∈ s, P t (σ i) i from
        funext fun t => Finset.prod_insert ha]
      exact (hP (σ a) a).mul ih

/-- Entries of the adjugate of an entrywise-differentiable path are
differentiable. -/
theorem differentiableAt_adjugate_entry {n : ℕ}
    (P : ℝ → Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ)
    (hP : ∀ i j, DifferentiableAt ℝ (fun t => P t i j) t₀) (i j : Fin n) :
    DifferentiableAt ℝ (fun t => (P t).adjugate i j) t₀ := by
  rw [show (fun t => (P t).adjugate i j) =
      fun t => (Matrix.updateRow (P t) j (Pi.single i 1)).det from
    funext fun t => Matrix.adjugate_apply (P t) i j]
  apply differentiableAt_det
  intro a b
  simp only [Matrix.updateRow_apply]
  by_cases ha : a = j
  · simp only [ite_eq_left ha]
    exact differentiableAt_const _
  · simp only [ite_eq_right ha]
    exact hP a b

/-- Entries of the inverse of an entrywise-differentiable path are
differentiable at points where the path matrix is a unit, since
`A⁻¹ i j = det A ⁻¹ * adjugate A i j`. -/
theorem differentiableAt_inv_entry {n : ℕ}
    (P : ℝ → Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ)
    (hP : ∀ i j, DifferentiableAt ℝ (fun t => P t i j) t₀)
    (hP₀ : IsUnit (P t₀)) (i j : Fin n) :
    DifferentiableAt ℝ (fun t => (P t)⁻¹ i j) t₀ := by
  have hdet : DifferentiableAt ℝ (fun t => (P t).det) t₀ :=
    differentiableAt_det P t₀ hP
  have hadj : DifferentiableAt ℝ (fun t => (P t).adjugate i j) t₀ :=
    differentiableAt_adjugate_entry P t₀ hP i j
  have hdet0 : (P t₀).det ≠ 0 :=
    ((P t₀).isUnit_iff_isUnit_det.mp hP₀).ne_zero
  rw [show (fun t => (P t)⁻¹ i j) =
      fun t => ((P t).det)⁻¹ * (P t).adjugate i j from funext fun t => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]]
  exact (hdet.inv hdet0).mul hadj

/-- Implicit differentiation of `R(t) · P(t) = 1`: along the affine path
`P(t) = A + t·D` the inverse path has entrywise derivative
`R'(t₀) = -P(t₀)⁻¹ D P(t₀)⁻¹`. -/
theorem hasDerivAt_inv_entry_add_smul {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ)
    (hA : IsUnit (A + t₀ • D)) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (A + t • D)⁻¹ i j)
      (-((A + t₀ • D)⁻¹ * D * (A + t₀ • D)⁻¹) i j) t₀ := by
  classical
  set P : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t => A + t • D with hPdef
  have hP' : ∀ a b, HasDerivAt (fun t => P t a b) (D a b) t₀ := fun a b =>
    hasDerivAt_entry_add_smul A D t₀ a b
  have hPdiff : ∀ a b, DifferentiableAt ℝ (fun t => P t a b) t₀ := fun a b =>
    (hP' a b).differentiableAt
  have hAu : IsUnit (P t₀) := hA
  have hRdiff : ∀ a b, DifferentiableAt ℝ (fun t => (P t)⁻¹ a b) t₀ := fun a b =>
    differentiableAt_inv_entry P t₀ hPdiff hAu a b
  set R' : Matrix (Fin n) (Fin n) ℝ :=
    fun a b => deriv (fun t => (P t)⁻¹ a b) t₀ with hR'def
  have hR' : ∀ a b, HasDerivAt (fun t => (P t)⁻¹ a b) (R' a b) t₀ := fun a b =>
    (hRdiff a b).hasDerivAt
  -- Invertibility persists in a neighborhood of `t₀`.
  have hdet0 : (P t₀).det ≠ 0 := ((P t₀).isUnit_iff_isUnit_det.mp hAu).ne_zero
  have hdetC : ContinuousAt (fun t => (P t).det) t₀ :=
    (differentiableAt_det P t₀ hPdiff).continuousAt
  have hev : ∀ᶠ t in 𝓝 t₀, IsUnit (P t) := by
    filter_upwards [hdetC.eventually_ne hdet0] with t ht
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ht)
  have hev1 : ∀ᶠ t in 𝓝 t₀, (P t)⁻¹ * P t = 1 :=
    hev.mono fun t ht => Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp ht)
  -- Entrywise, `R(t)P(t) = 1` eventually, so its derivative is `0`.
  have hzero : ∀ a b, deriv (fun t => ((P t)⁻¹ * P t) a b) t₀ = 0 := fun a b => by
    have hevij : (fun t : ℝ => ((P t)⁻¹ * P t) a b) =ᶠ[𝓝 t₀]
        fun _ => (1 : Matrix (Fin n) (Fin n) ℝ) a b :=
      hev1.mono fun t ht => congrArg (fun M => M a b) ht
    have hconst : HasDerivAt (fun t => ((P t)⁻¹ * P t) a b) 0 t₀ :=
      (hasDerivAt_const t₀ ((1 : Matrix (Fin n) (Fin n) ℝ) a b)).congr_of_eventuallyEq
        hevij
    exact hconst.deriv
  -- The product rule gives the same derivative as `(R' P₀ + P₀⁻¹ D) a b`.
  have hprod : ∀ a b, deriv (fun t => ((P t)⁻¹ * P t) a b) t₀ =
      (R' * P t₀ + (P t₀)⁻¹ * D) a b := fun a b => by
    have hdiff : ∀ k : Fin n,
        DifferentiableAt ℝ (fun t => (P t)⁻¹ a k * P t k b) t₀ :=
      fun k => ((hR' a k).mul (hP' k b)).differentiableAt
    have hval : ∀ k : Fin n, deriv (fun t => (P t)⁻¹ a k * P t k b) t₀ =
        R' a k * (P t₀) k b + (P t₀)⁻¹ a k * D k b := fun k =>
      ((hR' a k).mul (hP' k b)).deriv
    rw [show (fun t => ((P t)⁻¹ * P t) a b) =
        fun t => ∑ k, (P t)⁻¹ a k * P t k b from
      funext fun t => by rw [Matrix.mul_apply]]
    rw [deriv_fun_sum fun k _ => hdiff k]
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => hval k
  have hmat : R' * P t₀ + (P t₀)⁻¹ * D = 0 := by
    ext a b
    rw [← hprod a b, hzero a b]
    rfl
  have hRval : R' = -((P t₀)⁻¹ * D * (P t₀)⁻¹) := by
    have h1 : R' * P t₀ = -((P t₀)⁻¹ * D) := eq_neg_of_add_eq_zero_left hmat
    calc R' = R' * P t₀ * (P t₀)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _
            ((Matrix.isUnit_iff_isUnit_det _).mp hAu), Matrix.mul_one]
      _ = -((P t₀)⁻¹ * D) * (P t₀)⁻¹ := by rw [h1]
      _ = -((P t₀)⁻¹ * D * (P t₀)⁻¹) := neg_mul _ _
  -- Rewrite `R' i j` as the claimed value.
  have hval : R' i j = (-((A + t₀ • D)⁻¹ * D * (A + t₀ • D)⁻¹)) i j := by
    rw [hRval]
  exact (hR' i j).congr_deriv hval

/-- Entrywise derivative of `t ↦ (R(t)·C·R(t)) i j` along `R(t) = (A + t·E)⁻¹`:
the product rule gives `(R'·C·R₀ + R₀·C·R') i j` with `R' = -R₀·E·R₀`. -/
theorem hasDerivAt_inv_mul_mul_inv_entry {n : ℕ}
    (A E C : Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ) (hA : IsUnit (A + t₀ • E))
    (i j : Fin n) :
    HasDerivAt (fun t : ℝ => ((A + t • E)⁻¹ * C * (A + t • E)⁻¹) i j)
      ((-((A + t₀ • E)⁻¹ * E * (A + t₀ • E)⁻¹) * C * (A + t₀ • E)⁻¹ +
          (A + t₀ • E)⁻¹ * C * -((A + t₀ • E)⁻¹ * E * (A + t₀ • E)⁻¹)) i j) t₀ := by
  set P : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t => A + t • E
  set R' : Matrix (Fin n) (Fin n) ℝ := -((P t₀)⁻¹ * E * (P t₀)⁻¹)
  have hRi : ∀ a b, HasDerivAt (fun t => (P t)⁻¹ a b) (R' a b) t₀ := fun a b =>
    hasDerivAt_inv_entry_add_smul A E t₀ hA a b
  -- Expand the product entrywise and apply the product rule under the sums.
  rw [show (fun t => ((P t)⁻¹ * C * (P t)⁻¹) i j) =
      fun t => ∑ k, (∑ l, (P t)⁻¹ i l * C l k) * (P t)⁻¹ k j from
    funext fun t => by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => by rw [Matrix.mul_apply]]
  have hinner : ∀ k, HasDerivAt (fun t => ∑ l, (P t)⁻¹ i l * C l k)
      (∑ l, R' i l * C l k) t₀ := fun k =>
    HasDerivAt.fun_sum fun l _ => (hRi i l).mul_const (C l k)
  apply HasDerivAt.congr_deriv
    (HasDerivAt.fun_sum fun k _ => (hinner k).mul (hRi k j))
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Matrix.mul_apply, ← Matrix.mul_apply]

/-- Pathwise first derivative of the resolvent entry-sum along a batch
direction: for `P(t) = bI - (M + tD)`,
`d/dt ∑ᵢⱼ P(t)⁻¹ᵢⱼ |_{t₀} = ∑ᵢⱼ (R D R)ᵢⱼ` with `R = P(t₀)⁻¹`.
This is the first-order term of the (B.3) Hessian computation. -/
theorem hasDerivAt_resolvent_inv_sum {n : ℕ} (b : ℝ)
    (M D : Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ)
    (hA : IsUnit (Matrix.diagonal (fun _ : Fin n => b) - (M + t₀ • D))) :
    HasDerivAt (fun t : ℝ => ∑ i : Fin n, ∑ j : Fin n,
        (Matrix.diagonal (fun _ : Fin n => b) - (M + t • D))⁻¹ i j)
      (∑ i : Fin n, ∑ j : Fin n,
        ((Matrix.diagonal (fun _ : Fin n => b) - (M + t₀ • D))⁻¹ * D *
          (Matrix.diagonal (fun _ : Fin n => b) - (M + t₀ • D))⁻¹) i j) t₀ := by
  have hid : ∀ t : ℝ, Matrix.diagonal (fun _ : Fin n => b) - (M + t • D) =
      (Matrix.diagonal (fun _ : Fin n => b) - M) + t • (-D) := fun t => by
    rw [smul_neg, ← sub_eq_add_neg, sub_add_eq_sub_sub]
  have h : ∀ i j : Fin n, HasDerivAt
      (fun t : ℝ => (Matrix.diagonal (fun _ : Fin n => b) - (M + t • D))⁻¹ i j)
      (-(((Matrix.diagonal (fun _ : Fin n => b) - M) + t₀ • (-D))⁻¹ * (-D) *
        ((Matrix.diagonal (fun _ : Fin n => b) - M) + t₀ • (-D))⁻¹) i j) t₀ := by
    intro i j
    rw [show (fun t : ℝ => (Matrix.diagonal (fun _ : Fin n => b) - (M + t • D))⁻¹ i j) =
        fun t => (((Matrix.diagonal (fun _ : Fin n => b) - M) + t • (-D))⁻¹) i j from
      funext fun t => congrArg (fun X => X i j) (congrArg Inv.inv (hid t))]
    exact hasDerivAt_inv_entry_add_smul
      (Matrix.diagonal (fun _ : Fin n => b) - M) (-D) t₀ (by rwa [← hid t₀]) i j
  apply HasDerivAt.congr_deriv
    (HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => h i j)
  rw [hid t₀]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.neg_apply, mul_neg, neg_mul, neg_neg]

/-- Pathwise second derivative along a batch direction: with
`P(t) = bI - (M + tD)` and `R = P(t₀)⁻¹`,
`(d/dt)² ∑ᵢⱼ P(t)⁻¹ᵢⱼ |_{t₀} = 2·∑ᵢⱼ (R D R D R)ᵢⱼ`.
This is the Hessian value in the (B.3) computation. -/
theorem hasDerivAt_resolvent_inv_mul_sum {n : ℕ} (b : ℝ)
    (M D : Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ)
    (hA : IsUnit (Matrix.diagonal (fun _ : Fin n => b) - (M + t₀ • D))) :
    HasDerivAt (fun t : ℝ => ∑ i : Fin n, ∑ j : Fin n,
        ((Matrix.diagonal (fun _ : Fin n => b) - (M + t • D))⁻¹ * D *
          (Matrix.diagonal (fun _ : Fin n => b) - (M + t • D))⁻¹) i j)
      (2 * ∑ i : Fin n, ∑ j : Fin n,
        ((Matrix.diagonal (fun _ : Fin n => b) - (M + t₀ • D))⁻¹ * D *
          (Matrix.diagonal (fun _ : Fin n => b) - (M + t₀ • D))⁻¹ * D *
          (Matrix.diagonal (fun _ : Fin n => b) - (M + t₀ • D))⁻¹) i j) t₀ := by
  have hid : ∀ t : ℝ, Matrix.diagonal (fun _ : Fin n => b) - (M + t • D) =
      (Matrix.diagonal (fun _ : Fin n => b) - M) + t • (-D) := fun t => by
    rw [smul_neg, ← sub_eq_add_neg, sub_add_eq_sub_sub]
  have h : ∀ i j : Fin n, HasDerivAt
      (fun t : ℝ => ((Matrix.diagonal (fun _ : Fin n => b) - (M + t • D))⁻¹ * D *
        (Matrix.diagonal (fun _ : Fin n => b) - (M + t • D))⁻¹) i j)
      ((-(((Matrix.diagonal (fun _ : Fin n => b) - M) + t₀ • (-D))⁻¹ * (-D) *
          ((Matrix.diagonal (fun _ : Fin n => b) - M) + t₀ • (-D))⁻¹) * D *
          ((Matrix.diagonal (fun _ : Fin n => b) - M) + t₀ • (-D))⁻¹ +
        ((Matrix.diagonal (fun _ : Fin n => b) - M) + t₀ • (-D))⁻¹ * D *
          -(((Matrix.diagonal (fun _ : Fin n => b) - M) + t₀ • (-D))⁻¹ * (-D) *
            ((Matrix.diagonal (fun _ : Fin n => b) - M) + t₀ • (-D))⁻¹)) i j) t₀ := by
    intro i j
    rw [show (fun t : ℝ => ((Matrix.diagonal (fun _ : Fin n => b) - (M + t • D))⁻¹ * D *
          (Matrix.diagonal (fun _ : Fin n => b) - (M + t • D))⁻¹) i j) =
        fun t => (((Matrix.diagonal (fun _ : Fin n => b) - M) + t • (-D))⁻¹ * D *
          ((Matrix.diagonal (fun _ : Fin n => b) - M) + t • (-D))⁻¹) i j from
      funext fun t => congrArg (fun X => X i j)
        (congrArg (fun X => X * D * X) (congrArg Inv.inv (hid t)))]
    exact hasDerivAt_inv_mul_mul_inv_entry
      (Matrix.diagonal (fun _ : Fin n => b) - M) (-D) D t₀ (by rwa [← hid t₀]) i j
  apply HasDerivAt.congr_deriv
    (HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => h i j)
  rw [hid t₀, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_neg, neg_mul, neg_neg, Matrix.add_apply, Matrix.mul_assoc, two_mul]

end Komlos
