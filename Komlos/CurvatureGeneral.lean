import Komlos
import Komlos.Curvature
import Mathlib.Analysis.Convex.Deriv

/-!
# Pathwise resolvent calculus along general (non-affine) paths

`Komlos.Curvature` proves the derivative formulas for the *affine* slack
path `P(t) = A + t·D`.  Along the actual walk, however, the slack is
`P(t) = bI − M(x + t·h)` with `M` built from the nonlinear weights
`ν(uᵢ(t))`, so `P` is not affine: writing `Dp(t) = P'(t)` and
`D₂(t) = P''(t)`, implicit differentiation of `R(t)·P(t) = 1`,
`R(t) = P(t)⁻¹`, gives

* `R' = −R·Dp·R`,
* `R'' = 2·R·Dp·R·Dp·R − R·D₂·R`.

This module proves the general-path versions:

* `hasDerivAt_inv_entry_of_path`: entrywise `R' = −R·Dp·R`;
* `hasDerivAt_inv_sum_of_path`: `F'(t₀) = −∑ᵢⱼ (R·Dp·R)ᵢⱼ`;
* `hasDerivAt_inv_mul_fun_mul_inv_entry`: the triple product rule for
  `t ↦ (R·C(t)·R)ᵢⱼ`;
* `hasDerivAt2_inv_sum_of_path`: `F''(t₀) = 2·∑ᵢⱼ(R·Dp·R·Dp·R)ᵢⱼ −
  ∑ᵢⱼ(R·D₂·R)ᵢⱼ`;
* `concaveOn_inv_sum_path`: the second-derivative criterion, lifting the
  Hessian hypothesis to `ConcaveOn` of the inverse entry-sum on a trust
  window.

For the slack path `P(t) = bI − M(t)` one has `Dp = −M'`, `D₂ = −M''`, so
the potential's second derivative along the walk direction is
`2·∑ᵢⱼ(R·M'·R·M'·R)ᵢⱼ + ∑ᵢⱼ(R·M''·R)ᵢⱼ`, matching the two-term Hessian
of Appendix B.
-/

namespace Komlos

open scoped BigOperators
open Filter
open scoped Topology

/-- Implicit differentiation of `R(t)·P(t) = 1` along a general
entrywise-differentiable path: `R'(t₀) = −P₀⁻¹·Dp·P₀⁻¹`. -/
theorem hasDerivAt_inv_entry_of_path {n : ℕ}
    (P : ℝ → Matrix (Fin n) (Fin n) ℝ) (Dp : Matrix (Fin n) (Fin n) ℝ)
    (t₀ : ℝ)
    (hP : ∀ i j, HasDerivAt (fun t => P t i j) (Dp i j) t₀)
    (hP₀ : IsUnit (P t₀)) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (P t)⁻¹ i j)
      (-((P t₀)⁻¹ * Dp * (P t₀)⁻¹) i j) t₀ := by
  classical
  have hPdiff : ∀ a b, DifferentiableAt ℝ (fun t => P t a b) t₀ := fun a b =>
    (hP a b).differentiableAt
  have hRdiff : ∀ a b, DifferentiableAt ℝ (fun t => (P t)⁻¹ a b) t₀ := fun a b =>
    differentiableAt_inv_entry P t₀ hPdiff hP₀ a b
  set R' : Matrix (Fin n) (Fin n) ℝ :=
    fun a b => deriv (fun t => (P t)⁻¹ a b) t₀ with hR'def
  have hR' : ∀ a b, HasDerivAt (fun t => (P t)⁻¹ a b) (R' a b) t₀ := fun a b =>
    (hRdiff a b).hasDerivAt
  have hdet0 : (P t₀).det ≠ 0 := ((P t₀).isUnit_iff_isUnit_det.mp hP₀).ne_zero
  have hdetC : ContinuousAt (fun t => (P t).det) t₀ :=
    (differentiableAt_det P t₀ hPdiff).continuousAt
  have hev : ∀ᶠ t in 𝓝 t₀, IsUnit (P t) := by
    filter_upwards [hdetC.eventually_ne hdet0] with t ht
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ht)
  have hev1 : ∀ᶠ t in 𝓝 t₀, (P t)⁻¹ * P t = 1 :=
    hev.mono fun t ht => Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp ht)
  have hzero : ∀ a b, deriv (fun t => ((P t)⁻¹ * P t) a b) t₀ = 0 := fun a b => by
    have hevij : (fun t : ℝ => ((P t)⁻¹ * P t) a b) =ᶠ[𝓝 t₀]
        fun _ => (1 : Matrix (Fin n) (Fin n) ℝ) a b :=
      hev1.mono fun t ht => congrArg (fun M => M a b) ht
    have hconst : HasDerivAt (fun t => ((P t)⁻¹ * P t) a b) 0 t₀ :=
      (hasDerivAt_const t₀ ((1 : Matrix (Fin n) (Fin n) ℝ) a b)).congr_of_eventuallyEq
        hevij
    exact hconst.deriv
  have hprod : ∀ a b, deriv (fun t => ((P t)⁻¹ * P t) a b) t₀ =
      (R' * P t₀ + (P t₀)⁻¹ * Dp) a b := fun a b => by
    have hdiff : ∀ k : Fin n,
        DifferentiableAt ℝ (fun t => (P t)⁻¹ a k * P t k b) t₀ :=
      fun k => ((hR' a k).mul (hP k b)).differentiableAt
    have hval : ∀ k : Fin n, deriv (fun t => (P t)⁻¹ a k * P t k b) t₀ =
        R' a k * (P t₀) k b + (P t₀)⁻¹ a k * Dp k b := fun k =>
      ((hR' a k).mul (hP k b)).deriv
    rw [show (fun t => ((P t)⁻¹ * P t) a b) =
        fun t => ∑ k, (P t)⁻¹ a k * P t k b from
      funext fun t => by rw [Matrix.mul_apply]]
    rw [deriv_fun_sum fun k _ => hdiff k]
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => hval k
  have hmat : R' * P t₀ + (P t₀)⁻¹ * Dp = 0 := by
    ext a b
    rw [← hprod a b, hzero a b]
    rfl
  have hRval : R' = -((P t₀)⁻¹ * Dp * (P t₀)⁻¹) := by
    have h1 : R' * P t₀ = -((P t₀)⁻¹ * Dp) := eq_neg_of_add_eq_zero_left hmat
    calc R' = R' * P t₀ * (P t₀)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _
            ((Matrix.isUnit_iff_isUnit_det _).mp hP₀), Matrix.mul_one]
      _ = -((P t₀)⁻¹ * Dp) * (P t₀)⁻¹ := by rw [h1]
      _ = -((P t₀)⁻¹ * Dp * (P t₀)⁻¹) := neg_mul _ _
  have hval : R' i j = (-((P t₀)⁻¹ * Dp * (P t₀)⁻¹)) i j := by
    rw [hRval]
  exact (hR' i j).congr_deriv hval

/-- General-path first derivative of the inverse entry-sum:
`F'(t₀) = −∑ᵢⱼ (P₀⁻¹·Dp·P₀⁻¹)ᵢⱼ`. -/
theorem hasDerivAt_inv_sum_of_path {n : ℕ}
    (P : ℝ → Matrix (Fin n) (Fin n) ℝ) (Dp : Matrix (Fin n) (Fin n) ℝ)
    (t₀ : ℝ)
    (hP : ∀ i j, HasDerivAt (fun t => P t i j) (Dp i j) t₀)
    (hP₀ : IsUnit (P t₀)) :
    HasDerivAt (fun t : ℝ => ∑ i : Fin n, ∑ j : Fin n, (P t)⁻¹ i j)
      (-(∑ i : Fin n, ∑ j : Fin n, ((P t₀)⁻¹ * Dp * (P t₀)⁻¹) i j)) t₀ := by
  apply HasDerivAt.congr_deriv
    (HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
      hasDerivAt_inv_entry_of_path P Dp t₀ hP hP₀ i j)
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]

/-- Triple product rule at an entry: for matrix paths `X Y Z` with
derivatives `Dx Dy Dz`,
`(X·Y·Z)' i j = (Dx·Y·Z + X·Dy·Z + X·Y·Dz) i j`. -/
theorem hasDerivAt_mul_mul_entry_of_path {n : ℕ}
    (X Y Z : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (Dx Dy Dz : Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ)
    (hX : ∀ i j, HasDerivAt (fun t => X t i j) (Dx i j) t₀)
    (hY : ∀ i j, HasDerivAt (fun t => Y t i j) (Dy i j) t₀)
    (hZ : ∀ i j, HasDerivAt (fun t => Z t i j) (Dz i j) t₀)
    (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (X t * Y t * Z t) i j)
      ((Dx * Y t₀ * Z t₀ + X t₀ * Dy * Z t₀ + X t₀ * Y t₀ * Dz) i j) t₀ := by
  rw [show (fun t : ℝ => (X t * Y t * Z t) i j) =
      fun t => ∑ k, ∑ l, X t i l * (Y t l k * Z t k j) from
    funext fun t => by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => by
        rw [Matrix.mul_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => mul_assoc _ _ _]
  have hterm : ∀ k l : Fin n, HasDerivAt
      (fun t => X t i l * (Y t l k * Z t k j))
      (Dx i l * (Y t₀ l k * Z t₀ k j) +
        X t₀ i l * (Dy l k * Z t₀ k j + Y t₀ l k * Dz k j)) t₀ := fun k l =>
    (hX i l).mul ((hY l k).mul (hZ k j))
  apply HasDerivAt.congr_deriv
    (HasDerivAt.fun_sum fun k _ => HasDerivAt.fun_sum fun l _ => hterm k l)
  simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- Derivative of `t ↦ (P(t)⁻¹ · C(t) · P(t)⁻¹) i j` along a general
path: `(R'·C·R + R·C'·R + R·C·R') i j` with `R' = −R·Dp·R`. -/
theorem hasDerivAt_inv_mul_fun_mul_inv_entry {n : ℕ}
    (P C : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (Dp Dc : Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ)
    (hP : ∀ i j, HasDerivAt (fun t => P t i j) (Dp i j) t₀)
    (hC : ∀ i j, HasDerivAt (fun t => C t i j) (Dc i j) t₀)
    (hP₀ : IsUnit (P t₀)) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => ((P t)⁻¹ * C t * (P t)⁻¹) i j)
      ((-((P t₀)⁻¹ * Dp * (P t₀)⁻¹) * C t₀ * (P t₀)⁻¹ +
          (P t₀)⁻¹ * Dc * (P t₀)⁻¹ +
          (P t₀)⁻¹ * C t₀ * -((P t₀)⁻¹ * Dp * (P t₀)⁻¹)) i j) t₀ := by
  set R' : Matrix (Fin n) (Fin n) ℝ := -((P t₀)⁻¹ * Dp * (P t₀)⁻¹)
  have hRi : ∀ a b, HasDerivAt (fun t => (P t)⁻¹ a b) (R' a b) t₀ := fun a b =>
    hasDerivAt_inv_entry_of_path P Dp t₀ hP hP₀ a b
  exact hasDerivAt_mul_mul_entry_of_path (fun t => (P t)⁻¹) C
    (fun t => (P t)⁻¹) R' Dc R' t₀ hRi hC hRi i j

/-- **General-path second derivative.** If `Dp` is the entrywise
derivative path of `P` and `D₂` its derivative at `t₀`, then

`(d/dt) (−∑ᵢⱼ (R·Dp·R)ᵢⱼ)|_{t₀}
   = 2·∑ᵢⱼ (R·Dp·R·Dp·R)ᵢⱼ − ∑ᵢⱼ (R·D₂·R)ᵢⱼ`. -/
theorem hasDerivAt2_inv_sum_of_path {n : ℕ}
    (P Dp : ℝ → Matrix (Fin n) (Fin n) ℝ) (D2 : Matrix (Fin n) (Fin n) ℝ)
    (t₀ : ℝ)
    (hP : ∀ i j, HasDerivAt (fun t => P t i j) (Dp t₀ i j) t₀)
    (hDp : ∀ i j, HasDerivAt (fun t => Dp t i j) (D2 i j) t₀)
    (hP₀ : IsUnit (P t₀)) :
    HasDerivAt
      (fun t : ℝ => -(∑ i : Fin n, ∑ j : Fin n,
        ((P t)⁻¹ * Dp t * (P t)⁻¹) i j))
      (2 * ∑ i : Fin n, ∑ j : Fin n,
          ((P t₀)⁻¹ * Dp t₀ * (P t₀)⁻¹ * Dp t₀ * (P t₀)⁻¹) i j -
        ∑ i : Fin n, ∑ j : Fin n,
          ((P t₀)⁻¹ * D2 * (P t₀)⁻¹) i j) t₀ := by
  have hterm : ∀ i j : Fin n, HasDerivAt
      (fun t : ℝ => ((P t)⁻¹ * Dp t * (P t)⁻¹) i j)
      ((-((P t₀)⁻¹ * Dp t₀ * (P t₀)⁻¹) * Dp t₀ * (P t₀)⁻¹ +
          (P t₀)⁻¹ * D2 * (P t₀)⁻¹ +
          (P t₀)⁻¹ * Dp t₀ * -((P t₀)⁻¹ * Dp t₀ * (P t₀)⁻¹)) i j) t₀ :=
    fun i j => hasDerivAt_inv_mul_fun_mul_inv_entry P Dp (Dp t₀) D2 t₀ hP
      hDp hP₀ i j
  have hsum : HasDerivAt (fun t : ℝ => ∑ i : Fin n, ∑ j : Fin n,
      ((P t)⁻¹ * Dp t * (P t)⁻¹) i j)
      (∑ i : Fin n, ∑ j : Fin n,
        ((-((P t₀)⁻¹ * Dp t₀ * (P t₀)⁻¹) * Dp t₀ * (P t₀)⁻¹ +
            (P t₀)⁻¹ * D2 * (P t₀)⁻¹ +
            (P t₀)⁻¹ * Dp t₀ * -((P t₀)⁻¹ * Dp t₀ * (P t₀)⁻¹)) i j)) t₀ :=
    HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => hterm i j
  apply HasDerivAt.congr_deriv hsum.neg
  simp only [← Finset.sum_neg_distrib]
  have key : ∀ i j : Fin n,
      -((-((P t₀)⁻¹ * Dp t₀ * (P t₀)⁻¹) * Dp t₀ * (P t₀)⁻¹ +
          (P t₀)⁻¹ * D2 * (P t₀)⁻¹ +
          (P t₀)⁻¹ * Dp t₀ * -((P t₀)⁻¹ * Dp t₀ * (P t₀)⁻¹)) i j) =
        2 * ((P t₀)⁻¹ * Dp t₀ * (P t₀)⁻¹ * Dp t₀ * (P t₀)⁻¹) i j -
          ((P t₀)⁻¹ * D2 * (P t₀)⁻¹) i j := by
    intro i j
    have h1 : (-((P t₀)⁻¹ * Dp t₀ * (P t₀)⁻¹)) * Dp t₀ * (P t₀)⁻¹ =
        -((P t₀)⁻¹ * Dp t₀ * (P t₀)⁻¹ * Dp t₀ * (P t₀)⁻¹) := by
      rw [neg_mul, neg_mul]
    have h2' : (P t₀)⁻¹ * Dp t₀ * -((P t₀)⁻¹ * Dp t₀ * (P t₀)⁻¹) =
        -((P t₀)⁻¹ * Dp t₀ * (P t₀)⁻¹ * Dp t₀ * (P t₀)⁻¹) := by
      rw [mul_neg, neg_inj, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    rw [h1, h2']
    simp only [Matrix.add_apply, Matrix.neg_apply]
    ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key i j]
  simp only [Finset.sum_sub_distrib, Finset.mul_sum]

/-- **Second-derivative concavity criterion along a general path.** If
`P` stays invertible on `[a, c]` and the general-path Hessian value
`2·∑ᵢⱼ(R·Dp·R·Dp·R)ᵢⱼ − ∑ᵢⱼ(R·D₂·R)ᵢⱼ` is nonpositive at every interior
point, then `t ↦ ∑ᵢⱼ P(t)⁻¹ᵢⱼ` is concave on `[a, c]`. -/
theorem concaveOn_inv_sum_path {n : ℕ}
    (P Dp D2 : ℝ → Matrix (Fin n) (Fin n) ℝ) (a c : ℝ)
    (hP : ∀ t ∈ Set.Icc a c, ∀ i j,
      HasDerivAt (fun s => P s i j) (Dp t i j) t)
    (hDp : ∀ t ∈ Set.Icc a c, ∀ i j,
      HasDerivAt (fun s => Dp s i j) (D2 t i j) t)
    (hunit : ∀ t ∈ Set.Icc a c, IsUnit (P t))
    (h2 : ∀ t ∈ Set.Ioo a c,
      2 * ∑ i : Fin n, ∑ j : Fin n,
          ((P t)⁻¹ * Dp t * (P t)⁻¹ * Dp t * (P t)⁻¹) i j -
        ∑ i : Fin n, ∑ j : Fin n,
          ((P t)⁻¹ * D2 t * (P t)⁻¹) i j ≤ 0) :
    ConcaveOn ℝ (Set.Icc a c)
      (fun t => ∑ i : Fin n, ∑ j : Fin n, (P t)⁻¹ i j) := by
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc a c)
    (f' := fun t => -(∑ i : Fin n, ∑ j : Fin n,
      ((P t)⁻¹ * Dp t * (P t)⁻¹) i j))
    (f'' := fun t => 2 * ∑ i : Fin n, ∑ j : Fin n,
        ((P t)⁻¹ * Dp t * (P t)⁻¹ * Dp t * (P t)⁻¹) i j -
      ∑ i : Fin n, ∑ j : Fin n,
        ((P t)⁻¹ * D2 t * (P t)⁻¹) i j)
    ?_ ?_ ?_ ?_
  · intro t ht
    exact (hasDerivAt_inv_sum_of_path P (Dp t) t (hP t ht)
      (hunit t ht)).differentiableAt.continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (hasDerivAt_inv_sum_of_path P (Dp t) t (hP t
      (Set.Ioo_subset_Icc_self ht)) (hunit t
        (Set.Ioo_subset_Icc_self ht))).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (hasDerivAt2_inv_sum_of_path P Dp (D2 t) t (hP t
      (Set.Ioo_subset_Icc_self ht)) (hDp t (Set.Ioo_subset_Icc_self ht))
      (hunit t (Set.Ioo_subset_Icc_self ht))).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact h2 t ht

end Komlos
