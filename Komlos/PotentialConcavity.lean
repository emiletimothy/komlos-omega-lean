import Komlos
import Komlos.MatrixInverse
import Komlos.Curvature
import Komlos.ConcaveStep
import Mathlib.Analysis.Convex.Deriv

/-!
# Concavity of the resolvent potential along a batch direction

`Komlos.Curvature` computes the pathwise derivative values of the
resolvent entry-sum along the linear slack path
`P(t) = bI − (M + t·D)`:

* `hasDerivAt_resolvent_inv_sum`: `F'(t₀) = ∑ᵢⱼ (R D R)ᵢⱼ`,
* `hasDerivAt_resolvent_inv_mul_sum`: `F''(t₀) = 2·∑ᵢⱼ (R D R D R)ᵢⱼ`,

with `R = P(t₀)⁻¹`.  This module assembles them into the *global*
statement the walk needs: if the Hessian value is nonpositive at every
interior point of a trust window `[a, c]` on which `P(t)` stays
invertible, then `t ↦ resolventPotential b (M + t·D)` is concave on the
window (`concaveOn_resolvent_inv_sum`, `concaveOn_resolventPotential_path`).

The specialization `pair_average_resolventPotential_le` is the engine of
Proposition 2.1's final line: averaging the potential over the fair sign
`σ ∈ {±1}` does not increase it.  The Hessian hypothesis `h2` is exactly
what the spectral-subspace construction supplies on the trust window.
-/

namespace Komlos

open scoped BigOperators
open Matrix

/-- The `∑ᵢⱼ (bI − M)⁻¹ᵢⱼ` form of the resolvent potential:
`∑ⱼ resolventVector j = ∑ⱼ∑ᵢ (bI−M)⁻¹ⱼᵢ`. -/
theorem sum_resolventVector_eq {s : ℕ} (b : ℝ) (M : Input s s) :
    (∑ j : Fin s, resolventVector b M j) =
      ∑ i : Fin s, ∑ j : Fin s, (slackMatrix b M)⁻¹ i j := by
  unfold resolventVector
  have hrow : ∀ j : Fin s,
      ((slackMatrix b M)⁻¹ *ᵥ fun _ => (1 : ℝ)) j =
        ∑ i : Fin s, (slackMatrix b M)⁻¹ j i := fun j => by
    rw [Matrix.mulVec_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_one]
  rw [Finset.sum_congr rfl fun j _ => hrow j]

/-- The resolvent potential equals the inverse entry-sum minus the
trace-term `s/b`. -/
theorem resolventPotential_eq_inv_sum {s : ℕ} (b : ℝ) (M : Input s s) :
    resolventPotential b M =
      (∑ i : Fin s, ∑ j : Fin s, (slackMatrix b M)⁻¹ i j) - s / b := by
  unfold resolventPotential
  rw [sum_resolventVector_eq]

/-- **Concavity of the inverse entry-sum on a trust window.**
If `P(t) = bI − (M + t·D)` is invertible throughout `[a, c]` and the
Hessian value `2·∑ᵢⱼ (R D R D R)ᵢⱼ` is nonpositive at every interior
point, then `t ↦ ∑ᵢⱼ P(t)⁻¹ᵢⱼ` is concave on `[a, c]`. -/
theorem concaveOn_resolvent_inv_sum {s : ℕ} (b : ℝ)
    (M D : Input s s) (a c : ℝ)
    (hunit : ∀ t ∈ Set.Icc a c,
      IsUnit (Matrix.diagonal (fun _ : Fin s => b) - (M + t • D)))
    (h2 : ∀ t ∈ Set.Ioo a c,
      2 * ∑ i : Fin s, ∑ j : Fin s,
        ((Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹ * D *
          (Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹ * D *
          (Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹) i j ≤ 0) :
    ConcaveOn ℝ (Set.Icc a c)
      (fun t => ∑ i : Fin s, ∑ j : Fin s,
        (Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹ i j) := by
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc a c)
    (f' := fun t => ∑ i : Fin s, ∑ j : Fin s,
      ((Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹ * D *
        (Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹) i j)
    (f'' := fun t => 2 * ∑ i : Fin s, ∑ j : Fin s,
      ((Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹ * D *
        (Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹ * D *
        (Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹) i j)
    ?_ ?_ ?_ ?_
  · intro t ht
    exact (hasDerivAt_resolvent_inv_sum b M D t (hunit t ht)).differentiableAt
      |>.continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (hasDerivAt_resolvent_inv_sum b M D t
      (hunit t (Set.Ioo_subset_Icc_self ht))).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (hasDerivAt_resolvent_inv_mul_sum b M D t
      (hunit t (Set.Ioo_subset_Icc_self ht))).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact h2 t ht

/-- **Concavity of the resolvent potential on a trust window.** The
constant shift `s/b` does not affect concavity. -/
theorem concaveOn_resolventPotential_path {s : ℕ} (b : ℝ)
    (M D : Input s s) (a c : ℝ)
    (hunit : ∀ t ∈ Set.Icc a c,
      IsUnit (Matrix.diagonal (fun _ : Fin s => b) - (M + t • D)))
    (h2 : ∀ t ∈ Set.Ioo a c,
      2 * ∑ i : Fin s, ∑ j : Fin s,
        ((Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹ * D *
          (Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹ * D *
          (Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹) i j ≤ 0) :
    ConcaveOn ℝ (Set.Icc a c) (fun t => resolventPotential b (M + t • D)) := by
  have hconc := concaveOn_resolvent_inv_sum b M D a c hunit h2
  have hshift : ConcaveOn ℝ (Set.Icc a c)
      (fun t => (∑ i : Fin s, ∑ j : Fin s,
        (Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹ i j) + (-(s : ℝ) / b)) :=
    ConcaveOn.add_const hconc (-(s : ℝ) / b)
  have heq : (fun t : ℝ => resolventPotential b (M + t • D)) =
      fun t => (∑ i : Fin s, ∑ j : Fin s,
        (Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹ i j) + (-(s : ℝ) / b) := by
    funext t
    rw [resolventPotential_eq_inv_sum]
    unfold slackMatrix
    ring
  rw [heq]
  exact hshift

/-- **Proposition 2.1's expectation bound, deterministic form.** On a
trust window symmetric about `0` of half-width `T`, if the slack stays
invertible and the Hessian value is nonpositive throughout the interior,
the fair-sign average of the resolvent potential does not exceed the
value at the center:

`(F_b(M + T·D) + F_b(M − T·D)) / 2 ≤ F_b(M)`.

This is the analytic content behind `𝔼_σ F_b(M(x + σ·t·h)) ≤ F_b(M(x))`;
combined with `Komlos.ConcaveStep` it yields the per-batch expectation
nonincrease of the walk. -/
theorem pair_average_resolventPotential_le {s : ℕ} (b : ℝ)
    (M D : Input s s) {T : ℝ} (hT : 0 < T)
    (hunit : ∀ t ∈ Set.Icc (-T) T,
      IsUnit (Matrix.diagonal (fun _ : Fin s => b) - (M + t • D)))
    (h2 : ∀ t ∈ Set.Ioo (-T) T,
      2 * ∑ i : Fin s, ∑ j : Fin s,
        ((Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹ * D *
          (Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹ * D *
          (Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹) i j ≤ 0) :
    (resolventPotential b (M + T • D) + resolventPotential b (M - T • D)) / 2 ≤
      resolventPotential b M := by
  have hconc := concaveOn_resolventPotential_path b M D (-T) T hunit h2
  have h := concaveOn_pair_average_le hT hconc
  have hM : M + (-T) • D = M - T • D := by
    rw [neg_smul, sub_eq_add_neg]
  have hzero : M + (0 : ℝ) • D = M := by simp
  rw [hM, hzero] at h
  exact h

end Komlos
