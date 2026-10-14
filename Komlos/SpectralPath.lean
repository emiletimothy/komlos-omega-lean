import Komlos
import Komlos.CurvatureGeneral
import Komlos.PotentialConcavity

/-!
# The batch spectral matrix and its pathwise potential

This module instantiates the general-path resolvent calculus of
`Komlos.CurvatureGeneral` for the paper's batch matrix (2.5):

`M(t) = M₀ + ∑ᵢ ν(uᵢ + t·cᵢ)·zᵢzᵢᵀ`

where the anchor contribution `M₀` is constant along the step and each
light row's weight `ν(uᵢ + t·cᵢ)` moves affinely in `t` — the walk
specialization is `cᵢ = gᵢᵀh`, the barrier gradient along the step
direction `h`.

* `batchMatrix`: `M₀ + ∑ᵢ weight(uᵢ)·zᵢzᵢᵀ`.
* `batchMatrixDeriv`: `M'(t) = ∑ᵢ ν′(uᵢ)·cᵢ·zᵢzᵢᵀ`.
* `batchMatrixDeriv2`: `M''(t) = ∑ᵢ ν″(uᵢ)·cᵢ²·zᵢzᵢᵀ`.
* `hasDerivAt_batchMatrix_entry`, `hasDerivAt_batchMatrixDeriv_entry`,
  `hasDerivAt_slack_batch_entry`, `hasDerivAt_slack_deriv_entry`:
  entrywise derivative certificates.
* `concaveOn_resolventPotential_batch`: with `P(t) = bI − M(t)`,
  `R = P(t)⁻¹`, if the slack stays invertible on `[lo, hi]` and

  `2·∑ᵢⱼ (R·M'·R·M'·R)ᵢⱼ + ∑ᵢⱼ (R·M''·R)ᵢⱼ ≤ 0`

  on the interior — the paper's `∇²F_b = P − D` sign condition
  `P_x[h] ≤ (1 − ρ/2)·D_x[h]` — then the resolvent potential is concave
  on the window.
* `pair_average_resolventPotential_batch`: the fair-sign expectation
  bound `𝔼_σ F_b(M(x + σ·T·d)) ≤ F_b(M(x))` of Proposition 2.1.
-/

namespace Komlos

open scoped BigOperators
open Matrix

/-! ## The batch matrix and its variations -/

/-- The batch matrix (2.5): the anchor part `M₀` plus the light rows'
weighted Gram `∑ᵢ ν(uᵢ)·zᵢzᵢᵀ`. -/
noncomputable def batchMatrix {m s : ℕ} (M0 : Matrix (Fin s) (Fin s) ℝ)
    (z : Fin m → Fin s → ℝ) (u : Fin m → ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  M0 + ∑ i, weight (u i) • Matrix.vecMulVec (z i) (z i)

/-- First variation along `t`: `∑ᵢ ν′(uᵢ)·cᵢ·zᵢzᵢᵀ`. -/
noncomputable def batchMatrixDeriv {m s : ℕ}
    (z : Fin m → Fin s → ℝ) (u c : Fin m → ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  ∑ i, (weightDeriv (u i) * c i) • Matrix.vecMulVec (z i) (z i)

/-- Second variation along `t`: `∑ᵢ ν″(uᵢ)·cᵢ²·zᵢzᵢᵀ`. -/
noncomputable def batchMatrixDeriv2 {m s : ℕ}
    (z : Fin m → Fin s → ℝ) (u c : Fin m → ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  ∑ i, (weightDeriv2 (u i) * c i ^ 2) • Matrix.vecMulVec (z i) (z i)

/-- Second variation along a general barrier path: with `cᵢ = uᵢ'` and
`dᵢ = uᵢ''`, this is `∑ᵢ (ν″(uᵢ)·cᵢ² + ν′(uᵢ)·dᵢ)·zᵢzᵢᵀ`.  The second
summand is where the row barrier's quadratic energy contributes the
paper's negative diagonal `D`. -/
noncomputable def batchMatrixDeriv2Gen {m s : ℕ}
    (z : Fin m → Fin s → ℝ) (u c d : Fin m → ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  ∑ i, (weightDeriv2 (u i) * c i ^ 2 + weightDeriv (u i) * d i) •
    Matrix.vecMulVec (z i) (z i)

theorem batchMatrix_apply {m s : ℕ} (M0 : Matrix (Fin s) (Fin s) ℝ)
    (z : Fin m → Fin s → ℝ) (u : Fin m → ℝ) (j k : Fin s) :
    batchMatrix M0 z u j k =
      M0 j k + ∑ i, weight (u i) * (z i j * z i k) := by
  unfold batchMatrix
  rw [Matrix.add_apply, Matrix.sum_apply]
  congr 1

theorem batchMatrixDeriv_apply {m s : ℕ}
    (z : Fin m → Fin s → ℝ) (u c : Fin m → ℝ) (j k : Fin s) :
    batchMatrixDeriv z u c j k =
      ∑ i, weightDeriv (u i) * c i * (z i j * z i k) := by
  unfold batchMatrixDeriv
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]

theorem batchMatrixDeriv2_apply {m s : ℕ}
    (z : Fin m → Fin s → ℝ) (u c : Fin m → ℝ) (j k : Fin s) :
    batchMatrixDeriv2 z u c j k =
      ∑ i, weightDeriv2 (u i) * c i ^ 2 * (z i j * z i k) := by
  unfold batchMatrixDeriv2
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]

/-- The affine inner path `t ↦ uᵢ + t·cᵢ`. -/
theorem hasDerivAt_u_path (u c : ℝ) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => u + t * c) c t₀ :=
  (((hasDerivAt_id' t₀).mul_const c).const_add u).congr_deriv (by rw [one_mul])

/-- Entrywise first derivative of the batch matrix along an affine
barrier path. -/
theorem hasDerivAt_batchMatrix_entry {m s : ℕ}
    (M0 : Matrix (Fin s) (Fin s) ℝ) (z : Fin m → Fin s → ℝ)
    (u c : Fin m → ℝ) (t₀ : ℝ)
    (hu : ∀ i, (1 - (u i + t₀ * c i) / 20000) ≠ 0) (j k : Fin s) :
    HasDerivAt (fun t => batchMatrix M0 z (fun i => u i + t * c i) j k)
      (batchMatrixDeriv z (fun i => u i + t₀ * c i) c j k) t₀ := by
  have hterm : ∀ i : Fin m, HasDerivAt
      (fun t => weight (u i + t * c i) * (z i j * z i k))
      (weightDeriv (u i + t₀ * c i) * c i * (z i j * z i k)) t₀ := fun i =>
    ((hasDerivAt_weight (hu i)).comp t₀ (hasDerivAt_u_path (u i) (c i) t₀)
      |>.mul_const (z i j * z i k)).congr_deriv (by ring)
  rw [show (fun t => batchMatrix M0 z (fun i => u i + t * c i) j k) =
      fun t => M0 j k + ∑ i, weight (u i + t * c i) * (z i j * z i k) from
    funext fun t => batchMatrix_apply M0 z (fun i => u i + t * c i) j k]
  apply HasDerivAt.congr_deriv
    ((hasDerivAt_const t₀ (M0 j k)).add
      (HasDerivAt.fun_sum fun i _ => hterm i))
  rw [zero_add, batchMatrixDeriv_apply]

/-- Entrywise derivative of the first-variation path: `(M')' = M''`. -/
theorem hasDerivAt_batchMatrixDeriv_entry {m s : ℕ}
    (z : Fin m → Fin s → ℝ) (u c : Fin m → ℝ) (t₀ : ℝ)
    (hu : ∀ i, (1 - (u i + t₀ * c i) / 20000) ≠ 0) (j k : Fin s) :
    HasDerivAt
      (fun t => batchMatrixDeriv z (fun i => u i + t * c i) c j k)
      (batchMatrixDeriv2 z (fun i => u i + t₀ * c i) c j k) t₀ := by
  have hterm : ∀ i : Fin m, HasDerivAt
      (fun t => weightDeriv (u i + t * c i) * c i * (z i j * z i k))
      (weightDeriv2 (u i + t₀ * c i) * c i ^ 2 * (z i j * z i k)) t₀ := by
    intro i
    have hc := ((hasDerivAt_weightDeriv (hu i)).comp t₀
      (hasDerivAt_u_path (u i) (c i) t₀)).mul_const (c i * (z i j * z i k))
    rw [show (fun t => weightDeriv (u i + t * c i) * c i * (z i j * z i k)) =
        fun t => weightDeriv (u i + t * c i) * (c i * (z i j * z i k)) from
      funext fun t => by ring]
    exact hc.congr_deriv (by ring)
  rw [show (fun t => batchMatrixDeriv z (fun i => u i + t * c i) c j k) =
      fun t => ∑ i, weightDeriv (u i + t * c i) * c i * (z i j * z i k) from
    funext fun t => batchMatrixDeriv_apply z (fun i => u i + t * c i) c j k]
  apply HasDerivAt.congr_deriv
    (HasDerivAt.fun_sum fun i _ => hterm i)
  rw [batchMatrixDeriv2_apply]

theorem batchMatrixDeriv2Gen_apply {m s : ℕ}
    (z : Fin m → Fin s → ℝ) (u c d : Fin m → ℝ) (j k : Fin s) :
    batchMatrixDeriv2Gen z u c d j k =
      ∑ i, (weightDeriv2 (u i) * c i ^ 2 + weightDeriv (u i) * d i) *
        (z i j * z i k) := by
  unfold batchMatrixDeriv2Gen
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]

/-- The quadratic barrier path `t ↦ uᵢ + t·cᵢ − t²·dᵢ`, the exact form of
the row barriers along a straight walk direction (2.2). -/
theorem hasDerivAt_u_quad (u c d t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => u + t * c - t ^ 2 * d) (c - 2 * t₀ * d) t₀ := by
  apply HasDerivAt.congr_deriv
    ((((hasDerivAt_id' t₀).mul_const c).const_add u).sub
      (((hasDerivAt_id' t₀).pow 2).mul_const d))
  simp only [Nat.reduceSub, pow_one]
  ring

/-- Entrywise first derivative of the batch matrix along a quadratic
barrier path `uᵢ(t) = uᵢ + t·cᵢ − t²·dᵢ`. -/
theorem hasDerivAt_batchMatrix_quad_entry {m s : ℕ}
    (M0 : Matrix (Fin s) (Fin s) ℝ) (z : Fin m → Fin s → ℝ)
    (u c d : Fin m → ℝ) (t₀ : ℝ)
    (hu : ∀ i, (1 - (u i + t₀ * c i - t₀ ^ 2 * d i) / 20000) ≠ 0)
    (j k : Fin s) :
    HasDerivAt
      (fun t => batchMatrix M0 z
        (fun i => u i + t * c i - t ^ 2 * d i) j k)
      (batchMatrixDeriv z (fun i => u i + t₀ * c i - t₀ ^ 2 * d i)
        (fun i => c i - 2 * t₀ * d i) j k) t₀ := by
  have hterm : ∀ i : Fin m, HasDerivAt
      (fun t => weight (u i + t * c i - t ^ 2 * d i) * (z i j * z i k))
      (weightDeriv (u i + t₀ * c i - t₀ ^ 2 * d i) *
        (c i - 2 * t₀ * d i) * (z i j * z i k)) t₀ := fun i =>
    ((hasDerivAt_weight (hu i)).comp t₀
      (hasDerivAt_u_quad (u i) (c i) (d i) t₀)
      |>.mul_const (z i j * z i k)).congr_deriv (by ring)
  rw [show (fun t => batchMatrix M0 z
      (fun i => u i + t * c i - t ^ 2 * d i) j k) =
      fun t => M0 j k +
        ∑ i, weight (u i + t * c i - t ^ 2 * d i) * (z i j * z i k) from
    funext fun t => batchMatrix_apply M0 z
      (fun i => u i + t * c i - t ^ 2 * d i) j k]
  apply HasDerivAt.congr_deriv
    ((hasDerivAt_const t₀ (M0 j k)).add
      (HasDerivAt.fun_sum fun i _ => hterm i))
  rw [zero_add, batchMatrixDeriv_apply]

/-- Entrywise second derivative along the quadratic path: the
`(cᵢ − 2tdᵢ)`-slope batch matrix has derivative `M''`. -/
theorem hasDerivAt_batchMatrixDeriv_quad_entry {m s : ℕ}
    (z : Fin m → Fin s → ℝ) (u c d : Fin m → ℝ) (t₀ : ℝ)
    (hu : ∀ i, (1 - (u i + t₀ * c i - t₀ ^ 2 * d i) / 20000) ≠ 0)
    (j k : Fin s) :
    HasDerivAt
      (fun t => batchMatrixDeriv z
        (fun i => u i + t * c i - t ^ 2 * d i)
        (fun i => c i - 2 * t * d i) j k)
      (batchMatrixDeriv2Gen z (fun i => u i + t₀ * c i - t₀ ^ 2 * d i)
        (fun i => c i - 2 * t₀ * d i) (fun i => -(2 * d i)) j k) t₀ := by
  have hslope : ∀ i : Fin m, HasDerivAt (fun t : ℝ => c i - 2 * t * d i)
      (-(2 * d i)) t₀ := fun i =>
    (((hasDerivAt_id' t₀).const_mul 2 |>.mul_const (d i)).const_sub (c i))
      |>.congr_deriv (by ring)
  have hterm : ∀ i : Fin m, HasDerivAt
      (fun t => weightDeriv (u i + t * c i - t ^ 2 * d i) *
        (c i - 2 * t * d i) * (z i j * z i k))
      ((weightDeriv2 (u i + t₀ * c i - t₀ ^ 2 * d i) *
          (c i - 2 * t₀ * d i) * (c i - 2 * t₀ * d i) +
        weightDeriv (u i + t₀ * c i - t₀ ^ 2 * d i) * (-(2 * d i))) *
        (z i j * z i k)) t₀ := by
    intro i
    have hw := (hasDerivAt_weightDeriv (hu i)).comp t₀
      (hasDerivAt_u_quad (u i) (c i) (d i) t₀)
    have hprod := (hw.mul (hslope i)).mul_const (z i j * z i k)
    refine hprod.congr_deriv ?_
    simp only [Function.comp_apply]
    try ring
  rw [show (fun t => batchMatrixDeriv z
      (fun i => u i + t * c i - t ^ 2 * d i)
      (fun i => c i - 2 * t * d i) j k) =
      fun t => ∑ i, weightDeriv (u i + t * c i - t ^ 2 * d i) *
        (c i - 2 * t * d i) * (z i j * z i k) from
    funext fun t => batchMatrixDeriv_apply z
      (fun i => u i + t * c i - t ^ 2 * d i)
      (fun i => c i - 2 * t * d i) j k]
  apply HasDerivAt.congr_deriv
    (HasDerivAt.fun_sum fun i _ => hterm i)
  rw [batchMatrixDeriv2Gen_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The slack `bI − M(t)` has entrywise derivative `−M'(t)`. -/
theorem hasDerivAt_slack_batch_entry {m s : ℕ} (b : ℝ)
    (M0 : Matrix (Fin s) (Fin s) ℝ) (z : Fin m → Fin s → ℝ)
    (u c : Fin m → ℝ) (t₀ : ℝ)
    (hu : ∀ i, (1 - (u i + t₀ * c i) / 20000) ≠ 0) (j k : Fin s) :
    HasDerivAt
      (fun t => slackMatrix b (batchMatrix M0 z
        (fun i => u i + t * c i)) j k)
      (-(batchMatrixDeriv z (fun i => u i + t₀ * c i) c j k)) t₀ := by
  rw [show (fun t => slackMatrix b (batchMatrix M0 z
      (fun i => u i + t * c i)) j k) =
      fun t => (Matrix.diagonal (fun _ : Fin s => b)) j k -
        batchMatrix M0 z (fun i => u i + t * c i) j k from
    funext fun t => by
      simp only [slackMatrix, Matrix.sub_apply]]
  apply HasDerivAt.congr_deriv
    ((hasDerivAt_const t₀ _).sub (hasDerivAt_batchMatrix_entry M0 z u c t₀ hu j k))
  rw [zero_sub]

/-- The derivative path `t ↦ −M'(t)` differentiates to `−M''(t)`. -/
theorem hasDerivAt_neg_batchDeriv_entry {m s : ℕ}
    (z : Fin m → Fin s → ℝ) (u c : Fin m → ℝ) (t₀ : ℝ)
    (hu : ∀ i, (1 - (u i + t₀ * c i) / 20000) ≠ 0) (j k : Fin s) :
    HasDerivAt
      (fun t => -(batchMatrixDeriv z (fun i => u i + t * c i) c j k))
      (-(batchMatrixDeriv2 z (fun i => u i + t₀ * c i) c j k)) t₀ :=
  (hasDerivAt_batchMatrixDeriv_entry z u c t₀ hu j k).neg

/-! ## Concavity of the resolvent potential on a trust window -/

/-- `R·(−X)·R·(−X)·R = R·X·R·X·R` — the two negations cancel. -/
theorem mul_neg_mul_neg_mul_eq {n : ℕ} (R X : Matrix (Fin n) (Fin n) ℝ) :
    R * (-X) * R * (-X) * R = R * X * R * X * R := by
  simp only [mul_neg, neg_mul, neg_neg]

/-- `R·(−X)·R = −(R·X·R)`. -/
theorem mul_neg_mul_eq_neg {n : ℕ} (R X : Matrix (Fin n) (Fin n) ℝ) :
    R * (-X) * R = -(R * X * R) := by
  simp only [mul_neg, neg_mul]

/-- Entry-sum of a negated matrix is the negated entry-sum. -/
theorem sum_sum_neg_apply {s : ℕ} (X : Matrix (Fin s) (Fin s) ℝ) :
    (∑ p : Fin s, ∑ q : Fin s, (-X) p q) = -(∑ p : Fin s, ∑ q : Fin s, X p q) := by
  rw [Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Matrix.neg_apply _ _ _]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_neg_distrib]

/-- **Concavity of the resolvent potential along a batch direction.**
Let `M(t) = M₀ + ∑ᵢ ν(uᵢ + t·cᵢ)·zᵢzᵢᵀ`, `P(t) = bI − M(t)`,
`R(t) = P(t)⁻¹`, `M'`, `M''` the first and second variations.  If `P`
stays invertible on `[lo, hi]` and

`2·∑ᵢⱼ (R M' R M' R)ᵢⱼ + ∑ᵢⱼ (R M'' R)ᵢⱼ ≤ 0`

at every interior point — the paper's curvature inequality
`P_x[h] ≤ (1 − ρ/2) D_x[h]`, since `∇²F = vᵀM''v + 2(M'v)ᵀR(M'v)` equals
`(U[h] − D[h]) + 2(C h)ᵀR(C h)` — then `t ↦ F_b(M(t))` is concave on the
window. -/
theorem concaveOn_resolventPotential_batch {m s : ℕ} (b : ℝ)
    (M0 : Matrix (Fin s) (Fin s) ℝ) (z : Fin m → Fin s → ℝ)
    (u c : Fin m → ℝ) (lo hi : ℝ)
    (hpole : ∀ t ∈ Set.Icc lo hi, ∀ i,
      (1 - (u i + t * c i) / 20000) ≠ 0)
    (hunit : ∀ t ∈ Set.Icc lo hi,
      IsUnit (slackMatrix b (batchMatrix M0 z (fun i => u i + t * c i))))
    (h2 : ∀ t ∈ Set.Ioo lo hi,
      2 * ∑ p : Fin s, ∑ q : Fin s,
          ((slackMatrix b (batchMatrix M0 z
            (fun i => u i + t * c i)))⁻¹ *
            batchMatrixDeriv z (fun i => u i + t * c i) c *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i)))⁻¹ *
            batchMatrixDeriv z (fun i => u i + t * c i) c *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i)))⁻¹) p q +
        ∑ p : Fin s, ∑ q : Fin s,
          ((slackMatrix b (batchMatrix M0 z
            (fun i => u i + t * c i)))⁻¹ *
            batchMatrixDeriv2 z (fun i => u i + t * c i) c *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i)))⁻¹) p q ≤ 0) :
    ConcaveOn ℝ (Set.Icc lo hi)
      (fun t => resolventPotential b
        (batchMatrix M0 z (fun i => u i + t * c i))) := by
  have hP : ∀ t ∈ Set.Icc lo hi, ∀ j k : Fin s,
      HasDerivAt (fun τ => slackMatrix b (batchMatrix M0 z
        (fun i => u i + τ * c i)) j k)
        ((-(batchMatrixDeriv z (fun i => u i + t * c i) c)) j k) t :=
    fun t ht j k =>
      (hasDerivAt_slack_batch_entry b M0 z u c t (hpole t ht) j k).congr_deriv
        (Matrix.neg_apply _ _ _).symm
  have hDp : ∀ t ∈ Set.Icc lo hi, ∀ j k : Fin s,
      HasDerivAt (fun τ => (-(batchMatrixDeriv z (fun i => u i + τ * c i) c)) j k)
        ((-(batchMatrixDeriv2 z (fun i => u i + t * c i) c)) j k) t := by
    intro t ht j k
    rw [show (fun τ : ℝ =>
        (-(batchMatrixDeriv z (fun i => u i + τ * c i) c)) j k) =
        fun τ => -(batchMatrixDeriv z (fun i => u i + τ * c i) c j k) from
      funext fun τ => Matrix.neg_apply _ _ _]
    exact (hasDerivAt_neg_batchDeriv_entry z u c t (hpole t ht) j k).congr_deriv
      (Matrix.neg_apply _ _ _).symm
  have h2' : ∀ t ∈ Set.Ioo lo hi,
      2 * ∑ p : Fin s, ∑ q : Fin s,
          ((slackMatrix b (batchMatrix M0 z (fun i => u i + t * c i)))⁻¹ *
            (-(batchMatrixDeriv z (fun i => u i + t * c i) c)) *
            (slackMatrix b (batchMatrix M0 z (fun i => u i + t * c i)))⁻¹ *
            (-(batchMatrixDeriv z (fun i => u i + t * c i) c)) *
            (slackMatrix b (batchMatrix M0 z (fun i => u i + t * c i)))⁻¹) p q -
        ∑ p : Fin s, ∑ q : Fin s,
          ((slackMatrix b (batchMatrix M0 z (fun i => u i + t * c i)))⁻¹ *
            (-(batchMatrixDeriv2 z (fun i => u i + t * c i) c)) *
            (slackMatrix b (batchMatrix M0 z (fun i => u i + t * c i)))⁻¹) p q ≤ 0 := by
    intro t ht
    have h := h2 t ht
    rw [mul_neg_mul_neg_mul_eq, mul_neg_mul_eq_neg, sum_sum_neg_apply]
    linarith
  have hconc := concaveOn_inv_sum_path
    (fun t => slackMatrix b (batchMatrix M0 z (fun i => u i + t * c i)))
    (fun t => -(batchMatrixDeriv z (fun i => u i + t * c i) c))
    (fun t => -(batchMatrixDeriv2 z (fun i => u i + t * c i) c)) lo hi
    hP hDp hunit h2'
  have hshift : ConcaveOn ℝ (Set.Icc lo hi)
      (fun t : ℝ => (∑ p : Fin s, ∑ q : Fin s,
        (slackMatrix b (batchMatrix M0 z (fun i => u i + t * c i)))⁻¹ p q) +
          (-(s : ℝ) / b)) :=
    ConcaveOn.add_const hconc (-(s : ℝ) / b)
  have heq : (fun t : ℝ => resolventPotential b
      (batchMatrix M0 z (fun i => u i + t * c i))) =
      fun t => (∑ p : Fin s, ∑ q : Fin s,
        (slackMatrix b (batchMatrix M0 z (fun i => u i + t * c i)))⁻¹ p q) +
          (-(s : ℝ) / b) := by
    funext t
    rw [resolventPotential_eq_inv_sum]
    ring
  rw [heq]
  exact hshift

/-- **Proposition 2.1's expectation bound on the batch matrix.** If the
window `±T` keeps the slack invertible and the curvature inequality
holds, the fair-sign average of the potential does not increase:

`(F_b(M(T·c)) + F_b(M(−T·c))) / 2 ≤ F_b(M(0))`. -/
theorem pair_average_resolventPotential_batch {m s : ℕ} (b : ℝ)
    (M0 : Matrix (Fin s) (Fin s) ℝ) (z : Fin m → Fin s → ℝ)
    (u c : Fin m → ℝ) {T : ℝ} (hT : 0 < T)
    (hpole : ∀ t ∈ Set.Icc (-T) T, ∀ i,
      (1 - (u i + t * c i) / 20000) ≠ 0)
    (hunit : ∀ t ∈ Set.Icc (-T) T,
      IsUnit (slackMatrix b (batchMatrix M0 z (fun i => u i + t * c i))))
    (h2 : ∀ t ∈ Set.Ioo (-T) T,
      2 * ∑ p : Fin s, ∑ q : Fin s,
          ((slackMatrix b (batchMatrix M0 z
            (fun i => u i + t * c i)))⁻¹ *
            batchMatrixDeriv z (fun i => u i + t * c i) c *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i)))⁻¹ *
            batchMatrixDeriv z (fun i => u i + t * c i) c *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i)))⁻¹) p q +
        ∑ p : Fin s, ∑ q : Fin s,
          ((slackMatrix b (batchMatrix M0 z
            (fun i => u i + t * c i)))⁻¹ *
            batchMatrixDeriv2 z (fun i => u i + t * c i) c *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i)))⁻¹) p q ≤ 0) :
    (resolventPotential b (batchMatrix M0 z (fun i => u i + T * c i)) +
      resolventPotential b (batchMatrix M0 z (fun i => u i - T * c i))) / 2 ≤
      resolventPotential b (batchMatrix M0 z u) := by
  have hconc := concaveOn_resolventPotential_batch b M0 z u c (-T) T
    hpole hunit h2
  have h := concaveOn_pair_average_le hT hconc
  have hneg : ∀ i : Fin m, u i + -T * c i = u i - T * c i := fun i => by ring
  have hzero : ∀ i : Fin m, u i + (0 : ℝ) * c i = u i := fun i => by ring
  rw [show (fun i : Fin m => u i + -T * c i) = fun i => u i - T * c i from
    funext hneg] at h
  rw [show (fun i : Fin m => u i + (0 : ℝ) * c i) = u from funext hzero] at h
  exact h

/-! ## The quadratic barrier path -/

/-- The quadratic-path slack has entrywise derivative `−M'(t)`, where
`M'(t)` uses the slope `cᵢ − 2tdᵢ`. -/
theorem hasDerivAt_slack_batch_quad_entry {m s : ℕ} (b : ℝ)
    (M0 : Matrix (Fin s) (Fin s) ℝ) (z : Fin m → Fin s → ℝ)
    (u c d : Fin m → ℝ) (t₀ : ℝ)
    (hu : ∀ i, (1 - (u i + t₀ * c i - t₀ ^ 2 * d i) / 20000) ≠ 0)
    (j k : Fin s) :
    HasDerivAt
      (fun t => slackMatrix b (batchMatrix M0 z
        (fun i => u i + t * c i - t ^ 2 * d i)) j k)
      (-(batchMatrixDeriv z (fun i => u i + t₀ * c i - t₀ ^ 2 * d i)
        (fun i => c i - 2 * t₀ * d i) j k)) t₀ := by
  rw [show (fun t => slackMatrix b (batchMatrix M0 z
      (fun i => u i + t * c i - t ^ 2 * d i)) j k) =
      fun t => (Matrix.diagonal (fun _ : Fin s => b)) j k -
        batchMatrix M0 z (fun i => u i + t * c i - t ^ 2 * d i) j k from
    funext fun t => by
      simp only [slackMatrix, Matrix.sub_apply]]
  apply HasDerivAt.congr_deriv
    ((hasDerivAt_const t₀ _).sub
      (hasDerivAt_batchMatrix_quad_entry M0 z u c d t₀ hu j k))
  rw [zero_sub]

/-- The quadratic-path derivative `t ↦ −M'(t)` differentiates to
`−M''(t)` with `M''` including the `−2dᵢ` barrier-curvature term. -/
theorem hasDerivAt_neg_batchDeriv_quad_entry {m s : ℕ}
    (z : Fin m → Fin s → ℝ) (u c d : Fin m → ℝ) (t₀ : ℝ)
    (hu : ∀ i, (1 - (u i + t₀ * c i - t₀ ^ 2 * d i) / 20000) ≠ 0)
    (j k : Fin s) :
    HasDerivAt
      (fun t => -(batchMatrixDeriv z
        (fun i => u i + t * c i - t ^ 2 * d i)
        (fun i => c i - 2 * t * d i) j k))
      (-(batchMatrixDeriv2Gen z (fun i => u i + t₀ * c i - t₀ ^ 2 * d i)
        (fun i => c i - 2 * t₀ * d i) (fun i => -(2 * d i)) j k)) t₀ :=
  (hasDerivAt_batchMatrixDeriv_quad_entry z u c d t₀ hu j k).neg

/-- **Concavity of the resolvent potential along a quadratic barrier
direction.** Along `uᵢ(t) = uᵢ + t·cᵢ − t²·dᵢ` — the exact form of a
row barrier along a straight walk step (2.2) — if the slack stays
invertible on `[lo, hi]` and the curvature inequality

`2·∑ᵢⱼ (R M' R M' R)ᵢⱼ + ∑ᵢⱼ (R M'' R)ᵢⱼ ≤ 0`

holds at every interior point, then `t ↦ F_b(M(t))` is concave on the
window.  The `dᵢ`-term inside `M''` is precisely the paper's negative
diagonal `D` from (2.6). -/
theorem concaveOn_resolventPotential_quad {m s : ℕ} (b : ℝ)
    (M0 : Matrix (Fin s) (Fin s) ℝ) (z : Fin m → Fin s → ℝ)
    (u c d : Fin m → ℝ) (lo hi : ℝ)
    (hpole : ∀ t ∈ Set.Icc lo hi, ∀ i,
      (1 - (u i + t * c i - t ^ 2 * d i) / 20000) ≠ 0)
    (hunit : ∀ t ∈ Set.Icc lo hi,
      IsUnit (slackMatrix b (batchMatrix M0 z
        (fun i => u i + t * c i - t ^ 2 * d i))))
    (h2 : ∀ t ∈ Set.Ioo lo hi,
      2 * ∑ p : Fin s, ∑ q : Fin s,
          ((slackMatrix b (batchMatrix M0 z
            (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *
            batchMatrixDeriv z
              (fun i => u i + t * c i - t ^ 2 * d i)
              (fun i => c i - 2 * t * d i) *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *
            batchMatrixDeriv z
              (fun i => u i + t * c i - t ^ 2 * d i)
              (fun i => c i - 2 * t * d i) *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹) p q +
        ∑ p : Fin s, ∑ q : Fin s,
          ((slackMatrix b (batchMatrix M0 z
            (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *
            batchMatrixDeriv2Gen z
              (fun i => u i + t * c i - t ^ 2 * d i)
              (fun i => c i - 2 * t * d i) (fun i => -(2 * d i)) *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹) p q ≤ 0) :
    ConcaveOn ℝ (Set.Icc lo hi)
      (fun t => resolventPotential b
        (batchMatrix M0 z (fun i => u i + t * c i - t ^ 2 * d i))) := by
  have hP : ∀ t ∈ Set.Icc lo hi, ∀ j k : Fin s,
      HasDerivAt (fun τ => slackMatrix b (batchMatrix M0 z
        (fun i => u i + τ * c i - τ ^ 2 * d i)) j k)
        ((-(batchMatrixDeriv z (fun i => u i + t * c i - t ^ 2 * d i)
          (fun i => c i - 2 * t * d i))) j k) t :=
    fun t ht j k =>
      (hasDerivAt_slack_batch_quad_entry b M0 z u c d t (hpole t ht) j k)
        |>.congr_deriv (Matrix.neg_apply _ _ _).symm
  have hDp : ∀ t ∈ Set.Icc lo hi, ∀ j k : Fin s,
      HasDerivAt (fun τ =>
        (-(batchMatrixDeriv z (fun i => u i + τ * c i - τ ^ 2 * d i)
          (fun i => c i - 2 * τ * d i))) j k)
        ((-(batchMatrixDeriv2Gen z
          (fun i => u i + t * c i - t ^ 2 * d i)
          (fun i => c i - 2 * t * d i) (fun i => -(2 * d i)))) j k) t := by
    intro t ht j k
    rw [show (fun τ : ℝ =>
        (-(batchMatrixDeriv z (fun i => u i + τ * c i - τ ^ 2 * d i)
          (fun i => c i - 2 * τ * d i))) j k) =
        fun τ => -(batchMatrixDeriv z
          (fun i => u i + τ * c i - τ ^ 2 * d i)
          (fun i => c i - 2 * τ * d i) j k) from
      funext fun τ => Matrix.neg_apply _ _ _]
    exact (hasDerivAt_neg_batchDeriv_quad_entry z u c d t (hpole t ht) j k)
      |>.congr_deriv (Matrix.neg_apply _ _ _).symm
  have h2' : ∀ t ∈ Set.Ioo lo hi,
      2 * ∑ p : Fin s, ∑ q : Fin s,
          ((slackMatrix b (batchMatrix M0 z
            (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *
            (-(batchMatrixDeriv z
              (fun i => u i + t * c i - t ^ 2 * d i)
              (fun i => c i - 2 * t * d i))) *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *
            (-(batchMatrixDeriv z
              (fun i => u i + t * c i - t ^ 2 * d i)
              (fun i => c i - 2 * t * d i))) *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹) p q -
        ∑ p : Fin s, ∑ q : Fin s,
          ((slackMatrix b (batchMatrix M0 z
            (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *
            (-(batchMatrixDeriv2Gen z
              (fun i => u i + t * c i - t ^ 2 * d i)
              (fun i => c i - 2 * t * d i) (fun i => -(2 * d i)))) *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹) p q ≤ 0 := by
    intro t ht
    have h := h2 t ht
    rw [mul_neg_mul_neg_mul_eq, mul_neg_mul_eq_neg, sum_sum_neg_apply]
    linarith
  have hconc := concaveOn_inv_sum_path
    (fun t => slackMatrix b (batchMatrix M0 z
      (fun i => u i + t * c i - t ^ 2 * d i)))
    (fun t => -(batchMatrixDeriv z (fun i => u i + t * c i - t ^ 2 * d i)
      (fun i => c i - 2 * t * d i)))
    (fun t => -(batchMatrixDeriv2Gen z
      (fun i => u i + t * c i - t ^ 2 * d i)
      (fun i => c i - 2 * t * d i) (fun i => -(2 * d i)))) lo hi
    hP hDp hunit h2'
  have hshift : ConcaveOn ℝ (Set.Icc lo hi)
      (fun t : ℝ => (∑ p : Fin s, ∑ q : Fin s,
        (slackMatrix b (batchMatrix M0 z
          (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ p q) +
          (-(s : ℝ) / b)) :=
    ConcaveOn.add_const hconc (-(s : ℝ) / b)
  have heq : (fun t : ℝ => resolventPotential b
      (batchMatrix M0 z (fun i => u i + t * c i - t ^ 2 * d i))) =
      fun t => (∑ p : Fin s, ∑ q : Fin s,
        (slackMatrix b (batchMatrix M0 z
          (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ p q) +
          (-(s : ℝ) / b) := by
    funext t
    rw [resolventPotential_eq_inv_sum]
    ring
  rw [heq]
  exact hshift

/-- **Proposition 2.1's expectation bound along a true walk step.** For
the quadratic barrier path (2.2), if the `±T` window keeps the slack
invertible and the curvature inequality holds, the fair-sign average of
the potential does not increase. -/
theorem pair_average_resolventPotential_quad {m s : ℕ} (b : ℝ)
    (M0 : Matrix (Fin s) (Fin s) ℝ) (z : Fin m → Fin s → ℝ)
    (u c d : Fin m → ℝ) {T : ℝ} (hT : 0 < T)
    (hpole : ∀ t ∈ Set.Icc (-T) T, ∀ i,
      (1 - (u i + t * c i - t ^ 2 * d i) / 20000) ≠ 0)
    (hunit : ∀ t ∈ Set.Icc (-T) T,
      IsUnit (slackMatrix b (batchMatrix M0 z
        (fun i => u i + t * c i - t ^ 2 * d i))))
    (h2 : ∀ t ∈ Set.Ioo (-T) T,
      2 * ∑ p : Fin s, ∑ q : Fin s,
          ((slackMatrix b (batchMatrix M0 z
            (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *
            batchMatrixDeriv z
              (fun i => u i + t * c i - t ^ 2 * d i)
              (fun i => c i - 2 * t * d i) *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *
            batchMatrixDeriv z
              (fun i => u i + t * c i - t ^ 2 * d i)
              (fun i => c i - 2 * t * d i) *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹) p q +
        ∑ p : Fin s, ∑ q : Fin s,
          ((slackMatrix b (batchMatrix M0 z
            (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *
            batchMatrixDeriv2Gen z
              (fun i => u i + t * c i - t ^ 2 * d i)
              (fun i => c i - 2 * t * d i) (fun i => -(2 * d i)) *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹) p q ≤ 0) :
    (resolventPotential b (batchMatrix M0 z
        (fun i => u i + T * c i - T ^ 2 * d i)) +
      resolventPotential b (batchMatrix M0 z
        (fun i => u i - T * c i - T ^ 2 * d i))) / 2 ≤
      resolventPotential b (batchMatrix M0 z u) := by
  have hconc := concaveOn_resolventPotential_quad b M0 z u c d (-T) T
    hpole hunit h2
  have h := concaveOn_pair_average_le hT hconc
  have hneg : ∀ i : Fin m, u i + -T * c i - (-T) ^ 2 * d i =
      u i - T * c i - T ^ 2 * d i := fun i => by ring
  have hzero : ∀ i : Fin m, u i + (0 : ℝ) * c i - (0 : ℝ) ^ 2 * d i = u i :=
    fun i => by ring
  rw [show (fun i : Fin m => u i + -T * c i - (-T) ^ 2 * d i) =
      fun i => u i - T * c i - T ^ 2 * d i from funext hneg] at h
  rw [show (fun i : Fin m => u i + (0 : ℝ) * c i - (0 : ℝ) ^ 2 * d i) = u
      from funext hzero] at h
  exact h

end Komlos
