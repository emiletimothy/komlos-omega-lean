import Komlos.MatrixInverse

/-!
# Entrywise resolvent stability: the (B.5) estimates

Appendix B of the paper bounds the displacement of the resolvent vector
`v = (bI − M)⁻¹·1` and of the associated quadratic forms when the matrix
`M` moves from its anchor `M₀` to `Mx` inside the trust window.  This
module proves the entrywise/quadratic-form level of that chain; no
operator-norm arguments are needed.

## The (B.5) resolvent-vector bound

Writing `Ax = slackMatrix b Mx = bI − Mx`, the coordinatewise resolvent
equations `b·v₀ⱼ = 1 + (M₀v₀)ⱼ` and `b·vxⱼ = 1 + (Mx·vx)ⱼ` give the
exact identity (`resolvent_vector_diff_eq`)

    vx − v₀ = Ax⁻¹ *ᵥ ((Mx − M₀) *ᵥ v₀).

Since `Ax` is positive definite and `Mx ≥ 0`, the inverse `Ax⁻¹` is
entrywise nonnegative (`slack_inverse_entrywise_nonneg`), so a
deposit-relative error `|((Mx − M₀)·v₀)ⱼ| ≤ ε·b·v₀ⱼ` yields

    |vxⱼ − v₀ⱼ| ≤ ε·(Ax⁻¹ *ᵥ (b • v₀))ⱼ
              = ε·(vxⱼ + (Ax⁻¹ *ᵥ (M₀ *ᵥ v₀))ⱼ),

the correction form proved in `resolvent_vector_stability_correction`
(using `b•v₀ = 1 + M₀·v₀` and `Ax⁻¹*ᵥ1 = vx`).  Capping the deposit by
`b·v₀ⱼ ≤ B` turns the bound into the clean relative form

    |vxⱼ − v₀ⱼ| ≤ ε·B·vxⱼ

proved in `resolvent_vector_stability`.  **Note the reference vector is
`vx`, the *new* vector**: this is the form the nonnegative resolvent
yields directly (matching `resolvent_vector_relative_change` in
`MatrixInverse.lean`).  The two-sided comparison
`(1−εB)·vx ≤ v₀ ≤ (1+εB)·vx` and, when `ε·B < 1`, the
anchor-relative variant `|vxⱼ − v₀ⱼ| ≤ (εB/(1−εB))·v₀ⱼ` follow in
`resolvent_vector_stability_two_sided` and
`resolvent_vector_stability_rel`.

## Load stability

For `z ≥ 0` and loads `tᵢ = zᵢᵀv`, entrywise relative control of the
vector transports to the loads without Cauchy–Schwarz:
`|zᵢᵀv' − zᵢᵀv| ≤ ε·zᵢᵀv` (`z_dot_stability`).

## Quadratic-form slack comparison

The paper's `M` is the weighted Gram matrix `∑ᵢ wᵢ zᵢzᵢᵀ`, recorded
here as `gramMatrix z w` with `xᵀMx = ∑ᵢ wᵢ(zᵢᵀx)²`
(`dotProduct_mulVec_gramMatrix`).  A relative weight perturbation
`|w'ᵢ − wᵢ| ≤ ε·wᵢ` gives `|Q'[h] − Q[h]| ≤ ε·Q[h]`
(`weighted_gram_qf_perturbation`), and since the slack difference is
`Aₓ[h] − A₀[h] = Q[h] − Q'[h]` (`slackQuadratic_sub_eq`), the
domination `Q[h] ≤ κ·A₀[h]` — supplied in applications by
`weighted_gram_slack_domination` — closes the (B.5) conclusion

    Aₓ[h] ≥ (1 − εκ)·A₀[h]

in `slackQuadratic_stability`.
-/

namespace Komlos

open scoped BigOperators
open Matrix

/-! ## The resolvent-vector perturbation identity -/

/-- Any vector satisfying the coordinatewise resolvent equation
`b·vⱼ = 1 + (Mv)ⱼ` is the resolvent vector `resolventVector b M`. -/
theorem eq_resolventVector {s : ℕ} {b : ℝ} {M : Input s s} {v : Fin s → ℝ}
    (hpos : (slackMatrix b M).PosDef)
    (hv : ∀ j, b * v j = 1 + ∑ k, M j k * v k) :
    v = resolventVector b M := by
  have hunit : IsUnit (slackMatrix b M).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hpos.isUnit
  have e : slackMatrix b M *ᵥ v = fun _ => (1 : ℝ) := by
    funext j
    rw [congrFun (slackMatrix_mulVec b M v) j]
    show b * v j - ∑ k, M j k * v k = 1
    linarith [hv j]
  calc v = (slackMatrix b M)⁻¹ *ᵥ (slackMatrix b M *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit,
          Matrix.one_mulVec]
    _ = resolventVector b M :=
      congrArg (fun w => (slackMatrix b M)⁻¹ *ᵥ w) e

/-- The difference of the two resolvent solutions is the moved resolvent
applied to the deposit error: `Ax·(vx − v₀) = (Mx − M₀)·v₀`. -/
theorem resolvent_vector_diff_eq {s : ℕ} {b : ℝ} {M₀ Mx : Input s s}
    {v₀ vx : Fin s → ℝ}
    (hpos : (slackMatrix b Mx).PosDef)
    (hv₀ : ∀ j, b * v₀ j = 1 + ∑ k, M₀ j k * v₀ k)
    (hvx : ∀ j, b * vx j = 1 + ∑ k, Mx j k * vx k) :
    vx - v₀ = (slackMatrix b Mx)⁻¹ *ᵥ ((Mx - M₀) *ᵥ v₀) := by
  have hunit : IsUnit (slackMatrix b Mx).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hpos.isUnit
  have e : slackMatrix b Mx *ᵥ (vx - v₀) = (Mx - M₀) *ᵥ v₀ := by
    funext j
    rw [congrFun (slackMatrix_mulVec b Mx (vx - v₀)) j,
      congrFun (Matrix.sub_mulVec Mx M₀ v₀) j]
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
    have h1 : b * (vx j - v₀ j) =
        (∑ k, Mx j k * vx k) - ∑ k, M₀ j k * v₀ k := by
      rw [mul_sub, hvx j, hv₀ j]
      ring
    have h2 : (∑ k, Mx j k * (vx k - v₀ k)) =
        (∑ k, Mx j k * vx k) - ∑ k, Mx j k * v₀ k := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h1, h2]
    ring
  calc vx - v₀ =
      (slackMatrix b Mx)⁻¹ *ᵥ (slackMatrix b Mx *ᵥ (vx - v₀)) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit,
          Matrix.one_mulVec]
    _ = (slackMatrix b Mx)⁻¹ *ᵥ ((Mx - M₀) *ᵥ v₀) := by rw [e]

/-! ## The (B.5) resolvent-vector bounds -/

/-- **Correction form.** `|vxⱼ − v₀ⱼ| ≤ ε·(vxⱼ + (Ax⁻¹·M₀·v₀)ⱼ)`.
Since `Ax⁻¹·(b•v₀) = Ax⁻¹·(1 + M₀·v₀) = vx + Ax⁻¹·(M₀·v₀)`, the deposit
error `≤ ε·b·v₀` transported through the nonnegative inverse is exactly
`ε` times `vx` plus the nonnegative correction `Ax⁻¹·(M₀·v₀)`.  No cap on
`b·v₀` is needed for this form. -/
theorem resolvent_vector_stability_correction {s : ℕ} {b ε : ℝ}
    {M₀ Mx : Input s s} {v₀ vx : Fin s → ℝ}
    (hMx : ∀ j k, 0 ≤ Mx j k)
    (hpos : (slackMatrix b Mx).PosDef)
    (hv₀ : ∀ j, b * v₀ j = 1 + ∑ k, M₀ j k * v₀ k)
    (hvx : ∀ j, b * vx j = 1 + ∑ k, Mx j k * vx k)
    (_hε : 0 ≤ ε)
    (herr : ∀ j, |((Mx - M₀) *ᵥ v₀) j| ≤ ε * (b * v₀ j))
    (j : Fin s) :
    |vx j - v₀ j| ≤
      ε * (vx j + ((slackMatrix b Mx)⁻¹ *ᵥ (M₀ *ᵥ v₀)) j) := by
  have hnn : ∀ k, 0 ≤ (slackMatrix b Mx)⁻¹ j k :=
    fun k => slack_inverse_entrywise_nonneg hMx hpos j k
  have hvxinv : vx = resolventVector b Mx := eq_resolventVector hpos hvx
  have hbv₀ : b • v₀ = (fun _ => (1 : ℝ)) + M₀ *ᵥ v₀ := by
    funext j'
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Matrix.mulVec,
      dotProduct]
    linarith [hv₀ j']
  have hsplit : (slackMatrix b Mx)⁻¹ *ᵥ (b • v₀) =
      vx + (slackMatrix b Mx)⁻¹ *ᵥ (M₀ *ᵥ v₀) := by
    have h1 : (slackMatrix b Mx)⁻¹ *ᵥ (fun _ => (1 : ℝ)) = vx := hvxinv.symm
    rw [hbv₀, Matrix.mulVec_add, h1]
  have hvdiff := resolvent_vector_diff_eq hpos hv₀ hvx
  have hle : |vx j - v₀ j| ≤
      ε * ((slackMatrix b Mx)⁻¹ *ᵥ (b • v₀)) j := by
    rw [← Pi.sub_apply, hvdiff]
    calc |((slackMatrix b Mx)⁻¹ *ᵥ ((Mx - M₀) *ᵥ v₀)) j|
        = |∑ k, (slackMatrix b Mx)⁻¹ j k * ((Mx - M₀) *ᵥ v₀) k| := rfl
      _ ≤ ∑ k, |(slackMatrix b Mx)⁻¹ j k * ((Mx - M₀) *ᵥ v₀) k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, (slackMatrix b Mx)⁻¹ j k * (ε * (b * v₀ k)) := by
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul, abs_of_nonneg (hnn k)]
          exact mul_le_mul_of_nonneg_left (herr k) (hnn k)
      _ = ε * ((slackMatrix b Mx)⁻¹ *ᵥ (b • v₀)) j := by
          show ∑ k, (slackMatrix b Mx)⁻¹ j k * (ε * (b * v₀ k)) =
            ε * ∑ k, (slackMatrix b Mx)⁻¹ j k * (b • v₀) k
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
  rwa [hsplit, Pi.add_apply] at hle

/-- **The (B.5) bound, capped form.**  With the deposit cap
`b·v₀ⱼ ≤ B`, the entrywise relative perturbation `≤ ε·b·v₀` gives
`|vxⱼ − v₀ⱼ| ≤ ε·B·vxⱼ`, relative to the *new* vector `vx`. -/
theorem resolvent_vector_stability {s : ℕ} {b ε B : ℝ} {M₀ Mx : Input s s}
    {v₀ vx : Fin s → ℝ}
    (hMx : ∀ j k, 0 ≤ Mx j k)
    (hpos : (slackMatrix b Mx).PosDef)
    (hv₀ : ∀ j, b * v₀ j = 1 + ∑ k, M₀ j k * v₀ k)
    (hvx : ∀ j, b * vx j = 1 + ∑ k, Mx j k * vx k)
    (hB : ∀ j, b * v₀ j ≤ B)
    (hε : 0 ≤ ε)
    (herr : ∀ j, |((Mx - M₀) *ᵥ v₀) j| ≤ ε * (b * v₀ j))
    (j : Fin s) :
    |vx j - v₀ j| ≤ ε * B * vx j := by
  have hnn : ∀ k, 0 ≤ (slackMatrix b Mx)⁻¹ j k :=
    fun k => slack_inverse_entrywise_nonneg hMx hpos j k
  have hvxinv : vx = resolventVector b Mx := eq_resolventVector hpos hvx
  have hvxj : vx j = ∑ k, (slackMatrix b Mx)⁻¹ j k := by
    rw [hvxinv]
    simp only [resolventVector, Matrix.mulVec, dotProduct, mul_one]
  have hvdiff := resolvent_vector_diff_eq hpos hv₀ hvx
  rw [← Pi.sub_apply, hvdiff]
  calc |((slackMatrix b Mx)⁻¹ *ᵥ ((Mx - M₀) *ᵥ v₀)) j|
      = |∑ k, (slackMatrix b Mx)⁻¹ j k * ((Mx - M₀) *ᵥ v₀) k| := rfl
    _ ≤ ∑ k, |(slackMatrix b Mx)⁻¹ j k * ((Mx - M₀) *ᵥ v₀) k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, (slackMatrix b Mx)⁻¹ j k * (ε * (b * v₀ k)) := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul, abs_of_nonneg (hnn k)]
        exact mul_le_mul_of_nonneg_left (herr k) (hnn k)
    _ = ε * ∑ k, (slackMatrix b Mx)⁻¹ j k * (b * v₀ k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ ≤ ε * ∑ k, (slackMatrix b Mx)⁻¹ j k * B := by
        apply mul_le_mul_of_nonneg_left _ hε
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hB k) (hnn k)
    _ = ε * B * vx j := by
        rw [← Finset.sum_mul, ← hvxj]
        ring

/-- Two-sided form of the (B.5) bound:
`(1 − εB)·vx ≤ v₀ ≤ (1 + εB)·vx` entrywise. -/
theorem resolvent_vector_stability_two_sided {s : ℕ} {b ε B : ℝ}
    {M₀ Mx : Input s s} {v₀ vx : Fin s → ℝ}
    (hMx : ∀ j k, 0 ≤ Mx j k)
    (hpos : (slackMatrix b Mx).PosDef)
    (hv₀ : ∀ j, b * v₀ j = 1 + ∑ k, M₀ j k * v₀ k)
    (hvx : ∀ j, b * vx j = 1 + ∑ k, Mx j k * vx k)
    (hB : ∀ j, b * v₀ j ≤ B)
    (hε : 0 ≤ ε)
    (herr : ∀ j, |((Mx - M₀) *ᵥ v₀) j| ≤ ε * (b * v₀ j))
    (j : Fin s) :
    (1 - ε * B) * vx j ≤ v₀ j ∧ v₀ j ≤ (1 + ε * B) * vx j := by
  have h := abs_le.mp
    (resolvent_vector_stability hMx hpos hv₀ hvx hB hε herr j)
  constructor <;> linarith [h.1, h.2]

/-- **Anchor-relative form.**  When `ε·B < 1`, the new-vector bound
`|vx − v₀| ≤ εB·vx` solves to the old-vector bound
`|vxⱼ − v₀ⱼ| ≤ (εB/(1−εB))·v₀ⱼ`. -/
theorem resolvent_vector_stability_rel {s : ℕ} {b ε B : ℝ}
    {M₀ Mx : Input s s} {v₀ vx : Fin s → ℝ}
    (hMx : ∀ j k, 0 ≤ Mx j k)
    (hpos : (slackMatrix b Mx).PosDef)
    (hv₀ : ∀ j, b * v₀ j = 1 + ∑ k, M₀ j k * v₀ k)
    (hvx : ∀ j, b * vx j = 1 + ∑ k, Mx j k * vx k)
    (hB : ∀ j, b * v₀ j ≤ B)
    (hB0 : 0 ≤ B)
    (hε : 0 ≤ ε)
    (herr : ∀ j, |((Mx - M₀) *ᵥ v₀) j| ≤ ε * (b * v₀ j))
    (hεB : ε * B < 1)
    (j : Fin s) :
    |vx j - v₀ j| ≤ (ε * B / (1 - ε * B)) * v₀ j := by
  have h := resolvent_vector_stability hMx hpos hv₀ hvx hB hε herr j
  have hb := resolvent_vector_stability_two_sided
    hMx hpos hv₀ hvx hB hε herr j
  have h1 : (0 : ℝ) < 1 - ε * B := by linarith
  have hvxle : vx j ≤ v₀ j / (1 - ε * B) := by
    rw [le_div_iff₀ h1]
    linarith [hb.1]
  calc |vx j - v₀ j| ≤ ε * B * vx j := h
    _ ≤ ε * B * (v₀ j / (1 - ε * B)) :=
        mul_le_mul_of_nonneg_left hvxle (mul_nonneg hε hB0)
    _ = (ε * B / (1 - ε * B)) * v₀ j := by ring

/-! ## Load stability -/

/-- **Load stability.**  For `z ≥ 0` entrywise and loads `tᵢ = zᵢᵀv`,
entrywise relative control `|v'ⱼ − vⱼ| ≤ ε·vⱼ` transports to the loads:
`|zᵢᵀv' − zᵢᵀv| ≤ ε·(zᵢᵀv)`.  No Cauchy–Schwarz is needed since `z`
has a sign. -/
theorem z_dot_stability {m s : ℕ} {z : Fin m → Fin s → ℝ}
    {v v' : Fin s → ℝ} {ε : ℝ}
    (hz : ∀ i j, 0 ≤ z i j)
    (h : ∀ j, |v' j - v j| ≤ ε * v j) (i : Fin m) :
    |z i ⬝ᵥ v' - z i ⬝ᵥ v| ≤ ε * (z i ⬝ᵥ v) := by
  rw [← dotProduct_sub]
  calc |z i ⬝ᵥ (v' - v)| = |∑ j, z i j * (v' - v) j| := rfl
    _ ≤ ∑ j, |z i j * (v' - v) j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, z i j * |v' j - v j| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Pi.sub_apply, abs_mul, abs_of_nonneg (hz i j)]
    _ ≤ ∑ j, z i j * (ε * v j) :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (h j) (hz i j)
    _ = ε * (z i ⬝ᵥ v) := by
        show ∑ j, z i j * (ε * v j) = ε * ∑ j, z i j * v j
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring

/-! ## The weighted Gram matrix and its quadratic form -/

/-- The weighted Gram matrix `∑ᵢ wᵢ zᵢzᵢᵀ` of the row family `z` with
weights `w`; this is the `M` of the paper, so that
`xᵀMx = ∑ᵢ wᵢ(zᵢᵀx)²`. -/
noncomputable def gramMatrix {m s : ℕ} (z : Fin m → Fin s → ℝ)
    (w : Fin m → ℝ) : Input s s :=
  fun j k => ∑ i, w i * z i j * z i k

theorem gramMatrix_isSymm {m s : ℕ} (z : Fin m → Fin s → ℝ)
    (w : Fin m → ℝ) : (gramMatrix z w).IsSymm := by
  apply Matrix.ext
  intro j k
  simp only [Matrix.transpose_apply, gramMatrix]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem gramMatrix_nonneg {m s : ℕ} {z : Fin m → Fin s → ℝ}
    {w : Fin m → ℝ} (hz : ∀ i j, 0 ≤ z i j) (hw : ∀ i, 0 ≤ w i)
    (j k : Fin s) :
    0 ≤ gramMatrix z w j k :=
  Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (hw i) (hz i j)) (hz i k)

/-- The action of the weighted Gram matrix:
`(gramMatrix z w · x)ⱼ = ∑ᵢ wᵢ zᵢⱼ (zᵢᵀx)`. -/
theorem gramMatrix_mulVec_apply {m s : ℕ} {z : Fin m → Fin s → ℝ}
    {w : Fin m → ℝ} (x : Fin s → ℝ) (j : Fin s) :
    (gramMatrix z w *ᵥ x) j = ∑ i, w i * z i j * ∑ k, z i k * x k := by
  show ∑ k, (∑ i, w i * z i j * z i k) * x k =
    ∑ i, w i * z i j * ∑ k, z i k * x k
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The quadratic form of the weighted Gram matrix is the weighted sum of
squared loads: `xᵀ(gramMatrix z w)x = ∑ᵢ wᵢ(zᵢᵀx)²`. -/
theorem dotProduct_mulVec_gramMatrix {m s : ℕ} {z : Fin m → Fin s → ℝ}
    {w : Fin m → ℝ} (x : Fin s → ℝ) :
    x ⬝ᵥ (gramMatrix z w *ᵥ x) = ∑ i, w i * (z i ⬝ᵥ x) ^ 2 := by
  simp only [dotProduct]
  simp_rw [gramMatrix_mulVec_apply]
  simp_rw [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_two, Finset.sum_mul_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j' _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-! ## Quadratic-form slack comparison -/

/-- **Weight-perturbation of a weighted Gram quadratic form.**  A
relative weight change `|w'ᵢ − wᵢ| ≤ ε·wᵢ` perturbs the Gram quadratic
form relatively: `|Q'[h] − Q[h]| ≤ ε·Q[h]`. -/
theorem weighted_gram_qf_perturbation {m s : ℕ} {z : Fin m → Fin s → ℝ}
    {w w' : Fin m → ℝ} (h : Fin s → ℝ) {ε : ℝ}
    (hpert : ∀ i, |w' i - w i| ≤ ε * w i) :
    |∑ i, w' i * (z i ⬝ᵥ h) ^ 2 - ∑ i, w i * (z i ⬝ᵥ h) ^ 2| ≤
      ε * ∑ i, w i * (z i ⬝ᵥ h) ^ 2 := by
  rw [← Finset.sum_sub_distrib]
  calc |∑ i, (w' i * (z i ⬝ᵥ h) ^ 2 - w i * (z i ⬝ᵥ h) ^ 2)|
      ≤ ∑ i, |w' i * (z i ⬝ᵥ h) ^ 2 - w i * (z i ⬝ᵥ h) ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ε * (w i * (z i ⬝ᵥ h) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg (z i ⬝ᵥ h))]
        have hle := mul_le_mul_of_nonneg_right (hpert i)
          (sq_nonneg (z i ⬝ᵥ h))
        linarith
    _ = ε * ∑ i, w i * (z i ⬝ᵥ h) ^ 2 := by rw [Finset.mul_sum]

/-- The slack quadratic forms of `M₀` and `Mx` differ by the difference
of their quadratic forms: `Aₓ[h] − A₀[h] = hᵀM₀h − hᵀMₓh`. -/
theorem slackQuadratic_sub_eq {s : ℕ} (b : ℝ) (M₀ Mx : Input s s)
    (h : Fin s → ℝ) :
    slackQuadratic b Mx h - slackQuadratic b M₀ h =
      h ⬝ᵥ (M₀ *ᵥ h) - h ⬝ᵥ (Mx *ᵥ h) := by
  have hdot : ∀ M : Input s s,
      h ⬝ᵥ (M *ᵥ h) = ∑ j, h j * ∑ k, M j k * h k := by
    intro M
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mulVec_apply_eq_sum]
  unfold slackQuadratic
  rw [hdot M₀, hdot Mx, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Slack stability (the quadratic-form (B.5) conclusion).**  For the
weighted Gram matrices `M₀ = gramMatrix z w` and `Mx = gramMatrix z w'`
with a relative weight perturbation `|w'ᵢ − wᵢ| ≤ ε·wᵢ`, if the anchor
Gram form is dominated by `κ·A₀[h]` — as supplied by
`weighted_gram_slack_domination` in `Resolvent.lean` — then the moved
slack satisfies `Aₓ[h] ≥ (1 − εκ)·A₀[h]`. -/
theorem slackQuadratic_stability {m s : ℕ} {b ε κ : ℝ}
    {z : Fin m → Fin s → ℝ} {w w' : Fin m → ℝ} (h : Fin s → ℝ)
    (hε : 0 ≤ ε)
    (hpert : ∀ i, |w' i - w i| ≤ ε * w i)
    (hdom : ∑ i, w i * (z i ⬝ᵥ h) ^ 2 ≤
      κ * slackQuadratic b (gramMatrix z w) h) :
    (1 - ε * κ) * slackQuadratic b (gramMatrix z w) h ≤
      slackQuadratic b (gramMatrix z w') h := by
  have hdiff := slackQuadratic_sub_eq b (gramMatrix z w) (gramMatrix z w') h
  rw [dotProduct_mulVec_gramMatrix, dotProduct_mulVec_gramMatrix] at hdiff
  have hpert' := weighted_gram_qf_perturbation (z := z) h hpert
  have hQ : -(ε * ∑ i, w i * (z i ⬝ᵥ h) ^ 2) ≤
      ∑ i, w i * (z i ⬝ᵥ h) ^ 2 - ∑ i, w' i * (z i ⬝ᵥ h) ^ 2 := by
    linarith [(abs_le.mp hpert').2]
  have hle : ε * ∑ i, w i * (z i ⬝ᵥ h) ^ 2 ≤
      ε * κ * slackQuadratic b (gramMatrix z w) h := by
    have := mul_le_mul_of_nonneg_left hdom hε
    linarith
  linarith

/-! ## The resolvent Loewner comparison `Rₓ ⪯ (1 + Caκ)·R₀`

Appendix B's resolvent perturbation step: inside the trust window the moved
slack `Aₓ` dominates `(1 − δ)·A₀` at quadratic-form level (the conclusion of
`slackQuadratic_stability`), and inverting the pair — by the same
`max_y (2⟨x,y⟩ − yᵀSy)` completing-the-square argument as `qfLower_inv_le`,
applied pairwise — gives `xᵀRₓx ≤ (1−δ)⁻¹·xᵀR₀x` for every `x`, i.e.
`Rₓ ⪯ (1 + Caκ)·R₀` with `Caκ = (1−δ)⁻¹ − 1`.  Everything stays at the
quadratic-form level; no operator square roots are needed. -/

/-- **Pairwise inverse propagation.**  If `S` is positive definite and its
quadratic form is bounded below by `c` times that of a positive definite `T`,
then `Q_{S⁻¹}[x] ≤ c⁻¹·Q_{T⁻¹}[x]` for every `x`.  This is the pairwise
version of `qfLower_inv_le`: `xᵀS⁻¹x = 2⟨x,y*⟩ − y*ᵀSy*` at `y* = S⁻¹x`, and
`2⟨x,z⟩ − c·zᵀTz ≤ c⁻¹·xᵀT⁻¹x` for every `z` by nonnegativity of
`c·(z − c⁻¹T⁻¹x)ᵀT(z − c⁻¹T⁻¹x)`. -/
theorem qf_rel_lower_inv_le {d : ℕ} {c : ℝ}
    {S T : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosDef) (hT : T.PosDef) (hc : 0 < c)
    (hrel : ∀ y : Fin d → ℝ, c * (y ⬝ᵥ (T *ᵥ y)) ≤ y ⬝ᵥ (S *ᵥ y))
    (x : Fin d → ℝ) :
    x ⬝ᵥ (S⁻¹ *ᵥ x) ≤ c⁻¹ * (x ⬝ᵥ (T⁻¹ *ᵥ x)) := by
  have hdetS : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  have hdetT : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hT.isUnit
  have hTpsd : T.PosSemidef := hT.posSemidef
  have hTsym : T.IsSymm := hT.isHermitian.isSymm
  -- Completing the square: `2⟨x,z⟩ − c·zᵀTz ≤ c⁻¹·xᵀT⁻¹x` for every `z`.
  have key : ∀ z : Fin d → ℝ,
      2 * (x ⬝ᵥ z) - c * (z ⬝ᵥ (T *ᵥ z)) ≤
        c⁻¹ * (x ⬝ᵥ (T⁻¹ *ᵥ x)) := by
    intro z
    set w := c⁻¹ • (T⁻¹ *ᵥ x) with hw
    have hTw : T *ᵥ w = c⁻¹ • x := by
      rw [hw, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv T hdetT, Matrix.one_mulVec]
    have hnn0 : 0 ≤ star (z - w) ⬝ᵥ (T *ᵥ (z - w)) :=
      hTpsd.dotProduct_mulVec_nonneg (z - w)
    rw [star_trivial] at hnn0
    have hnn : 0 ≤ c * ((z - w) ⬝ᵥ (T *ᵥ (z - w))) :=
      mul_nonneg hc.le hnn0
    have hexp : (z - w) ⬝ᵥ (T *ᵥ (z - w)) =
        z ⬝ᵥ (T *ᵥ z) - 2 * (z ⬝ᵥ (T *ᵥ w)) + w ⬝ᵥ (T *ᵥ w) := by
      rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
        hTsym.dotProduct_mulVec_comm (x := w) (y := z)]
      ring
    have hw' : w ⬝ᵥ (T *ᵥ w) = c⁻¹ * (c⁻¹ * (x ⬝ᵥ (T⁻¹ *ᵥ x))) := by
      rw [hTw, dotProduct_smul, hw, smul_dotProduct,
        dotProduct_comm ((T⁻¹ *ᵥ x)) x]
      ring
    have hz' : z ⬝ᵥ (T *ᵥ w) = c⁻¹ * (x ⬝ᵥ z) := by
      rw [hTw, dotProduct_smul, dotProduct_comm z x, smul_eq_mul]
    have hcz : c * (z ⬝ᵥ (T *ᵥ w)) = x ⬝ᵥ z := by
      rw [hz', mul_inv_cancel_left₀ hc.ne']
    have hcw : c * (w ⬝ᵥ (T *ᵥ w)) = c⁻¹ * (x ⬝ᵥ (T⁻¹ *ᵥ x)) := by
      rw [hw', ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    nlinarith [hnn, hexp, hcz, hcw]
  set y := S⁻¹ *ᵥ x with hy
  have hSy : S *ᵥ y = x := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S hdetS,
      Matrix.one_mulVec]
  have heq : x ⬝ᵥ (S⁻¹ *ᵥ x) = 2 * (x ⬝ᵥ y) - y ⬝ᵥ (S *ᵥ y) := by
    rw [hSy, dotProduct_comm y x]
    ring
  rw [heq]
  calc 2 * (x ⬝ᵥ y) - y ⬝ᵥ (S *ᵥ y)
      ≤ 2 * (x ⬝ᵥ y) - c * (y ⬝ᵥ (T *ᵥ y)) := by linarith [hrel y]
    _ ≤ c⁻¹ * (x ⬝ᵥ (T⁻¹ *ᵥ x)) := key y

/-- **Resolvent Loewner comparison, relative form.**  If the moved slack
stays above `(1 − δ)` times the anchor at quadratic-form level — the
conclusion of `slackQuadratic_stability` — then `Rₓ[h] ≤ (1−δ)⁻¹·R₀[h]` for
every `h`. -/
theorem resolvent_loewner_le_of_slack_rel {s : ℕ} {b δ : ℝ}
    {M₀ Mx : Input s s}
    (hpos₀ : (slackMatrix b M₀).PosDef) (hposx : (slackMatrix b Mx).PosDef)
    (hδ : 0 < 1 - δ)
    (hrel : ∀ h : Fin s → ℝ,
      (1 - δ) * slackQuadratic b M₀ h ≤ slackQuadratic b Mx h)
    (h : Fin s → ℝ) :
    h ⬝ᵥ ((slackMatrix b Mx)⁻¹ *ᵥ h) ≤
      (1 - δ)⁻¹ * (h ⬝ᵥ ((slackMatrix b M₀)⁻¹ *ᵥ h)) := by
  apply qf_rel_lower_inv_le hposx hpos₀ hδ _ h
  intro y
  have h1 := hrel y
  rwa [slackQuadratic_eq_dotProduct, slackQuadratic_eq_dotProduct] at h1

/-- **The (B.10) resolvent comparison from a Gram weight perturbation.**  If
`Mx = gramMatrix z w'` differs from the anchor `M₀ = gramMatrix z w` by a
relative weight change `|w'ᵢ − wᵢ| ≤ ε·wᵢ`, and the anchor Gram quadratic
form is dominated by `κ·A₀` (as supplied by
`weighted_gram_slack_domination`), then `Rₓ[h] ≤ (1 − εκ)⁻¹·R₀[h]`. -/
theorem resolvent_loewner_le_of_gram_perturbation {m s : ℕ} {b ε κ : ℝ}
    {z : Fin m → Fin s → ℝ} {w w' : Fin m → ℝ}
    (hpos₀ : (slackMatrix b (gramMatrix z w)).PosDef)
    (hposx : (slackMatrix b (gramMatrix z w')).PosDef)
    (hε : 0 ≤ ε) (hεκ : 0 < 1 - ε * κ)
    (hpert : ∀ i, |w' i - w i| ≤ ε * w i)
    (hdom : ∀ h : Fin s → ℝ, ∑ i, w i * (z i ⬝ᵥ h) ^ 2 ≤
      κ * slackQuadratic b (gramMatrix z w) h)
    (h : Fin s → ℝ) :
    h ⬝ᵥ ((slackMatrix b (gramMatrix z w'))⁻¹ *ᵥ h) ≤
      (1 - ε * κ)⁻¹ * (h ⬝ᵥ ((slackMatrix b (gramMatrix z w))⁻¹ *ᵥ h)) :=
  resolvent_loewner_le_of_slack_rel hpos₀ hposx hεκ
    (fun y => slackQuadratic_stability y hε hpert (hdom y)) h

/-- The reciprocal bound in `1 + c` form: `(1−δ)⁻¹ ≤ 1 + c` whenever
`1 ≤ (1−δ)(1+c)` (equivalently `δ ≤ c/(1+c)`). -/
theorem inv_one_sub_le_one_add {δ c : ℝ} (_hc : 0 < c) (hδ : 0 < 1 - δ)
    (h : 1 ≤ (1 - δ) * (1 + c)) : (1 - δ)⁻¹ ≤ 1 + c := by
  rw [← one_div, div_le_iff₀ hδ]
  nlinarith [h]

/-- **The resolvent comparison `Rₓ ⪯ (1 + Caκ)·R₀`.**  The (B.10) conclusion
in `1 + Caκ` form: the relative slack bound with `δ ≤ c/(1+c)` inverts to
`Rₓ[h] ≤ (1 + c)·R₀[h]`. -/
theorem resolvent_loewner_le_one_add {s : ℕ} {b δ c : ℝ}
    {M₀ Mx : Input s s}
    (hpos₀ : (slackMatrix b M₀).PosDef) (hposx : (slackMatrix b Mx).PosDef)
    (hc : 0 < c) (hδ : 0 < 1 - δ)
    (hδc : 1 ≤ (1 - δ) * (1 + c))
    (hrel : ∀ h : Fin s → ℝ,
      (1 - δ) * slackQuadratic b M₀ h ≤ slackQuadratic b Mx h)
    (h : Fin s → ℝ) :
    h ⬝ᵥ ((slackMatrix b Mx)⁻¹ *ᵥ h) ≤
      (1 + c) * (h ⬝ᵥ ((slackMatrix b M₀)⁻¹ *ᵥ h)) := by
  have hnn0 : 0 ≤ star h ⬝ᵥ ((slackMatrix b M₀)⁻¹ *ᵥ h) :=
    hpos₀.inv.posSemidef.dotProduct_mulVec_nonneg h
  rw [star_trivial] at hnn0
  calc h ⬝ᵥ ((slackMatrix b Mx)⁻¹ *ᵥ h)
      ≤ (1 - δ)⁻¹ * (h ⬝ᵥ ((slackMatrix b M₀)⁻¹ *ᵥ h)) :=
        resolvent_loewner_le_of_slack_rel hpos₀ hposx hδ hrel h
    _ ≤ (1 + c) * (h ⬝ᵥ ((slackMatrix b M₀)⁻¹ *ᵥ h)) :=
        mul_le_mul_of_nonneg_right (inv_one_sub_le_one_add hc hδ hδc) hnn0

end Komlos
