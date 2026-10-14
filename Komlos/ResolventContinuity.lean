import Komlos.Curvature
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
# Continuity of the resolvent inverse and persistence of positive definiteness

`Komlos.Curvature.differentiableAt_inv_entry` proves entrywise
differentiability — hence continuity — of `t ↦ (P t)⁻¹` whenever `P` is
entrywise differentiable and `P t₀` is invertible.  This module assembles that
entrywise statement into `ContinuousAt` for the matrix path
`t ↦ (slackMatrix b (P t))⁻¹`, which is the analytic input needed by the
conditional `HasDerivAt` theorems of `Komlos.SpectralDimension`.

It also proves the *open-cone* lemma for positive-definite matrices:
positive definiteness persists along entrywise-continuous symmetric paths
(`posDef_eventually`).  Together these discharge — for affine and quadratic
slack paths — the continuity (`hcont`) and neighborhood
positive-definiteness (`hnbhd`) hypotheses carried by the conditional
derivative theorems, leaving only `PosDef (slackMatrix b M)` and symmetry of
`M`, `N`.

## Main results

* `continuousAt_slack_inv`: `(P t)⁻¹` is continuous at `0` for entrywise
  differentiable `P` with invertible `P 0`.
* `continuousAt_slack_inv_add_smul` / `continuousAt_slack_inv_quadratic`:
  the affine and quadratic slack paths used by Appendix B.
* `posDef_eventually`: positive definiteness is an open condition along
  entrywise-continuous paths that remain symmetric.
* `posDef_slackMatrix_eventually_add_smul` /
  `posDef_slackMatrix_eventually_quadratic`: the instantiated neighborhood
  hypotheses, needing only `PosDef (slackMatrix b M)` plus symmetry of
  `M`, `N`.
-/

namespace Komlos

open Filter Matrix Topology
open scoped BigOperators

noncomputable section

/-! ## Entrywise differentiability and continuity of slack paths -/

/-- Entries of the slack matrix of an entrywise-differentiable path are
differentiable (`t ↦ dᵢⱼ − P t i j`). -/
theorem differentiableAt_slackMatrix_entry {s : ℕ} {b : ℝ}
    {P : ℝ → Input s s} {t₀ : ℝ}
    (hP : ∀ i j, DifferentiableAt ℝ (fun t => P t i j) t₀) (i j : Fin s) :
    DifferentiableAt ℝ (fun t => slackMatrix b (P t) i j) t₀ := by
  have hfun : (fun t => slackMatrix b (P t) i j) =
      fun t => Matrix.diagonal (fun _ : Fin s => b) i j - P t i j := by
    funext t
    simp only [slackMatrix, Matrix.sub_apply]
  rw [hfun]
  exact (differentiableAt_const _).sub (hP i j)

/-- `t ↦ (slackMatrix b (P t))⁻¹` is continuous at `0` whenever the slack path
is entrywise differentiable and the initial slack matrix is invertible. -/
theorem continuousAt_slack_inv {s : ℕ} {b : ℝ} {P : ℝ → Input s s}
    (hP : ∀ i j, DifferentiableAt ℝ (fun t => slackMatrix b (P t) i j) 0)
    (hP0 : IsUnit (slackMatrix b (P 0))) :
    ContinuousAt (fun t => (slackMatrix b (P t))⁻¹) 0 := by
  refine continuousAt_pi' fun i => continuousAt_pi' fun j => ?_
  exact (differentiableAt_inv_entry _ _ hP hP0 i j).continuousAt

/-- A positive-definite slack matrix is invertible. -/
theorem isUnit_slackMatrix_of_posDef {s : ℕ} {b : ℝ} {M : Input s s}
    (hMpos : (slackMatrix b M).PosDef) : IsUnit (slackMatrix b M) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr hMpos.det_pos.ne')

/-- Entrywise differentiability of the affine slack path `M + t • N`. -/
theorem differentiableAt_slack_add_smul_entry {s : ℕ} {b : ℝ} {M N : Input s s}
    (i j : Fin s) :
    DifferentiableAt ℝ (fun t : ℝ => slackMatrix b (M + t • N) i j) 0 := by
  have heq : (fun t : ℝ => slackMatrix b (M + t • N) i j) =
      fun t => slackMatrix b M i j - t * N i j := by
    funext t
    simp only [slackMatrix, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  exact (differentiableAt_const _).sub (differentiableAt_id.mul_const _)

/-- Entrywise differentiability of the quadratic slack path
`M + t • N₁ + t² • N₂`. -/
theorem differentiableAt_slack_quadratic_entry {s : ℕ} {b : ℝ}
    {M N₁ N₂ : Input s s} (i j : Fin s) :
    DifferentiableAt ℝ
      (fun t : ℝ => slackMatrix b (M + t • N₁ + t ^ 2 • N₂) i j) 0 := by
  have heq : (fun t : ℝ => slackMatrix b (M + t • N₁ + t ^ 2 • N₂) i j) =
      fun t => slackMatrix b M i j - (t * N₁ i j + t ^ 2 * N₂ i j) := by
    funext t
    simp only [slackMatrix, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  exact (differentiableAt_const _).sub
    ((differentiableAt_id.mul_const _).add
      ((differentiableAt_id.pow 2).mul_const _))

/-- Inverse-path continuity along the affine update `M + t • N`, needing only
positive definiteness of the slack at `t = 0`. -/
theorem continuousAt_slack_inv_add_smul {s : ℕ} {b : ℝ} {M N : Input s s}
    (hMpos : (slackMatrix b M).PosDef) :
    ContinuousAt (fun t : ℝ => (slackMatrix b (M + t • N))⁻¹) 0 :=
  continuousAt_slack_inv (fun i j => differentiableAt_slack_add_smul_entry i j)
    (by simpa using isUnit_slackMatrix_of_posDef hMpos)

/-- Inverse-path continuity along the quadratic update
`M + t • N₁ + t² • N₂`. -/
theorem continuousAt_slack_inv_quadratic {s : ℕ} {b : ℝ} {M N₁ N₂ : Input s s}
    (hMpos : (slackMatrix b M).PosDef) :
    ContinuousAt (fun t : ℝ => (slackMatrix b (M + t • N₁ + t ^ 2 • N₂))⁻¹) 0 :=
  continuousAt_slack_inv (fun i j => differentiableAt_slack_quadratic_entry i j)
    (by simpa using isUnit_slackMatrix_of_posDef hMpos)

/-! ## Quadratic-form continuity and the open-cone lemma -/

/-- The quadratic form `x ↦ xᵀ A x` is continuous on `Fin s → ℝ`. -/
theorem continuous_dotProduct_mulVec_self {s : ℕ} (A : Input s s) :
    Continuous fun x : Fin s → ℝ => x ⬝ᵥ A *ᵥ x := by
  have hfun : (fun x : Fin s → ℝ => x ⬝ᵥ A *ᵥ x) =
      fun x => ∑ i : Fin s, x i * ∑ j : Fin s, A i j * x j := by
    funext x
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [hfun]
  apply continuous_finsetSum
  intro i _
  apply Continuous.mul (continuous_apply i)
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul (continuous_apply j)

/-- For `x` nonzero, `xᵀAx ≥ c‖x‖²` follows once `yᵀAy ≥ c` holds on the unit
sphere. -/
theorem le_dotProduct_mulVec_self_of_sphere {s : ℕ} {A : Input s s} {c : ℝ}
    (hsphere : ∀ y : Fin s → ℝ, ‖y‖ = 1 → c ≤ y ⬝ᵥ A *ᵥ y)
    (x : Fin s → ℝ) :
    c * ‖x‖ ^ 2 ≤ x ⬝ᵥ A *ᵥ x := by
  by_cases hx : x = 0
  · simp [hx]
  · have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hy : ‖(‖x‖⁻¹ • x : Fin s → ℝ)‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnx),
        inv_mul_cancel₀ hnx.ne']
    have h := hsphere _ hy
    have hscale : (‖x‖⁻¹ • x : Fin s → ℝ) ⬝ᵥ A *ᵥ (‖x‖⁻¹ • x) =
        ‖x‖⁻¹ * (‖x‖⁻¹ * (x ⬝ᵥ A *ᵥ x)) := by
      rw [smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul]
      ring
    rw [hscale] at h
    have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg ‖x‖)
    have heq : ‖x‖ ^ 2 * (‖x‖⁻¹ * (‖x‖⁻¹ * (x ⬝ᵥ A *ᵥ x))) = x ⬝ᵥ A *ᵥ x := by
      field_simp
    rw [heq] at hmul
    linarith [hmul]

/-- The quadratic-form defect under a perturbation `D`:
`|xᵀDx| ≤ (∑ᵢⱼ |Dᵢⱼ|) · ‖x‖²` with the Pi (sup) norm. -/
theorem abs_dotProduct_mulVec_le {s : ℕ} (D : Input s s) (x : Fin s → ℝ) :
    |x ⬝ᵥ D *ᵥ x| ≤ (∑ i : Fin s, ∑ j : Fin s, |D i j|) * ‖x‖ ^ 2 := by
  have hfun : x ⬝ᵥ D *ᵥ x =
      ∑ i : Fin s, ∑ j : Fin s, x i * D i j * x j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfun]
  calc |∑ i : Fin s, ∑ j : Fin s, x i * D i j * x j|
      ≤ ∑ i : Fin s, ∑ j : Fin s, |x i * D i j * x j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i : Fin s, ∑ j : Fin s, |D i j| * |x i| * |x j| := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_mul]
        ring
    _ ≤ ∑ i : Fin s, ∑ j : Fin s, |D i j| * ‖x‖ * ‖x‖ := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        have hi : |x i| ≤ ‖x‖ := norm_le_pi_norm x i
        have hj : |x j| ≤ ‖x‖ := norm_le_pi_norm x j
        have h1 : |D i j| * |x i| ≤ |D i j| * ‖x‖ :=
          mul_le_mul_of_nonneg_left hi (abs_nonneg _)
        have h2 : |D i j| * |x i| * |x j| ≤ |D i j| * ‖x‖ * ‖x‖ := by
          apply mul_le_mul h1 hj (abs_nonneg _)
          exact mul_nonneg (abs_nonneg _) (norm_nonneg _)
        exact h2
    _ = (∑ i : Fin s, ∑ j : Fin s, |D i j|) * ‖x‖ ^ 2 := by
        have hinner : ∀ i : Fin s, ∑ j : Fin s, |D i j| * ‖x‖ * ‖x‖ =
            (∑ j : Fin s, |D i j|) * (‖x‖ * ‖x‖) := fun i => by
          rw [← Finset.sum_mul, ← Finset.sum_mul, mul_assoc]
        rw [Finset.sum_congr rfl fun i _ => hinner i, ← Finset.sum_mul, ← pow_two]

/-- **The positive-definite cone is open along continuous paths.**  If `P 0`
is positive definite, the path `P` is entrywise continuous at `0`, and `P t`
stays symmetric near `0`, then `P t` is positive definite near `0`. -/
theorem posDef_eventually {s : ℕ} {P : ℝ → Input s s}
    (hP0 : (P 0).PosDef)
    (hcont : ∀ i j, ContinuousAt (fun t => P t i j) 0)
    (hsymm : ∀ᶠ t : ℝ in 𝓝 0, (P t).IsSymm) :
    ∀ᶠ t : ℝ in 𝓝 0, (P t).PosDef := by
  classical
  rcases isEmpty_or_nonempty (Fin s) with hE | hE
  · filter_upwards [hsymm] with t ht
    rw [posDef_iff_dotProduct_mulVec]
    refine ⟨isHermitian_iff_isSymm.mpr ht, fun x hx => ?_⟩
    exact absurd (Subsingleton.elim x 0) hx
  obtain ⟨i0⟩ := hE
  -- `c` = minimum of `xᵀ (P 0) x` over the unit sphere; `c > 0`.
  have hcontQF : Continuous fun x : Fin s → ℝ => x ⬝ᵥ P 0 *ᵥ x :=
    continuous_dotProduct_mulVec_self (P 0)
  set v : Fin s → ℝ := Pi.single i0 1 with hvdef
  have hv : v ≠ 0 := by
    intro h
    have := congrFun h i0
    simp [hvdef] at this
  have hnv : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  have hsphere_mem : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : Fin s → ℝ) 1 := by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hnv), inv_mul_cancel₀ hnv.ne']
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_sphere (0 : Fin s → ℝ) 1).exists_isMinOn
    ⟨_, hsphere_mem⟩ hcontQF.continuousOn
  have hx₀norm : ‖x₀‖ = 1 := by
    have := hx₀
    rw [Metric.mem_sphere, dist_zero_right] at this
    exact this
  have hx₀ne : x₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx₀norm
    exact zero_ne_one hx₀norm
  have hcpos : (0 : ℝ) < star x₀ ⬝ᵥ P 0 *ᵥ x₀ :=
    (posDef_iff_dotProduct_mulVec.mp hP0).2 hx₀ne
  have hstar : ∀ x : Fin s → ℝ, star x = x := fun x => by
    funext i
    rw [Pi.star_apply]
    exact star_trivial _
  -- The sphere bound transfers to `c‖x‖² ≤ xᵀAx` for all `x`.
  set c := x₀ ⬝ᵥ P 0 *ᵥ x₀ with hc
  have hc' : (0 : ℝ) < c := by rw [hc]; rwa [hstar] at hcpos
  have hmin' : ∀ y : Fin s → ℝ, ‖y‖ = 1 → c ≤ y ⬝ᵥ P 0 *ᵥ y := by
    intro y hy
    exact hmin (show y ∈ Metric.sphere (0 : Fin s → ℝ) 1 by
      rwa [Metric.mem_sphere, dist_zero_right])
  have hbig : ∀ x : Fin s → ℝ, c * ‖x‖ ^ 2 ≤ x ⬝ᵥ P 0 *ᵥ x :=
    le_dotProduct_mulVec_self_of_sphere hmin'
  -- Entrywise closeness: `∑ᵢⱼ |P t i j - P 0 i j| < c` near `0`.
  have hlim : Tendsto (fun t : ℝ => ∑ i : Fin s, ∑ j : Fin s, |P t i j - P 0 i j|)
      (𝓝 0) (𝓝 (∑ i : Fin s, ∑ j : Fin s, |P 0 i j - P 0 i j|)) := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact ((hcont i j).sub
      (continuousAt_const : ContinuousAt (fun _ : ℝ => P 0 i j) 0)).abs
  simp only [sub_self, abs_zero, Finset.sum_const_zero] at hlim
  have hev : ∀ᶠ t : ℝ in 𝓝 0,
      ∑ i : Fin s, ∑ j : Fin s, |P t i j - P 0 i j| < c :=
    hlim.eventually (Iio_mem_nhds hc')
  -- Assemble: `xᵀ (P t) x ≥ (c − ∑ᵢⱼ|·|) ‖x‖² > 0`.
  filter_upwards [hsymm, hev] with t ht htclose
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨isHermitian_iff_isSymm.mpr ht, fun x hx => ?_⟩
  rw [hstar x]
  have hdecomp : x ⬝ᵥ P t *ᵥ x =
      x ⬝ᵥ P 0 *ᵥ x + x ⬝ᵥ (P t - P 0) *ᵥ x := by
    rw [← dotProduct_add, ← Matrix.add_mulVec]
    congr 1
    rw [add_sub_cancel]
  rw [hdecomp]
  have hlt : |x ⬝ᵥ (P t - P 0) *ᵥ x| < c * ‖x‖ ^ 2 := by
    have hnx : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
    calc |x ⬝ᵥ (P t - P 0) *ᵥ x|
        ≤ (∑ i : Fin s, ∑ j : Fin s, |P t i j - P 0 i j|) * ‖x‖ ^ 2 := by
          have habs := abs_dotProduct_mulVec_le (P t - P 0) x
          rwa [show (∑ i : Fin s, ∑ j : Fin s, |(P t - P 0) i j|) =
              ∑ i : Fin s, ∑ j : Fin s, |P t i j - P 0 i j| from
            Finset.sum_congr rfl fun i _ =>
              Finset.sum_congr rfl fun j _ => by rw [Matrix.sub_apply]] at habs
      _ < c * ‖x‖ ^ 2 := mul_lt_mul_of_pos_right htclose (pow_pos hnx 2)
  have hnx : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hbound := hbig x
  have hneg : -|x ⬝ᵥ (P t - P 0) *ᵥ x| ≤ x ⬝ᵥ (P t - P 0) *ᵥ x := neg_abs_le _
  nlinarith [hlt, hbound, hneg, hnx]

/-- Symmetry persists along the affine slack path when `M`, `N` are
symmetric (in fact for all `t`). -/
theorem isSymm_slackMatrix_add_smul {s : ℕ} {b : ℝ} {M N : Input s s}
    (hM : M.IsSymm) (hN : N.IsSymm) (t : ℝ) :
    (slackMatrix b (M + t • N)).IsSymm :=
  (isSymm_diagonal _).sub (hM.add (hN.smul t))

/-- Symmetry persists along the quadratic slack path. -/
theorem isSymm_slackMatrix_quadratic {s : ℕ} {b : ℝ} {M N₁ N₂ : Input s s}
    (hM : M.IsSymm) (hN₁ : N₁.IsSymm) (hN₂ : N₂.IsSymm) (t : ℝ) :
    (slackMatrix b (M + t • N₁ + t ^ 2 • N₂)).IsSymm :=
  (isSymm_diagonal _).sub ((hM.add (hN₁.smul t)).add (hN₂.smul (t ^ 2)))

/-- **The `hnbhd` hypothesis, discharged.**  Along the affine slack path of a
positive-definite slack with symmetric `M`, `N`, the slack stays positive
definite near `0`. -/
theorem posDef_slackMatrix_eventually_add_smul {s : ℕ} {b : ℝ} {M N : Input s s}
    (hMpos : (slackMatrix b M).PosDef)
    (hM : M.IsSymm) (hN : N.IsSymm) :
    ∀ᶠ t : ℝ in 𝓝 0, (slackMatrix b (M + t • N)).PosDef :=
  posDef_eventually (P := fun t : ℝ => slackMatrix b (M + t • N))
    (by simpa using hMpos)
    (fun i j => (differentiableAt_slack_add_smul_entry i j).continuousAt)
    (Eventually.of_forall (isSymm_slackMatrix_add_smul hM hN))

/-- The quadratic-path analogue of `posDef_slackMatrix_eventually_add_smul`. -/
theorem posDef_slackMatrix_eventually_quadratic {s : ℕ} {b : ℝ}
    {M N₁ N₂ : Input s s}
    (hMpos : (slackMatrix b M).PosDef)
    (hM : M.IsSymm) (hN₁ : N₁.IsSymm) (hN₂ : N₂.IsSymm) :
    ∀ᶠ t : ℝ in 𝓝 0, (slackMatrix b (M + t • N₁ + t ^ 2 • N₂)).PosDef :=
  posDef_eventually (P := fun t : ℝ => slackMatrix b (M + t • N₁ + t ^ 2 • N₂))
    (by simpa using hMpos)
    (fun i j => (differentiableAt_slack_quadratic_entry i j).continuousAt)
    (Eventually.of_forall (isSymm_slackMatrix_quadratic hM hN₁ hN₂))

end

end Komlos
