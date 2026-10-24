/-
# Appendix D.5: the explicit density of a Gaussian pushed through a linear map

This file formalizes the density computation underlying the Appendix-D.5
conditioning step of *The Komlós Problem in Near Matrix-Multiplication Time*.

For `L : E →L[ℝ] F` between finite-dimensional real inner product spaces, the
restriction `A : ↥(ker L)ᗮ ≃ₗ[ℝ] ↥(range L)` (`gaussEquiv L`) is a linear
equivalence between spaces of the same dimension `r = finrank (range L)`.
Pushing the standard Gaussian on `(ker L)ᗮ` through `A` is therefore an
*equal-dimensional* linear change of variables — no genuine coarea argument is
needed — and we prove unconditionally that `L Z`, viewed on `range L`, has
intrinsic-volume density

    p(y) = (2π)^{-r/2} (normDet A)⁻¹ exp(-⟪y, G⁻¹ y⟫ / 2),

where `G = A ∘ A*` is the Gram operator on `range L` and `normDet A` is the
linear-map Jacobian (`normDet A = |det A|`, with `normDet A ^ 2 = det (A* ∘ A)`,
equivalently `normDet A = (det G)^{1/2}`).

Main contents:

* `lintegral_fin_prod`, `pi_withDensity`, `MeasurableEquiv.map_withDensity`,
  `smul_withDensity`: general measure-theoretic infrastructure.
* `stdGaussianDensity` / `stdGaussian_eq_withDensity`: the standard Gaussian on
  a `d`-dimensional inner product space has density `(2π)^{-d/2} e^{-‖x‖²/2}`
  with respect to `volume`.
* `map_volume_linearEquiv`: the linear Jacobian rule
  `map A volume = ENNReal.ofReal (normDet A)⁻¹ • volume`.
* `gramOp`, `gramKer`, `gramInv`: the Gram operators `A ∘ A*` (on `range L`)
  and `A* ∘ A` (on `(ker L)ᗮ`) and the inverse Gram, with
  `det G = normDet A ^ 2` and `⟪y, G⁻¹ y⟫ = ‖A.symm y‖²`.
* `gaussDensity` / `DensityFormula` / `densityFormula`: the Appendix-D.5
  density formula, stated as a `Prop` and proved.
* Consequences needed downstream: `gaussPushforward` normalization
  (`gaussPushforward_univ`, `gaussLaw_univ`), support on `range L`
  (`gaussLaw_compl_range`), the explicit integral formula `gaussLaw_apply`,
  positivity of the density (`gaussDensity_pos`, `gaussDensity_ne_zero`), and
  stabilizer invariance (`gaussPushforward_stabilizer`,
  `isDensityStabilizer_of_intertwining`).

No part of this file introduces axioms, `sorry`, or encapsulated hypotheses:
everything is derived from Mathlib's Gaussian/Haar/change-of-variables
machinery.
-/

import Komlos.GaussianDisintegration
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Probability.Distributions.Gaussian.Real

namespace Komlos

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace ENNReal

noncomputable section

/-! ### Measure-theoretic infrastructure -/

/-- Tonelli for a `Fin n`-indexed product measure: the Lebesgue integral of a
coordinatewise product is the product of the coordinate integrals. -/
theorem lintegral_fin_prod {n : ℕ} {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)]
    {μ : (i : Fin n) → Measure (α i)} [∀ i, SigmaFinite (μ i)]
    {f : (i : Fin n) → α i → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → α i, ∏ i, f i (x i) ∂Measure.pi μ =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        _ = ∫⁻ x : α 0 × ((i : Fin n) → α i.succ),
            f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i)
              ∂((μ 0).prod (Measure.pi fun i ↦ μ i.succ)) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _) _]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0)
            * ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ := by
          rw [← ih (f := fun i ↦ f i.succ) (hf := fun i ↦ hf i.succ),
            ← lintegral_prod_mul (hf 0).aemeasurable
              ((Finset.measurable_prod _ fun i _ ↦
                (hf i.succ).comp (measurable_pi_apply i)).aemeasurable)]
        _ = ∏ i, ∫⁻ x, f i x ∂μ i := (Fin.prod_univ_succ _).symm

/-- A `Fin n`-indexed product of `withDensity` Lebesgue measures on `ℝ` is
`withDensity` of the coordinatewise product density on `Fin n → ℝ`. -/
theorem pi_withDensity {n : ℕ} {f : Fin n → ℝ → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) (hft : ∀ i x, f i x ≠ ⊤) :
    Measure.pi (fun i ↦ (volume : Measure ℝ).withDensity (f i)) =
      volume.withDensity (fun x : Fin n → ℝ ↦ ∏ i, f i (x i)) := by
  haveI : ∀ i : Fin n, SigmaFinite ((volume : Measure ℝ).withDensity (f i)) :=
    fun i ↦ SigmaFinite.withDensity_of_ne_top' (hft i)
  refine Measure.pi_eq fun s hs ↦ ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  rw [show (volume : Measure (Fin n → ℝ)) = Measure.pi (fun _ : Fin n ↦ volume)
      from volume_pi]
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hfun : (Set.pi Set.univ s).indicator (fun x : Fin n → ℝ ↦ ∏ i, f i (x i)) =
      fun x ↦ ∏ i, (s i).indicator (f i) (x i) := by
    funext x
    by_cases hx : x ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hx]
      rw [Set.mem_univ_pi] at hx
      exact Finset.prod_congr rfl fun i _ ↦ (Set.indicator_of_mem (hx i) _).symm
    · rw [Set.indicator_of_notMem hx]
      rw [Set.mem_univ_pi] at hx
      push_neg at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i)
        (Set.indicator_of_notMem hi _)).symm
  rw [hfun, lintegral_fin_prod fun i ↦ (hf i).indicator (hs i)]
  exact Finset.prod_congr rfl fun i _ ↦ by
    rw [← lintegral_indicator (hs i), ← withDensity_apply _ (hs i)]

/-- Pushing a `withDensity` measure through a measurable equivalence gives the
`withDensity` of the transported density. -/
theorem MeasurableEquiv.map_withDensity {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (e : α ≃ᵐ β) (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (f ∘ ⇑e.symm) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, ← lintegral_indicator (e.measurable hs),
    ← lintegral_indicator hs,
    lintegral_map ((hf.comp e.symm.measurable).indicator hs) e.measurable]
  apply lintegral_congr
  intro x
  by_cases hx : e x ∈ s
  · rw [Set.indicator_of_mem hx (f ∘ ⇑e.symm),
      Set.indicator_of_mem (s := ⇑e ⁻¹' s) hx f]
    simp
  · rw [Set.indicator_of_notMem hx (f ∘ ⇑e.symm),
      Set.indicator_of_notMem (s := ⇑e ⁻¹' s) hx f]

/-- A scalar multiple of a `withDensity` measure merges the scalar into the
density. -/
theorem smul_withDensity {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (c : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : Measurable f) :
    (c • μ).withDensity f = μ.withDensity (fun x ↦ c * f x) := by
  apply Measure.ext
  intro s hs
  rw [withDensity_apply _ hs, withDensity_apply _ hs, ← lintegral_indicator hs,
    ← lintegral_indicator hs, lintegral_smul_measure, smul_eq_mul,
    ← lintegral_const_mul c (hf.indicator hs)]
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ s
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha]
  · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, mul_zero]

/-! ### The standard Gaussian density `(2π)^{-d/2} exp(-‖x‖²/2)` -/

/-- The density of the standard Gaussian on a `d`-dimensional real inner
product space, as a function of `x`:
`(2π)^{-d/2} * exp(-‖x‖²/2)`. -/
noncomputable def stdGaussianDensity (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (x : E) : ℝ :=
  (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2)

theorem stdGaussianDensity_nonneg (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (x : E) :
    0 ≤ stdGaussianDensity E x :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _)

theorem stdGaussianDensity_pos (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (x : E) :
    0 < stdGaussianDensity E x :=
  mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

theorem measurable_stdGaussianDensity (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] : Measurable (stdGaussianDensity E) :=
  measurable_const.mul
    ((Real.continuous_exp.comp ((continuous_norm.pow 2).neg.div_const 2)).measurable)

/-- The product of `n` univariate standard-Gaussian pdfs at the coordinates of
`x` is the `n`-dimensional standard Gaussian density. -/
theorem prod_gaussianPDF {n : ℕ} (x : Fin n → ℝ) :
    ∏ i, gaussianPDF 0 1 (x i) =
      ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2)
        * Real.exp (-(∑ i, (x i) ^ 2) / 2)) := by
  have hd : ∀ i : Fin n, gaussianPDF 0 1 (x i)
      = ENNReal.ofReal ((√(2 * Real.pi))⁻¹ * Real.exp (-(x i) ^ 2 / 2)) := by
    intro i
    simp [gaussianPDF, gaussianPDFReal]
  rw [Finset.prod_congr rfl fun i _ ↦ hd i,
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ by positivity)]
  congr 1
  have hsqrt : (√(2 * Real.pi))⁻¹ ^ n = (2 * Real.pi) ^ (-(n : ℝ) / 2) := by
    rw [inv_pow, ← Real.rpow_natCast (√(2 * Real.pi)) n, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (by positivity)]
    rw [← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    congr 1
    ring
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum, hsqrt]
  congr 1
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]

/-- A product measure of univariate standard Gaussians on `Fin n → ℝ` equals
the `volume` measure with the `n`-dimensional Gaussian density. -/
theorem pi_gaussianReal_eq_withDensity {n : ℕ} :
    Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1) =
      volume.withDensity (fun x : Fin n → ℝ ↦
        ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2)
          * Real.exp (-(∑ i, (x i) ^ 2) / 2))) := by
  rw [show (fun _ : Fin n ↦ gaussianReal 0 1)
      = fun i ↦ (volume : Measure ℝ).withDensity (gaussianPDF 0 1) from
    funext fun _ ↦ gaussianReal_of_var_ne_zero 0 one_ne_zero]
  rw [pi_withDensity (fun _ ↦ measurable_gaussianPDF 0 1)
    fun _ _ ↦ ENNReal.ofReal_ne_top]
  congr 1
  funext x
  exact prod_gaussianPDF x

/-- The standard Gaussian on a finite-dimensional real inner product space has
density `(2π)^{-d/2} exp(-‖x‖²/2)` with respect to `volume`. -/
theorem stdGaussian_eq_withDensity (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    stdGaussian E =
      volume.withDensity (fun x : E ↦ ENNReal.ofReal (stdGaussianDensity E x)) := by
  set r := Module.finrank ℝ E with hr
  set b := stdOrthonormalBasis ℝ E with hb
  set eLI : EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] E :=
    (EuclideanSpace.basisFun (Fin r) ℝ).equiv b (Equiv.refl (Fin r)) with heLI
  have hT : (fun x : Fin r → ℝ ↦ ∑ i, x i • b i) = ⇑eLI ∘ WithLp.toLp 2 := by
    simp_rw [← b.equiv_apply_euclideanSpace]
    rfl
  have hFmeas : Measurable (fun x : Fin r → ℝ ↦ ∏ i, gaussianPDF 0 1 (x i)) :=
    Finset.measurable_prod _ fun i _ ↦
      (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)
  have htoLp : (WithLp.toLp 2 : (Fin r → ℝ) → EuclideanSpace ℝ (Fin r)) =
      ⇑(MeasurableEquiv.toLp 2 (fun _ : Fin r ↦ ℝ)) := rfl
  have hvolToLp :
      Measure.map ⇑(MeasurableEquiv.toLp 2 (fun _ : Fin r ↦ ℝ)) volume
        = volume := by
    rw [← htoLp]
    exact PiLp.volume_preserving_toLp.map_eq
  have hDmeas : Measurable fun v : EuclideanSpace ℝ (Fin r) ↦
      ENNReal.ofReal ((2 * Real.pi) ^ (-(r : ℝ) / 2)
        * Real.exp (-‖v‖ ^ 2 / 2)) :=
    (measurable_const.mul ((Real.continuous_exp.comp
      ((continuous_norm.pow 2).neg.div_const 2)).measurable)).ennreal_ofReal
  have hcomp : (fun x : Fin r → ℝ ↦ ∏ i, gaussianPDF 0 1 (x i)) ∘
        ⇑(MeasurableEquiv.toLp 2 (fun _ : Fin r ↦ ℝ)).symm
      = fun v : EuclideanSpace ℝ (Fin r) ↦
        ENNReal.ofReal ((2 * Real.pi) ^ (-(r : ℝ) / 2)
          * Real.exp (-‖v‖ ^ 2 / 2)) := by
    funext v
    simp only [Function.comp_apply, MeasurableEquiv.coe_toLp_symm]
    rw [prod_gaussianPDF (WithLp.ofLp v)]
    congr 1
    rw [show (∑ i, ((WithLp.ofLp v) i) ^ 2) = ‖v‖ ^ 2 from
      (EuclideanSpace.real_norm_sq_eq v).symm]
  have heLIcoe : (⇑eLI : EuclideanSpace ℝ (Fin r) → E)
      = ⇑eLI.toMeasurableEquiv := rfl
  have hvolLI : Measure.map ⇑eLI volume = volume :=
    eLI.measurePreserving.map_eq
  rw [stdGaussian_eq_map_pi_orthonormalBasis b, hT, pi_gaussianReal_eq_withDensity]
  rw [htoLp, Measure.map_map eLI.continuous.measurable
    (MeasurableEquiv.toLp 2 _).measurable,
    (MeasurableEquiv.toLp 2 _).map_withDensity volume hFmeas, hvolToLp, hcomp]
  rw [heLIcoe, eLI.toMeasurableEquiv.map_withDensity volume hDmeas,
    ← heLIcoe, hvolLI]
  congr 1
  funext x
  simp only [Function.comp_apply, LinearIsometryEquiv.coe_symm_toMeasurableEquiv,
    eLI.symm.norm_map, stdGaussianDensity, hr]

/-! ### The linear Jacobian: `map A volume = (normDet A)⁻¹ • volume` -/

/-- The pushforward of `volume` by a linear equivalence between
finite-dimensional real inner product spaces is the `normDet`-scaled volume:
the linear case of the coarea/Jacobian factor `√det (L* ∘ L)`. -/
theorem map_volume_linearEquiv {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (A : X ≃ₗ[ℝ] Y) :
    Measure.map ⇑A volume =
      ENNReal.ofReal (A.toLinearMap.normDet)⁻¹ • volume := by
  apply Measure.ext
  intro t ht
  have hA : Measurable ⇑A := A.toLinearMap.continuous_of_finiteDimensional.measurable
  rw [Measure.map_apply hA ht]
  have himg : ⇑A ⁻¹' t = ⇑A.symm '' t := by
    ext x
    constructor
    · intro hx
      exact ⟨A x, hx, A.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [himg]
  have h := LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume
    (f := A.symm.toLinearMap) t
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h
  rw [h, Measure.smul_apply, smul_eq_mul]
  congr 1
  have h1 := LinearMap.normDet_comp_of_finrank_eq A.symm.toLinearMap
    A.toLinearMap A.finrank_eq.symm
  have hid : A.toLinearMap ∘ₗ A.symm.toLinearMap
      = (LinearMap.id : Y →ₗ[ℝ] Y) := by
    ext y
    simp
  rw [hid, LinearMap.normDet_id] at h1
  have hmul : A.symm.toLinearMap.normDet = A.toLinearMap.normDet⁻¹ :=
    eq_inv_of_mul_eq_one_left h1.symm
  rw [hmul]

/-- The pushforward of `stdGaussian X` through a linear equivalence
`A : X ≃ₗ Y` has density `y ↦ (normDet A)⁻¹ * stdGaussianDensity X (A.symm y)`
with respect to `volume`. -/
theorem map_stdGaussian_linearEquiv {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (A : X ≃ₗ[ℝ] Y) :
    (stdGaussian X).map ⇑A = volume.withDensity fun y ↦
      ENNReal.ofReal
        (A.toLinearMap.normDet⁻¹ * stdGaussianDensity X (A.symm y)) := by
  have hp : Measurable fun x : X ↦ ENNReal.ofReal (stdGaussianDensity X x) :=
    (measurable_stdGaussianDensity X).ennreal_ofReal
  rw [stdGaussian_eq_withDensity]
  let eME : X ≃ᵐ Y := A.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hme : ⇑eME = ⇑A := rfl
  have hmes : ⇑eME.symm = ⇑A.symm := rfl
  rw [← hme, eME.map_withDensity volume hp, hme, hmes, map_volume_linearEquiv A,
    smul_withDensity volume _ hp]
  congr 1
  funext y
  simp only [Function.comp_apply]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (LinearMap.normDet_nonneg _))]

/-! ### The Appendix-D.5 Gram operators and the conditional density formula -/

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

variable (L : E →L[ℝ] F)

/-- The Gram operator `G = A ∘ A*` on `range L`, where
`A : ↥(ker L)ᗮ ≃ₗ ↥(range L)` is `gaussEquiv L`. This is the `L L*`-type
operator appearing in the Appendix-D.5 density formula. -/
noncomputable def gramOp (L : E →L[ℝ] F) :
    ↥(LinearMap.range (L : E →ₗ[ℝ] F)) →ₗ[ℝ]
      ↥(LinearMap.range (L : E →ₗ[ℝ] F)) :=
  (gaussEquiv L).toLinearMap ∘ₗ (gaussEquiv L).toLinearMap.adjoint

/-- The Gram operator `Gᵏ = A* ∘ A` on `(ker L)ᗮ`: the `L* L`-type operator
from which `normDet A` is extracted (`normDet A ^ 2 = det Gᵏ`). -/
noncomputable def gramKer (L : E →L[ℝ] F) :
    ↥(LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ →ₗ[ℝ]
      ↥(LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ :=
  (gaussEquiv L).toLinearMap.adjoint ∘ₗ (gaussEquiv L).toLinearMap

/-- The inverse Gram operator `G⁻¹ = (A⁻¹)* ∘ A⁻¹` on `range L`, appearing in
the exponent of the density. -/
noncomputable def gramInv (L : E →L[ℝ] F) :
    ↥(LinearMap.range (L : E →ₗ[ℝ] F)) →ₗ[ℝ]
      ↥(LinearMap.range (L : E →ₗ[ℝ] F)) :=
  (gaussEquiv L).symm.toLinearMap.adjoint ∘ₗ (gaussEquiv L).symm.toLinearMap

/-- `(A⁻¹)* ∘ A* = id` on `range L`: the adjoint-inverse relation used in
`gramInv_comp_gramOp`. -/
theorem gramAdjoint_left :
    (gaussEquiv L).symm.toLinearMap.adjoint ∘ₗ (gaussEquiv L).toLinearMap.adjoint
      = LinearMap.id := by
  have h := LinearMap.adjoint_comp (gaussEquiv L).toLinearMap
    (gaussEquiv L).symm.toLinearMap
  have hid : (gaussEquiv L).toLinearMap ∘ₗ (gaussEquiv L).symm.toLinearMap
      = (LinearMap.id : ↥(LinearMap.range (L : E →ₗ[ℝ] F)) →ₗ[ℝ] _) := by
    ext y
    simp [LinearMap.comp_apply]
  rw [hid, LinearMap.adjoint_id] at h
  exact h.symm

/-- `A* ∘ (A⁻¹)* = id` on `(ker L)ᗮ`. -/
theorem gramAdjoint_right :
    (gaussEquiv L).toLinearMap.adjoint ∘ₗ (gaussEquiv L).symm.toLinearMap.adjoint
      = LinearMap.id := by
  have h := LinearMap.adjoint_comp (gaussEquiv L).symm.toLinearMap
    (gaussEquiv L).toLinearMap
  have hid : (gaussEquiv L).symm.toLinearMap ∘ₗ (gaussEquiv L).toLinearMap
      = (LinearMap.id : ↥(LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ →ₗ[ℝ] _) := by
    ext x
    simp [LinearMap.comp_apply]
  rw [hid, LinearMap.adjoint_id] at h
  exact h.symm

/-- `gramInv` is a left inverse of `gramOp`: `G⁻¹ ∘ G = id` on `range L`. -/
theorem gramInv_comp_gramOp : gramInv L ∘ₗ gramOp L = LinearMap.id := by
  have e1 : ∀ x : ↥(LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ,
      (gaussEquiv L).symm.toLinearMap ((gaussEquiv L).toLinearMap x) = x :=
    fun x ↦ (gaussEquiv L).symm_apply_apply x
  ext y
  simp only [gramInv, gramOp, LinearMap.comp_apply]
  rw [e1]
  exact LinearMap.congr_fun (gramAdjoint_left L) y |>.trans rfl

/-- `gramInv` is a right inverse of `gramOp`: `G ∘ G⁻¹ = id` on `range L`. -/
theorem gramOp_comp_gramInv : gramOp L ∘ₗ gramInv L = LinearMap.id := by
  ext y
  simp only [gramOp, gramInv, LinearMap.comp_apply]
  rw [show (gaussEquiv L).toLinearMap.adjoint
      ((gaussEquiv L).symm.toLinearMap.adjoint ((gaussEquiv L).symm.toLinearMap y))
      = (gaussEquiv L).symm.toLinearMap y from
    LinearMap.congr_fun (gramAdjoint_right L) _]
  exact (gaussEquiv L).apply_symm_apply y

/-- The quadratic form `⟪y, G⁻¹ y⟫` of the density exponent equals
`‖A⁻¹ y‖²`. -/
theorem inner_gramInv (y : ↥(LinearMap.range (L : E →ₗ[ℝ] F))) :
    ⟪y, gramInv L y⟫_ℝ = ‖(gaussEquiv L).symm y‖ ^ 2 := by
  rw [gramInv, LinearMap.comp_apply, LinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]

/-- The quadratic form `⟪x, Gᵏ x⟫` on `(ker L)ᗮ` equals `‖A x‖²`. -/
theorem inner_gramKer (x : ↥(LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ) :
    ⟪x, gramKer L x⟫_ℝ = ‖gaussEquiv L x‖ ^ 2 := by
  rw [gramKer, LinearMap.comp_apply, LinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]

/-- `det Gᵏ = normDet A ^ 2`: the squared Jacobian of `L` restricted to
`(ker L)ᗮ` is the determinant of the `L* L`-type Gram operator. -/
theorem det_gramKer :
    LinearMap.det (gramKer L) = ((gaussEquiv L).toLinearMap.normDet) ^ 2 := by
  have h := LinearMap.normDet_sq (gaussEquiv L).toLinearMap
  rw [gramKer]
  simpa using h.symm

/-- `det G = normDet A ^ 2`: the determinant of the range Gram operator
`G = A ∘ A*` equals the squared Jacobian of `A`. -/
theorem det_gramOp :
    LinearMap.det (gramOp L) = ((gaussEquiv L).toLinearMap.normDet) ^ 2 := by
  classical
  have hfin : Module.finrank ℝ ↥(LinearMap.range (L : E →ₗ[ℝ] F))
      = Module.finrank ℝ ↥(LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ :=
    (gaussEquiv L).finrank_eq.symm
  set r := Module.finrank ℝ ↥(LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ with hr
  let bu : OrthonormalBasis (Fin r) ℝ ↥(LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ :=
    stdOrthonormalBasis ℝ _
  let bv : OrthonormalBasis (Fin r) ℝ ↥(LinearMap.range (L : E →ₗ[ℝ] F)) :=
    (stdOrthonormalBasis ℝ _).reindex (finCongr hfin)
  have hcomp : LinearMap.toMatrix bv.toBasis bv.toBasis (gramOp L) =
      LinearMap.toMatrix bu.toBasis bv.toBasis (gaussEquiv L).toLinearMap
        * LinearMap.toMatrix bv.toBasis bu.toBasis
          (gaussEquiv L).toLinearMap.adjoint := by
    rw [gramOp]
    exact LinearMap.toMatrix_comp bv.toBasis bu.toBasis bv.toBasis
      (gaussEquiv L).toLinearMap.adjoint (gaussEquiv L).toLinearMap
  have hadj : LinearMap.toMatrix bv.toBasis bu.toBasis
        (gaussEquiv L).toLinearMap.adjoint =
      Matrix.conjTranspose
        (LinearMap.toMatrix bu.toBasis bv.toBasis (gaussEquiv L).toLinearMap) :=
    LinearMap.toMatrix_adjoint bu bv (gaussEquiv L).toLinearMap
  rw [← LinearMap.det_toMatrix bv.toBasis, hcomp, hadj, Matrix.det_mul,
    Matrix.det_conjTranspose, star_trivial, ← pow_two]
  rw [LinearMap.normDet_eq_norm_det_toMatrix _ bu bv, Real.norm_eq_abs, sq_abs]

/-- `normDet A = √(det G)`: the Jacobian prefactor is the square root of the
Gram determinant. -/
theorem normDet_gaussEquiv_eq_sqrt_det_gramOp :
    (gaussEquiv L).toLinearMap.normDet = √(LinearMap.det (gramOp L)) := by
  rw [det_gramOp, Real.sqrt_sq (LinearMap.normDet_nonneg _)]

/-- `A` is injective, so its norm-determinant is positive. -/
theorem normDet_gaussEquiv_pos :
    0 < (gaussEquiv L).toLinearMap.normDet := by
  have h : (gaussEquiv L).toLinearMap.normDet ≠ 0 := by
    rw [Ne, LinearMap.normDet_eq_zero_iff_ker_ne_bot, not_not]
    exact LinearEquiv.ker (gaussEquiv L)
  exact lt_of_le_of_ne (LinearMap.normDet_nonneg _) h.symm

/-- The Appendix-D.5 density on `range L`, as a real-valued function:
`p(y) = (2π)^{-r/2} (normDet A)⁻¹ exp(-⟪y, G⁻¹ y⟫ / 2)` where
`r = finrank ℝ (range L)`. -/
noncomputable def gaussDensityReal (L : E →L[ℝ] F)
    (y : ↥(LinearMap.range (L : E →ₗ[ℝ] F))) : ℝ :=
  (gaussEquiv L).toLinearMap.normDet⁻¹
    * (2 * Real.pi) ^ (-(Module.finrank ℝ
        ↥(LinearMap.range (L : E →ₗ[ℝ] F)) : ℝ) / 2)
    * Real.exp (-⟪y, gramInv L y⟫_ℝ / 2)

/-- The Appendix-D.5 density on `range L`, as an `ℝ≥0∞`-valued measurable
function. -/
noncomputable def gaussDensity (L : E →L[ℝ] F)
    (y : ↥(LinearMap.range (L : E →ₗ[ℝ] F))) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussDensityReal L y)

theorem gaussDensityReal_nonneg (y : ↥(LinearMap.range (L : E →ₗ[ℝ] F))) :
    0 ≤ gaussDensityReal L y :=
  mul_nonneg (mul_nonneg (inv_nonneg.mpr (normDet_gaussEquiv_pos L).le)
    (Real.rpow_nonneg (by positivity) _)) (Real.exp_nonneg _)

/-- The density is strictly positive on all of `range L`. -/
theorem gaussDensityReal_pos (y : ↥(LinearMap.range (L : E →ₗ[ℝ] F))) :
    0 < gaussDensityReal L y :=
  mul_pos (mul_pos (inv_pos.mpr (normDet_gaussEquiv_pos L))
    (Real.rpow_pos_of_pos (by positivity) _)) (Real.exp_pos _)

theorem measurable_gaussDensityReal : Measurable (gaussDensityReal L) := by
  have hc : Continuous fun y : ↥(LinearMap.range (L : E →ₗ[ℝ] F)) ↦
      ⟪y, gramInv L y⟫_ℝ :=
    continuous_inner.comp (continuous_id.prodMk
      (gramInv L).continuous_of_finiteDimensional)
  exact measurable_const.mul
    ((Real.continuous_exp.comp (hc.neg.div_const 2)).measurable)

theorem measurable_gaussDensity : Measurable (gaussDensity L) :=
  (measurable_gaussDensityReal L).ennreal_ofReal

/-- The Appendix-D.5 conditional density formula: pushing the standard
Gaussian on `(ker L)ᗮ` through `A = gaussEquiv L` gives the `volume` measure
on `range L` with density `gaussDensity L`. -/
def DensityFormula (L : E →L[ℝ] F) : Prop :=
  (stdGaussian ↥(LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ).map (gaussEquiv L) =
    volume.withDensity (gaussDensity L)

/-- The Appendix-D.5 density formula holds. -/
theorem densityFormula : DensityFormula L := by
  unfold DensityFormula
  rw [map_stdGaussian_linearEquiv (gaussEquiv L)]
  congr 1
  funext y
  simp only [gaussDensity]
  rw [show gaussDensityReal L y = (gaussEquiv L).toLinearMap.normDet⁻¹
        * stdGaussianDensity ↥(LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ
          ((gaussEquiv L).symm y) from ?_]
  · rfl
  unfold gaussDensityReal stdGaussianDensity
  rw [inner_gramInv, (gaussEquiv L).finrank_eq]
  rfl

/-! ### Consequences of the density formula -/

/-- The pushforward of the standard Gaussian on `(ker L)ᗮ` under `A`; equal to
the `withDensity` measure of `gaussDensity L`. -/
noncomputable def gaussPushforward (L : E →L[ℝ] F) :
    Measure ↥(LinearMap.range (L : E →ₗ[ℝ] F)) :=
  (stdGaussian ↥(LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ).map (gaussEquiv L)

theorem gaussPushforward_eq :
    gaussPushforward L = volume.withDensity (gaussDensity L) :=
  densityFormula L

/-- Normalization: `gaussPushforward L` is a probability measure. -/
instance : IsProbabilityMeasure (gaussPushforward L) where
  measure_univ := by
    have hg : Measurable ⇑(gaussEquiv L) :=
      (gaussEquiv L).toLinearMap.continuous_of_finiteDimensional.measurable
    rw [gaussPushforward, Measure.map_apply hg MeasurableSet.univ]
    simp

theorem gaussPushforward_univ : gaussPushforward L Set.univ = 1 :=
  measure_univ

/-- Total mass one, expressed through the density: the Appendix-D.5 density
integrates to `1` over `range L`. -/
theorem gaussDensity_integrates :
    ∫⁻ y, gaussDensity L y ∂volume = 1 := by
  have h1 : (volume.withDensity (gaussDensity L)) Set.univ = 1 := by
    rw [← gaussPushforward_eq L]
    exact gaussPushforward_univ L
  rwa [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h1

/-- The density is pointwise positive, hence nonzero. -/
theorem gaussDensity_pos (y : ↥(LinearMap.range (L : E →ₗ[ℝ] F))) :
    0 < gaussDensity L y := by
  rw [gaussDensity, ENNReal.ofReal_pos]
  exact gaussDensityReal_pos L y

theorem gaussDensity_ne_zero (y : ↥(LinearMap.range (L : E →ₗ[ℝ] F))) :
    gaussDensity L y ≠ 0 :=
  (gaussDensity_pos L y).ne'

theorem gaussDensity_ne_top (y : ↥(LinearMap.range (L : E →ₗ[ℝ] F))) :
    gaussDensity L y ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- The law of `L Z` on `F` is the image of `gaussPushforward L` under the
inclusion `↥(range L) ↪ F`. -/
theorem map_stdGaussian_eq_range :
    (stdGaussian E).map ⇑L =
      (gaussPushforward L).map
        (fun y : ↥(LinearMap.range (L : E →ₗ[ℝ] F)) ↦ (y : F)) := by
  set K := LinearMap.ker (L : E →ₗ[ℝ] F) with hK
  have step := stdGaussian_eq_prod_map_add K
  have hadd : Measurable fun p : ↥K × ↥Kᗮ ↦ (p.1 : E) + (p.2 : E) :=
    ((continuous_subtype_val.comp continuous_fst).add
      (continuous_subtype_val.comp continuous_snd)).measurable
  have hg : Measurable fun v : ↥Kᗮ ↦ L (v : E) :=
    (L.continuous.comp continuous_subtype_val).measurable
  have hge : Measurable ⇑(gaussEquiv L) :=
    (gaussEquiv L).toLinearMap.continuous_of_finiteDimensional.measurable
  have hL : (stdGaussian E).map ⇑L =
      (stdGaussian ↥Kᗮ).map (fun v : ↥Kᗮ ↦ L (v : E)) := by
    conv_lhs => rw [step]
    rw [Measure.map_map L.measurable hadd]
    have hfun : (⇑L ∘ fun p : ↥K × ↥Kᗮ ↦ (p.1 : E) + (p.2 : E))
        = (fun v : ↥Kᗮ ↦ L (v : E)) ∘ Prod.snd := by
      funext p
      simp only [Function.comp_apply]
      have hz : L (p.1 : E) = 0 := LinearMap.mem_ker.mp p.1.2
      rw [map_add, hz, zero_add]
    rw [hfun, ← Measure.map_map hg measurable_snd]
    have hsnd : ((stdGaussian ↥K).prod (stdGaussian ↥Kᗮ)).map Prod.snd =
        stdGaussian ↥Kᗮ := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    rw [hsnd]
  rw [hL]
  have hfun2 : (fun v : ↥Kᗮ ↦ L (v : E))
      = (fun y : ↥(LinearMap.range (L : E →ₗ[ℝ] F)) ↦ (y : F))
        ∘ ⇑(gaussEquiv L) :=
    funext fun v ↦ (gaussEquiv_apply L v).symm
  rw [hfun2, Measure.map_map measurable_subtype_coe hge]
  rfl

/-- Normalization on `F`: `Law(L Z)` is a probability measure. -/
theorem gaussLaw_univ : ((stdGaussian E).map ⇑L) Set.univ = 1 := by
  rw [Measure.map_apply L.measurable MeasurableSet.univ]
  simp

/-- Support: `Law(L Z)` is concentrated on `range L`. -/
theorem gaussLaw_compl_range :
    ((stdGaussian E).map ⇑L)
      ((LinearMap.range (L : E →ₗ[ℝ] F) : Set F)ᶜ) = 0 := by
  have hco : Measurable (fun y : ↥(LinearMap.range (L : E →ₗ[ℝ] F)) ↦ (y : F)) :=
    measurable_subtype_coe
  rw [map_stdGaussian_eq_range,
    Measure.map_apply hco
      ((Submodule.closed_of_finiteDimensional _).measurableSet.compl)]
  have hempty : (fun y : ↥(LinearMap.range (L : E →ₗ[ℝ] F)) ↦ (y : F)) ⁻¹'
      ((LinearMap.range (L : E →ₗ[ℝ] F) : Set F)ᶜ) = ∅ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe,
      Set.mem_empty_iff_false, iff_false, not_not]
    exact y.2
  rw [hempty, measure_empty]

/-- The explicit integral formula for the law of `L Z`: for measurable
`s : Set F`, `Law(LZ)(s)` is the intrinsic-volume integral of the
Appendix-D.5 density over the range-points lying in `s`. -/
theorem gaussLaw_apply (s : Set F) (hs : MeasurableSet s) :
    ((stdGaussian E).map ⇑L) s =
      ∫⁻ y in {y : ↥(LinearMap.range (L : E →ₗ[ℝ] F)) | (y : F) ∈ s},
        gaussDensity L y ∂volume := by
  have hco : Measurable (fun y : ↥(LinearMap.range (L : E →ₗ[ℝ] F)) ↦ (y : F)) :=
    measurable_subtype_coe
  rw [map_stdGaussian_eq_range, Measure.map_apply hco hs, gaussPushforward_eq,
    withDensity_apply _ (hco hs)]
  rfl

/-! ### Stabilizer invariance -/

/-- An isometry `U` of `range L` is a *density stabilizer* if lifting through
`A⁻¹` preserves norms, equivalently if `U` preserves the `G⁻¹`-quadratic form
`⟪y, G⁻¹ y⟫ = ‖A⁻¹ y‖²` appearing in the density exponent. -/
def IsDensityStabilizer (L : E →L[ℝ] F)
    (U : ↥(LinearMap.range (L : E →ₗ[ℝ] F)) ≃ₗᵢ[ℝ]
      ↥(LinearMap.range (L : E →ₗ[ℝ] F))) : Prop :=
  ∀ y : ↥(LinearMap.range (L : E →ₗ[ℝ] F)),
    ‖(gaussEquiv L).symm (U y)‖ = ‖(gaussEquiv L).symm y‖

/-- The Appendix-D.5 density is invariant under density stabilizers. -/
theorem gaussDensity_stabilizer
    {U : ↥(LinearMap.range (L : E →ₗ[ℝ] F)) ≃ₗᵢ[ℝ]
      ↥(LinearMap.range (L : E →ₗ[ℝ] F))}
    (hU : IsDensityStabilizer L U)
    (y : ↥(LinearMap.range (L : E →ₗ[ℝ] F))) :
    gaussDensity L (U y) = gaussDensity L y := by
  simp only [gaussDensity, gaussDensityReal]
  congr 1
  rw [inner_gramInv, inner_gramInv, hU y]

/-- The inverse of a density stabilizer is a density stabilizer. -/
theorem IsDensityStabilizer.symm
    {U : ↥(LinearMap.range (L : E →ₗ[ℝ] F)) ≃ₗᵢ[ℝ]
      ↥(LinearMap.range (L : E →ₗ[ℝ] F))}
    (hU : IsDensityStabilizer L U) : IsDensityStabilizer L U.symm := by
  intro y
  have h := hU (U.symm y)
  rwa [U.apply_symm_apply] at h
  exact h.symm

/-- The pushforward measure is invariant under density stabilizers. -/
theorem gaussPushforward_stabilizer
    {U : ↥(LinearMap.range (L : E →ₗ[ℝ] F)) ≃ₗᵢ[ℝ]
      ↥(LinearMap.range (L : E →ₗ[ℝ] F))}
    (hU : IsDensityStabilizer L U) :
    (gaussPushforward L).map U = gaussPushforward L := by
  rw [gaussPushforward_eq, ← LinearIsometryEquiv.coe_toMeasurableEquiv (f := U),
    U.toMeasurableEquiv.map_withDensity volume (measurable_gaussDensity L)]
  have hvol : Measure.map ⇑U.toMeasurableEquiv volume = volume := by
    simpa only [LinearIsometryEquiv.coe_toMeasurableEquiv] using
      U.measurePreserving.map_eq
  rw [hvol]
  congr 1
  funext y
  rw [Function.comp_apply, LinearIsometryEquiv.coe_symm_toMeasurableEquiv]
  exact gaussDensity_stabilizer L hU.symm y

/-- Stabilizers arise from intertwinings: if `V` is an isometry of `(ker L)ᗮ`
and `U` an isometry of `range L` with `U ∘ A = A ∘ V`, then `U` stabilizes
the density. -/
theorem isDensityStabilizer_of_intertwining
    (V : ↥(LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ ≃ₗᵢ[ℝ]
      ↥(LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ)
    (U : ↥(LinearMap.range (L : E →ₗ[ℝ] F)) ≃ₗᵢ[ℝ]
      ↥(LinearMap.range (L : E →ₗ[ℝ] F)))
    (hUV : ∀ x : ↥(LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ,
      U (gaussEquiv L x) = gaussEquiv L (V x)) :
    IsDensityStabilizer L U := by
  intro y
  have h : (gaussEquiv L).symm (U y) = V ((gaussEquiv L).symm y) := by
    have h2 := hUV ((gaussEquiv L).symm y)
    rw [LinearEquiv.apply_symm_apply] at h2
    have h3 := congrArg (gaussEquiv L).symm h2
    rwa [LinearEquiv.symm_apply_apply] at h3
  rw [h, V.norm_map]

end
end Komlos
