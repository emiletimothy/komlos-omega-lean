/-
# Conditional standard Gaussian laws under linear maps

This module discharges the abstract regular-conditional-distribution hypothesis
(item 3 of the dependency inventory in `GaussianCompletion.lean`): for
`Z ~ N(0, I_E)` on a finite-dimensional real inner product space and a
continuous linear map `L : E →L[ℝ] F`, the conditional law of `Z` given
`L Z = y` is standard Gaussian on `ker L` shifted by a canonical lift
`gaussLift L y` (the unique preimage of `y` inside `(ker L)ᗮ`, i.e. the
Moore–Penrose pseudoinverse applied to `y`). This is the analytic core behind
the paper's "hidden Gaussian rows stay Gaussian after conditioning on the
exposed history" invariant.

Everything is proved unconditionally (no `sorry`, no axioms, no hypotheses
standing in for missing theorems).

## Main statements

* `stdGaussian_eq_prod_map_add`: sampling split `Z = W + V` with `W ~ N(0, I_K)`
  and `V ~ N(0, I_Kᗮ)` independent, for any subspace `K`.
* `stdGaussian_map_orthogonalProjectionOnto_prod`: the two orthogonal
  projections of `Z` onto `K` and `Kᗮ` are independent standard Gaussians.
* `gaussLift`: the canonical partial inverse of `L`, satisfying
  `gaussLift L (L z) = (ker L)ᗮ`-component of `z` (`gaussLift_apply_self`).
* `stdGaussian_eq_prod_map_add_gaussLift`: the sampling form of the
  conditional law — draw `y ~ L∗N(0,I_E)` and independently `w ~ N(0,I_{ker L})`,
  output `w + gaussLift L y`.
* `gaussCondKernel`: the kernel `y ↦ N(0,I_{ker L})` shifted by `gaussLift L y`,
  with `stdGaussian_map_prodMk_compProd` expressing the joint law of `(LZ, Z)`
  as `Law(LZ) ⊗ₘ gaussCondKernel`.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.Unique

namespace Komlos

open InnerProductSpace MeasureTheory ProbabilityTheory

noncomputable section

/-- Pairing an element of `K` with `t : E` only sees the `K`-component of `t`. -/
theorem inner_coe_eq_inner_proj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Submodule ℝ E) (w : K) (t : E) :
    ⟪(w : E), t⟫_ℝ = ⟪w, K.orthogonalProjectionOnto t⟫_ℝ :=
  (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left w t).symm

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

section OrthogonalSplit

variable (K : Submodule ℝ E)

/-- Sampling identity for the standard Gaussian: `Z = W + V` where
`W ~ N(0, I_K)` and `V ~ N(0, I_Kᗮ)` are independent. Proved by identifying
characteristic functions: the product law has characteristic function
`exp(-(‖P_K t‖² + ‖P_Kᗮ t‖²)/2) = exp(-‖t‖²/2)` by Pythagoras. -/
theorem stdGaussian_eq_prod_map_add :
    stdGaussian E =
      ((stdGaussian ↥K).prod (stdGaussian ↥Kᗮ)).map
        (fun p : ↥K × ↥Kᗮ ↦ (p.1 : E) + (p.2 : E)) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stdGaussian]
  have hcont : Continuous fun p : ↥K × ↥Kᗮ ↦ (p.1 : E) + (p.2 : E) :=
    (continuous_subtype_val.comp continuous_fst).add
      (continuous_subtype_val.comp continuous_snd)
  rw [charFun_apply, integral_map hcont.measurable.aemeasurable
    (by fun_prop : AEStronglyMeasurable
      (fun x ↦ Complex.exp (⟪x, t⟫_ℝ * Complex.I))
      (((stdGaussian ↥K).prod (stdGaussian ↥Kᗮ)).map
        (fun p : ↥K × ↥Kᗮ ↦ (p.1 : E) + (p.2 : E))))]
  have hsplit :
      (fun p : ↥K × ↥Kᗮ ↦ Complex.exp (⟪(p.1 : E) + (p.2 : E), t⟫_ℝ * Complex.I)) =
        fun p ↦ Complex.exp (⟪(p.1 : E), t⟫_ℝ * Complex.I) *
          Complex.exp (⟪(p.2 : E), t⟫_ℝ * Complex.I) := by
    funext p
    rw [inner_add_left, Complex.ofReal_add, add_mul, Complex.exp_add]
  have hfprod :=
    integral_prod_mul (μ := stdGaussian ↥K) (ν := stdGaussian ↥Kᗮ)
      (fun w : ↥K ↦ Complex.exp (⟪(w : E), t⟫_ℝ * Complex.I))
      (fun v : ↥Kᗮ ↦ Complex.exp (⟪(v : E), t⟫_ℝ * Complex.I))
  rw [hsplit, hfprod]
  have hK : (∫ w : ↥K, Complex.exp (⟪(w : E), t⟫_ℝ * Complex.I)
        ∂(stdGaussian ↥K))
      = Complex.exp (-(‖K.orthogonalProjectionOnto t‖ ^ 2) / 2) := by
    have hcongr :
        (fun w : ↥K ↦ Complex.exp (⟪(w : E), t⟫_ℝ * Complex.I)) =
          fun w ↦ Complex.exp (⟪w, K.orthogonalProjectionOnto t⟫_ℝ * Complex.I) := by
      funext w
      rw [inner_coe_eq_inner_proj K w t]
    rw [hcongr, ← charFun_apply, charFun_stdGaussian]
  have hKC : (∫ v : ↥Kᗮ, Complex.exp (⟪(v : E), t⟫_ℝ * Complex.I)
        ∂(stdGaussian ↥Kᗮ))
      = Complex.exp (-(‖Kᗮ.orthogonalProjectionOnto t‖ ^ 2) / 2) := by
    have hcongr :
        (fun v : ↥Kᗮ ↦ Complex.exp (⟪(v : E), t⟫_ℝ * Complex.I)) =
          fun v ↦ Complex.exp (⟪v, Kᗮ.orthogonalProjectionOnto t⟫_ℝ * Complex.I) := by
      funext v
      rw [inner_coe_eq_inner_proj Kᗮ v t]
    rw [hcongr, ← charFun_apply, charFun_stdGaussian]
  rw [hK, hKC, ← Complex.exp_add]
  congr 1
  have h : (-(‖K.orthogonalProjectionOnto t‖^2 : ℝ)) / 2 +
      -(‖Kᗮ.orthogonalProjectionOnto t‖^2 : ℝ) / 2 = -(‖t‖^2 : ℝ) / 2 := by
    linarith [K.norm_sq_eq_add_norm_sq_projection t]
  exact_mod_cast h.symm

/-- The two orthogonal projections of `Z ~ N(0,I_E)` onto `K` and `Kᗮ` are
independent standard Gaussians. -/
theorem stdGaussian_map_orthogonalProjectionOnto_prod :
    (stdGaussian E).map
        (fun z ↦ (K.orthogonalProjectionOnto z, Kᗮ.orthogonalProjectionOnto z)) =
      (stdGaussian ↥K).prod (stdGaussian ↥Kᗮ) := by
  have hadd : Measurable fun p : ↥K × ↥Kᗮ ↦ (p.1 : E) + (p.2 : E) :=
    ((continuous_subtype_val.comp continuous_fst).add
      (continuous_subtype_val.comp continuous_snd)).measurable
  have hproj : Measurable fun z ↦
      (K.orthogonalProjectionOnto z, Kᗮ.orthogonalProjectionOnto z) :=
    ((K.orthogonalProjectionOnto).continuous.prodMk
      (Kᗮ.orthogonalProjectionOnto).continuous).measurable
  rw [stdGaussian_eq_prod_map_add K, Measure.map_map hproj hadd]
  have hid : ((fun z ↦ (K.orthogonalProjectionOnto z, Kᗮ.orthogonalProjectionOnto z))
      ∘ fun p : ↥K × ↥Kᗮ ↦ (p.1 : E) + (p.2 : E)) = id := by
    funext p
    refine Prod.ext ?_ ?_
    · show K.orthogonalProjectionOnto ((p.1 : E) + (p.2 : E)) = p.1
      rw [map_add, K.orthogonalProjectionOnto_mem_subspace_eq_self p.1,
        K.orthogonalProjectionOnto_eq_zero_iff.mpr p.2.property, add_zero]
    · show Kᗮ.orthogonalProjectionOnto ((p.1 : E) + (p.2 : E)) = p.2
      rw [map_add,
        Kᗮ.orthogonalProjectionOnto_eq_zero_iff.mpr
          (K.le_orthogonal_orthogonal p.1.property),
        Kᗮ.orthogonalProjectionOnto_mem_subspace_eq_self p.2, zero_add]
  rw [hid, Measure.map_id]

end OrthogonalSplit

section ConditionalLaw

set_option linter.unusedSectionVars false

variable (L : E →L[ℝ] F)

/-- The restriction of `L` to `(ker L)ᗮ` is injective. -/
theorem ker_domRestrict_ker_orthogonal :
    LinearMap.ker ((L : E →ₗ[ℝ] F).domRestrict (LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have h1 : (x : E) ∈ LinearMap.ker (L : E →ₗ[ℝ] F) := hx
  have h2 : (x : E) ∈
      LinearMap.ker (L : E →ₗ[ℝ] F) ⊓ (LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ := ⟨h1, x.2⟩
  have h3 : LinearMap.ker (L : E →ₗ[ℝ] F) ⊓ (LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ = ⊥ :=
    (Submodule.orthogonal_disjoint _).eq_bot
  rw [h3] at h2
  have h4 : (x : E) = 0 := by simpa using h2
  exact Subtype.ext h4

/-- The image of `L` restricted to `(ker L)ᗮ` is the full range of `L`. -/
theorem range_domRestrict_ker_orthogonal :
    LinearMap.range ((L : E →ₗ[ℝ] F).domRestrict (LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ) =
      LinearMap.range (L : E →ₗ[ℝ] F) := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, rfl⟩
    exact LinearMap.mem_range_self _ (x : E)
  · rintro y ⟨x, rfl⟩
    refine ⟨(LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ.orthogonalProjectionOnto x, ?_⟩
    have h1 : L (((LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ.orthogonalProjectionOnto x : E)) = L x := by
      rw [Submodule.coe_orthogonalProjectionOnto_apply]
      conv_rhs =>
        rw [← (LinearMap.ker (L : E →ₗ[ℝ] F)).starProjection_add_starProjection_orthogonal x]
      have hz : L ((LinearMap.ker (L : E →ₗ[ℝ] F)).starProjection x) = 0 :=
        LinearMap.mem_ker.mp
          ((LinearMap.ker (L : E →ₗ[ℝ] F)).starProjection_apply_mem x)
      rw [map_add, hz, zero_add]
    exact h1

/-- The linear equivalence `(ker L)ᗮ ≃ₗ LinearMap.range L` induced by `L`. -/
noncomputable def gaussEquiv :
    ↥(LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ ≃ₗ[ℝ] LinearMap.range (L : E →ₗ[ℝ] F) :=
  (LinearEquiv.ofInjective
      ((L : E →ₗ[ℝ] F).domRestrict (LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ)
      (LinearMap.ker_eq_bot.mp (ker_domRestrict_ker_orthogonal L))).trans
    (LinearEquiv.ofEq _ _ (range_domRestrict_ker_orthogonal L))

/-- Under `gaussEquiv`, `L` is the coercion `↥(range L) → F`. -/
theorem gaussEquiv_apply (x : ↥(LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ) :
    L (x : E) = ((gaussEquiv L x : LinearMap.range (L : E →ₗ[ℝ] F)) : F) := by
  have h : ((gaussEquiv L x : LinearMap.range (L : E →ₗ[ℝ] F)) : F) =
      ((L : E →ₗ[ℝ] F).domRestrict (LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ) x := by
    rw [gaussEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
      LinearEquiv.ofInjective_apply]
  rw [h]
  rfl

theorem gaussEquiv_symm (y : ↥(LinearMap.range (L : E →ₗ[ℝ] F))) :
    L (((gaussEquiv L).symm y : ↥(LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ) : E) = (y : F) := by
  have h := gaussEquiv_apply L ((gaussEquiv L).symm y)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h

/-- The canonical lift (Moore–Penrose pseudoinverse of `L`): projects `y : F`
orthogonally onto `LinearMap.range L`, then takes the unique preimage inside
`(ker L)ᗮ`. For `y = L z` it returns the `(ker L)ᗮ`-component of `z`. -/
noncomputable def gaussLift : F →L[ℝ] E :=
  ((LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ).subtypeL ∘L
    ((gaussEquiv L).symm.toLinearMap.toContinuousLinearMap) ∘L
      (LinearMap.range (L : E →ₗ[ℝ] F)).orthogonalProjectionOnto

/-- `gaussLift L y` always lands in `(ker L)ᗮ`. -/
theorem gaussLift_mem_ker_orthogonal (y : F) :
    gaussLift L y ∈ (LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ := by
  simp only [gaussLift, ContinuousLinearMap.coe_comp, Function.comp_apply,
    Submodule.subtypeL_apply]
  exact SetLike.coe_mem _

/-- `gaussLift` is a right inverse of `L` on `LinearMap.range L`. -/
theorem gaussLift_lifting {y : F} (hy : y ∈ LinearMap.range (L : E →ₗ[ℝ] F)) :
    L (gaussLift L y) = y := by
  have hproj : (LinearMap.range (L : E →ₗ[ℝ] F)).orthogonalProjectionOnto y = ⟨y, hy⟩ :=
    (LinearMap.range (L : E →ₗ[ℝ] F)).orthogonalProjectionOnto_mem_subspace_eq_self
      ⟨y, hy⟩
  simp only [gaussLift, ContinuousLinearMap.coe_comp, Function.comp_apply,
    Submodule.subtypeL_apply, LinearMap.coe_toContinuousLinearMap',
    LinearEquiv.coe_coe, hproj]
  exact gaussEquiv_symm L ⟨y, hy⟩

/-- Applying the lift to `L z` recovers the `(ker L)ᗮ`-component of `z`. -/
theorem gaussLift_apply_self (z : E) :
    gaussLift L (L z) = (LinearMap.ker (L : E →ₗ[ℝ] F))ᗮ.starProjection z := by
  set K := LinearMap.ker (L : E →ₗ[ℝ] F)
  have hinj : Function.Injective ((L : E →ₗ[ℝ] F).domRestrict Kᗮ) :=
    LinearMap.ker_eq_bot.mp (ker_domRestrict_ker_orthogonal L)
  have hmem : gaussLift L (L z) ∈ Kᗮ := gaussLift_mem_ker_orthogonal L (L z)
  have hmem2 : Kᗮ.starProjection z ∈ Kᗮ := Kᗮ.starProjection_apply_mem z
  have hL_eq : L (gaussLift L (L z)) = L (Kᗮ.starProjection z) := by
    have h1 := gaussLift_lifting L (y := L z) ⟨z, rfl⟩
    rw [h1]
    nth_rw 1 [← K.starProjection_add_starProjection_orthogonal z]
    have hz : L (K.starProjection z) = 0 :=
      LinearMap.mem_ker.mp (K.starProjection_apply_mem z)
    rw [map_add, hz, zero_add]
  have hdom : ((L : E →ₗ[ℝ] F).domRestrict Kᗮ) ⟨gaussLift L (L z), hmem⟩ =
      ((L : E →ₗ[ℝ] F).domRestrict Kᗮ) ⟨Kᗮ.starProjection z, hmem2⟩ := hL_eq
  exact congrArg Subtype.val (hinj hdom)

/-- Sampling form of the conditional Gaussian law: `Z` has the law of
`W + c Y` where `W ~ N(0, I_{ker L})` is independent of `Y ~ L∗N(0, I_E)` and
`c = gaussLift L`. Conditional on `L Z = y`, `Z` is therefore standard
Gaussian on `ker L` shifted by `c y`. -/
theorem stdGaussian_eq_prod_map_add_gaussLift :
    stdGaussian E =
      ((stdGaussian ↥(LinearMap.ker (L : E →ₗ[ℝ] F))).prod
        ((stdGaussian E).map L)).map
        (fun p : ↥(LinearMap.ker (L : E →ₗ[ℝ] F)) × F ↦
          (p.1 : E) + gaussLift L p.2) := by
  set K := LinearMap.ker (L : E →ₗ[ℝ] F) with hK
  have step := stdGaussian_eq_prod_map_add K
  have hadd : Measurable fun p : ↥K × ↥Kᗮ ↦ (p.1 : E) + (p.2 : E) :=
    ((continuous_subtype_val.comp continuous_fst).add
      (continuous_subtype_val.comp continuous_snd)).measurable
  have hg : Measurable fun v : ↥Kᗮ ↦ L (v : E) :=
    (L.continuous.comp continuous_subtype_val).measurable
  have hL : (stdGaussian E).map L =
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
  calc stdGaussian E
      = ((stdGaussian ↥K).prod (stdGaussian ↥Kᗮ)).map
          (fun p : ↥K × ↥Kᗮ ↦ (p.1 : E) + (p.2 : E)) := step
    _ = ((stdGaussian ↥K).prod (stdGaussian ↥Kᗮ)).map
          ((fun p : ↥K × F ↦ (p.1 : E) + gaussLift L p.2)
            ∘ Prod.map id (fun v : ↥Kᗮ ↦ L (v : E))) := by
        congr 1
        funext p
        obtain ⟨w, v⟩ := p
        show (w : E) + (v : E) = (w : E) + gaussLift L (L (v : E))
        rw [gaussLift_apply_self, Kᗮ.starProjection_eq_self_iff.mpr v.2]
    _ = (((stdGaussian ↥K).prod (stdGaussian ↥Kᗮ)).map
          (Prod.map id (fun v : ↥Kᗮ ↦ L (v : E)))).map
          (fun p : ↥K × F ↦ (p.1 : E) + gaussLift L p.2) := by
        rw [← Measure.map_map
          (show Measurable fun p : ↥K × F ↦ (p.1 : E) + gaussLift L p.2 from
            ((continuous_subtype_val.comp continuous_fst).add
              ((gaussLift L).continuous.comp continuous_snd)).measurable)
          (show Measurable (Prod.map id fun v : ↥Kᗮ ↦ L (v : E)) from
            measurable_id.prodMap hg)]
    _ = (((stdGaussian ↥K).map id).prod
          ((stdGaussian ↥Kᗮ).map (fun v : ↥Kᗮ ↦ L (v : E)))).map
          (fun p : ↥K × F ↦ (p.1 : E) + gaussLift L p.2) := by
        rw [← Measure.map_prod_map _ _ measurable_id hg]
    _ = ((stdGaussian ↥K).prod ((stdGaussian E).map L)).map
          (fun p : ↥K × F ↦ (p.1 : E) + gaussLift L p.2) := by
        rw [Measure.map_id, ← hL]

/-- The conditional kernel `y ↦ N(0, I_{ker L})` shifted by `gaussLift L y`. -/
noncomputable def gaussCondKernel : Kernel F E :=
  ⟨fun y ↦ (stdGaussian ↥(LinearMap.ker (L : E →ₗ[ℝ] F))).map
      (fun w : ↥(LinearMap.ker (L : E →ₗ[ℝ] F)) ↦ (w : E) + gaussLift L y),
    Measure.measurable_measure.mpr fun s hs ↦ by
      set K := LinearMap.ker (L : E →ₗ[ℝ] F)
      have hTmeas : MeasurableSet
          ((fun p : F × ↥K ↦ (p.2 : E) + gaussLift L p.1) ⁻¹' s) :=
        (((continuous_subtype_val.comp continuous_snd).add
          ((gaussLift L).continuous.comp continuous_fst)).measurable) hs
      have hfun : (fun y ↦ ((stdGaussian ↥K).map
            (fun w : ↥K ↦ (w : E) + gaussLift L y)) s)
          = fun y ↦ (stdGaussian ↥K)
            (Prod.mk y ⁻¹'
              ((fun p : F × ↥K ↦ (p.2 : E) + gaussLift L p.1) ⁻¹' s)) := by
        funext y
        rw [Measure.map_apply
          (show Measurable fun w : ↥K ↦ (w : E) + gaussLift L y from
            (continuous_subtype_val.add continuous_const).measurable) hs]
        rfl
      rw [hfun]
      exact measurable_measure_prodMk_left hTmeas⟩

/-- `gaussCondKernel` evaluated at `y` is `N(0, I_{ker L})` shifted by
`gaussLift L y`. -/
theorem gaussCondKernel_apply (y : F) :
    gaussCondKernel L y =
      (stdGaussian ↥(LinearMap.ker (L : E →ₗ[ℝ] F))).map
        (fun w : ↥(LinearMap.ker (L : E →ₗ[ℝ] F)) ↦ (w : E) + gaussLift L y) := rfl

instance : IsMarkovKernel (gaussCondKernel L) :=
  ⟨fun y ↦ by
    show IsProbabilityMeasure
      ((stdGaussian ↥(LinearMap.ker (L : E →ₗ[ℝ] F))).map
        (fun w : ↥(LinearMap.ker (L : E →ₗ[ℝ] F)) ↦ (w : E) + gaussLift L y))
    infer_instance⟩

/-- The joint law of `(L Z, Z)` is `Law(L Z) ⊗ₘ gaussCondKernel`: the kernel
`gaussCondKernel` is a regular conditional distribution of `Z` given `L Z`. -/
theorem stdGaussian_map_prodMk_compProd :
    (stdGaussian E).map (fun z ↦ (L z, z)) =
      ((stdGaussian E).map ⇑L) ⊗ₘ gaussCondKernel L := by
  set K := LinearMap.ker (L : E →ₗ[ℝ] F) with hK
  have hsamp := stdGaussian_eq_prod_map_add_gaussLift L
  have hsum : Measurable fun p : ↥K × F ↦ (p.1 : E) + gaussLift L p.2 :=
    ((continuous_subtype_val.comp continuous_fst).add
      ((gaussLift L).continuous.comp continuous_snd)).measurable
  have hLz : Measurable fun z ↦ (L z, z) := L.measurable.prodMk measurable_id
  have hG : Measurable fun p : F × ↥K ↦ (p.1, (p.2 : E) + gaussLift L p.1) :=
    measurable_fst.prodMk
      (((continuous_subtype_val.comp continuous_snd).add
        ((gaussLift L).continuous.comp continuous_fst)).measurable)
  -- `L (gaussLift L y) = y` holds `μL`-a.e. because `μL` is supported on
  -- `LinearMap.range L`.
  have hT : ∀ᵐ y ∂((stdGaussian E).map L), L (gaussLift L y) = y := by
    have hclosed : IsClosed (LinearMap.range (L : E →ₗ[ℝ] F) : Set F) :=
      (LinearMap.range (L : E →ₗ[ℝ] F)).closed_of_finiteDimensional
    have hcompl : ((stdGaussian E).map L)
        ((LinearMap.range (L : E →ₗ[ℝ] F))ᶜ) = 0 := by
      rw [Measure.map_apply L.measurable hclosed.measurableSet.compl]
      have huniv : ⇑L ⁻¹' ((LinearMap.range (L : E →ₗ[ℝ] F)) : Set F) = Set.univ :=
        Set.eq_univ_of_forall fun z ↦ LinearMap.mem_range_self _ z
      rw [Set.preimage_compl, huniv, Set.compl_univ, measure_empty]
    rw [ae_iff]
    apply measure_mono_null ?_ hcompl
    intro y hy hy'
    exact hy (gaussLift_lifting L hy')
  -- On the product `ν ×ˢ μL`, `(w, y) ↦ (L (w + c y), w + c y)` is a.e. equal
  -- to `(w, y) ↦ (y, w + c y)`.
  have hcond : ∀ᵐ p : ↥K × F ∂((stdGaussian ↥K).prod ((stdGaussian E).map ⇑L)),
      L ((p.1 : E) + gaussLift L p.2) = p.2 := by
    have hs_meas : MeasurableSet
        {p : ↥K × F | L ((p.1 : E) + gaussLift L p.2) = p.2} := by
      have hfs : Measurable fun p : ↥K × F ↦
          L ((p.1 : E) + gaussLift L p.2) - p.2 :=
        (L.measurable.comp hsum).sub measurable_snd
      have hset : {p : ↥K × F | L ((p.1 : E) + gaussLift L p.2) = p.2} =
          (fun p : ↥K × F ↦ L ((p.1 : E) + gaussLift L p.2) - p.2) ⁻¹' {0} := by
        ext p
        simp [sub_eq_zero]
      rw [hset]
      exact (measurableSet_singleton 0).preimage hfs
    have hcond_set : ∀ᵐ p : ↥K × F ∂((stdGaussian ↥K).prod ((stdGaussian E).map ⇑L)),
        p ∈ {p : ↥K × F | L ((p.1 : E) + gaussLift L p.2) = p.2} := by
      rw [Measure.ae_prod_mem_iff_ae_ae_mem hs_meas]
      filter_upwards with w
      filter_upwards [hT] with y hy
      have hw : L (w : E) = 0 := LinearMap.mem_ker.mp w.2
      show L ((w : E) + gaussLift L y) = y
      rw [map_add, hw, zero_add]
      exact hy
    filter_upwards [hcond_set] with p hp
    exact hp
  calc (stdGaussian E).map (fun z ↦ (L z, z))
      = (((stdGaussian ↥K).prod ((stdGaussian E).map ⇑L)).map
          (fun p : ↥K × F ↦ (p.1 : E) + gaussLift L p.2)).map
          (fun z ↦ (L z, z)) := by conv_lhs => rw [hsamp]
    _ = ((stdGaussian ↥K).prod ((stdGaussian E).map ⇑L)).map
          ((fun z ↦ (L z, z)) ∘ fun p : ↥K × F ↦
            (p.1 : E) + gaussLift L p.2) := by
        rw [← Measure.map_map hLz hsum]
    _ = ((stdGaussian ↥K).prod ((stdGaussian E).map ⇑L)).map
          (fun p : ↥K × F ↦ (p.2, (p.1 : E) + gaussLift L p.2)) := by
        refine Measure.map_congr ?_
        filter_upwards [hcond] with p hp
        exact Prod.ext hp rfl
    _ = (((stdGaussian E).map ⇑L).prod (stdGaussian ↥K)).map
          (fun p : F × ↥K ↦ (p.1, (p.2 : E) + gaussLift L p.1)) := by
        have hsw : (fun p : ↥K × F ↦ (p.2, (p.1 : E) + gaussLift L p.2)) =
            (fun p : F × ↥K ↦ (p.1, (p.2 : E) + gaussLift L p.1)) ∘
              Prod.swap := by
          funext p
          rfl
        rw [hsw, ← Measure.map_map hG measurable_swap, Measure.prod_swap]
    _ = ((stdGaussian E).map ⇑L) ⊗ₘ gaussCondKernel L := by
        ext s hs
        rw [Measure.compProd_apply hs, Measure.map_apply hG hs,
          Measure.prod_apply (hG hs)]
        apply lintegral_congr
        intro y
        rw [gaussCondKernel_apply L y,
          Measure.map_apply
            (show Measurable fun w : ↥K ↦ (w : E) + gaussLift L y from
              (continuous_subtype_val.add continuous_const).measurable)
            (hs.preimage measurable_prodMk_left)]
        congr 1

end ConditionalLaw
