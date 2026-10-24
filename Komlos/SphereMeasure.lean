import Komlos.UniformSphere
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# The normalized uniform measure on the sphere (Gaussian pushforward)

This module upgrades the `dirRV` uniformity story of `Komlos/UniformSphere.lean`.
Mathlib does not provide a named normalized surface measure on the unit sphere
(only `Measure.toSphere`, the unnormalized cone-measure of an additive Haar
measure, see `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`).  We
construct the uniform probability on the sphere directly as the pushforward of
the standard Gaussian under radial normalization `x ↦ ‖x‖⁻¹ • x`.  This is the
classical representation `h = Z/‖Z‖`, `Z ~ N(0, I)`, of the uniform law on the
sphere: `Z ≠ 0` is a null event because the Gaussian is diffuse
(`stdGaussian_zero`), and rotational invariance is immediate from
`stdGaussian_map` because normalization commutes with isometries
(`normalizeVec_isometry`).

## Main results

* `normalizeVec`, `sphereLaw`: the radial projection and the pushforward law
  `(stdGaussian E).map normalizeVec` — a probability measure concentrated a.e.
  on the unit sphere (`ae_sphereLaw_norm`), invariant under every linear
  isometry equivalence (`sphereLaw_map_isometry`) and symmetric under `x ↦ -x`
  (`sphereLaw_neg`).
* `sphereSubtypeMeasure`: the same law realized on the sphere *type*
  `sphere (0 : E) 1` (`sphereSubtypeMeasure_map_val`), invariant under the
  isometry action on the sphere (`sphereSubtypeMeasure_map_isomAct`).
* `sphereVecLaw`: the `Fin k → ℝ` coordinate version built on
  `stdVecMeasure`, identified with `sphereLaw` through `WithLp.ofLp`
  (`sphereVecLaw_eq_map`); a.e. `sqNorm v = 1` (`ae_sphereVecLaw_sqNorm`).
* `sphereLawOn K`: the uniform sphere law of a subspace `K`, pushed forward to
  the ambient space via `K.subtypeₗᵢ`; supported on `sphere ∩ K`
  (`ae_sphereLawOn_norm`, `ae_sphereLawOn_mem`) and invariant under every
  ambient isometry that stabilizes `K` (`sphereLawOn_map_stabilizer`), via the
  restricted isometry `stabRestrict`.
* `uniformSphereMeasure Z`: `sphereLawOn (rangeZ Z)` — an explicit measure
  satisfying the *same* invariance characterization as the sampler's `dirLaw`
  (`uniformSphereMeasure_isUniform : IsUniformSphereLaw Z (uniformSphereMeasure Z)`).
* `IsUniformSphereLawUnique` + `dirLaw_eq_uniformSphereMeasure_of_unique`:
  the honest residual bridge — `dirLaw` equals the true uniform measure
  modulo the missing "unique invariant measure on a homogeneous space"
  theorem.  `dirLaw_eq_uniformSphereMeasure_finrank_one` discharges the
  bridge *unconditionally* when `range Z` is one-dimensional
  (`isUniformSphereLaw_unique_finrank_one`: a fair-oriented law on a
  two-point sphere is forced to be `(δ₊ + δ₋)/2`).
* `IsUniformSphereLaw.integral_inner_eq_zero` (fair orientation ⇒ centered),
  `IsUniformSphereLaw.integral_inner_sq_le` (`𝔼⟪u,h⟫² ≤ ‖u‖²`), and
  `IsUniformSphereLaw.meas_abs_inner_le` (Markov concentration
  `μ{|⟪u,h⟫| ≥ t} ≤ ‖u‖²/t²`) — the distributional conclusions the paper uses,
  proved for *every* `IsUniformSphereLaw`, hence for both `dirLaw` and
  `uniformSphereMeasure`.
-/

namespace Komlos

open MeasureTheory ProbabilityTheory Matrix InnerProductSpace Metric
open scoped BigOperators ENNReal NNReal Classical

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-! ## The radial normalization map -/

/-- The radial projection `x ↦ ‖x‖⁻¹ • x`.  At `x = 0` it returns `0` —
a null event under any diffuse (non-atomic at 0) law. -/
noncomputable def normalizeVec (x : E) : E := ‖x‖⁻¹ • x

theorem measurable_normalizeVec : Measurable (normalizeVec : E → E) :=
  measurable_norm.inv.smul measurable_id

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Normalization produces unit vectors away from `0`. -/
lemma normalizeVec_apply_norm (x : E) (hx : x ≠ 0) : ‖normalizeVec x‖ = 1 := by
  rw [normalizeVec, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- Normalization commutes with linear isometry equivalences. -/
lemma normalizeVec_isometry (U : E ≃ₗᵢ[ℝ] F) (x : E) :
    normalizeVec (U x) = U (normalizeVec x) := by
  rw [normalizeVec, normalizeVec, U.norm_map, map_smul]

/-! ## The Gaussian is diffuse at `0` -/

/-- `N(0, I_E)` puts no mass on `{0}`: the singleton is inside the kernel of
any nonzero inner-product functional, whose pushforward is a real Gaussian
with positive variance, hence absolutely continuous. -/
theorem stdGaussian_zero [Nontrivial E] :
    stdGaussian E ({0} : Set E) = 0 := by
  obtain ⟨w, hw⟩ := exists_ne (0 : E)
  have hsub : ({0} : Set E) ⊆ (innerSL ℝ w) ⁻¹' ({0} : Set ℝ) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [Set.mem_preimage, hx, Set.mem_singleton_iff]
    exact map_zero _
  apply measure_mono_null hsub
  rw [← Measure.map_apply (innerSL ℝ w).measurable (measurableSet_singleton 0),
    IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, innerSL_apply_norm]
  exact gaussianReal_absolutelyContinuous 0
    ((Real.toNNReal_pos.mpr
      (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hw))).ne')
    Real.volume_singleton

/-- The standard Gaussian is a.e. nonzero. -/
theorem stdGaussian_ae_ne_zero [Nontrivial E] :
    ∀ᵐ x ∂(stdGaussian E), x ≠ 0 := by
  have h : {x : E | ¬x ≠ 0} = {0} := by ext x; simp
  rw [ae_iff, h]
  exact stdGaussian_zero

/-! ## The uniform sphere law on `E` -/

/-- The normalized uniform probability measure on the unit sphere of `E`,
realized as the pushforward of `stdGaussian E` under `x ↦ ‖x‖⁻¹ • x`. -/
noncomputable def sphereLaw (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] : Measure E :=
  (stdGaussian E).map normalizeVec

instance : IsProbabilityMeasure (sphereLaw E) :=
  inferInstanceAs (IsProbabilityMeasure ((stdGaussian E).map normalizeVec))

/-- `sphereLaw` is concentrated on the unit sphere. -/
theorem ae_sphereLaw_norm [Nontrivial E] :
    ∀ᵐ x ∂(sphereLaw E), ‖x‖ = 1 := by
  have hmeas : MeasurableSet {x : E | ‖x‖ = 1} :=
    measurableSet_eq_fun measurable_norm measurable_const
  rw [sphereLaw, ae_map_iff measurable_normalizeVec.aemeasurable hmeas]
  filter_upwards [stdGaussian_ae_ne_zero] with x hx
  exact normalizeVec_apply_norm x hx

/-- `sphereLaw` is also concentrated on `E \ {0}`. -/
theorem ae_sphereLaw_ne_zero [Nontrivial E] :
    ∀ᵐ x ∂(sphereLaw E), x ≠ 0 := by
  filter_upwards [ae_sphereLaw_norm (E := E)] with x hx
  intro h0
  rw [h0, norm_zero] at hx
  exact one_ne_zero hx.symm

/-- **Orthogonal invariance**: pushing `sphereLaw E` along a linear isometry
equivalence gives `sphereLaw F`.  This is the rotational invariance of the
uniform sphere measure. -/
theorem sphereLaw_map_isometry (U : E ≃ₗᵢ[ℝ] F) :
    (sphereLaw E).map (⇑U) = sphereLaw F := by
  have hcomp : (⇑U) ∘ normalizeVec = normalizeVec ∘ (⇑U) :=
    funext fun x ↦ (normalizeVec_isometry U x).symm
  calc (sphereLaw E).map (⇑U)
      = (stdGaussian E).map ((⇑U) ∘ normalizeVec) :=
        Measure.map_map U.continuous.measurable measurable_normalizeVec
    _ = (stdGaussian E).map (normalizeVec ∘ (⇑U)) := by rw [hcomp]
    _ = ((stdGaussian E).map U).map normalizeVec :=
        (Measure.map_map measurable_normalizeVec U.continuous.measurable).symm
    _ = (stdGaussian F).map normalizeVec := by rw [stdGaussian_map U]
    _ = sphereLaw F := rfl

/-- `sphereLaw` is symmetric under `x ↦ -x` (fair orientation): negation is a
linear isometry equivalence. -/
theorem sphereLaw_neg : (sphereLaw E).map (fun x : E ↦ -x) = sphereLaw E := by
  rw [← LinearIsometryEquiv.coe_neg (R := ℝ) (E := E)]
  exact sphereLaw_map_isometry (LinearIsometryEquiv.neg ℝ)

/-! ## The same law on the sphere *type* -/

section SphereSubtype

variable [Nontrivial E]

/-- A chosen unit vector, used as the value of `toSpherePt` at `0` (a null
event). -/
noncomputable def sphereDefaultPoint : sphere (0 : E) 1 :=
  ⟨normalizeVec (Classical.choose (exists_ne (0 : E))),
    mem_sphere_zero_iff_norm.mpr
      (normalizeVec_apply_norm _ (Classical.choose_spec (exists_ne (0 : E))))⟩

/-- The a.e.-defined radial retraction `E → sphere 0 1`, made total by a
classical default at `0`. -/
noncomputable def toSpherePt (x : E) : sphere (0 : E) 1 :=
  dite (x ∈ ({0} : Set E)) (fun _ ↦ sphereDefaultPoint)
    (fun h ↦ ⟨normalizeVec x, mem_sphere_zero_iff_norm.mpr
      (normalizeVec_apply_norm x (Set.notMem_singleton_iff.mp h))⟩)

theorem measurable_toSpherePt : Measurable (toSpherePt : E → sphere (0 : E) 1) := by
  refine measurable_of_measurable_on_compl_finite ({0} : Set E)
    (Set.finite_singleton 0) ?_
  have hfun : ({0} : Set E)ᶜ.domRestrict toSpherePt =
      fun y : ↥(({0} : Set E)ᶜ) ↦
        (⟨normalizeVec y.1, mem_sphere_zero_iff_norm.mpr
          (normalizeVec_apply_norm y.1 (Set.notMem_singleton_iff.mp y.2))⟩ :
          sphere (0 : E) 1) := by
    funext ⟨x, hx⟩
    show toSpherePt x = _
    unfold toSpherePt
    rw [dite_eq_right hx]
  rw [hfun]
  exact Measurable.subtype_mk (measurable_normalizeVec.comp measurable_subtype_coe)

/-- The uniform probability measure on the sphere type `sphere (0 : E) 1`. -/
noncomputable def sphereSubtypeMeasure : Measure (sphere (0 : E) 1) :=
  (stdGaussian E).map toSpherePt

instance : IsProbabilityMeasure (sphereSubtypeMeasure (E := E)) :=
  inferInstanceAs (IsProbabilityMeasure ((stdGaussian E).map toSpherePt))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For `x ≠ 0`, `toSpherePt x` is the normalized `x`. -/
lemma toSpherePt_apply_coe {x : E} (hx : x ≠ 0) :
    (toSpherePt x : E) = normalizeVec x := by
  unfold toSpherePt
  rw [dite_eq_right (Set.notMem_singleton_iff.mpr hx)]

/-- The ambient-space version `sphereLaw` is the `Subtype.val`-pushforward of
`sphereSubtypeMeasure`. -/
theorem sphereSubtypeMeasure_map_val :
    (sphereSubtypeMeasure (E := E)).map Subtype.val = sphereLaw E := by
  have hcomp : (Subtype.val : sphere (0 : E) 1 → E) ∘ toSpherePt =ᵐ[stdGaussian E]
      normalizeVec := by
    filter_upwards [stdGaussian_ae_ne_zero] with x hx
    exact toSpherePt_apply_coe hx
  calc (sphereSubtypeMeasure (E := E)).map Subtype.val
      = (stdGaussian E).map (Subtype.val ∘ toSpherePt) :=
        Measure.map_map measurable_subtype_coe measurable_toSpherePt
    _ = (stdGaussian E).map normalizeVec := Measure.map_congr hcomp
    _ = sphereLaw E := rfl

/-- The action of a linear isometry equivalence on the unit sphere. -/
noncomputable def sphereIsomAct (U : E ≃ₗᵢ[ℝ] E) :
    sphere (0 : E) 1 → sphere (0 : E) 1 :=
  fun x ↦ ⟨U x, mem_sphere_zero_iff_norm.mpr (by
    rw [U.norm_map]
    exact mem_sphere_zero_iff_norm.mp x.2)⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] in
lemma measurable_sphereIsomAct (U : E ≃ₗᵢ[ℝ] E) :
    Measurable (sphereIsomAct U) :=
  Measurable.subtype_mk (U.continuous.measurable.comp measurable_subtype_coe)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `toSpherePt` is equivariant under isometries (off the null set `{0}`). -/
lemma sphereIsomAct_toSpherePt (U : E ≃ₗᵢ[ℝ] E) {x : E} (hx : x ≠ 0) :
    sphereIsomAct U (toSpherePt x) = toSpherePt (U x) := by
  have hUx : U x ≠ 0 := by
    intro h
    exact hx (U.injective (h.trans (map_zero U).symm))
  apply Subtype.ext
  show U (toSpherePt x : E) = (toSpherePt (U x) : E)
  rw [toSpherePt_apply_coe hx, toSpherePt_apply_coe hUx,
    normalizeVec_isometry]

/-- The uniform measure on the sphere type is invariant under every
isometry of the sphere induced by an ambient linear isometry. -/
theorem sphereSubtypeMeasure_map_isomAct (U : E ≃ₗᵢ[ℝ] E) :
    (sphereSubtypeMeasure (E := E)).map (sphereIsomAct U) =
      sphereSubtypeMeasure (E := E) := by
  have hcomp : sphereIsomAct U ∘ toSpherePt =ᵐ[stdGaussian E]
      toSpherePt ∘ (⇑U) := by
    filter_upwards [stdGaussian_ae_ne_zero] with x hx
    exact sphereIsomAct_toSpherePt U hx
  calc (sphereSubtypeMeasure (E := E)).map (sphereIsomAct U)
      = (stdGaussian E).map (sphereIsomAct U ∘ toSpherePt) :=
        Measure.map_map (measurable_sphereIsomAct U) measurable_toSpherePt
    _ = (stdGaussian E).map (toSpherePt ∘ (⇑U)) := Measure.map_congr hcomp
    _ = ((stdGaussian E).map ⇑U).map toSpherePt :=
        (Measure.map_map measurable_toSpherePt U.continuous.measurable).symm
    _ = (stdGaussian E).map toSpherePt := by rw [stdGaussian_map U]
    _ = sphereSubtypeMeasure (E := E) := rfl

end SphereSubtype

/-! ## The `Fin k → ℝ` coordinate version -/

section VecVersion

variable {k : ℕ}

/-- `√(sqNorm v)` is the Euclidean norm of `v` under `toLp`. -/
theorem sqrt_sqNorm (v : Fin k → ℝ) :
    Real.sqrt (sqNorm v) = ‖WithLp.toLp 2 v‖ := by
  rw [← sqNorm_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The `Fin k → ℝ` normalization `v ↦ (√(∑ vⱼ²))⁻¹ • v`. -/
noncomputable def normalizeVecFun (v : Fin k → ℝ) : Fin k → ℝ :=
  (Real.sqrt (sqNorm v))⁻¹ • v

theorem measurable_normalizeVecFun :
    Measurable (normalizeVecFun : (Fin k → ℝ) → Fin k → ℝ) := by
  have hsq : Measurable fun v : Fin k → ℝ ↦ sqNorm v :=
    Finset.measurable_sum _ fun j _ ↦ (measurable_pi_apply j).pow_const 2
  exact ((Real.continuous_sqrt.measurable.comp hsq).inv).smul measurable_id

/-- The uniform sphere law on `Fin k → ℝ`: pushforward of the product-Gaussian
`stdVecMeasure` under `v ↦ v/‖v‖₂`. -/
noncomputable def sphereVecLaw (k : ℕ) : Measure (Fin k → ℝ) :=
  (stdVecMeasure k).map normalizeVecFun

instance : IsProbabilityMeasure (sphereVecLaw k) :=
  inferInstanceAs (IsProbabilityMeasure ((stdVecMeasure k).map normalizeVecFun))

/-- `stdVecMeasure` is diffuse at `0` (transported from `stdGaussian` through
the `ofLp` isometry). -/
theorem stdVecMeasure_zero [Nonempty (Fin k)] :
    stdVecMeasure k ({0} : Set (Fin k → ℝ)) = 0 := by
  have : Nontrivial (EuclideanSpace ℝ (Fin k)) := by
    obtain ⟨i⟩ := (inferInstance : Nonempty (Fin k))
    refine ⟨WithLp.toLp 2 (Pi.single i (1 : ℝ)), 0, fun h ↦ ?_⟩
    have h1 : (Pi.single i (1 : ℝ) : Fin k → ℝ) = 0 :=
      (WithLp.toLp_eq_zero 2).mp h
    have h2 := congrFun h1 i
    rw [Pi.single_eq_same, Pi.zero_apply] at h2
    exact one_ne_zero h2
  rw [stdVecMeasure_eq_map,
    Measure.map_apply (WithLp.measurable_ofLp 2 _) (measurableSet_singleton 0)]
  have hpre : (WithLp.ofLp ⁻¹' ({0} : Set (Fin k → ℝ)) :
      Set (EuclideanSpace ℝ (Fin k))) = {0} := by
    ext x
    simp
  rw [hpre]
  exact stdGaussian_zero

/-- `stdVecMeasure`-almost every vector is nonzero. -/
theorem stdVecMeasure_ae_ne_zero [Nonempty (Fin k)] :
    ∀ᵐ v ∂(stdVecMeasure k), v ≠ 0 := by
  have h : {v : Fin k → ℝ | ¬v ≠ 0} = {0} := by ext; simp
  rw [ae_iff, h]
  exact stdVecMeasure_zero

/-- `sphereVecLaw` is concentrated on the `sqNorm`-unit vectors. -/
theorem ae_sphereVecLaw_sqNorm [Nonempty (Fin k)] :
    ∀ᵐ v ∂(sphereVecLaw k), sqNorm v = 1 := by
  have hsq : Measurable fun v : Fin k → ℝ ↦ sqNorm v :=
    Finset.measurable_sum _ fun j _ ↦ (measurable_pi_apply j).pow_const 2
  have hmeas : MeasurableSet {v : Fin k → ℝ | sqNorm v = 1} :=
    measurableSet_eq_fun hsq measurable_const
  rw [sphereVecLaw, ae_map_iff measurable_normalizeVecFun.aemeasurable hmeas]
  filter_upwards [stdVecMeasure_ae_ne_zero] with v hv
  have hpos : 0 < sqNorm v := sqNorm_pos hv
  rw [normalizeVecFun, sqNorm_smul, inv_pow, Real.sq_sqrt hpos.le,
    inv_mul_cancel₀ hpos.ne']

/-- `sphereVecLaw` agrees with `sphereLaw` through the `ofLp` identification
of `EuclideanSpace ℝ (Fin k)` with `Fin k → ℝ`. -/
theorem sphereVecLaw_eq_map (k : ℕ) :
    sphereVecLaw k =
      (sphereLaw (EuclideanSpace ℝ (Fin k))).map WithLp.ofLp := by
  have hcomp : normalizeVecFun ∘
      (WithLp.ofLp : EuclideanSpace ℝ (Fin k) → Fin k → ℝ) =
      (WithLp.ofLp : EuclideanSpace ℝ (Fin k) → Fin k → ℝ) ∘ normalizeVec := by
    funext x
    show (Real.sqrt (sqNorm (WithLp.ofLp x)))⁻¹ • WithLp.ofLp x =
      WithLp.ofLp (‖x‖⁻¹ • x)
    rw [sqrt_sqNorm, WithLp.toLp_ofLp, WithLp.ofLp_smul]
  calc sphereVecLaw k
      = (stdVecMeasure k).map normalizeVecFun := rfl
    _ = ((stdGaussian _).map WithLp.ofLp).map normalizeVecFun := by
        rw [stdVecMeasure_eq_map]
    _ = (stdGaussian _).map (normalizeVecFun ∘ WithLp.ofLp) :=
        Measure.map_map measurable_normalizeVecFun (WithLp.measurable_ofLp 2 _)
    _ = (stdGaussian _).map (WithLp.ofLp ∘ normalizeVec) := by rw [hcomp]
    _ = ((stdGaussian _).map normalizeVec).map WithLp.ofLp :=
        (Measure.map_map (WithLp.measurable_ofLp 2 _)
          measurable_normalizeVec).symm
    _ = (sphereLaw _).map WithLp.ofLp := rfl

end VecVersion

/-! ## The uniform sphere law of a subspace -/

section SubspaceVersion

variable (K : Submodule ℝ E)

/-- The uniform sphere law of a subspace `K`, realized as a measure on the
ambient space: the `K.subtypeₗᵢ`-pushforward of the Gaussian sphere law on
`↥K`. -/
noncomputable def sphereLawOn : Measure E :=
  (sphereLaw ↥K).map K.subtypeₗᵢ

instance : IsProbabilityMeasure (sphereLawOn K) :=
  inferInstanceAs (IsProbabilityMeasure ((sphereLaw ↥K).map K.subtypeₗᵢ))

theorem ae_sphereLawOn_norm [Nontrivial ↥K] :
    ∀ᵐ x ∂(sphereLawOn K), ‖x‖ = 1 := by
  have hmeas : MeasurableSet {x : E | ‖x‖ = 1} :=
    measurableSet_eq_fun measurable_norm measurable_const
  rw [sphereLawOn, ae_map_iff K.subtypeₗᵢ.continuous.measurable.aemeasurable hmeas]
  filter_upwards [ae_sphereLaw_norm (E := ↥K)] with x hx
  rwa [LinearIsometry.norm_map]

theorem ae_sphereLawOn_mem :
    ∀ᵐ x ∂(sphereLawOn K), x ∈ K := by
  have hmeas : MeasurableSet {x : E | x ∈ K} :=
    K.closed_of_finiteDimensional.measurableSet
  rw [sphereLawOn, ae_map_iff K.subtypeₗᵢ.continuous.measurable.aemeasurable hmeas]
  exact Filter.Eventually.of_forall fun x ↦ x.2

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- An ambient isometry that preserves `K` as a set maps `K` onto `K`. -/
lemma submodule_map_eq_of_stabilizer {U : E ≃ₗᵢ[ℝ] E}
    (hUK : ∀ x : E, U x ∈ K ↔ x ∈ K) :
    K.map (U : E →ₗ[ℝ] E) = K := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    exact (hUK x).mpr hx
  · intro y hy
    apply Submodule.mem_map.mpr
    refine ⟨U.symm y, ?_, U.apply_symm_apply y⟩
    exact (hUK (U.symm y)).mp (by rw [U.apply_symm_apply]; exact hy)

/-- The restriction of an ambient linear isometry equivalence to a submodule
it stabilizes. -/
noncomputable def stabRestrict (U : E ≃ₗᵢ[ℝ] E)
    (hUK : ∀ x : E, U x ∈ K ↔ x ∈ K) : ↥K ≃ₗᵢ[ℝ] ↥K :=
  (U.submoduleMap K).trans
    (LinearIsometryEquiv.ofEq _ _ (submodule_map_eq_of_stabilizer K hUK))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma stabRestrict_coe_apply (U : E ≃ₗᵢ[ℝ] E)
    (hUK : ∀ x : E, U x ∈ K ↔ x ∈ K) (x : ↥K) :
    ((stabRestrict K U hUK x : ↥K) : E) = U (x : E) :=
  rfl

/-- `sphereLawOn K` is invariant under every ambient isometry stabilizing `K`:
the ambient action factors through the restricted isometry `stabRestrict`. -/
theorem sphereLawOn_map_stabilizer {U : E ≃ₗᵢ[ℝ] E}
    (hUK : ∀ x : E, U x ∈ K ↔ x ∈ K) :
    (sphereLawOn K).map (⇑U) = sphereLawOn K := by
  have hcomp : (⇑U) ∘ ⇑K.subtypeₗᵢ = ⇑K.subtypeₗᵢ ∘ ⇑(stabRestrict K U hUK) :=
    funext fun x ↦ (stabRestrict_coe_apply K U hUK x).symm
  calc (sphereLawOn K).map (⇑U)
      = (sphereLaw ↥K).map ((⇑U) ∘ ⇑K.subtypeₗᵢ) :=
        Measure.map_map U.continuous.measurable K.subtypeₗᵢ.continuous.measurable
    _ = (sphereLaw ↥K).map (⇑K.subtypeₗᵢ ∘ ⇑(stabRestrict K U hUK)) := by rw [hcomp]
    _ = ((sphereLaw ↥K).map (stabRestrict K U hUK)).map (⇑K.subtypeₗᵢ) :=
        (Measure.map_map K.subtypeₗᵢ.continuous.measurable
          (stabRestrict K U hUK).continuous.measurable).symm
    _ = (sphereLaw ↥K).map (⇑K.subtypeₗᵢ) := by rw [sphereLaw_map_isometry]
    _ = sphereLawOn K := rfl

/-- `sphereLawOn K` is symmetric under `x ↦ -x`. -/
theorem sphereLawOn_neg :
    (sphereLawOn K).map (fun x : E ↦ -x) = sphereLawOn K := by
  have hcomp : (fun x : E ↦ -x) ∘ ⇑K.subtypeₗᵢ =
      ⇑K.subtypeₗᵢ ∘ (fun x : ↥K ↦ -x) :=
    funext fun x ↦ (map_neg K.subtypeₗᵢ.toLinearMap x).symm
  calc (sphereLawOn K).map (fun x : E ↦ -x)
      = (sphereLaw ↥K).map ((fun x : E ↦ -x) ∘ ⇑K.subtypeₗᵢ) :=
        Measure.map_map measurable_neg K.subtypeₗᵢ.continuous.measurable
    _ = (sphereLaw ↥K).map (⇑K.subtypeₗᵢ ∘ (fun x : ↥K ↦ -x)) := by rw [hcomp]
    _ = ((sphereLaw ↥K).map (fun x : ↥K ↦ -x)).map (⇑K.subtypeₗᵢ) :=
        (Measure.map_map K.subtypeₗᵢ.continuous.measurable measurable_neg).symm
    _ = (sphereLaw ↥K).map (⇑K.subtypeₗᵢ) := by rw [sphereLaw_neg]
    _ = sphereLawOn K := rfl

end SubspaceVersion

/-! ## The uniform sphere measure on `range Z` -/

section UniformOnRange

variable {s m : ℕ}

/-- `range Z` is nontrivial when `Z` has linearly independent columns: the
first column `Z *ᵥ e₀` is a nonzero element. -/
theorem nontrivial_rangeZ {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    (hZ : Function.Injective Z.mulVecLin) : Nontrivial ↥(rangeZ Z) := by
  have hv : Z *ᵥ (Pi.single (0 : Fin (m + 1)) 1) ≠ 0 := by
    apply mulVec_ne_zero_of_injective hZ
    intro h
    have h2 := congrFun h (0 : Fin (m + 1))
    rw [Pi.single_eq_same, Pi.zero_apply] at h2
    exact one_ne_zero h2
  refine ⟨⟨WithLp.toLp 2 (Z *ᵥ Pi.single (0 : Fin (m + 1)) 1),
    mem_rangeZ.mpr ⟨_, rfl⟩⟩, 0, ?_⟩
  intro h
  apply hv
  have h2 : WithLp.toLp 2 (Z *ᵥ Pi.single (0 : Fin (m + 1)) 1) =
      (0 : EuclideanSpace ℝ (Fin s)) := by
    have := Subtype.ext_iff.mp h
    simpa using this
  exact WithLp.toLp_injective 2 h2

/-- The normalized uniform measure on the unit sphere of `range Z`:
the `rangeZ`-Gaussian sphere law pushed into the ambient Euclidean space. -/
noncomputable def uniformSphereMeasure (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    Measure (EuclideanSpace ℝ (Fin s)) :=
  sphereLawOn (rangeZ Z)

instance (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    IsProbabilityMeasure (uniformSphereMeasure Z) :=
  inferInstanceAs (IsProbabilityMeasure (sphereLawOn (rangeZ Z)))

/-- **The true uniform measure satisfies the surrogate spec.**
`uniformSphereMeasure Z` is an explicit probability measure (independent of
the sampler) satisfying the exact `IsUniformSphereLaw` characterization that
`dirRV_law_uniform` proves for `dirLaw`. -/
theorem uniformSphereMeasure_isUniform {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    (hZ : Function.Injective Z.mulVecLin) :
    IsUniformSphereLaw Z (uniformSphereMeasure Z) := by
  have := nontrivial_rangeZ hZ
  exact ⟨inferInstance, ae_sphereLawOn_norm (rangeZ Z),
    ae_sphereLawOn_mem (rangeZ Z),
    fun U hU ↦ sphereLawOn_map_stabilizer (rangeZ Z) (fun x ↦ hU.1 x),
    sphereLawOn_neg (rangeZ Z)⟩

/-- **The residual uniqueness hypothesis**: any two measures satisfying the
stabilizer-invariance characterization coincide.  Mathematically true — a
transitive compact group action on a sphere admits a unique invariant
probability measure — but not yet available in Mathlib (it would follow from
Haar-measure uniqueness on `O(range Z)` packaged for the orbit map).  This is
the *only* remaining gap between `dirRV`'s law and the literal uniform sphere
measure. -/
def IsUniformSphereLawUnique (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) : Prop :=
  ∀ μ ν : Measure (EuclideanSpace ℝ (Fin s)),
    IsUniformSphereLaw Z μ → IsUniformSphereLaw Z ν → μ = ν

/-- Under the uniqueness hypothesis, `dirRV`'s law *is* the normalized
uniform measure on the sphere of `range Z` — closing the distributional half
of Theorem 4.1 to a single, clearly-labeled residual. -/
theorem dirLaw_eq_uniformSphereMeasure_of_unique
    {Z : Matrix (Fin s) (Fin (m + 1)) ℝ} (hZ : Function.Injective Z.mulVecLin)
    (hu : IsUniformSphereLawUnique Z) :
    dirLaw Z = uniformSphereMeasure Z :=
  hu _ _ (dirRV_law_uniform hZ) (uniformSphereMeasure_isUniform hZ)

end UniformOnRange

/-! ## Unconditional uniqueness in dimension 1 -/

section DimOne

variable {s m : ℕ}

/-- In a one-dimensional subspace, every unit vector is `x₀` or `-x₀`. -/
theorem eq_or_eq_neg_of_finrank_one {K : Submodule ℝ (EuclideanSpace ℝ (Fin s))}
    (hK : Module.finrank ℝ ↥K = 1)
    {x₀ x : EuclideanSpace ℝ (Fin s)}
    (hx₀ : x₀ ∈ K) (hx₀n : ‖x₀‖ = 1) (hx : x ∈ K) (hxn : ‖x‖ = 1) :
    x = x₀ ∨ x = -x₀ := by
  have hx₀ne : x₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx₀n
    exact one_ne_zero hx₀n.symm
  have hspan : Submodule.span ℝ {x₀} = K :=
    Submodule.eq_of_le_of_finrank_le
      ((Submodule.span_singleton_le_iff_mem x₀ K).mpr hx₀)
      (hK.trans (finrank_span_singleton hx₀ne).symm).le
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hx)
  have hcabs : |c| = 1 := by
    have h1 : ‖x‖ = |c| * ‖x₀‖ := by
      rw [← hc, norm_smul]
      simp
    rw [hxn, hx₀n, mul_one] at h1
    exact h1.symm
  rcases eq_or_eq_neg_of_abs_eq hcabs with h | h
  · left
    rw [← hc, h, one_smul]
  · right
    rw [← hc, h, neg_smul, one_smul]

/-- A symmetric probability measure concentrated (a.e.) on the antipodal pair
`{x₀, -x₀}` puts mass `1/2` on each point. -/
theorem measure_singleton_eq_half {μ : Measure (EuclideanSpace ℝ (Fin s))}
    [IsProbabilityMeasure μ] {x₀ : EuclideanSpace ℝ (Fin s)}
    (hx₀ : x₀ ≠ -x₀)
    (ht : ∀ᵐ x ∂μ, x = x₀ ∨ x = -x₀) (hsym : μ.map (fun x ↦ -x) = μ) :
    μ {x₀} = (2 : ℝ≥0∞)⁻¹ ∧ μ {-x₀} = (2 : ℝ≥0∞)⁻¹ := by
  have hae : ∀ᵐ x ∂μ, x ∈ ({x₀, -x₀} : Set (EuclideanSpace ℝ (Fin s))) := ht
  have htset : MeasurableSet ({x₀, -x₀} : Set (EuclideanSpace ℝ (Fin s))) :=
    ((Set.finite_singleton _).insert _).measurableSet
  have ht1 : μ ({x₀, -x₀} : Set (EuclideanSpace ℝ (Fin s))) = 1 :=
    (mem_ae_iff_prob_eq_one htset).mp hae
  have hdisj : Disjoint ({x₀} : Set (EuclideanSpace ℝ (Fin s))) {-x₀} :=
    Set.disjoint_singleton_right.mpr fun h ↦ hx₀ h.symm
  have hsum : μ {x₀} + μ {-x₀} = 1 := by
    rw [← measure_union hdisj (measurableSet_singleton _)]
    rw [show ({x₀} : Set _) ∪ {-x₀} = {x₀, -x₀} from rfl]
    exact ht1
  have hnegpre : (fun x : EuclideanSpace ℝ (Fin s) ↦ -x) ⁻¹' {x₀} = {-x₀} := by
    ext x
    simp
  have heq : μ {x₀} = μ {-x₀} := by
    conv_lhs => rw [← hsym]
    rw [Measure.map_apply measurable_neg (measurableSet_singleton x₀), hnegpre]
  have h2 : μ {x₀} * (2 : ℝ≥0∞) = 1 := by
    rw [mul_comm, two_mul]
    nth_rw 2 [heq]
    exact hsum
  have h3 : μ {-x₀} * (2 : ℝ≥0∞) = 1 := by
    rw [mul_comm, two_mul]
    nth_rw 1 [← heq]
    exact hsum
  exact ⟨ENNReal.eq_inv_of_mul_eq_one_left h2,
    ENNReal.eq_inv_of_mul_eq_one_left h3⟩

/-- Two symmetric probability measures concentrated on the same antipodal pair
coincide. -/
theorem measure_eq_of_ae_pair {μ ν : Measure (EuclideanSpace ℝ (Fin s))}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {x₀ : EuclideanSpace ℝ (Fin s)} (hx₀ : x₀ ≠ -x₀)
    (hμ : ∀ᵐ x ∂μ, x = x₀ ∨ x = -x₀) (hμs : μ.map (fun x ↦ -x) = μ)
    (hν : ∀ᵐ x ∂ν, x = x₀ ∨ x = -x₀) (hνs : ν.map (fun x ↦ -x) = ν) :
    μ = ν := by
  obtain ⟨hμ0, hμn⟩ := measure_singleton_eq_half hx₀ hμ hμs
  obtain ⟨hν0, hνn⟩ := measure_singleton_eq_half hx₀ hν hνs
  have htcμ : μ ({x₀, -x₀} : Set (EuclideanSpace ℝ (Fin s)))ᶜ = 0 :=
    mem_ae_iff.mp hμ
  have htcν : ν ({x₀, -x₀} : Set (EuclideanSpace ℝ (Fin s)))ᶜ = 0 :=
    mem_ae_iff.mp hν
  have htset : MeasurableSet ({x₀, -x₀} : Set (EuclideanSpace ℝ (Fin s))) :=
    ((Set.finite_singleton _).insert _).measurableSet
  apply Measure.ext
  intro t htm
  have hkey : ∀ ρ : Measure (EuclideanSpace ℝ (Fin s)),
      ρ ({x₀, -x₀} : Set (EuclideanSpace ℝ (Fin s)))ᶜ = 0 →
      ρ t = ρ (t ∩ {x₀}) + ρ (t ∩ {-x₀}) := by
    intro ρ hρc
    calc ρ t = ρ (t ∩ {x₀, -x₀}) + ρ (t \ {x₀, -x₀}) :=
          (measure_inter_add_sdiff t htset).symm
      _ = ρ (t ∩ {x₀, -x₀}) := by
          rw [measure_mono_null
            (show t \ {x₀, -x₀} ⊆ ({x₀, -x₀} : Set _)ᶜ from fun _ hx ↦ hx.2)
            hρc, add_zero]
      _ = ρ ((t ∩ {x₀}) ∪ (t ∩ {-x₀})) := by
          congr 1
          rw [show {x₀, -x₀} = ({x₀} : Set _) ∪ {-x₀} from rfl,
            Set.inter_union_distrib_left]
      _ = ρ (t ∩ {x₀}) + ρ (t ∩ {-x₀}) := by
          apply measure_union
          · rw [Set.disjoint_left]
            rintro x ⟨_, rfl⟩ ⟨_, h2⟩
            rw [Set.mem_singleton_iff] at h2
            exact hx₀ h2
          · exact htm.inter (measurableSet_singleton _)
  rw [hkey μ htcμ, hkey ν htcν]
  have hμx : μ (t ∩ {x₀}) = if x₀ ∈ t then (2 : ℝ≥0∞)⁻¹ else 0 := by
    by_cases hx : x₀ ∈ t
    · rw [Set.inter_singleton_of_mem hx, hμ0, ite_eq_left hx]
    · rw [Set.inter_singleton_eq_empty.mpr hx, measure_empty, ite_eq_right hx]
  have hνx : ν (t ∩ {x₀}) = if x₀ ∈ t then (2 : ℝ≥0∞)⁻¹ else 0 := by
    by_cases hx : x₀ ∈ t
    · rw [Set.inter_singleton_of_mem hx, hν0, ite_eq_left hx]
    · rw [Set.inter_singleton_eq_empty.mpr hx, measure_empty, ite_eq_right hx]
  have hμnx : μ (t ∩ {-x₀}) = if -x₀ ∈ t then (2 : ℝ≥0∞)⁻¹ else 0 := by
    by_cases hx : -x₀ ∈ t
    · rw [Set.inter_singleton_of_mem hx, hμn, ite_eq_left hx]
    · rw [Set.inter_singleton_eq_empty.mpr hx, measure_empty, ite_eq_right hx]
  have hνnx : ν (t ∩ {-x₀}) = if -x₀ ∈ t then (2 : ℝ≥0∞)⁻¹ else 0 := by
    by_cases hx : -x₀ ∈ t
    · rw [Set.inter_singleton_of_mem hx, hνn, ite_eq_left hx]
    · rw [Set.inter_singleton_eq_empty.mpr hx, measure_empty, ite_eq_right hx]
  rw [hμx, hμnx, hνx, hνnx]

/-- **Unconditional uniqueness in dimension 1**: on a one-dimensional
`range Z`, the `IsUniformSphereLaw` characterization already determines the
law — the fair-oriented measure on the two-point sphere `{±x₀}` is forced to
be `(δ_{x₀} + δ_{-x₀})/2`.  In particular the surrogate is *complete* here:
`dirRV`'s law equals the true uniform measure with no extra hypothesis. -/
theorem isUniformSphereLaw_unique_finrank_one
    {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    (hK : Module.finrank ℝ ↥(rangeZ Z) = 1)
    {μ ν : Measure (EuclideanSpace ℝ (Fin s))}
    (hμ : IsUniformSphereLaw Z μ) (hν : IsUniformSphereLaw Z ν) : μ = ν := by
  obtain ⟨x₀, hx₀mem, hx₀n⟩ :
      ∃ x₀ ∈ rangeZ Z, ‖x₀‖ = 1 := by
    have hne : rangeZ Z ≠ ⊥ := by
      intro hbot
      rw [hbot] at hK
      simp at hK
    obtain ⟨x, hx, hxne⟩ := (Submodule.ne_bot_iff (rangeZ Z)).mp hne
    refine ⟨‖x‖⁻¹ • x, (rangeZ Z).smul_mem _ hx, ?_⟩
    rw [norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hxne)]
  have hx₀ne : x₀ ≠ -x₀ := by
    intro hneg
    have hadd : x₀ + x₀ = 0 := eq_neg_iff_add_eq_zero.mp hneg
    have h0 : x₀ = 0 := by
      have h2 : (2 : ℝ) • x₀ = 0 := by rw [two_smul]; exact hadd
      exact (smul_eq_zero_iff_right two_ne_zero).mp h2
    rw [h0, norm_zero] at hx₀n
    exact one_ne_zero hx₀n.symm
  have htwo : ∀ {ρ : Measure (EuclideanSpace ℝ (Fin s))},
      IsUniformSphereLaw Z ρ → ∀ᵐ x ∂ρ, x = x₀ ∨ x = -x₀ := by
    intro ρ hρ
    filter_upwards [hρ.sphere, hρ.mem_range] with x hn hm
    exact eq_or_eq_neg_of_finrank_one hK hx₀mem hx₀n hm hn
  have := hμ.isProb
  have := hν.isProb
  exact measure_eq_of_ae_pair hx₀ne (htwo hμ) hμ.symmetric (htwo hν) hν.symmetric

/-- In dimension 1, `dirRV`'s law *is* the normalized uniform measure on the
sphere of `range Z` — no uniqueness hypothesis needed. -/
theorem dirLaw_eq_uniformSphereMeasure_finrank_one
    {Z : Matrix (Fin s) (Fin (m + 1)) ℝ} (hZ : Function.Injective Z.mulVecLin)
    (hK : Module.finrank ℝ ↥(rangeZ Z) = 1) :
    dirLaw Z = uniformSphereMeasure Z :=
  isUniformSphereLaw_unique_finrank_one hK (dirRV_law_uniform hZ)
    (uniformSphereMeasure_isUniform hZ)

end DimOne

/-! ## Distributional conclusions: centering, second moment, concentration -/

section Conclusions

variable {s m : ℕ}

/-- A linear functional is square-integrable under a uniform sphere law
(it is a.e. bounded by `‖u‖`). -/
theorem IsUniformSphereLaw.integrable_inner_sq
    {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    {μ : Measure (EuclideanSpace ℝ (Fin s))} (h : IsUniformSphereLaw Z μ)
    (u : EuclideanSpace ℝ (Fin s)) :
    Integrable (fun x ↦ (⟪u, x⟫_ℝ) ^ 2) μ := by
  have := h.isProb
  apply Integrable.of_bound _ (‖u‖ ^ 2)
  · filter_upwards [h.sphere] with x hx
    have hb : |⟪u, x⟫_ℝ| ≤ ‖u‖ :=
      (abs_real_inner_le_norm u x).trans (by rw [hx, mul_one])
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' ((neg_le_neg hb).trans (neg_abs_le _))
      ((le_abs_self _).trans hb)
  · exact (((innerSL ℝ u).measurable).pow_const 2).aestronglyMeasurable

/-- **Fair orientation ⇒ centered**: every linear functional has mean zero
under a uniform sphere law — the conclusion the paper's "fair orientation"
gives, proved for every `IsUniformSphereLaw` (hence for `dirLaw` and for
`uniformSphereMeasure` alike). -/
theorem IsUniformSphereLaw.integral_inner_eq_zero
    {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    {μ : Measure (EuclideanSpace ℝ (Fin s))} (h : IsUniformSphereLaw Z μ)
    (u : EuclideanSpace ℝ (Fin s)) :
    ∫ x, ⟪u, x⟫_ℝ ∂μ = 0 := by
  have := h.isProb
  have hI : Integrable (fun x ↦ ⟪u, x⟫_ℝ) μ := by
    apply Integrable.of_bound _ ‖u‖
    · filter_upwards [h.sphere] with x hx
      calc ‖⟪u, x⟫_ℝ‖ ≤ ‖u‖ * ‖x‖ := norm_inner_le_norm u x
        _ = ‖u‖ := by rw [hx, mul_one]
    · exact (innerSL ℝ u).measurable.aestronglyMeasurable
  have key : (∫ x, ⟪u, x⟫_ℝ ∂μ) = -∫ x, ⟪u, x⟫_ℝ ∂μ := by
    conv_lhs => rw [← h.symmetric]
    have hg : AEStronglyMeasurable (fun x ↦ ⟪u, x⟫_ℝ)
        (μ.map fun x ↦ -x) := by
      rw [h.symmetric]
      exact hI.aestronglyMeasurable
    rw [integral_map measurable_neg.aemeasurable hg]
    simp_rw [inner_neg_right]
    rw [integral_neg]
  linarith

/-- Second-moment bound: `𝔼⟪u,h⟫² ≤ ‖u‖²`, valid for every uniform sphere
law (the sharp value `‖u‖²/d` would need the uniqueness/covariance
computation). -/
theorem IsUniformSphereLaw.integral_inner_sq_le
    {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    {μ : Measure (EuclideanSpace ℝ (Fin s))} (h : IsUniformSphereLaw Z μ)
    (u : EuclideanSpace ℝ (Fin s)) :
    ∫ x, (⟪u, x⟫_ℝ) ^ 2 ∂μ ≤ ‖u‖ ^ 2 := by
  have := h.isProb
  have hle : ∀ᵐ x ∂μ, (⟪u, x⟫_ℝ) ^ 2 ≤ ‖u‖ ^ 2 := by
    filter_upwards [h.sphere] with x hx
    have hb : |⟪u, x⟫_ℝ| ≤ ‖u‖ :=
      (abs_real_inner_le_norm u x).trans (by rw [hx, mul_one])
    exact sq_le_sq' ((neg_le_neg hb).trans (neg_abs_le _))
      ((le_abs_self _).trans hb)
  calc ∫ x, (⟪u, x⟫_ℝ) ^ 2 ∂μ ≤ ∫ _x, ‖u‖ ^ 2 ∂μ :=
        integral_mono_ae (h.integrable_inner_sq u) (integrable_const _) hle
    _ = ‖u‖ ^ 2 := by simp [integral_const]

/-- **Markov concentration**: for a uniform sphere law,
`μ {x | t ≤ |⟪u, x⟫|} ≤ ‖u‖² / t²` — the quadratic tail bound behind the
paper's small-ball/concentration bookkeeping, valid for `dirLaw` and
`uniformSphereMeasure` alike. -/
theorem IsUniformSphereLaw.meas_abs_inner_le
    {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    {μ : Measure (EuclideanSpace ℝ (Fin s))} (h : IsUniformSphereLaw Z μ)
    (u : EuclideanSpace ℝ (Fin s)) {t : ℝ} (ht : 0 < t) :
    μ {x | t ≤ |⟪u, x⟫_ℝ|} ≤ ENNReal.ofReal (‖u‖ ^ 2 / t ^ 2) := by
  have := h.isProb
  have hsub : {x : EuclideanSpace ℝ (Fin s) | t ≤ |⟪u, x⟫_ℝ|} ⊆
      {x | ENNReal.ofReal (t ^ 2) ≤ ENNReal.ofReal ((⟪u, x⟫_ℝ) ^ 2)} := by
    intro x hx
    show ENNReal.ofReal (t ^ 2) ≤ ENNReal.ofReal ((⟪u, x⟫_ℝ) ^ 2)
    rw [ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)]
    calc t ^ 2 ≤ |⟪u, x⟫_ℝ| ^ 2 :=
          sq_le_sq.mpr (by rw [abs_abs, abs_of_nonneg ht.le]; exact hx)
      _ = (⟪u, x⟫_ℝ) ^ 2 := sq_abs _
  apply (measure_mono hsub).trans
  have hfm : AEMeasurable (fun x ↦ ENNReal.ofReal ((⟪u, x⟫_ℝ) ^ 2)) μ :=
    (((innerSL ℝ u).measurable.pow_const 2).ennreal_ofReal).aemeasurable
  calc μ {x | ENNReal.ofReal (t ^ 2) ≤ ENNReal.ofReal ((⟪u, x⟫_ℝ) ^ 2)}
      ≤ (∫⁻ x, ENNReal.ofReal ((⟪u, x⟫_ℝ) ^ 2) ∂μ) / ENNReal.ofReal (t ^ 2) :=
        meas_ge_le_lintegral_div hfm
          (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_ne_zero ht.ne'))
          ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (∫ x, (⟪u, x⟫_ℝ) ^ 2 ∂μ) / ENNReal.ofReal (t ^ 2) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable_inner_sq u)
          (Filter.Eventually.of_forall fun x ↦ sq_nonneg _)]
    _ ≤ ENNReal.ofReal (‖u‖ ^ 2) / ENNReal.ofReal (t ^ 2) := by
        apply ENNReal.div_le_div_right
        exact ENNReal.ofReal_le_ofReal (h.integral_inner_sq_le u)
    _ = ENNReal.ofReal (‖u‖ ^ 2 / t ^ 2) := by
        rw [← ENNReal.ofReal_div_of_pos (sq_pos_of_ne_zero ht.ne')]

/-- Instantiated to the true uniform sphere measure. -/
theorem uniformSphereMeasure_integral_inner_eq_zero
    {Z : Matrix (Fin s) (Fin (m + 1)) ℝ} (hZ : Function.Injective Z.mulVecLin)
    (u : EuclideanSpace ℝ (Fin s)) :
    ∫ x, ⟪u, x⟫_ℝ ∂(uniformSphereMeasure Z) = 0 :=
  (uniformSphereMeasure_isUniform hZ).integral_inner_eq_zero u

/-- Instantiated to the sampler's direction law: `dirRV`'s law is centered —
a new conclusion beyond `UniformSphere.lean`'s invariance/symmetry story. -/
theorem dirLaw_integral_inner_eq_zero
    {Z : Matrix (Fin s) (Fin (m + 1)) ℝ} (hZ : Function.Injective Z.mulVecLin)
    (u : EuclideanSpace ℝ (Fin s)) :
    ∫ x, ⟪u, x⟫_ℝ ∂(dirLaw Z) = 0 :=
  (dirRV_law_uniform hZ).integral_inner_eq_zero u

/-- The `‖u‖² / t²` tail bound for the sampler's direction. -/
theorem dirLaw_meas_abs_inner_le
    {Z : Matrix (Fin s) (Fin (m + 1)) ℝ} (hZ : Function.Injective Z.mulVecLin)
    (u : EuclideanSpace ℝ (Fin s)) {t : ℝ} (ht : 0 < t) :
    dirLaw Z {x | t ≤ |⟪u, x⟫_ℝ|} ≤ ENNReal.ofReal (‖u‖ ^ 2 / t ^ 2) :=
  (dirRV_law_uniform hZ).meas_abs_inner_le u ht

end Conclusions

end

end Komlos
