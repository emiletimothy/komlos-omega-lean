import Komlos
import Komlos.GaussianDensity
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Uniformity of the sampler's normalized direction (distributional half of Theorem 4.1)

The Section-4 completion sampler outputs `h = dirRV Z` on the unit sphere of
`range Z`.  Theorem 4.1 of the paper asserts that `h` is *uniform* on that
sphere with a *fair orientation*.  Since Mathlib has no normalized uniform
sphere measure, we prove the equivalent invariance statement: the law of `h`
is invariant under every Euclidean isometry `U` that maps `range Z` to itself
and fixes `(range Z)ᗮ` pointwise (the stabilizer of `range Z`, isomorphic to
`O(range Z)`), and under negation (the fair sign).

## Mathematical argument

Write `p = (g, r)` for the sampler's random input and `Q = completionQ Z g r`.

* `hiddenRowsMeasure` is a product of `stdVecMeasure`s; each `stdVecMeasure` is
  `ofLp`-pushforward of `stdGaussian`, which is invariant under linear
  isometries (`stdGaussian_map`).  Hence the source measure is invariant under
  `S : (g, r) ↦ (U∘gᵢ, r)` (`measurePreserving_stabSourceMap`) and under
  `T : (g, r) ↦ (g, -r)` (`measurePreserving_negRefMap`).
* Equivariance (`dirRV_equivariance`): if `Z` has injective `mulVecLin` and `U`
  stabilizes `range Z`, let `A y := (ZᵀZ)⁻¹ Zᵀ (U (Z y))` — the coefficient of
  `U (Z y)` in the `Z`-basis.  On the a.s. event `det Q ≠ 0`, `det Q(Sp) ≠ 0`,
  one has `Q(Sp) *ᵥ A y = ⟨r, A y⟩ • e_k`, hence `y(Sp) = A y / ⟨r, A y⟩` and
  `h(Sp) = sgn⟨r, A y⟩ • U h(p)` exactly.
* Sign decoupling (`measure_map_smul_eq_map_of_even_odd`): the
  sign `ρ(p) = sgn⟨r, A y⟩` is even under `T` while `U h` is odd, so
  `Law(ρ • U h) = Law(U h)`.  Combined with invariance under `S` this gives
  `Law(U h) = Law(h)`, i.e. `dirLaw.map U = dirLaw` (`dirRV_law_invariant`).
* Fair orientation (`dirRV_law_neg`): `h(g, -r) = -h(g,r)` exactly, so
  `Law(-h) = Law(h)` by invariance under `T`.

Since any probability measure on the unit sphere of `range Z` invariant under
the full stabilizer is the normalized uniform (Haar) measure, stabilizer
invariance + symmetry is the honest surrogate for uniformity; see
`IsUniformSphereLaw` and `dirRV_law_uniform`.

## Main results

* `IsStabilizerZ`, `stabConjugate`, `stabSign`: the stabilizer predicate, the
  coefficient conjugator `y ↦ (ZᵀZ)⁻¹Zᵀ(UZy)`, and the equivariance sign.
* `measure_map_smul_eq_map_of_even_odd`: the even/odd sign-decoupling lemma.
* `dirRV_equivariance`: pointwise equivariance on the nonsingular event.
* `dirRV_law_invariant`, `dirRV_law_neg`, `ae_dirLaw_norm`, `ae_dirLaw_range`.
* `dirRV_law_uniform`: `IsUniformSphereLaw Z (dirLaw Z)`.
* `dirRVUniformStatement_holds`: the (weaker, trivially-true) placeholder
  `dirRVUniformStatement` of `GaussianDensity.lean`.
-/

namespace Komlos

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators InnerProductSpace

noncomputable section

variable {s m k : ℕ}

/-- Abbreviation for the sampler's probability space. -/
abbrev SamplerSpace (m s : ℕ) := (Fin m → Fin s → ℝ) × (Fin (m + 1) → ℝ)

/-! ## Isometries on coefficient vectors -/

/-- The action of a Euclidean isometry `U` on a plain coefficient vector
`v : Fin k → ℝ`, via the `WithLp.toLp`/`WithLp.ofLp` identification. -/
noncomputable def isomAct
    (U : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k))
    (v : Fin k → ℝ) : Fin k → ℝ :=
  WithLp.ofLp (U (WithLp.toLp 2 v))

@[simp]
theorem toLp_isomAct
    (U : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k))
    (v : Fin k → ℝ) :
    WithLp.toLp 2 (isomAct U v) = U (WithLp.toLp 2 v) := rfl

theorem measurable_isomAct
    (U : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
    Measurable (isomAct U) :=
  (WithLp.measurable_ofLp 2 _).comp
    (U.continuous.measurable.comp (WithLp.measurable_toLp 2 _))

theorem injective_isomAct
    (U : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
    Function.Injective (isomAct U) := by
  intro a b h
  have h2 := congrArg (WithLp.toLp 2) h
  rw [toLp_isomAct, toLp_isomAct] at h2
  have h3 := congrArg ⇑U.symm h2
  rw [U.symm_apply_apply, U.symm_apply_apply] at h3
  exact WithLp.toLp_injective 2 h3

theorem isomAct_smul
    (U : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k))
    (a : ℝ) (v : Fin k → ℝ) :
    isomAct U (a • v) = a • isomAct U v := by
  simp [isomAct, WithLp.toLp_smul, map_smul]

theorem isomAct_neg
    (U : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k))
    (v : Fin k → ℝ) :
    isomAct U (-v) = -isomAct U v := by
  simp [isomAct]

theorem isomAct_zero
    (U : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
    isomAct U 0 = 0 := by
  simpa using isomAct_smul (k := k) U 0 0

/-- `Fin k → ℝ` dot product agrees with the Euclidean inner product under
`toLp`. -/
theorem dotProduct_eq_inner_toLp (a b : Fin k → ℝ) :
    a ⬝ᵥ b = ⟪WithLp.toLp 2 a, WithLp.toLp 2 b⟫_ℝ := by
  simp only [dotProduct, PiLp.inner_apply, RCLike.inner_apply',
    starRingEnd_apply, star_trivial]

theorem isomAct_dotProduct
    (U : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k))
    (a b : Fin k → ℝ) :
    isomAct U a ⬝ᵥ isomAct U b = a ⬝ᵥ b := by
  rw [dotProduct_eq_inner_toLp, toLp_isomAct, toLp_isomAct, U.inner_map_map,
    ← dotProduct_eq_inner_toLp]

theorem sqNorm_isomAct
    (U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s))
    (v : Fin s → ℝ) :
    sqNorm (isomAct U v) = sqNorm v := by
  rw [← sqNorm_eq_norm_sq, ← sqNorm_eq_norm_sq, toLp_isomAct, U.norm_map]

theorem sqNorm_smul (a : ℝ) (v : Fin s → ℝ) :
    sqNorm (a • v) = a ^ 2 * sqNorm v := by
  unfold sqNorm
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.mul_sum]

theorem sqNorm_neg (v : Fin s → ℝ) : sqNorm (-v) = sqNorm v := by
  simpa using sqNorm_smul (-1) v

/-! ## The standard Gaussian on `Fin k → ℝ` is orthogonally invariant -/

/-- `stdVecMeasure` is invariant under the coordinatewise action of any linear
isometry of `EuclideanSpace ℝ (Fin k)` — the rotational invariance of the
standard Gaussian, transported through `ofLp`. -/
theorem stdVecMeasure_map_isomAct
    (U : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
    (stdVecMeasure k).map (isomAct U) = stdVecMeasure k := by
  have hcomp : isomAct U ∘
      (WithLp.ofLp : EuclideanSpace ℝ (Fin k) → Fin k → ℝ) =
      WithLp.ofLp ∘ (⇑U) := by
    funext x
    simp [isomAct]
  rw [stdVecMeasure_eq_map,
    Measure.map_map (measurable_isomAct U) (WithLp.measurable_ofLp 2 _),
    hcomp,
    ← Measure.map_map (WithLp.measurable_ofLp 2 _) U.continuous.measurable,
    stdGaussian_map, ← stdVecMeasure_eq_map]

/-- `stdVecMeasure` is symmetric under `v ↦ -v`. -/
theorem stdVecMeasure_map_neg :
    (stdVecMeasure k).map (fun v : Fin k → ℝ ↦ -v) = stdVecMeasure k := by
  have hneg : (fun v : Fin k → ℝ ↦ -v) =
      isomAct (LinearIsometryEquiv.neg ℝ) := by
    funext v
    simp [isomAct]
  rw [hneg, stdVecMeasure_map_isomAct]

/-! ## Measure-preserving transformations of the sampler source -/

/-- Apply `U` to every hidden Gaussian row and leave the reference row fixed. -/
noncomputable def stabSourceMap
    (U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s)) :
    SamplerSpace m s → SamplerSpace m s :=
  Prod.map (fun g i ↦ isomAct U (g i)) id

/-- Negate the reference row. -/
noncomputable def negRefMap : SamplerSpace m s → SamplerSpace m s :=
  Prod.map id (fun r ↦ -r)

theorem measurable_stabSourceMap
    (U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s)) :
    Measurable (stabSourceMap (m := m) U) :=
  Measurable.prodMap
    (Measurable.of_eval fun i ↦
      (measurable_isomAct U).comp (measurable_pi_apply i))
    measurable_id

theorem measurable_negRefMap :
    Measurable (negRefMap (m := m) (s := s)) :=
  Measurable.prodMap measurable_id measurable_id.neg

/-- The `m`-fold product of `stdVecMeasure` is invariant under applying the same
isometry in every factor. -/
theorem hiddenRowsMeasure_map_isomAct
    (U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s)) :
    (hiddenRowsMeasure m s).map (fun g : Fin m → Fin s → ℝ ↦
      fun i ↦ isomAct U (g i)) = hiddenRowsMeasure m s := by
  show (Measure.pi fun _ : Fin m ↦ stdVecMeasure s).map _ =
    Measure.pi fun _ : Fin m ↦ stdVecMeasure s
  rw [Measure.pi_map_pi (f := fun _ : Fin m ↦ isomAct U)
    (hf := fun _ ↦ (measurable_isomAct U).aemeasurable)]
  congr 1
  funext i
  exact stdVecMeasure_map_isomAct U

/-- The sampler source measure is invariant under `stabSourceMap`. -/
theorem measurePreserving_stabSourceMap
    (U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s)) :
    MeasurePreserving (stabSourceMap (m := m) U)
      (samplerSource m s) (samplerSource m s) := by
  refine ⟨measurable_stabSourceMap U, ?_⟩
  have hfm : Measurable (fun g : Fin m → Fin s → ℝ ↦
      fun i ↦ isomAct U (g i)) :=
    Measurable.of_eval fun i ↦
      (measurable_isomAct U).comp (measurable_pi_apply i)
  show ((hiddenRowsMeasure m s).prod (stdVecMeasure (m + 1))).map
      (Prod.map (fun g i ↦ isomAct U (g i)) id) = _
  rw [← Measure.map_prod_map _ _ hfm measurable_id]
  rw [hiddenRowsMeasure_map_isomAct, Measure.map_id]
  rfl

/-- The sampler source measure is invariant under `negRefMap`. -/
theorem measurePreserving_negRefMap :
    MeasurePreserving (negRefMap (m := m) (s := s))
      (samplerSource m s) (samplerSource m s) := by
  refine ⟨measurable_negRefMap, ?_⟩
  show ((hiddenRowsMeasure m s).prod (stdVecMeasure (m + 1))).map
      (Prod.map id fun r : Fin (m + 1) → ℝ ↦ -r) = _
  rw [← Measure.map_prod_map _ _ (f := id) (g := fun r : Fin (m + 1) → ℝ ↦ -r)
      measurable_id measurable_id.neg]
  rw [Measure.map_id, stdVecMeasure_map_neg]
  rfl

/-! ## The sign-decoupling lemma -/

/-- If `T` is a measure-preserving involution-style symmetry under which the
scalar `a` is even (`a ∘ T = a`, valued in `{±1}`) and the vector `G` is odd
(`G ∘ T = -G`), then `a • G` and `G` have the same law.  This is the abstract
content of "the sign is fair": a sign which is independent of the orientation
parity cannot bias the distribution. -/
theorem measure_map_smul_eq_map_of_even_odd
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {a : Ω → ℝ} (ham : Measurable a) (ha : ∀ p, a p = 1 ∨ a p = -1)
    (haT : ∀ p, a (T p) = a p)
    {G : Ω → F} (hGm : Measurable G) (hGT : ∀ p, G (T p) = -G p) :
    μ.map (fun p ↦ a p • G p) = μ.map G := by
  have hsm : Measurable fun p ↦ a p • G p := ham.smul hGm
  have hGm' : Measurable fun p ↦ -G p := hGm.neg
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply hsm hB, Measure.map_apply hGm hB]
  -- split the domain by the sign of `a`
  have hE : MeasurableSet (a ⁻¹' ({-1} : Set ℝ)) :=
    ham (measurableSet_singleton (-1))
  have hsplit : (fun p ↦ a p • G p) ⁻¹' B =
      (G ⁻¹' B ∩ (a ⁻¹' {-1})ᶜ) ∪ ((fun p ↦ -G p) ⁻¹' B ∩ a ⁻¹' {-1}) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_inter_iff,
      Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · intro hb
      rcases ha p with h1 | h1
      · rw [h1, one_smul] at hb
        exact Or.inl ⟨hb, by rw [h1]; norm_num⟩
      · rw [h1, neg_smul, one_smul] at hb
        exact Or.inr ⟨hb, h1⟩
    · rintro (⟨hb, hn⟩ | ⟨hb, hn⟩)
      · have h1 : a p = 1 := by
          rcases ha p with h | h
          · exact h
          · exact absurd h hn
        rwa [h1, one_smul]
      · have h1 : a p = -1 := hn
        rwa [h1, neg_smul, one_smul]
  have hpre : T ⁻¹' ((fun p ↦ -G p) ⁻¹' B ∩ a ⁻¹' {-1}) =
      G ⁻¹' B ∩ a ⁻¹' {-1} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rw [hGT p, neg_neg] at h1
      rw [haT p] at h2
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      rw [hGT p, neg_neg, haT p]
      exact ⟨h1, h2⟩
  have hEm2 : MeasurableSet ((fun p ↦ -G p) ⁻¹' B ∩ a ⁻¹' {-1}) :=
    (hGm' hB).inter hE
  have hkey : μ ((fun p ↦ -G p) ⁻¹' B ∩ a ⁻¹' {-1}) =
      μ (G ⁻¹' B ∩ a ⁻¹' {-1}) := by
    conv_rhs => rw [← hpre]
    rw [← Measure.map_apply hT.measurable hEm2, hT.map_eq]
  have hsplitG : (G ⁻¹' B ∩ (a ⁻¹' {-1})ᶜ) ∪ (G ⁻¹' B ∩ a ⁻¹' {-1}) =
      G ⁻¹' B := by
    ext p
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro (⟨hb, -⟩ | ⟨hb, -⟩) <;> exact hb
    · intro hb
      by_cases hp : p ∈ a ⁻¹' {-1}
      · exact Or.inr ⟨hb, hp⟩
      · exact Or.inl ⟨hb, hp⟩
  have hdisj : Disjoint (G ⁻¹' B ∩ (a ⁻¹' {-1})ᶜ)
      ((fun p ↦ -G p) ⁻¹' B ∩ a ⁻¹' {-1}) := by
    rw [Set.disjoint_left]
    rintro p ⟨-, hn⟩ ⟨-, hp⟩
    exact hn hp
  have hdisj' : Disjoint (G ⁻¹' B ∩ (a ⁻¹' {-1})ᶜ) (G ⁻¹' B ∩ a ⁻¹' {-1}) := by
    rw [Set.disjoint_left]
    rintro p ⟨-, hn⟩ ⟨-, hp⟩
    exact hn hp
  rw [hsplit, measure_union hdisj hEm2, hkey,
    ← measure_union hdisj' ((hGm hB).inter hE), hsplitG]

/-! ## The stabilizer of `range Z` -/

/-- `range Z` viewed as a submodule of `EuclideanSpace ℝ (Fin s)`. -/
noncomputable def rangeZ (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin s)) :=
  (LinearMap.range Z.mulVecLin).map
    (WithLp.linearEquiv 2 ℝ (Fin s → ℝ)).symm.toLinearMap

theorem mem_rangeZ {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    {x : EuclideanSpace ℝ (Fin s)} :
    x ∈ rangeZ Z ↔ ∃ w : Fin (m + 1) → ℝ, WithLp.toLp 2 (Z *ᵥ w) = x := by
  rw [rangeZ, Submodule.mem_map]
  constructor
  · rintro ⟨y, ⟨w, hw⟩, rfl⟩
    exact ⟨w, by rw [← hw, Matrix.mulVecLin_apply]; rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨Z *ᵥ w, ⟨w, Matrix.mulVecLin_apply Z w⟩, rfl⟩

/-- The stabilizer of `range Z`: linear isometries `U` of the ambient Euclidean
space that map `range Z` onto itself and fix `(range Z)ᗮ` pointwise.  These
are exactly the orthogonal transformations of `range Z`; the action on `h`'s
law only uses the range-preserving half. -/
def IsStabilizerZ (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s)) : Prop :=
  (∀ x : EuclideanSpace ℝ (Fin s), U x ∈ rangeZ Z ↔ x ∈ rangeZ Z) ∧
    ∀ x ∈ (rangeZ Z)ᗮ, U x = x

theorem isStabilizerZ_refl (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    IsStabilizerZ Z (LinearIsometryEquiv.refl ℝ _) :=
  ⟨fun _ ↦ Iff.rfl, fun _ _ ↦ rfl⟩

theorem IsStabilizerZ.symm {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    {U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s)}
    (hU : IsStabilizerZ Z U) : IsStabilizerZ Z U.symm := by
  refine ⟨fun x ↦ ?_, fun x hx ↦ ?_⟩
  · have h := hU.1 (U.symm x)
    rw [U.apply_symm_apply] at h
    exact h.symm
  · have h : U x = x := hU.2 x hx
    calc U.symm x = U.symm (U x) := by rw [h]
      _ = x := U.symm_apply_apply x

theorem IsStabilizerZ.trans {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    {U V : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s)}
    (hU : IsStabilizerZ Z U) (hV : IsStabilizerZ Z V) :
    IsStabilizerZ Z (U.trans V) := by
  refine ⟨fun x ↦ ?_, fun x hx ↦ ?_⟩
  · rw [LinearIsometryEquiv.trans_apply, hV.1]
    exact hU.1 x
  · rw [LinearIsometryEquiv.trans_apply, hU.2 x hx, hV.2 x hx]

/-! ## The conjugator -/

/-- The coefficient vector of `U (Z *ᵥ w)` in the `Z`-basis, computed via the
left inverse `(ZᵀZ)⁻¹ Zᵀ`.  No choice is involved, so this is measurable in
`w`. -/
noncomputable def stabConjugate (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s))
    (w : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  ((Zᵀ * Z)⁻¹ * Zᵀ) *ᵥ isomAct U (Z *ᵥ w)

/-- `Zᵀ Z` is invertible when `Z` has linearly independent columns: if
`ZᵀZ *ᵥ v = 0` then `‖Zv‖² = v ⬝ᵥ (ZᵀZ *ᵥ v) = 0`, hence `v = 0`. -/
theorem isUnit_det_transpose_mul_self {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    (hZ : Function.Injective Z.mulVecLin) : IsUnit (Zᵀ * Z).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv
  apply hZ
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_zero]
  have h2 : v ⬝ᵥ ((Zᵀ * Z) *ᵥ v) = 0 := by rw [hAv]; exact dotProduct_zero _
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose] at h2
  exact dotProduct_self_eq_zero.mp h2

/-- The key property: `Z *ᵥ stabConjugate Z U w = isomAct U (Z *ᵥ w)`, i.e.
`stabConjugate` is the `Z`-coordinate conjugate of `U` on `range Z`. -/
theorem stabConjugate_spec {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    (hZ : Function.Injective Z.mulVecLin)
    {U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s)}
    (hU : IsStabilizerZ Z U) (w : Fin (m + 1) → ℝ) :
    Z *ᵥ stabConjugate Z U w = isomAct U (Z *ᵥ w) := by
  -- `isomAct U (Z *ᵥ w)` lies in `range Z`: pick `v` with `Z *ᵥ v = isomAct U (Z *ᵥ w)`.
  have hmem : WithLp.toLp 2 (Z *ᵥ w) ∈ rangeZ Z := mem_rangeZ.mpr ⟨w, rfl⟩
  obtain ⟨v, hv⟩ := mem_rangeZ.mp ((hU.1 _).mpr hmem)
  have hv' : isomAct U (Z *ᵥ w) = Z *ᵥ v := by
    have h2 := congrArg WithLp.ofLp hv
    rw [WithLp.ofLp_toLp] at h2
    show WithLp.ofLp (U (WithLp.toLp 2 (Z *ᵥ w))) = Z *ᵥ v
    exact h2.symm
  have hZZ : IsUnit (Zᵀ * Z).det := isUnit_det_transpose_mul_self hZ
  conv_lhs => rw [stabConjugate, hv']
  calc Z *ᵥ (((Zᵀ * Z)⁻¹ * Zᵀ) *ᵥ (Z *ᵥ v))
      = (Z * ((Zᵀ * Z)⁻¹ * Zᵀ)) *ᵥ (Z *ᵥ v) := Matrix.mulVec_mulVec _ _ _
    _ = ((Z * ((Zᵀ * Z)⁻¹ * Zᵀ)) * Z) *ᵥ v := Matrix.mulVec_mulVec _ _ _
    _ = (Z * ((Zᵀ * Z)⁻¹ * (Zᵀ * Z))) *ᵥ v := by simp [Matrix.mul_assoc]
    _ = Z *ᵥ v := by
        rw [Matrix.nonsing_inv_mul _ hZZ, Matrix.mul_one]
    _ = isomAct U (Z *ᵥ w) := hv'.symm

/-- `stabConjugate` has trivial kernel: `stabConjugate Z U w = 0 → w = 0`. -/
theorem stabConjugate_eq_zero {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    (hZ : Function.Injective Z.mulVecLin)
    {U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s)}
    (hU : IsStabilizerZ Z U) {w : Fin (m + 1) → ℝ}
    (hw : stabConjugate Z U w = 0) : w = 0 := by
  have h := stabConjugate_spec hZ hU w
  rw [hw, Matrix.mulVec_zero] at h
  have h2 : Z *ᵥ w = 0 := by
    have hi := injective_isomAct (k := s) U
    exact hi (h.symm.trans (isomAct_zero (k := s) U).symm)
  apply hZ
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, h2, Matrix.mulVec_zero]

theorem stabConjugate_neg (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s))
    (w : Fin (m + 1) → ℝ) :
    stabConjugate Z U (-w) = -stabConjugate Z U w := by
  unfold stabConjugate
  rw [Matrix.mulVec_neg, isomAct_neg, Matrix.mulVec_neg]

theorem measurable_stabConjugate (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s)) :
    Measurable (stabConjugate Z U) := by
  unfold stabConjugate
  exact measurable_mulVec_const _
    ((measurable_isomAct U).comp (measurable_mulVec_const Z measurable_id))

/-! ## The equivariance sign -/

/-- The sign in the equivariance `h(Ug, r) = ±U h(g, r)`:
`sgn ⟨r, stabConjugate Z U y⟩`, made `{±1}`-valued by convention. -/
noncomputable def stabSign (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s))
    (p : SamplerSpace m s) : ℝ :=
  if 0 < p.2 ⬝ᵥ stabConjugate Z U (completionY Z p.1 p.2) then 1 else -1

theorem stabSign_eq_or (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s))
    (p : SamplerSpace m s) : stabSign Z U p = 1 ∨ stabSign Z U p = -1 := by
  unfold stabSign
  split_ifs <;> simp

theorem measurable_stabSign (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s)) :
    Measurable (stabSign Z (m := m) U) := by
  classical
  have hdot : Measurable fun p : SamplerSpace m s ↦
      p.2 ⬝ᵥ stabConjugate Z U (completionY Z p.1 p.2) := by
    have heq : (fun p : SamplerSpace m s ↦
        p.2 ⬝ᵥ stabConjugate Z U (completionY Z p.1 p.2)) =
        fun p ↦ ∑ j, p.2 j *
          (stabConjugate Z U (completionY Z p.1 p.2)) j :=
      funext fun _ ↦ rfl
    rw [heq]
    exact Finset.measurable_sum _ fun j _ ↦
      ((measurable_pi_apply j).comp measurable_snd).mul
        ((measurable_pi_apply j).comp
          ((measurable_stabConjugate Z U).comp (measurable_completionY Z)))
  have hs : MeasurableSet
      {p : SamplerSpace m s |
        0 < p.2 ⬝ᵥ stabConjugate Z U (completionY Z p.1 p.2)} :=
    hdot measurableSet_Ioi
  unfold stabSign
  exact Measurable.ite hs measurable_const measurable_const

/-! ## Pointwise lemmas on `completionY` -/

/-- Right-inverse multiplication: `Q⁻¹ *ᵥ (Q *ᵥ v) = v` for invertible `Q`. -/
theorem inv_mulVec_mulVec {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : IsUnit Q.det) (v : Fin n → ℝ) :
    Q⁻¹ *ᵥ (Q *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hQ, Matrix.one_mulVec]

/-- Negating the reference row negates `y = Q⁻¹ e_k`. -/
theorem completionY_neg_ref (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (g : Fin m → Fin s → ℝ) (r : Fin (m + 1) → ℝ) :
    completionY Z g (-r) = -completionY Z g r := by
  have hdet : (completionQ Z g (-r)).det = -(completionQ Z g r).det := by
    rw [completionQ_det_eq Z g (-r), completionQ_det_eq Z g r,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp [Pi.neg_apply, mul_neg]
  by_cases h : (completionQ Z g r).det = 0
  · have hQ0 : (completionQ Z g r)⁻¹ = 0 := by
      apply Matrix.nonsing_inv_apply_not_isUnit
      rwa [isUnit_iff_ne_zero, not_not]
    have hQn0 : (completionQ Z g (-r))⁻¹ = 0 := by
      apply Matrix.nonsing_inv_apply_not_isUnit
      rw [isUnit_iff_ne_zero, not_not, hdet]
      exact neg_eq_zero.mpr h
    unfold completionY
    rw [hQ0, hQn0, Matrix.zero_mulVec, neg_zero]
  · have hQ : IsUnit (completionQ Z g r).det := isUnit_iff_ne_zero.mpr h
    have hQn : IsUnit (completionQ Z g (-r)).det :=
      isUnit_iff_ne_zero.mpr (by rw [hdet]; exact neg_ne_zero.mpr h)
    have hmul : (completionQ Z g (-r)) *ᵥ (-completionY Z g r) =
        Pi.single (Fin.last m) 1 := by
      funext i
      induction i using Fin.lastCases with
      | last =>
        rw [Matrix.mulVec_apply]
        have hrow : (completionQ Z g (-r)).row (Fin.last m) = -r :=
          completionQ_last_row Z g (-r)
        rw [hrow, neg_dotProduct_neg, Pi.single_eq_same]
        have h1 := congrFun (completionQ_mulVec_y
          ((Matrix.isUnit_iff_isUnit_det _).mpr hQ)) (Fin.last m)
        rw [Matrix.mulVec_apply] at h1
        have hrow' : (completionQ Z g r).row (Fin.last m) = r :=
          completionQ_last_row Z g r
        rw [hrow', Pi.single_eq_same] at h1
        exact h1
      | cast i' =>
        rw [Matrix.mulVec_apply]
        have hrow : (completionQ Z g (-r)).row (Fin.castSucc i') =
            g i' ᵥ* Z := completionQ_hidden_row Z g (-r) i'
        rw [hrow, dotProduct_neg, Pi.single_eq_of_ne
            (Fin.ne_of_lt (Fin.castSucc_lt_last i')), neg_eq_zero]
        exact hidden_row_annihilates ((Matrix.isUnit_iff_isUnit_det _).mpr hQ) i'
    rw [completionY, ← hmul]
    exact inv_mulVec_mulVec hQn _

/-- `dirRV` is odd in the reference row, pointwise everywhere. -/
theorem dirRV_neg_ref (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (g : Fin m → Fin s → ℝ) (r : Fin (m + 1) → ℝ) :
    dirRV Z (g, -r) = -dirRV Z (g, r) := by
  have hdet : (completionQ Z g (-r)).det = -(completionQ Z g r).det := by
    rw [completionQ_det_eq Z g (-r), completionQ_det_eq Z g r,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp [Pi.neg_apply, mul_neg]
  by_cases h : (completionQ Z g r).det = 0
  · have hn : (completionQ Z g (-r)).det = 0 := by
      rw [hdet]; exact neg_eq_zero.mpr h
    have hnn : (g, -r) ∉ {q : SamplerSpace m s |
        (completionQ Z q.1 q.2).det ≠ 0} := not_not_intro hn
    have hnh : (g, r) ∉ {q : SamplerSpace m s |
        (completionQ Z q.1 q.2).det ≠ 0} := not_not_intro h
    unfold dirRV
    rw [Set.indicator_of_notMem hnn, Set.indicator_of_notMem hnh]
    simp
  · have hz : completionZ Z g (-r) = -completionZ Z g r := by
      unfold completionZ
      rw [completionY_neg_ref, Matrix.mulVec_neg]
    have hH : completionH Z g (-r) = -completionH Z g r := by
      unfold completionH
      rw [hz, sqNorm_neg, smul_neg]
    rw [dirRV_eq_completionH Z (g, -r)
        (by rw [hdet]; exact neg_ne_zero.mpr h), hH,
      ← dirRV_eq_completionH Z (g, r) h]

/-- `stabSign` is even under `negRefMap`. -/
theorem stabSign_negRefMap (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s))
    (p : SamplerSpace m s) :
    stabSign Z U (negRefMap p) = stabSign Z U p := by
  have hnr : negRefMap p = (p.1, -p.2) := rfl
  rw [stabSign, hnr]
  show (if 0 < (-p.2) ⬝ᵥ stabConjugate Z U (completionY Z p.1 (-p.2)) then
      (1 : ℝ) else -1) =
    if 0 < p.2 ⬝ᵥ stabConjugate Z U (completionY Z p.1 p.2) then 1 else -1
  rw [completionY_neg_ref, stabConjugate_neg, neg_dotProduct_neg]

/-! ## The equivariance lemma -/

/-- On the nonsingular event for both `(g, r)` and `(U∘g, r)`, the normalized
direction transforms as `h(Ug, r) = sgn⟨r, Ay⟩ • U h(g, r)` where
`Ay = stabConjugate Z U y` is the `Z`-coefficient vector of `U(Zy)`. -/
theorem dirRV_equivariance (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (hZ : Function.Injective Z.mulVecLin)
    {U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s)}
    (hU : IsStabilizerZ Z U)
    (g : Fin m → Fin s → ℝ) (r : Fin (m + 1) → ℝ)
    (hp : (completionQ Z g r).det ≠ 0)
    (hp' : (completionQ Z (fun i ↦ isomAct U (g i)) r).det ≠ 0) :
    dirRV Z (fun i ↦ isomAct U (g i), r) =
      stabSign Z U (g, r) • isomAct U (dirRV Z (g, r)) := by
  set g' : Fin m → Fin s → ℝ := fun i ↦ isomAct U (g i)
  set Q := completionQ Z g r
  set Q' := completionQ Z g' r
  set y := completionY Z g r
  set Ay := stabConjugate Z U y
  set c := r ⬝ᵥ Ay
  have hQ : IsUnit Q.det := isUnit_iff_ne_zero.mpr hp
  have hQ' : IsUnit Q'.det := isUnit_iff_ne_zero.mpr hp'
  have hQy : Q *ᵥ y = Pi.single (Fin.last m) 1 :=
    completionQ_mulVec_y ((Matrix.isUnit_iff_isUnit_det Q).mpr hQ)
  have hy : y ≠ 0 :=
    completionY_ne_zero ((Matrix.isUnit_iff_isUnit_det Q).mpr hQ)
  have hAy : Ay ≠ 0 := fun hAy ↦ hy (stabConjugate_eq_zero hZ hU hAy)
  have hZAy : Z *ᵥ Ay = isomAct U (Z *ᵥ y) := stabConjugate_spec hZ hU y
  -- `Q' *ᵥ Ay` annihilates hidden rows and has last entry `c`.
  have hQ'mul : Q' *ᵥ Ay = Pi.single (Fin.last m) c := by
    funext i
    induction i using Fin.lastCases with
    | last =>
      rw [Matrix.mulVec_apply]
      have hrow : Q'.row (Fin.last m) = r := completionQ_last_row Z g' r
      rw [hrow, Pi.single_eq_same]
    | cast i' =>
      rw [Matrix.mulVec_apply]
      have hrow : Q'.row (Fin.castSucc i') = g' i' ᵥ* Z :=
        completionQ_hidden_row Z g' r i'
      rw [hrow, ← Matrix.dotProduct_mulVec, hZAy]
      -- `g' i' ⬝ᵥ isomAct U (Z *ᵥ y) = g i' ⬝ᵥ (Z *ᵥ y) = 0`
      show isomAct U (g i') ⬝ᵥ isomAct U (Z *ᵥ y) =
        (Pi.single (Fin.last m) c : Fin (m + 1) → ℝ) (Fin.castSucc i')
      rw [isomAct_dotProduct, Matrix.dotProduct_mulVec]
      have h1 := congrFun hQy (Fin.castSucc i')
      rw [Matrix.mulVec_apply] at h1
      have hrowQ : Q.row (Fin.castSucc i') = g i' ᵥ* Z :=
        completionQ_hidden_row Z g r i'
      rw [hrowQ] at h1
      have hne : Fin.castSucc i' ≠ Fin.last m :=
        Fin.ne_of_lt (Fin.castSucc_lt_last i')
      rw [h1, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne]
  -- hence `c ≠ 0` (else `Ay ∈ ker Q'`)
  have hc : c ≠ 0 := by
    intro hc0
    have h0 : Q' *ᵥ Ay = 0 := by
      rw [hQ'mul]; simp [hc0]
    have hAy' : Ay = Q'⁻¹ *ᵥ (Q' *ᵥ Ay) := by
      rw [inv_mulVec_mulVec hQ']
    rw [h0, Matrix.mulVec_zero] at hAy'
    exact hAy hAy'
  -- `y' = c⁻¹ • Ay` is the unique solution of `Q' *ᵥ · = e_k`
  have h1 : Q' *ᵥ (c⁻¹ • Ay) = Pi.single (Fin.last m) 1 := by
    rw [Matrix.mulVec_smul, hQ'mul]
    funext j
    by_cases hj : j = Fin.last m
    · subst hj
      rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul,
        inv_mul_cancel₀ hc]
    · rw [Pi.smul_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj,
        smul_zero]
  have hy' : completionY Z g' r = c⁻¹ • Ay := by
    unfold completionY
    rw [← h1]
    exact inv_mulVec_mulVec hQ' _
  -- so `z' = c⁻¹ • U z`
  have hz' : completionZ Z g' r = c⁻¹ • isomAct U (Z *ᵥ y) := by
    unfold completionZ
    rw [hy', Matrix.mulVec_smul, hZAy]
  -- norms
  have hsq : sqNorm (completionZ Z g' r) =
      c⁻¹ ^ 2 * sqNorm (Z *ᵥ y) := by
    rw [hz', sqNorm_smul, sqNorm_isomAct]
  have hnorm : Real.sqrt (sqNorm (completionZ Z g' r)) =
      |c|⁻¹ * Real.sqrt (sqNorm (Z *ᵥ y)) := by
    rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_inv]
  -- `h' = (|c| * c⁻¹) • U h`
  have hz : completionZ Z g r = Z *ᵥ y := rfl
  have hH : completionH Z g' r =
      (|c| * c⁻¹) • isomAct U (completionH Z g r) := by
    unfold completionH
    rw [isomAct_smul, smul_smul, hz, hnorm, hz', smul_smul]
    congr 1
    rw [mul_inv, inv_inv]
    ring
  -- `|c| * c⁻¹ = stabSign`
  have hsign : (|c| * c⁻¹) = stabSign Z U (g, r) := by
    have hc' : c ≠ 0 := hc
    unfold stabSign
    show (|c| * c⁻¹) = if 0 < r ⬝ᵥ Ay then (1 : ℝ) else -1
    by_cases hpos : 0 < c
    · rw [ite_eq_left hpos, abs_of_pos hpos, mul_inv_cancel₀ hpos.ne']
    · have hneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hc'
      rw [ite_eq_right (not_lt.mpr hneg.le), abs_of_neg hneg, neg_mul,
        mul_inv_cancel₀ hc']
  rw [dirRV_eq_completionH Z (g', r) hp', dirRV_eq_completionH Z (g, r) hp]
  show completionH Z g' r =
    stabSign Z U (g, r) • isomAct U (completionH Z g r)
  rw [hH, hsign]

/-! ## Almost-everywhere equivariance and the main invariance theorem -/

/-- The equivariance holds `samplerSource`-almost everywhere. -/
theorem ae_dirRV_equivariance {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    (hZ : Function.Injective Z.mulVecLin)
    {U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s)}
    (hU : IsStabilizerZ Z U) :
    (fun p : SamplerSpace m s ↦ WithLp.toLp 2 (dirRV Z (stabSourceMap U p)))
      =ᵐ[samplerSource m s]
    (fun p ↦ stabSign Z U p • U (WithLp.toLp 2 (dirRV Z p))) := by
  have hmeas : MeasurableSet {q : SamplerSpace m s |
      (completionQ Z q.1 q.2).det ≠ 0} :=
    (measurableSet_singleton 0).compl.preimage
      (measurable_matrix_det.comp (measurable_completionQ Z))
  have h2 : ∀ᵐ p ∂(samplerSource m s),
      (completionQ Z (stabSourceMap U p).1 (stabSourceMap U p).2).det ≠ 0 := by
    have h := ae_det_completionQ_ne_zero (m := m) (s := s) (Z := Z) hZ
    rw [← (measurePreserving_stabSourceMap U).map_eq] at h
    rwa [ae_map_iff (measurable_stabSourceMap U).aemeasurable hmeas] at h
  filter_upwards [ae_det_completionQ_ne_zero hZ, h2] with p hp hp'
  have hpt := dirRV_equivariance Z hZ hU p.1 p.2 hp hp'
  calc WithLp.toLp 2 (dirRV Z (stabSourceMap U p))
      = WithLp.toLp 2 (dirRV Z (fun i ↦ isomAct U (p.1 i), p.2)) := rfl
    _ = WithLp.toLp 2
          (stabSign Z U (p.1, p.2) • isomAct U (dirRV Z (p.1, p.2))) :=
        congrArg _ hpt
    _ = stabSign Z U p • U (WithLp.toLp 2 (dirRV Z p)) := by
        rw [WithLp.toLp_smul, toLp_isomAct]

/-- The law of the normalized direction on `EuclideanSpace ℝ (Fin s)`. -/
noncomputable def dirLaw (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    Measure (EuclideanSpace ℝ (Fin s)) :=
  (samplerSource m s).map fun p ↦ WithLp.toLp 2 (dirRV Z p)

instance (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) : IsProbabilityMeasure (dirLaw Z) :=
  inferInstanceAs (IsProbabilityMeasure ((samplerSource m s).map _))

theorem measurable_toLp_dirRV (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    Measurable (fun p : SamplerSpace m s ↦ WithLp.toLp 2 (dirRV Z p)) :=
  (WithLp.measurable_toLp 2 _).comp (measurable_dirRV Z)

/-- **Main theorem**: the law of `dirRV Z` is invariant under the stabilizer
of `range Z` — rotations of `E = range Z` that fix `Eᗮ` — for `Z` of full
column rank.  This is the honest uniformity statement (there is no normalized
sphere measure in Mathlib; invariance under the full stabilizer `O(E)` is the
surrogate). -/
theorem dirRV_law_invariant {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    (hZ : Function.Injective Z.mulVecLin)
    {U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s)}
    (hU : IsStabilizerZ Z U) :
    (dirLaw Z).map (⇑U) = dirLaw Z := by
  have hEm : Measurable (fun p : SamplerSpace m s ↦
      WithLp.toLp 2 (dirRV Z p)) := measurable_toLp_dirRV Z
  have hUm : Measurable (⇑U) := U.continuous.measurable
  -- `G p = U (toLp (dirRV p))` is odd under `negRefMap`; `stabSign` is even.
  have hodd : ∀ p : SamplerSpace m s,
      U (WithLp.toLp 2 (dirRV Z (negRefMap p))) =
        -U (WithLp.toLp 2 (dirRV Z p)) := by
    intro p
    have hnr : negRefMap p = (p.1, -p.2) := rfl
    rw [hnr, dirRV_neg_ref Z p.1 p.2, WithLp.toLp_neg, map_neg]
  have hsign_meas : Measurable (stabSign Z (m := m) U) := measurable_stabSign Z U
  calc (dirLaw Z).map (⇑U)
      = ((samplerSource m s).map
          fun p ↦ WithLp.toLp 2 (dirRV Z p)).map (⇑U) := rfl
    _ = (samplerSource m s).map
          ((⇑U) ∘ fun p ↦ WithLp.toLp 2 (dirRV Z p)) :=
        Measure.map_map hUm hEm
    _ = (samplerSource m s).map
          (fun p ↦ U (WithLp.toLp 2 (dirRV Z p))) := rfl
    _ = (samplerSource m s).map
          (fun p ↦ stabSign Z U p • U (WithLp.toLp 2 (dirRV Z p))) :=
        (measure_map_smul_eq_map_of_even_odd measurePreserving_negRefMap
          hsign_meas (stabSign_eq_or Z U) (stabSign_negRefMap Z U)
          (hUm.comp hEm) hodd).symm
    _ = (samplerSource m s).map
          (fun p ↦ WithLp.toLp 2 (dirRV Z (stabSourceMap U p))) :=
        (Measure.map_congr (ae_dirRV_equivariance hZ hU)).symm
    _ = (samplerSource m s).map
          ((fun p ↦ WithLp.toLp 2 (dirRV Z p)) ∘ stabSourceMap U) := rfl
    _ = ((samplerSource m s).map (stabSourceMap U)).map
          (fun p ↦ WithLp.toLp 2 (dirRV Z p)) :=
        (Measure.map_map hEm (measurable_stabSourceMap U)).symm
    _ = (samplerSource m s).map fun p ↦ WithLp.toLp 2 (dirRV Z p) := by
        rw [(measurePreserving_stabSourceMap U).map_eq]
    _ = dirLaw Z := rfl

/-- **Fair orientation**: the law of `h` is symmetric under `h ↦ -h`, since
negating the reference row negates `h` and preserves the source measure. -/
theorem dirRV_law_neg (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    (dirLaw Z).map (fun x : EuclideanSpace ℝ (Fin s) ↦ -x) = dirLaw Z := by
  have hEm : Measurable (fun p : SamplerSpace m s ↦
      WithLp.toLp 2 (dirRV Z p)) := measurable_toLp_dirRV Z
  have hneg : ∀ p : SamplerSpace m s,
      -WithLp.toLp 2 (dirRV Z p) = WithLp.toLp 2 (dirRV Z (negRefMap p)) := by
    intro p
    have hnr : negRefMap p = (p.1, -p.2) := rfl
    rw [hnr, dirRV_neg_ref Z p.1 p.2, WithLp.toLp_neg]
  calc (dirLaw Z).map (fun x : EuclideanSpace ℝ (Fin s) ↦ -x)
      = ((samplerSource m s).map
          fun p ↦ WithLp.toLp 2 (dirRV Z p)).map (fun x ↦ -x) := rfl
    _ = (samplerSource m s).map
          ((fun x : EuclideanSpace ℝ (Fin s) ↦ -x) ∘
            fun p ↦ WithLp.toLp 2 (dirRV Z p)) :=
        Measure.map_map measurable_neg hEm
    _ = (samplerSource m s).map
          (fun p ↦ -WithLp.toLp 2 (dirRV Z p)) := rfl
    _ = (samplerSource m s).map
          (fun p ↦ WithLp.toLp 2 (dirRV Z (negRefMap p))) :=
        Measure.map_congr (Filter.Eventually.of_forall hneg)
    _ = (samplerSource m s).map
          ((fun p ↦ WithLp.toLp 2 (dirRV Z p)) ∘ negRefMap) := rfl
    _ = ((samplerSource m s).map negRefMap).map
          (fun p ↦ WithLp.toLp 2 (dirRV Z p)) :=
        (Measure.map_map hEm measurable_negRefMap).symm
    _ = (samplerSource m s).map fun p ↦ WithLp.toLp 2 (dirRV Z p) := by
        rw [measurePreserving_negRefMap.map_eq]
    _ = dirLaw Z := rfl

/-- `h` has Euclidean norm `1` almost surely under `dirLaw`. -/
theorem ae_dirLaw_norm {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    (hZ : Function.Injective Z.mulVecLin) :
    ∀ᵐ x ∂(dirLaw Z), ‖x‖ = 1 := by
  have hmeas : MeasurableSet {x : EuclideanSpace ℝ (Fin s) | ‖x‖ = 1} :=
    measurableSet_eq_fun measurable_norm measurable_const
  rw [dirLaw, ae_map_iff (measurable_toLp_dirRV Z).aemeasurable hmeas]
  exact ae_norm_dirRV hZ

/-- `h` lies in `range Z` pointwise (it is `Z *ᵥ (Q⁻¹e_k)` scaled, or `0`). -/
theorem dirRV_mem_rangeZ (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (p : SamplerSpace m s) :
    WithLp.toLp 2 (dirRV Z p) ∈ rangeZ Z := by
  unfold dirRV
  by_cases hp : (completionQ Z p.1 p.2).det ≠ 0
  · rw [Set.indicator_of_mem hp]
    unfold completionH completionZ
    rw [WithLp.toLp_smul]
    exact (rangeZ Z).smul_mem _ (mem_rangeZ.mpr ⟨completionY Z p.1 p.2, rfl⟩)
  · rw [Set.indicator_of_notMem hp]
    exact (rangeZ Z).zero_mem

/-- `h` lies in `range Z` almost surely under `dirLaw`. -/
theorem ae_dirLaw_range (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    ∀ᵐ x ∂(dirLaw Z), x ∈ rangeZ Z := by
  have hmeas : MeasurableSet {x : EuclideanSpace ℝ (Fin s) |
      x ∈ rangeZ Z} :=
    (rangeZ Z).closed_of_finiteDimensional.measurableSet
  rw [dirLaw]
  exact (ae_map_iff (measurable_toLp_dirRV Z).aemeasurable hmeas).mpr
    (Filter.Eventually.of_forall fun p ↦ dirRV_mem_rangeZ Z p)

/-! ## The uniformity statement -/

/-- The statement that `μ` is "the uniform probability measure on the unit
sphere of `range Z`", expressed via its characterization rather than a named
sphere measure (which Mathlib does not provide): `μ` is a probability measure
supported on the unit sphere of `range Z`, invariant under the stabilizer of
`range Z` (i.e. under `O(range Z)`), and symmetric under negation (fair
orientation).  These properties uniquely characterize normalized Haar measure
on the sphere. -/
structure IsUniformSphereLaw (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin s))) : Prop where
  isProb : IsProbabilityMeasure μ
  sphere : ∀ᵐ x ∂μ, ‖x‖ = 1
  mem_range : ∀ᵐ x ∂μ, x ∈ rangeZ Z
  invariant : ∀ U : EuclideanSpace ℝ (Fin s) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s),
    IsStabilizerZ Z U → μ.map (⇑U) = μ
  symmetric : μ.map (fun x ↦ -x) = μ

/-- **Uniformity of the sampler direction** (distributional half of
Theorem 4.1): for `Z` of full column rank, `dirRV Z` is uniform on the unit
sphere of `range Z` with a fair orientation, in the sense of
`IsUniformSphereLaw`. -/
theorem dirRV_law_uniform {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    (hZ : Function.Injective Z.mulVecLin) :
    IsUniformSphereLaw Z (dirLaw Z) where
  isProb := inferInstance
  sphere := ae_dirLaw_norm hZ
  mem_range := ae_dirLaw_range Z
  invariant := fun _ hU ↦ dirRV_law_invariant hZ hU
  symmetric := dirRV_law_neg Z

/-- The placeholder `dirRVUniformStatement` from `GaussianDensity.lean` holds
(the pushforward of a probability measure is a probability measure).  The
non-vacuous content is `dirRV_law_uniform` above. -/
theorem dirRVUniformStatement_holds (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    dirRVUniformStatement Z :=
  ⟨dirLaw Z, inferInstance, rfl⟩

end

end Komlos
