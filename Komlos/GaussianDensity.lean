import Komlos
import Komlos.CompletionSampler
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Instances.Matrix

/-!
# Measure-theoretic model for the completion sampler (Section 4, Theorem 4.1)

This file equips the deterministic construction of `Komlos/CompletionSampler.lean`
with a probability model.  The sampler draws

* `m = k − 1` hidden Gaussian vectors `gᵢ ~ N(0, I_s)` (the "hidden" rows), and
* one independent reference vector `r ~ N(0, I_k)`,

forms `Q = completionQ Z g r` (rows `gᵢᵀZ` plus `r`), and outputs
`h = dirRV Z (g, r) = Zy/‖Zy‖` with `y = Q⁻¹e_k`, defined to be `0` on the
measure-zero event `det Q = 0`.

## Main results

* `stdVecMeasure`, `hiddenRowsMeasure`, `samplerSource`, `samplerMeasure`:
  the coordinate-wise `N(0,1)` product measures and the pushforward law of `Q`.
* `ae_det_mul_ne_zero`: for `A : s×m` with linearly independent columns
  (`A.mulVecLin` injective), a Gaussian `m×s` matrix `G` satisfies
  `det (G * A) ≠ 0` almost surely.
* `ae_det_completionQ_ne_zero` / `ae_isUnit_det_samplerMeasure`:
  for `Z` with linearly independent columns, `Q` is a.s. nonsingular.
* `hiddenRowLaw_eq_map`, `hiddenRowLaw_map_strongDual`,
  `measurePreserving_hiddenRow`: each hidden row `gᵢᵀZ` is a centered Gaussian
  vector with `ZᵀZ` covariance structure.
* `measurable_dirRV`, `ae_sqNorm_dirRV`, `ae_norm_dirRV`:
  the normalized direction is measurable and a.s. a unit vector.
-/

namespace Komlos

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

noncomputable section

variable {s m k : ℕ}

/-! ## The Gaussian product measures -/

/-- The standard Gaussian `N(0, I_k)` on `Fin k → ℝ`, realized as the product of
`k` copies of `gaussianReal 0 1`. -/
noncomputable def stdVecMeasure (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi fun _ : Fin k ↦ gaussianReal 0 1

/-- The law of `m` independent standard Gaussian vectors in `ℝ^s`:
the "hidden" rows of the completion sampler. -/
noncomputable def hiddenRowsMeasure (m s : ℕ) : Measure (Fin m → Fin s → ℝ) :=
  Measure.pi fun _ : Fin m ↦ stdVecMeasure s

/-- The joint law of `(g, r)`: `m` hidden vectors `gᵢ ~ N(0, I_s)` and one
independent reference vector `r ~ N(0, I_{m+1})`.  This is the product measure
on `(Fin m → Fin s → ℝ) × (Fin (m+1) → ℝ)` driving the sampler. -/
noncomputable def samplerSource (m s : ℕ) :
    Measure ((Fin m → Fin s → ℝ) × (Fin (m + 1) → ℝ)) :=
  (hiddenRowsMeasure m s).prod (stdVecMeasure (m + 1))

/-- The law of the completion matrix `Q = completionQ Z g r`: the pushforward of
`samplerSource` under the row map `(g, r) ↦ (g₁ᵀZ, …, g_{k-1}ᵀZ, r)`. -/
noncomputable def samplerMeasure (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    Measure (Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :=
  (samplerSource m s).map fun p ↦ completionQ Z p.1 p.2

instance : IsProbabilityMeasure (stdVecMeasure k) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin k ↦ gaussianReal 0 1))

instance : IsProbabilityMeasure (hiddenRowsMeasure m s) :=
  inferInstanceAs
    (IsProbabilityMeasure (Measure.pi fun _ : Fin m ↦ stdVecMeasure s))

instance : IsProbabilityMeasure (samplerSource m s) :=
  inferInstanceAs
    (IsProbabilityMeasure ((hiddenRowsMeasure m s).prod (stdVecMeasure (m + 1))))

instance (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    IsProbabilityMeasure (samplerMeasure Z) :=
  inferInstanceAs (IsProbabilityMeasure ((samplerSource m s).map _))

/-! ## Measurability -/

theorem measurable_matrix_det :
    Measurable (Matrix.det : Matrix (Fin k) (Fin k) ℝ → ℝ) :=
  continuous_id.matrix_det.measurable

theorem measurable_matrix_adjugate :
    Measurable (Matrix.adjugate : Matrix (Fin k) (Fin k) ℝ →
      Matrix (Fin k) (Fin k) ℝ) :=
  continuous_id.matrix_adjugate.measurable

theorem measurable_matrix_inv :
    Measurable (Inv.inv : Matrix (Fin k) (Fin k) ℝ → Matrix (Fin k) (Fin k) ℝ) := by
  rw [Matrix.measurable_iff]
  intro i j
  have hinv : Measurable (Ring.inverse : ℝ → ℝ) := by
    rw [Ring.inverse_eq_inv']; exact measurable_id.inv
  have : (fun A : Matrix (Fin k) (Fin k) ℝ ↦ A⁻¹ i j) =
      fun A ↦ Ring.inverse (A.det) * A.adjugate i j := by
    funext A; rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  rw [this]
  exact (hinv.comp measurable_matrix_det).mul
    (measurable_matrix_adjugate.eval_matrix)

/-- The sampler map `(g, r) ↦ completionQ Z g r` is measurable. -/
theorem measurable_completionQ (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    Measurable fun p : (Fin m → Fin s → ℝ) × (Fin (m + 1) → ℝ) ↦
      completionQ Z p.1 p.2 := by
  rw [Matrix.measurable_iff]
  intro i j
  induction i using Fin.lastCases with
  | last =>
    simp only [completionQ, Matrix.of_apply, Fin.lastCases_last]
    exact (measurable_pi_apply j).comp measurable_snd
  | cast i' =>
    simp only [completionQ, Matrix.of_apply, Fin.lastCases_castSucc]
    have : (fun p : (Fin m → Fin s → ℝ) × (Fin (m + 1) → ℝ) ↦
        (p.1 i' ᵥ* Z) j) = fun p ↦ ∑ a, p.1 i' a * Z a j :=
      funext fun p ↦ Matrix.vecMul_apply_eq_sum ..
    rw [this]
    exact Finset.measurable_sum _ fun a _ ↦
      (((measurable_pi_apply a).comp (measurable_pi_apply i') :
        Measurable fun g : Fin m → Fin s → ℝ ↦ g i' a).comp measurable_fst).mul
        measurable_const

/-- The hidden-row map `g ↦ g ᵥ* Z` is measurable. -/
theorem measurable_vecMul (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    Measurable fun g : Fin s → ℝ ↦ g ᵥ* Z := by
  refine Measurable.of_eval fun j ↦ ?_
  have : (fun g : Fin s → ℝ ↦ (g ᵥ* Z) j) = fun g ↦ ∑ a, g a * Z a j :=
    funext fun g ↦ Matrix.vecMul_apply_eq_sum ..
  rw [this]
  exact Finset.measurable_sum _ fun a _ ↦ (measurable_pi_apply a).mul measurable_const

/-- `G ↦ G * A` is measurable (entries are polynomials in `G`). -/
theorem measurable_mul_const {t : ℕ} (A : Matrix (Fin s) (Fin t) ℝ) :
    Measurable fun G : Fin m → Fin s → ℝ ↦ Matrix.of G * A := by
  rw [Matrix.measurable_iff]
  intro i l
  have : (fun G : Fin m → Fin s → ℝ ↦ (Matrix.of G * A) i l) =
      fun G ↦ ∑ a, G i a * A a l :=
    funext fun G ↦ Matrix.mul_apply
  rw [this]
  exact Finset.measurable_sum _ fun a _ ↦
    (((measurable_pi_apply a).comp (measurable_pi_apply i) :
      Measurable fun G : Fin m → Fin s → ℝ ↦ G i a)).mul measurable_const

/-- `p ↦ Z *ᵥ v p` is measurable for measurable `v`. -/
theorem measurable_mulVec_const {β : Type*} [MeasurableSpace β] {t : ℕ}
    (Z : Matrix (Fin s) (Fin t) ℝ) {v : β → Fin t → ℝ} (hv : Measurable v) :
    Measurable fun b ↦ Z *ᵥ v b := by
  refine Measurable.of_eval fun i ↦ ?_
  have : (fun b ↦ (Z *ᵥ v b) i) = fun b ↦ ∑ j, Z i j * v b j :=
    funext fun b ↦ Matrix.mulVec_apply_eq_sum ..
  rw [this]
  exact Finset.measurable_sum _ fun j _ ↦
    measurable_const.mul ((measurable_pi_apply j).comp hv)

/-- `p ↦ completionY Z g r = Q⁻¹ e_k` is measurable. -/
theorem measurable_completionY (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    Measurable fun p : (Fin m → Fin s → ℝ) × (Fin (m + 1) → ℝ) ↦
      completionY Z p.1 p.2 := by
  refine Measurable.of_eval fun i ↦ ?_
  have : (fun p : (Fin m → Fin s → ℝ) × (Fin (m + 1) → ℝ) ↦
      completionY Z p.1 p.2 i) =
      fun p ↦ ∑ j, (completionQ Z p.1 p.2)⁻¹ i j *
        (Pi.single (Fin.last m) (1 : ℝ) : Fin (m + 1) → ℝ) j :=
    funext fun p ↦ Matrix.mulVec_apply_eq_sum ..
  rw [this]
  exact Finset.measurable_sum _ fun j _ ↦
    ((measurable_matrix_inv.comp (measurable_completionQ Z)).eval_matrix).mul
      measurable_const

/-- `p ↦ completionZ Z g r = Zy` is measurable. -/
theorem measurable_completionZ (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    Measurable fun p : (Fin m → Fin s → ℝ) × (Fin (m + 1) → ℝ) ↦
      completionZ Z p.1 p.2 :=
  measurable_mulVec_const Z (measurable_completionY Z)

/-- `p ↦ completionH Z g r = z/‖z‖` is measurable. -/
theorem measurable_completionH (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    Measurable fun p : (Fin m → Fin s → ℝ) × (Fin (m + 1) → ℝ) ↦
      completionH Z p.1 p.2 := by
  refine Measurable.of_eval fun i ↦ ?_
  have hz := measurable_completionZ Z (s := s) (m := m)
  have hnorm : Measurable fun p : (Fin m → Fin s → ℝ) × (Fin (m + 1) → ℝ) ↦
      sqNorm (completionZ Z p.1 p.2) :=
    Finset.measurable_sum _ fun j _ ↦
      ((measurable_pi_apply j).comp hz).pow_const 2
  have : (fun p : (Fin m → Fin s → ℝ) × (Fin (m + 1) → ℝ) ↦
      completionH Z p.1 p.2 i) =
      fun p ↦ (Real.sqrt (sqNorm (completionZ Z p.1 p.2)))⁻¹ *
        (completionZ Z p.1 p.2) i := by
    funext p
    simp only [completionH, Pi.smul_apply, smul_eq_mul]
  rw [this]
  exact ((Real.continuous_sqrt.measurable.comp hnorm).inv).mul
    ((measurable_pi_apply i).comp hz)

/-! ## The standard Gaussian on `EuclideanSpace` and linear pushforwards -/

/-- `stdVecMeasure` is the `ofLp`-pushforward of Mathlib's `stdGaussian` on the
Euclidean space. -/
theorem stdVecMeasure_eq_map (k : ℕ) :
    stdVecMeasure k =
      (stdGaussian (EuclideanSpace ℝ (Fin k))).map
        (WithLp.ofLp : EuclideanSpace ℝ (Fin k) → Fin k → ℝ) := by
  have hid : (WithLp.ofLp : EuclideanSpace ℝ (Fin k) → Fin k → ℝ) ∘
      WithLp.toLp 2 = id :=
    funext fun _ ↦ rfl
  rw [stdVecMeasure, ← map_pi_eq_stdGaussian (ι := Fin k),
      Measure.map_map (WithLp.measurable_ofLp 2 _) (WithLp.measurable_toLp 2 _),
      hid, Measure.map_id]

/-- For `w ≠ 0`, the coordinate hyperplane `{x | ∑ wₐ xₐ = 0}` has measure zero
under `stdVecMeasure`: the linear functional is a nonzero-variance Gaussian. -/
theorem stdVecMeasure_ae_linear_ne_zero {w : Fin k → ℝ} (hw : w ≠ 0) :
    ∀ᵐ x ∂(stdVecMeasure k), (∑ a, w a * x a) ≠ 0 := by
  set wE : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 w
  have hTmeas : Measurable fun x : Fin k → ℝ ↦ ∑ a, w a * x a :=
    Finset.measurable_sum _ fun a _ ↦ (measurable_pi_apply a).const_mul _
  have hcomp : ((fun x : Fin k → ℝ ↦ ∑ a, w a * x a) ∘
      (WithLp.ofLp : EuclideanSpace ℝ (Fin k) → Fin k → ℝ)) =
      ⇑(innerSL ℝ wE) := by
    funext y
    rw [innerSL_apply_apply]
    simp only [Function.comp_apply, PiLp.inner_apply, RCLike.inner_apply',
      starRingEnd_apply, star_trivial]
    have hwE' : WithLp.ofLp wE = w := rfl
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [hwE']
  have hmap : (stdVecMeasure k).map (fun x ↦ ∑ a, w a * x a) =
      gaussianReal 0 ((‖wE‖ ^ 2).toNNReal) := by
    rw [stdVecMeasure_eq_map,
        Measure.map_map hTmeas (WithLp.measurable_ofLp 2 _), hcomp,
        IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
        variance_dual_stdGaussian, innerSL_apply_norm]
  have hwE : wE ≠ 0 := by
    intro h
    exact hw (congrArg WithLp.ofLp h)
  have hv : (‖wE‖ ^ 2).toNNReal ≠ 0 :=
    (Real.toNNReal_pos.mpr (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hwE))).ne'
  rw [ae_iff]
  have hset : {x : Fin k → ℝ | ¬(∑ a, w a * x a) ≠ 0} =
      (fun x ↦ ∑ a, w a * x a) ⁻¹' {0} := by
    ext x; simp
  rw [hset, ← Measure.map_apply hTmeas (measurableSet_singleton 0), hmap]
  exact gaussianReal_absolutelyContinuous 0 hv Real.volume_singleton

/-! ## Algebra: minors through column deletions -/

/-- Deleting column `j` of `Z` and multiplying by `v` equals padding `v` with a
zero at `j` and multiplying by `Z`. -/
theorem mulVec_submatrix_succAbove (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (j : Fin (m + 1)) (v : Fin m → ℝ) :
    (Z.submatrix id j.succAbove) *ᵥ v =
      Z *ᵥ (Fin.insertNth (α := fun _ : Fin (m + 1) ↦ ℝ) j 0 v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, submatrix_apply, id_eq]
  rw [j.sum_univ_succAbove
    (fun a ↦ Z i a * Fin.insertNth (α := fun _ : Fin (m + 1) ↦ ℝ) j 0 v a)]
  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/-- If `Z` has linearly independent columns, so does `Z` with column `j`
removed. -/
theorem injective_mulVecLin_submatrix {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    (hZ : Function.Injective Z.mulVecLin) (j : Fin (m + 1)) :
    Function.Injective (Z.submatrix id j.succAbove).mulVecLin := by
  intro v w hvw
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, mulVec_submatrix_succAbove,
    mulVec_submatrix_succAbove] at hvw
  have h : Fin.insertNth (α := fun _ : Fin (m + 1) ↦ ℝ) j 0 v =
      Fin.insertNth (α := fun _ : Fin (m + 1) ↦ ℝ) j 0 w := by
    apply hZ
    rwa [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
  funext l
  have hl := congrFun h (j.succAbove l)
  rwa [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove] at hl

/-- An injective `mulVecLin` maps nonzero vectors to nonzero vectors. -/
theorem mulVec_ne_zero_of_injective {t : ℕ} {A : Matrix (Fin s) (Fin t) ℝ}
    (hA : Function.Injective A.mulVecLin) {v : Fin t → ℝ} (hv : v ≠ 0) :
    A *ᵥ v ≠ 0 := by
  intro h
  apply hv
  apply hA
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, h, Matrix.mulVec_zero]

/-! ## Gaussian matrices are a.s. nonsingular on column-independent maps -/

/-- For `A : s×m` with linearly independent columns, the `m×m` matrix `G * A`
with `G` an `m×s` standard Gaussian is a.s. nonsingular.

This is the key "generically invertible" input.  The proof expands `det (G * A)`
along the last row: it is a linear functional of the last Gaussian row `x`
whose coefficients are `± det (G' * A_{-l})` for the row-truncated `G'` and the
column-deleted `A_{-l}`.  Inductively, every minor is a.s. nonzero, so `det` is
a nondegenerate linear functional of `x`, whose zero set is a hyperplane. -/
theorem ae_det_mul_ne_zero {s : ℕ} :
    ∀ {m : ℕ} (A : Matrix (Fin s) (Fin m) ℝ), Function.Injective A.mulVecLin →
      ∀ᵐ G ∂(hiddenRowsMeasure m s), (Matrix.of G * A).det ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro A _
    exact Filter.Eventually.of_forall fun G ↦ by
      rw [Matrix.det_isEmpty]; exact one_ne_zero
  | succ m ih =>
    intro A hA
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ Fin s → ℝ)
      (Fin.last m) with he
    have hmp : MeasurePreserving e
        (Measure.pi fun _ : Fin (m + 1) ↦ stdVecMeasure s)
        ((stdVecMeasure s).prod
          (Measure.pi fun _ : Fin m ↦ stdVecMeasure s)) := by
      rw [he]; exact measurePreserving_piFinSuccAbove _ _
    -- the det-nonvanishing set is measurable
    have hGA : Measurable fun G : Fin (m + 1) → Fin s → ℝ ↦
        (Matrix.of G * A).det :=
      measurable_matrix_det.comp (measurable_mul_const A)
    have hS : MeasurableSet {G : Fin (m + 1) → Fin s → ℝ |
        (Matrix.of G * A).det ≠ 0} :=
      (measurableSet_singleton 0).compl.preimage hGA
    have hS' : MeasurableSet {p : (Fin s → ℝ) × (Fin m → Fin s → ℝ) |
        (Matrix.of (e.symm p : Fin (m + 1) → Fin s → ℝ) * A).det ≠ 0} :=
      hS.preimage (e.symm.measurable)
    -- pointwise computations of `e.symm` at the last and cast rows
    have hlast : ∀ (x : Fin s → ℝ) (G' : Fin m → Fin s → ℝ) (a : Fin s),
        e.symm (x, G') (Fin.last m) a = x a := by
      intro x G' a
      simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Equiv.coe_fn_mk, Fin.insertNth_apply_same]
    have hcast : ∀ (x : Fin s → ℝ) (G' : Fin m → Fin s → ℝ) (i : Fin m) (a : Fin s),
        e.symm (x, G') (Fin.castSucc i) a = G' i a := by
      intro x G' i a
      conv_lhs => rw [← Fin.succAbove_last_apply]
      simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Equiv.coe_fn_mk, Fin.insertNth_apply_succAbove]
    suffices h' : ∀ᵐ p ∂(stdVecMeasure s).prod (hiddenRowsMeasure m s),
        (Matrix.of (e.symm p : Fin (m + 1) → Fin s → ℝ) * A).det ≠ 0 by
      have hmapm : (Measure.pi fun _ : Fin m ↦ stdVecMeasure s) =
          hiddenRowsMeasure m s := rfl
      rw [hmapm] at hmp
      have hpi : hiddenRowsMeasure (m + 1) s =
          Measure.pi fun _ : Fin (m + 1) ↦ stdVecMeasure s := rfl
      rw [hpi, ← hmp.symm.map_eq,
          ae_map_iff e.symm.measurable.aemeasurable hS]
      exact h'
    rw [Measure.ae_prod_iff_ae_ae hS', Measure.ae_ae_comm hS']
    -- for a.e. truncated `G'`, all column minors are nonsingular
    have hminors : ∀ᵐ G' ∂(hiddenRowsMeasure m s),
        ∀ l : Fin (m + 1),
          (Matrix.of G' * A.submatrix id l.succAbove).det ≠ 0 := by
      rw [ae_all_iff]
      intro l
      exact ih _ (injective_mulVecLin_submatrix hA l)
    filter_upwards [hminors] with G' hG'
    -- express det as a linear functional of the last row `x`
    have hd : ∀ x : Fin s → ℝ,
        (Matrix.of (e.symm (x, G') : Fin (m + 1) → Fin s → ℝ) * A).det =
          ∑ a, (A *ᵥ (fun l : Fin (m + 1) ↦
            (-1 : ℝ) ^ (m + (l : ℕ)) *
              (Matrix.of G' * A.submatrix id l.succAbove).det)) a * x a := by
      intro x
      rw [Matrix.det_succ_row _ (Fin.last m), Fin.val_last]
      have hminor : ∀ l : Fin (m + 1),
          (Matrix.of (e.symm (x, G') : Fin (m + 1) → Fin s → ℝ) * A).submatrix
              (Fin.last m).succAbove l.succAbove =
            Matrix.of G' * A.submatrix id l.succAbove := by
        intro l
        rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id]
        congr 1
        ext i a
        simp only [Matrix.submatrix_apply, Matrix.of_apply, id_eq,
          Fin.succAbove_last_apply]
        exact hcast x G' i a
      have hrow : ∀ l : Fin (m + 1),
          (Matrix.of (e.symm (x, G') : Fin (m + 1) → Fin s → ℝ) * A)
              (Fin.last m) l = ∑ a, x a * A a l := by
        intro l
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        simp only [Matrix.of_apply]
        exact congrArg (· * A a l) (hlast x G' a)
      have hsum : ∀ l : Fin (m + 1),
          (-1 : ℝ) ^ (m + (l : ℕ)) *
              (Matrix.of (e.symm (x, G') : Fin (m + 1) → Fin s → ℝ) * A)
                (Fin.last m) l *
            ((Matrix.of (e.symm (x, G') : Fin (m + 1) → Fin s → ℝ) * A).submatrix
              (Fin.last m).succAbove l.succAbove).det =
            ∑ a : Fin s, ((-1 : ℝ) ^ (m + (l : ℕ)) *
              (Matrix.of G' * A.submatrix id l.succAbove).det * A a l) * x a := by
        intro l
        rw [hrow l, hminor l, mul_assoc, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ ↦ by ring
      calc ∑ l : Fin (m + 1), (-1 : ℝ) ^ (m + (l : ℕ)) *
              (Matrix.of (e.symm (x, G') : Fin (m + 1) → Fin s → ℝ) * A)
                (Fin.last m) l *
            ((Matrix.of (e.symm (x, G') : Fin (m + 1) → Fin s → ℝ) * A).submatrix
              (Fin.last m).succAbove l.succAbove).det
          = ∑ l : Fin (m + 1), ∑ a : Fin s, ((-1 : ℝ) ^ (m + (l : ℕ)) *
              (Matrix.of G' * A.submatrix id l.succAbove).det * A a l) * x a :=
            Finset.sum_congr rfl fun l _ ↦ hsum l
        _ = ∑ a : Fin s, ∑ l : Fin (m + 1), ((-1 : ℝ) ^ (m + (l : ℕ)) *
              (Matrix.of G' * A.submatrix id l.succAbove).det * A a l) * x a :=
            Finset.sum_comm
        _ = ∑ a : Fin s, (A *ᵥ (fun l : Fin (m + 1) ↦
              (-1 : ℝ) ^ (m + (l : ℕ)) *
                (Matrix.of G' * A.submatrix id l.succAbove).det)) a * x a := by
            refine Finset.sum_congr rfl fun a _ ↦ ?_
            rw [Matrix.mulVec_apply_eq_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun l _ ↦ ?_
            show ((-1 : ℝ) ^ (m + (l : ℕ)) *
                (Matrix.of G' * A.submatrix id l.succAbove).det * A a l) * x a =
              A a l * ((-1 : ℝ) ^ (m + (l : ℕ)) *
                (Matrix.of G' * A.submatrix id l.succAbove).det) * x a
            ring
    -- the coefficient vector `w = A *ᵥ d` is nonzero since `d ≠ 0` and `A` has
    -- independent columns
    have hd0 : (fun l : Fin (m + 1) ↦ (-1 : ℝ) ^ (m + (l : ℕ)) *
        (Matrix.of G' * A.submatrix id l.succAbove).det) ≠ 0 := by
      rw [Function.ne_iff]
      refine ⟨0, ?_⟩
      have h0 := hG' 0
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) h0
    have hw : (A *ᵥ (fun l : Fin (m + 1) ↦ (-1 : ℝ) ^ (m + (l : ℕ)) *
        (Matrix.of G' * A.submatrix id l.succAbove).det)) ≠ 0 :=
      mulVec_ne_zero_of_injective hA hd0
    filter_upwards [stdVecMeasure_ae_linear_ne_zero hw] with x hx
    rwa [hd x]

/-! ## The last-row expansion of `det (completionQ Z g r)` -/

/-- The `m×m` minors of `completionQ` along its last row are `g * Z_{-j}`:
the hidden-row matrix times `Z` with column `j` deleted. -/
theorem completionQ_submatrix_castSucc (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (g : Fin m → Fin s → ℝ) (r : Fin (m + 1) → ℝ) {t : ℕ} (e : Fin t → Fin (m + 1)) :
    (completionQ Z g r).submatrix Fin.castSucc e =
      Matrix.of g * Z.submatrix id e := by
  ext i l
  rw [Matrix.submatrix_apply]
  have hrow := completionQ_hidden_row Z g r i
  rw [show (completionQ Z g r) (Fin.castSucc i) (e l) =
      (g i ᵥ* Z) (e l) from congrFun hrow (e l)]
  rfl

/-- Laplace expansion of `det Q` along the last row: `det Q` is the linear form
`r ↦ ∑ⱼ cⱼ rⱼ` with cofactor coefficients `cⱼ = (-1)^{m+j} det (g · Z_{-j})`. -/
theorem completionQ_det_eq (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (g : Fin m → Fin s → ℝ) (r : Fin (m + 1) → ℝ) :
    (completionQ Z g r).det =
      ∑ j : Fin (m + 1), ((-1 : ℝ) ^ (m + (j : ℕ)) *
        (Matrix.of g * Z.submatrix id j.succAbove).det) * r j := by
  rw [Matrix.det_succ_row _ (Fin.last m)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Fin.val_last, Fin.succAbove_last, completionQ_submatrix_castSucc]
  have hrl : (completionQ Z g r) (Fin.last m) j = r j :=
    congrFun (completionQ_last_row Z g r) j
  rw [hrl]
  ring

/-! ## `Q` is a.s. nonsingular -/

/-- For `Z` with linearly independent columns (i.e. `Z` a basis matrix of the
subspace `E`), the completion matrix `Q` is a.s. nonsingular: conditioned on
the hidden rows `g`, `det Q` is a linear functional of `r` whose coefficients
are the column minors `±det(g · Z_{-j})`, which are a.s. nonzero. -/
theorem ae_det_completionQ_ne_zero {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    (hZ : Function.Injective Z.mulVecLin) :
    ∀ᵐ p ∂(samplerSource m s), (completionQ Z p.1 p.2).det ≠ 0 := by
  have hQ : MeasurableSet {p : (Fin m → Fin s → ℝ) × (Fin (m + 1) → ℝ) |
      (completionQ Z p.1 p.2).det ≠ 0} :=
    (measurableSet_singleton 0).compl.preimage
      (measurable_matrix_det.comp (measurable_completionQ Z))
  unfold samplerSource
  rw [Measure.ae_prod_iff_ae_ae hQ]
  -- a.e. `g` has all column minors nonzero
  have hminors : ∀ᵐ g ∂(hiddenRowsMeasure m s),
      ∀ j : Fin (m + 1), (Matrix.of g * Z.submatrix id j.succAbove).det ≠ 0 := by
    rw [ae_all_iff]
    intro j
    exact ae_det_mul_ne_zero _ (injective_mulVecLin_submatrix hZ j)
  filter_upwards [hminors] with g hg
  -- for such `g`, `det Q` is a nonzero linear functional of `r`
  have hwne : (fun j : Fin (m + 1) ↦ (-1 : ℝ) ^ (m + (j : ℕ)) *
      (Matrix.of g * Z.submatrix id j.succAbove).det) ≠ 0 := by
    rw [Function.ne_iff]
    exact ⟨0, mul_ne_zero (pow_ne_zero _ (by norm_num)) (hg 0)⟩
  filter_upwards [stdVecMeasure_ae_linear_ne_zero hwne] with r hr
  rwa [completionQ_det_eq]

/-- The pushforward form: `Q` is a.s. a unit under `samplerMeasure Z`. -/
theorem ae_isUnit_det_samplerMeasure {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    (hZ : Function.Injective Z.mulVecLin) :
    ∀ᵐ Q ∂(samplerMeasure Z), IsUnit Q.det := by
  have hQ : MeasurableSet {Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ |
      IsUnit Q.det} := by
    have : {Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ | IsUnit Q.det} =
        {Q | Q.det ≠ 0} := by
      ext Q; simp [isUnit_iff_ne_zero]
    rw [this]
    exact (measurableSet_singleton 0).compl.preimage measurable_matrix_det
  rw [samplerMeasure, ae_map_iff (measurable_completionQ Z).aemeasurable hQ]
  filter_upwards [ae_det_completionQ_ne_zero hZ] with p hp
  exact isUnit_iff_ne_zero.mpr hp

/-! ## The law of a hidden row -/

/-- The row map `g ↦ g ᵥ* Z = Zᵀ *ᵥ g`, as a continuous linear map. -/
noncomputable def vecMulCLM (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    (Fin s → ℝ) →L[ℝ] (Fin (m + 1) → ℝ) :=
  { toLinearMap := Zᵀ.mulVecLin,
    cont := Zᵀ.mulVecLin.continuous_of_finiteDimensional }

theorem vecMulCLM_apply (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) (g : Fin s → ℝ) :
    vecMulCLM Z g = g ᵥ* Z := by
  show Zᵀ *ᵥ g = g ᵥ* Z
  conv_rhs => rw [← Matrix.transpose_transpose Z]
  rw [Matrix.vecMul_transpose]

/-- The law of a hidden row `gᵢᵀZ` for `gᵢ ~ N(0, I_s)`: a centered Gaussian on
`Fin (m+1) → ℝ` with `ZᵀZ` covariance structure. -/
noncomputable def hiddenRowLaw (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    Measure (Fin (m + 1) → ℝ) :=
  (stdVecMeasure s).map fun g ↦ g ᵥ* Z

/-- `hiddenRowLaw` is the pushforward of the Euclidean-space standard Gaussian
by the continuous linear map `x ↦ Zᵀx`. -/
theorem hiddenRowLaw_eq_map (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    hiddenRowLaw Z = (stdGaussian (EuclideanSpace ℝ (Fin s))).map
      (vecMulCLM Z ∘L
        (EuclideanSpace.equiv (Fin s) ℝ :
          EuclideanSpace ℝ (Fin s) →L[ℝ] (Fin s → ℝ))) := by
  unfold hiddenRowLaw
  rw [stdVecMeasure_eq_map,
      Measure.map_map (measurable_vecMul Z) (WithLp.measurable_ofLp 2 _)]
  congr 1
  funext x
  show ((fun g ↦ g ᵥ* Z) ∘ (WithLp.ofLp :
    EuclideanSpace ℝ (Fin s) → Fin s → ℝ)) x =
      (vecMulCLM Z ∘L (EuclideanSpace.equiv (Fin s) ℝ).toContinuousLinearMap) x
  simp only [Function.comp_apply, ContinuousLinearMap.coe_comp,
    ContinuousLinearEquiv.coe_coe, PiLp.coe_continuousLinearEquiv]
  rw [vecMulCLM_apply]

instance (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) : IsGaussian (hiddenRowLaw Z) := by
  rw [hiddenRowLaw_eq_map]; infer_instance

/-- Each hidden row is *centered*: `∫ h ∂(hiddenRowLaw Z) = 0`. -/
theorem hiddenRowLaw_integral_zero (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    ∫ x, x ∂hiddenRowLaw Z = 0 := by
  rw [hiddenRowLaw_eq_map,
      ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_stdGaussian, map_zero]

/-- Marginal consistency: the `i`-th hidden row of the sampler has law
`hiddenRowLaw Z`. -/
theorem measurePreserving_hiddenRow (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (i : Fin m) :
    MeasurePreserving (fun p : (Fin m → Fin s → ℝ) × (Fin (m + 1) → ℝ) ↦
      p.1 i ᵥ* Z) (samplerSource m s) (hiddenRowLaw Z) := by
  have h₁ : MeasurePreserving Prod.fst (samplerSource m s)
      (hiddenRowsMeasure m s) :=
    measurePreserving_fst
  have h₂ : MeasurePreserving (fun g : Fin m → Fin s → ℝ ↦ g i)
      (hiddenRowsMeasure m s) (stdVecMeasure s) :=
    measurePreserving_eval _ i
  have h₃ : MeasurePreserving (fun g : Fin s → ℝ ↦ g ᵥ* Z)
      (stdVecMeasure s) (hiddenRowLaw Z) :=
    ⟨measurable_vecMul Z, rfl⟩
  have hc := h₃.comp (h₂.comp h₁)
  exact hc

/-- Pushforward of `hiddenRowLaw` by a dual vector `L`: a real Gaussian with
mean `0` and variance `‖L ∘ vecMul‖²` — this encodes the `ZᵀZ` covariance
structure of the hidden rows. -/
theorem hiddenRowLaw_map_strongDual (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (L : StrongDual ℝ (Fin (m + 1) → ℝ)) :
    (hiddenRowLaw Z).map L =
      gaussianReal 0
        (‖L.comp (vecMulCLM Z ∘L
          (EuclideanSpace.equiv (Fin s) ℝ :
            EuclideanSpace ℝ (Fin s) →L[ℝ] (Fin s → ℝ)))‖ ^ 2).toNNReal := by
  rw [hiddenRowLaw_eq_map,
      Measure.map_map L.measurable
        (vecMulCLM Z ∘L
          (EuclideanSpace.equiv (Fin s) ℝ).toContinuousLinearMap).measurable,
      ← ContinuousLinearMap.coe_comp, IsGaussian.map_eq_gaussianReal,
      integral_strongDual_stdGaussian, variance_dual_stdGaussian]

/-! ## The normalized direction as a random variable -/

/-- The normalized direction random variable: `completionH Z g r` on the a.s.
event `det Q ≠ 0`, and `0` on the complementary null set.  `Set.indicator` is
used to sidestep decidability of real equality. -/
noncomputable def dirRV (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (p : (Fin m → Fin s → ℝ) × (Fin (m + 1) → ℝ)) : Fin s → ℝ :=
  {q | (completionQ Z q.1 q.2).det ≠ 0}.indicator
    (fun q ↦ completionH Z q.1 q.2) p

theorem measurable_dirRV (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) :
    Measurable (dirRV Z) := by
  unfold dirRV
  exact Measurable.indicator (measurable_completionH Z)
    ((measurableSet_singleton 0).compl.preimage
      (measurable_matrix_det.comp (measurable_completionQ Z)))

/-- On the event `det Q ≠ 0`, `dirRV` agrees with `completionH`. -/
theorem dirRV_eq_completionH (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (p : (Fin m → Fin s → ℝ) × (Fin (m + 1) → ℝ))
    (hp : (completionQ Z p.1 p.2).det ≠ 0) :
    dirRV Z p = completionH Z p.1 p.2 := by
  rw [dirRV]
  exact Set.indicator_of_mem hp _

/-- Unconditionally (given the rank hypothesis on `Z`), `dirRV` is either a unit
vector or lies on the singular event. -/
theorem ae_sqNorm_dirRV_or {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    (hZ : Function.Injective Z.mulVecLin) :
    ∀ᵐ p ∂(samplerSource m s),
      sqNorm (dirRV Z p) = 1 ∨ (completionQ Z p.1 p.2).det = 0 := by
  refine Filter.Eventually.of_forall fun p ↦ ?_
  by_cases hp : (completionQ Z p.1 p.2).det = 0
  · exact Or.inr hp
  · left
    rw [dirRV_eq_completionH Z p hp]
    apply completionH_unit
    have hQ : IsUnit (completionQ Z p.1 p.2) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hp)
    exact mulVec_ne_zero_of_injective hZ (completionY_ne_zero hQ)

/-- The sampler outputs a unit vector almost surely (for `Z` of full column
rank). -/
theorem ae_sqNorm_dirRV {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    (hZ : Function.Injective Z.mulVecLin) :
    ∀ᵐ p ∂(samplerSource m s), sqNorm (dirRV Z p) = 1 := by
  filter_upwards [ae_sqNorm_dirRV_or hZ, ae_det_completionQ_ne_zero hZ]
    with p hp hdet
  exact hp.resolve_right hdet

/-- `sqNorm x = ∑ xⱼ²` is the squared Euclidean norm. -/
theorem sqNorm_eq_norm_sq (v : Fin s → ℝ) :
    (‖WithLp.toLp 2 v‖ : ℝ) ^ 2 = sqNorm v := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold sqNorm
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp

/-- The sampler's direction has Euclidean norm `1` almost surely. -/
theorem ae_norm_dirRV {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    (hZ : Function.Injective Z.mulVecLin) :
    ∀ᵐ p ∂(samplerSource m s),
      ‖(WithLp.toLp 2 (dirRV Z p) : EuclideanSpace ℝ (Fin s))‖ = 1 := by
  filter_upwards [ae_sqNorm_dirRV hZ] with p hp
  have h1 : ‖(WithLp.toLp 2 (dirRV Z p) : EuclideanSpace ℝ (Fin s))‖ =
      Real.sqrt (sqNorm (dirRV Z p)) := by
    rw [← Real.sqrt_sq (norm_nonneg _), sqNorm_eq_norm_sq]
  rw [h1, hp, Real.sqrt_one]

end

/-! ## Unproved claims

The paper's Theorem 4.1 additionally asserts that `dirRV Z` is *uniformly*
distributed on the unit sphere of `E = range Z` with a fair orientation.  That
statement — equality of the `samplerSource`-pushforward of `dirRV` with the
normalized uniform sphere measure — is recorded below as a `Prop`-valued
definition, pending a formalization of the uniform sphere measure and the
rotational-invariance argument of Appendix D. -/

/-- The statement (not proved here) that the normalized direction is uniform on
the unit sphere: the pushforward of `samplerSource` by `toLp ∘ dirRV` equals
some probability measure on `EuclideanSpace ℝ (Fin s)` (candidate: normalized
Hausdorff measure on the unit sphere).  This `Prop` serves as a placeholder for
the distributional half of Theorem 4.1. -/
def dirRVUniformStatement (Z : Matrix (Fin s) (Fin (m + 1)) ℝ) : Prop :=
  ∃ μ : Measure (EuclideanSpace ℝ (Fin s)), IsProbabilityMeasure μ ∧
    (samplerSource m s).map (fun p ↦ WithLp.toLp 2 (dirRV Z p)) = μ

end Komlos
