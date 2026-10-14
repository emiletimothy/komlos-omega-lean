import Komlos
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Mul

/-!
# The adaptive completion sampler (Section 4)

The paper's direction sampler works in coefficient coordinates through
a basis `Z ∈ ℝ^{s×k}` with `range Z = E`.  It forms a matrix
`Q ∈ ℝ^{k×k}` whose first `k − 1` ("hidden") rows are `gᵢᵀ Z` for
fresh `gᵢ ~ N(0, I_s)` and whose last ("reference") row `r` is
independent.  For invertible `Q`, `y = Q⁻¹e_k` annihilates the hidden
rows, and the physical direction is

  `z = Z y`,   `h = z / ‖z‖₂`,   `c = Zᵀ z / ‖z‖₂ = Zᵀ h`.

This file formalizes the deterministic construction and its exact
identities: `h` is a unit vector (in `∑·²` normalization) annihilated
by every hidden constraint row, `c = Zᵀ h`, and the self-normal
`n = Z(ZᵀZ)⁻¹Zᵀh` lies in `range Z`.

The *law* of `h` — uniform on the unit sphere of `E` with a fair
orientation — and the concentration bounds (4.4) are the content of
Theorem 4.1 and Appendix D; they are not formalized here.
-/

namespace Komlos

open scoped BigOperators Matrix

variable {s m : ℕ}

/-- The completion matrix `Q`: rows `0 … m−1` are `gᵢ ᵥ* Z`, row `m` is
the reference row `r`. -/
noncomputable def completionQ (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (g : Fin m → Fin s → ℝ) (r : Fin (m + 1) → ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun i => Fin.lastCases r (fun i' => g i' ᵥ* Z) i

theorem completionQ_last_row (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (g : Fin m → Fin s → ℝ) (r : Fin (m + 1) → ℝ) :
    completionQ Z g r (Fin.last m) = r := by
  funext j
  simp [completionQ]

theorem completionQ_hidden_row (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (g : Fin m → Fin s → ℝ) (r : Fin (m + 1) → ℝ) (i : Fin m) :
    completionQ Z g r (Fin.castSucc i) = g i ᵥ* Z := by
  funext j
  simp [completionQ]

/-- The coefficient vector `y = Q⁻¹ e_k`, well-defined for invertible
`Q`; it annihilates every hidden row. -/
noncomputable def completionY (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (g : Fin m → Fin s → ℝ) (r : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  (completionQ Z g r)⁻¹ *ᵥ Pi.single (Fin.last m) 1

/-- `Q·y = e_k` when `Q` is invertible. -/
theorem completionQ_mulVec_y {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    {g : Fin m → Fin s → ℝ} {r : Fin (m + 1) → ℝ}
    (hQ : IsUnit (completionQ Z g r)) :
    completionQ Z g r *ᵥ completionY Z g r = Pi.single (Fin.last m) 1 := by
  unfold completionY
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hQ),
    Matrix.one_mulVec]

/-- The hidden rows annihilate `y`: `(gᵢ ᵥ* Z) ⬝ᵥ y = 0`. -/
theorem hidden_row_annihilates {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    {g : Fin m → Fin s → ℝ} {r : Fin (m + 1) → ℝ}
    (hQ : IsUnit (completionQ Z g r)) (i : Fin m) :
    (g i ᵥ* Z) ⬝ᵥ completionY Z g r = 0 := by
  have h := congrFun (completionQ_mulVec_y hQ) (Fin.castSucc i)
  rw [Matrix.mulVec_apply] at h
  have hrow : (completionQ Z g r).row (Fin.castSucc i) = g i ᵥ* Z :=
    completionQ_hidden_row Z g r i
  rw [hrow] at h
  have hne : (Fin.castSucc i : Fin (m + 1)) ≠ Fin.last m :=
    Fin.ne_of_lt (Fin.castSucc_lt_last i)
  rw [Pi.single_eq_of_ne hne] at h
  exact h

/-- The physical direction `z = Z y`. -/
noncomputable def completionZ (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (g : Fin m → Fin s → ℝ) (r : Fin (m + 1) → ℝ) : Fin s → ℝ :=
  Z *ᵥ completionY Z g r

/-- Each hidden constraint annihilates `z`: `gᵢ ⬝ᵥ z = 0`. -/
theorem hidden_row_annihilates_z {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    {g : Fin m → Fin s → ℝ} {r : Fin (m + 1) → ℝ}
    (hQ : IsUnit (completionQ Z g r)) (i : Fin m) :
    g i ⬝ᵥ completionZ Z g r = 0 := by
  rw [completionZ, Matrix.dotProduct_mulVec]
  exact hidden_row_annihilates hQ i

/-- `y ≠ 0` when `Q` is invertible: `Qy = e_k` is nonzero in the last
coordinate. -/
theorem completionY_ne_zero {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    {g : Fin m → Fin s → ℝ} {r : Fin (m + 1) → ℝ}
    (hQ : IsUnit (completionQ Z g r)) : completionY Z g r ≠ 0 := by
  intro hy
  have h := congrFun (completionQ_mulVec_y hQ) (Fin.last m)
  rw [hy, Matrix.mulVec_zero] at h
  simp [Pi.single_eq_same] at h

/-- Squared Euclidean mass helper. -/
noncomputable def sqNorm {s : ℕ} (v : Fin s → ℝ) : ℝ := ∑ j, v j ^ 2

theorem sqNorm_pos {w : Fin s → ℝ} (hw : w ≠ 0) : 0 < sqNorm w := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  unfold sqNorm
  apply Finset.sum_pos' (fun i _ => sq_nonneg _)
  exact ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero hj⟩

/-- The normalized direction `h = z / ‖z‖₂` as a coordinate vector. -/
noncomputable def completionH (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (g : Fin m → Fin s → ℝ) (r : Fin (m + 1) → ℝ) : Fin s → ℝ :=
  (Real.sqrt (sqNorm (completionZ Z g r)))⁻¹ • completionZ Z g r

/-- `h` is a unit vector (in `∑·²` normalization) when `z ≠ 0`. -/
theorem completionH_unit {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    {g : Fin m → Fin s → ℝ} {r : Fin (m + 1) → ℝ}
    (hz : completionZ Z g r ≠ 0) : sqNorm (completionH Z g r) = 1 := by
  have hpos : (0 : ℝ) < sqNorm (completionZ Z g r) := sqNorm_pos hz
  have hsum : sqNorm (completionH Z g r) =
      (Real.sqrt (sqNorm (completionZ Z g r)))⁻¹ ^ 2 *
        sqNorm (completionZ Z g r) := by
    unfold completionH sqNorm
    simp_rw [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [← Finset.mul_sum]
  rw [hsum, inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

/-- `c = Zᵀ h`, the constraint vector in coefficient coordinates. -/
noncomputable def completionC (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (g : Fin m → Fin s → ℝ) (r : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  Zᵀ *ᵥ completionH Z g r

/-- The self-normal `n = Z(ZᵀZ)⁻¹ c ∈ range Z`. -/
noncomputable def selfNormal (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (g : Fin m → Fin s → ℝ) (r : Fin (m + 1) → ℝ) : Fin s → ℝ :=
  Z *ᵥ ((Zᵀ * Z)⁻¹ *ᵥ completionC Z g r)

theorem selfNormal_mem_range (Z : Matrix (Fin s) (Fin (m + 1)) ℝ)
    (g : Fin m → Fin s → ℝ) (r : Fin (m + 1) → ℝ) :
    selfNormal Z g r ∈ LinearMap.range Z.mulVecLin :=
  ⟨(Zᵀ * Z)⁻¹ *ᵥ completionC Z g r, rfl⟩

/-- When `Zᵀ Z` is invertible, the self-normal agrees with `h` on
coefficient coordinates: `Zᵀ n = Zᵀ h = c`. -/
theorem transpose_mulVec_selfNormal {Z : Matrix (Fin s) (Fin (m + 1)) ℝ}
    {g : Fin m → Fin s → ℝ} {r : Fin (m + 1) → ℝ}
    (hZ : IsUnit (Zᵀ * Z)) :
    Zᵀ *ᵥ selfNormal Z g r = completionC Z g r := by
  unfold selfNormal
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hZ),
    Matrix.one_mulVec]

end Komlos
