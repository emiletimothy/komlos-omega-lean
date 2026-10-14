/-
# Sherman–Morrison rank-one inverse update (Appendix E)

Formalizes the Sherman–Morrison formula and the rank-one bookkeeping used by
the dynamic inverse maintenance in Appendix E of
"The Komlós Problem in Near Matrix-Multiplication Time".

For `A : Matrix (Fin n) (Fin n) ℝ` invertible and `u v : Fin n → ℝ` with
`1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0`,

    (A + u vᵀ)⁻¹ = A⁻¹ − (1 + v ⬝ᵥ A⁻¹ u)⁻¹ • (A⁻¹ u)(v ⬝ᵥ A⁻¹),

where `u vᵀ` is `Matrix.vecMulVec u v`.  The paper's dynamic data structure
applies this with `v = eᵢ`, i.e. adding `u` to column `i` of `A`; we record
the column-update specialization, the Frobenius-norm factorization
`‖u vᵀ‖²_F = (∑ᵢ uᵢ²)(∑ⱼ vⱼ²)`, and the matrix determinant lemma
`det (A + u vᵀ) = det A * (1 + v ⬝ᵥ A⁻¹ u)`.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Komlos.InverseMaintenanceBlock

namespace Komlos

open scoped Matrix.Norms.Frobenius
open Matrix

noncomputable section

variable {n : ℕ}

/-- The **Sherman–Morrison formula** (Appendix E): the inverse of a rank-one
update `A + u vᵀ` is a rank-one update of `A⁻¹`,

    (A + u vᵀ)⁻¹ = A⁻¹ − (1 + v ⬝ᵥ A⁻¹ u)⁻¹ • (A⁻¹ u)(v ⬝ᵥ A⁻¹).

In Mathlib, `u vᵀ` is `Matrix.vecMulVec u v` and the row `v ⬝ᵥ A⁻¹` is written
`Aᵀ⁻¹ *ᵥ v`.  Proved by multiplying out `B * (A + u vᵀ)` for the claimed `B`
and collecting the scalar `1 + v ⬝ᵥ A⁻¹ u`. -/
theorem sherman_morrison (A : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ)
    (hA : IsUnit A.det) (h : 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) :
    (A + Matrix.vecMulVec u v)⁻¹ =
      A⁻¹ - (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ •
        Matrix.vecMulVec (A⁻¹ *ᵥ u) (Aᵀ⁻¹ *ᵥ v) := by
  have hy : Aᵀ⁻¹ *ᵥ v = v ᵥ* A⁻¹ := by
    rw [← Matrix.transpose_nonsing_inv, Matrix.mulVec_transpose]
  have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  have hyA : (v ᵥ* A⁻¹) ᵥ* A = v := by
    rw [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
  have hdot : (v ᵥ* A⁻¹) ⬝ᵥ u = v ⬝ᵥ (A⁻¹ *ᵥ u) :=
    (Matrix.dotProduct_mulVec v A⁻¹ u).symm
  have hWA : Matrix.vecMulVec (A⁻¹ *ᵥ u) (Aᵀ⁻¹ *ᵥ v) * A =
      Matrix.vecMulVec (A⁻¹ *ᵥ u) v := by
    rw [Matrix.vecMulVec_mul, hy, hyA]
  have hWU : Matrix.vecMulVec (A⁻¹ *ᵥ u) (Aᵀ⁻¹ *ᵥ v) * Matrix.vecMulVec u v =
      (v ⬝ᵥ (A⁻¹ *ᵥ u)) • Matrix.vecMulVec (A⁻¹ *ᵥ u) v := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hy, hdot, Matrix.vecMulVec_smul]
  have hcoeff : 1 - (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ * (v ⬝ᵥ (A⁻¹ *ᵥ u)) =
      (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ := by
    have hs : (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ * (1 + v ⬝ᵥ (A⁻¹ *ᵥ u)) = 1 :=
      inv_mul_cancel₀ h
    rw [mul_add, mul_one] at hs
    linarith [hs]
  have hM : ∀ q : ℝ, Matrix.vecMulVec (A⁻¹ *ᵥ u) v -
      q • Matrix.vecMulVec (A⁻¹ *ᵥ u) v =
      (1 - q) • Matrix.vecMulVec (A⁻¹ *ᵥ u) v := fun q ↦ by
    rw [sub_smul, one_smul]
  apply Matrix.inv_eq_left_inv
  simp only [mul_add, sub_mul, Matrix.smul_mul]
  rw [hinv, hWA, Matrix.mul_vecMulVec A⁻¹ u v, hWU, smul_smul]
  rw [hM, hcoeff, sub_add_cancel]

/-- Sherman–Morrison specialized to a column update `A + u eᵢᵀ`, which is the
update maintained by the paper's algorithm: the inverse gains the rank-one
term `(1 + (A⁻¹ u)ᵢ)⁻¹ • (A⁻¹ u)(A⁻¹ row i)`. -/
theorem sherman_morrison_col (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ)
    (i : Fin n) (hA : IsUnit A.det) (h : 1 + (A⁻¹ *ᵥ u) i ≠ 0) :
    (A + Matrix.vecMulVec u (Pi.single i (1:ℝ)))⁻¹ =
      A⁻¹ - (1 + (A⁻¹ *ᵥ u) i)⁻¹ •
        Matrix.vecMulVec (A⁻¹ *ᵥ u) (A⁻¹.row i) := by
  have h' : 1 + Pi.single i (1:ℝ) ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0 := by
    rwa [single_one_dotProduct]
  have hcol : Aᵀ⁻¹ *ᵥ Pi.single i (1:ℝ) = A⁻¹.row i := by
    rw [← Matrix.transpose_nonsing_inv, Matrix.mulVec_single_one]
    ext j
    simp [Matrix.col_apply, Matrix.transpose_apply, Matrix.row_apply]
  rw [sherman_morrison A u _ hA h', single_one_dotProduct, hcol]

/-- Entry formula for `vecMulVec u eᵢ`. -/
theorem vecMulVec_single_apply (u : Fin n → ℝ) (i j k : Fin n) :
    Matrix.vecMulVec u (Pi.single i (1:ℝ)) j k =
      u j * (Pi.single i (1:ℝ) : Fin n → ℝ) k :=
  Matrix.vecMulVec_apply _ _ _ _

/-- The `i`-th column of `vecMulVec u eᵢ` is `u`. -/
theorem vecMulVec_single_apply_same (u : Fin n → ℝ) (i j : Fin n) :
    Matrix.vecMulVec u (Pi.single i (1:ℝ)) j i = u j := by
  rw [vecMulVec_single_apply, Pi.single_eq_same, mul_one]

/-- Columns of `vecMulVec u eᵢ` other than `i` vanish. -/
theorem vecMulVec_single_apply_of_ne (u : Fin n → ℝ) {i j k : Fin n}
    (hk : k ≠ i) :
    Matrix.vecMulVec u (Pi.single i (1:ℝ)) j k = 0 := by
  rw [vecMulVec_single_apply, Pi.single_eq_of_ne hk, mul_zero]

/-- `A + vecMulVec u eᵢ` is `A` with `u` added to column `i`. -/
theorem add_vecMulVec_single_col (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ)
    (i j : Fin n) :
    (A + Matrix.vecMulVec u (Pi.single i (1:ℝ))).col i j = A.col i j + u j := by
  rw [Matrix.col_apply, Matrix.col_apply, Matrix.add_apply,
    vecMulVec_single_apply_same]

/-- `vecMulVec u eᵢ` acting on a vector `x` returns `x i • u`. -/
theorem vecMulVec_single_mulVec (u x : Fin n → ℝ) (i : Fin n) :
    Matrix.vecMulVec u (Pi.single i (1:ℝ)) *ᵥ x = x i • u := by
  rw [Matrix.vecMulVec_mulVec, single_one_dotProduct, op_smul_eq_smul]

/-- Frobenius norm of a rank-one matrix factors:
`‖u vᵀ‖²_F = (∑ᵢ uᵢ²) * (∑ⱼ vⱼ²)`. -/
theorem frobenius_norm_sq_vecMulVec (u v : Fin n → ℝ) :
    ‖Matrix.vecMulVec u v‖ ^ 2 = (∑ i, u i ^ 2) * (∑ j, v j ^ 2) := by
  rw [frobenius_norm_sq, Finset.sum_mul_sum]
  simp_rw [Matrix.vecMulVec_apply, mul_pow]

/-- The **matrix determinant lemma** for `I + x vᵀ`:
`det (1 + x vᵀ) = 1 + v ⬝ᵥ x`. -/
theorem det_one_add_vecMulVec (x v : Fin n → ℝ) :
    (1 + Matrix.vecMulVec x v).det = 1 + v ⬝ᵥ x := by
  rw [Matrix.vecMulVec_eq (Fin 1), Matrix.det_one_add_replicateCol_mul_replicateRow]

/-- The **matrix determinant lemma**:
`det (A + u vᵀ) = det A * (1 + v ⬝ᵥ A⁻¹ u)`.  This is the determinant
consistency check for the Sherman–Morrison update: `A + u vᵀ` is invertible
exactly when `1 + v ⬝ᵥ A⁻¹ u ≠ 0`. -/
theorem det_add_vecMulVec (A : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ)
    (hA : IsUnit A.det) :
    (A + Matrix.vecMulVec u v).det = A.det * (1 + v ⬝ᵥ (A⁻¹ *ᵥ u)) := by
  have hfact : A + Matrix.vecMulVec u v =
      A * (1 + Matrix.vecMulVec (A⁻¹ *ᵥ u) v) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec,
      Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]
  rw [hfact, Matrix.det_mul, det_one_add_vecMulVec]

end

end Komlos
