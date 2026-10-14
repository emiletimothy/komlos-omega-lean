/-
# Augmented block inverse (equation 4.5)

Formalizes the block lower-triangular augmentation used in Section 4.3 of
"The Komlós Problem in Near Matrix-Multiplication Time".  For
`Q : Matrix (Fin k) (Fin k) ℝ` (a query matrix) and `B : Matrix (Fin (s + k))
(Fin k) ℝ` (the stack `[Z; ZᵀZ]`), the augmented matrix is

    A(Q) = ⎛ Q    0 ⎞
           ⎝ −B   I ⎠

with inverse (equation 4.5)

    A(Q)⁻¹ = ⎛ Q⁻¹     0 ⎞
              ⎝ B Q⁻¹  I ⎠ ,

so that `A(Q)⁻¹ · (eⱼ, 0) = (Q⁻¹ eⱼ, B Q⁻¹ eⱼ)` returns the direction `y`,
the coefficient `z` and the normal `w` in a single column query.

We also record the exact Frobenius-norm bookkeeping used in Section 5:
`‖A(Q)‖²_F = ‖Q‖²_F + ‖B‖²_F + (s + k)` and
`‖A(Q)⁻¹‖²_F ≤ ‖Q⁻¹‖²_F + ‖B‖²_F ‖Q⁻¹‖²_F + (s + k)`.
-/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.SchurComplement

namespace Komlos

open scoped Matrix.Norms.Frobenius
open Matrix

noncomputable section

variable {k s : ℕ}

/-- The augmented block lower-triangular matrix `A(Q)` of equation (4.5).
`Q` is the `k × k` query matrix and `B` is the `(s+k) × k` stack `[Z; ZᵀZ]`;
the identity block has size `s + k`. -/
def augmentedMatrix (Q : Matrix (Fin k) (Fin k) ℝ) (B : Matrix (Fin (s + k)) (Fin k) ℝ) :
    Matrix (Fin k ⊕ Fin (s + k)) (Fin k ⊕ Fin (s + k)) ℝ :=
  Matrix.fromBlocks Q 0 (-B) 1

/-- Equation (4.5): the inverse of the augmented matrix.  The lower-left
block `-(I⁻¹ (-B) Q⁻¹) = B Q⁻¹` packages `z` and `w` in one inverse column. -/
theorem augmentedMatrix_inv (Q : Matrix (Fin k) (Fin k) ℝ)
    (B : Matrix (Fin (s + k)) (Fin k) ℝ) (hQ : IsUnit Q) :
    (augmentedMatrix Q B)⁻¹ = Matrix.fromBlocks Q⁻¹ 0 (B * Q⁻¹) 1 := by
  have h1 : IsUnit (1 : Matrix (Fin (s + k)) (Fin (s + k)) ℝ) := isUnit_one
  have h21 : -((1 : Matrix (Fin (s + k)) (Fin (s + k)) ℝ)⁻¹ * -B * Q⁻¹) = B * Q⁻¹ := by
    simp
  rw [augmentedMatrix,
    Matrix.inv_fromBlocks_zero₁₂_of_isUnit_iff _ _ _
      (hAD := ⟨fun _ => h1, fun _ => hQ⟩), h21, inv_one]

/-- The column query of (4.5): `A(Q)⁻¹ · (eⱼ, 0) = (Q⁻¹ eⱼ, B Q⁻¹ eⱼ)`.
With `B = [Z; ZᵀZ]` the second block is `(z, w) = (Z y, Zᵀ Z y)` for
`y = Q⁻¹ eⱼ`. -/
theorem augmentedMatrix_inv_mulVec (Q : Matrix (Fin k) (Fin k) ℝ)
    (B : Matrix (Fin (s + k)) (Fin k) ℝ) (hQ : IsUnit Q) (j : Fin k) :
    (augmentedMatrix Q B)⁻¹ *ᵥ Sum.elim (Pi.single j 1) 0 =
      Sum.elim (Q⁻¹ *ᵥ Pi.single j 1) (B *ᵥ (Q⁻¹ *ᵥ Pi.single j 1)) := by
  have hxl : Sum.elim (Pi.single j (1 : ℝ)) (0 : Fin (s + k) → ℝ) ∘ Sum.inl =
      Pi.single j 1 := rfl
  have hxr : Sum.elim (Pi.single j (1 : ℝ)) (0 : Fin (s + k) → ℝ) ∘ Sum.inr =
      0 := rfl
  rw [augmentedMatrix_inv Q B hQ, Matrix.fromBlocks_mulVec, hxl, hxr,
    Matrix.zero_mulVec, add_zero, Matrix.one_mulVec, add_zero,
    Matrix.mulVec_mulVec]

/-- Squared Frobenius norm of a real matrix as an entry sum. -/
theorem frobenius_norm_sq {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) :
    ‖M‖ ^ 2 = ∑ i, ∑ j, (M i j) ^ 2 := by
  have hnn : 0 ≤ ∑ i : m, ∑ j : n, ‖M i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (norm_nonneg _) _
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt hnn]
  simp_rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]

/-- Squared Frobenius norm of a block matrix splits over the four blocks. -/
theorem frobenius_norm_sq_fromBlocks {m n o p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin m) (Fin p) ℝ) (C : Matrix (Fin o) (Fin n) ℝ)
    (D : Matrix (Fin o) (Fin p) ℝ) :
    ‖Matrix.fromBlocks A B C D‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 + ‖C‖ ^ 2 + ‖D‖ ^ 2 := by
  rw [frobenius_norm_sq (Matrix.fromBlocks A B C D), frobenius_norm_sq A,
    frobenius_norm_sq B, frobenius_norm_sq C, frobenius_norm_sq D]
  simp_rw [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Finset.sum_add_distrib]
  ring

/-- Squared Frobenius norm of the identity matrix is the dimension. -/
theorem frobenius_norm_sq_one (n : ℕ) :
    ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ ^ 2 = n := by
  rw [frobenius_norm_sq]
  simp [Matrix.one_apply, ite_pow, Finset.sum_ite_eq, Finset.card_univ]

/-- Norm bookkeeping for `A(Q)` from Section 5:
`‖A(Q)‖²_F = ‖Q‖²_F + ‖B‖²_F + (s + k)`. -/
theorem augmentedMatrix_norm_sq (Q : Matrix (Fin k) (Fin k) ℝ)
    (B : Matrix (Fin (s + k)) (Fin k) ℝ) :
    ‖augmentedMatrix Q B‖ ^ 2 = ‖Q‖ ^ 2 + ‖B‖ ^ 2 + (s + k) := by
  rw [augmentedMatrix, frobenius_norm_sq_fromBlocks, norm_neg, norm_zero,
    frobenius_norm_sq_one, Nat.cast_add]
  ring

/-- Norm bookkeeping for `A(Q)⁻¹` from Section 5:
`‖A(Q)⁻¹‖²_F ≤ ‖Q⁻¹‖²_F + ‖B‖²_F ‖Q⁻¹‖²_F + (s + k)`. -/
theorem augmentedMatrix_inv_norm_sq_le (Q : Matrix (Fin k) (Fin k) ℝ)
    (B : Matrix (Fin (s + k)) (Fin k) ℝ) (hQ : IsUnit Q) :
    ‖(augmentedMatrix Q B)⁻¹‖ ^ 2 ≤
      ‖Q⁻¹‖ ^ 2 + ‖B‖ ^ 2 * ‖Q⁻¹‖ ^ 2 + (s + k) := by
  rw [augmentedMatrix_inv Q B hQ, frobenius_norm_sq_fromBlocks, norm_zero,
    frobenius_norm_sq_one, Nat.cast_add]
  have hmul : ‖B * Q⁻¹‖ ^ 2 ≤ ‖B‖ ^ 2 * ‖Q⁻¹‖ ^ 2 := by
    calc ‖B * Q⁻¹‖ ^ 2 ≤ (‖B‖ * ‖Q⁻¹‖) ^ 2 :=
        sq_le_sq' ((neg_nonpos.mpr
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans (norm_nonneg _))
          (Matrix.frobenius_norm_mul _ _)
      _ = ‖B‖ ^ 2 * ‖Q⁻¹‖ ^ 2 := mul_pow _ _ _
  have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [h0]
  linarith [hmul]

/-- Under the Section 5 hypotheses (`Q` invertible, `‖Q‖_F, ‖Q⁻¹‖_F ≤ K`,
`‖B‖_F ≤ K_C`): `‖A(Q)‖²_F ≤ K² + K_C² + s + k` and
`‖A(Q)⁻¹‖²_F ≤ K² + K_C²K² + s + k`.  Invertibility is a hypothesis, since
`‖Q⁻¹‖_F` is defined through `Ring.inverse`, which vanishes on non-units. -/
theorem augmentedMatrix_norm_sq_le (Q : Matrix (Fin k) (Fin k) ℝ)
    (B : Matrix (Fin (s + k)) (Fin k) ℝ) (hunit : IsUnit Q)
    {K KC : ℝ} (hQ : ‖Q‖ ≤ K) (hQi : ‖Q⁻¹‖ ≤ K) (hB : ‖B‖ ≤ KC)
    (hK : 0 ≤ K) (hKC : 0 ≤ KC) :
    ‖augmentedMatrix Q B‖ ^ 2 ≤ K ^ 2 + KC ^ 2 + (s + k) ∧
    ‖(augmentedMatrix Q B)⁻¹‖ ^ 2 ≤ K ^ 2 + KC ^ 2 * K ^ 2 + (s + k) := by
  have hQ2 : ‖Q‖ ^ 2 ≤ K ^ 2 :=
    sq_le_sq' ((neg_nonpos.mpr hK).trans (norm_nonneg _)) hQ
  have hQi2 : ‖Q⁻¹‖ ^ 2 ≤ K ^ 2 :=
    sq_le_sq' ((neg_nonpos.mpr hK).trans (norm_nonneg _)) hQi
  have hB2 : ‖B‖ ^ 2 ≤ KC ^ 2 :=
    sq_le_sq' ((neg_nonpos.mpr hKC).trans (norm_nonneg _)) hB
  rw [augmentedMatrix_norm_sq]
  refine ⟨by linarith [hQ2, hB2], ?_⟩
  refine (augmentedMatrix_inv_norm_sq_le Q B hunit).trans ?_
  have hprod : ‖B‖ ^ 2 * ‖Q⁻¹‖ ^ 2 ≤ KC ^ 2 * K ^ 2 :=
    mul_le_mul hB2 hQi2 (sq_nonneg _) (sq_nonneg _)
  linarith [hQi2, hprod]

end

end Komlos
