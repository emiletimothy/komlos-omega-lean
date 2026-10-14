/-
# Dynamic inverse maintenance: correctness invariant and amortized cost

This file connects the verified matrix algebra of `Komlos.InverseUpdate`
(the Sherman–Morrison formula and the matrix determinant lemma) and
`Komlos.InverseMaintenanceBlock` (the augmented block inverse of
equation (4.5)) to the abstract bit-cost model of `Komlos.Runtime`,
formalizing the correctness invariant and the cost account of the dynamic
inverse maintenance used in Section 5 and Appendix E of "The Komlós
Problem in Near Matrix-Multiplication Time" (Anand–Chen).

## Contents

1. `DynamicInverseState n`: a maintained pair `(A, Inv)` of `n × n` real
   matrices with the certificate `Inv * A = 1`.  For square real matrices a
   left inverse is two-sided (`inv_eq`, `isUnit_det`, `mul_inv`), so `Inv`
   is provably the genuine `A⁻¹`.
2. `DynamicInverseState.update` and `updateCol`: the Sherman–Morrison
   rank-one update of the cache, proved to preserve the certificate — the
   new `Inv` satisfies `Inv' * (A + u vᵀ) = 1` — whenever the guard
   `1 + v ⬝ᵥ (Inv *ᵥ u) ≠ 0` holds.  `guard_iff_isUnit_det` shows this
   guard is *exactly* nonsingularity of the updated matrix, via
   `det_add_vecMulVec`.  `updateIfValid` and `updateAll` fold adaptively
   chosen updates while maintaining the invariant structurally.
3. Operation counts (literal counts of rational operations, each charged
   by the `BitCostModel` fields):
   * `guardCheckOps`: `n` length-`n` dot products for `Inv *ᵥ u`, one more
     for `v ⬝ᵥ w`, one `+1`, one zero-comparison;
     `guardCheckOps_le` bounds it by `scalarConst·(2n²+2n+2)·B²`, and
     `guardCheckOps_quadratic` by `6·scalarConst·n²·B²`.
   * `rankOneUpdateOps`: two matrix–vector products, the guard scalar, one
     scalar inversion, the `n²` entry updates of `Inv`, and the `n²` entry
     updates of `A`; `rankOneUpdateOps_le` bounds it by
     `12·scalarConst·n^ω·B²`.
   * `blockQueryOps`: one matrix–vector product on the order-`N` augmented
     matrix `A(Q)` of `augmentedMatrix`, which returns `(y, z, w)` in one
     shot by `augmentedMatrix_inv_mulVec`; `blockQueryOps_le` bounds it by
     `2·scalarConst·N²·B²`.
   * `recomputeOps`: a full inverse recomputation charged as one
     `matmulCost n B` (the model's `inversion = O(n^ω)` convention).
4. The amortized account: `dynamicOps` totals `T` updates, `Q` block
   queries, and `R` recomputations; `dynamicOps_le` gives the unamortized
   bound and `dynamicOps_amortized_le` the key bound — under the rebuild
   schedule hypothesis `R·n ≤ T` (at most one recomputation per `n`
   operations) the total is `O(T·n^ω·B² + Q·N²·B² + T·n^{ω-1}·B)`, the
   `T·s^{ω-1}` amortized term of Theorem 5.1 / equation (E.2).
   `maintenanceTotalOps` adds the one-time `matmulCost` initialization,
   `maintenanceEnvelope` packages the bound as
   `(matmulLeadingConst + 12·scalarConst·B)·(T+1)·n^ω·B`, and
   `maintenanceTotalOps_le` proves the total fits inside it.

## Status

* **Proved** (conditional only on the `BitCostModel` field hypotheses, as
  is the whole cost model): the state invariant and its preservation under
  rank-one updates (`update`, `updateCol`, `updateAll`), the exact guard
  criterion `guard_iff_isUnit_det`, all operation-count bounds, both
  amortization lemmas, and `dynamicMaintenanceBound`.
* **Explicit hypotheses / modeling conventions, not proved theorems:**
  `recomputeOps` charges a full recomputation as a single `matmulCost`;
  the rebuild-count hypothesis `R·n ≤ T` replaces the paper's
  `L = ⌈log₂ N⌉`-level rebuild hierarchy (Appendix E), which is not
  formalized; the entry bit size `B` is a parameter, not a maintained
  invariant; all arithmetic is exact real arithmetic — the
  finite-precision Woodbury error analysis of Appendix E (equation (E.3))
  is out of scope.
* **Not attempted:** the lookahead/candidate-set combinatorics of
  Section 5, adaptivity constraints on the update stream, and hidden
  polylogarithmic factors — the bound here is a proved `O(·)`, not `Õ`.
-/

import Komlos.InverseUpdate
import Komlos.Runtime

namespace Komlos

open Matrix
open scoped Classical

noncomputable section

/-! ## The maintained state and its inverse certificate -/

/-- A dynamic-inverse state in dimension `n`: the current matrix `A`, the
cached value `Inv`, and a certificate `Inv * A = 1`.  For square real
matrices a left inverse is two-sided, so the certificate makes `Inv` the
genuine `A⁻¹` (`DynamicInverseState.inv_eq`). -/
structure DynamicInverseState (n : ℕ) where
  /-- The current matrix. -/
  A : Matrix (Fin n) (Fin n) ℝ
  /-- The cached inverse. -/
  Inv : Matrix (Fin n) (Fin n) ℝ
  /-- Certificate: `Inv` is a left inverse of `A`. -/
  cert : Inv * A = 1

section Invariant

variable {n : ℕ}

namespace DynamicInverseState

/-- The certificate forces `A` nonsingular. -/
theorem isUnit_det (s : DynamicInverseState n) : IsUnit s.A.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have h : s.Inv.det * s.A.det = 1 := by
    rw [← Matrix.det_mul, s.cert, Matrix.det_one]
  rw [h0, mul_zero] at h
  exact one_ne_zero h.symm

/-- The certificate makes `A` a unit of the matrix ring. -/
theorem isUnit (s : DynamicInverseState n) : IsUnit s.A :=
  (Matrix.isUnit_iff_isUnit_det s.A).mpr s.isUnit_det

/-- `Inv` is the genuine two-sided inverse `A⁻¹`. -/
theorem inv_eq (s : DynamicInverseState n) : (s.A)⁻¹ = s.Inv :=
  Matrix.inv_eq_left_inv s.cert

/-- `Inv` is also a right inverse of `A`. -/
theorem mul_inv (s : DynamicInverseState n) : s.A * s.Inv = 1 := by
  rw [← s.inv_eq]
  exact Matrix.mul_nonsing_inv s.A s.isUnit_det

/-- Initialize the data structure at a nonsingular matrix by computing
`A⁻¹` once; in the cost account this is charged as one `recomputeOps`
(one `matmulCost`). -/
def init (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) :
    DynamicInverseState n where
  A := A
  Inv := A⁻¹
  cert := Matrix.nonsing_inv_mul A hA

/-- The trivial initial state `A = Inv = I`. -/
def one : DynamicInverseState n where
  A := 1
  Inv := 1
  cert := mul_one 1

/-- **Sherman–Morrison update.**  For the update `A ↦ A + u vᵀ`, the new
cached inverse is `Inv − c⁻¹ • (Inv*u)(Invᵀ*v)` with the guard scalar
`c = 1 + v ⬝ᵥ (Inv *ᵥ u)`.  Provided `c ≠ 0` — exactly the condition under
which `A + u vᵀ` stays invertible (`guard_iff_isUnit_det`) — the returned
state again satisfies the certificate `Inv' * A' = 1`. -/
def update (s : DynamicInverseState n) (u v : Fin n → ℝ)
    (h : 1 + v ⬝ᵥ (s.Inv *ᵥ u) ≠ 0) : DynamicInverseState n where
  A := s.A + Matrix.vecMulVec u v
  Inv := s.Inv - (1 + v ⬝ᵥ (s.Inv *ᵥ u))⁻¹ •
        Matrix.vecMulVec (s.Inv *ᵥ u) ((s.Inv)ᵀ *ᵥ v)
  cert := by
    have hA : IsUnit s.A.det := s.isUnit_det
    have hInv : (s.A)⁻¹ = s.Inv := s.inv_eq
    have hguard : 1 + v ⬝ᵥ ((s.A)⁻¹ *ᵥ u) ≠ 0 := by rwa [hInv]
    have hdet : IsUnit (s.A + Matrix.vecMulVec u v).det := by
      rw [det_add_vecMulVec s.A u v hA, hInv]
      exact hA.mul (isUnit_iff_ne_zero.mpr h)
    have hsm := sherman_morrison s.A u v hA hguard
    rw [← Matrix.transpose_nonsing_inv, hInv] at hsm
    rw [← hsm]
    exact Matrix.nonsing_inv_mul (s.A + Matrix.vecMulVec u v) hdet

/-- The updated matrix is `A + u vᵀ`. -/
@[simp]
theorem update_A (s : DynamicInverseState n) (u v : Fin n → ℝ)
    (h : 1 + v ⬝ᵥ (s.Inv *ᵥ u) ≠ 0) :
    (s.update u v h).A = s.A + Matrix.vecMulVec u v := rfl

/-- The updated cached inverse is the Sherman–Morrison rank-one
correction. -/
@[simp]
theorem update_Inv (s : DynamicInverseState n) (u v : Fin n → ℝ)
    (h : 1 + v ⬝ᵥ (s.Inv *ᵥ u) ≠ 0) :
    (s.update u v h).Inv =
      s.Inv - (1 + v ⬝ᵥ (s.Inv *ᵥ u))⁻¹ •
        Matrix.vecMulVec (s.Inv *ᵥ u) ((s.Inv)ᵀ *ᵥ v) := rfl

/-- **Column update** `A ↦ A + u eᵢᵀ` — the operation of the paper's
algorithm: `u` is added to column `i` of `A`.  The guard specializes to
`1 + (Inv *ᵥ u) i ≠ 0`. -/
def updateCol (s : DynamicInverseState n) (u : Fin n → ℝ) (i : Fin n)
    (h : 1 + (s.Inv *ᵥ u) i ≠ 0) : DynamicInverseState n :=
  s.update u (Pi.single i 1) (by rwa [single_one_dotProduct])

/-- The column update adds `u eᵢᵀ` to `A`. -/
@[simp]
theorem updateCol_A (s : DynamicInverseState n) (u : Fin n → ℝ) (i : Fin n)
    (h : 1 + (s.Inv *ᵥ u) i ≠ 0) :
    (s.updateCol u i h).A = s.A + Matrix.vecMulVec u (Pi.single i 1) := rfl

/-- A column update really adds `u` to column `i`. -/
theorem updateCol_col (s : DynamicInverseState n) (u : Fin n → ℝ)
    (i j : Fin n) (h : 1 + (s.Inv *ᵥ u) i ≠ 0) :
    (s.updateCol u i h).A.col i j = s.A.col i j + u j :=
  add_vecMulVec_single_col s.A u i j

/-- The updated cache for a column update is the Sherman–Morrison
correction with `Inv.row i` — the form used in `sherman_morrison_col`. -/
theorem updateCol_Inv (s : DynamicInverseState n) (u : Fin n → ℝ) (i : Fin n)
    (h : 1 + (s.Inv *ᵥ u) i ≠ 0) :
    (s.updateCol u i h).Inv =
      s.Inv - (1 + (s.Inv *ᵥ u) i)⁻¹ •
        Matrix.vecMulVec (s.Inv *ᵥ u) (s.Inv.row i) := by
  have h1 : (s.updateCol u i h).Inv =
      s.Inv - (1 + Pi.single i (1 : ℝ) ⬝ᵥ (s.Inv *ᵥ u))⁻¹ •
        Matrix.vecMulVec (s.Inv *ᵥ u) ((s.Inv)ᵀ *ᵥ Pi.single i 1) := rfl
  rw [h1, single_one_dotProduct, Matrix.mulVec_transpose,
    Matrix.single_vecMul, one_smul]

/-- **The guard is exact.**  The rank-one update `A + u vᵀ` remains
invertible precisely when the Sherman–Morrison denominator
`1 + v ⬝ᵥ (Inv *ᵥ u)` is nonzero — the matrix determinant lemma
`det (A + u vᵀ) = det A · (1 + v ⬝ᵥ A⁻¹ u)`, with `A⁻¹ = Inv` by `inv_eq`. -/
theorem guard_iff_isUnit_det (s : DynamicInverseState n) (u v : Fin n → ℝ) :
    1 + v ⬝ᵥ (s.Inv *ᵥ u) ≠ 0 ↔ IsUnit (s.A + Matrix.vecMulVec u v).det := by
  have hA : IsUnit s.A.det := s.isUnit_det
  rw [det_add_vecMulVec s.A u v hA, s.inv_eq, isUnit_iff_ne_zero,
    mul_ne_zero_iff_left (isUnit_iff_ne_zero.mp hA)]

/-- Apply the update if the guard holds, keep the old state otherwise.
By `guard_iff_isUnit_det` the `else` branch is taken only when the update
would have destroyed invertibility. -/
def updateIfValid (s : DynamicInverseState n) (u v : Fin n → ℝ) :
    DynamicInverseState n :=
  if h : 1 + v ⬝ᵥ (s.Inv *ᵥ u) ≠ 0 then s.update u v h else s

theorem updateIfValid_eq_update (s : DynamicInverseState n) (u v : Fin n → ℝ)
    (h : 1 + v ⬝ᵥ (s.Inv *ᵥ u) ≠ 0) :
    s.updateIfValid u v = s.update u v h := dite_eq_left h

theorem updateIfValid_eq_self (s : DynamicInverseState n) (u v : Fin n → ℝ)
    (h : ¬ 1 + v ⬝ᵥ (s.Inv *ᵥ u) ≠ 0) :
    s.updateIfValid u v = s := dite_eq_right h

/-- Fold a stream of adaptively chosen rank-one updates, skipping those
whose guard fails.  Every returned state satisfies the certificate by
construction. -/
def updateAll (s : DynamicInverseState n)
    (ops : List ((Fin n → ℝ) × (Fin n → ℝ))) : DynamicInverseState n :=
  ops.foldl (fun st uv => st.updateIfValid uv.1 uv.2) s

/-- The folded state still satisfies the inverse certificate. -/
theorem updateAll_cert (s : DynamicInverseState n)
    (ops : List ((Fin n → ℝ) × (Fin n → ℝ))) :
    (s.updateAll ops).Inv * (s.updateAll ops).A = 1 :=
  (s.updateAll ops).cert

end DynamicInverseState

end Invariant

/-! ## Rational-operation counts -/

/-- Accounted rational-operation count for testing the guard
`1 + v ⬝ᵥ (Inv *ᵥ u) ≠ 0` from the cached inverse alone:

* `Inv *ᵥ u`: `n` dot products, each `n` multiplies and at most `n` adds;
* `v ⬝ᵥ w`: one more length-`n` dot product;
* the `+1` and the comparison to `0`: one add and one compare. -/
def guardCheckOps (c : BitCostModel) (n B : ℕ) : ℕ :=
  n * (n * c.mulCost B + n * c.addCost B) +
    (n * c.mulCost B + n * c.addCost B) + (c.addCost B + c.cmpCost B)

/-- The guard test costs `O(n²·B²)` bit operations: literally
`scalarConst·(2n²+2n+2)·B²`. -/
theorem guardCheckOps_le (c : BitCostModel) (n B : ℕ) (hB : 1 ≤ B) :
    (guardCheckOps c n B : ℝ) ≤
      c.scalarConst * (2 * (n : ℝ) ^ 2 + 2 * n + 2) * (B : ℝ) ^ 2 := by
  have hs := c.scalarConst_nonneg
  have hBR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hBB : (B : ℝ) ≤ (B : ℝ) ^ 2 :=
    le_self_pow₀ hBR (by decide : (2 : ℕ) ≠ 0)
  have hmul : (c.mulCost B : ℝ) ≤ c.scalarConst * (B : ℝ) ^ 2 := c.mulCost_le B
  have hadd : (c.addCost B : ℝ) ≤ c.scalarConst * (B : ℝ) ^ 2 :=
    (c.addCost_le B).trans (mul_le_mul_of_nonneg_left hBB hs)
  have hcmp : (c.cmpCost B : ℝ) ≤ c.scalarConst * (B : ℝ) ^ 2 :=
    (c.cmpCost_le B).trans (mul_le_mul_of_nonneg_left hBB hs)
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have e1 : (n : ℝ) *
        ((n : ℝ) * (c.mulCost B : ℝ) + (n : ℝ) * (c.addCost B : ℝ)) ≤
      c.scalarConst * (2 * (n : ℝ) ^ 2) * (B : ℝ) ^ 2 := by
    calc _ = (n : ℝ) ^ 2 * ((c.mulCost B : ℝ) + (c.addCost B : ℝ)) := by ring
      _ ≤ (n : ℝ) ^ 2 *
            (c.scalarConst * (B : ℝ) ^ 2 + c.scalarConst * (B : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add hmul hadd) hn2
      _ = _ := by ring
  have e2 : (n : ℝ) * (c.mulCost B : ℝ) + (n : ℝ) * (c.addCost B : ℝ) ≤
      c.scalarConst * (2 * n) * (B : ℝ) ^ 2 := by
    calc _ ≤ (n : ℝ) * (c.scalarConst * (B : ℝ) ^ 2) +
          (n : ℝ) * (c.scalarConst * (B : ℝ) ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hmul hn0)
            (mul_le_mul_of_nonneg_left hadd hn0)
      _ = _ := by ring
  have e3 : (c.addCost B : ℝ) + (c.cmpCost B : ℝ) ≤
      c.scalarConst * 2 * (B : ℝ) ^ 2 := by
    calc _ ≤ c.scalarConst * (B : ℝ) ^ 2 + c.scalarConst * (B : ℝ) ^ 2 :=
          add_le_add hadd hcmp
      _ = _ := by ring
  have hRHS : c.scalarConst * (2 * (n : ℝ) ^ 2 + 2 * n + 2) * (B : ℝ) ^ 2 =
      c.scalarConst * (2 * (n : ℝ) ^ 2) * (B : ℝ) ^ 2 +
        c.scalarConst * (2 * n) * (B : ℝ) ^ 2 +
        c.scalarConst * 2 * (B : ℝ) ^ 2 := by ring
  unfold guardCheckOps
  push_cast
  rw [hRHS]
  exact add_le_add (add_le_add e1 e2) e3

/-- Asymptotic form of `guardCheckOps_le`: the guard is checkable in
`6·scalarConst·n²·B²` bit operations for `n, B ≥ 1`. -/
theorem guardCheckOps_quadratic (c : BitCostModel) (n B : ℕ) (hn : 1 ≤ n)
    (hB : 1 ≤ B) :
    (guardCheckOps c n B : ℝ) ≤
      6 * c.scalarConst * (n : ℝ) ^ 2 * (B : ℝ) ^ 2 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnself : (n : ℝ) ≤ (n : ℝ) ^ 2 :=
    le_self_pow₀ hnR (by decide : (2 : ℕ) ≠ 0)
  have hone2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := hnR.trans hnself
  have hpoly : 2 * (n : ℝ) ^ 2 + 2 * n + 2 ≤ 6 * (n : ℝ) ^ 2 := by linarith
  calc (guardCheckOps c n B : ℝ)
      ≤ c.scalarConst * (2 * (n : ℝ) ^ 2 + 2 * n + 2) * (B : ℝ) ^ 2 :=
        guardCheckOps_le c n B hB
    _ ≤ c.scalarConst * (6 * (n : ℝ) ^ 2) * (B : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpoly c.scalarConst_nonneg) (sq_nonneg _)
    _ = 6 * c.scalarConst * (n : ℝ) ^ 2 * (B : ℝ) ^ 2 := by ring

/-- Accounted rational-operation count for one Sherman–Morrison rank-one
update of the cached inverse in dimension `n`:

* two matrix–vector products `Inv *ᵥ u` and `Invᵀ *ᵥ v`;
* the guard scalar `1 + v ⬝ᵥ (Inv *ᵥ u)`;
* one scalar inversion `c⁻¹`;
* the `n²` entry updates `Invᵢⱼ ↦ Invᵢⱼ − c⁻¹ · wᵢ · w'ⱼ` of `Inv`;
* the `n²` entry updates of `A ↦ A + u vᵀ` itself. -/
def rankOneUpdateOps (c : BitCostModel) (n B : ℕ) : ℕ :=
  2 * (n * (n * c.mulCost B + n * c.addCost B)) +
    (n * c.mulCost B + n * c.addCost B + c.addCost B) +
    c.divCost B +
    n * n * (2 * c.mulCost B + c.addCost B) +
    n * n * c.addCost B

/-- One rank-one update costs `O(n²·B²)` scalar work, which the
multiplication bound already absorbs: `12·scalarConst·n^ω·B²`. -/
theorem rankOneUpdateOps_le (c : BitCostModel) (n B : ℕ) (hn : 1 ≤ n)
    (hB : 1 ≤ B) :
    (rankOneUpdateOps c n B : ℝ) ≤
      12 * c.scalarConst * (n : ℝ) ^ c.ω * (B : ℝ) ^ 2 := by
  have hs := c.scalarConst_nonneg
  have hBR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hBB : (B : ℝ) ≤ (B : ℝ) ^ 2 :=
    le_self_pow₀ hBR (by decide : (2 : ℕ) ≠ 0)
  have hmul : (c.mulCost B : ℝ) ≤ c.scalarConst * (B : ℝ) ^ 2 := c.mulCost_le B
  have hadd : (c.addCost B : ℝ) ≤ c.scalarConst * (B : ℝ) ^ 2 :=
    (c.addCost_le B).trans (mul_le_mul_of_nonneg_left hBB hs)
  have hdiv : (c.divCost B : ℝ) ≤ c.scalarConst * (B : ℝ) ^ 2 :=
    c.divCost_le B
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have e1 : (2 : ℝ) * ((n : ℝ) *
        ((n : ℝ) * (c.mulCost B : ℝ) + (n : ℝ) * (c.addCost B : ℝ))) ≤
      c.scalarConst * (4 * (n : ℝ) ^ 2) * (B : ℝ) ^ 2 := by
    calc _ = 2 * (n : ℝ) ^ 2 * ((c.mulCost B : ℝ) + (c.addCost B : ℝ)) := by
          ring
      _ ≤ 2 * (n : ℝ) ^ 2 *
            (c.scalarConst * (B : ℝ) ^ 2 + c.scalarConst * (B : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add hmul hadd)
            (mul_nonneg (by norm_num) hn2)
      _ = _ := by ring
  have e2 : (n : ℝ) * (c.mulCost B : ℝ) + (n : ℝ) * (c.addCost B : ℝ) +
        (c.addCost B : ℝ) ≤
      c.scalarConst * (2 * n + 1) * (B : ℝ) ^ 2 := by
    calc _ ≤ (n : ℝ) * (c.scalarConst * (B : ℝ) ^ 2) +
          (n : ℝ) * (c.scalarConst * (B : ℝ) ^ 2) +
          c.scalarConst * (B : ℝ) ^ 2 :=
          add_le_add
            (add_le_add (mul_le_mul_of_nonneg_left hmul hn0)
              (mul_le_mul_of_nonneg_left hadd hn0)) hadd
      _ = _ := by ring
  have e3 : (c.divCost B : ℝ) ≤ c.scalarConst * 1 * (B : ℝ) ^ 2 := by
    calc _ ≤ c.scalarConst * (B : ℝ) ^ 2 := hdiv
      _ = _ := by ring
  have e4 : (n : ℝ) * (n : ℝ) *
        ((2 : ℝ) * (c.mulCost B : ℝ) + (c.addCost B : ℝ)) ≤
      c.scalarConst * (3 * (n : ℝ) ^ 2) * (B : ℝ) ^ 2 := by
    calc _ = (n : ℝ) ^ 2 *
          ((2 : ℝ) * (c.mulCost B : ℝ) + (c.addCost B : ℝ)) := by ring
      _ ≤ (n : ℝ) ^ 2 *
            ((2 : ℝ) * (c.scalarConst * (B : ℝ) ^ 2) +
              c.scalarConst * (B : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (add_le_add
              (mul_le_mul_of_nonneg_left hmul (by norm_num)) hadd) hn2
      _ = _ := by ring
  have e5 : (n : ℝ) * (n : ℝ) * (c.addCost B : ℝ) ≤
      c.scalarConst * ((n : ℝ) ^ 2) * (B : ℝ) ^ 2 := by
    calc _ = (n : ℝ) ^ 2 * (c.addCost B : ℝ) := by ring
      _ ≤ (n : ℝ) ^ 2 * (c.scalarConst * (B : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hadd hn2
      _ = _ := by ring
  have hquad : (rankOneUpdateOps c n B : ℝ) ≤
      c.scalarConst * (8 * (n : ℝ) ^ 2 + 2 * n + 2) * (B : ℝ) ^ 2 := by
    have hRHS : c.scalarConst * (8 * (n : ℝ) ^ 2 + 2 * n + 2) * (B : ℝ) ^ 2 =
        c.scalarConst * (4 * (n : ℝ) ^ 2) * (B : ℝ) ^ 2 +
          c.scalarConst * (2 * n + 1) * (B : ℝ) ^ 2 +
          c.scalarConst * 1 * (B : ℝ) ^ 2 +
          c.scalarConst * (3 * (n : ℝ) ^ 2) * (B : ℝ) ^ 2 +
          c.scalarConst * ((n : ℝ) ^ 2) * (B : ℝ) ^ 2 := by ring
    unfold rankOneUpdateOps
    push_cast
    rw [hRHS]
    exact add_le_add (add_le_add (add_le_add (add_le_add e1 e2) e3) e4) e5
  have hn2ω : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ c.ω := by
    rw [← Real.rpow_two]
    exact c.rpow_two_le_rpow_ω hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnself : (n : ℝ) ≤ (n : ℝ) ^ 2 :=
    le_self_pow₀ hnR (by decide : (2 : ℕ) ≠ 0)
  have hone2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := hnR.trans hnself
  have hpoly : 8 * (n : ℝ) ^ 2 + 2 * n + 2 ≤ 12 * (n : ℝ) ^ 2 := by linarith
  calc (rankOneUpdateOps c n B : ℝ)
      ≤ c.scalarConst * (8 * (n : ℝ) ^ 2 + 2 * n + 2) * (B : ℝ) ^ 2 := hquad
    _ ≤ c.scalarConst * (12 * (n : ℝ) ^ 2) * (B : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpoly hs) (sq_nonneg _)
    _ = (12 * c.scalarConst * (B : ℝ) ^ 2) * (n : ℝ) ^ 2 := by ring
    _ ≤ (12 * c.scalarConst * (B : ℝ) ^ 2) * (n : ℝ) ^ c.ω :=
        mul_le_mul_of_nonneg_left hn2ω
          (mul_nonneg (mul_nonneg (by norm_num) hs) (sq_nonneg _))
    _ = 12 * c.scalarConst * (n : ℝ) ^ c.ω * (B : ℝ) ^ 2 := by ring

/-- Accounted cost of one column query on the order-`N` augmented matrix
`A(Q)` of `augmentedMatrix` (in the paper `N = s + 2k`): a single
matrix–vector product returning `(y, z, w)` by
`augmentedMatrix_inv_mulVec`. -/
def blockQueryOps (c : BitCostModel) (N B : ℕ) : ℕ :=
  N * (N * c.mulCost B + N * c.addCost B)

theorem blockQueryOps_le (c : BitCostModel) (N B : ℕ) (hB : 1 ≤ B) :
    (blockQueryOps c N B : ℝ) ≤
      2 * c.scalarConst * (N : ℝ) ^ 2 * (B : ℝ) ^ 2 := by
  have hs := c.scalarConst_nonneg
  have hBR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hBB : (B : ℝ) ≤ (B : ℝ) ^ 2 :=
    le_self_pow₀ hBR (by decide : (2 : ℕ) ≠ 0)
  have hmul : (c.mulCost B : ℝ) ≤ c.scalarConst * (B : ℝ) ^ 2 := c.mulCost_le B
  have hadd : (c.addCost B : ℝ) ≤ c.scalarConst * (B : ℝ) ^ 2 :=
    (c.addCost_le B).trans (mul_le_mul_of_nonneg_left hBB hs)
  unfold blockQueryOps
  push_cast
  calc (N : ℝ) *
        ((N : ℝ) * (c.mulCost B : ℝ) + (N : ℝ) * (c.addCost B : ℝ))
      = (N : ℝ) ^ 2 * ((c.mulCost B : ℝ) + (c.addCost B : ℝ)) := by ring
    _ ≤ (N : ℝ) ^ 2 *
          (c.scalarConst * (B : ℝ) ^ 2 + c.scalarConst * (B : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hmul hadd) (sq_nonneg _)
    _ = 2 * c.scalarConst * (N : ℝ) ^ 2 * (B : ℝ) ^ 2 := by ring

/-- A full inverse recomputation, charged as one `n × n` matrix
multiplication — the model's convention for `inversion = O(n^ω)` work.
This is an accounting convention, not a theorem about inversion
algorithms. -/
def recomputeOps (c : BitCostModel) (n B : ℕ) : ℕ := c.matmulCost n B

theorem recomputeOps_le (c : BitCostModel) (n B : ℕ) :
    (recomputeOps c n B : ℝ) ≤
      c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ) :=
  c.matmulCost_le n B

/-! ## The amortized cost account -/

/-- Total accounted bit-cost of `T` rank-one updates, `Q` block queries on
an order-`N` augmented matrix, and `R` full recomputations in
dimension `n`. -/
def dynamicOps (c : BitCostModel) (n B N T Q R : ℕ) : ℕ :=
  T * rankOneUpdateOps c n B + Q * blockQueryOps c N B +
    R * recomputeOps c n B

/-- The unamortized total: `T` updates, `Q` queries, `R` recomputations. -/
theorem dynamicOps_le (c : BitCostModel) (n B N T Q R : ℕ) (hn : 1 ≤ n)
    (hB : 1 ≤ B) :
    (dynamicOps c n B N T Q R : ℝ) ≤
      12 * c.scalarConst * (T : ℝ) * (n : ℝ) ^ c.ω * (B : ℝ) ^ 2 +
        2 * c.scalarConst * (Q : ℝ) * (N : ℝ) ^ 2 * (B : ℝ) ^ 2 +
        (R : ℝ) * c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ) := by
  have e1 : ((T * rankOneUpdateOps c n B : ℕ) : ℝ) ≤
      (T : ℝ) * (12 * c.scalarConst * (n : ℝ) ^ c.ω * (B : ℝ) ^ 2) := by
    push_cast
    exact mul_le_mul_of_nonneg_left (rankOneUpdateOps_le c n B hn hB)
      (Nat.cast_nonneg _)
  have e2 : ((Q * blockQueryOps c N B : ℕ) : ℝ) ≤
      (Q : ℝ) * (2 * c.scalarConst * (N : ℝ) ^ 2 * (B : ℝ) ^ 2) := by
    push_cast
    exact mul_le_mul_of_nonneg_left (blockQueryOps_le c N B hB)
      (Nat.cast_nonneg _)
  have e3 : ((R * recomputeOps c n B : ℕ) : ℝ) ≤
      (R : ℝ) * (c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ)) := by
    push_cast
    exact mul_le_mul_of_nonneg_left (recomputeOps_le c n B)
      (Nat.cast_nonneg _)
  calc (dynamicOps c n B N T Q R : ℝ)
      = ((T * rankOneUpdateOps c n B : ℕ) : ℝ) +
          ((Q * blockQueryOps c N B : ℕ) : ℝ) +
          ((R * recomputeOps c n B : ℕ) : ℝ) := by
        unfold dynamicOps; push_cast; ring
    _ ≤ (T : ℝ) * (12 * c.scalarConst * (n : ℝ) ^ c.ω * (B : ℝ) ^ 2) +
          (Q : ℝ) * (2 * c.scalarConst * (N : ℝ) ^ 2 * (B : ℝ) ^ 2) +
          (R : ℝ) * (c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ)) :=
        add_le_add (add_le_add e1 e2) e3
    _ = _ := by ring

/-- **The amortization lemma.**  Under the paper's rebuild schedule —
at most one recomputation per `n` operations, `R·n ≤ T` — the
recomputation total is `matmulLeadingConst·T·n^{ω−1}·B`, the
`T s^{ω−1}` amortized term of Theorem 5.1 and equation (E.2), while the
`T` updates contribute `12·scalarConst·T·n^ω·B²` of accounted scalar work
and the `Q` queries `2·scalarConst·Q·N²·B²`. -/
theorem dynamicOps_amortized_le (c : BitCostModel) (n B N T Q R : ℕ)
    (hn : 1 ≤ n) (hB : 1 ≤ B) (hR : (R : ℝ) * (n : ℝ) ≤ (T : ℝ)) :
    (dynamicOps c n B N T Q R : ℝ) ≤
      12 * c.scalarConst * (T : ℝ) * (n : ℝ) ^ c.ω * (B : ℝ) ^ 2 +
        2 * c.scalarConst * (Q : ℝ) * (N : ℝ) ^ 2 * (B : ℝ) ^ 2 +
        c.matmulLeadingConst * (T : ℝ) * (n : ℝ) ^ (c.ω - 1) * (B : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) :=
    by exact_mod_cast (show (0 : ℕ) < n from by omega)
  have hpow : (n : ℝ) ^ c.ω = (n : ℝ) * (n : ℝ) ^ (c.ω - 1) := by
    have hω : c.ω = 1 + (c.ω - 1) := by ring
    conv_lhs => rw [hω]
    rw [Real.rpow_add hnpos, Real.rpow_one]
  have hnn : 0 ≤ (n : ℝ) ^ (c.ω - 1) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hCB : 0 ≤ c.matmulLeadingConst * (B : ℝ) :=
    mul_nonneg c.matmulLeadingConst_nonneg (Nat.cast_nonneg _)
  have e3 : (R : ℝ) * c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ) ≤
      c.matmulLeadingConst * (T : ℝ) * (n : ℝ) ^ (c.ω - 1) * (B : ℝ) := by
    calc (R : ℝ) * c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ)
        = (c.matmulLeadingConst * (B : ℝ) * (n : ℝ) ^ (c.ω - 1)) *
            ((R : ℝ) * (n : ℝ)) := by rw [hpow]; ring
      _ ≤ (c.matmulLeadingConst * (B : ℝ) * (n : ℝ) ^ (c.ω - 1)) * (T : ℝ) :=
          mul_le_mul_of_nonneg_left hR (mul_nonneg hCB hnn)
      _ = c.matmulLeadingConst * (T : ℝ) * (n : ℝ) ^ (c.ω - 1) *
            (B : ℝ) := by ring
  exact (dynamicOps_le c n B N T Q R hn hB).trans
    (add_le_add (add_le_add (le_refl _) (le_refl _)) e3)

/-- Total accounted bit-cost of running the maintained structure over a
run of `T` rank-one updates with `R` recomputations, including the
one-time `matmulCost` initialization (`DynamicInverseState.init`). -/
def maintenanceTotalOps (c : BitCostModel) (n B T R : ℕ) : ℕ :=
  c.matmulCost n B + T * rankOneUpdateOps c n B + R * recomputeOps c n B

/-- The packaged maintenance envelope
`(matmulLeadingConst + 12·scalarConst·B)·(T+1)·n^ω·B`: `T` updates at the
`n^ω·B²` scalar-work scale, the `T·n^{ω−1}·B` amortized recomputation
term, and the one-time `n^ω·B` initialization, merged into one product. -/
def maintenanceEnvelope (c : BitCostModel) (n B T : ℕ) : ℝ :=
  (c.matmulLeadingConst + 12 * c.scalarConst * (B : ℝ)) * ((T : ℝ) + 1) *
    (n : ℝ) ^ c.ω * (B : ℝ)

/-- **Near matrix-multiplication total work, packaged.**  Initialization
plus `T` updates plus `R` recomputations, with at most one recomputation
per `n` operations (`R·n ≤ T`), fits inside `maintenanceEnvelope`. -/
theorem maintenanceTotalOps_le (c : BitCostModel) (n B T R : ℕ)
    (hn : 1 ≤ n) (hB : 1 ≤ B) (hR : (R : ℝ) * (n : ℝ) ≤ (T : ℝ)) :
    (maintenanceTotalOps c n B T R : ℝ) ≤ maintenanceEnvelope c n B T := by
  have hnpos : (0 : ℝ) < (n : ℝ) :=
    by exact_mod_cast (show (0 : ℕ) < n from by omega)
  have hpow : (n : ℝ) ^ c.ω = (n : ℝ) * (n : ℝ) ^ (c.ω - 1) := by
    have hω : c.ω = 1 + (c.ω - 1) := by ring
    conv_lhs => rw [hω]
    rw [Real.rpow_add hnpos, Real.rpow_one]
  have hnn : 0 ≤ (n : ℝ) ^ (c.ω - 1) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hω1 : (n : ℝ) ^ (c.ω - 1) ≤ (n : ℝ) ^ c.ω :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
  have e0 : ((c.matmulCost n B : ℕ) : ℝ) ≤
      c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ) := c.matmulCost_le n B
  have e1 : (T : ℝ) * (rankOneUpdateOps c n B : ℝ) ≤
      12 * c.scalarConst * (T : ℝ) * (n : ℝ) ^ c.ω * (B : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_left (rankOneUpdateOps_le c n B hn hB)
      (Nat.cast_nonneg _)).trans (le_of_eq (by ring))
  have e2 : (R : ℝ) * (recomputeOps c n B : ℝ) ≤
      c.matmulLeadingConst * (T : ℝ) * (n : ℝ) ^ (c.ω - 1) * (B : ℝ) := by
    calc (R : ℝ) * (recomputeOps c n B : ℝ)
        ≤ (R : ℝ) * (c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ)) :=
          mul_le_mul_of_nonneg_left (recomputeOps_le c n B) (Nat.cast_nonneg _)
      _ = (c.matmulLeadingConst * (B : ℝ) * (n : ℝ) ^ (c.ω - 1)) *
            ((R : ℝ) * (n : ℝ)) := by rw [hpow]; ring
      _ ≤ (c.matmulLeadingConst * (B : ℝ) * (n : ℝ) ^ (c.ω - 1)) *
            (T : ℝ) :=
          mul_le_mul_of_nonneg_left hR (mul_nonneg (mul_nonneg
            c.matmulLeadingConst_nonneg (Nat.cast_nonneg _)) hnn)
      _ = c.matmulLeadingConst * (T : ℝ) * (n : ℝ) ^ (c.ω - 1) *
            (B : ℝ) := by ring
  have e2' : c.matmulLeadingConst * (T : ℝ) * (n : ℝ) ^ (c.ω - 1) *
        (B : ℝ) ≤
      c.matmulLeadingConst * (T : ℝ) * (n : ℝ) ^ c.ω * (B : ℝ) := by
    calc _ = (c.matmulLeadingConst * (T : ℝ) * (B : ℝ)) *
          (n : ℝ) ^ (c.ω - 1) := by ring
      _ ≤ (c.matmulLeadingConst * (T : ℝ) * (B : ℝ)) * (n : ℝ) ^ c.ω :=
          mul_le_mul_of_nonneg_left hω1
            (mul_nonneg (mul_nonneg c.matmulLeadingConst_nonneg
              (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
      _ = _ := by ring
  have hnn2 : 0 ≤ 12 * c.scalarConst * (n : ℝ) ^ c.ω * (B : ℝ) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) c.scalarConst_nonneg)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (sq_nonneg _)
  have hRHS : maintenanceEnvelope c n B T =
      c.matmulLeadingConst * (T : ℝ) * (n : ℝ) ^ c.ω * (B : ℝ) +
        c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ) +
        12 * c.scalarConst * (T : ℝ) * (n : ℝ) ^ c.ω * (B : ℝ) ^ 2 +
        12 * c.scalarConst * (n : ℝ) ^ c.ω * (B : ℝ) ^ 2 := by
    unfold maintenanceEnvelope; ring
  unfold maintenanceTotalOps
  push_cast
  rw [hRHS]
  linarith

/-- The packaged claim: for `T` rank-one updates with at most one
recomputation per `n` operations, the total accounted cost —
initialization, updates, and recomputations — stays within
`maintenanceEnvelope`.  Unlike `DiscrepancyRuntimeBound` in
`Komlos.Runtime`, this `Prop` is *proved* below; the definition only
packages the statement. -/
def DynamicMaintenanceBound (c : BitCostModel) : Prop :=
  ∀ (n B T R : ℕ), 1 ≤ n → 1 ≤ B → (R : ℝ) * (n : ℝ) ≤ (T : ℝ) →
    (maintenanceTotalOps c n B T R : ℝ) ≤ maintenanceEnvelope c n B T

/-- `DynamicMaintenanceBound` holds for every admissible bit-cost model:
this is `maintenanceTotalOps_le`. -/
theorem dynamicMaintenanceBound (c : BitCostModel) :
    DynamicMaintenanceBound c :=
  fun _n _B _T _R hn hB hR => maintenanceTotalOps_le c _ _ _ _ hn hB hR

end

end Komlos
