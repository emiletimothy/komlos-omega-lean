import Komlos.SpectralPath
import Komlos.MatrixInverse
import Komlos.NonpositiveSubspace

/-!
# The `P − D` Hessian decomposition (2.6)/(B.3)

This module identifies the second derivative of the resolvent
potential along a quadratic barrier path with the paper's curvature
decomposition `∇²F_b[h] = P[h] − D[h]`, where

* `U[h] = ∑ᵢ ν″(uᵢ)·tᵢ²·(gᵢᵀh)²`,
* `D[h] = 8·∑ᵢ ν′(uᵢ)·tᵢ²·∑ⱼ zᵢⱼhⱼ²`,
* `(Ch)ⱼ = ∑ᵢ ν′(uᵢ)·tᵢ·(gᵢᵀh)·zᵢⱼ`,
* `P[h] = U[h] + 2·(Ch)ᵀR(Ch)`,

with `tᵢ = zᵢᵀv` the row load and `R` the slack resolvent.  The main
theorem `curvature_lhs_eq_quadP_sub_quadD` rewrites the matrix-level
curvature expression `2∑ᵢⱼ(RM′RM′R)ᵢⱼ + ∑ᵢⱼ(RM″R)ᵢⱼ` — which appears
in `concaveOn_resolventPotential_quad` — as `P[h] − D[h]`.  Together
with `quadD_nonneg`, this turns the subspace bound
`P[h] ≤ (1 − ρ/2)·D[h]` of Proposition 2.1 into concavity of the
potential.
-/

namespace Komlos

open scoped Matrix

/-! ## Symmetry of the batch matrices -/

theorem isSymm_vecMulVec_self {s : ℕ} (z : Fin s → ℝ) :
    (Matrix.vecMulVec z z).IsSymm :=
  Matrix.transpose_vecMulVec z z

theorem isSymm_sum {ι : Type*} [Fintype ι] {s : ℕ}
    {f : ι → Matrix (Fin s) (Fin s) ℝ}
    (hf : ∀ i, (f i).IsSymm) : (∑ i, f i).IsSymm := by
  ext j k
  rw [Matrix.transpose_apply]
  simp only [Matrix.sum_apply]
  exact Finset.sum_congr rfl fun i _ => (hf i).apply j k

theorem isSymm_batchMatrixDeriv {m s : ℕ} (z : Fin m → Fin s → ℝ)
    (u c : Fin m → ℝ) : (batchMatrixDeriv z u c).IsSymm :=
  isSymm_sum fun i => (isSymm_vecMulVec_self (z i)).smul _

theorem isSymm_batchMatrixDeriv2Gen {m s : ℕ} (z : Fin m → Fin s → ℝ)
    (u c d : Fin m → ℝ) : (batchMatrixDeriv2Gen z u c d).IsSymm :=
  isSymm_sum fun i => (isSymm_vecMulVec_self (z i)).smul _

theorem isSymm_batchMatrix {m s : ℕ} {M0 : Matrix (Fin s) (Fin s) ℝ}
    (hM0 : M0.IsSymm) (z : Fin m → Fin s → ℝ) (u : Fin m → ℝ) :
    (batchMatrix M0 z u).IsSymm :=
  hM0.add (isSymm_sum fun i => (isSymm_vecMulVec_self (z i)).smul _)

theorem isSymm_slack {s : ℕ} (b : ℝ) {M : Matrix (Fin s) (Fin s) ℝ}
    (hM : M.IsSymm) : (slackMatrix b M).IsSymm :=
  (Matrix.isSymm_diagonal _).sub hM

theorem isSymm_resolvent {s : ℕ} (b : ℝ) {M : Matrix (Fin s) (Fin s) ℝ}
    (hM : M.IsSymm) : (slackMatrix b M)⁻¹.IsSymm :=
  (isSymm_slack b hM).inv

/-! ## Entry-sum sandwiches

The total entry sum `∑ᵢⱼ Xᵢⱼ` equals `1ᵀX1`; peeling symmetric
resolvents off both sides turns the curvature expression into
quadratic forms in `v = R1`. -/

/-- `∑ᵢⱼ Xᵢⱼ = 1 ⬝ᵥ (X1)`. -/
theorem sum_sum_eq_one_dot {s : ℕ} (X : Matrix (Fin s) (Fin s) ℝ) :
    ∑ i, ∑ j, X i j = (fun _ => (1 : ℝ)) ⬝ᵥ (X *ᵥ fun _ => 1) := by
  simp [dotProduct, Matrix.mulVec]

/-- For symmetric `R`, `1 ⬝ᵥ Rw = (R1) ⬝ᵥ w`. -/
theorem dot_one_mulVec_symm {s : ℕ} {R : Matrix (Fin s) (Fin s) ℝ}
    (hR : R.IsSymm) (w : Fin s → ℝ) :
    (fun _ => (1 : ℝ)) ⬝ᵥ (R *ᵥ w) = (R *ᵥ fun _ => 1) ⬝ᵥ w := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  congr 1
  rw [show Rᵀ = R from hR]

/-- `∑ᵢⱼ (RXR)ᵢⱼ = (R1) ⬝ᵥ X(R1)` for symmetric `R`. -/
theorem sum_sum_inv_conj {s : ℕ} {R X : Matrix (Fin s) (Fin s) ℝ}
    (hR : R.IsSymm) :
    ∑ i, ∑ j, (R * X * R) i j =
      (R *ᵥ fun _ => 1) ⬝ᵥ (X *ᵥ (R *ᵥ fun _ => 1)) := by
  rw [sum_sum_eq_one_dot]
  simp only [← Matrix.mulVec_mulVec]
  rw [dot_one_mulVec_symm hR]

/-- `∑ᵢⱼ (RXRXR)ᵢⱼ = (X(R1)) ⬝ᵥ R(X(R1))` for symmetric `R`, `X`. -/
theorem sum_sum_inv_sandwich {s : ℕ} {R X : Matrix (Fin s) (Fin s) ℝ}
    (hR : R.IsSymm) (hX : X.IsSymm) :
    ∑ i, ∑ j, (R * X * R * X * R) i j =
      (X *ᵥ (R *ᵥ fun _ => 1)) ⬝ᵥ
        (R *ᵥ (X *ᵥ (R *ᵥ fun _ => 1))) := by
  rw [sum_sum_eq_one_dot]
  simp only [← Matrix.mulVec_mulVec]
  rw [dot_one_mulVec_symm hR, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose]
  congr 1
  rw [show Xᵀ = X from hX]

/-! ## The `P − D` terms -/

/-- The barrier quadratic energy `∑ⱼ zⱼhⱼ²` — this is `qᵢ` in the row
barrier identity (2.2). -/
noncomputable def barrierQuad {s : ℕ} (z h : Fin s → ℝ) : ℝ := ∑ j, z j * h j ^ 2

/-- `U[h] = ∑ᵢ ν″(uᵢ)·(zᵢᵀv)²·(gᵢᵀh)²`, the `ν″` part of `vᵀM″v`. -/
noncomputable def quadU {m s : ℕ} (z g : Fin m → Fin s → ℝ) (u : Fin m → ℝ)
    (v h : Fin s → ℝ) : ℝ :=
  ∑ i, weightDeriv2 (u i) * (z i ⬝ᵥ v) ^ 2 * (g i ⬝ᵥ h) ^ 2

/-- `D[h] = 8·∑ᵢ ν′(uᵢ)·(zᵢᵀv)²·∑ⱼ zᵢⱼhⱼ²`, the negative diagonal
curvature contribution from the barrier's quadratic energy. -/
noncomputable def quadD {m s : ℕ} (z : Fin m → Fin s → ℝ) (u : Fin m → ℝ)
    (v h : Fin s → ℝ) : ℝ :=
  8 * ∑ i, weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2 * barrierQuad (z i) h

/-- `Ch ∈ ℝˢ` with `(Ch)ⱼ = ∑ᵢ ν′(uᵢ)·(zᵢᵀv)·(gᵢᵀh)·zᵢⱼ`; this is
exactly `M′[h]·v` for the direction `h`. -/
noncomputable def quadCvec {m s : ℕ} (z g : Fin m → Fin s → ℝ) (u : Fin m → ℝ)
    (v h : Fin s → ℝ) : Fin s → ℝ :=
  fun j => ∑ i, weightDeriv (u i) * (z i ⬝ᵥ v) * (g i ⬝ᵥ h) * z i j

/-- `P[h] = U[h] + 2·(Ch)ᵀR(Ch)`, the positive curvature term. -/
noncomputable def quadP {m s : ℕ} (z g : Fin m → Fin s → ℝ) (u : Fin m → ℝ)
    (v h : Fin s → ℝ) (R : Matrix (Fin s) (Fin s) ℝ) : ℝ :=
  quadU z g u v h + 2 * (quadCvec z g u v h ⬝ᵥ (R *ᵥ quadCvec z g u v h))

/-! ## Identification with the pathwise second derivative -/

/-- `(∑ᵢ wᵢ·zᵢzᵢᵀ)·v` entrywise: `(Sv)ⱼ = ∑ᵢ wᵢ·(zᵢᵀv)·zᵢⱼ`. -/
theorem smulGram_mulVec {m s : ℕ} (z : Fin m → Fin s → ℝ)
    (w : Fin m → ℝ) (v : Fin s → ℝ) :
    (∑ i, w i • Matrix.vecMulVec (z i) (z i)) *ᵥ v =
      fun j => ∑ i, w i * (z i ⬝ᵥ v) * z i j := by
  funext j
  simp_rw [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show w i * (∑ k : Fin s, z i k * v k) * z i j =
      w i * z i j * (∑ k : Fin s, z i k * v k) from by ring]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- `vᵀ(∑ᵢ wᵢ·zᵢzᵢᵀ)v = ∑ᵢ wᵢ·(zᵢᵀv)²`. -/
theorem dot_smulGram_mulVec {m s : ℕ} (z : Fin m → Fin s → ℝ)
    (w : Fin m → ℝ) (v : Fin s → ℝ) :
    v ⬝ᵥ ((∑ i, w i • Matrix.vecMulVec (z i) (z i)) *ᵥ v) =
      ∑ i, w i * (z i ⬝ᵥ v) ^ 2 := by
  rw [smulGram_mulVec]
  simp only [dotProduct]
  have hexp : ∀ j : Fin s,
      v j * (∑ i, w i * (∑ k, z i k * v k) * z i j) =
        ∑ i, v j * (w i * (∑ k, z i k * v k) * z i j) :=
    fun j => by rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun j _ => hexp j]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hc : ∀ j : Fin s,
      v j * (w i * (∑ k, z i k * v k) * z i j) =
        (v j * z i j) * (w i * ∑ k, z i k * v k) := fun j => by ring
  rw [Finset.sum_congr rfl fun j _ => hc j, ← Finset.sum_mul]
  rw [Finset.sum_congr rfl fun j _ => mul_comm (v j) (z i j)]
  ring

/-- `M′·v = Ch` as vectors. -/
theorem batchMatrixDeriv_mulVec_eq_quadCvec {m s : ℕ}
    (z g : Fin m → Fin s → ℝ) (u : Fin m → ℝ) (v h : Fin s → ℝ) :
    batchMatrixDeriv z u (fun i => g i ⬝ᵥ h) *ᵥ v =
      quadCvec z g u v h := by
  unfold batchMatrixDeriv quadCvec
  rw [smulGram_mulVec]
  funext j
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `vᵀM″v = U[h] − D[h]` when `M″` is evaluated on the quadratic
barrier path with `dᵢ = 4·∑ⱼ zᵢⱼhⱼ²` (so `uᵢ″ = −2dᵢ = −8·qᵢ`). -/
theorem dot_batchMatrixDeriv2Gen_mulVec_eq {m s : ℕ}
    (z g : Fin m → Fin s → ℝ) (u : Fin m → ℝ) (v h : Fin s → ℝ) :
    v ⬝ᵥ (batchMatrixDeriv2Gen z u (fun i => g i ⬝ᵥ h)
        (fun i => -(2 * (4 * barrierQuad (z i) h))) *ᵥ v) =
      quadU z g u v h - quadD z u v h := by
  unfold batchMatrixDeriv2Gen quadU quadD
  rw [dot_smulGram_mulVec, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The curvature identity.** For symmetric `M`, the matrix-level
second-derivative expression of the resolvent potential along the
quadratic barrier path with slopes `cᵢ = gᵢᵀh` and quadratic
coefficients `dᵢ = 4·∑ⱼzᵢⱼhⱼ²` equals `P[h] − D[h]` of (2.6). -/
theorem curvature_lhs_eq_quadP_sub_quadD {m s : ℕ} (b : ℝ)
    {M : Matrix (Fin s) (Fin s) ℝ} (hM : M.IsSymm)
    (z g : Fin m → Fin s → ℝ) (u : Fin m → ℝ) (h : Fin s → ℝ) :
    2 * ∑ p : Fin s, ∑ q : Fin s,
        ((slackMatrix b M)⁻¹ *
          batchMatrixDeriv z u (fun i => g i ⬝ᵥ h) *
          (slackMatrix b M)⁻¹ *
          batchMatrixDeriv z u (fun i => g i ⬝ᵥ h) *
          (slackMatrix b M)⁻¹) p q +
      ∑ p : Fin s, ∑ q : Fin s,
        ((slackMatrix b M)⁻¹ *
          batchMatrixDeriv2Gen z u (fun i => g i ⬝ᵥ h)
            (fun i => -(2 * (4 * barrierQuad (z i) h))) *
          (slackMatrix b M)⁻¹) p q =
      quadP z g u ((slackMatrix b M)⁻¹ *ᵥ fun _ => 1) h
          (slackMatrix b M)⁻¹ -
        quadD z u ((slackMatrix b M)⁻¹ *ᵥ fun _ => 1) h := by
  have hR := isSymm_resolvent b hM
  have hM' := isSymm_batchMatrixDeriv z u (fun i => g i ⬝ᵥ h)
  rw [sum_sum_inv_sandwich hR hM', sum_sum_inv_conj hR,
    batchMatrixDeriv_mulVec_eq_quadCvec,
    dot_batchMatrixDeriv2Gen_mulVec_eq]
  unfold quadP
  ring

/-- `D[h] ≥ 0` when `z` is entrywise nonnegative and every barrier is
nonpositive (so `ν′(uᵢ) > 0`). -/
theorem quadD_nonneg {m s : ℕ} {z : Fin m → Fin s → ℝ}
    {u : Fin m → ℝ} {v h : Fin s → ℝ}
    (hz : ∀ i j, 0 ≤ z i j) (hu : ∀ i, u i ≤ 0) : 0 ≤ quadD z u v h := by
  unfold quadD barrierQuad
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  apply mul_nonneg (weightDeriv_pos (hu i)).le
  exact sq_nonneg _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hz i j) (sq_nonneg _)

/-- **Curvature nonpositivity from the subspace bound.** If
`P[h] ≤ (1 − ρ/2)·D[h]` with `ρ ≥ 0` and `D[h] ≥ 0` holds on the
window, the matrix-level curvature expression `2∑∑(RM′RM′R) + ∑∑(RM″R)`
is nonpositive — the hypothesis needed by
`concaveOn_resolventPotential_quad`. -/
theorem curvature_lhs_nonpos_of_quadP_le {m s : ℕ} (b : ℝ)
    {M : Matrix (Fin s) (Fin s) ℝ} (hM : M.IsSymm)
    {z g : Fin m → Fin s → ℝ} {u : Fin m → ℝ} {h : Fin s → ℝ} {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hz : ∀ i j, 0 ≤ z i j) (hu : ∀ i, u i ≤ 0)
    (hPD : quadP z g u ((slackMatrix b M)⁻¹ *ᵥ fun _ => 1) h
        (slackMatrix b M)⁻¹ ≤
      (1 - ρ / 2) *
        quadD z u ((slackMatrix b M)⁻¹ *ᵥ fun _ => 1) h) :
    2 * ∑ p : Fin s, ∑ q : Fin s,
        ((slackMatrix b M)⁻¹ *
          batchMatrixDeriv z u (fun i => g i ⬝ᵥ h) *
          (slackMatrix b M)⁻¹ *
          batchMatrixDeriv z u (fun i => g i ⬝ᵥ h) *
          (slackMatrix b M)⁻¹) p q +
      ∑ p : Fin s, ∑ q : Fin s,
        ((slackMatrix b M)⁻¹ *
          batchMatrixDeriv2Gen z u (fun i => g i ⬝ᵥ h)
            (fun i => -(2 * (4 * barrierQuad (z i) h))) *
          (slackMatrix b M)⁻¹) p q ≤ 0 := by
  rw [curvature_lhs_eq_quadP_sub_quadD b hM z g u h]
  have hD : 0 ≤ quadD z u ((slackMatrix b M)⁻¹ *ᵥ fun _ => 1) h :=
    quadD_nonneg hz hu
  have hle : (1 - ρ / 2) *
        quadD z u ((slackMatrix b M)⁻¹ *ᵥ fun _ => 1) h ≤
      quadD z u ((slackMatrix b M)⁻¹ *ᵥ fun _ => 1) h := by
    have h2 : 0 ≤ (ρ / 2) *
        quadD z u ((slackMatrix b M)⁻¹ *ᵥ fun _ => 1) h :=
      mul_nonneg (by linarith) hD
    calc (1 - ρ / 2) * quadD z u ((slackMatrix b M)⁻¹ *ᵥ fun _ => 1) h
        = quadD z u ((slackMatrix b M)⁻¹ *ᵥ fun _ => 1) h -
          (ρ / 2) * quadD z u ((slackMatrix b M)⁻¹ *ᵥ fun _ => 1) h := by
          ring
      _ ≤ quadD z u ((slackMatrix b M)⁻¹ *ᵥ fun _ => 1) h := by linarith
  linarith

/-! ## Matrix-level `U`, `C`, `D`, `P` and the subspace corollary

The scalar quadratic forms `quadU`, `quadD`, `quadCvec`, `quadP` are
`hᵀUh`, `hᵀDh`, `Ch`, `hᵀPh` for explicit matrices — needed to apply
`exists_nonpositive_subspace_of_trace`. -/

/-- `(∑ᵢ wᵢ·aᵢbᵢᵀ)·v` entrywise: `(Sv)ⱼ = ∑ᵢ wᵢ·(bᵢᵀv)·aᵢⱼ`. -/
theorem smulOuter_mulVec {m s : ℕ} (a b : Fin m → Fin s → ℝ)
    (w : Fin m → ℝ) (v : Fin s → ℝ) :
    (∑ i, w i • Matrix.vecMulVec (a i) (b i)) *ᵥ v =
      fun j => ∑ i, w i * (b i ⬝ᵥ v) * a i j := by
  funext j
  simp_rw [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [show w i * (∑ k : Fin s, b i k * v k) * a i j =
      w i * a i j * (∑ k : Fin s, b i k * v k) from by ring]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- `U = ∑ᵢ ν″(uᵢ)·(zᵢᵀv)²·gᵢgᵢᵀ` as a matrix. -/
noncomputable def Umat {m s : ℕ} (z g : Fin m → Fin s → ℝ)
    (u : Fin m → ℝ) (v : Fin s → ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  ∑ i, (weightDeriv2 (u i) * (z i ⬝ᵥ v) ^ 2) •
    Matrix.vecMulVec (g i) (g i)

/-- `C = ∑ᵢ ν′(uᵢ)·(zᵢᵀv)·zᵢgᵢᵀ` as a matrix. -/
noncomputable def Cmat {m s : ℕ} (z g : Fin m → Fin s → ℝ)
    (u : Fin m → ℝ) (v : Fin s → ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  ∑ i, (weightDeriv (u i) * (z i ⬝ᵥ v)) •
    Matrix.vecMulVec (z i) (g i)

/-- `D = 8·∑ᵢ ν′(uᵢ)·(zᵢᵀv)²·diag(zᵢ)` as a diagonal matrix. -/
noncomputable def Dmat {m s : ℕ} (z : Fin m → Fin s → ℝ)
    (u : Fin m → ℝ) (v : Fin s → ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  Matrix.diagonal fun j =>
    8 * ∑ i, weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2 * z i j

/-- `P = U + 2CᵀRC` as a matrix. -/
noncomputable def Pmat {m s : ℕ} (z g : Fin m → Fin s → ℝ)
    (u : Fin m → ℝ) (v : Fin s → ℝ) (R : Matrix (Fin s) (Fin s) ℝ) :
    Matrix (Fin s) (Fin s) ℝ :=
  Umat z g u v + (2 : ℝ) • ((Cmat z g u v)ᵀ * R * Cmat z g u v)

/-- `hᵀUh = U[h]`. -/
theorem dot_Umat_eq_quadU {m s : ℕ} (z g : Fin m → Fin s → ℝ)
    (u : Fin m → ℝ) (v h : Fin s → ℝ) :
    h ⬝ᵥ (Umat z g u v *ᵥ h) = quadU z g u v h := by
  unfold Umat quadU
  rw [dot_smulGram_mulVec]

/-- `Ch = C·h` as vectors. -/
theorem Cmat_mulVec_eq_quadCvec {m s : ℕ} (z g : Fin m → Fin s → ℝ)
    (u : Fin m → ℝ) (v h : Fin s → ℝ) :
    Cmat z g u v *ᵥ h = quadCvec z g u v h := by
  unfold Cmat quadCvec
  rw [smulOuter_mulVec]

/-- Swapping a constant-scaled double sum. -/
theorem sum_const_mul_eq {m s : ℕ} (a : ℝ)
    (w : Fin m → ℝ) (f : Fin m → Fin s → ℝ) (g : Fin s → ℝ) :
    ∑ j : Fin s, (a * ∑ i : Fin m, w i * f i j) * g j =
      a * ∑ i : Fin m, w i * ∑ j : Fin s, f i j * g j := by
  conv_lhs =>
    enter [2, j]
    rw [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs =>
    rw [Finset.mul_sum]
    enter [2, i]
    rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- `hᵀDh = D[h]`. -/
theorem dot_Dmat_eq_quadD {m s : ℕ} (z : Fin m → Fin s → ℝ)
    (u : Fin m → ℝ) (v h : Fin s → ℝ) :
    h ⬝ᵥ (Dmat z u v *ᵥ h) = quadD z u v h := by
  have hlhs : h ⬝ᵥ (Dmat z u v *ᵥ h) =
      ∑ j : Fin s, (8 * ∑ i, weightDeriv (u i) *
        (z i ⬝ᵥ v) ^ 2 * z i j) * h j ^ 2 := by
    simp only [Dmat, dotProduct, Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hlhs]
  unfold quadD barrierQuad
  exact sum_const_mul_eq 8
    (fun i => weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2)
    (fun i j => z i j) (fun j => h j ^ 2)

/-- `hᵀP h = P[h]` for the matrix `P = U + 2CᵀRC`. -/
theorem dot_Pmat_eq_quadP {m s : ℕ} (z g : Fin m → Fin s → ℝ)
    (u : Fin m → ℝ) (v h : Fin s → ℝ) (R : Matrix (Fin s) (Fin s) ℝ) :
    h ⬝ᵥ (Pmat z g u v R *ᵥ h) = quadP z g u v h R := by
  unfold Pmat quadP
  rw [Matrix.add_mulVec, dotProduct_add, dot_Umat_eq_quadU]
  congr 1
  rw [Matrix.smul_mulVec, dotProduct_smul]
  show (2 : ℝ) * (h ⬝ᵥ ((Cmat z g u v)ᵀ * R * Cmat z g u v) *ᵥ h) =
    2 * quadCvec z g u v h ⬝ᵥ R *ᵥ quadCvec z g u v h
  congr 1
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [Cmat_mulVec_eq_quadCvec]

/-- A Gram matrix `vvᵀ` is positive semidefinite. -/
theorem posSemidef_vecMulVec_self {s : ℕ} (g : Fin s → ℝ) :
    (Matrix.vecMulVec g g).PosSemidef := by
  simpa [star_trivial] using Matrix.posSemidef_vecMulVec_self_star g

/-- `U` is positive semidefinite on nonpositive barriers. -/
theorem posSemidef_Umat {m s : ℕ} (z g : Fin m → Fin s → ℝ)
    (u : Fin m → ℝ) (v : Fin s → ℝ)
    (hu : ∀ i, u i ≤ 0) : (Umat z g u v).PosSemidef := by
  have hs' : ∀ s' : Finset (Fin m), (∑ i ∈ s',
      (weightDeriv2 (u i) * (z i ⬝ᵥ v) ^ 2) •
        Matrix.vecMulVec (g i) (g i)).PosSemidef := by
    intro s'
    induction s' using Finset.induction with
    | empty => simpa using Matrix.PosSemidef.zero
    | @insert a s' ha ih =>
      rw [Finset.sum_insert ha]
      exact ((posSemidef_vecMulVec_self (g a)).smul
        (mul_nonneg (weightDeriv2_pos (hu a)).le (sq_nonneg _))).add ih
  exact hs' Finset.univ

/-- `CᵀRC` is positive semidefinite when `R` is. -/
theorem posSemidef_Cmat_conj {m s : ℕ} (z g : Fin m → Fin s → ℝ)
    (u : Fin m → ℝ) (v : Fin s → ℝ) {R : Matrix (Fin s) (Fin s) ℝ}
    (hR : R.PosSemidef) :
    ((Cmat z g u v)ᵀ * R * Cmat z g u v).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · apply Matrix.isHermitian_iff_isSymm.mpr
    show ((Cmat z g u v)ᵀ * R * Cmat z g u v)ᵀ = _
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose]
    rw [show Rᵀ = R from Matrix.isHermitian_iff_isSymm.mp hR.isHermitian]
    rw [Matrix.mul_assoc]
  · intro x
    rw [star_trivial]
    simp only [← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    simpa only [star_trivial] using
      hR.dotProduct_mulVec_nonneg (Cmat z g u v *ᵥ x)

/-- `P` is positive semidefinite on nonpositive barriers when `R` is
positive semidefinite — the hypothesis of
`exists_nonpositive_subspace_of_trace`. -/
theorem posSemidef_Pmat {m s : ℕ} (z g : Fin m → Fin s → ℝ)
    (u : Fin m → ℝ) (v : Fin s → ℝ) {R : Matrix (Fin s) (Fin s) ℝ}
    (hR : R.PosSemidef) (hu : ∀ i, u i ≤ 0) :
    (Pmat z g u v R).PosSemidef :=
  (posSemidef_Umat z g u v hu).add
    (Matrix.PosSemidef.smul (posSemidef_Cmat_conj z g u v hR)
      (show (0 : ℝ) ≤ (2 : ℝ) by norm_num))

/-- `D` is a nonnegative diagonal matrix on nonpositive barriers with
nonnegative `z`. -/
theorem isDiag_Dmat {m s : ℕ} (z : Fin m → Fin s → ℝ)
    (u : Fin m → ℝ) (v : Fin s → ℝ) :
    Matrix.IsDiag (Dmat z u v) :=
  Matrix.isDiag_diagonal _

theorem Dmat_diag_nonneg {m s : ℕ} {z : Fin m → Fin s → ℝ}
    {u : Fin m → ℝ} {v : Fin s → ℝ}
    (hz : ∀ i j, 0 ≤ z i j) (hu : ∀ i, u i ≤ 0) :
    ∀ j, 0 ≤ Dmat z u v j j := by
  intro j
  unfold Dmat
  rw [Matrix.diagonal_apply, ite_eq_left rfl]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg
    (mul_nonneg (weightDeriv_pos (hu i)).le (sq_nonneg _)) (hz i j)

/-- **The valid subspace exists (Proposition 2.1, existence part).**
If the anchor diagonal bound `P₀ⱼⱼ ≤ θ·(1−ρ)·D₀ⱼⱼ` holds and `R` is
positive semidefinite, there is a subspace of dimension at least
`s − θs` on which `P[h] ≤ (1−ρ)·D[h]`. -/
theorem exists_subspace_quadP_le {m s : ℕ} {θ ρ : ℝ}
    {z g : Fin m → Fin s → ℝ} {u : Fin m → ℝ} {v : Fin s → ℝ}
    {R : Matrix (Fin s) (Fin s) ℝ}
    (hR : R.PosSemidef) (hθ : 0 ≤ θ) (hρ : ρ ≤ 1)
    (hz : ∀ i j, 0 ≤ z i j) (hu : ∀ i, u i ≤ 0)
    (hQD : ∀ j, Pmat z g u v R j j ≤ θ * ((1 - ρ) • Dmat z u v) j j) :
    ∃ E : Submodule ℝ (Fin s → ℝ),
      (s : ℝ) - θ * s ≤ Module.finrank ℝ E ∧
      ∀ h ∈ E, quadP z g u v h R ≤ (1 - ρ) * quadD z u v h := by
  obtain ⟨E, hEdim, hE⟩ := exists_nonpositive_subspace_of_trace
    (Pmat z g u v R) ((1 - ρ) • Dmat z u v)
    (posSemidef_Pmat z g u v hR hu) hθ
    (fun j => smul_nonneg (sub_nonneg.mpr hρ) (Dmat_diag_nonneg hz hu j))
    ((isDiag_Dmat z u v).smul _) hQD
  refine ⟨E, hEdim, fun h hh => ?_⟩
  have h := hE h hh
  rw [Matrix.sub_mulVec, dotProduct_sub, dot_Pmat_eq_quadP,
    Matrix.smul_mulVec, dotProduct_smul, dot_Dmat_eq_quadD] at h
  exact sub_nonpos.mp h

/-- **Subspace concavity (the geometric core of Proposition 2.1).**
If the slack resolvent `R = (bI − M)⁻¹` is positive definite and the
anchor diagonal bound `P₀ⱼⱼ ≤ θ·(1−ρ)·D₀ⱼⱼ` holds, there is a
subspace `E` of dimension at least `s − θs` such that for every
`h ∈ E` the matrix-level curvature expression of the resolvent
potential along the quadratic barrier path is nonpositive — the
hypothesis of `concaveOn_resolventPotential_quad`. -/
theorem exists_subspace_curvature_lhs_nonpos {m s : ℕ} (b : ℝ)
    {θ ρ : ℝ} {M : Matrix (Fin s) (Fin s) ℝ} (hM : M.IsSymm)
    {z g : Fin m → Fin s → ℝ} {u : Fin m → ℝ}
    (hpos : (slackMatrix b M).PosDef)
    (hθ : 0 ≤ θ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hz : ∀ i j, 0 ≤ z i j) (hu : ∀ i, u i ≤ 0)
    (hQD : ∀ j, Pmat z g u ((slackMatrix b M)⁻¹ *ᵥ fun _ => 1)
        ((slackMatrix b M)⁻¹) j j ≤
      θ * ((1 - ρ) •
        Dmat z u ((slackMatrix b M)⁻¹ *ᵥ fun _ => 1)) j j) :
    ∃ E : Submodule ℝ (Fin s → ℝ),
      (s : ℝ) - θ * s ≤ Module.finrank ℝ E ∧
      ∀ h ∈ E,
        2 * ∑ p : Fin s, ∑ q : Fin s,
            ((slackMatrix b M)⁻¹ *
              batchMatrixDeriv z u (fun i => g i ⬝ᵥ h) *
              (slackMatrix b M)⁻¹ *
              batchMatrixDeriv z u (fun i => g i ⬝ᵥ h) *
              (slackMatrix b M)⁻¹) p q +
          ∑ p : Fin s, ∑ q : Fin s,
            ((slackMatrix b M)⁻¹ *
              batchMatrixDeriv2Gen z u (fun i => g i ⬝ᵥ h)
                (fun i => -(2 * (4 * barrierQuad (z i) h))) *
              (slackMatrix b M)⁻¹) p q ≤ 0 := by
  obtain ⟨E, hEdim, hE⟩ := exists_subspace_quadP_le
    (v := (slackMatrix b M)⁻¹ *ᵥ fun _ => 1)
    (R := (slackMatrix b M)⁻¹) hpos.inv.posSemidef hθ hρ1 hz hu hQD
  refine ⟨E, hEdim, fun h hh => ?_⟩
  have hD : 0 ≤ quadD z u ((slackMatrix b M)⁻¹ *ᵥ fun _ => 1) h :=
    quadD_nonneg hz hu
  have hle : quadP z g u ((slackMatrix b M)⁻¹ *ᵥ fun _ => 1) h
        (slackMatrix b M)⁻¹ ≤
      (1 - ρ / 2) * quadD z u ((slackMatrix b M)⁻¹ *ᵥ fun _ => 1) h := by
    refine le_trans (hE h hh) (mul_le_mul_of_nonneg_right ?_ hD)
    linarith
  exact curvature_lhs_nonpos_of_quadP_le b hM hρ0 hz hu hle

/-- **Window concavity from the transported curvature bound.**
If the quadratic-form bound `Pₜ[h] ≤ (1−ρ)·Dₜ[h]` holds for the
direction `h` at every interior `t` of the window — the conclusion of
the paper's stability-transport step, where `gᵢ(t)` is any family of
effective directions with `gᵢ(t)ᵀh = uᵢ'(t) = cᵢ − 2t·dᵢ` — then the
resolvent potential is concave along the quadratic barrier path
`t ↦ M(x₀ + t·h)`. -/
theorem concaveOn_of_transported_bound {m s : ℕ} (b : ℝ)
    {ρ lo hi : ℝ} {M0 : Matrix (Fin s) (Fin s) ℝ} (hM0 : M0.IsSymm)
    {z : Fin m → Fin s → ℝ} {u c d : Fin m → ℝ} {h : Fin s → ℝ}
    {gT : ℝ → Fin m → Fin s → ℝ}
    (hgT : ∀ t i, gT t i ⬝ᵥ h = c i - 2 * t * d i)
    (hd : ∀ i, d i = 4 * barrierQuad (z i) h)
    (hρ : 0 ≤ ρ) (hz : ∀ i j, 0 ≤ z i j)
    (hpole : ∀ t ∈ Set.Icc lo hi, ∀ i,
      (1 - (u i + t * c i - t ^ 2 * d i) / 20000) ≠ 0)
    (hunit : ∀ t ∈ Set.Icc lo hi,
      IsUnit (slackMatrix b (batchMatrix M0 z
        (fun i => u i + t * c i - t ^ 2 * d i))))
    (huT : ∀ t ∈ Set.Ioo lo hi, ∀ i,
      u i + t * c i - t ^ 2 * d i ≤ 0)
    (htrans : ∀ t ∈ Set.Ioo lo hi,
      quadP z (gT t) (fun i => u i + t * c i - t ^ 2 * d i)
        ((slackMatrix b (batchMatrix M0 z
          (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *ᵥ fun _ => 1) h
        (slackMatrix b (batchMatrix M0 z
          (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ ≤
      (1 - ρ) * quadD z (fun i => u i + t * c i - t ^ 2 * d i)
        ((slackMatrix b (batchMatrix M0 z
          (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *ᵥ fun _ => 1) h) :
    ConcaveOn ℝ (Set.Icc lo hi)
      (fun t => resolventPotential b
        (batchMatrix M0 z (fun i => u i + t * c i - t ^ 2 * d i))) := by
  apply concaveOn_resolventPotential_quad b M0 z u c d lo hi hpole hunit
  intro t ht
  have hd' : (fun i => -(2 * d i)) =
      (fun i => -(2 * (4 * barrierQuad (z i) h))) :=
    funext fun i => by rw [hd i]
  have hc' : (fun i => c i - 2 * t * d i) =
      (fun i => gT t i ⬝ᵥ h) :=
    funext fun i => (hgT t i).symm
  rw [hd', hc', curvature_lhs_eq_quadP_sub_quadD b
    (isSymm_batchMatrix hM0 z _) z (gT t)
    (fun i => u i + t * c i - t ^ 2 * d i) h]
  have hD : 0 ≤ quadD z (fun i => u i + t * c i - t ^ 2 * d i)
      ((slackMatrix b (batchMatrix M0 z
        (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *ᵥ fun _ => 1) h :=
    quadD_nonneg hz (huT t ht)
  have h1 : (1 - ρ) * quadD z (fun i => u i + t * c i - t ^ 2 * d i)
      ((slackMatrix b (batchMatrix M0 z
        (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *ᵥ fun _ => 1) h ≤
      quadD z (fun i => u i + t * c i - t ^ 2 * d i)
      ((slackMatrix b (batchMatrix M0 z
        (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *ᵥ fun _ => 1) h := by
    have := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) - ρ ≤ 1 by linarith) hD
    rwa [one_mul] at this
  linarith [htrans t ht]

end Komlos
