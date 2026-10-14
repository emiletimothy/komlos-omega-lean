import Komlos.Curvature
import Komlos.NonpositiveSubspace
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Appendix B: spectral dimension, stability, and curvature bookkeeping

This module develops the verified parts of Appendix B of the Anand–Chen
manuscript (*The Komlós Problem in Near Matrix-Multiplication Time*) on top of
`Komlos.MatrixInverse`, `Komlos.Resolvent`, `Komlos.Curvature`, and `Komlos`.

## Fully proved

* `batchPerturbation` and its algebra: the batch update matrix
  `∑ᵢ cᵢ zᵢ zᵢᵀ` used for multi-row updates, with entrywise/symmetry/`mulVec`
  lemmas (`rankOne`, `rankOne_mulVec`, `batchPerturbation_mulVec`).
* The exact resolvent step and resolvent-potential step identities used to
  derive equation (B.3):
  - `resolvent_step_eq`: `v_{M+tN} − v_M = t · (bI − M − tN)⁻¹ N v_M`,
    the exact form of `v' = R M' v`.
  - `resolventPotential_step`: `F_b(M+tN) − F_b(M) = t · v_{M+tN}ᵀ N v_M`,
    the exact (difference-quotient) form of `F' = vᵀ M' v`.
  - `resolventPotential_step_taylor`: the exact second-order expansion
    `F_b(M+tN) − F_b(M) = t · v_Mᵀ N v_M + t² · (Nv_M)ᵀ R_t (Nv_M)`,
    which is (B.3)'s `F'' = 2(M'v)ᵀR(M'v)` in integrated form (the
    `vᵀM''v` term vanishes because the path is affine).
  - `resolventPotential_symmetric_difference` and
    `resolventPotential_midpoint_le`: the centred second difference equals
    `t²` times the two one-sided curvature quadratic forms, and nonpositivity
    of their sum gives midpoint concavity along the line.
* `resolventVariation1` (`vᵀNv`, the first-variation scalar),
  `resolventVariation2` (`2(Nv)ᵀR(Nv)`, the second-variation scalar), and
  `resolventVariation1_batch`: for the batch update the first variation is the
  weighted Gram energy `∑ᵢ cᵢ (zᵢᵀv)²`.
* Stability estimates (the (B.5) content):
  - `batch_mulVec_bound`: `|(ΔM v)ⱼ| ≤ η ∑ᵢ νᵢ (zᵢᵀv) zᵢⱼ` when
    `|Δcᵢ| ≤ η νᵢ` and everything is nonnegative.
  - `resolvent_vector_batch_relative_change`,
    `resolvent_vector_batch_relative_bounds`,
    `resolventPotential_batch_change`: pointwise relative resolvent and
    potential perturbation bounds under a batch update, via
    `resolvent_vector_relative_change`.
  - `weight_abs_sub_le`: the two-sided exponential weight-change factor,
    `|ν(u) − ν(u₀)| ≤ (e^{a/2} − 1) ν(u₀)` for `|u − u₀| ≤ a`.
  - `weight_neg_one_gt`: the numerical bound `ν(−1) > 357/5`, obtained from
    `one_sub_inv_pow_le_exp` and `exp(1) < 2.7182818286` (`Real.exp_one_lt_d9`).
* Curvature comparisons:
  - `udiag_curvature_le`: the second-derivative diagonal satisfies
    `ν''ᵢ tᵢ² zᵢⱼ² ≤ (1+1/10000)/4 · (D₀)ⱼⱼ`-type bound used to control
    `U₀` by `D₀` in Appendix B.
  - `gradient_drift_sq_le` and `curvature_drift_le`: the Cauchy–Schwarz
    gradient-drift bounds `(∑ⱼ 8 zⱼ yⱼ hⱼ)² ≤ 64 a² ∑ⱼ zⱼ hⱼ²` and its
    `ν''/ν'` summed version controlling the `(1+1/10000)` loss.
  - `light_gram_resolvent_form_le`: under the load hypothesis
    `∑ᵢ ν'ᵢ tᵢ² (Aᵢᵀv) Aᵢⱼ ≤ κ`, the resolvent-transported quadratic form
    satisfies `∑ᵢ ν'ᵢ tᵢ² (Aᵢᵀ R x)² ≤ κ · xᵀ R x`; this is the
    "`R^{1/2} Σ R^{1/2} ⪯ κ I`" content used in stability arguments.
  - `resolvent_mulVec_le_max`: `(Rh)ⱼ ≤ vⱼ · max_k hₖ` for nonnegative `h`,
    using inverse positivity (`R ≥ 0` entrywise) and `1ᵀR = v`.
* Dimension bookkeeping for the spectral-subspace claim (the (B.4) content):
  - `large_row_count` (from `live_row_count`), `nearly_tight_row_count`,
    `heavy_row_count`, `four_loss_card`, `spectral_dimension_margin`:
    the four explicit losses together with the fifth potential-loss term
    are bounded by `(31/32)·s` using `curvature_dimension_margin`.
  - `constraintMap`, `mem_ker_constraintMap`,
    `finrank_ker_constraintMap_ge`, `finrank_inf_ker_constraintMap_ge`:
    intersecting a subspace with the kernel of `k` linear constraints costs
    at most `k` dimensions.
  - `spectral_subspace_exists`, `spectral_subspace_dimension`:
    a conditional version of the paper's `dim > s/32` subspace claim.  Given a
    starting subspace `E₀` of dimension at least `(1 − μ₅) s` on which the
    curvature bound `hᵀQh ≤ (1−ρ) hᵀDh` holds, and at most
    `(μ₁+μ₂+μ₃+μ₄) s` linear constraints, there is a subspace of dimension
    strictly greater than `s/32` satisfying both properties.
* `posSemidef_two_quad` / `posSemidef_eq_zero_of_diag`: the standard
  two-dimensional quadratic-form argument: a positive-semidefinite matrix
  with a vanishing diagonal entry has a vanishing row/column.
  `matrix_inverse_entry_sq_le` is the resulting `Rjk² ≤ Rjj Rkk` bound for the
  inverse (stated for a general positive-semidefinite matrix; not required
  downstream, but standard).

## Proved only conditionally

The paper's `F' = vᵀM'v` and `F'' = vᵀM''v + 2(M'v)ᵀR(M'v)` are also stated as
genuine `HasDerivAt` statements:

* `hasDerivAt_resolventPotential`: along the affine path `t ↦ M + tN`,
  `F_b` has derivative `v_Mᵀ N v_M` at `0`, provided
  `slackMatrix b (M + t•N)` is positive definite in a neighbourhood of `0`
  and `t ↦ (bI − M − tN)⁻¹` is continuous at `0` (entrywise).
* `hasDerivAt_resolventQuadraticForm`: along the same path,
  `t ↦ v_tᵀ N v_t` has derivative `2 (Nv_M)ᵀ R (Nv_M)` at `0`, provided `N` is
  symmetric plus the same positive-definiteness/continuity hypotheses.  This is
  exactly `F''` for an affine path.
* `potentialSlope` / `potentialHessian` and
  `hasDerivAt_potentialSlope`: along the quadratic path
  `M(t) = M + tN₁ + t²N₂` (so `M'(0) = N₁`, `M''(0) = 2N₂`), the slope
  `v_tᵀ (N₁ + 2tN₂) v_t` has derivative
  `2 v₀ᵀN₂v₀ + 2 (N₁v₀)ᵀR(N₁v₀) = vᵀM''v + 2(M'v)ᵀR(M'v)` at `0`, provided the
  matrices are symmetric and again positive definiteness and entrywise
  continuity of the inverse are assumed.

The exact hypotheses are the missing analytic facts: Mathlib's matrix inverse
has no continuity/smoothness API, so they are carried as hypotheses rather than
proved.  The algebraic content (the difference-quotient identities) is proved
unconditionally.

## Omitted (missing Mathlib infrastructure)

* Loewner-order monotonicity `X ⪯ Y ⟹ X⁻¹ ⪰ Y⁻¹` of the inverse, and the
  positive-square-root construction `R^{1/2}` used in the paper's
  "`‖R^{1/2}ΣR^{1/2}‖`" notation.  `light_gram_resolvent_form_le` formalizes
  the corresponding quadratic-form consequence directly.
* The operator norm `‖R‖op ≤ maxⱼ vⱼ ≤ 1ᵀv` chain from (B.1); only its
  entrywise/`mulVec` consequences (`resolvent_mulVec_le_max`) are proved, since
  Mathlib lacks the needed spectral arguments here.
* Eigenvalue perturbation theory and the spectral construction of `E₀`
  itself (the paper builds it from eigenvalues of `R^{1/2} P R^{1/2}`).  The
  existence of `E₀` is therefore the explicit hypothesis `hE0dim`, `hE0prop`
  of `spectral_subspace_exists`.
* The remaining analytic input for `hasDerivAt` (continuity of the matrix
  inverse), as described above.
-/

namespace Komlos

open scoped BigOperators
open Matrix Filter Topology

noncomputable section

/-! ### Rank-one and batch perturbation matrices -/

/-- The rank-one symmetric matrix `z zᵀ` appearing in batch updates. -/
def rankOne {s : ℕ} (z : Fin s → ℝ) : Input s s := fun j k => z j * z k

theorem rankOne_apply {s : ℕ} (z : Fin s → ℝ) (j k : Fin s) :
    rankOne z j k = z j * z k := rfl

theorem rankOne_symm {s : ℕ} (z : Fin s → ℝ) (j k : Fin s) :
    rankOne z j k = rankOne z k j := mul_comm _ _

theorem rankOne_mulVec {s : ℕ} (z v : Fin s → ℝ) :
    rankOne z *ᵥ v = (z ⬝ᵥ v) • z := by
  funext j
  simp only [rankOne, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The batch perturbation `∑ᵢ cᵢ zᵢ zᵢᵀ` used for multi-row updates:
`M(x + ∑ᵢ cᵢ zᵢ)` adds `batchPerturbation z c` to the energy matrix. -/
def batchPerturbation {m s : ℕ} (z : Fin m → Fin s → ℝ) (c : Fin m → ℝ) :
    Input s s :=
  ∑ i, c i • rankOne (z i)

theorem batchPerturbation_apply {m s : ℕ} (z : Fin m → Fin s → ℝ) (c : Fin m → ℝ)
    (j k : Fin s) :
    batchPerturbation z c j k = ∑ i, c i * z i j * z i k := by
  simp only [batchPerturbation, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    rankOne, mul_assoc]

theorem batchPerturbation_symm {m s : ℕ} (z : Fin m → Fin s → ℝ) (c : Fin m → ℝ)
    (j k : Fin s) :
    batchPerturbation z c j k = batchPerturbation z c k j := by
  rw [batchPerturbation_apply, batchPerturbation_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem batchPerturbation_mulVec {m s : ℕ} (z : Fin m → Fin s → ℝ) (c : Fin m → ℝ)
    (v : Fin s → ℝ) (j : Fin s) :
    (batchPerturbation z c *ᵥ v) j = ∑ i, c i * (z i ⬝ᵥ v) * z i j := by
  unfold batchPerturbation
  rw [Matrix.sum_mulVec]
  simp only [Finset.sum_apply, Matrix.smul_mulVec, rankOne_mulVec, Pi.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Bound on a batch perturbation applied to a nonnegative vector, assuming
`|cᵢ| ≤ η νᵢ` and nonnegativity of `z`, `v`, `ν`: the linear batch matrix
(B.5) content. -/
theorem batch_mulVec_bound {m s : ℕ} (z : Fin m → Fin s → ℝ) (δ ν : Fin m → ℝ)
    (v : Fin s → ℝ) (η : ℝ) (j : Fin s)
    (hz : ∀ i j, 0 ≤ z i j) (hv : ∀ j, 0 ≤ v j) (_hν : ∀ i, 0 ≤ ν i)
    (hδ : ∀ i, |δ i| ≤ η * ν i) :
    |((batchPerturbation z δ) *ᵥ v) j| ≤
      η * ∑ i, ν i * (z i ⬝ᵥ v) * z i j := by
  rw [batchPerturbation_mulVec]
  rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hzi : 0 ≤ z i ⬝ᵥ v := dotProduct_nonneg_of_nonneg (hz i) hv
  have hην : 0 ≤ η * ν i := le_trans (abs_nonneg _) (hδ i)
  calc
    |δ i * (z i ⬝ᵥ v) * z i j| = (|δ i| * (z i ⬝ᵥ v)) * z i j := by
      rw [abs_mul, abs_mul, abs_of_nonneg hzi, abs_of_nonneg (hz i j)]
    _ ≤ (η * ν i * (z i ⬝ᵥ v)) * z i j :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hδ i) hzi) (hz i j)
    _ = η * (ν i * (z i ⬝ᵥ v) * z i j) := by ring

/-! ### Resolvent along a linear path -/

theorem slackMatrix_add_smul {s : ℕ} (b : ℝ) (M N : Input s s) (t : ℝ) :
    slackMatrix b (M + t • N) = slackMatrix b M - t • N := by
  ext i j
  simp only [slackMatrix, Matrix.diagonal_apply, Matrix.sub_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The inverse of a positive-definite slack matrix is symmetric entrywise. -/
theorem slackMatrix_inv_symm {s : ℕ} {b : ℝ} {M : Input s s}
    (hpos : (slackMatrix b M).PosDef) (j k : Fin s) :
    (slackMatrix b M)⁻¹ j k = (slackMatrix b M)⁻¹ k j := by
  have h := hpos.inv.isHermitian.apply k j
  simpa using h

/-- The exact resolvent-vector step along `M ↦ M + tN`:
`v_{M+tN} − v_M = t · R_{M+tN} N v_M`, i.e. `(v_{t+s} − v_t)/s → R M' v`,
which is `v' = R M' v` of (B.3) in exact form. -/
theorem resolvent_step_eq {s : ℕ} {b t : ℝ} {M N : Input s s}
    (hMpos : (slackMatrix b M).PosDef)
    (hpos : (slackMatrix b (M + t • N)).PosDef) :
    resolventVector b (M + t • N) - resolventVector b M =
      t • ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M)) := by
  rw [resolvent_vector_difference hMpos hpos, add_sub_cancel_left, smul_mulVec,
    Matrix.mulVec_smul]

/-- Column-sum of the inverse slack equals the resolvent vector (uses
symmetry of the inverse). -/
theorem sum_resolvent_mulVec {s : ℕ} {b : ℝ} {X : Input s s}
    (hpos : (slackMatrix b X).PosDef) (w : Fin s → ℝ) :
    ∑ j, ((slackMatrix b X)⁻¹ *ᵥ w) j = resolventVector b X ⬝ᵥ w := by
  have hR : ∀ j k : Fin s, (slackMatrix b X)⁻¹ j k = (slackMatrix b X)⁻¹ k j :=
    slackMatrix_inv_symm hpos
  have hcol : ∀ k : Fin s, (∑ j, (slackMatrix b X)⁻¹ j k) =
      resolventVector b X k := by
    intro k
    have hv : resolventVector b X k = ∑ j, (slackMatrix b X)⁻¹ k j := by
      simp [resolventVector, Matrix.mulVec, dotProduct]
    rw [hv]
    apply Finset.sum_congr rfl
    intro j _
    exact hR j k
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_mul, hcol k]

/-- The exact first-variation identity for the resolvent potential along
`M ↦ M + tN` (the exact form of `F' = vᵀ M' v` in (B.3)):
`F_b(M+tN) − F_b(M) = t · v_{M+tN}ᵀ N v_M`. -/
theorem resolventPotential_step {s : ℕ} {b t : ℝ} {M N : Input s s}
    (hMpos : (slackMatrix b M).PosDef)
    (hpos : (slackMatrix b (M + t • N)).PosDef) :
    resolventPotential b (M + t • N) - resolventPotential b M =
      t * (resolventVector b (M + t • N) ⬝ᵥ (N *ᵥ resolventVector b M)) := by
  have hstep := resolvent_step_eq hMpos hpos
  have hF : resolventPotential b (M + t • N) - resolventPotential b M =
      ∑ j, (resolventVector b (M + t • N) j - resolventVector b M j) := by
    simp only [resolventPotential]
    rw [Finset.sum_sub_distrib]
    ring
  rw [hF]
  have hent : ∀ j : Fin s,
      resolventVector b (M + t • N) j - resolventVector b M j =
        t * ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M)) j := by
    intro j
    have hc := congrFun hstep j
    rwa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hc
  simp_rw [hent]
  rw [← Finset.mul_sum, sum_resolvent_mulVec hpos]

/-- The first-variation scalar `vᵀNv`, the value `F'(0)` of (B.3). -/
noncomputable def resolventVariation1 {s : ℕ} (b : ℝ) (M N : Input s s) : ℝ :=
  resolventVector b M ⬝ᵥ (N *ᵥ resolventVector b M)

/-- The second-variation scalar `2 (Nv)ᵀR(Nv)`, the value `F''(0)` of (B.3)
along an affine path (`M'' = 0`). -/
noncomputable def resolventVariation2 {s : ℕ} (b : ℝ) (M N : Input s s) : ℝ :=
  2 * ((N *ᵥ resolventVector b M) ⬝ᵥ
    ((slackMatrix b M)⁻¹ *ᵥ (N *ᵥ resolventVector b M)))

/-- The exact second-order identity for the resolvent potential along an
affine path: `F_b(M+tN) − F_b(M) = t·vᵀNv + t²·(Nv)ᵀR_t(Nv)`.
This is the integrated form of `F'' = 2(M'v)ᵀR(M'v)` from (B.3). -/
theorem resolventPotential_step_taylor {s : ℕ} {b t : ℝ} {M N : Input s s}
    (hMpos : (slackMatrix b M).PosDef)
    (hpos : (slackMatrix b (M + t • N)).PosDef) :
    resolventPotential b (M + t • N) - resolventPotential b M =
      t * resolventVariation1 b M N +
        t ^ 2 * ((N *ᵥ resolventVector b M) ⬝ᵥ
          ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M))) := by
  have hstep := resolvent_step_eq hMpos hpos
  have h1 := resolventPotential_step hMpos hpos
  have hv : resolventVector b (M + t • N) ⬝ᵥ (N *ᵥ resolventVector b M) =
      resolventVector b M ⬝ᵥ (N *ᵥ resolventVector b M) +
        t * ((N *ᵥ resolventVector b M) ⬝ᵥ
          ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M))) := by
    have hd : resolventVector b (M + t • N) = resolventVector b M +
        t • ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M)) :=
      sub_eq_iff_eq_add'.mp hstep
    rw [hd, add_dotProduct, smul_dotProduct, smul_eq_mul,
      dotProduct_comm ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M))
        (N *ᵥ resolventVector b M)]
  rw [h1, hv]
  unfold resolventVariation1
  ring

/-- The centred second difference of the resolvent potential along an affine
path equals `t²` times the sum of the two one-sided curvature quadratic forms. -/
theorem resolventPotential_symmetric_difference {s : ℕ} {b t : ℝ}
    {M N : Input s s}
    (hMpos : (slackMatrix b M).PosDef)
    (hposP : (slackMatrix b (M + t • N)).PosDef)
    (hposN : (slackMatrix b (M - t • N)).PosDef) :
    resolventPotential b (M + t • N) + resolventPotential b (M - t • N) -
        2 * resolventPotential b M =
      t ^ 2 * ((N *ᵥ resolventVector b M) ⬝ᵥ
          ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M)) +
        (N *ᵥ resolventVector b M) ⬝ᵥ
          ((slackMatrix b (M - t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M))) := by
  have hneg : M - t • N = M + (-t) • N := by
    rw [sub_eq_add_neg, ← neg_smul]
  rw [hneg] at hposN
  have h1 := resolventPotential_step_taylor hMpos hposP
  have h2 := resolventPotential_step_taylor (t := -t) hMpos hposN
  rw [hneg]
  linarith

/-- Midpoint concavity corollary: if the sum of the two one-sided curvature
quadratic forms is nonpositive, `F_b` is concave along the affine path. -/
theorem resolventPotential_midpoint_le {s : ℕ} {b t : ℝ} {M N : Input s s}
    (hMpos : (slackMatrix b M).PosDef)
    (hposP : (slackMatrix b (M + t • N)).PosDef)
    (hposN : (slackMatrix b (M - t • N)).PosDef)
    (hcurv : (N *ᵥ resolventVector b M) ⬝ᵥ
        ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M)) +
      (N *ᵥ resolventVector b M) ⬝ᵥ
        ((slackMatrix b (M - t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M)) ≤ 0) :
    resolventPotential b (M + t • N) + resolventPotential b (M - t • N) ≤
      2 * resolventPotential b M := by
  have h := resolventPotential_symmetric_difference hMpos hposP hposN
  have hnonpos : t ^ 2 * ((N *ᵥ resolventVector b M) ⬝ᵥ
        ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M)) +
      (N *ᵥ resolventVector b M) ⬝ᵥ
        ((slackMatrix b (M - t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) hcurv
  linarith

/-- The first variation of a batch perturbation is the weighted Gram energy
`∑ᵢ cᵢ (zᵢᵀv)²`. -/
theorem resolventVariation1_batch {m s : ℕ} (b : ℝ) (z : Fin m → Fin s → ℝ)
    (c : Fin m → ℝ) (M : Input s s) :
    resolventVariation1 b M (batchPerturbation z c) =
      ∑ i, c i * (z i ⬝ᵥ resolventVector b M) ^ 2 := by
  unfold resolventVariation1 batchPerturbation
  rw [Matrix.sum_mulVec, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.smul_mulVec, rankOne_mulVec, dotProduct_smul, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, dotProduct_comm (resolventVector b M) (z i)]
  ring

/-- For a symmetric `A`, `xᵀAy = (Ax)ᵀy`. -/
theorem dotProduct_mulVec_eq {s : ℕ} {A : Input s s}
    (hsymm : ∀ j k, A j k = A k j) (x y : Fin s → ℝ) :
    x ⬝ᵥ (A *ᵥ y) = (A *ᵥ x) ⬝ᵥ y := by
  simp only [dotProduct, Matrix.mulVec]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [hsymm i j]
  ring

/-! ### Resolvent norms: the (B.1) content that does not need `R^{1/2}` -/

/-- For nonnegative `h`, `(Rh)ⱼ ≤ vⱼ · max_k hₖ`: the entrywise consequence of
`‖R‖op ≤ maxⱼ vⱼ` used in the resolvent norm bound (B.1). -/
theorem resolvent_mulVec_le_max {s : ℕ} {b : ℝ} {M : Input s s}
    (hM : ∀ j k, 0 ≤ M j k) (hpos : (slackMatrix b M).PosDef)
    (h : Fin s → ℝ) (_hh : ∀ j, 0 ≤ h j) (j : Fin s) :
    ((slackMatrix b M)⁻¹ *ᵥ h) j ≤
      resolventVector b M j * Finset.univ.sup' ⟨j, Finset.mem_univ j⟩ h := by
  have hcol : (∑ k, (slackMatrix b M)⁻¹ j k) = resolventVector b M j := by
    simp [resolventVector, Matrix.mulVec, dotProduct]
  calc
    ((slackMatrix b M)⁻¹ *ᵥ h) j = ∑ k, (slackMatrix b M)⁻¹ j k * h k := rfl
    _ ≤ ∑ k, (slackMatrix b M)⁻¹ j k *
          Finset.univ.sup' ⟨j, Finset.mem_univ j⟩ h :=
      Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_left
          (Finset.le_sup' _ (Finset.mem_univ k))
          (slack_inverse_entrywise_nonneg hM hpos j k)
    _ = resolventVector b M j * Finset.univ.sup' ⟨j, Finset.mem_univ j⟩ h := by
      rw [← Finset.sum_mul, hcol]

/-! ### Stability: relative resolvent and potential change (B.5) -/

/-- Relative change of the resolvent vector under a batch perturbation whose
coefficients satisfy `|δᵢ| ≤ η νᵢ` with slack-dominated loads
`∑ᵢ νᵢ (zᵢᵀv) zᵢⱼ ≤ κ`.  This is the multi-row version of the one-sided
relative bound `|Δvⱼ| ≤ ε v'_ⱼ` underlying (B.5). -/
theorem resolvent_vector_batch_relative_change {m s : ℕ} {b η κ : ℝ}
    {M : Input s s} (z : Fin m → Fin s → ℝ) (δ ν : Fin m → ℝ)
    (hM : ∀ j k, 0 ≤ M j k)
    (hN : ∀ j k, 0 ≤ (M + batchPerturbation z δ) j k)
    (hMpos : (slackMatrix b M).PosDef)
    (hNpos : (slackMatrix b (M + batchPerturbation z δ)).PosDef)
    (hη : 0 ≤ η)
    (hz : ∀ i j, 0 ≤ z i j) (hν : ∀ i, 0 ≤ ν i)
    (hδ : ∀ i, |δ i| ≤ η * ν i)
    (hload : ∀ j, ∑ i, ν i * (z i ⬝ᵥ resolventVector b M) * z i j ≤ κ)
    (j : Fin s) :
    |resolventVector b (M + batchPerturbation z δ) j - resolventVector b M j| ≤
      (η * κ) * resolventVector b (M + batchPerturbation z δ) j := by
  apply resolvent_vector_relative_change hN hMpos hNpos _ j
  intro k
  have hsub : M + batchPerturbation z δ - M = batchPerturbation z δ :=
    add_sub_cancel_left M _
  rw [hsub]
  calc
    |(batchPerturbation z δ *ᵥ resolventVector b M) k| ≤
        η * ∑ i, ν i * (z i ⬝ᵥ resolventVector b M) * z i k :=
      batch_mulVec_bound z δ ν _ η k hz (resolventVector_nonneg hM hMpos) hν hδ
    _ ≤ η * κ := mul_le_mul_of_nonneg_left (hload k) hη

/-- Two-sided relative resolvent bounds for a batch update: `v'_ⱼ` lies in
`[vⱼ/(1+ηκ), vⱼ/(1−ηκ)]`, the form used for potential comparison in (B.5). -/
theorem resolvent_vector_batch_relative_bounds {m s : ℕ} {b η κ : ℝ}
    {M : Input s s} (z : Fin m → Fin s → ℝ) (δ ν : Fin m → ℝ)
    (hM : ∀ j k, 0 ≤ M j k)
    (hN : ∀ j k, 0 ≤ (M + batchPerturbation z δ) j k)
    (hMpos : (slackMatrix b M).PosDef)
    (hNpos : (slackMatrix b (M + batchPerturbation z δ)).PosDef)
    (hη : 0 ≤ η) (hηκ : η * κ < 1)
    (hz : ∀ i j, 0 ≤ z i j) (hν : ∀ i, 0 ≤ ν i)
    (hδ : ∀ i, |δ i| ≤ η * ν i)
    (hload : ∀ j, ∑ i, ν i * (z i ⬝ᵥ resolventVector b M) * z i j ≤ κ)
    (j : Fin s) :
    resolventVector b M j / (1 + η * κ) ≤
        resolventVector b (M + batchPerturbation z δ) j ∧
      resolventVector b (M + batchPerturbation z δ) j ≤
        resolventVector b M j / (1 - η * κ) := by
  apply resolvent_vector_relative_bounds hN hMpos hNpos _
    (mul_nonneg hη (le_trans (Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (hν i)
        (dotProduct_nonneg_of_nonneg (hz i) (resolventVector_nonneg hM hMpos)))
        (hz i _)) (hload j))) hηκ j
  intro k
  have hsub : M + batchPerturbation z δ - M = batchPerturbation z δ :=
    add_sub_cancel_left M _
  rw [hsub]
  calc
    |(batchPerturbation z δ *ᵥ resolventVector b M) k| ≤
        η * ∑ i, ν i * (z i ⬝ᵥ resolventVector b M) * z i k :=
      batch_mulVec_bound z δ ν _ η k hz (resolventVector_nonneg hM hMpos) hν hδ
    _ ≤ η * κ := mul_le_mul_of_nonneg_left (hload k) hη

/-- The resolvent potential changes by at most `ηκ` times the resolvent mass
of the perturbed vector: `|F_b(M+Δ) − F_b(M)| ≤ ηκ · 1ᵀ v'`. -/
theorem resolventPotential_batch_change {m s : ℕ} {b η κ : ℝ}
    {M : Input s s} (z : Fin m → Fin s → ℝ) (δ ν : Fin m → ℝ)
    (hM : ∀ j k, 0 ≤ M j k)
    (hN : ∀ j k, 0 ≤ (M + batchPerturbation z δ) j k)
    (hMpos : (slackMatrix b M).PosDef)
    (hNpos : (slackMatrix b (M + batchPerturbation z δ)).PosDef)
    (hη : 0 ≤ η)
    (hz : ∀ i j, 0 ≤ z i j) (hν : ∀ i, 0 ≤ ν i)
    (hδ : ∀ i, |δ i| ≤ η * ν i)
    (hload : ∀ j, ∑ i, ν i * (z i ⬝ᵥ resolventVector b M) * z i j ≤ κ) :
    |resolventPotential b (M + batchPerturbation z δ) - resolventPotential b M| ≤
      (η * κ) * ∑ j, resolventVector b (M + batchPerturbation z δ) j := by
  have hF : resolventPotential b (M + batchPerturbation z δ) - resolventPotential b M =
      ∑ j, (resolventVector b (M + batchPerturbation z δ) j - resolventVector b M j) := by
    simp only [resolventPotential]
    rw [Finset.sum_sub_distrib]
    ring
  rw [hF]
  calc
    |∑ j, (resolventVector b (M + batchPerturbation z δ) j - resolventVector b M j)| ≤
        ∑ j, |resolventVector b (M + batchPerturbation z δ) j - resolventVector b M j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (η * κ) * resolventVector b (M + batchPerturbation z δ) j :=
      Finset.sum_le_sum fun j _ =>
        resolvent_vector_batch_relative_change z δ ν hM hN hMpos hNpos hη hz hν hδ hload j
    _ = (η * κ) * ∑ j, resolventVector b (M + batchPerturbation z δ) j := by
      rw [Finset.mul_sum]

/-- Two-sided weight stability: for `|u − u₀| ≤ a` (with `u + a ≤ 0`),
`|ν(u) − ν(u₀)| ≤ (e^{a/2} − 1) · ν(u₀)`.  This is the paper's
`|δᵢ| ≤ (e^{|Δ|/2} − 1) νᵢ` relative weight bound from (B.5). -/
theorem weight_abs_sub_le {u₀ u a : ℝ} (ha : 0 ≤ a) (hu : u ≤ 0) (hu₀ : u₀ + a ≤ 0)
    (hlo : u₀ - a ≤ u) (hhi : u ≤ u₀ + a) :
    |weight u - weight u₀| ≤ (Real.exp (a / 2) - 1) * weight u₀ := by
  have hu₀0 : u₀ ≤ 0 := by linarith
  have hw0 : 0 < weight u₀ := weight_pos hu₀0
  have hup : weight u ≤ Real.exp (a / 2) * weight u₀ :=
    (weight_mono hhi hu₀).trans (weight_relative_change ha hu₀)
  have hlow : Real.exp (-(a / 2)) * weight u₀ ≤ weight u := by
    have h1 : weight u₀ ≤ Real.exp (a / 2) * weight (u₀ - a) := by
      have := weight_relative_change (u := u₀ - a) (δ := a) ha (by linarith)
      rwa [show u₀ - a + a = u₀ from by ring] at this
    have h2 : weight (u₀ - a) ≤ weight u := weight_mono hlo hu
    have h3 : weight u₀ ≤ Real.exp (a / 2) * weight u :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)
    have h4 := mul_le_mul_of_nonneg_right h3 (Real.exp_pos (-(a / 2))).le
    have h5 : Real.exp (a / 2) * weight u * Real.exp (-(a / 2)) = weight u := by
      have hexp : Real.exp (a / 2) * Real.exp (-(a / 2)) = 1 := by
        rw [← Real.exp_add]
        simp
      calc
        Real.exp (a / 2) * weight u * Real.exp (-(a / 2))
          = (Real.exp (a / 2) * Real.exp (-(a / 2))) * weight u := by ring
        _ = weight u := by rw [hexp]; ring
    rw [h5] at h4
    linarith
  have he1 : (1:ℝ) ≤ Real.exp (a / 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have he' : Real.exp (-(a / 2)) ≤ 1 := by
    rw [Real.exp_neg]
    exact inv_le_one_of_one_le₀ he1
  have hlower : weight u₀ - weight u ≤ (Real.exp (a / 2) - 1) * weight u₀ := by
    have h6 : weight u₀ - weight u ≤ (1 - Real.exp (-(a / 2))) * weight u₀ := by
      nlinarith
    have h7 : (1 - Real.exp (-(a / 2))) * weight u₀ ≤
        (Real.exp (a / 2) - 1) * weight u₀ := by
      apply mul_le_mul_of_nonneg_right _ hw0.le
      -- 1 - e' ≤ e - 1 ⟺ e + e' ≥ 2; here (e - 1)·e' = 1 - e'? use e·e' = 1
      have hexp : Real.exp (a / 2) * Real.exp (-(a / 2)) = 1 := by
        rw [← Real.exp_add]
        simp
      have hsq : (Real.exp (a / 2) - 1) ^ 2 ≥ 0 := sq_nonneg _
      nlinarith
    exact h6.trans h7
  have hupper : weight u - weight u₀ ≤ (Real.exp (a / 2) - 1) * weight u₀ := by
    nlinarith
  rw [abs_le]
  constructor <;> linarith [hlower, hupper]

/-- The numerical estimate `ν(−1) > 357/5`, used to bound the contribution of
nearly tight rows (`uᵢ ≥ −1`) in the spectral counting argument. -/
theorem weight_neg_one_gt : 357 / 5 < weight (-1) := by
  have h1 : (1 - (-1 : ℝ) / 20000) ^ 10000 ≤ Real.exp (1 / 2) := by
    have h2 : (1 - (-1 : ℝ) / 20000) = (1 - (1 / 20001 : ℝ))⁻¹ := by norm_num
    rw [h2]
    have h := one_sub_inv_pow_le_exp 10000 (y := 1 / 20001) (by norm_num) (by norm_num)
    rwa [show ((10000 : ℕ) : ℝ) * (1 / 20001) / (1 - 1 / 20001) = 1 / 2
      from by norm_num] at h
  have hX : (0 : ℝ) < (1 - (-1 : ℝ) / 20000) ^ 10000 := by positivity
  have hexp : Real.exp (1 / 2) < 595 / 357 := by
    have h9 : Real.exp 1 < (595 / 357) ^ 2 :=
      lt_trans Real.exp_one_lt_d9 (by norm_num)
    rw [Real.exp_half]
    exact (Real.sqrt_lt (Real.exp_nonneg 1) (by norm_num : (0 : ℝ) ≤ 595 / 357)).mpr h9
  have hl : (119 : ℝ) / Real.exp (1 / 2) ≤ 119 / (1 - (-1 : ℝ) / 20000) ^ 10000 := by
    apply div_le_div_of_nonneg_left (by norm_num) hX h1
  have hl2 : (357 : ℝ) / 5 = 119 / (595 / 357) := by norm_num
  have hl3 : (119 : ℝ) / (595 / 357) < 119 / Real.exp (1 / 2) :=
    div_lt_div_of_pos_left (by norm_num) (Real.exp_pos _) hexp
  calc
    (357 : ℝ) / 5 = 119 / (595 / 357) := hl2
    _ < 119 / Real.exp (1 / 2) := hl3
    _ ≤ 119 / (1 - (-1 : ℝ) / 20000) ^ 10000 := hl
    _ = weight (-1) := rfl

/-! ### Curvature comparisons -/

/-- Pointwise bound of the second-derivative diagonal by the first-derivative
(`D₀`) diagonal used to absorb `U₀` into `D₀` in Appendix B: under
`(gᵢⱼ)² ≤ 4 zᵢⱼ` (i.e. `z = zᵢzᵢᵀ`-type diagonal domination) and `uᵢ ≤ 0`,
`∑ᵢ ν''ᵢ tᵢ² gᵢⱼ² ≤ (1 + 1/10000)/4 · (8 ∑ᵢ ν'ᵢ tᵢ² zᵢⱼ)`. -/
theorem udiag_curvature_le {m s : ℕ} {u t : Fin m → ℝ} {z g : Fin m → Fin s → ℝ}
    (hu : ∀ i, u i ≤ 0) (hz : ∀ i j, 0 ≤ z i j)
    (hg : ∀ i j, (g i j) ^ 2 ≤ 4 * z i j) (j : Fin s) :
    ∑ i, weightDeriv2 (u i) * (t i) ^ 2 * (g i j) ^ 2 ≤
      ((1 + 1 / 10000) / 4) * (8 * ∑ i, weightDeriv (u i) * (t i) ^ 2 * z i j) := by
  calc
    ∑ i, weightDeriv2 (u i) * (t i) ^ 2 * (g i j) ^ 2
        ≤ ∑ i, weightDeriv2 (u i) * ((t i) ^ 2 * (4 * z i j)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hg i j) (sq_nonneg _))
        (weightDeriv2_pos (hu i)).le
    _ ≤ ∑ i, weightDeriv (u i) * ((1 + 1 / 10000) / 2) * ((t i) ^ 2 * (4 * z i j)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (weightDeriv2_le (hu i))
        (mul_nonneg (sq_nonneg (t i)) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (hz i j)))
    _ = ((1 + 1 / 10000) / 4) * (8 * ∑ i, weightDeriv (u i) * (t i) ^ 2 * z i j) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The Cauchy–Schwarz gradient-drift bound behind (B.6): if `0 ≤ zⱼ`,
`∑ⱼ zⱼ ≤ 1`, and `|yⱼ| ≤ a`, then `(∑ⱼ 8 zⱼ yⱼ hⱼ)² ≤ 64 a² ∑ⱼ zⱼ hⱼ²`. -/
theorem gradient_drift_sq_le {s : ℕ} (z y h : Fin s → ℝ) (a : ℝ)
    (ha : 0 ≤ a) (hz : ∀ j, 0 ≤ z j) (hzsum : ∑ j, z j ≤ 1)
    (hy : ∀ j, |y j| ≤ a) :
    (∑ j, (8 * z j * y j) * h j) ^ 2 ≤ 64 * a ^ 2 * ∑ j, z j * (h j) ^ 2 := by
  have hsqrt : ∀ j, Real.sqrt (z j) * y j * (Real.sqrt (z j) * h j) =
      z j * y j * h j := by
    intro j
    calc
      Real.sqrt (z j) * y j * (Real.sqrt (z j) * h j)
        = (Real.sqrt (z j) * Real.sqrt (z j)) * (y j * h j) := by ring
      _ = z j * (y j * h j) := by rw [Real.mul_self_sqrt (hz j)]
      _ = z j * y j * h j := by ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j => Real.sqrt (z j) * y j) (fun j => Real.sqrt (z j) * h j)
  simp_rw [hsqrt] at hcs
  have hf : ∀ j, (Real.sqrt (z j) * y j) ^ 2 = z j * (y j) ^ 2 := by
    intro j
    rw [mul_pow, Real.sq_sqrt (hz j)]
  have hg : ∀ j, (Real.sqrt (z j) * h j) ^ 2 = z j * (h j) ^ 2 := by
    intro j
    rw [mul_pow, Real.sq_sqrt (hz j)]
  simp_rw [hf, hg] at hcs
  have hy2 : ∀ j, (y j) ^ 2 ≤ a ^ 2 := by
    intro j
    rw [← abs_of_nonneg ha] at hy
    exact sq_le_sq.mpr (hy j)
  have hsumy : ∑ j, z j * (y j) ^ 2 ≤ a ^ 2 * ∑ j, z j := by
    calc
      ∑ j, z j * (y j) ^ 2 ≤ ∑ j, z j * a ^ 2 :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hy2 j) (hz j)
      _ = a ^ 2 * ∑ j, z j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hX : 0 ≤ ∑ j, z j * (h j) ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hz j) (sq_nonneg _)
  have hmain : (∑ j, z j * y j * h j) ^ 2 ≤ a ^ 2 * ∑ j, z j * (h j) ^ 2 := by
    calc
      (∑ j, z j * y j * h j) ^ 2 ≤
          (∑ j, z j * (y j) ^ 2) * ∑ j, z j * (h j) ^ 2 := hcs
      _ ≤ (a ^ 2 * ∑ j, z j) * ∑ j, z j * (h j) ^ 2 :=
        mul_le_mul_of_nonneg_right hsumy hX
      _ = a ^ 2 * ((∑ j, z j) * ∑ j, z j * (h j) ^ 2) := by ring
      _ ≤ a ^ 2 * (1 * ∑ j, z j * (h j) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hzsum hX) (sq_nonneg a)
      _ = a ^ 2 * ∑ j, z j * (h j) ^ 2 := by ring
  have hleft : (∑ j, (8 * z j * y j) * h j) ^ 2 = 64 * (∑ j, z j * y j * h j) ^ 2 := by
    have he : (∑ j, (8 * z j * y j) * h j) = 8 * ∑ j, z j * y j * h j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he]
    ring
  rw [hleft]
  have := mul_le_mul_of_nonneg_left hmain (by norm_num : (0:ℝ) ≤ 64)
  linarith

/-- The summed (`ν''`-weighted) version of the gradient drift bound (B.6):
each `(∑ⱼ 8 zᵢⱼ yⱼ hⱼ)²` is bounded via `gradient_drift_sq_le` and
`ν''ᵢ ≤ ν'ᵢ · (1 + 1/10000)/2`, giving the `5 a² · 8D₀`-type bound. -/
theorem curvature_drift_le {m s : ℕ} (u : Fin m → ℝ) (t : Fin m → ℝ)
    (z : Fin m → Fin s → ℝ) (y h : Fin s → ℝ) (a : ℝ)
    (ha : 0 ≤ a) (hu : ∀ i, u i ≤ 0) (hz : ∀ i j, 0 ≤ z i j)
    (hzsum : ∀ i, ∑ j, z i j ≤ 1) (hy : ∀ j, |y j| ≤ a) :
    ∑ i, weightDeriv2 (u i) * (t i) ^ 2 * (∑ j, (8 * z i j * y j) * h j) ^ 2 ≤
      5 * a ^ 2 * (8 * ∑ i, weightDeriv (u i) * (t i) ^ 2 * ∑ j, z i j * (h j) ^ 2) := by
  have hX : 0 ≤ ∑ i, weightDeriv (u i) * (t i) ^ 2 * ∑ j, z i j * (h j) ^ 2 :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (weightDeriv_nonneg (hu i)) (sq_nonneg _))
        (Finset.sum_nonneg fun j _ => mul_nonneg (hz i j) (sq_nonneg _))
  calc
    ∑ i, weightDeriv2 (u i) * (t i) ^ 2 * (∑ j, (8 * z i j * y j) * h j) ^ 2
        ≤ ∑ i, weightDeriv2 (u i) * (t i) ^ 2 *
            (64 * a ^ 2 * ∑ j, z i j * (h j) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (gradient_drift_sq_le (z i) y h a ha (hz i) (hzsum i) hy)
        (mul_nonneg (weightDeriv2_pos (hu i)).le (sq_nonneg _))
    _ ≤ ∑ i, weightDeriv (u i) * ((1 + 1 / 10000) / 2) * ((t i) ^ 2 *
            (64 * a ^ 2 * ∑ j, z i j * (h j) ^ 2)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (weightDeriv2_le (hu i))
        (mul_nonneg (sq_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64) (sq_nonneg a))
            (Finset.sum_nonneg fun j _ => mul_nonneg (hz i j) (sq_nonneg _))))
    _ = 32 * (1 + 1 / 10000) * a ^ 2 *
          ∑ i, weightDeriv (u i) * (t i) ^ 2 * ∑ j, z i j * (h j) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ 5 * a ^ 2 * (8 * ∑ i, weightDeriv (u i) * (t i) ^ 2 *
          ∑ j, z i j * (h j) ^ 2) := by
      have hconst : (32 : ℝ) * (1 + 1 / 10000) ≤ 40 := by norm_num
      have hle : 32 * (1 + 1 / 10000) * a ^ 2 ≤ 40 * a ^ 2 :=
        mul_le_mul_of_nonneg_right hconst (sq_nonneg a)
      have hleX := mul_le_mul_of_nonneg_right hle hX
      have he : (5 : ℝ) * a ^ 2 * (8 * ∑ i, weightDeriv (u i) * (t i) ^ 2 *
          ∑ j, z i j * (h j) ^ 2) = (40 * a ^ 2) *
            ∑ i, weightDeriv (u i) * (t i) ^ 2 * ∑ j, z i j * (h j) ^ 2 := by ring
      rw [he]
      exact hleX

/-- Under a load bound `∑ᵢ ν'ᵢ tᵢ² (Aᵢᵀv) Aᵢⱼ ≤ κ`, the resolvent-transported
weighted Gram form is bounded by `κ · xᵀ R x`.  This is the quadratic-form
content of "`R^{1/2} (Σᵢ ν'ᵢ tᵢ² AᵢAᵢᵀ) R^{1/2} ⪯ κ I`" used for stability. -/
theorem light_gram_resolvent_form_le {m s : ℕ} {A : Input m s} {u t : Fin m → ℝ}
    {κ b : ℝ} {M : Input s s} {x : Fin s → ℝ}
    (hb : 0 < b) (hMsymm : ∀ j k, M j k = M k j) (hM : ∀ j k, 0 ≤ M j k)
    (hpos : (slackMatrix b M).PosDef)
    (hA : ∀ i j, 0 ≤ A i j) (hu : ∀ i, u i ≤ 0) (hκ : 0 ≤ κ)
    (hload : ∀ j, ∑ i, weightDeriv (u i) * (t i) ^ 2 *
        (∑ k, A i k * resolventVector b M k) * A i j ≤ κ) :
    ∑ i, weightDeriv (u i) * (t i) ^ 2 * (A i ⬝ᵥ ((slackMatrix b M)⁻¹ *ᵥ x)) ^ 2 ≤
      κ * (x ⬝ᵥ ((slackMatrix b M)⁻¹ *ᵥ x)) := by
  have hv : ∀ j, 0 < resolventVector b M j := fun j =>
    lt_of_lt_of_le (one_div_pos.mpr hb) (resolventVector_lower_bound hb hM hpos j)
  have hquad : slackQuadratic b M ((slackMatrix b M)⁻¹ *ᵥ x) =
      x ⬝ᵥ ((slackMatrix b M)⁻¹ *ᵥ x) := by
    have h2 : slackQuadratic b M ((slackMatrix b M)⁻¹ *ᵥ x) =
        ((slackMatrix b M)⁻¹ *ᵥ x) ⬝ᵥ
          (slackMatrix b M *ᵥ ((slackMatrix b M)⁻¹ *ᵥ x)) := by
      simp only [slackQuadratic, dotProduct]
      conv_rhs => rw [slackMatrix_mulVec]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h2, slack_inverse_mulVec_eq hpos x, dotProduct_comm]
  have hmain := weighted_gram_slack_domination b κ M A
    (fun i => weightDeriv (u i) * (t i) ^ 2) (resolventVector b M)
    ((slackMatrix b M)⁻¹ *ᵥ x)
    hMsymm hM hv (fun j => resolvent_equation hpos j) hA
    (fun i => mul_nonneg (weightDeriv_nonneg (hu i)) (sq_nonneg _)) hκ hload
  rw [hquad] at hmain
  convert hmain using 2
  rfl

/-! ### Dimension bookkeeping: the (B.4) margin and the s/32 subspace -/

/-- Rows with squared row mass above `Rmax² = (291/200)²` number at most
`s/Rmax²` — direct corollary of `live_row_count`. -/
theorem large_row_count {m s : ℕ} {A : Input m s} (hA : ColumnNormalized A)
    (S : Finset (Fin m))
    (hS : ∀ i ∈ S, (291 / 200) ^ 2 ≤ ∑ j, (A i j) ^ 2) :
    (S.card : ℝ) ≤ s / (291 / 200) ^ 2 :=
  live_row_count hA S (by positivity) hS

/-- Rows that are nearly tight (`uᵢ ≥ −1`) and heavy (`(massᵢ)² ≥ (64/65)²`)
contribute each at least `θ = (357/5)·(64/65)⁴` to
`∑ ν(uᵢ)·(massᵢ)²`; hence their number is at most
`5 (65/64)⁴ s / 238` provided the total weight is at most `3s/2`. -/
theorem nearly_tight_row_count {m s : ℕ} {u : Fin m → ℝ} {mass : Fin m → ℝ}
    (S : Finset (Fin m)) (hu : ∀ i ∈ S, -1 ≤ u i) (hu0 : ∀ i, u i ≤ 0)
    (hm : ∀ i ∈ S, (64 / 65) ^ 2 ≤ mass i)
    (hsum : ∑ i ∈ S, weight (u i) * (mass i) ^ 2 ≤ 3 * s / 2) :
    (S.card : ℝ) ≤ 5 * (65 / 64) ^ 4 * s / 238 := by
  have hθ : (0 : ℝ) < (357 / 5) * (64 / 65) ^ 4 := by positivity
  have hcontrib : ∀ i ∈ S, (357 / 5) * (64 / 65) ^ 4 ≤ weight (u i) * (mass i) ^ 2 := by
    intro i hi
    have hw : weight (-1) ≤ weight (u i) := weight_mono (hu i hi) (hu0 i)
    have hm2 : (64 / 65) ^ 4 ≤ (mass i) ^ 2 := by
      have h1 : (0 : ℝ) ≤ (64 / 65) ^ 2 := by positivity
      have h2 := pow_le_pow_left₀ h1 (hm i hi) 2
      rwa [show ((64 / 65) ^ 2 : ℝ) ^ 2 = (64 / 65) ^ 4 from by ring] at h2
    have hw' : (357 : ℝ) / 5 ≤ weight (u i) := (weight_neg_one_gt.trans_le hw).le
    exact mul_le_mul hw' hm2 (by positivity) (weight_pos (hu0 i)).le
  have hcard : (S.card : ℝ) * ((357 / 5) * (64 / 65) ^ 4) ≤ 3 * s / 2 := by
    calc
      (S.card : ℝ) * ((357 / 5) * (64 / 65) ^ 4) =
          ∑ _i ∈ S, (357 / 5) * (64 / 65) ^ 4 := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ S, weight (u i) * (mass i) ^ 2 := Finset.sum_le_sum hcontrib
      _ ≤ 3 * s / 2 := hsum
  have hcard' : (S.card : ℝ) ≤ (3 * s / 2) / ((357 / 5) * (64 / 65) ^ 4) :=
    (le_div_iff₀ hθ).mpr hcard
  refine hcard'.trans_eq ?_
  field_simp
  ring

/-- If every row of `S` has `tᵢ ≥ Θ/2` and `∑ᵢ tᵢ ≤ Λ·P·s` with
`Θ = 4096 Λ P` (the paper's `Θ`-quantiles), then `|S| ≤ s/2048`: this is the
`O(s/Θ)·...`-style heavy-count lemma. -/
theorem heavy_row_count {m s : ℕ} {t : Fin m → ℝ} (S : Finset (Fin m))
    {Λ P Θ : ℝ} (hΘ : 0 < Θ) (hΛ : 0 < Λ) (hP : 0 < P)
    (ht : ∀ i ∈ S, Θ / 2 ≤ t i) (htot : ∑ i ∈ S, t i ≤ Λ * P * s)
    (hΘdef : Θ = 4096 * Λ * P) :
    (S.card : ℝ) ≤ s / 2048 := by
  have h1 : (S.card : ℝ) * (Θ / 2) ≤ Λ * P * s := by
    calc
      (S.card : ℝ) * (Θ / 2) = ∑ _i ∈ S, Θ / 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ S, t i := Finset.sum_le_sum ht
      _ ≤ Λ * P * s := htot
  have h2 : (S.card : ℝ) ≤ (Λ * P * s) / (Θ / 2) :=
    (le_div_iff₀ (by linarith : (0 : ℝ) < Θ / 2)).mpr h1
  refine h2.trans_eq ?_
  rw [hΘdef]
  field_simp
  ring

/-- The four explicit dimension losses from (B.4): large rows
(`s/Rmax²`), nearly tight rows (`5(65/64)⁴s/238`), heavy rows
(`s/(64(α−b_dep))`), and protected rows (`s/2048`) together with the fifth
potential loss `(1+α)(1+1/K)⁴/((1−α)(1−ρ))·s` are bounded by `(31/32)s`;
equivalently their total exceeds `s` by less than `s/32`. This is
`curvature_dimension_margin` restated for counting. -/
theorem four_loss_card {s : ℝ} (n₁ n₂ n₃ n₄ : ℝ)
    (h₁ : n₁ ≤ s / (291 / 200) ^ 2)
    (h₂ : n₂ ≤ 5 * (65 / 64) ^ 4 * s / 238)
    (h₃ : n₃ ≤ s / (64 * (4 / 25 - 3 / 625)))
    (h₄ : n₄ ≤ s / 2048) :
    n₁ + n₂ + n₃ + n₄ ≤
      (1 / (291 / 200) ^ 2 + 5 * (65 / 64) ^ 4 / 238 +
        1 / (64 * (4 / 25 - 3 / 625)) + 1 / 2048) * s := by
  have e1 : s / (291 / 200) ^ 2 = (1 / (291 / 200) ^ 2) * s := by ring
  have e3 : s / (64 * (4 / 25 - 3 / 625)) = (1 / (64 * (4 / 25 - 3 / 625))) * s := by
    ring
  have e4 : s / 2048 = (1 / 2048) * s := by ring
  rw [e1] at h₁
  rw [e3] at h₃
  rw [e4] at h₄
  linarith [h₁, h₂, h₃, h₄]

/-- Combined (B.4) bound: the five losses together are at most `(31/32)·s`. -/
theorem spectral_dimension_margin {s : ℝ} (c₁ c₂ c₃ c₄ c₅ : ℝ)
    (h₁ : c₁ ≤ (1 / (291 / 200) ^ 2) * s)
    (h₂ : c₂ ≤ (5 * (65 / 64) ^ 4 / 238) * s)
    (h₃ : c₃ ≤ (1 / (64 * (4 / 25 - 3 / 625))) * s)
    (h₄ : c₄ ≤ (1 / 2048) * s)
    (h₅ : c₅ ≤ ((1 + 4 / 25) * (1 + 1 / 10000) /
        (4 * (1 - 4 / 25) * (1 - 1 / 64))) * s)
    (hs : 0 < s) :
    c₁ + c₂ + c₃ + c₄ + c₅ < (31 / 32) * s := by
  have hTlt : (1 / (291 / 200) ^ 2 + 5 * (65 / 64) ^ 4 / 238 +
      1 / (64 * (4 / 25 - 3 / 625)) + 1 / 2048 +
      (1 + 4 / 25) * (1 + 1 / 10000) / (4 * (1 - 4 / 25) * (1 - 1 / 64)) : ℝ) <
      31 / 32 := by
    norm_num
  linarith [h₁, h₂, h₃, h₄, h₅, mul_lt_mul_of_pos_right hTlt hs]

/-- The linear map assigning to `h` the vector of constraint evaluations
`i ↦ gᵢᵀ h`. -/
noncomputable def constraintMap {s : ℕ} {ι : Type*} [Fintype ι]
    (g : ι → Fin s → ℝ) : (Fin s → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun h i := g i ⬝ᵥ h
  map_add' x y := funext fun i => dotProduct_add (g i) x y
  map_smul' a x := funext fun i => dotProduct_smul a (g i) x

theorem mem_ker_constraintMap {s : ℕ} {ι : Type*} [Fintype ι]
    (g : ι → Fin s → ℝ) (h : Fin s → ℝ) :
    h ∈ LinearMap.ker (constraintMap g) ↔ ∀ i, g i ⬝ᵥ h = 0 := by
  rw [LinearMap.mem_ker]
  change (fun i => g i ⬝ᵥ h) = 0 ↔ ∀ i, g i ⬝ᵥ h = 0
  rw [funext_iff]
  exact forall_congr' fun i => by rw [Pi.zero_apply]

/-- `dim ker T + k ≥ s` for a constraint map `T : ℝˢ → ℝᵏ`. -/
theorem finrank_ker_constraintMap_ge {s : ℕ} {ι : Type*} [Fintype ι]
    (g : ι → Fin s → ℝ) :
    Module.finrank ℝ (LinearMap.ker (constraintMap g)) + Fintype.card ι ≥ s := by
  have hrank := LinearMap.finrank_range_add_finrank_ker (constraintMap g)
  have hle : Module.finrank ℝ (LinearMap.range (constraintMap g)) ≤ Fintype.card ι := by
    calc
      Module.finrank ℝ (LinearMap.range (constraintMap g)) ≤
          Module.finrank ℝ (ι → ℝ) := Submodule.finrank_le _
      _ = Fintype.card ι := Module.finrank_pi ℝ
  rw [Module.finrank_fin_fun ℝ] at hrank
  omega

/-- Intersecting `E₀` with the kernel of `k` constraints loses at most `k`
dimensions: `dim (E₀ ⊓ ker T) + k ≥ dim E₀`. -/
theorem finrank_inf_ker_constraintMap_ge {s : ℕ} {ι : Type*} [Fintype ι]
    (E0 : Submodule ℝ (Fin s → ℝ)) (g : ι → Fin s → ℝ) :
    Module.finrank ℝ ↥(E0 ⊓ LinearMap.ker (constraintMap g)) + Fintype.card ι ≥
      Module.finrank ℝ ↥E0 := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq E0 (LinearMap.ker (constraintMap g))
  have hker := finrank_ker_constraintMap_ge g
  have hle : Module.finrank ℝ ↥(E0 ⊔ LinearMap.ker (constraintMap g)) ≤ s := by
    calc
      Module.finrank ℝ ↥(E0 ⊔ LinearMap.ker (constraintMap g)) ≤
          Module.finrank ℝ (Fin s → ℝ) := Submodule.finrank_le _
      _ = s := Module.finrank_fin_fun ℝ
  omega

/-- Conditional (B.4): if `E₀` has dimension at least `(1 − μ₅)·s` and
satisfies the curvature bound `hᵀQh ≤ (1−ρ) hᵀDh`, and there are at most
`(μ₁+μ₂+μ₃+μ₄)·s` linear constraints `gᵢᵀh = 0`, then
`E = E₀ ⊓ ker(constraintMap g)` has dimension `> s/32`, satisfies the same
curvature bound, and is annihilated by every constraint. -/
theorem spectral_subspace_exists {s : ℕ} {ι : Type*} [Fintype ι]
    (hs : 0 < s)
    (E0 : Submodule ℝ (Fin s → ℝ)) (g : ι → Fin s → ℝ)
    (Q D : Input s s) (ρ : ℝ)
    (hE0dim : (1 - (1 + 4 / 25) * (1 + 1 / 10000) /
        (4 * (1 - 4 / 25) * (1 - 1 / 64))) * (s : ℝ) ≤ Module.finrank ℝ E0)
    (hcard : (Fintype.card ι : ℝ) ≤
      (1 / (291 / 200) ^ 2 + 5 * (65 / 64) ^ 4 / 238 +
        1 / (64 * (4 / 25 - 3 / 625)) + 1 / 2048) * s)
    (hE0prop : ∀ h ∈ E0, h ⬝ᵥ (Q *ᵥ h) ≤ (1 - ρ) * (h ⬝ᵥ (D *ᵥ h))) :
    ∃ E : Submodule ℝ (Fin s → ℝ),
      (s : ℝ) / 32 < Module.finrank ℝ E ∧
      (∀ h ∈ E, h ⬝ᵥ (Q *ᵥ h) ≤ (1 - ρ) * (h ⬝ᵥ (D *ᵥ h))) ∧
      ∀ h ∈ E, ∀ i, g i ⬝ᵥ h = 0 := by
  refine ⟨E0 ⊓ LinearMap.ker (constraintMap g), ?_, ?_, ?_⟩
  · have hfin := finrank_inf_ker_constraintMap_ge E0 g
    have hcast : (Module.finrank ℝ E0 : ℝ) - Fintype.card ι ≤
        Module.finrank ℝ ↥(E0 ⊓ LinearMap.ker (constraintMap g)) := by
      have hR : (Module.finrank ℝ E0 : ℝ) ≤
          (Module.finrank ℝ ↥(E0 ⊓ LinearMap.ker (constraintMap g)) : ℝ) +
            Fintype.card ι := by
        exact_mod_cast hfin
      linarith
    have hTlt : (1 / (291 / 200) ^ 2 + 5 * (65 / 64) ^ 4 / 238 +
        1 / (64 * (4 / 25 - 3 / 625)) + 1 / 2048 +
        (1 + 4 / 25) * (1 + 1 / 10000) / (4 * (1 - 4 / 25) * (1 - 1 / 64)) : ℝ) <
        31 / 32 := by
      norm_num
    have hprod := mul_lt_mul_of_pos_right hTlt (Nat.cast_pos.mpr hs)
    have hcoef : (s : ℝ) / 32 <
        (1 - (1 + 4 / 25) * (1 + 1 / 10000) / (4 * (1 - 4 / 25) * (1 - 1 / 64))) * s -
          (1 / (291 / 200) ^ 2 + 5 * (65 / 64) ^ 4 / 238 +
            1 / (64 * (4 / 25 - 3 / 625)) + 1 / 2048) * s := by
      linarith [hprod]
    have key : (1 - (1 + 4 / 25) * (1 + 1 / 10000) /
          (4 * (1 - 4 / 25) * (1 - 1 / 64))) * (s : ℝ) -
        (1 / (291 / 200) ^ 2 + 5 * (65 / 64) ^ 4 / 238 +
          1 / (64 * (4 / 25 - 3 / 625)) + 1 / 2048) * s ≤
        (Module.finrank ℝ ↥(E0 ⊓ LinearMap.ker (constraintMap g)) : ℝ) := by
      linarith [hcast, hE0dim, hcard]
    exact lt_of_lt_of_le hcoef key
  · intro h hh
    exact hE0prop h (Submodule.mem_inf.mp hh).1
  · intro h hh i
    exact (mem_ker_constraintMap g h).mp (Submodule.mem_inf.mp hh).2 i

/-- The `dim > s/32` bound in ceil form: there is a subspace `E` of dimension
at least `⌈s/32⌉₊` with the curvature and constraint properties. -/
theorem spectral_subspace_dimension {s : ℕ} {ι : Type*} [Fintype ι]
    (hs : 0 < s)
    (E0 : Submodule ℝ (Fin s → ℝ)) (g : ι → Fin s → ℝ)
    (Q D : Input s s) (ρ : ℝ)
    (hE0dim : (1 - (1 + 4 / 25) * (1 + 1 / 10000) /
        (4 * (1 - 4 / 25) * (1 - 1 / 64))) * (s : ℝ) ≤ Module.finrank ℝ E0)
    (hcard : (Fintype.card ι : ℝ) ≤
      (1 / (291 / 200) ^ 2 + 5 * (65 / 64) ^ 4 / 238 +
        1 / (64 * (4 / 25 - 3 / 625)) + 1 / 2048) * s)
    (hE0prop : ∀ h ∈ E0, h ⬝ᵥ (Q *ᵥ h) ≤ (1 - ρ) * (h ⬝ᵥ (D *ᵥ h))) :
    ∃ E : Submodule ℝ (Fin s → ℝ),
      ⌈(s : ℝ) / 32⌉₊ ≤ Module.finrank ℝ E ∧
      (∀ h ∈ E, h ⬝ᵥ (Q *ᵥ h) ≤ (1 - ρ) * (h ⬝ᵥ (D *ᵥ h))) ∧
      ∀ h ∈ E, ∀ i, g i ⬝ᵥ h = 0 := by
  obtain ⟨E, hdim, hprop, hker⟩ :=
    spectral_subspace_exists hs E0 g Q D ρ hE0dim hcard hE0prop
  exact ⟨E, Nat.ceil_le.mpr hdim.le, hprop, hker⟩

/-! ### Positive-semidefinite two-dimensional quadratic forms -/

/-- The two-dimensional quadratic form of a positive-semidefinite matrix at
`a eⱼ + b eₖ` is nonnegative. -/
theorem posSemidef_two_quad {s : ℕ} {D : Input s s} (hD : D.PosSemidef)
    (j k : Fin s) (a b : ℝ) :
    0 ≤ a * (a * D j j + b * D j k) + b * (a * D k j + b * D k k) := by
  classical
  have h := hD.dotProduct_mulVec_nonneg (Pi.single j a + Pi.single k b)
  have heq : (Pi.single j a + Pi.single k b) ⬝ᵥ (D *ᵥ (Pi.single j a + Pi.single k b)) =
      a * (a * D j j + b * D j k) + b * (a * D k j + b * D k k) := by
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
    simp only [single_dotProduct, Matrix.mulVec, dotProduct_single]
    ring
  simp only [star_trivial] at h
  rw [heq] at h
  exact h

/-- A positive-semidefinite matrix with a vanishing diagonal entry has the
whole corresponding column equal to zero. -/
theorem posSemidef_eq_zero_of_diag {s : ℕ} {D : Input s s} (hD : D.PosSemidef)
    {j : Fin s} (hjj : D j j = 0) (k : Fin s) : D k j = 0 := by
  by_cases hd : D k j = 0
  · exact hd
  · exfalso
    have hsym : D j k = D k j := by
      simpa using hD.1.apply k j
    have hq := posSemidef_two_quad hD j k (-(D k k + 1) / (2 * D k j)) 1
    rw [hjj, hsym] at hq
    simp only [mul_zero] at hq
    have hkey : -(D k k + 1) / (2 * D k j) * (D k j) = -(D k k + 1) / 2 := by
      field_simp
    nlinarith [hq]

/-- The discriminant bound `Rjk² ≤ Rjj Rkk` for a positive-semidefinite
matrix `D` — applied downstream to the resolvent inverse `R` (which is
positive semidefinite whenever the slack is positive definite).  This is the
`(a, b) = (D j k, -D j j)` case of `posSemidef_two_quad`, with the degenerate
case `D j j = 0` discharged by `posSemidef_eq_zero_of_diag`. -/
theorem matrix_inverse_entry_sq_le {s : ℕ} {D : Input s s} (hD : D.PosSemidef)
    (j k : Fin s) : (D j k) ^ 2 ≤ D j j * D k k := by
  have hsymm : D j k = D k j := by simpa using hD.1.apply k j
  have hDjj0 : 0 ≤ D j j := by
    have h := posSemidef_two_quad hD j k 1 0
    simpa using h
  by_cases hjj : D j j = 0
  · have hkj : D k j = 0 := posSemidef_eq_zero_of_diag hD hjj k
    have hjk : D j k = 0 := hsymm.trans hkj
    rw [hjk, hjj]
    norm_num
  · have hDjj : 0 < D j j := lt_of_le_of_ne' hDjj0 hjj
    have ha := posSemidef_two_quad hD j k (D j k) (-(D j j))
    rw [← hsymm] at ha
    have e2 : D j j * (D j k) ^ 2 ≤ D j j * (D j j * D k k) := by linarith [ha]
    exact le_of_mul_le_mul_left e2 hDjj

/-! ### Conditional differentiation lemmas (B.3) -/

/-- Entrywise continuity of the path `t ↦ W(t)` defined by an affine matrix
path: `(N₁ + tN₂) *ᵥ v` tends to `N₁ *ᵥ v` at `0`. -/
theorem tendsto_pathW {s : ℕ} (N₁ N₂ : Input s s) (v : Fin s → ℝ) :
    Tendsto (fun t : ℝ => (N₁ + t • N₂) *ᵥ v) (𝓝 0) (𝓝 (N₁ *ᵥ v)) := by
  have heq : (fun t : ℝ => (N₁ + t • N₂) *ᵥ v) =
      fun t : ℝ => N₁ *ᵥ v + t • (N₂ *ᵥ v) := by
    funext t
    rw [Matrix.add_mulVec, Matrix.smul_mulVec]
  rw [heq]
  have h : Tendsto (fun t : ℝ => N₁ *ᵥ v + t • (N₂ *ᵥ v)) (𝓝 0)
      (𝓝 (N₁ *ᵥ v + (0 : ℝ) • (N₂ *ᵥ v))) :=
    Tendsto.add tendsto_const_nhds
      (Tendsto.smul (tendsto_id : Tendsto id (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)))
        tendsto_const_nhds)
  simpa using h

/-- `Tendsto` of a constant-matrix `mulVec` applied to a tending vector. -/
theorem tendsto_mulVec {s : ℕ} (N : Input s s) {X : ℝ → Fin s → ℝ} {x₀ : Fin s → ℝ}
    {t₀ : ℝ} (hX : Tendsto X (𝓝 t₀) (𝓝 x₀)) :
    Tendsto (fun t => N *ᵥ X t) (𝓝 t₀) (𝓝 (N *ᵥ x₀)) := by
  rw [tendsto_pi_nhds] at hX ⊢
  intro j
  have hfun : (fun t => (N *ᵥ X t) j) = fun t => ∑ k, N j k * X t k := by
    funext t
    rfl
  have hx : (N *ᵥ x₀) j = ∑ k, N j k * x₀ k := rfl
  rw [hfun, hx]
  apply tendsto_finsetSum
  intro k _
  exact Tendsto.mul tendsto_const_nhds (hX k)

/-- `Tendsto` of the dot product of two tending vector functions. -/
theorem tendsto_dotProduct_of_tendsto {s : ℕ} {X Y : ℝ → Fin s → ℝ}
    {x₀ y₀ : Fin s → ℝ} {t₀ : ℝ}
    (hX : Tendsto X (𝓝 t₀) (𝓝 x₀)) (hY : Tendsto Y (𝓝 t₀) (𝓝 y₀)) :
    Tendsto (fun t => X t ⬝ᵥ Y t) (𝓝 t₀) (𝓝 (x₀ ⬝ᵥ y₀)) := by
  rw [tendsto_pi_nhds] at hX hY
  have hfun : (fun t => X t ⬝ᵥ Y t) = fun t => ∑ j, X t j * Y t j := by
    funext t
    rfl
  have hxy : x₀ ⬝ᵥ y₀ = ∑ j, x₀ j * y₀ j := rfl
  rw [hfun, hxy]
  apply tendsto_finsetSum
  intro j _
  exact Tendsto.mul (hX j) (hY j)

/-- `Tendsto` of `R_t *ᵥ W_t` given entrywise continuity of `R_t` and a
tending vector `W_t`. -/
theorem tendsto_resolvent_mulVec {s : ℕ} {b : ℝ} {P : ℝ → Input s s} {t₀ : ℝ}
    (hcont : ContinuousAt (fun t => (slackMatrix b (P t))⁻¹) t₀)
    {W : ℝ → Fin s → ℝ} {w₀ : Fin s → ℝ}
    (hW : Tendsto W (𝓝 t₀) (𝓝 w₀)) :
    Tendsto (fun t => (slackMatrix b (P t))⁻¹ *ᵥ W t) (𝓝 t₀)
      (𝓝 ((slackMatrix b (P t₀))⁻¹ *ᵥ w₀)) := by
  have hcont' : ∀ j k : Fin s,
      ContinuousAt (fun t => (slackMatrix b (P t))⁻¹ j k) t₀ := fun j k =>
    (continuousAt_pi.mp ((continuousAt_pi.mp hcont) j)) k
  rw [tendsto_pi_nhds] at hW ⊢
  intro j
  have hfun : (fun t => ((slackMatrix b (P t))⁻¹ *ᵥ W t) j) =
      fun t => ∑ k, (slackMatrix b (P t))⁻¹ j k * W t k := by
    funext t
    rfl
  have hx : ((slackMatrix b (P t₀))⁻¹ *ᵥ w₀) j =
      ∑ k, (slackMatrix b (P t₀))⁻¹ j k * w₀ k := rfl
  rw [hfun, hx]
  apply tendsto_finsetSum
  intro k _
  exact Tendsto.mul (hcont' j k) (hW k)

/-- `Tendsto` of `x ⬝ᵥ (R_t *ᵥ y)` for constant `x, y`. -/
theorem tendsto_dotProduct_resolvent_mulVec {s : ℕ} {b : ℝ} {P : ℝ → Input s s}
    {t₀ : ℝ} (x y : Fin s → ℝ)
    (hcont : ContinuousAt (fun t => (slackMatrix b (P t))⁻¹) t₀) :
    Tendsto (fun t => x ⬝ᵥ ((slackMatrix b (P t))⁻¹ *ᵥ y)) (𝓝 t₀)
      (𝓝 (x ⬝ᵥ ((slackMatrix b (P t₀))⁻¹ *ᵥ y))) :=
  tendsto_dotProduct_of_tendsto tendsto_const_nhds
    (tendsto_resolvent_mulVec hcont tendsto_const_nhds)

/-- **Conditional (B.3), first derivative.** Along `t ↦ M + tN`, the
resolvent potential has derivative `vᵀNv` at `0`, provided the slack matrix
stays positive definite near `0` and `t ↦ R_t` is entrywise continuous at `0`.
The algebraic step `slope = V₁ + t·q_t` is the exact identity
`resolventPotential_step_taylor`; the missing analytic input is only the
continuity of the inverse. -/
theorem hasDerivAt_resolventPotential {s : ℕ} {b : ℝ} {M N : Input s s}
    (hMpos : (slackMatrix b M).PosDef)
    (hnbhd : ∀ᶠ (t : ℝ) in 𝓝 0, (slackMatrix b (M + t • N)).PosDef)
    (hcont : ContinuousAt (fun t : ℝ => (slackMatrix b (M + t • N))⁻¹) 0) :
    HasDerivAt (fun t : ℝ => resolventPotential b (M + t • N))
      (resolventVariation1 b M N) 0 := by
  have hq : Tendsto (fun t : ℝ => (N *ᵥ resolventVector b M) ⬝ᵥ
        ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M))) (𝓝[≠] 0)
      (𝓝 ((N *ᵥ resolventVector b M) ⬝ᵥ
        ((slackMatrix b M)⁻¹ *ᵥ (N *ᵥ resolventVector b M)))) := by
    have h := tendsto_dotProduct_resolvent_mulVec
      (P := fun t => M + t • N) (N *ᵥ resolventVector b M)
      (N *ᵥ resolventVector b M) hcont
    simp only [zero_smul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hslope : (fun t : ℝ => slope (fun t : ℝ => resolventPotential b (M + t • N)) 0 t) =ᶠ[𝓝[≠] (0 : ℝ)]
      fun t => resolventVariation1 b M N + t *
        ((N *ᵥ resolventVector b M) ⬝ᵥ
          ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M))) := by
    filter_upwards [hnbhd.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t ht ht0
    have ht0' : t ≠ 0 := by simpa using ht0
    have h := resolventPotential_step_taylor hMpos ht
    rw [slope_def_field]
    simp only [sub_zero, zero_smul, add_zero]
    rw [h, div_eq_iff ht0']
    ring
  rw [hasDerivAt_iff_tendsto_slope]
  apply Tendsto.congr' hslope.symm
  have hlim : Tendsto (fun t : ℝ => resolventVariation1 b M N + t *
        ((N *ᵥ resolventVector b M) ⬝ᵥ
          ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M))))
        (𝓝[≠] 0) (𝓝 (resolventVariation1 b M N)) := by
    have := Tendsto.add
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => resolventVariation1 b M N) (𝓝[≠] 0)
        (𝓝 (resolventVariation1 b M N)))
      (Tendsto.mul (tendsto_id.mono_left nhdsWithin_le_nhds) hq)
    simpa using this
  exact hlim

/-- **Conditional (B.3), second derivative (affine path).** Along `t ↦ M+tN`
with `N` symmetric, `t ↦ v_tᵀNv_t` has derivative `2(Nv)ᵀR(Nv)` at `0` —
exactly `F''` of (B.3) with `M'' = 0`. -/
theorem hasDerivAt_resolventQuadraticForm {s : ℕ} {b : ℝ} {M N : Input s s}
    (hNsymm : ∀ j k, N j k = N k j)
    (hMpos : (slackMatrix b M).PosDef)
    (hnbhd : ∀ᶠ (t : ℝ) in 𝓝 0, (slackMatrix b (M + t • N)).PosDef)
    (hcont : ContinuousAt (fun t : ℝ => (slackMatrix b (M + t • N))⁻¹) 0) :
    HasDerivAt (fun t : ℝ => resolventVector b (M + t • N) ⬝ᵥ
        (N *ᵥ resolventVector b (M + t • N))) (resolventVariation2 b M N) 0 := by
  have hid : ∀ t : ℝ, (slackMatrix b (M + t • N)).PosDef →
      resolventVector b (M + t • N) ⬝ᵥ (N *ᵥ resolventVector b (M + t • N)) -
          resolventVector b M ⬝ᵥ (N *ᵥ resolventVector b M) =
        t * (((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M)) ⬝ᵥ
            (N *ᵥ resolventVector b M)) +
          t * ((N *ᵥ resolventVector b M) ⬝ᵥ
            ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M))) +
          t ^ 2 * (((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M)) ⬝ᵥ
            (N *ᵥ ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M)))) := by
    intro t ht
    set w := N *ᵥ resolventVector b M with hw
    set d := resolventVector b (M + t • N) - resolventVector b M with hd
    have hd2 : d = t • ((slackMatrix b (M + t • N))⁻¹ *ᵥ w) :=
      resolvent_step_eq hMpos ht
    have hvt : resolventVector b (M + t • N) = resolventVector b M + d := by
      simp [hd]
    have hbilin : resolventVector b (M + t • N) ⬝ᵥ (N *ᵥ resolventVector b (M + t • N)) =
        resolventVector b M ⬝ᵥ w + d ⬝ᵥ w +
          resolventVector b M ⬝ᵥ (N *ᵥ d) + d ⬝ᵥ (N *ᵥ d) := by
      rw [hvt, Matrix.mulVec_add]
      rw [add_dotProduct, dotProduct_add, dotProduct_add, ← hw]
      ring
    have hswap : resolventVector b M ⬝ᵥ (N *ᵥ d) = w ⬝ᵥ d := by
      rw [dotProduct_mulVec_eq hNsymm]
    have hd1 : d ⬝ᵥ w = t * (((slackMatrix b (M + t • N))⁻¹ *ᵥ w) ⬝ᵥ w) := by
      rw [hd2, smul_dotProduct, smul_eq_mul]
    have hd1' : w ⬝ᵥ d = t * (w ⬝ᵥ ((slackMatrix b (M + t • N))⁻¹ *ᵥ w)) := by
      rw [hd2, dotProduct_smul, smul_eq_mul]
    have hdN : d ⬝ᵥ (N *ᵥ d) = t ^ 2 *
        (((slackMatrix b (M + t • N))⁻¹ *ᵥ w) ⬝ᵥ
          (N *ᵥ ((slackMatrix b (M + t • N))⁻¹ *ᵥ w))) := by
      rw [hd2, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
      simp only [smul_eq_mul]
      ring
    rw [hbilin, hswap, hd1, hd1', hdN]
    ring
  have hq : Tendsto (fun t : ℝ => ((slackMatrix b (M + t • N))⁻¹ *ᵥ
        (N *ᵥ resolventVector b M)) ⬝ᵥ (N *ᵥ resolventVector b M)) (𝓝[≠] 0)
      (𝓝 (((slackMatrix b M)⁻¹ *ᵥ (N *ᵥ resolventVector b M)) ⬝ᵥ
        (N *ᵥ resolventVector b M))) := by
    have h := tendsto_dotProduct_of_tendsto
      (tendsto_resolvent_mulVec (P := fun t => M + t • N) hcont
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => N *ᵥ resolventVector b M) (𝓝 0)
          (𝓝 (N *ᵥ resolventVector b M))))
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => N *ᵥ resolventVector b M) (𝓝 0)
        (𝓝 (N *ᵥ resolventVector b M)))
    simp only [zero_smul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hq' : Tendsto (fun t : ℝ => (N *ᵥ resolventVector b M) ⬝ᵥ
        ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M))) (𝓝[≠] 0)
      (𝓝 ((N *ᵥ resolventVector b M) ⬝ᵥ
        ((slackMatrix b M)⁻¹ *ᵥ (N *ᵥ resolventVector b M)))) := by
    have h := tendsto_dotProduct_resolvent_mulVec (P := fun t => M + t • N)
      (N *ᵥ resolventVector b M) (N *ᵥ resolventVector b M) hcont
    simp only [zero_smul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun t : ℝ => ((slackMatrix b (M + t • N))⁻¹ *ᵥ
        (N *ᵥ resolventVector b M)) ⬝ᵥ
        (N *ᵥ ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M)))) (𝓝[≠] 0)
      (𝓝 (((slackMatrix b M)⁻¹ *ᵥ (N *ᵥ resolventVector b M)) ⬝ᵥ
        (N *ᵥ ((slackMatrix b M)⁻¹ *ᵥ (N *ᵥ resolventVector b M))))) := by
    have hX := tendsto_resolvent_mulVec (P := fun t => M + t • N) hcont
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => N *ᵥ resolventVector b M) (𝓝 0)
        (𝓝 (N *ᵥ resolventVector b M)))
    have h := tendsto_dotProduct_of_tendsto hX (tendsto_mulVec N hX)
    simp only [zero_smul, add_zero] at hX h
    exact h.mono_left nhdsWithin_le_nhds
  have hslope : (fun t : ℝ => slope (fun t : ℝ => resolventVector b (M + t • N) ⬝ᵥ
        (N *ᵥ resolventVector b (M + t • N))) 0 t) =ᶠ[𝓝[≠] (0 : ℝ)]
      fun t => (((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M)) ⬝ᵥ
          (N *ᵥ resolventVector b M)) +
        ((N *ᵥ resolventVector b M) ⬝ᵥ
          ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M))) +
        t * (((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M)) ⬝ᵥ
          (N *ᵥ ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M)))) := by
    filter_upwards [hnbhd.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t ht ht0
    have ht0' : t ≠ 0 := by simpa using ht0
    have h := hid t ht
    rw [slope_def_field]
    simp only [sub_zero, zero_smul, add_zero]
    rw [h, div_eq_iff ht0']
    ring
  rw [hasDerivAt_iff_tendsto_slope]
  apply Tendsto.congr' hslope.symm
  have hlim : Tendsto (fun t : ℝ =>
        (((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M)) ⬝ᵥ
          (N *ᵥ resolventVector b M)) +
        ((N *ᵥ resolventVector b M) ⬝ᵥ
          ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M))) +
        t * (((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M)) ⬝ᵥ
          (N *ᵥ ((slackMatrix b (M + t • N))⁻¹ *ᵥ (N *ᵥ resolventVector b M)))))
      (𝓝[≠] 0) (𝓝 (resolventVariation2 b M N)) := by
    have h := Tendsto.add (Tendsto.add hq hq')
      (Tendsto.mul (tendsto_id.mono_left nhdsWithin_le_nhds) hr)
    have hgoal : (N *ᵥ resolventVector b M) ⬝ᵥ
        ((slackMatrix b M)⁻¹ *ᵥ (N *ᵥ resolventVector b M)) =
      ((slackMatrix b M)⁻¹ *ᵥ (N *ᵥ resolventVector b M)) ⬝ᵥ
        (N *ᵥ resolventVector b M) := dotProduct_comm _ _
    have heq : ((slackMatrix b M)⁻¹ *ᵥ (N *ᵥ resolventVector b M)) ⬝ᵥ
          (N *ᵥ resolventVector b M) +
        ((N *ᵥ resolventVector b M) ⬝ᵥ
          ((slackMatrix b M)⁻¹ *ᵥ (N *ᵥ resolventVector b M))) +
        (0 : ℝ) * (((slackMatrix b M)⁻¹ *ᵥ (N *ᵥ resolventVector b M)) ⬝ᵥ
          (N *ᵥ ((slackMatrix b M)⁻¹ *ᵥ (N *ᵥ resolventVector b M)))) =
        resolventVariation2 b M N := by
      unfold resolventVariation2
      rw [hgoal]
      ring
    rwa [heq] at h
  exact hlim

/-- The slope `F'_t` proxy along the quadratic path `M(t) = M + tN₁ + t²N₂`:
`potentialSlope t = v_tᵀ (N₁ + 2tN₂) v_t`, which equals `F'(t)` whenever `F`
is differentiable (`M'(t) = N₁ + 2tN₂`). -/
noncomputable def potentialSlope {s : ℕ} (b : ℝ) (M N₁ N₂ : Input s s) (t : ℝ) : ℝ :=
  resolventVector b (M + t • N₁ + t ^ 2 • N₂) ⬝ᵥ
    ((N₁ + (2 * t) • N₂) *ᵥ resolventVector b (M + t • N₁ + t ^ 2 • N₂))

/-- The second derivative of the potential at `0` along
`M(t) = M + tN₁ + t²N₂` (`M''(0) = 2N₂`):
`2 v₀ᵀN₂v₀ + 2 (N₁v₀)ᵀR(N₁v₀)`, the `vᵀM''v + 2(M'v)ᵀR(M'v)` of (B.3). -/
noncomputable def potentialHessian {s : ℕ} (b : ℝ) (M N₁ N₂ : Input s s) : ℝ :=
  2 * (resolventVector b M ⬝ᵥ (N₂ *ᵥ resolventVector b M)) +
    2 * ((N₁ *ᵥ resolventVector b M) ⬝ᵥ
      ((slackMatrix b M)⁻¹ *ᵥ (N₁ *ᵥ resolventVector b M)))

/-- The resolvent-vector step along the quadratic path. -/
theorem resolvent_vector_path_sub {s : ℕ} {b t : ℝ} {M N₁ N₂ : Input s s}
    (hMpos : (slackMatrix b M).PosDef)
    (hpos : (slackMatrix b (M + t • N₁ + t ^ 2 • N₂)).PosDef) :
    resolventVector b (M + t • N₁ + t ^ 2 • N₂) - resolventVector b M =
      t • ((slackMatrix b (M + t • N₁ + t ^ 2 • N₂))⁻¹ *ᵥ
        ((N₁ + t • N₂) *ᵥ resolventVector b M)) := by
  have hsub : (M + t • N₁ + t ^ 2 • N₂) - M = t • (N₁ + t • N₂) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [resolvent_vector_difference hMpos hpos, hsub, smul_mulVec, Matrix.mulVec_smul]

/-- Symmetry of the effective path derivative `Q_t = N₁ + 2tN₂`. -/
theorem pathQ_symm {s : ℕ} {N₁ N₂ : Input s s}
    (h₁ : ∀ j k, N₁ j k = N₁ k j) (h₂ : ∀ j k, N₂ j k = N₂ k j)
    (t : ℝ) (j k : Fin s) :
    (N₁ + (2 * t) • N₂) j k = (N₁ + (2 * t) • N₂) k j := by
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [h₁ j k, h₂ j k]

/-- The exact difference identity for `potentialSlope` along the quadratic
path (the algebraic content of `F'' = vᵀM''v + 2(M'v)ᵀR(M'v)`):
`potentialSlope t − potentialSlope 0 =
  2t·(R_t W_t)ᵀ(Q_t v₀) + t²·(R_tW_t)ᵀ Q_t (R_tW_t) + 2t·v₀ᵀN₂v₀`
where `W_t = (N₁ + tN₂)v₀` and `Q_t = N₁ + 2tN₂`. -/
theorem potentialSlope_sub {s : ℕ} {b t : ℝ} {M N₁ N₂ : Input s s}
    (hN₁symm : ∀ j k, N₁ j k = N₁ k j) (hN₂symm : ∀ j k, N₂ j k = N₂ k j)
    (hMpos : (slackMatrix b M).PosDef)
    (hpos : (slackMatrix b (M + t • N₁ + t ^ 2 • N₂)).PosDef) :
    potentialSlope b M N₁ N₂ t - potentialSlope b M N₁ N₂ 0 =
      2 * t * (((slackMatrix b (M + t • N₁ + t ^ 2 • N₂))⁻¹ *ᵥ
            ((N₁ + t • N₂) *ᵥ resolventVector b M)) ⬝ᵥ
          (N₁ *ᵥ resolventVector b M + (2 * t) • (N₂ *ᵥ resolventVector b M))) +
        t ^ 2 * (((slackMatrix b (M + t • N₁ + t ^ 2 • N₂))⁻¹ *ᵥ
            ((N₁ + t • N₂) *ᵥ resolventVector b M)) ⬝ᵥ
          ((N₁ + (2 * t) • N₂) *ᵥ ((slackMatrix b (M + t • N₁ + t ^ 2 • N₂))⁻¹ *ᵥ
            ((N₁ + t • N₂) *ᵥ resolventVector b M)))) +
        2 * t * (resolventVector b M ⬝ᵥ (N₂ *ᵥ resolventVector b M)) := by
  set R := (slackMatrix b (M + t • N₁ + t ^ 2 • N₂))⁻¹
  set W := (N₁ + t • N₂) *ᵥ resolventVector b M
  set d := t • (R *ᵥ W)
  have hstep : resolventVector b (M + t • N₁ + t ^ 2 • N₂) =
      resolventVector b M + d := by
    have h := resolvent_vector_path_sub hMpos hpos
    rwa [sub_eq_iff_eq_add'] at h
  have hQv0 : (N₁ + (2 * t) • N₂) *ᵥ resolventVector b M =
      N₁ *ᵥ resolventVector b M + (2 * t) • (N₂ *ᵥ resolventVector b M) := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec]
  have hS0 : potentialSlope b M N₁ N₂ 0 =
      resolventVector b M ⬝ᵥ (N₁ *ᵥ resolventVector b M) := by
    simp [potentialSlope]
  have hexp : potentialSlope b M N₁ N₂ t =
      resolventVector b M ⬝ᵥ ((N₁ + (2 * t) • N₂) *ᵥ resolventVector b M) +
        d ⬝ᵥ ((N₁ + (2 * t) • N₂) *ᵥ resolventVector b M) +
        resolventVector b M ⬝ᵥ ((N₁ + (2 * t) • N₂) *ᵥ d) +
        d ⬝ᵥ ((N₁ + (2 * t) • N₂) *ᵥ d) := by
    rw [potentialSlope, hstep, Matrix.mulVec_add,
      add_dotProduct, dotProduct_add, dotProduct_add]
    ring
  have hd1 : d ⬝ᵥ ((N₁ + (2 * t) • N₂) *ᵥ resolventVector b M) =
      t * ((R *ᵥ W) ⬝ᵥ (N₁ *ᵥ resolventVector b M + (2 * t) • (N₂ *ᵥ resolventVector b M))) := by
    rw [show d = t • (R *ᵥ W) from rfl, smul_dotProduct, smul_eq_mul, hQv0]
  have hd2 : resolventVector b M ⬝ᵥ ((N₁ + (2 * t) • N₂) *ᵥ d) =
      t * ((R *ᵥ W) ⬝ᵥ (N₁ *ᵥ resolventVector b M + (2 * t) • (N₂ *ᵥ resolventVector b M))) := by
    have hswap : resolventVector b M ⬝ᵥ ((N₁ + (2 * t) • N₂) *ᵥ d) =
        ((N₁ + (2 * t) • N₂) *ᵥ resolventVector b M) ⬝ᵥ d :=
      dotProduct_mulVec_eq (fun j k => pathQ_symm hN₁symm hN₂symm t j k) _ _
    rw [hswap, hQv0, show d = t • (R *ᵥ W) from rfl, dotProduct_smul, smul_eq_mul,
      dotProduct_comm]
  have hd3 : d ⬝ᵥ ((N₁ + (2 * t) • N₂) *ᵥ d) =
      t ^ 2 * ((R *ᵥ W) ⬝ᵥ ((N₁ + (2 * t) • N₂) *ᵥ (R *ᵥ W))) := by
    rw [show d = t • (R *ᵥ W) from rfl, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct]
    simp only [smul_eq_mul]
    ring
  have hsplit : resolventVector b M ⬝ᵥ ((N₁ + (2 * t) • N₂) *ᵥ resolventVector b M) =
      resolventVector b M ⬝ᵥ (N₁ *ᵥ resolventVector b M) +
        2 * t * (resolventVector b M ⬝ᵥ (N₂ *ᵥ resolventVector b M)) := by
    rw [hQv0, dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [hexp, hd1, hd2, hd3, hsplit, hS0]
  ring

/-- **Conditional (B.3), second derivative (general path).** Along the
quadratic path `M(t) = M + tN₁ + t²N₂` (with `N₁`, `N₂` symmetric), the slope
`potentialSlope` has derivative `2v₀ᵀN₂v₀ + 2(N₁v₀)ᵀR(N₁v₀)` at `0`, i.e.
`vᵀM''v + 2(M'v)ᵀR(M'v)`, provided `R_t` is entrywise continuous at `0` and
the slack stays positive definite near `0`. -/
theorem hasDerivAt_potentialSlope {s : ℕ} {b : ℝ} {M N₁ N₂ : Input s s}
    (hN₁symm : ∀ j k, N₁ j k = N₁ k j) (hN₂symm : ∀ j k, N₂ j k = N₂ k j)
    (hMpos : (slackMatrix b M).PosDef)
    (hnbhd : ∀ᶠ (t : ℝ) in 𝓝 0, (slackMatrix b (M + t • N₁ + t ^ 2 • N₂)).PosDef)
    (hcont : ContinuousAt (fun t : ℝ => (slackMatrix b (M + t • N₁ + t ^ 2 • N₂))⁻¹) 0) :
    HasDerivAt (potentialSlope b M N₁ N₂) (potentialHessian b M N₁ N₂) 0 := by
  set P : ℝ → Input s s := fun t => M + t • N₁ + t ^ 2 • N₂ with hP
  have hW : Tendsto (fun t : ℝ => (N₁ + t • N₂) *ᵥ resolventVector b M) (𝓝 0)
      (𝓝 (N₁ *ᵥ resolventVector b M)) := tendsto_pathW N₁ N₂ _
  have hX : Tendsto (fun t => (slackMatrix b (P t))⁻¹ *ᵥ
        ((N₁ + t • N₂) *ᵥ resolventVector b M)) (𝓝 0)
      (𝓝 ((slackMatrix b M)⁻¹ *ᵥ (N₁ *ᵥ resolventVector b M))) := by
    have h := tendsto_resolvent_mulVec hcont hW
    simp only [zero_smul, add_zero, pow_two, mul_zero] at h
    simp only [hP, pow_two]
    exact h
  have hA : Tendsto (fun t => ((slackMatrix b (P t))⁻¹ *ᵥ
        ((N₁ + t • N₂) *ᵥ resolventVector b M)) ⬝ᵥ
        (N₁ *ᵥ resolventVector b M + (2 * t) • (N₂ *ᵥ resolventVector b M))) (𝓝[≠] 0)
      (𝓝 (((slackMatrix b M)⁻¹ *ᵥ (N₁ *ᵥ resolventVector b M)) ⬝ᵥ
        (N₁ *ᵥ resolventVector b M))) := by
    have hY : Tendsto (fun t : ℝ => N₁ *ᵥ resolventVector b M +
          (2 * t) • (N₂ *ᵥ resolventVector b M)) (𝓝 0)
        (𝓝 (N₁ *ᵥ resolventVector b M)) := by
      have h := Tendsto.add
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => N₁ *ᵥ resolventVector b M) (𝓝 0)
          (𝓝 (N₁ *ᵥ resolventVector b M)))
        (Tendsto.smul
          (Tendsto.mul
            (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) (𝓝 0) (𝓝 2))
            (tendsto_id : Tendsto id (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))))
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => N₂ *ᵥ resolventVector b M) (𝓝 0)
            (𝓝 (N₂ *ᵥ resolventVector b M))))
      simpa using h
    exact (tendsto_dotProduct_of_tendsto hX hY).mono_left nhdsWithin_le_nhds
  have hB : Tendsto (fun t => ((slackMatrix b (P t))⁻¹ *ᵥ
        ((N₁ + t • N₂) *ᵥ resolventVector b M)) ⬝ᵥ
        ((N₁ + (2 * t) • N₂) *ᵥ ((slackMatrix b (P t))⁻¹ *ᵥ
          ((N₁ + t • N₂) *ᵥ resolventVector b M)))) (𝓝[≠] 0)
      (𝓝 (((slackMatrix b M)⁻¹ *ᵥ (N₁ *ᵥ resolventVector b M)) ⬝ᵥ
        (N₁ *ᵥ ((slackMatrix b M)⁻¹ *ᵥ (N₁ *ᵥ resolventVector b M))))) := by
    have hY : Tendsto (fun t => (N₁ + (2 * t) • N₂) *ᵥ
          ((slackMatrix b (P t))⁻¹ *ᵥ ((N₁ + t • N₂) *ᵥ resolventVector b M))) (𝓝 0)
        (𝓝 (N₁ *ᵥ ((slackMatrix b M)⁻¹ *ᵥ (N₁ *ᵥ resolventVector b M)))) := by
      have hQ : Tendsto (fun t : ℝ => (N₁ + (2 * t) • N₂)) (𝓝 0) (𝓝 N₁) := by
        have h := Tendsto.add
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => N₁) (𝓝 0) (𝓝 N₁))
          (Tendsto.smul
            (Tendsto.mul
              (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) (𝓝 0) (𝓝 2))
              (tendsto_id : Tendsto id (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))))
            (tendsto_const_nhds : Tendsto (fun _ : ℝ => N₂) (𝓝 0) (𝓝 N₂)))
        simpa using h
      have hQ' : ∀ j k : Fin s,
          Tendsto (fun t : ℝ => (N₁ + (2 * t) • N₂) j k) (𝓝 0) (𝓝 (N₁ j k)) := by
        intro j k
        have h := (tendsto_pi_nhds.mp hQ) j
        exact (tendsto_pi_nhds.mp h) k
      rw [tendsto_pi_nhds]
      intro j
      have hfun : (fun t => ((N₁ + (2 * t) • N₂) *ᵥ
            ((slackMatrix b (P t))⁻¹ *ᵥ ((N₁ + t • N₂) *ᵥ resolventVector b M))) j) =
          fun t => ∑ k, (N₁ + (2 * t) • N₂) j k *
            ((slackMatrix b (P t))⁻¹ *ᵥ ((N₁ + t • N₂) *ᵥ resolventVector b M)) k := by
        funext t
        rfl
      have hx : (N₁ *ᵥ ((slackMatrix b M)⁻¹ *ᵥ (N₁ *ᵥ resolventVector b M))) j =
          ∑ k, N₁ j k * ((slackMatrix b M)⁻¹ *ᵥ (N₁ *ᵥ resolventVector b M)) k := rfl
      rw [hfun, hx]
      apply tendsto_finsetSum
      intro k _
      exact Tendsto.mul (hQ' j k) ((tendsto_pi_nhds.mp hX) k)
    exact (tendsto_dotProduct_of_tendsto hX hY).mono_left nhdsWithin_le_nhds
  have hslope : (fun t : ℝ => slope (potentialSlope b M N₁ N₂) 0 t) =ᶠ[𝓝[≠] (0 : ℝ)]
      fun t => 2 * (((slackMatrix b (P t))⁻¹ *ᵥ
            ((N₁ + t • N₂) *ᵥ resolventVector b M)) ⬝ᵥ
          (N₁ *ᵥ resolventVector b M + (2 * t) • (N₂ *ᵥ resolventVector b M))) +
        t * (((slackMatrix b (P t))⁻¹ *ᵥ
            ((N₁ + t • N₂) *ᵥ resolventVector b M)) ⬝ᵥ
          ((N₁ + (2 * t) • N₂) *ᵥ ((slackMatrix b (P t))⁻¹ *ᵥ
            ((N₁ + t • N₂) *ᵥ resolventVector b M)))) +
        2 * (resolventVector b M ⬝ᵥ (N₂ *ᵥ resolventVector b M)) := by
    filter_upwards [hnbhd.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t ht ht0
    have ht0' : t ≠ 0 := by simpa using ht0
    have h := potentialSlope_sub hN₁symm hN₂symm hMpos ht
    rw [slope_def_field]
    simp only [sub_zero]
    have heq : (potentialSlope b M N₁ N₂ t - potentialSlope b M N₁ N₂ 0) / t =
        2 * (((slackMatrix b (P t))⁻¹ *ᵥ
            ((N₁ + t • N₂) *ᵥ resolventVector b M)) ⬝ᵥ
          (N₁ *ᵥ resolventVector b M + (2 * t) • (N₂ *ᵥ resolventVector b M))) +
        t * (((slackMatrix b (P t))⁻¹ *ᵥ
            ((N₁ + t • N₂) *ᵥ resolventVector b M)) ⬝ᵥ
          ((N₁ + (2 * t) • N₂) *ᵥ ((slackMatrix b (P t))⁻¹ *ᵥ
            ((N₁ + t • N₂) *ᵥ resolventVector b M)))) +
        2 * (resolventVector b M ⬝ᵥ (N₂ *ᵥ resolventVector b M)) := by
      rw [h]
      rw [div_eq_iff ht0']
      ring
    rw [heq]
  rw [hasDerivAt_iff_tendsto_slope]
  apply Tendsto.congr' hslope.symm
  have hlim : Tendsto (fun t : ℝ => 2 * (((slackMatrix b (P t))⁻¹ *ᵥ
            ((N₁ + t • N₂) *ᵥ resolventVector b M)) ⬝ᵥ
          (N₁ *ᵥ resolventVector b M + (2 * t) • (N₂ *ᵥ resolventVector b M))) +
        t * (((slackMatrix b (P t))⁻¹ *ᵥ
            ((N₁ + t • N₂) *ᵥ resolventVector b M)) ⬝ᵥ
          ((N₁ + (2 * t) • N₂) *ᵥ ((slackMatrix b (P t))⁻¹ *ᵥ
            ((N₁ + t • N₂) *ᵥ resolventVector b M)))) +
        2 * (resolventVector b M ⬝ᵥ (N₂ *ᵥ resolventVector b M)))
      (𝓝[≠] 0) (𝓝 (potentialHessian b M N₁ N₂)) := by
    have h2 := Tendsto.add
      (Tendsto.add
        (Tendsto.mul
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) (𝓝[≠] 0) (𝓝 2)) hA)
        (Tendsto.mul (tendsto_id.mono_left nhdsWithin_le_nhds) hB))
      (tendsto_const_nhds : Tendsto
        (fun _ : ℝ => 2 * (resolventVector b M ⬝ᵥ (N₂ *ᵥ resolventVector b M)))
        (𝓝[≠] 0) (𝓝 (2 * (resolventVector b M ⬝ᵥ (N₂ *ᵥ resolventVector b M)))))
    have hgoal : potentialHessian b M N₁ N₂ =
        2 * (((slackMatrix b M)⁻¹ *ᵥ (N₁ *ᵥ resolventVector b M)) ⬝ᵥ
          (N₁ *ᵥ resolventVector b M)) +
        0 * (((slackMatrix b M)⁻¹ *ᵥ (N₁ *ᵥ resolventVector b M)) ⬝ᵥ
          (N₁ *ᵥ ((slackMatrix b M)⁻¹ *ᵥ (N₁ *ᵥ resolventVector b M)))) +
        2 * (resolventVector b M ⬝ᵥ (N₂ *ᵥ resolventVector b M)) := by
      unfold potentialHessian
      rw [dotProduct_comm (((slackMatrix b M)⁻¹ *ᵥ (N₁ *ᵥ resolventVector b M)))
        (N₁ *ᵥ resolventVector b M)]
      ring
    rw [hgoal]
    exact h2
  exact hlim

/-! ### Unconditional good subspace (B.4)

`spectral_subspace_exists` takes the spectral subspace `E₀` as a hypothesis.
`NonpositiveSubspace.exists_nonpositive_subspace_of_trace` now constructs it
unconditionally: applied to `Q` and the scaled diagonal `(1−ρ) • D` at
`θ = μ₅`, it produces a subspace of dimension at least `(1−μ₅)·s` on which
`hᵀ(Q − (1−ρ)D)h ≤ 0`, i.e. `hᵀQh ≤ (1−ρ)·hᵀDh`. -/

/-- **Unconditional `E₀` construction (B.4)**: if `Q` is positive
semidefinite, `D` is diagonal with nonnegative entries, `ρ ≤ 1`, and
`Q j j ≤ μ₅ · (1−ρ) · D j j` entrywise, where
`μ₅ = (1 + 4/25) · (1 + 1/10000) / (4 · (1 − 4/25) · (1 − 1/64))`,
then a subspace `E₀` of dimension at least `(1−μ₅)·s` exists on which
`hᵀQh ≤ (1−ρ)·hᵀDh`. -/
theorem good_subspace_exists {s : ℕ} (Q D : Input s s) (ρ : ℝ)
    (hQ : Q.PosSemidef) (hD : Matrix.IsDiag D)
    (hDdiag : ∀ j, 0 ≤ D j j) (hρ : ρ ≤ 1)
    (hQD : ∀ j, Q j j ≤
      ((1 + 4 / 25) * (1 + 1 / 10000) / (4 * (1 - 4 / 25) * (1 - 1 / 64))) *
        (1 - ρ) * D j j) :
    ∃ E0 : Submodule ℝ (Fin s → ℝ),
      (1 - (1 + 4 / 25) * (1 + 1 / 10000) /
          (4 * (1 - 4 / 25) * (1 - 1 / 64))) * (s : ℝ) ≤
        Module.finrank ℝ E0 ∧
      ∀ h ∈ E0, h ⬝ᵥ (Q *ᵥ h) ≤ (1 - ρ) * (h ⬝ᵥ (D *ᵥ h)) := by
  set μ₅ : ℝ := (1 + 4 / 25) * (1 + 1 / 10000) /
    (4 * (1 - 4 / 25) * (1 - 1 / 64)) with hμ₅def
  have hμ₅ : 0 ≤ μ₅ := by rw [hμ₅def]; positivity
  have h1ρ : (0 : ℝ) ≤ 1 - ρ := sub_nonneg.mpr hρ
  have hD' : Matrix.IsDiag ((1 - ρ) • D) := by
    intro i j hij
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [hD hij, mul_zero]
  have hD'diag : ∀ j, 0 ≤ ((1 - ρ) • D) j j := fun j => by
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg h1ρ (hDdiag j)
  have hQD' : ∀ j, Q j j ≤ μ₅ * ((1 - ρ) • D) j j := fun j => by
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← mul_assoc]
    exact hQD j
  obtain ⟨E0, hEdim, hEprop⟩ :=
    exists_nonpositive_subspace_of_trace Q ((1 - ρ) • D) hQ hμ₅ hD'diag hD' hQD'
  refine ⟨E0, ?_, ?_⟩
  · calc (1 - μ₅) * (s : ℝ) = (s : ℝ) - μ₅ * s := by ring
      _ ≤ Module.finrank ℝ E0 := hEdim
  · intro h hh
    have hz := hEprop h hh
    simp only [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul] at hz
    linarith [hz]

/-- **Unconditional (B.4) packaged**: combining `good_subspace_exists` with
`spectral_subspace_exists`, the intersection subspace `E` exists directly
from spectral hypotheses on `Q` and `D`, with no hypothesis on `E₀`. -/
theorem spectral_subspace_exists_unconditional {s : ℕ} {ι : Type*} [Fintype ι]
    (hs : 0 < s) (g : ι → Fin s → ℝ) (Q D : Input s s) (ρ : ℝ)
    (hQ : Q.PosSemidef) (hD : Matrix.IsDiag D) (hDdiag : ∀ j, 0 ≤ D j j)
    (hρ : ρ ≤ 1)
    (hQD : ∀ j, Q j j ≤
      ((1 + 4 / 25) * (1 + 1 / 10000) / (4 * (1 - 4 / 25) * (1 - 1 / 64))) *
        (1 - ρ) * D j j)
    (hcard : (Fintype.card ι : ℝ) ≤
      (1 / (291 / 200) ^ 2 + 5 * (65 / 64) ^ 4 / 238 +
        1 / (64 * (4 / 25 - 3 / 625)) + 1 / 2048) * s) :
    ∃ E : Submodule ℝ (Fin s → ℝ),
      (s : ℝ) / 32 < Module.finrank ℝ E ∧
      (∀ h ∈ E, h ⬝ᵥ (Q *ᵥ h) ≤ (1 - ρ) * (h ⬝ᵥ (D *ᵥ h))) ∧
      ∀ h ∈ E, ∀ i, g i ⬝ᵥ h = 0 := by
  obtain ⟨E0, hE0dim, hE0prop⟩ := good_subspace_exists Q D ρ hQ hD hDdiag hρ hQD
  exact spectral_subspace_exists hs E0 g Q D ρ hE0dim hcard hE0prop

end

end Komlos
