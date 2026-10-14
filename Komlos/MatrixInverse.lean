import Komlos.Resolvent
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace Komlos

open scoped BigOperators
open Matrix

def slackMatrix {s : ℕ} (b : ℝ) (M : Input s s) : Input s s :=
  Matrix.diagonal (fun _ => b) - M

theorem slackMatrix_mulVec {s : ℕ} (b : ℝ) (M : Input s s) (x : Fin s → ℝ) :
    slackMatrix b M *ᵥ x = fun j => b * x j - ∑ k, M j k * x k := by
  unfold slackMatrix
  rw [Matrix.sub_mulVec, Matrix.diagonal_const_mulVec]
  rfl

theorem slackQuadratic_eq_dotProduct {s : ℕ} (b : ℝ) (M : Input s s) (x : Fin s → ℝ) :
    slackQuadratic b M x = x ⬝ᵥ (slackMatrix b M *ᵥ x) := by
  rw [slackMatrix_mulVec]
  unfold slackQuadratic dotProduct
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem posDef_slackQuadratic_pos {s : ℕ} {b : ℝ} {M : Input s s}
    (hpos : (slackMatrix b M).PosDef) {x : Fin s → ℝ} (hx : x ≠ 0) :
    0 < slackQuadratic b M x := by
  rw [slackQuadratic_eq_dotProduct]
  simpa using hpos.dotProduct_mulVec_pos hx

theorem slack_solution_nonneg {s : ℕ} {b : ℝ} {M : Input s s}
    (hM : ∀ j k, 0 ≤ M j k) (hpos : (slackMatrix b M).PosDef)
    (x : Fin s → ℝ) (hf : ∀ j, 0 ≤ b * x j - ∑ k, M j k * x k) : ∀ j, 0 ≤ x j := by
  classical
  let y : Fin s → ℝ := fun j => min (x j) 0
  have hy0 (j) : y j ≤ 0 := min_le_right _ _
  have hyx (j) : y j ≤ x j := min_le_left _ _
  have hprod (j) : y j * x j = (y j) ^ 2 := by
    by_cases hx : x j ≤ 0
    · simp [y, min_eq_left hx, pow_two]
    · simp [y, min_eq_right (le_of_not_ge hx)]
  have hquad : slackQuadratic b M y ≤ 0 := by
    calc
      slackQuadratic b M y ≤ ∑ j, y j * (b * x j - ∑ k, M j k * x k) := by
        apply Finset.sum_le_sum
        intro j _
        have hsum : (∑ k, M j k * y k) ≤ ∑ k, M j k * x k :=
          Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hyx k) (hM j k))
        have hmul := mul_le_mul_of_nonpos_left hsum (hy0 j)
        have he := congrArg (fun z : ℝ => b * z) (hprod j)
        nlinarith only [he, hmul]
      _ ≤ 0 := Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonpos_of_nonneg (hy0 j) (hf j))
  have hyzero : y = 0 := by
    by_contra hne
    have hp := posDef_slackQuadratic_pos hpos hne
    linarith
  intro j
  have hj : min (x j) 0 = 0 := congrFun hyzero j
  exact min_eq_right_iff.mp hj

theorem slack_inverse_mulVec_eq {s : ℕ} {b : ℝ} {M : Input s s}
    (hpos : (slackMatrix b M).PosDef) (f : Fin s → ℝ) :
    slackMatrix b M *ᵥ ((slackMatrix b M)⁻¹ *ᵥ f) = f := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hpos.isUnit), Matrix.one_mulVec]

theorem slack_inverse_mulVec_nonneg {s : ℕ} {b : ℝ} {M : Input s s}
    (hM : ∀ j k, 0 ≤ M j k) (hpos : (slackMatrix b M).PosDef)
    (f : Fin s → ℝ) (hf : ∀ j, 0 ≤ f j) : ∀ j, 0 ≤ ((slackMatrix b M)⁻¹ *ᵥ f) j := by
  apply slack_solution_nonneg hM hpos
  intro j
  have he := congrFun (slack_inverse_mulVec_eq hpos f) j
  rw [slackMatrix_mulVec] at he
  rw [show b * ((slackMatrix b M)⁻¹ *ᵥ f) j -
    ∑ k, M j k * ((slackMatrix b M)⁻¹ *ᵥ f) k = f j from he]
  exact hf j

theorem slack_inverse_entrywise_nonneg {s : ℕ} {b : ℝ} {M : Input s s}
    (hM : ∀ j k, 0 ≤ M j k) (hpos : (slackMatrix b M).PosDef) (i j : Fin s) :
    0 ≤ (slackMatrix b M)⁻¹ i j := by
  have hf : ∀ k : Fin s, 0 ≤ (if k = j then (1 : ℝ) else 0) := by
    intro k
    split_ifs <;> norm_num
  have h := slack_inverse_mulVec_nonneg hM hpos (fun k => if k = j then 1 else 0) hf i
  simpa [Matrix.mulVec, dotProduct, mul_ite] using h

noncomputable def resolventVector {s : ℕ} (b : ℝ) (M : Input s s) : Fin s → ℝ :=
  (slackMatrix b M)⁻¹ *ᵥ (fun _ => 1)

noncomputable def resolventPotential {s : ℕ} (b : ℝ) (M : Input s s) : ℝ :=
  (∑ j, resolventVector b M j) - s / b

theorem resolvent_equation {s : ℕ} {b : ℝ} {M : Input s s}
    (hpos : (slackMatrix b M).PosDef) (j : Fin s) :
    b * resolventVector b M j = 1 + ∑ k, M j k * resolventVector b M k := by
  have he := congrFun (slack_inverse_mulVec_eq hpos (fun _ => 1)) j
  rw [slackMatrix_mulVec] at he
  change b * resolventVector b M j - ∑ k, M j k * resolventVector b M k = 1 at he
  linarith

theorem resolventVector_nonneg {s : ℕ} {b : ℝ} {M : Input s s}
    (hM : ∀ j k, 0 ≤ M j k) (hpos : (slackMatrix b M).PosDef) (j : Fin s) :
    0 ≤ resolventVector b M j :=
  slack_inverse_mulVec_nonneg hM hpos (fun _ => 1) (fun _ => zero_le_one) j

theorem resolventVector_lower_bound {s : ℕ} {b : ℝ} {M : Input s s}
    (hb : 0 < b) (hM : ∀ j k, 0 ≤ M j k) (hpos : (slackMatrix b M).PosDef) (j : Fin s) :
    1 / b ≤ resolventVector b M j := by
  apply (div_le_iff₀ hb).mpr
  have hs : 0 ≤ ∑ k, M j k * resolventVector b M k :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hM j k) (resolventVector_nonneg hM hpos k))
  nlinarith [resolvent_equation hpos j]

theorem resolventVector_pos {s : ℕ} {b : ℝ} {M : Input s s}
    (hb : 0 < b) (hM : ∀ j k, 0 ≤ M j k) (hpos : (slackMatrix b M).PosDef) (j : Fin s) :
    0 < resolventVector b M j :=
  (div_pos zero_lt_one hb).trans_le (resolventVector_lower_bound hb hM hpos j)

theorem resolventPotential_nonneg {s : ℕ} {b : ℝ} {M : Input s s}
    (hb : 0 < b) (hM : ∀ j k, 0 ≤ M j k) (hpos : (slackMatrix b M).PosDef) :
    0 ≤ resolventPotential b M := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => resolventVector_lower_bound hb hM hpos j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  unfold resolventPotential
  exact sub_nonneg.mpr (by simpa [div_eq_mul_inv] using hs)

theorem resolvent_ground_state_lower_bound {s : ℕ} {b : ℝ} {M : Input s s}
    (hb : 0 < b) (hMsymm : ∀ j k, M j k = M k j) (hM : ∀ j k, 0 ≤ M j k)
    (hpos : (slackMatrix b M).PosDef) (h : Fin s → ℝ) :
    (∑ j, (h j) ^ 2 / resolventVector b M j) ≤ slackQuadratic b M h :=
  ground_state_lower_bound b M (resolventVector b M) h hMsymm hM
    (resolventVector_pos hb hM hpos) (resolvent_equation hpos)

theorem slack_solution_comparison {s : ℕ} {b : ℝ} {M : Input s s}
    (hM : ∀ j k, 0 ≤ M j k) (hpos : (slackMatrix b M).PosDef)
    (x y : Fin s → ℝ)
    (hxy : ∀ j, b * x j - (∑ k, M j k * x k) ≤ b * y j - ∑ k, M j k * y k) :
    ∀ j, x j ≤ y j := by
  have hnonneg : ∀ j, 0 ≤ b * (y j - x j) - ∑ k, M j k * (y k - x k) := by
    intro j
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    linarith [hxy j]
  have h := slack_solution_nonneg hM hpos (fun j => y j - x j) hnonneg
  intro j
  exact sub_nonneg.mp (h j)

theorem resolventVector_entrywise_mono {s : ℕ} {b : ℝ} {M N : Input s s}
    (hM : ∀ j k, 0 ≤ M j k) (hN : ∀ j k, 0 ≤ N j k)
    (hMpos : (slackMatrix b M).PosDef) (hNpos : (slackMatrix b N).PosDef)
    (hMN : ∀ j k, M j k ≤ N j k) (j : Fin s) :
    resolventVector b M j ≤ resolventVector b N j := by
  apply slack_solution_comparison hM hMpos (resolventVector b M) (resolventVector b N) _ j
  intro i
  have hsum : (∑ k, M i k * resolventVector b N k) ≤
      ∑ k, N i k * resolventVector b N k :=
    Finset.sum_le_sum (fun k _ =>
      mul_le_mul_of_nonneg_right (hMN i k) (resolventVector_nonneg hN hNpos k))
  linarith [resolvent_equation hMpos i, resolvent_equation hNpos i]

theorem resolventPotential_entrywise_mono {s : ℕ} {b : ℝ} {M N : Input s s}
    (hM : ∀ j k, 0 ≤ M j k) (hN : ∀ j k, 0 ≤ N j k)
    (hMpos : (slackMatrix b M).PosDef) (hNpos : (slackMatrix b N).PosDef)
    (hMN : ∀ j k, M j k ≤ N j k) : resolventPotential b M ≤ resolventPotential b N := by
  exact sub_le_sub_right
    (Finset.sum_le_sum (fun j _ => resolventVector_entrywise_mono hM hN hMpos hNpos hMN j)) _

theorem resolvent_inverse_difference {s : ℕ} {b : ℝ} {M N : Input s s}
    (hMpos : (slackMatrix b M).PosDef) (hNpos : (slackMatrix b N).PosDef) :
    (slackMatrix b N)⁻¹ - (slackMatrix b M)⁻¹ =
      (slackMatrix b N)⁻¹ * (N - M) * (slackMatrix b M)⁻¹ := by
  have he : slackMatrix b M - slackMatrix b N = N - M := by
    unfold slackMatrix
    abel
  rw [Matrix.inv_sub_inv ⟨fun _ => hMpos.isUnit, fun _ => hNpos.isUnit⟩, he]

theorem resolventVector_comparison_with_guard {s : ℕ} {b : ℝ} {M : Input s s}
    (hM : ∀ j k, 0 ≤ M j k) (hpos : (slackMatrix b M).PosDef)
    (vhat : Fin s → ℝ) (hguard : ∀ j, 1 / 2 ≤ b * vhat j - ∑ k, M j k * vhat k)
    (j : Fin s) : resolventVector b M j ≤ 2 * vhat j := by
  have hcomp : ∀ j, resolventVector b M j / 2 ≤ vhat j := by
    apply slack_solution_comparison hM hpos
    intro i
    have he := resolvent_equation hpos i
    have hsum : (∑ k, M i k * (resolventVector b M k / 2)) =
        (∑ k, M i k * resolventVector b M k) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hsum]
    linarith [hguard i]
  linarith [hcomp j]

theorem sum_along_embedding_le {t s : ℕ} (e : Fin t ↪ Fin s) (f : Fin s → ℝ)
    (hf : ∀ j, 0 ≤ f j) : (∑ j, f (e j)) ≤ ∑ j, f j := by
  classical
  calc
    (∑ j, f (e j)) = ∑ i ∈ Finset.univ.image e, f i := by
      rw [Finset.sum_image (fun _ _ _ _ he => e.injective he)]
    _ ≤ ∑ j, f j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => hf j)

theorem slackMatrix_submatrix {t s : ℕ} (e : Fin t ↪ Fin s) (b : ℝ) (M : Input s s) :
    slackMatrix b (M.submatrix e e) = (slackMatrix b M).submatrix e e := by
  simp [slackMatrix, Matrix.submatrix_sub, Matrix.submatrix_diagonal_embedding, Function.comp_def]

theorem slackMatrix_principal_posDef {t s : ℕ} (e : Fin t ↪ Fin s)
    {b : ℝ} {M : Input s s} (hpos : (slackMatrix b M).PosDef) :
    (slackMatrix b (M.submatrix e e)).PosDef := by
  rw [slackMatrix_submatrix]
  exact hpos.submatrix e.injective

theorem resolventVector_principal_le {t s : ℕ} (e : Fin t ↪ Fin s)
    {b : ℝ} {M : Input s s} (hM : ∀ j k, 0 ≤ M j k) (hpos : (slackMatrix b M).PosDef)
    (j : Fin t) : resolventVector b (M.submatrix e e) j ≤ resolventVector b M (e j) := by
  have hsub := slackMatrix_principal_posDef e hpos
  apply slack_solution_comparison (fun i k => hM (e i) (e k)) hsub
    (resolventVector b (M.submatrix e e)) (fun i => resolventVector b M (e i)) _ j
  intro i
  have hsum := sum_along_embedding_le e (fun k => M (e i) k * resolventVector b M k)
    (fun k => mul_nonneg (hM (e i) k) (resolventVector_nonneg hM hpos k))
  have he := resolvent_equation hsub i
  have hefull := resolvent_equation hpos (e i)
  change b * resolventVector b (M.submatrix e e) i -
      (∑ k, M (e i) (e k) * resolventVector b (M.submatrix e e) k) ≤
        b * resolventVector b M (e i) - ∑ k, M (e i) (e k) * resolventVector b M (e k)
  simp only [Matrix.submatrix_apply] at he
  linarith

theorem resolventPotential_eq_sum_excess {s : ℕ} (b : ℝ) (M : Input s s) :
    resolventPotential b M = ∑ j, (resolventVector b M j - 1 / b) := by
  unfold resolventPotential
  rw [Finset.sum_sub_distrib]
  simp [div_eq_mul_inv]

theorem resolventPotential_principal_le {t s : ℕ} (e : Fin t ↪ Fin s)
    {b : ℝ} {M : Input s s} (hb : 0 < b) (hM : ∀ j k, 0 ≤ M j k)
    (hpos : (slackMatrix b M).PosDef) :
    resolventPotential b (M.submatrix e e) ≤ resolventPotential b M := by
  rw [resolventPotential_eq_sum_excess, resolventPotential_eq_sum_excess]
  calc
    (∑ j, (resolventVector b (M.submatrix e e) j - 1 / b)) ≤
        ∑ j, (resolventVector b M (e j) - 1 / b) :=
      Finset.sum_le_sum (fun j _ => sub_le_sub_right (resolventVector_principal_le e hM hpos j) _)
    _ ≤ ∑ j, (resolventVector b M j - 1 / b) :=
      sum_along_embedding_le e _ (fun j => sub_nonneg.mpr (resolventVector_lower_bound hb hM hpos j))

theorem resolvent_excess_equation {s : ℕ} {b : ℝ} {M : Input s s}
    (hb : 0 < b) (hpos : (slackMatrix b M).PosDef) (j : Fin s) :
    b * (resolventVector b M j - 1 / b) -
      (∑ k, M j k * (resolventVector b M k - 1 / b)) = (∑ k, M j k) / b := by
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  have hs : (∑ k, M j k * (1 / b)) = (∑ k, M j k) / b := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hs, mul_one_div_cancel hb.ne']
  linarith [resolvent_equation hpos j]

theorem resolventPotential_barrier_antitone {s : ℕ} {b c : ℝ} {M : Input s s}
    (hb : 0 < b) (hbc : b ≤ c) (hM : ∀ j k, 0 ≤ M j k)
    (hbpos : (slackMatrix b M).PosDef) (hcpos : (slackMatrix c M).PosDef) :
    resolventPotential c M ≤ resolventPotential b M := by
  have hc : 0 < c := hb.trans_le hbc
  have hcomp : ∀ j, resolventVector c M j - 1 / c ≤ resolventVector b M j - 1 / b := by
    apply slack_solution_comparison hM hcpos
    intro j
    have hsum : 0 ≤ ∑ k, M j k := Finset.sum_nonneg (fun k _ => hM j k)
    have hdiv := div_le_div_of_nonneg_left hsum hb hbc
    have hexcess := resolventVector_lower_bound hb hM hbpos j
    have hmul := mul_nonneg (sub_nonneg.mpr hbc) (sub_nonneg.mpr hexcess)
    have heb := resolvent_excess_equation hb hbpos j
    have hec := resolvent_excess_equation hc hcpos j
    nlinarith only [hdiv, hmul, heb, hec]
  rw [resolventPotential_eq_sum_excess, resolventPotential_eq_sum_excess]
  exact Finset.sum_le_sum (fun j _ => hcomp j)

theorem slackMatrix_isHermitian {s : ℕ} (b : ℝ) (M : Input s s)
    (hM : ∀ j k, M j k = M k j) : (slackMatrix b M).IsHermitian := by
  have hm : M.IsHermitian := Matrix.IsHermitian.ext (fun i j => by simpa using hM j i)
  have hd : (Matrix.diagonal (fun _ : Fin s => b)).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [Matrix.diagonal, eq_comm]
  exact hd.sub hm

theorem slack_posDef_of_positive_supersolution {s : ℕ} (b : ℝ) (M : Input s s)
    (hMsymm : ∀ j k, M j k = M k j) (hM : ∀ j k, 0 ≤ M j k)
    (v : Fin s → ℝ) (hv : ∀ j, 0 < v j)
    (hpositive : ∀ j, 0 < b * v j - ∑ k, M j k * v k) : (slackMatrix b M).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (slackMatrix_isHermitian b M hMsymm)
  intro x hx
  let f : Fin s → ℝ := fun j => b * v j - ∑ k, M j k * v k
  have hf (j) : 0 < f j := hpositive j
  have hres (j) : b * v j = f j + ∑ k, M j k * v k := by dsimp [f]; ring
  have hxj : ∃ j, x j ≠ 0 := by
    by_contra hn
    apply hx
    ext j
    by_contra hj
    exact hn ⟨j, hj⟩
  have hdiag : 0 < ∑ j, f j * (x j) ^ 2 / v j := by
    apply Finset.sum_pos'
    · intro j _
      exact div_nonneg (mul_nonneg (hf j).le (sq_nonneg _)) (hv j).le
    · obtain ⟨j, hj⟩ := hxj
      exact ⟨j, Finset.mem_univ j, div_pos (mul_pos (hf j) (sq_pos_of_ne_zero hj)) (hv j)⟩
  have hp : 0 < slackQuadratic b M x := by
    rw [ground_state_identity_with_rhs b M v x f hMsymm hv hres]
    exact add_pos_of_pos_of_nonneg hdiag
      (ground_state_penalty_nonneg M v x hM (fun j => (hv j).le))
  simpa [slackQuadratic_eq_dotProduct] using hp

theorem anchor_guard_sound {s : ℕ} (b cap : ℝ) (M : Input s s)
    (hMsymm : ∀ j k, M j k = M k j) (hM : ∀ j k, 0 ≤ M j k)
    (vhat : Fin s → ℝ) (hvhat : ∀ j, 0 < vhat j)
    (hguard : ∀ j, 1 / 2 ≤ b * vhat j - ∑ k, M j k * vhat k)
    (hcap : (∑ j, vhat j) ≤ cap / 2) :
    (slackMatrix b M).PosDef ∧ (∑ j, resolventVector b M j) ≤ cap := by
  have hpos := slack_posDef_of_positive_supersolution b M hMsymm hM vhat hvhat
    (fun j => lt_of_lt_of_le (by norm_num) (hguard j))
  refine ⟨hpos, ?_⟩
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => resolventVector_comparison_with_guard hM hpos vhat hguard j)
  rw [← Finset.mul_sum] at hs
  linarith

theorem resolvent_vector_difference {s : ℕ} {b : ℝ} {M N : Input s s}
    (hMpos : (slackMatrix b M).PosDef) (hNpos : (slackMatrix b N).PosDef) :
    resolventVector b N - resolventVector b M =
      (slackMatrix b N)⁻¹ *ᵥ ((N - M) *ᵥ resolventVector b M) := by
  simp only [resolventVector, ← Matrix.sub_mulVec, resolvent_inverse_difference hMpos hNpos,
    ← Matrix.mulVec_mulVec]

theorem resolvent_vector_relative_change {s : ℕ} {b ε : ℝ} {M N : Input s s}
    (hN : ∀ j k, 0 ≤ N j k)
    (hMpos : (slackMatrix b M).PosDef) (hNpos : (slackMatrix b N).PosDef)
    (herr : ∀ j, |((N - M) *ᵥ resolventVector b M) j| ≤ ε) (j : Fin s) :
    |resolventVector b N j - resolventVector b M j| ≤ ε * resolventVector b N j := by
  have he := congrFun (resolvent_vector_difference hMpos hNpos) j
  change resolventVector b N j - resolventVector b M j =
    ∑ k, (slackMatrix b N)⁻¹ j k * ((N - M) *ᵥ resolventVector b M) k at he
  rw [he]
  calc
    |∑ k, (slackMatrix b N)⁻¹ j k * ((N - M) *ᵥ resolventVector b M) k| ≤
        ∑ k, |(slackMatrix b N)⁻¹ j k * ((N - M) *ᵥ resolventVector b M) k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, (slackMatrix b N)⁻¹ j k * ε := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, abs_of_nonneg (slack_inverse_entrywise_nonneg hN hNpos j k)]
      exact mul_le_mul_of_nonneg_left (herr k) (slack_inverse_entrywise_nonneg hN hNpos j k)
    _ = ε * resolventVector b N j := by
      simp only [resolventVector, Matrix.mulVec, dotProduct, mul_one]
      rw [← Finset.sum_mul]
      ring

theorem resolvent_vector_relative_bounds {s : ℕ} {b ε : ℝ} {M N : Input s s}
    (hN : ∀ j k, 0 ≤ N j k)
    (hMpos : (slackMatrix b M).PosDef) (hNpos : (slackMatrix b N).PosDef)
    (herr : ∀ j, |((N - M) *ᵥ resolventVector b M) j| ≤ ε)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (j : Fin s) :
    resolventVector b M j / (1 + ε) ≤ resolventVector b N j ∧
      resolventVector b N j ≤ resolventVector b M j / (1 - ε) := by
  have h := abs_le.mp (resolvent_vector_relative_change hN hMpos hNpos herr j)
  constructor
  · apply (div_le_iff₀ (by linarith : 0 < 1 + ε)).mpr
    nlinarith [h.1]
  · apply (le_div_iff₀ (by linarith : 0 < 1 - ε)).mpr
    nlinarith [h.2]

end Komlos
