import Komlos

namespace Komlos

open scoped BigOperators

noncomputable def weight (u : ℝ) : ℝ :=
  119 / (1 - u / 20000) ^ 10000

theorem weight_pos {u : ℝ} (hu : u ≤ 0) : 0 < weight u := by
  apply div_pos (by norm_num)
  exact pow_pos (by linarith) _

theorem weight_mono {u v : ℝ} (huv : u ≤ v) (hv : v ≤ 0) : weight u ≤ weight v := by
  apply div_le_div_of_nonneg_left (by norm_num)
  · exact pow_pos (by linarith) _
  · exact pow_le_pow_left₀ (by linarith) (by linarith) _

theorem weight_le_119 {u : ℝ} (hu : u ≤ 0) : weight u ≤ 119 := by
  have h := weight_mono hu (show (0 : ℝ) ≤ 0 from le_rfl)
  simpa [weight] using h

theorem protected_weight_majorant {n : ℕ} (p b x y : Fin n → ℝ) (σ d r : ℝ)
    (hp : ∀ j, 0 ≤ p j) (hu : barrier σ d r (energy p x) ≤ 0)
    (hgradient : ∑ j, (σ * b j / r - 8 * p j / r ^ 2 * x j) * y j = 0) :
    weight (barrier σ (d + ∑ j, b j * y j) r (energy p (fun j => x j + y j))) ≤
      weight (barrier σ d r (energy p x)) :=
  weight_mono (protected_barrier_nonincrease p b x y σ d r hp hgradient) hu

def slackQuadratic {s : ℕ} (b : ℝ) (M : Input s s) (h : Fin s → ℝ) : ℝ :=
  ∑ j, (b * (h j) ^ 2 - h j * ∑ k, M j k * h k)

noncomputable def groundStatePenalty {s : ℕ} (M : Input s s) (v h : Fin s → ℝ) : ℝ :=
  (1 / 2) * ∑ j, ∑ k, M j k * v j * v k * (h j / v j - h k / v k) ^ 2

theorem ground_state_identity_with_rhs {s : ℕ} (b : ℝ) (M : Input s s) (v h f : Fin s → ℝ)
    (hM : ∀ j k, M j k = M k j) (hv : ∀ j, 0 < v j)
    (hres : ∀ j, b * v j = f j + ∑ k, M j k * v k) :
    slackQuadratic b M h = (∑ j, f j * (h j) ^ 2 / v j) + groundStatePenalty M v h := by
  have hentry (j k : Fin s) :
      M j k * v j * v k * (h j / v j - h k / v k) ^ 2 =
        M j k * (v k / v j) * (h j) ^ 2 +
          M j k * (v j / v k) * (h k) ^ 2 - 2 * M j k * h j * h k := by
    field_simp [(hv j).ne', (hv k).ne']
    ring
  have hswap :
      (∑ j, ∑ k, M j k * (v j / v k) * (h k) ^ 2) =
        ∑ j, ∑ k, M j k * (v k / v j) * (h j) ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hM k j]
  have hinner (j : Fin s) :
      (∑ k, M j k * (v k / v j) * (h j) ^ 2) =
        b * (h j) ^ 2 - f j * (h j) ^ 2 / v j := by
    calc
      (∑ k, M j k * (v k / v j) * (h j) ^ 2) =
          ((∑ k, M j k * v k) / v j) * (h j) ^ 2 := by
        rw [Finset.sum_div, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = b * (h j) ^ 2 - f j * (h j) ^ 2 / v j := by
        rw [show (∑ k, M j k * v k) = b * v j - f j by linarith [hres j]]
        field_simp [(hv j).ne']
  have hcross : (∑ j, ∑ k, 2 * M j k * h j * h k) =
      2 * ∑ j, h j * ∑ k, M j k * h k := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hpenalty : groundStatePenalty M v h =
      (∑ j, b * (h j) ^ 2) - (∑ j, f j * (h j) ^ 2 / v j) -
        ∑ j, h j * ∑ k, M j k * h k := by
    unfold groundStatePenalty
    simp_rw [hentry, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hswap, hcross]
    simp_rw [hinner, Finset.sum_sub_distrib]
    ring
  rw [hpenalty]
  unfold slackQuadratic
  rw [Finset.sum_sub_distrib]
  ring

theorem ground_state_identity {s : ℕ} (b : ℝ) (M : Input s s) (v h : Fin s → ℝ)
    (hM : ∀ j k, M j k = M k j) (hv : ∀ j, 0 < v j)
    (hres : ∀ j, b * v j = 1 + ∑ k, M j k * v k) :
    slackQuadratic b M h = (∑ j, (h j) ^ 2 / v j) + groundStatePenalty M v h := by
  simpa using ground_state_identity_with_rhs b M v h (fun _ => 1) hM hv hres

theorem ground_state_penalty_nonneg {s : ℕ} (M : Input s s) (v h : Fin s → ℝ)
    (hM : ∀ j k, 0 ≤ M j k) (hv : ∀ j, 0 ≤ v j) : 0 ≤ groundStatePenalty M v h := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (mul_nonneg (mul_nonneg (hM j k) (hv j)) (hv k)) (sq_nonneg _)

theorem ground_state_lower_bound {s : ℕ} (b : ℝ) (M : Input s s) (v h : Fin s → ℝ)
    (hMsymm : ∀ j k, M j k = M k j) (hMnonneg : ∀ j k, 0 ≤ M j k)
    (hv : ∀ j, 0 < v j) (hres : ∀ j, b * v j = 1 + ∑ k, M j k * v k) :
    (∑ j, (h j) ^ 2 / v j) ≤ slackQuadratic b M h := by
  rw [ground_state_identity b M v h hMsymm hv hres]
  exact le_add_of_nonneg_right (ground_state_penalty_nonneg M v h hMnonneg (fun j => (hv j).le))

theorem ground_state_strict_positive {s : ℕ} (b : ℝ) (M : Input s s) (v h : Fin s → ℝ)
    (hMsymm : ∀ j k, M j k = M k j) (hMnonneg : ∀ j k, 0 ≤ M j k)
    (hv : ∀ j, 0 < v j) (hres : ∀ j, b * v j = 1 + ∑ k, M j k * v k)
    (hh : ∃ j, h j ≠ 0) : 0 < slackQuadratic b M h := by
  have hdiag : 0 < ∑ j, (h j) ^ 2 / v j := by
    apply Finset.sum_pos'
    · intro j _
      exact div_nonneg (sq_nonneg _) (hv j).le
    · obtain ⟨j, hj⟩ := hh
      exact ⟨j, Finset.mem_univ j, div_pos (sq_pos_of_ne_zero hj) (hv j)⟩
  exact hdiag.trans_le (ground_state_lower_bound b M v h hMsymm hMnonneg hv hres)

theorem weighted_rank_one_domination {s : ℕ} (z v h : Fin s → ℝ)
    (hz : ∀ j, 0 ≤ z j) (hv : ∀ j, 0 < v j) :
    (∑ j, z j * h j) ^ 2 ≤ (∑ j, z j * v j) * ∑ j, z j / v j * (h j) ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun j _ => mul_nonneg (hz j) (hv j).le)
    (fun j _ => mul_nonneg (div_nonneg (hz j) (hv j).le) (sq_nonneg (h j)))
  intro j _
  apply le_of_eq
  field_simp [(hv j).ne']

theorem weighted_gram_diagonal_domination {m s : ℕ} (z : Input m s)
    (w : Fin m → ℝ) (v h : Fin s → ℝ)
    (hz : ∀ i j, 0 ≤ z i j) (hw : ∀ i, 0 ≤ w i) (hv : ∀ j, 0 < v j) :
    (∑ i, w i * (∑ j, z i j * h j) ^ 2) ≤
      ∑ j, ((∑ i, w i * (∑ k, z i k * v k) * z i j) / v j) * (h j) ^ 2 := by
  calc
    (∑ i, w i * (∑ j, z i j * h j) ^ 2) ≤
        ∑ i, w i * ((∑ j, z i j * v j) * ∑ j, z i j / v j * (h j) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (weighted_rank_one_domination (z i) v h (hz i) hv) (hw i)
    _ = ∑ i, ∑ j, w i * (∑ k, z i k * v k) * (z i j / v j * (h j) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_assoc, Finset.mul_sum]
    _ = ∑ j, ∑ i, w i * (∑ k, z i k * v k) * (z i j / v j * (h j) ^ 2) :=
      Finset.sum_comm
    _ = ∑ j, ((∑ i, w i * (∑ k, z i k * v k) * z i j) / v j) * (h j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem weighted_gram_load_domination {m s : ℕ} (z : Input m s)
    (w : Fin m → ℝ) (v h : Fin s → ℝ) (κ : ℝ)
    (hz : ∀ i j, 0 ≤ z i j) (hw : ∀ i, 0 ≤ w i) (hv : ∀ j, 0 < v j)
    (hload : ∀ j, (∑ i, w i * (∑ k, z i k * v k) * z i j) ≤ κ) :
    (∑ i, w i * (∑ j, z i j * h j) ^ 2) ≤ κ * ∑ j, (h j) ^ 2 / v j := by
  calc
    (∑ i, w i * (∑ j, z i j * h j) ^ 2) ≤
        ∑ j, ((∑ i, w i * (∑ k, z i k * v k) * z i j) / v j) * (h j) ^ 2 :=
      weighted_gram_diagonal_domination z w v h hz hw hv
    _ ≤ ∑ j, (κ / v j) * (h j) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hload j) (hv j).le) (sq_nonneg (h j))
    _ = κ * ∑ j, (h j) ^ 2 / v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem weighted_gram_slack_domination {m s : ℕ} (b κ : ℝ) (M : Input s s)
    (z : Input m s) (w : Fin m → ℝ) (v h : Fin s → ℝ)
    (hMsymm : ∀ j k, M j k = M k j) (hMnonneg : ∀ j k, 0 ≤ M j k)
    (hv : ∀ j, 0 < v j) (hres : ∀ j, b * v j = 1 + ∑ k, M j k * v k)
    (hz : ∀ i j, 0 ≤ z i j) (hw : ∀ i, 0 ≤ w i) (hκ : 0 ≤ κ)
    (hload : ∀ j, (∑ i, w i * (∑ k, z i k * v k) * z i j) ≤ κ) :
    (∑ i, w i * (∑ j, z i j * h j) ^ 2) ≤ κ * slackQuadratic b M h :=
  (weighted_gram_load_domination z w v h κ hz hw hv hload).trans
    (mul_le_mul_of_nonneg_left (ground_state_lower_bound b M v h hMsymm hMnonneg hv hres) hκ)

end Komlos
