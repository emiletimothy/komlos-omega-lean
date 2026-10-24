import Komlos.GaussianCompletion
import Komlos.MatrixInverse

/-!
# Epoch barrier bookkeeping (Appendix C)

Appendix C bounds the resolvent potential at the start of every epoch.
The barrier schedule is `b_j = 1 + ∑_{k=1}^{j} (4k²)⁻¹`, so
`b_{j+1} − b_j = (4(j+1)²)⁻¹` and `b_j ≤ 1 + π²/24 < 3/2` (proved here by
the elementary telescope `1/k² ≤ 1/(k(k−1))`, giving `∑ ≤ 1/2 − 1/(4j)` —
no `π` needed).

At the start of epoch `j+1` the previous epoch's slack is still positive
semidefinite at `b_j`, so the new slack `b_{j+1}I − M` satisfies the
quadratic-form lower bound `QFLower (b_{j+1}−b_j)`, and `qfLower_inv_le`
inverts it to the resolvent bound

    xᵀR_{b_{j+1}}x ≤ 4(j+1)²·‖x‖².

Applied to the all-ones vector this is the paper's epoch-start estimate
`F_{b_{j+1}}(M) = 1ᵀR1 − s/b_{j+1} ≤ 4(j+1)²·s` (the paper writes `4Nj²`
with ambient dimension `N`).  The initial-anchor bound
`F₁(M) ≤ s·bdep/(1−bdep)` from `M ⪯ bdep·I` is the same argument at
`c = 1 − bdep`.
-/

namespace Komlos

open Matrix
open scoped BigOperators

/-- `slackQuadratic b M x = b·‖x‖² − xᵀMx` at the quadratic-form level. -/
theorem slackQuadratic_eq_norm_sub {s : ℕ} {b : ℝ} {M : Input s s}
    (x : Fin s → ℝ) :
    slackQuadratic b M x = b * (x ⬝ᵥ x) - x ⬝ᵥ (M *ᵥ x) := by
  rw [slackQuadratic_eq_dotProduct]
  unfold slackMatrix
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.diagonal_const_mulVec,
    dotProduct_smul, smul_eq_mul]

/-- Adding `c` to the barrier adds `c·‖h‖²` to the slack quadratic form. -/
theorem slackQuadratic_add_barrier {s : ℕ} {b c : ℝ} {M : Input s s}
    (h : Fin s → ℝ) :
    slackQuadratic (b + c) M h =
      slackQuadratic b M h + c * (h ⬝ᵥ h) := by
  rw [slackQuadratic_eq_norm_sub, slackQuadratic_eq_norm_sub]
  ring

/-- **Epoch QF lower bound.** If the previous slack `bI − M` is
quadratic-form nonnegative, the new slack `(b+c)I − M` satisfies
`QFLower c` — the `(b_jI − M)⁻¹ ⪯ (b_j − b_{j-1})⁻¹I` step of App. C. -/
theorem qfLower_of_slack_psd_add {s : ℕ} {b c : ℝ} {M : Input s s}
    (hpsd : ∀ x : Fin s → ℝ, 0 ≤ slackQuadratic b M x)
    (x : Fin s → ℝ) :
    c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (slackMatrix (b + c) M *ᵥ x) := by
  rw [← slackQuadratic_eq_dotProduct (b + c) M x,
    slackQuadratic_add_barrier]
  linarith [hpsd x]

/-- **Epoch resolvent bound.** Inverting the epoch QF bound:
`xᵀ(b+c−M)⁻¹x ≤ c⁻¹·‖x‖²`.  With `c = (4(j+1)²)⁻¹` this is
`xᵀRx ≤ 4(j+1)²·‖x‖²`. -/
theorem resolvent_qf_le_of_slack_psd_add {s : ℕ} {b c : ℝ} {M : Input s s}
    (hpos : (slackMatrix (b + c) M).PosDef)
    (hpsd : ∀ x : Fin s → ℝ, 0 ≤ slackQuadratic b M x)
    (hc : 0 < c) (x : Fin s → ℝ) :
    x ⬝ᵥ ((slackMatrix (b + c) M)⁻¹ *ᵥ x) ≤ c⁻¹ * (x ⬝ᵥ x) :=
  qfLower_inv_le hpos (qfLower_of_slack_psd_add hpsd) hc x

/-- `⟨1, y⟩ = ∑ yⱼ` for the all-ones vector. -/
theorem dotProduct_ones_left {s : ℕ} (y : Fin s → ℝ) :
    (fun _ : Fin s => (1 : ℝ)) ⬝ᵥ y = ∑ j : Fin s, y j := by
  simp [dotProduct]

/-- The all-ones vector has `⟨1,1⟩ = s`. -/
theorem dotProduct_ones {s : ℕ} :
    (fun _ : Fin s => (1 : ℝ)) ⬝ᵥ (fun _ : Fin s => (1 : ℝ)) =
      (s : ℝ) := by
  simp [dotProduct]

/-- **Epoch-start potential bound (App. C).** If the previous slack at
barrier `b` is quadratic-form nonnegative, then at barrier `b + c` the
resolvent potential satisfies `F = 1ᵀR1 − s/(b+c) ≤ c⁻¹·s`.  At
`c = (4(j+1)²)⁻¹` this is the paper's `F_{b_j}(M) ≤ 4j²·N`. -/
theorem resolventPotential_le_of_slack_psd_add {s : ℕ} {b c : ℝ}
    {M : Input s s}
    (hpos : (slackMatrix (b + c) M).PosDef)
    (hpsd : ∀ x : Fin s → ℝ, 0 ≤ slackQuadratic b M x)
    (hc : 0 < c) (hbc : 0 < b + c) :
    resolventPotential (b + c) M ≤ c⁻¹ * s := by
  have h1 := resolvent_qf_le_of_slack_psd_add hpos hpsd hc
    (fun _ => (1 : ℝ))
  rw [dotProduct_ones] at h1
  have hsum : ∑ j, resolventVector (b + c) M j ≤ c⁻¹ * (s : ℝ) := by
    rw [show (∑ j, resolventVector (b + c) M j) =
        (fun _ => (1 : ℝ)) ⬝ᵥ (resolventVector (b + c) M) from
      (dotProduct_ones_left _).symm]
    exact h1
  have hbc' : 0 ≤ (s : ℝ) / (b + c) :=
    div_nonneg (Nat.cast_nonneg _) hbc.le
  unfold resolventPotential
  linarith

/-- **Initial-anchor bound.** `M ⪯ bdep·I` at quadratic-form level gives
`(I − M) ⪰ (1−bdep)·I`, hence `R ⪯ (1−bdep)⁻¹I` and
`F₁(M) = 1ᵀR1 − s ≤ s·bdep/(1−bdep)`: the paper's `F₁(M) ≤ Nbdep/(1−bdep)`. -/
theorem resolventPotential_le_initial {s : ℕ} {bdep : ℝ} {M : Input s s}
    (hpos : (slackMatrix 1 M).PosDef)
    (hM : ∀ x : Fin s → ℝ, x ⬝ᵥ (M *ᵥ x) ≤ bdep * (x ⬝ᵥ x))
    (_hbdep : 0 < bdep) (hbdep1 : bdep < 1) :
    resolventPotential 1 M ≤ (bdep / (1 - bdep)) * s := by
  have hqf : ∀ x : Fin s → ℝ,
      (1 - bdep) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (slackMatrix 1 M *ᵥ x) := by
    intro x
    rw [← slackQuadratic_eq_dotProduct 1 M x, slackQuadratic_eq_norm_sub]
    linarith [hM x]
  have h1 := qfLower_inv_le hpos hqf (by linarith : (0:ℝ) < 1 - bdep)
    (fun _ => (1 : ℝ))
  rw [dotProduct_ones] at h1
  have hsum : ∑ j, resolventVector 1 M j ≤ (1 - bdep)⁻¹ * (s : ℝ) := by
    rw [show (∑ j, resolventVector 1 M j) =
        (fun _ => (1 : ℝ)) ⬝ᵥ (resolventVector 1 M) from
      (dotProduct_ones_left _).symm]
    exact h1
  have hne : (1 - bdep) ≠ 0 := by linarith
  have hkey : (1 - bdep)⁻¹ * s - s = (bdep / (1 - bdep)) * s := by
    rw [div_mul_eq_mul_div]
    have e : (1 - bdep)⁻¹ * s - s = s * ((1 - bdep)⁻¹ - 1) := by ring
    rw [e]
    have e2 : (1 - bdep)⁻¹ - 1 = bdep * (1 - bdep)⁻¹ := by
      have h2 : bdep * (1 - bdep)⁻¹ =
          (1 - (1 - bdep)) * (1 - bdep)⁻¹ := by ring
      rw [h2, sub_mul, one_mul, mul_inv_cancel₀ hne]
    rw [e2]
    ring
  unfold resolventPotential
  rw [div_one]
  linarith [hsum, hkey]

/-- The epoch barrier schedule `b_j = 1 + ∑_{k=1}^{j} (4k²)⁻¹`. -/
noncomputable def epochBarrier (j : ℕ) : ℝ :=
  1 + ∑ k ∈ Finset.Icc 1 j, (4 * (k : ℝ) ^ 2)⁻¹

theorem epochBarrier_zero : epochBarrier 0 = 1 := by
  simp [epochBarrier]

theorem epochBarrier_succ (j : ℕ) :
    epochBarrier (j + 1) =
      epochBarrier j + (4 * ((j : ℝ) + 1) ^ 2)⁻¹ := by
  unfold epochBarrier
  rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ j + 1)]
  push_cast
  ring

theorem epochBarrier_sub_succ (j : ℕ) :
    epochBarrier (j + 1) - epochBarrier j = (4 * ((j : ℝ) + 1) ^ 2)⁻¹ := by
  rw [epochBarrier_succ]
  ring

/-- The telescoping step `1/(4(j+1)²) ≤ 1/(4j) − 1/(4(j+1))` for `j ≥ 1`. -/
theorem epochBarrier_step_le {j : ℕ} (hj : 1 ≤ j) :
    (4 * ((j : ℝ) + 1) ^ 2)⁻¹ ≤ (4 * (j : ℝ))⁻¹ - (4 * ((j : ℝ) + 1))⁻¹ := by
  have hjr : (0:ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hj1 : (0:ℝ) < (j : ℝ) + 1 := by linarith
  have h4j : (0:ℝ) < 4 * (j : ℝ) := by positivity
  have h4j1 : (0:ℝ) < 4 * ((j : ℝ) + 1) := by positivity
  have hdiff : (4 * (j : ℝ))⁻¹ - (4 * ((j : ℝ) + 1))⁻¹ =
      (4 * (j : ℝ) * ((j : ℝ) + 1))⁻¹ := by
    field_simp
    ring
  rw [hdiff, inv_le_inv₀ (by positivity) (by positivity)]
  calc 4 * (j : ℝ) * ((j : ℝ) + 1)
      ≤ (4 * ((j : ℝ) + 1)) * ((j : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 4 * ((j : ℝ) + 1) ^ 2 := by ring

/-- **Telescoping epoch sum.** `∑_{k=1}^{j} (4k²)⁻¹ ≤ 1/2 − 1/(4j)` for
`j ≥ 1`, via `1/(4k²) ≤ 1/(4(k−1)) − 1/(4k)`. -/
theorem epochBarrier_sum_le {j : ℕ} (hj : 1 ≤ j) :
    ∑ k ∈ Finset.Icc 1 j, (4 * (k : ℝ) ^ 2)⁻¹ ≤
      1 / 2 - (4 * (j : ℝ))⁻¹ := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ j + 1)]
    have hcast : (((j + 1 : ℕ)) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hstep := epochBarrier_step_le hj
    linarith

/-- **`b_j ≤ 3/2`** — the paper's `b_j ≤ 1 + π²/24 < 3/2`, proved by the
elementary telescope. -/
theorem epochBarrier_le_three_halves (j : ℕ) : epochBarrier j ≤ 3 / 2 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [epochBarrier_zero]
    norm_num
  · unfold epochBarrier
    have hsum := epochBarrier_sum_le hj
    have h4j : (0:ℝ) < 4 * (j : ℝ) := by
      have hjr : (0:ℝ) < (j : ℝ) := by exact_mod_cast hj
      positivity
    linarith [inv_pos.mpr h4j]

theorem epochBarrier_pos (j : ℕ) : 0 < epochBarrier j := by
  unfold epochBarrier
  have hnn : 0 ≤ ∑ k ∈ Finset.Icc 1 j, (4 * (k : ℝ) ^ 2)⁻¹ :=
    Finset.sum_nonneg fun k _ => by positivity
  linarith

theorem epochBarrier_mono (j : ℕ) : epochBarrier j ≤ epochBarrier (j + 1) := by
  rw [epochBarrier_succ]
  have : (0:ℝ) < (4 * ((j : ℝ) + 1) ^ 2)⁻¹ := by positivity
  linarith

/-- **Epoch-start potential bound, instantiated.** With
`c = (4(j+1)²)⁻¹ = b_{j+1} − b_j`, the previous-epoch slack PSD gives
`F_{b_{j+1}}(M) ≤ 4(j+1)²·s`: the paper's `F_{b_j}(M) ≤ 4Nj²` at epoch
starts. -/
theorem epoch_start_potential_le {s : ℕ} {j : ℕ} {M : Input s s}
    (hpos : (slackMatrix (epochBarrier (j + 1)) M).PosDef)
    (hpsd : ∀ x : Fin s → ℝ, 0 ≤ slackQuadratic (epochBarrier j) M x) :
    resolventPotential (epochBarrier (j + 1)) M ≤
      4 * ((j : ℝ) + 1) ^ 2 * s := by
  rw [epochBarrier_succ] at hpos ⊢
  have hc : (0:ℝ) < (4 * ((j : ℝ) + 1) ^ 2)⁻¹ := by positivity
  have hbc : 0 < epochBarrier j + (4 * ((j : ℝ) + 1) ^ 2)⁻¹ :=
    add_pos (epochBarrier_pos j) hc
  have h := resolventPotential_le_of_slack_psd_add hpos hpsd hc hbc
  rwa [inv_inv] at h

end Komlos
