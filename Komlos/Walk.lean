import Komlos

namespace Komlos

open scoped BigOperators

def squaredNorm {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ j, (x j) ^ 2

theorem squaredNorm_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ squaredNorm x :=
  Finset.sum_nonneg (fun j _ => sq_nonneg (x j))

theorem cube_squaredNorm_le {n : ℕ} (x : Fin n → ℝ) (hx : ∀ j, |x j| ≤ 1) :
    squaredNorm x ≤ n := by
  calc
    squaredNorm x ≤ ∑ _j : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      have hj := abs_le.mp (hx j)
      nlinarith
    _ = n := by simp

inductive SymmetricWalk (n : ℕ) where
  | leaf (x : Fin n → ℝ)
  | branch (x displacement : Fin n → ℝ) (left right : SymmetricWalk n)

namespace SymmetricWalk

def root {n : ℕ} : SymmetricWalk n → Fin n → ℝ
  | .leaf x => x
  | .branch x _ _ _ => x

def Coherent {n : ℕ} : SymmetricWalk n → Prop
  | .leaf _ => True
  | .branch x d left right =>
      root left = (fun j => x j + d j) ∧ root right = (fun j => x j - d j) ∧
        Coherent left ∧ Coherent right

def CubeLeaves {n : ℕ} : SymmetricWalk n → Prop
  | .leaf x => ∀ j, |x j| ≤ 1
  | .branch _ _ left right => CubeLeaves left ∧ CubeLeaves right

noncomputable def terminalEnergyAverage {n : ℕ} : SymmetricWalk n → ℝ
  | .leaf x => squaredNorm x
  | .branch _ _ left right => (terminalEnergyAverage left + terminalEnergyAverage right) / 2

noncomputable def squaredMoveAverage {n : ℕ} : SymmetricWalk n → ℝ
  | .leaf _ => 0
  | .branch _ d left right =>
      squaredNorm d + (squaredMoveAverage left + squaredMoveAverage right) / 2

noncomputable def largeMoveCountAverage {n : ℕ} (threshold : ℝ) : SymmetricWalk n → ℝ
  | .leaf _ => 0
  | .branch _ d left right =>
      (if threshold ≤ squaredNorm d then 1 else 0) +
        (largeMoveCountAverage threshold left + largeMoveCountAverage threshold right) / 2

theorem energy_accounting {n : ℕ} (tree : SymmetricWalk n) (hc : Coherent tree) :
    terminalEnergyAverage tree = squaredNorm (root tree) + squaredMoveAverage tree := by
  induction tree with
  | leaf x => simp [terminalEnergyAverage, squaredMoveAverage, root]
  | branch x d left right ihleft ihright =>
      obtain ⟨hl, hr, hcl, hcr⟩ := hc
      simp only [terminalEnergyAverage, squaredMoveAverage, root]
      rw [ihleft hcl, ihright hcr, hl, hr]
      have hs := symmetric_energy x d 1
      simp only [one_pow, one_mul] at hs
      unfold squaredNorm
      linarith

theorem terminal_energy_bound {n : ℕ} (tree : SymmetricWalk n) (hx : CubeLeaves tree) :
    terminalEnergyAverage tree ≤ n := by
  induction tree with
  | leaf x => exact cube_squaredNorm_le x hx
  | branch x d left right ihleft ihright =>
      have hl := ihleft hx.1
      have hr := ihright hx.2
      simp only [terminalEnergyAverage]
      linarith

theorem squared_move_budget {n : ℕ} (tree : SymmetricWalk n)
    (hc : Coherent tree) (hx : CubeLeaves tree) : squaredMoveAverage tree ≤ n := by
  have ha := energy_accounting tree hc
  have hb := terminal_energy_bound tree hx
  have hn := squaredNorm_nonneg (root tree)
  linarith

theorem large_move_cost_bound {n : ℕ} (tree : SymmetricWalk n) (threshold : ℝ) :
    threshold * largeMoveCountAverage threshold tree ≤ squaredMoveAverage tree := by
  induction tree with
  | leaf x => simp [largeMoveCountAverage, squaredMoveAverage]
  | branch x d left right ihleft ihright =>
      simp only [largeMoveCountAverage, squaredMoveAverage]
      split_ifs with hlarge
      · nlinarith
      · nlinarith [squaredNorm_nonneg d]

theorem full_step_count_bound {n : ℕ} (tree : SymmetricWalk n)
    (hc : Coherent tree) (hx : CubeLeaves tree) {τ : ℝ} (hτ : 0 < τ) :
    largeMoveCountAverage (τ ^ 2 / 9) tree ≤ 9 * n / τ ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hτ)).mpr
  have hcost := large_move_cost_bound tree (τ ^ 2 / 9)
  have hbudget := squared_move_budget tree hc hx
  nlinarith

noncomputable def terminalAverage {n : ℕ} (f : (Fin n → ℝ) → ℝ) : SymmetricWalk n → ℝ
  | .leaf x => f x
  | .branch _ _ left right => (terminalAverage f left + terminalAverage f right) / 2

def LeavesBound {n : ℕ} (f : (Fin n → ℝ) → ℝ) (bound : ℝ) : SymmetricWalk n → Prop
  | .leaf x => f x ≤ bound
  | .branch _ _ left right => LeavesBound f bound left ∧ LeavesBound f bound right

def LocalAverageNonincrease {n : ℕ} (f : (Fin n → ℝ) → ℝ) : SymmetricWalk n → Prop
  | .leaf _ => True
  | .branch x _ left right =>
      (f (root left) + f (root right)) / 2 ≤ f x ∧
        LocalAverageNonincrease f left ∧ LocalAverageNonincrease f right

theorem terminal_average_bound {n : ℕ} (f : (Fin n → ℝ) → ℝ) (bound : ℝ)
    (tree : SymmetricWalk n) (hle : LeavesBound f bound tree) : terminalAverage f tree ≤ bound := by
  induction tree with
  | leaf x => exact hle
  | branch x d left right ihleft ihright =>
      have hl := ihleft hle.1
      have hr := ihright hle.2
      simp only [terminalAverage]
      linarith

theorem terminal_average_le_root {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (tree : SymmetricWalk n) (hloc : LocalAverageNonincrease f tree) :
    terminalAverage f tree ≤ f (root tree) := by
  induction tree with
  | leaf x => exact le_rfl
  | branch x d left right ihleft ihright =>
      obtain ⟨hstep, hl, hr⟩ := hloc
      have hleft := ihleft hl
      have hright := ihright hr
      simp only [terminalAverage, root]
      linarith

noncomputable def markedMoveCountAverage {n : ℕ} (mark : SymmetricWalk n → Bool) :
    SymmetricWalk n → ℝ
  | .leaf _ => 0
  | .branch x d left right =>
      (if mark (.branch x d left right) then 1 else 0) +
        (markedMoveCountAverage mark left + markedMoveCountAverage mark right) / 2

def LocalProgress {n : ℕ} (f : (Fin n → ℝ) → ℝ) (mark : SymmetricWalk n → Bool) :
    SymmetricWalk n → Prop
  | .leaf _ => True
  | .branch x d left right =>
      f x + (if mark (.branch x d left right) then 1 else 0) / 2 ≤
          (f (root left) + f (root right)) / 2 ∧
        LocalProgress f mark left ∧ LocalProgress f mark right

theorem marked_progress_accounting {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (mark : SymmetricWalk n → Bool) (tree : SymmetricWalk n) (hprog : LocalProgress f mark tree) :
    f (root tree) + markedMoveCountAverage mark tree / 2 ≤ terminalAverage f tree := by
  induction tree with
  | leaf x => simp [root, markedMoveCountAverage, terminalAverage]
  | branch x d left right ihleft ihright =>
      obtain ⟨hstep, hl, hr⟩ := hprog
      have hleft := ihleft hl
      have hright := ihright hr
      simp only [root, markedMoveCountAverage, terminalAverage]
      linarith

theorem marked_step_count_bound {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (mark : SymmetricWalk n → Bool) (tree : SymmetricWalk n) (bound : ℝ)
    (hprog : LocalProgress f mark tree) (hle : LeavesBound f bound tree)
    (hroot : 0 ≤ f (root tree)) : markedMoveCountAverage mark tree ≤ 2 * bound := by
  have hp := marked_progress_accounting f mark tree hprog
  have ht := terminal_average_bound f bound tree hle
  linarith

end SymmetricWalk

theorem symmetric_boundary_hit {x d : ℝ} (h : |x| + |d| = 1) :
    |x + d| = 1 ∨ |x - d| = 1 := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 d with hd | hd
  · left
    rw [abs_of_nonneg hx, abs_of_nonneg hd] at h
    rw [abs_of_nonneg (add_nonneg hx hd)]
    exact h
  · right
    rw [abs_of_nonneg hx, abs_of_nonpos hd] at h
    rw [abs_of_nonneg (by linarith : 0 ≤ x - d)]
    linarith
  · right
    rw [abs_of_nonpos hx, abs_of_nonneg hd] at h
    rw [abs_of_nonpos (by linarith : x - d ≤ 0)]
    linarith
  · left
    rw [abs_of_nonpos hx, abs_of_nonpos hd] at h
    rw [abs_of_nonpos (add_nonpos hx hd)]
    linarith

theorem clipped_endpoint_hits_boundary {x h t : ℝ} (ht : 0 ≤ t)
    (hclip : t * |h| = 1 - |x|) : |x + t * h| = 1 ∨ |x - t * h| = 1 := by
  apply symmetric_boundary_hit
  rw [abs_mul, abs_of_nonneg ht]
  linarith

theorem symmetric_endpoints_in_cube {x h t : ℝ} (ht : 0 ≤ t)
    (hclip : |x| + t * |h| ≤ 1) : |x + t * h| ≤ 1 ∧ |x - t * h| ≤ 1 := by
  have hd : |t * h| = t * |h| := by rw [abs_mul, abs_of_nonneg ht]
  constructor
  · have hs := abs_add_le x (t * h)
    rw [hd] at hs
    linarith
  · have hs := abs_sub x (t * h)
    rw [hd] at hs
    linarith

end Komlos
