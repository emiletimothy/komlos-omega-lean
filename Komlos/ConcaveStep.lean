import Komlos
import Komlos.Walk
import Mathlib.Analysis.Convex.Function

/-!
# Concave potentials and the batched symmetric step

The engine of the paper's potential analysis is the last line of
Proposition 2.1: whenever `x − th`, `x`, `x + th` all lie in the
concave window of the resolvent potential, an independent fair sign
`σ` satisfies `𝔼_σ F_b(M(x + σth)) ≤ F_b(M(x))`.

`Komlos.Walk` already packages the walk as a binary tree whose
`LocalAverageNonincrease` predicate asks, at every branch
`x ↦ {x + d, x − d}`, for the two-point inequality
`(f(x + d) + f(x − d))/2 ≤ f x`.  This module shows that pointwise
*concavity* of the one-dimensional restrictions `t ↦ f (x + t • d)`
on the unit window is exactly what is needed to discharge that
predicate — and hence, via `terminal_average_le_root`, that the
terminal average of `f` over the tree (the fair-sign expectation) is
at most its root value.

The remaining analytic input — that `t ↦ F_b (M (x + t • h))` is
indeed concave on the window — is the Hessian inequality
`P_x[h] ≤ (1 − ρ/2) D_x[h]` of Proposition 2.1, proved through the
derivative identities of `Komlos.Curvature` together with the
spectral-subspace construction (in progress elsewhere).
-/

namespace Komlos

/-- The two-point concavity inequality on a symmetric interval:
the fair-sign average at `±T` is at most the center value. -/
theorem concaveOn_pair_average_le {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : ConcaveOn ℝ (Set.Icc (-T) T) f) :
    (f T + f (-T)) / 2 ≤ f 0 := by
  have hmem_neg : -T ∈ Set.Icc (-T) T := Set.left_mem_Icc.mpr (by linarith)
  have hmem_pos : T ∈ Set.Icc (-T) T := Set.right_mem_Icc.mpr (by linarith)
  have h := hf.2 hmem_neg hmem_pos
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hmid : (1 / 2 : ℝ) • (-T) + (1 / 2 : ℝ) • T = 0 := by
    simp [smul_eq_mul]
  rw [hmid] at h
  simp only [smul_eq_mul] at h
  linarith

/-- A single coherent branch of a `SymmetricWalk` does not increase a
potential that is concave along the displacement direction on the
unit window. -/
theorem concaveOn_branch_average_le {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (x d : Fin n → ℝ)
    (hf : ConcaveOn ℝ (Set.Icc (-1) 1)
      (fun t => f (fun j => x j + t * d j))) :
    (f (fun j => x j + d j) + f (fun j => x j - d j)) / 2 ≤ f x := by
  have h := concaveOn_pair_average_le (by norm_num) hf
  have hpos : (fun j => x j + (1 : ℝ) * d j) = (fun j => x j + d j) := by
    funext j; ring
  have hneg : (fun j => x j + (-1 : ℝ) * d j) = (fun j => x j - d j) := by
    funext j; ring
  have hzero : (fun j => x j + (0 : ℝ) * d j) = x := by
    funext j; ring
  rw [hpos, hneg, hzero] at h
  exact h

/-- Predicate on a `SymmetricWalk`: at every branch, the potential is
concave along the displacement direction on the unit window. -/
def BranchConcave {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    SymmetricWalk n → Prop
  | .leaf _ => True
  | .branch x d left right =>
      ConcaveOn ℝ (Set.Icc (-1) 1)
        (fun t => f (fun j => x j + t * d j)) ∧
        BranchConcave f left ∧ BranchConcave f right

/-- Branchwise concavity implies the walk's local
average-nonincrease invariant. -/
theorem localAverageNonincrease_of_branchConcave {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (tree : SymmetricWalk n)
    (hc : SymmetricWalk.Coherent tree) (hconc : BranchConcave f tree) :
    SymmetricWalk.LocalAverageNonincrease f tree := by
  induction tree with
  | leaf x => trivial
  | branch x d left right ihleft ihright =>
      obtain ⟨hl, hr, hcl, hcr⟩ := hc
      obtain ⟨hstep, hconcl, hconcr⟩ := hconc
      refine ⟨?_, ihleft hcl hconcl, ihright hcr hconcr⟩
      rw [hl, hr]
      exact concaveOn_branch_average_le f x d hstep

/-- **Walk-level expectation bound.** If the potential is concave
along every branch displacement of a coherent symmetric walk, the
terminal average — the fair-sign expectation of `f` over the leaves —
is at most `f` at the root.  This is the combinatorial content of
Proposition 2.1's final inequality iterated over a batch. -/
theorem terminal_average_le_root_of_branchConcave {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (tree : SymmetricWalk n)
    (hc : SymmetricWalk.Coherent tree) (hconc : BranchConcave f tree) :
    SymmetricWalk.terminalAverage f tree ≤ f (SymmetricWalk.root tree) :=
  SymmetricWalk.terminal_average_le_root f tree
    (localAverageNonincrease_of_branchConcave f tree hc hconc)

end Komlos
