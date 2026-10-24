/-
# Uniform-depth walks and the coin-path correspondence

This module connects `SymmetricWalk` to the finite coin model of
`SubGaussianBound`. For a *coherent* walk of *uniform depth* `k`, each
leaf is reached by exactly one coin sequence `ε : Fin k → Bool`, the
uniform leaf average is `unifAvg` over the coin cube, and the leaf
position is a predictable sign-weighted sum of the branch displacements
met along the path. This makes `signSum_tail_le` — the exponential
(C.2)-type concentration bound — applicable to any additive,
homogeneous readout of the adaptive walk (e.g. a row inner product):
under a pathwise quadratic budget `∑ (ρ dᵢ)² ≤ Q`,

  `Pr_leaves[ |ρ(leaf) − ρ(root)| ≥ u ] ≤ 2·exp(−u²/(2Q))`.

No `sorry`, `admit`, axioms, or `native_decide` are used.
-/

import Komlos.Walk
import Komlos.SubGaussianBound

namespace Komlos

open SymmetricWalk

/-! ## Uniform depth -/

/-- Every leaf of `t` sits exactly `k` branchings below the root. The
batched-walk epochs of the paper are depth-uniform by construction. -/
inductive UniformDepth {n : ℕ} : SymmetricWalk n → ℕ → Prop
  | leaf (x : Fin n → ℝ) : UniformDepth (.leaf x) 0
  | branch {x d : Fin n → ℝ} {l r : SymmetricWalk n} {k : ℕ} :
      UniformDepth l k → UniformDepth r k →
        UniformDepth (.branch x d l r) (k + 1)

/-- Coherence is inherited by the left subtree. -/
theorem coherent_left {n : ℕ} {x d : Fin n → ℝ} {l r : SymmetricWalk n}
    (h : Coherent (.branch x d l r)) : Coherent l := h.2.2.1

/-- Coherence is inherited by the right subtree. -/
theorem coherent_right {n : ℕ} {x d : Fin n → ℝ} {l r : SymmetricWalk n}
    (h : Coherent (.branch x d l r)) : Coherent r := h.2.2.2

/-! ## The `Fin.cons` tower property -/

/-- Splitting `Fin (k+1) → C` by the *first* coin — the `Fin.cons`
counterpart of `Fin.snocEquiv`. -/
def consEquiv {C : Type*} {k : ℕ} :
    (Fin (k + 1) → C) ≃ C × (Fin k → C) where
  toFun ε := (ε 0, Fin.tail ε)
  invFun p := Fin.cons p.1 p.2
  left_inv := fun ε => Fin.cons_self_tail ε
  right_inv := fun ⟨c, η⟩ => by
    show (Fin.cons c η 0, Fin.tail (Fin.cons c η)) = (c, η)
    refine Prod.ext ?_ ?_
    · exact Fin.cons_zero
    · funext j
      show Fin.cons c η j.succ = η j
      exact Fin.cons_succ

theorem sum_pi_succ_cons {C : Type*} [Fintype C] {k : ℕ}
    (F : (Fin (k + 1) → C) → ℝ) :
    ∑ ε : Fin (k + 1) → C, F ε =
      ∑ c : C, ∑ η : Fin k → C, F (Fin.cons c η) := by
  have h := Equiv.sum_comp (consEquiv (C := C)).symm F
  rw [← h, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro η _
  rfl

/-- Tower property, first-coin direction. -/
theorem unifAvg_pi_succ_cons {C : Type*} [Fintype C] {k : ℕ}
    (F : (Fin (k + 1) → C) → ℝ) :
    unifAvg F = unifAvg (fun c : C =>
      unifAvg (fun η : Fin k → C => F (Fin.cons c η))) := by
  have hCk : (Fintype.card (Fin k → C) : ℝ) = (Fintype.card C : ℝ) ^ k := by
    rw [card_piFin]; norm_cast
  have hCk1 : (Fintype.card (Fin (k + 1) → C) : ℝ) =
      (Fintype.card C : ℝ) * (Fintype.card C : ℝ) ^ k := by
    rw [card_piFin]; push_cast; ring
  simp only [unifAvg]
  rw [sum_pi_succ_cons F, hCk1, hCk, ← Finset.sum_div, div_div,
    mul_comm ((Fintype.card C : ℝ) ^ k)]

/-- Averaging over `Bool` is the two-term mean. -/
theorem unifAvg_bool (f : Bool → ℝ) :
    unifAvg f = (f true + f false) / 2 := by
  rw [unifAvg, Fintype.sum_bool, Fintype.card_bool]
  norm_cast

/-! ## Descent along a coin path -/

/-- Follow one coin at a node; leaves absorb further coins. -/
def stepCoin {n : ℕ} : SymmetricWalk n → Bool → SymmetricWalk n
  | .branch _ _ l _, true => l
  | .branch _ _ _ r, false => r
  | t, _ => t

theorem stepCoin_true {n : ℕ} (x d : Fin n → ℝ) (l r : SymmetricWalk n) :
    stepCoin (.branch x d l r) true = l := rfl

theorem stepCoin_false {n : ℕ} (x d : Fin n → ℝ) (l r : SymmetricWalk n) :
    stepCoin (.branch x d l r) false = r := rfl

/-- The node reached after `i` descent steps along `ε`. Coins beyond the
sequence length are ignored. -/
def nodeAfter {n k : ℕ} (t : SymmetricWalk n) (ε : Fin k → Bool) :
    ℕ → SymmetricWalk n
  | 0 => t
  | i + 1 =>
    if h : i < k then stepCoin (nodeAfter t ε i) (ε ⟨i, h⟩)
    else nodeAfter t ε i

/-- The displacement recorded at a node (`0` at a leaf). -/
def nodeDisp {n : ℕ} : SymmetricWalk n → Fin n → ℝ
  | .branch _ d _ _ => d
  | .leaf _ => 0

/-- The leaf reached by descending `t` along `ε`: `ε 0` selects the
root's left (`true`, the `+d` child) or right (`false`, the `−d` child),
then `Fin.tail ε` continues. For out-of-depth inputs the root is
returned. -/
def leafAt {n : ℕ} : (t : SymmetricWalk n) →
    ∀ {k : ℕ}, (Fin k → Bool) → Fin n → ℝ
  | .leaf x, _, _ => x
  | .branch x _ _ _, 0, _ => x
  | .branch _ _ l r, _ + 1, ε =>
    if ε 0 then leafAt l (Fin.tail ε) else leafAt r (Fin.tail ε)

/-- `leafAt` unfolded on a `Fin.cons` path. -/
theorem leafAt_cons {n k : ℕ} {x d : Fin n → ℝ} {l r : SymmetricWalk n}
    (c : Bool) (η : Fin k → Bool) :
    leafAt (.branch x d l r) (Fin.cons c η) =
      if c then leafAt l η else leafAt r η := by
  simp only [leafAt, Fin.cons_zero, Fin.tail_cons]

/-- `nodeAfter` satisfies the one-step recursion at an in-range index. -/
theorem nodeAfter_succ {n k : ℕ} (t : SymmetricWalk n) (ε : Fin k → Bool)
    {i : ℕ} (hi : i < k) :
    nodeAfter t ε (i + 1) =
      stepCoin (nodeAfter t ε i) (ε ⟨i, hi⟩) := by
  show (if h : i < k then stepCoin (nodeAfter t ε i) (ε ⟨i, h⟩)
    else nodeAfter t ε i) = _
  rw [dite_eq_left hi]

/-- `nodeAfter` is constant once `i` reaches `k`. -/
theorem nodeAfter_const {n k : ℕ} (t : SymmetricWalk n)
    (ε : Fin k → Bool) {i : ℕ} (hi : ¬ i < k) :
    nodeAfter t ε (i + 1) = nodeAfter t ε i := by
  show (if h : i < k then stepCoin (nodeAfter t ε i) (ε ⟨i, h⟩)
    else nodeAfter t ε i) = _
  rw [dite_eq_right hi]

/-- `nodeAfter` is predictable: the node at step `i` depends only on
coins strictly before `i`. -/
theorem nodeAfter_predictable {n k : ℕ} (t : SymmetricWalk n)
    (i : ℕ) (ε ε' : Fin k → Bool)
    (h : ∀ j : Fin k, j.val < i → ε j = ε' j) :
    nodeAfter t ε i = nodeAfter t ε' i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h' : ∀ j : Fin k, j.val < i → ε j = ε' j :=
      fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self i))
    by_cases hi : i < k
    · have hε : ε ⟨i, hi⟩ = ε' ⟨i, hi⟩ := h ⟨i, hi⟩ (Nat.lt_succ_self i)
      rw [nodeAfter_succ t ε hi, nodeAfter_succ t ε' hi, ih h', hε]
    · rw [nodeAfter_const t ε hi, nodeAfter_const t ε' hi]
      exact ih h'

/-- A leaf absorbs every descent step. -/
theorem nodeAfter_leaf {n k : ℕ} (x : Fin n → ℝ) (ε : Fin k → Bool)
    (i : ℕ) : nodeAfter (.leaf x) ε i = .leaf x := by
  induction i with
  | zero => rfl
  | succ i ih =>
    by_cases hi : i < k
    · rw [nodeAfter_succ _ _ hi, ih]
      rfl
    · rw [nodeAfter_const _ _ hi, ih]

/-- Shifting the path: `i + 1` steps in `t` along `ε` is `i` steps in
the chosen child along `Fin.tail ε`. -/
theorem nodeAfter_succ_eq_tail {n k : ℕ} (t : SymmetricWalk n)
    (ε : Fin (k + 1) → Bool) (i : ℕ) :
    nodeAfter t ε (i + 1) =
      nodeAfter (stepCoin t (ε 0)) (Fin.tail ε) i := by
  induction i with
  | zero =>
    rw [nodeAfter_succ t ε (Nat.zero_lt_succ k)]
    show stepCoin t (ε ⟨0, Nat.zero_lt_succ k⟩) = stepCoin t (ε 0)
    congr 2
    exact Fin.ext rfl
  | succ i ih =>
    by_cases hi : i < k
    · have hik : i + 1 < k + 1 := Nat.succ_lt_succ hi
      have htk : (Fin.tail ε) ⟨i, hi⟩ = ε ⟨i + 1, hik⟩ := rfl
      rw [nodeAfter_succ t ε hik, ih,
        nodeAfter_succ _ (Fin.tail ε) hi, htk]
    · have hik : ¬ (i + 1 < k + 1) := by omega
      rw [nodeAfter_const t ε hik, nodeAfter_const _ (Fin.tail ε) hi]
      exact ih

/-- `leafAt` is the root of the fully descended node. -/
theorem leafAt_eq_root_nodeAfter {n : ℕ} : ∀ (t : SymmetricWalk n)
    {k : ℕ} (ε : Fin k → Bool),
    leafAt t ε = root (nodeAfter t ε k) := by
  intro t k
  induction k generalizing t with
  | zero => intro ε; cases t <;> rfl
  | succ k ih =>
    intro ε
    cases t with
    | leaf x =>
      rw [nodeAfter_leaf]
      rfl
    | branch x d l r =>
      simp only [leafAt]
      rw [nodeAfter_succ_eq_tail]
      by_cases hc : ε 0 = true
      · rw [ite_eq_left hc, hc, stepCoin_true]
        exact ih l (Fin.tail ε)
      · rw [ite_eq_right hc]
        rw [Bool.not_eq_true] at hc
        rw [hc, stepCoin_false]
        exact ih r (Fin.tail ε)

/-- A descended node at step `i < k` of a depth-`k` tree is a branch. -/
theorem nodeAfter_branch {n : ℕ} : ∀ {t : SymmetricWalk n} {k : ℕ},
    UniformDepth t k → ∀ (ε : Fin k → Bool) {i : ℕ}, i < k →
      ∃ x d l r, nodeAfter t ε i = .branch x d l r := by
  intro t k hU
  induction hU with
  | leaf =>
    intro ε i hi
    exact absurd hi (Nat.not_lt_zero _)
  | @branch x d l r k' _hl _hr ihl ihr =>
    intro ε i hi
    cases i with
    | zero => exact ⟨x, d, l, r, rfl⟩
    | succ i =>
      have hi' : i < k' := by omega
      rw [nodeAfter_succ_eq_tail]
      by_cases hc : ε 0 = true
      · rw [hc, stepCoin_true]
        exact ihl (Fin.tail ε) hi'
      · rw [Bool.not_eq_true] at hc
        rw [hc, stepCoin_false]
        exact ihr (Fin.tail ε) hi'

/-- Coherence propagates along the descent. -/
theorem coherent_nodeAfter {n : ℕ} : ∀ {t : SymmetricWalk n} {k : ℕ},
    UniformDepth t k → Coherent t → ∀ (ε : Fin k → Bool) {i : ℕ},
      i ≤ k → Coherent (nodeAfter t ε i) := by
  intro t k hU
  induction hU with
  | leaf =>
    intro hC ε i hi
    have : i = 0 := by omega
    subst this
    exact hC
  | @branch x d l r k' _hl _hr ihl ihr =>
    intro hC ε i hi
    cases i with
    | zero => exact hC
    | succ i =>
      have hi' : i ≤ k' := by omega
      rw [nodeAfter_succ_eq_tail]
      by_cases hc : ε 0 = true
      · rw [hc, stepCoin_true]
        exact ihl (coherent_left hC) (Fin.tail ε) hi'
      · rw [Bool.not_eq_true] at hc
        rw [hc, stepCoin_false]
        exact ihr (coherent_right hC) (Fin.tail ε) hi'

/-! ## The displacement telescope -/

/-- The `j`-th coin, padded by `false` out of range. -/
def coinAt {k : ℕ} (ε : Fin k → Bool) (j : ℕ) : Bool :=
  if h : j < k then ε ⟨j, h⟩ else false

theorem coinAt_of_lt {k : ℕ} (ε : Fin k → Bool) {j : ℕ} (hj : j < k) :
    coinAt ε j = ε ⟨j, hj⟩ := by
  unfold coinAt
  rw [dite_eq_left hj]

/-- One descent step along a coherent branch adds `±d` componentwise. -/
theorem root_stepCoin_branch {n : ℕ} {x d : Fin n → ℝ}
    {l r : SymmetricWalk n} (hC : Coherent (.branch x d l r)) (c : Bool) :
    root (stepCoin (.branch x d l r) c) =
      fun j => x j + boolSign c * d j := by
  obtain ⟨hl, hr, _, _⟩ := hC
  cases c with
  | true => rw [stepCoin_true, hl]; simp [boolSign]
  | false => rw [stepCoin_false, hr]; funext j; simp [boolSign, sub_eq_add_neg]

/-- One descent step adds `boolSign(εᵢ) • d` to the root. -/
theorem root_nodeAfter_succ {n k : ℕ} {t : SymmetricWalk n}
    (hU : UniformDepth t k) (hC : Coherent t) (ε : Fin k → Bool)
    {i : ℕ} (hi : i < k) :
    root (nodeAfter t ε (i + 1)) =
      root (nodeAfter t ε i) +
        boolSign (ε ⟨i, hi⟩) • nodeDisp (nodeAfter t ε i) := by
  rw [nodeAfter_succ t ε hi]
  obtain ⟨x', d', l', r', hnode⟩ := nodeAfter_branch hU ε hi
  have hCn := coherent_nodeAfter hU hC ε hi.le
  rw [hnode] at hCn ⊢
  rw [root_stepCoin_branch hCn]
  funext j
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rfl

/-- **Displacement telescope**: after `i ≤ k` steps the root is the
start plus the predictable sign-weighted displacement sum. -/
theorem root_nodeAfter_eq_add_dispSum {n k : ℕ} {t : SymmetricWalk n}
    (hU : UniformDepth t k) (hC : Coherent t) (ε : Fin k → Bool) :
    ∀ {i : ℕ} (hi : i ≤ k),
    root (nodeAfter t ε i) =
      root t + ∑ j ∈ Finset.range i,
        boolSign (coinAt ε j) • nodeDisp (nodeAfter t ε j) := by
  intro i
  induction i with
  | zero =>
    intro _
    show (nodeAfter t ε 0).root =
      t.root + ∑ j ∈ Finset.range 0,
        boolSign (coinAt ε j) • nodeDisp (nodeAfter t ε j)
    simp
  | succ i ih =>
    intro hi
    have hik : i < k := by omega
    have hik' : i ≤ k := le_of_lt hik
    rw [root_nodeAfter_succ hU hC ε hik, ih hik',
      Finset.sum_range_succ, coinAt_of_lt ε hik, add_assoc]

/-- The leaf position is the root plus the sign-weighted displacement
sum over the whole path. -/
theorem leafAt_eq_root_add_dispSum {n k : ℕ} {t : SymmetricWalk n}
    (hU : UniformDepth t k) (hC : Coherent t) (ε : Fin k → Bool) :
    leafAt t ε =
      root t + ∑ j : Fin k,
        boolSign (ε j) • nodeDisp (nodeAfter t ε j.val) := by
  have hcoin : ∀ j : Fin k,
      boolSign (ε j) • nodeDisp (nodeAfter t ε j.val) =
        boolSign (coinAt ε j.val) •
          nodeDisp (nodeAfter t ε j.val) := by
    intro j
    rw [coinAt_of_lt ε j.isLt]
  rw [leafAt_eq_root_nodeAfter,
    root_nodeAfter_eq_add_dispSum hU hC ε le_rfl]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  exact (hcoin j).symm

/-! ## The leaf-average = coin-average identity -/

/-- For a depth-uniform tree, the uniform leaf average equals the
uniform average over coin sequences — the leaves of a depth-`k` walk
are in bijection with `Fin k → Bool`. -/
theorem terminalAverage_eq_unifAvg_leafAt {n : ℕ} :
    ∀ {t : SymmetricWalk n} {k : ℕ}, UniformDepth t k →
      ∀ (f : (Fin n → ℝ) → ℝ),
    terminalAverage f t =
      unifAvg (fun ε : Fin k → Bool => f (leafAt t ε)) := by
  intro t k hU
  induction hU with
  | leaf x =>
    intro f
    haveI : Nonempty (Fin 0 → Bool) := ⟨Fin.elim0⟩
    simp only [terminalAverage, leafAt]
    exact (unifAvg_const (f x)).symm
  | @branch x d l r k' _hl _hr ihl ihr =>
    intro f
    have hT : unifAvg (fun η : Fin k' → Bool =>
          f (leafAt (.branch x d l r) (Fin.cons true η))) =
        unifAvg (fun η : Fin k' → Bool => f (leafAt l η)) := by
      congr 1
      funext η
      rw [leafAt_cons]
      simp
    have hF : unifAvg (fun η : Fin k' → Bool =>
          f (leafAt (.branch x d l r) (Fin.cons false η))) =
        unifAvg (fun η : Fin k' → Bool => f (leafAt r η)) := by
      congr 1
      funext η
      rw [leafAt_cons]
      simp
    simp only [terminalAverage]
    rw [unifAvg_pi_succ_cons]
    simp only [unifAvg_bool, hT, hF]
    rw [ihl f, ihr f]

/-! ## Linear readouts and the (C.2) tail -/

/-- An additive readout commutes with finite sums. -/
theorem map_sum_of_additive {n : ℕ} {ι : Type*} [DecidableEq ι]
    (ρ : (Fin n → ℝ) → ℝ)
    (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y) (hzero : ρ 0 = 0)
    (s : Finset ι) (f : ι → Fin n → ℝ) :
    ρ (∑ i ∈ s, f i) = ∑ i ∈ s, ρ (f i) := by
  induction s using Finset.induction with
  | empty => simp [hzero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, hadd, ih]

/-- For a linear readout `ρ`, the centered leaf readout is the
predictable `signSum` of the displacement readouts. -/
theorem leaf_readout_eq_signSum {n k : ℕ} {t : SymmetricWalk n}
    (hU : UniformDepth t k) (hC : Coherent t)
    (ρ : (Fin n → ℝ) → ℝ)
    (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y)
    (hsmul : ∀ c x, ρ (c • x) = c * ρ x)
    (ε : Fin k → Bool) :
    ρ (leafAt t ε) - ρ (root t) =
      signSum (fun i ε' => ρ (nodeDisp (nodeAfter t ε' i.val)))
        boolSign ε := by
  have hzero : ρ 0 = 0 := by
    have h := hsmul 0 0
    simp at h
    exact h
  rw [leafAt_eq_root_add_dispSum hU hC ε, hadd,
    map_sum_of_additive ρ hadd hzero]
  have hcancel : ρ (root t) + ∑ j : Fin k,
      ρ (boolSign (ε j) • nodeDisp (nodeAfter t ε j.val)) -
        ρ (root t) =
      ∑ j : Fin k,
        ρ (boolSign (ε j) • nodeDisp (nodeAfter t ε j.val)) := by
    ring
  rw [hcancel]
  unfold signSum
  apply Finset.sum_congr rfl
  intro j _
  show ρ (boolSign (ε j) • nodeDisp (nodeAfter t ε j.val)) =
    ρ (nodeDisp (nodeAfter t ε j.val)) * boolSign (ε j)
  rw [hsmul, mul_comm]

/-- The predictable increment family along the walk. -/
theorem nodeDisp_readout_predictable {n k : ℕ} (t : SymmetricWalk n)
    (ρ : (Fin n → ℝ) → ℝ) :
    Predictable (fun i : Fin k => fun ε : Fin k → Bool =>
      ρ (nodeDisp (nodeAfter t ε i.val))) := by
  intro i ε ε' h
  show ρ (nodeDisp (nodeAfter t ε i.val)) =
    ρ (nodeDisp (nodeAfter t ε' i.val))
  rw [nodeAfter_predictable t i.val ε ε' (fun j hj => h j hj)]

/-- **(C.2) on the adaptive walk.** For a coherent, depth-uniform walk
and any additive, homogeneous readout `ρ` (e.g. a row inner product),
the uniform leaf distribution of `ρ(leaf) − ρ(root)` obeys the
sub-Gaussian tail `2·exp(−u²/(2Q))` whenever the predictable
displacement squares are pathwise bounded by `Q`. This is the paper's
capped-walk concentration input specialized to the finite coin model. -/
theorem leaf_linear_tail_le {n k : ℕ} {t : SymmetricWalk n}
    (hU : UniformDepth t k) (hC : Coherent t)
    {ρ : (Fin n → ℝ) → ℝ}
    (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y)
    (hsmul : ∀ c x, ρ (c • x) = c * ρ x)
    {Q u : ℝ} (hQ0 : 0 < Q) (hu : 0 < u)
    (hbudget : ∀ ε : Fin k → Bool,
      ∑ i : Fin k, (ρ (nodeDisp (nodeAfter t ε i.val))) ^ 2 ≤ Q) :
    unifAvg (fun ε : Fin k → Bool =>
        if u ≤ |ρ (leafAt t ε) - ρ (root t)| then (1 : ℝ) else 0) ≤
      2 * Real.exp (- u ^ 2 / (2 * Q)) := by
  have hS : ∀ ε : Fin k → Bool,
      ρ (leafAt t ε) - ρ (root t) =
        signSum (fun i ε' => ρ (nodeDisp (nodeAfter t ε' i.val)))
          boolSign ε :=
    leaf_readout_eq_signSum hU hC ρ hadd hsmul
  have ha := nodeDisp_readout_predictable t ρ
  have hmgf := signSum_tail_le _ ha hbudget hQ0 hu
  refine le_trans ?_ hmgf
  apply unifAvg_le_unifAvg
  intro ε
  rw [hS ε]

end Komlos
