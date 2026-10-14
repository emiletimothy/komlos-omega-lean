/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Komlos.Walk
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Trial concentration: a finite uniform model for the sign sampler

This file gives the trial/sampler mechanism of the paper a *finite, fully
computable* probability model: the uniform distribution on the `2 ^ n` sign
vectors `ε : Fin n → Bool`, realized as the normalized sum

```
signAvg f = (∑ ε : Fin n → Bool, f ε) / 2 ^ n
```

over a `Finset.univ` of a `Fintype`. This is deliberately the same
"average over leaves" formulation used by `SymmetricWalk.terminalAverage` in
`Komlos/Walk.lean`, so the two models can be connected by an identity rather
than by a measure-theoretic equivalence.

## What is proved unconditionally

* `sign_self_sum`, `sign_cross_sum`, `sign_product_sum`: for uniform random
  signs, `∑ ε, s ε j * s ε k = 2 ^ n` when `j = k` and `0` otherwise (the
  coordinate-flip involution `flipAt` pairs the `2 ^ n` outcomes into terms
  that cancel).
* `sum_sign_rowValue_sq`, `signAvg_rowValue_sq`: the second-moment identity
  `E_ε[(⟨row_i, ε⟩)²] = ∑ j, (A i j)²`. This is the Gaussian-free version of
  the paper's second-moment control of a single trial.
* `signAvg_sum_rowValue_sq`, `signAvg_sum_rowValue_sq_le`: averaging over rows
  gives `E_ε[∑ i (row_i ε)²] = ∑ i,j (A i j)² ≤ n` for `ColumnNormalized A`
  (via `total_mass_le_dimension`).
* `sq_mul_filter_card_le_sum_sq`, `sq_mul_badRowCount_le`: deterministic
  Markov-type counting `T² · #{bad} ≤ ∑ value²`.
* `sum_badRowCount_le`, `signAvg_badRowCount_le`,
  `exists_signing_few_bad_rows`: for `0 < T`, the expected number of rows with
  `|row_i ε| ≥ T` is at most `n / T²`, and hence **there exists** a signing
  with at most `n / T²` bad rows — the finite analogue of a successful trial.
* `row_tail_fraction_le`: the single-row tail bound
  `Pr_ε[|row_i ε| ≥ T] ≤ (∑ j (A i j)²) / T²` (Markov on the second moment).
* `signAvg_const`: normalization `E[1] = 1`.

## The connection to `SymmetricWalk` (proved, not assumed)

* `cubeDown`: an explicit full-depth symmetric binary tree whose branching at
  level `k + 1` flips coordinate `⟨k, _⟩`. Its `2 ^ k` leaves enumerate the
  cube: `cubeDown n x` has `2 ^ n` leaves, all signings.
* `terminalAverage_cubeTop`: `terminalAverage f (cubeDown n x)` is *exactly*
  the uniform average `signAvg (fun ε ↦ f (realSigning ε))`. So the
  leaf-uniform model of `Walk.lean` and the uniform-sign model coincide on the
  nose — no hypothesis needed. The proof expands the sum over
  `Fin (k+1) → Bool` by `Fin.snocEquiv`.
* `cubeDown_coherent`, `cubeDown_cubeLeaves`: `cubeDown n 0` satisfies the
  `Coherent` and `CubeLeaves` invariants of `Walk.lean`, so the energy
  accounting there applies.
* `memLeaf_cubeDown`: every leaf of `cubeDown k x` has `±1` in coordinates
  `< k` and agrees with `x` elsewhere; hence every leaf of `cubeDown n x` is an
  `IsSigning`.
* `exists_memLeaf_signing_few_bad_rows`: the "successful trial" statement
  inside the walk model — some leaf of the cube walk is a signing with at most
  `n / T²` bad rows.

## What is conditional, and what is omitted

* `exists_in_support_few_bad_rows` is the conditional/parameterized form: for
  *any* finite sampler with weights `w ε ≥ 0` of positive total mass, *if* the
  weighted second moment `∑ ε, w ε · ∑ i (row_i ε)² ≤ D`, then some point of
  the support has at most `D / (T² · ∑ w)` bad rows. This is the rigorous
  content of "if the sampler's marginal averages satisfy the bound, then a
  trial succeeds" — uniform `w` recovers the unconditional theorem.
* Omitted (needs Gaussian tails, adaptive conditioning, or the paper's
  per-coordinate clipping dynamics): the `e^{-Ω(T²)}` Gaussian tail, the
  concentration of *the adaptive walk's* terminal value (Lemma D.1), and any
  quantification over the randomized rounding order. The uniform model only
  provides polynomial (Markov) concentration; the paper's sub-constant
  discrepancy uses the Gaussian potential analysis formalized elsewhere
  (`GaussianCompletion.lean`), not this file.
-/

namespace Komlos

open scoped BigOperators

/-- The uniform average over all `2 ^ n` sign vectors `ε : Fin n → Bool`.
This is the finite uniform probability model for the trial sampler: no measure
theory is needed because the state space is a `Fintype`. -/
noncomputable def signAvg {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ :=
  (∑ ε : Fin n → Bool, f ε) / (2 : ℝ) ^ n

/-- `2 ^ n` is never zero as a real number. -/
private theorem two_pow_ne_zero (n : ℕ) : (2 : ℝ) ^ n ≠ 0 :=
  pow_ne_zero _ (by norm_num)

theorem signAvg_const {n : ℕ} (c : ℝ) : signAvg (fun _ : Fin n → Bool => c) = c := by
  rw [signAvg, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [mul_comm, mul_div_assoc, div_self (two_pow_ne_zero n), mul_one]

/-- Flipping one coordinate of a sign vector. -/
def flipAt {n : ℕ} (k : Fin n) (ε : Fin n → Bool) : Fin n → Bool :=
  Function.update ε k (!ε k)

/-- Coordinate flip is an involution on sign vectors. -/
theorem flipAt_involutive {n : ℕ} (k : Fin n) :
    Function.Involutive (flipAt k) := by
  intro ε
  funext c
  by_cases hc : c = k
  · subst hc
    simp [flipAt]
  · simp only [flipAt]
    rw [Function.update_of_ne hc, Function.update_of_ne hc]

theorem realSigning_flipAt_self {n : ℕ} (k : Fin n) (ε : Fin n → Bool) :
    realSigning (flipAt k ε) k = -realSigning ε k := by
  cases h : ε k <;> simp [realSigning, flipAt, h]

theorem realSigning_flipAt_of_ne {n : ℕ} {j k : Fin n} (h : j ≠ k)
    (ε : Fin n → Bool) :
    realSigning (flipAt k ε) j = realSigning ε j := by
  simp [realSigning, flipAt, Function.update_of_ne h]

/-- Diagonal sign correlations: `∑ ε, s_j² = 2^n` since each `s_j² = 1`. -/
theorem sign_self_sum {n : ℕ} (j : Fin n) :
    ∑ ε : Fin n → Bool, realSigning ε j * realSigning ε j = (2 : ℝ) ^ n := by
  have h1 : ∀ ε : Fin n → Bool, realSigning ε j * realSigning ε j = 1 := by
    intro ε
    cases h : ε j <;> simp [realSigning, h]
  rw [Finset.sum_congr rfl (fun ε _ => h1 ε), Finset.sum_const, nsmul_eq_mul,
    mul_one]
  have hcard : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [hcard]
  simp

/-- Off-diagonal sign correlations vanish: the coordinate-`k` flip pairs each
`ε` with a vector contributing the negative term, so the sum is its own
negation. -/
theorem sign_cross_sum {n : ℕ} {j k : Fin n} (hjk : j ≠ k) :
    ∑ ε : Fin n → Bool, realSigning ε j * realSigning ε k = 0 := by
  have hcomp := Equiv.sum_comp ((flipAt_involutive k).toPerm (flipAt k))
    (fun ε => realSigning ε j * realSigning ε k)
  have hterm : ∀ ε : Fin n → Bool,
      realSigning (((flipAt_involutive k).toPerm (flipAt k)) ε) j *
          realSigning (((flipAt_involutive k).toPerm (flipAt k)) ε) k =
        -(realSigning ε j * realSigning ε k) := by
    intro ε
    simp only [Function.Involutive.coe_toPerm]
    rw [realSigning_flipAt_of_ne hjk, realSigning_flipAt_self]
    ring
  have hsum : (∑ ε : Fin n → Bool, realSigning ε j * realSigning ε k) =
      ∑ ε : Fin n → Bool, -(realSigning ε j * realSigning ε k) := by
    conv_lhs => rw [← hcomp]
    exact Finset.sum_congr rfl fun ε _ => hterm ε
  rw [Finset.sum_neg_distrib] at hsum
  linarith

/-- Sign correlation tensor: `2^n` on the diagonal, `0` off the diagonal. -/
theorem sign_product_sum {n : ℕ} (j k : Fin n) :
    ∑ ε : Fin n → Bool, realSigning ε j * realSigning ε k =
      if j = k then (2 : ℝ) ^ n else 0 := by
  by_cases h : j = k
  · subst h
    rw [ite_eq_left rfl]
    exact sign_self_sum j
  · rw [ite_eq_right h]
    exact sign_cross_sum h

/-- The second-moment identity, unnormalized: expanding the square and summing
over all `2^n` signings kills the `j ≠ k` cross terms. -/
theorem sum_sign_rowValue_sq {m n : ℕ} (A : Input m n) (i : Fin m) :
    ∑ ε : Fin n → Bool, (rowValue A (realSigning ε) i) ^ 2 =
      (2 : ℝ) ^ n * ∑ j, (A i j) ^ 2 := by
  have hexpand : ∀ ε : Fin n → Bool, (rowValue A (realSigning ε) i) ^ 2 =
      ∑ j : Fin n, ∑ k : Fin n,
        (A i j * A i k) * (realSigning ε j * realSigning ε k) := by
    intro ε
    unfold rowValue
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    ∑ ε : Fin n → Bool, (rowValue A (realSigning ε) i) ^ 2
      = ∑ ε : Fin n → Bool, ∑ j : Fin n, ∑ k : Fin n,
          (A i j * A i k) * (realSigning ε j * realSigning ε k) :=
        Finset.sum_congr rfl fun ε _ => hexpand ε
    _ = ∑ j : Fin n, ∑ ε : Fin n → Bool, ∑ k : Fin n,
          (A i j * A i k) * (realSigning ε j * realSigning ε k) :=
        Finset.sum_comm
    _ = ∑ j : Fin n, ∑ k : Fin n, ∑ ε : Fin n → Bool,
          (A i j * A i k) * (realSigning ε j * realSigning ε k) := by
        apply Finset.sum_congr rfl
        intro j _
        exact Finset.sum_comm
    _ = ∑ j : Fin n, ∑ k : Fin n, (A i j * A i k) *
          ∑ ε : Fin n → Bool, realSigning ε j * realSigning ε k := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
    _ = ∑ j : Fin n, ∑ k : Fin n,
          (A i j * A i k) * (if j = k then (2 : ℝ) ^ n else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        rw [sign_product_sum]
    _ = ∑ j : Fin n, A i j * A i j * (2 : ℝ) ^ n := by
        apply Finset.sum_congr rfl
        intro j _
        have hite : ∀ k : Fin n,
            (A i j * A i k) * (if j = k then (2 : ℝ) ^ n else 0) =
              if j = k then A i j * A i k * (2 : ℝ) ^ n else 0 := fun k => by
          rw [mul_ite, mul_zero]
        rw [Finset.sum_congr rfl fun k _ => hite k, Finset.sum_ite_eq,
          ite_eq_left (Finset.mem_univ j)]
    _ = (2 : ℝ) ^ n * ∑ j : Fin n, (A i j) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring

/-- **Second-moment identity** (the substantive core): for uniform random
signs, `E[(row_i ε)²] = ∑ j, (A i j)²`. This is the Gaussian-free concentration
ingredient for a single trial. -/
theorem signAvg_rowValue_sq {m n : ℕ} (A : Input m n) (i : Fin m) :
    signAvg (fun ε => (rowValue A (realSigning ε) i) ^ 2) = ∑ j, (A i j) ^ 2 := by
  rw [signAvg, sum_sign_rowValue_sq, mul_comm ((2 : ℝ) ^ n), mul_div_assoc,
    div_self (two_pow_ne_zero n), mul_one]

/-- Summing the moment identity over all rows. -/
theorem signAvg_sum_rowValue_sq {m n : ℕ} (A : Input m n) :
    signAvg (fun ε => ∑ i, (rowValue A (realSigning ε) i) ^ 2) =
      ∑ i, ∑ j, (A i j) ^ 2 := by
  have h : ∑ ε : Fin n → Bool, ∑ i, (rowValue A (realSigning ε) i) ^ 2 =
      (2 : ℝ) ^ n * ∑ i, ∑ j, (A i j) ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact sum_sign_rowValue_sq A i
  rw [signAvg, h, mul_comm ((2 : ℝ) ^ n), mul_div_assoc,
    div_self (two_pow_ne_zero n), mul_one]

/-- For a column-normalized matrix, the expected squared discrepancy
`∑ i (row_i ε)²` is at most `n`. -/
theorem signAvg_sum_rowValue_sq_le {m n : ℕ} {A : Input m n}
    (hA : ColumnNormalized A) :
    signAvg (fun ε => ∑ i, (rowValue A (realSigning ε) i) ^ 2) ≤ (n : ℝ) := by
  rw [signAvg_sum_rowValue_sq]
  exact total_mass_le_dimension hA

/-- Generic Markov-type counting: `T²` times the number of indices with
`|v a| ≥ T` is at most `∑ v²`. -/
theorem sq_mul_filter_card_le_sum_sq {ι : Type*} [Fintype ι] (v : ι → ℝ)
    {T : ℝ} (hT : 0 ≤ T) :
    T ^ 2 * ((Finset.univ.filter fun a => T ≤ |v a|).card : ℝ) ≤
      ∑ a, (v a) ^ 2 := by
  have hs : ∀ a ∈ Finset.univ.filter (fun a => T ≤ |v a|),
      T ^ 2 ≤ (v a) ^ 2 := by
    intro a ha
    have habs : T ≤ |v a| := (Finset.mem_filter.mp ha).2
    have hnn : 0 ≤ |v a| := abs_nonneg _
    have hsq := sq_abs (v a)
    nlinarith
  calc
    T ^ 2 * ((Finset.univ.filter fun a => T ≤ |v a|).card : ℝ)
      = ∑ a ∈ Finset.univ.filter (fun a => T ≤ |v a|), T ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ a ∈ Finset.univ.filter (fun a => T ≤ |v a|), (v a) ^ 2 :=
        Finset.sum_le_sum hs
    _ ≤ ∑ a, (v a) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun a _ _ => sq_nonneg _

/-- The number of rows of `A` on which the signed value `x` reaches `T`,
as a real number. -/
noncomputable def badRowCount {m n : ℕ} (A : Input m n) (T : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ((Finset.univ.filter fun i => T ≤ |rowValue A x i|).card : ℝ)

/-- Pointwise Markov bound on the bad-row count of a signing. -/
theorem sq_mul_badRowCount_le {m n : ℕ} (A : Input m n) {T : ℝ} (hT : 0 ≤ T)
    (x : Fin n → ℝ) :
    T ^ 2 * badRowCount A T x ≤ ∑ i, (rowValue A x i) ^ 2 :=
  sq_mul_filter_card_le_sum_sq _ hT

/-- The total bad-row count over all `2^n` signings is at most
`2^n · (n / T²)`. -/
theorem sum_badRowCount_le {m n : ℕ} {A : Input m n} (hA : ColumnNormalized A)
    {T : ℝ} (hT : 0 < T) :
    ∑ ε : Fin n → Bool, badRowCount A T (realSigning ε) ≤
      (2 : ℝ) ^ n * ((n : ℝ) / T ^ 2) := by
  have h2 : (0 : ℝ) < T ^ 2 := sq_pos_of_pos hT
  have key : T ^ 2 * ∑ ε : Fin n → Bool, badRowCount A T (realSigning ε) ≤
      (2 : ℝ) ^ n * (n : ℝ) := by
    calc
      T ^ 2 * ∑ ε : Fin n → Bool, badRowCount A T (realSigning ε)
        = ∑ ε : Fin n → Bool,
            T ^ 2 * badRowCount A T (realSigning ε) :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ ε : Fin n → Bool, ∑ i, (rowValue A (realSigning ε) i) ^ 2 :=
          Finset.sum_le_sum fun ε _ =>
            sq_mul_badRowCount_le A hT.le (realSigning ε)
      _ = (2 : ℝ) ^ n * ∑ i, ∑ j, (A i j) ^ 2 := by
          rw [Finset.sum_comm, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          exact sum_sign_rowValue_sq A i
      _ ≤ (2 : ℝ) ^ n * (n : ℝ) :=
          mul_le_mul_of_nonneg_left (total_mass_le_dimension hA)
            (pow_nonneg (by norm_num) _)
  calc
    ∑ ε : Fin n → Bool, badRowCount A T (realSigning ε)
      ≤ (2 : ℝ) ^ n * (n : ℝ) / T ^ 2 := by
        apply (le_div_iff₀ h2).mpr
        linarith [key]
    _ = (2 : ℝ) ^ n * ((n : ℝ) / T ^ 2) := by rw [mul_div_assoc]

/-- **Average Markov bound**: for uniform random signs, the expected number of
rows with `|row_i ε| ≥ T` is at most `n / T²`. -/
theorem signAvg_badRowCount_le {m n : ℕ} {A : Input m n} (hA : ColumnNormalized A)
    {T : ℝ} (hT : 0 < T) :
    signAvg (fun ε => badRowCount A T (realSigning ε)) ≤ (n : ℝ) / T ^ 2 := by
  have hsum := sum_badRowCount_le hA hT
  rw [signAvg,
    div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)]
  linarith [hsum]

/-- **Existence of a good signing** (the per-trial success guarantee in this
model): some sign vector has at most `n / T²` rows with `|row_i ε| ≥ T`.
Obtained by pigeonhole: the minimum over `ε` is at most the average. -/
theorem exists_signing_few_bad_rows {m n : ℕ} {A : Input m n}
    (hA : ColumnNormalized A) {T : ℝ} (hT : 0 < T) :
    ∃ ε : Fin n → Bool, badRowCount A T (realSigning ε) ≤ (n : ℝ) / T ^ 2 := by
  have hsum := sum_badRowCount_le hA hT
  have hconst : ∑ _ε : Fin n → Bool, (n : ℝ) / T ^ 2 =
      (2 : ℝ) ^ n * ((n : ℝ) / T ^ 2) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [← hconst] at hsum
  obtain ⟨ε, _, hε⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨ε, hε⟩

/-- **Single-row tail bound** (Markov on the second moment): the fraction of
signings with `|row_i ε| ≥ T` is at most `(∑ j (A i j)²) / T²`. -/
theorem row_tail_fraction_le {m n : ℕ} (A : Input m n) (i : Fin m) {T : ℝ}
    (hT : 0 < T) :
    signAvg
        (fun ε => if T ≤ |rowValue A (realSigning ε) i| then (1 : ℝ) else 0) ≤
      (∑ j, (A i j) ^ 2) / T ^ 2 := by
  have h2 : (0 : ℝ) < T ^ 2 := sq_pos_of_pos hT
  have hcard : ∑ ε : Fin n → Bool,
      (if T ≤ |rowValue A (realSigning ε) i| then (1 : ℝ) else 0) =
        ((Finset.univ.filter fun ε : Fin n → Bool =>
          T ≤ |rowValue A (realSigning ε) i|).card : ℝ) :=
    Finset.sum_boole _ _
  have hcount : T ^ 2 *
      ((Finset.univ.filter fun ε : Fin n → Bool =>
          T ≤ |rowValue A (realSigning ε) i|).card : ℝ) ≤
        (2 : ℝ) ^ n * ∑ j, (A i j) ^ 2 := by
    calc
      T ^ 2 * ((Finset.univ.filter fun ε : Fin n → Bool =>
            T ≤ |rowValue A (realSigning ε) i|).card : ℝ)
        ≤ ∑ ε : Fin n → Bool, (rowValue A (realSigning ε) i) ^ 2 :=
          sq_mul_filter_card_le_sum_sq _ hT.le
      _ = (2 : ℝ) ^ n * ∑ j, (A i j) ^ 2 := sum_sign_rowValue_sq A i
  have hle : ((Finset.univ.filter fun ε : Fin n → Bool =>
        T ≤ |rowValue A (realSigning ε) i|).card : ℝ) ≤
      (2 : ℝ) ^ n * (∑ j, (A i j) ^ 2) / T ^ 2 := by
    apply (le_div_iff₀ h2).mpr
    linarith [hcount]
  rw [signAvg, hcard, div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)]
  exact hle.trans_eq (by ring)

/-! ### Conditional sampler theorem

The following theorem is the *conditional* form of the trial guarantee: it
takes an arbitrary finite sampler (weights `w ε ≥ 0` of positive total mass)
and assumes only a bound on its weighted second moment. Gaussian marginal
assumptions, adaptive conditional densities, and the paper's Lemma D.1 are
*not* available in this finite model — they enter only through the explicitly
stated hypothesis `hmoment`. -/

/-- **Conditional success of a trial**: for any finite sampler `w` with
nonnegative weights of positive total mass, if the weighted sum of squared row
values is at most `D`, then some sign vector in the support of `w` has at most
`D / (T² · ∑ w)` bad rows. Instantiating `w` with the uniform weight `2^{-n}`
recovers `exists_signing_few_bad_rows`. -/
theorem exists_in_support_few_bad_rows {m n : ℕ} (A : Input m n)
    (w : (Fin n → Bool) → ℝ) (hw : ∀ ε, 0 ≤ w ε) {D : ℝ}
    (hmoment :
      ∑ ε : Fin n → Bool, w ε * ∑ i, (rowValue A (realSigning ε) i) ^ 2 ≤ D)
    {T : ℝ} (hT : 0 < T) (htotal : 0 < ∑ ε : Fin n → Bool, w ε) :
    ∃ ε : Fin n → Bool, 0 < w ε ∧ badRowCount A T (realSigning ε) ≤
      D / (T ^ 2 * ∑ ε : Fin n → Bool, w ε) := by
  set S : Finset (Fin n → Bool) := Finset.univ.filter fun ε => 0 < w ε with hS
  have hsumW : ∑ ε ∈ S, w ε = ∑ ε : Fin n → Bool, w ε := by
    rw [hS, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ε _
    rcases lt_or_eq_of_le (hw ε) with hlt | h0
    · simp [hlt]
    · have h0' : w ε = 0 := h0.symm
      simp [h0']
  have hW : 0 < ∑ ε ∈ S, w ε := by
    rw [hsumW]
    exact htotal
  have hne : S.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hW
    simp at hW
  have hsupp : ∑ ε : Fin n → Bool, w ε * badRowCount A T (realSigning ε) =
      ∑ ε ∈ S, w ε * badRowCount A T (realSigning ε) := by
    rw [hS, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ε _
    rcases lt_or_eq_of_le (hw ε) with hlt | h0
    · simp [hlt]
    · have h0' : w ε = 0 := h0.symm
      simp [h0']
  have hle : ∑ ε : Fin n → Bool, w ε * badRowCount A T (realSigning ε) ≤
      D / T ^ 2 := by
    have hper : ∀ ε : Fin n → Bool,
        w ε * (T ^ 2 * badRowCount A T (realSigning ε)) ≤
          w ε * ∑ i, (rowValue A (realSigning ε) i) ^ 2 :=
      fun ε =>
        mul_le_mul_of_nonneg_left
          (sq_mul_badRowCount_le A hT.le (realSigning ε)) (hw ε)
    have hsum : ∑ ε : Fin n → Bool,
        w ε * (T ^ 2 * badRowCount A T (realSigning ε)) ≤ D :=
      (Finset.sum_le_sum fun ε _ => hper ε).trans hmoment
    have hexp : ∀ ε : Fin n → Bool,
        w ε * (T ^ 2 * badRowCount A T (realSigning ε)) =
          T ^ 2 * (w ε * badRowCount A T (realSigning ε)) := fun ε => by ring
    have hsum2 :
        T ^ 2 * ∑ ε : Fin n → Bool,
            w ε * badRowCount A T (realSigning ε) ≤ D := by
      have hconv : ∑ ε : Fin n → Bool,
            w ε * (T ^ 2 * badRowCount A T (realSigning ε)) =
          ∑ ε : Fin n → Bool,
            T ^ 2 * (w ε * badRowCount A T (realSigning ε)) :=
        Finset.sum_congr rfl fun ε _ => hexp ε
      rw [hconv, ← Finset.mul_sum] at hsum
      exact hsum
    apply (le_div_iff₀ (sq_pos_of_pos hT)).mpr
    linarith [hsum2]
  have hconst : ∑ ε ∈ S,
      w ε * (D / (T ^ 2 * ∑ ε ∈ S, w ε)) = D / T ^ 2 := by
    rw [← Finset.sum_mul]
    have hW' : (∑ ε ∈ S, w ε) ≠ 0 := ne_of_gt hW
    have hT' : T ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hT)
    rw [← mul_div_assoc, mul_comm (∑ ε ∈ S, w ε) D,
      mul_div_mul_right _ _ hW']
  have hsum_le : ∑ ε ∈ S, w ε * badRowCount A T (realSigning ε) ≤
      ∑ ε ∈ S, w ε * (D / (T ^ 2 * ∑ ε ∈ S, w ε)) := by
    rwa [← hsupp, hconst]
  obtain ⟨ε, hεmem, hεle⟩ := Finset.exists_le_of_sum_le hne hsum_le
  have hpos : 0 < w ε := by
    have hmem : ε ∈ Finset.univ.filter (fun ε' => 0 < w ε') := hS ▸ hεmem
    exact (Finset.mem_filter.mp hmem).2
  have hbc : badRowCount A T (realSigning ε) ≤
      D / (T ^ 2 * ∑ ε ∈ S, w ε) := le_of_mul_le_mul_left hεle hpos
  rw [hsumW] at hbc
  exact ⟨ε, hpos, hbc⟩

/-! ### The cube walk: connecting the uniform model to `SymmetricWalk` -/

/-- Assign coordinates `0, …, k-1` of `x` from the sign vector `ε : Fin k → Bool`;
coordinates `≥ k` keep their `x` values. -/
def assignVec {n k : ℕ} (x : Fin n → ℝ) (ε : Fin k → Bool) : Fin n → ℝ :=
  fun c => if h : c.val < k then (if ε ⟨c.val, h⟩ then 1 else -1) else x c

theorem assignVec_lt {n k : ℕ} (x : Fin n → ℝ) (ε : Fin k → Bool) (c : Fin n)
    (h : c.val < k) :
    assignVec x ε c = if ε ⟨c.val, h⟩ then (1 : ℝ) else -1 :=
  dite_eq_left h

theorem assignVec_ge {n k : ℕ} (x : Fin n → ℝ) (ε : Fin k → Bool) (c : Fin n)
    (h : ¬c.val < k) : assignVec x ε c = x c :=
  dite_eq_right h

/-- For the full assignment `k = n`, `assignVec` is exactly `realSigning`. -/
theorem assignVec_eq_realSigning {n : ℕ} (x : Fin n → ℝ) (ε : Fin n → Bool) :
    assignVec x ε = realSigning ε := by
  funext c
  unfold assignVec realSigning
  rw [dite_eq_left c.isLt]

/-- Snoc-step: assigning the first `k` coordinates by `η` after setting
coordinate `k` to `±1` equals assigning all `k + 1` coordinates by
`Fin.snoc η b`. -/
theorem assignVec_snoc {n k : ℕ} (hkn : k < n) (x : Fin n → ℝ) (b : Bool)
    (η : Fin k → Bool) :
    assignVec (Function.update x ⟨k, hkn⟩ (if b then (1 : ℝ) else -1)) η =
      assignVec x (Fin.snoc η b) := by
  funext c
  unfold assignVec
  by_cases hc : c.val < k
  · have hc' : c.val < k + 1 := lt_trans hc (Nat.lt_succ_self k)
    rw [dite_eq_left hc, dite_eq_left hc']
    congr 1
    have hcast : (⟨c.val, hc'⟩ : Fin (k + 1)) = (⟨c.val, hc⟩ : Fin k).castSucc :=
      Fin.ext_iff.mpr rfl
    rw [hcast, Fin.snoc_castSucc]
  · by_cases hc' : c.val < k + 1
    · have hck : c.val = k := by omega
      have hlast : (⟨c.val, hc'⟩ : Fin (k + 1)) = Fin.last k :=
        Fin.ext_iff.mpr hck
      have hupd : Function.update x ⟨k, hkn⟩ (if b then (1 : ℝ) else -1) c =
          (if b then (1 : ℝ) else -1) := by
        have hcj : c = ⟨k, hkn⟩ := Fin.ext_iff.mpr hck
        conv_lhs => rw [hcj]
        exact Function.update_self _ _ _
      rw [dite_eq_right hc, dite_eq_left hc', hlast, Fin.snoc_last, hupd]
    · rw [dite_eq_right hc, dite_eq_right hc']
      have hcj : c ≠ ⟨k, hkn⟩ := by
        intro he
        subst he
        exact absurd (Nat.lt_succ_self k) hc'
      rw [Function.update_of_ne hcj]

namespace SymmetricWalk

/-- `y` is a leaf position reached by the symmetric walk `t`. -/
inductive MemLeaf {n : ℕ} : SymmetricWalk n → (Fin n → ℝ) → Prop
  | leaf (x : Fin n → ℝ) : MemLeaf (.leaf x) x
  | left {x d : Fin n → ℝ} {l r : SymmetricWalk n} {y : Fin n → ℝ}
      (h : MemLeaf l y) : MemLeaf (.branch x d l r) y
  | right {x d : Fin n → ℝ} {l r : SymmetricWalk n} {y : Fin n → ℝ}
      (h : MemLeaf r y) : MemLeaf (.branch x d l r) y

/-- The minimum leaf value is at most the leaf-uniform average. -/
theorem exists_memLeaf_terminalAverage_le {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (t : SymmetricWalk n) :
    ∃ y, MemLeaf t y ∧ f y ≤ terminalAverage f t := by
  induction t with
  | leaf x => exact ⟨x, .leaf x, le_rfl⟩
  | branch x d l r ihl ihr =>
    simp only [terminalAverage]
    rcases le_total (terminalAverage f l) (terminalAverage f r) with h | h
    · obtain ⟨y, hy, hf⟩ := ihl
      exact ⟨y, .left hy, by linarith⟩
    · obtain ⟨y, hy, hf⟩ := ihr
      exact ⟨y, .right hy, by linarith⟩

/-- The full-depth cube walk: at level `k + 1` the walk branches by flipping
coordinate `⟨k, h⟩`; after `k` steps the first `k` coordinates are `±1`. The
`else` branch is unreachable whenever `k + 1 ≤ n` and exists only to keep the
definition total. -/
def cubeDown {n : ℕ} : ℕ → (Fin n → ℝ) → SymmetricWalk n
  | 0, x => .leaf x
  | k + 1, x =>
      if h : k < n then
        .branch x (Function.update (fun _ => (0 : ℝ)) ⟨k, h⟩ 1)
          (cubeDown k (Function.update x ⟨k, h⟩ 1))
          (cubeDown k (Function.update x ⟨k, h⟩ (-1)))
      else .leaf x

theorem cubeDown_zero {n : ℕ} (x : Fin n → ℝ) : cubeDown 0 x = .leaf x := rfl

theorem cubeDown_succ {n : ℕ} {k : ℕ} (hkn : k < n) (x : Fin n → ℝ) :
    cubeDown (k + 1) x =
      .branch x (Function.update (fun _ => (0 : ℝ)) ⟨k, hkn⟩ 1)
        (cubeDown k (Function.update x ⟨k, hkn⟩ 1))
        (cubeDown k (Function.update x ⟨k, hkn⟩ (-1))) :=
  dite_eq_left hkn

theorem cubeDown_leaf {n : ℕ} {k : ℕ} (hkn : ¬k < n) (x : Fin n → ℝ) :
    cubeDown (k + 1) x = .leaf x :=
  dite_eq_right hkn

/-- The root of `cubeDown k x` is always `x`. -/
theorem root_cubeDown {n : ℕ} : ∀ (k : ℕ) (x : Fin n → ℝ),
    root (cubeDown k x) = x
  | 0, _ => rfl
  | k + 1, x => by
    by_cases hkn : k < n
    · rw [cubeDown_succ hkn]
      rfl
    · rw [cubeDown_leaf hkn]
      rfl

/-- Every leaf of `cubeDown k x` has `±1` in all coordinates `< k` (already
assigned by the walk) and agrees with `x` in coordinates `≥ k` (not yet
touched). -/
theorem memLeaf_cubeDown {n : ℕ} :
    ∀ (k : ℕ), k ≤ n → ∀ (x y : Fin n → ℝ), MemLeaf (cubeDown k x) y →
      (∀ c : Fin n, c.val < k → |y c| = 1) ∧
        (∀ c : Fin n, k ≤ c.val → y c = x c) := by
  intro k
  induction k with
  | zero =>
    intro _ x y h
    rw [cubeDown_zero] at h
    cases h
    exact ⟨fun c hc => absurd hc (Nat.not_lt_zero _), fun _ _ => rfl⟩
  | succ k ih =>
    intro hk x y h
    have hkn : k < n := Nat.lt_of_succ_le hk
    rw [cubeDown_succ hkn] at h
    have hjval : (⟨k, hkn⟩ : Fin n).val = k := rfl
    have finish : ∀ v : ℝ, |v| = 1 →
        MemLeaf (cubeDown k (Function.update x ⟨k, hkn⟩ v)) y →
        (∀ c : Fin n, c.val < k + 1 → |y c| = 1) ∧
          (∀ c : Fin n, k + 1 ≤ c.val → y c = x c) := by
      intro v hv hy
      obtain ⟨hlt, hge⟩ := ih (Nat.le_of_succ_le hk) _ _ hy
      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
      · by_cases hck : c.val < k
        · exact hlt c hck
        · have heq : c.val = k := by omega
          have hupd : Function.update x ⟨k, hkn⟩ v c = v := by
            have hcj : c = ⟨k, hkn⟩ := Fin.ext_iff.mpr heq
            conv_lhs => rw [hcj]
            exact Function.update_self _ _ _
          have hyv : y c = v := (hge c (by omega)).trans hupd
          rw [hyv, hv]
      · have hcj : c ≠ ⟨k, hkn⟩ := by
          intro he
          rw [he] at hc
          rw [hjval] at hc
          omega
        have hyx : y c = (Function.update x ⟨k, hkn⟩ v) c := hge c (by omega)
        rwa [Function.update_of_ne hcj] at hyx
    cases h with
    | left hl => exact finish 1 (by norm_num) hl
    | right hr => exact finish (-1) (by norm_num) hr

/-- Every leaf of the full cube walk `cubeDown n x` is a signing. -/
theorem memLeaf_cubeDown_isSigning {n : ℕ} {x y : Fin n → ℝ}
    (h : MemLeaf (cubeDown n x) y) : IsSigning y := by
  intro j
  have h1 := (memLeaf_cubeDown n le_rfl x y h).1 j j.isLt
  rcases abs_choice (y j) with habs | habs
  · right
    rw [← habs]
    exact h1
  · left
    rw [habs] at h1
    linarith

/-- `cubeDown k x` is coherent (children are `x ± d`) provided all coordinates
`< k` of the starting vector `x` are still zero. -/
theorem cubeDown_coherent {n : ℕ} :
    ∀ (k : ℕ), k ≤ n → ∀ (x : Fin n → ℝ),
      (∀ c : Fin n, c.val < k → x c = 0) → Coherent (cubeDown k x) := by
  intro k
  induction k with
  | zero =>
    intro _ x _
    rw [cubeDown_zero]
    trivial
  | succ k ih =>
    intro hk x hx
    have hkn : k < n := Nat.lt_of_succ_le hk
    have hjval : (⟨k, hkn⟩ : Fin n).val = k := rfl
    have hxk : x ⟨k, hkn⟩ = 0 := hx ⟨k, hkn⟩ (Nat.lt_succ_self k)
    rw [cubeDown_succ hkn]
    have hinv : ∀ v : ℝ, ∀ c : Fin n, c.val < k →
        Function.update x ⟨k, hkn⟩ v c = 0 := by
      intro v c hc
      have hcj : c ≠ ⟨k, hkn⟩ := by
        intro he
        rw [he] at hc
        rw [hjval] at hc
        omega
      rw [Function.update_of_ne hcj]
      exact hx c (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [root_cubeDown]
      funext c
      by_cases hc : c = ⟨k, hkn⟩
      · subst hc
        simp [Function.update_self, hxk]
      · simp [Function.update_of_ne hc]
    · rw [root_cubeDown]
      funext c
      by_cases hc : c = ⟨k, hkn⟩
      · subst hc
        simp [Function.update_self, hxk]
      · simp [Function.update_of_ne hc]
    · exact ih (Nat.le_of_succ_le hk) _ (hinv 1)
    · exact ih (Nat.le_of_succ_le hk) _ (hinv (-1))

/-- `cubeDown k x` has cube leaves provided every coordinate of `x` is already
in `[-1, 1]`. -/
theorem cubeDown_cubeLeaves {n : ℕ} :
    ∀ (k : ℕ) (x : Fin n → ℝ), (∀ c : Fin n, |x c| ≤ 1) →
      CubeLeaves (cubeDown k x) := by
  intro k
  induction k with
  | zero =>
    intro x hx
    rw [cubeDown_zero]
    exact hx
  | succ k ih =>
    intro x hx
    by_cases hkn : k < n
    · have child : ∀ v : ℝ, |v| = 1 → ∀ c : Fin n,
          |Function.update x ⟨k, hkn⟩ v c| ≤ 1 := by
        intro v hv c
        by_cases hc : c = ⟨k, hkn⟩
        · subst hc
          rw [Function.update_self]
          exact hv.le
        · rw [Function.update_of_ne hc]
          exact hx c
      rw [cubeDown_succ hkn]
      exact ⟨ih _ (child 1 (by norm_num)), ih _ (child (-1) (by norm_num))⟩
    · rw [cubeDown_leaf hkn]
      exact hx

/-- **Leaf-uniform = sign-uniform**: the leaf-average of `f` over the cube
walk equals the uniform `Fin k → Bool` average of `f ∘ assignVec`. The proof
expands the `Fin (k+1) → Bool` sum by `Fin.snocEquiv` into the two subtrees. -/
theorem terminalAverage_cubeDown {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    ∀ (k : ℕ), k ≤ n → ∀ (x : Fin n → ℝ),
      terminalAverage f (cubeDown k x) =
        (∑ ε : Fin k → Bool, f (assignVec x ε)) / (2 : ℝ) ^ k := by
  intro k
  induction k with
  | zero =>
    intro _ x
    rw [cubeDown_zero]
    simp only [terminalAverage]
    have hassign : ∀ ε : Fin 0 → Bool, assignVec x ε = x := by
      intro ε
      funext c
      exact dite_eq_right (Nat.not_lt_zero _)
    have hconst : ∀ ε : Fin 0 → Bool, f (assignVec x ε) = f x :=
      fun ε => congrArg f (hassign ε)
    rw [Finset.sum_congr rfl fun ε _ => hconst ε, Finset.sum_const,
      Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      nsmul_eq_mul]
    norm_num
  | succ k ih =>
    intro hk x
    have hkn : k < n := Nat.lt_of_succ_le hk
    have hk' : k ≤ n := Nat.le_of_succ_le hk
    rw [cubeDown_succ hkn]
    simp only [terminalAverage]
    rw [ih hk' _, ih hk' _]
    have key1 : ∀ η : Fin k → Bool,
        f (assignVec (Function.update x ⟨k, hkn⟩ 1) η) =
          f (assignVec x (Fin.snoc η true)) := fun η =>
      congrArg f (assignVec_snoc hkn x true η)
    have key2 : ∀ η : Fin k → Bool,
        f (assignVec (Function.update x ⟨k, hkn⟩ (-1)) η) =
          f (assignVec x (Fin.snoc η false)) := fun η =>
      congrArg f (assignVec_snoc hkn x false η)
    rw [← add_div, div_div, ← pow_succ]
    congr 1
    rw [Finset.sum_congr rfl fun η _ => key1 η,
      Finset.sum_congr rfl fun η _ => key2 η]
    have hbool : (∑ η : Fin k → Bool, f (assignVec x (Fin.snoc η true))) +
        (∑ η : Fin k → Bool, f (assignVec x (Fin.snoc η false))) =
          ∑ b : Bool, ∑ η : Fin k → Bool, f (assignVec x (Fin.snoc η b)) := by
      have huniv : (Finset.univ : Finset Bool) = {true, false} := by decide
      rw [huniv, Finset.sum_pair (by decide : (true : Bool) ≠ false)]
    have hprod : (∑ b : Bool, ∑ η : Fin k → Bool,
          f (assignVec x (Fin.snoc η b))) =
        ∑ p : Bool × (Fin k → Bool), f (assignVec x (Fin.snoc p.2 p.1)) := by
      rw [Fintype.sum_prod_type]
    have heq : ∑ p : Bool × (Fin k → Bool), f (assignVec x (Fin.snoc p.2 p.1)) =
        ∑ ε : Fin (k + 1) → Bool, f (assignVec x ε) :=
      Equiv.sum_comp (Fin.snocEquiv fun _ => Bool) fun ε => f (assignVec x ε)
    rw [hbool, hprod, heq]

end SymmetricWalk

open SymmetricWalk in
/-- **The leaf-uniform average on the cube walk is the uniform sign model.**
This is the proved connection between the sampler model of this file and the
finite walk model of `Walk.lean`: no hypothesis is needed. -/
theorem terminalAverage_cubeTop {n : ℕ} (x : Fin n → ℝ)
    (f : (Fin n → ℝ) → ℝ) :
    SymmetricWalk.terminalAverage f (SymmetricWalk.cubeDown n x) =
      signAvg fun ε => f (realSigning ε) := by
  rw [SymmetricWalk.terminalAverage_cubeDown f n le_rfl x, signAvg]
  congr 1
  apply Finset.sum_congr rfl
  intro ε _
  rw [assignVec_eq_realSigning]

open SymmetricWalk in
/-- The full cube walk from the origin satisfies the `Coherent` invariant. -/
theorem cubeTop_coherent {n : ℕ} :
    SymmetricWalk.Coherent (SymmetricWalk.cubeDown n (0 : Fin n → ℝ)) :=
  SymmetricWalk.cubeDown_coherent n le_rfl _ fun c _ => by simp

open SymmetricWalk in
/-- The full cube walk from the origin has cube leaves. -/
theorem cubeTop_cubeLeaves {n : ℕ} :
    SymmetricWalk.CubeLeaves (SymmetricWalk.cubeDown n (0 : Fin n → ℝ)) :=
  SymmetricWalk.cubeDown_cubeLeaves n _ fun c => by simp

open SymmetricWalk in
/-- The leaf-uniform bad-row average over the cube walk is at most `n / T²`:
the walk-model form of `signAvg_badRowCount_le`. -/
theorem cubeTop_badRow_avg_le {m n : ℕ} {A : Input m n} (hA : ColumnNormalized A)
    {T : ℝ} (hT : 0 < T) :
    SymmetricWalk.terminalAverage (badRowCount A T)
        (SymmetricWalk.cubeDown n (0 : Fin n → ℝ)) ≤ (n : ℝ) / T ^ 2 := by
  rw [terminalAverage_cubeTop]
  exact signAvg_badRowCount_le hA hT

open SymmetricWalk in
/-- **Successful trial inside the walk model**: some leaf of the full cube
walk is a signing with at most `n / T²` bad rows. -/
theorem exists_memLeaf_signing_few_bad_rows {m n : ℕ} {A : Input m n}
    (hA : ColumnNormalized A) {T : ℝ} (hT : 0 < T) :
    ∃ y, SymmetricWalk.MemLeaf (SymmetricWalk.cubeDown n (0 : Fin n → ℝ)) y ∧
      IsSigning y ∧ badRowCount A T y ≤ (n : ℝ) / T ^ 2 := by
  obtain ⟨y, hy, hfy⟩ := SymmetricWalk.exists_memLeaf_terminalAverage_le
    (badRowCount A T) (SymmetricWalk.cubeDown n (0 : Fin n → ℝ))
  exact ⟨y, hy, SymmetricWalk.memLeaf_cubeDown_isSigning hy,
    hfy.trans (cubeTop_badRow_avg_le hA hT)⟩

end Komlos
