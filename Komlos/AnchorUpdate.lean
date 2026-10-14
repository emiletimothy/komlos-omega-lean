import Komlos
import Mathlib.Data.Finset.Max

/-!
# Anchored per-row update (Algorithm 1, step 3)

This module formalizes the per-row **anchored cleanup** of Algorithm 1,
step 3, of "The Komlós Problem in Near Matrix-Multiplication Time"
(Anand–Chen).  The paper's specification is in §2.1–2.3 (row
representation Eq. (2.3), coefficient removal Eq. (2.6), deliberate
spread deletion Eq. (2.8), the spread invariant Eq. (2.9), retirement
Eqs. (2.10)–(2.11), and the rational scale rule Eqs. (2.13)–(2.14)).

## State

A row state `RowState n` consists of

* `c : ℝ` — the scalar offset;
* `b p : Fin n → ℝ` — moving coefficients and their masses,
  related by `p j = (b j)^2`;
* `q : ℝ` — remaining mass `q = ∑ j, p j`;
* `r : ℝ` — the rational scale, satisfying `q ≤ r^2 < γ^2 q`, `r ≤ Rmax`
  for medium rows (paper Eq. (2.13)).

The stored `p`/`q` are tracked coherently (`RowState.Coherent`).

## The update

`anchorUpdate x s qstar` performs, in order,

1. `transferFixed x s` — transfer every coefficient on a frozen
   (already signed, `|x j| = 1`) coordinate into the offset;
2. `spreadLoop x` — while `0 < q`, `q ≤ Rmax^2` and some entry has
   `(b j)^2 > q * spreadBound`, transfer that entry (well-founded on
   the count of nonzero coefficients);
3. classification by `RowClass`: `q = 0` completed, `0 < q ≤ qstar`
   retired (cf. `RowState.retire`, the paper's Eq. (2.11)), and the
   remaining rows are anchored — for medium anchored rows the scale is
   reset by `updateScale` (the paper's square-root-free rule).

## Invariants proved

* `q` nonincreasing and nonnegative through every phase
  (`anchorUpdate_q_le`, `anchorUpdate_q_nonneg`);
* each loop step deletes mass `> q/64` (`transfer_q_decrease`);
* on exit every noncompleted medium row is spread
  (`anchorUpdate_spread`, paper Eq. (2.9));
* `r` nonincreasing and `≤ Rmax` (`anchorUpdate_r_le`,
  `anchorUpdate_r_le_Rmax`), and the scale-window invariant
  (`anchorUpdate_scale_invariant`, `anchorUpdate_scale_window`);
* the affine identity `c + ∑ bⱼ xⱼ` is preserved exactly
  (`transfer_affine`, `transferFixed_affine`, `anchorUpdate_affine`);
* at exit exactly one of the three classes applies
  (`classify_trichotomy`, `anchorUpdate_classify_trichotomy`).
-/

namespace Komlos

open scoped BigOperators
open scoped Classical

/-! ## Constants (paper Eq. (2.7)) -/

/-- The spread constant `Ksp = 64`, stored as the fraction `1/Ksp`. -/
noncomputable def spreadBound : ℝ := 1 / 64

/-- Maximum scale `Rmax = 291/200`. -/
noncomputable def Rmax : ℝ := 291 / 200

/-- The large-row deposit weight `bdep = 3/625`. -/
noncomputable def bdep : ℝ := 3 / 625

/-- Scale slack `γ = 65/64`. -/
noncomputable def γ : ℝ := 65 / 64

theorem spreadBound_pos : 0 < spreadBound := by norm_num [spreadBound]

theorem spreadBound_lt_one : spreadBound < 1 := by norm_num [spreadBound]

theorem Rmax_pos : 0 < Rmax := by norm_num [Rmax]

theorem gamma_pos : 0 < γ := by norm_num [γ]

theorem gamma_gt_one : 1 < γ := by norm_num [γ]

theorem gamma_sq_gt_one : 1 < γ ^ 2 := by norm_num [γ]

theorem spreadBound_lt_gamma_sq : spreadBound < γ ^ 2 := by
  norm_num [spreadBound, γ]

/-! ## Coefficient bookkeeping -/

/-- Remaining mass of a coefficient vector `q = ∑ j, (b j)^2`
(paper Eq. (2.4)). -/
def rowMass {n : ℕ} (b : Fin n → ℝ) : ℝ := ∑ j, (b j) ^ 2

/-- The coefficient vector with entry `j` deleted: `b̃ⱼ ← 0`
(paper Eq. (2.6)). -/
def deleteCoefficient {n : ℕ} (b : Fin n → ℝ) (j : Fin n) : Fin n → ℝ :=
  Function.update b j 0

/-- Pointwise form of a deleted coefficient. -/
theorem deleteCoefficient_apply {n : ℕ} (b : Fin n → ℝ) (j k : Fin n) :
    deleteCoefficient b j k = if k = j then 0 else b k := by
  rw [deleteCoefficient, Function.update_apply]

/-- The amount transferred into the row offset when entry `j` is
removed: `bⱼ * xⱼ` (paper Eq. (2.6)). -/
def rowErrorChangeEntry {n : ℕ} (b x : Fin n → ℝ) (j : Fin n) : ℝ :=
  b j * x j

/-- The new offset after transferring entry `j`: `c + bⱼ xⱼ`. -/
def rowOffset {n : ℕ} (c : ℝ) (b x : Fin n → ℝ) (j : Fin n) : ℝ :=
  c + rowErrorChangeEntry b x j

/-- Coordinates already frozen at a sign, `|x j| = 1`. -/
noncomputable def frozenCoefficients {n : ℕ} (x : Fin n → ℝ) :
    Finset (Fin n) :=
  Finset.univ.filter fun j => |x j| = 1

/-- The support (nonzero entries) of a coefficient vector. -/
noncomputable def coeffSupport {n : ℕ} (b : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun j => b j ≠ 0

theorem mem_coeffSupport {n : ℕ} {b : Fin n → ℝ} {j : Fin n} :
    j ∈ coeffSupport b ↔ b j ≠ 0 := by
  simp [coeffSupport]

/-- Sum over a deleted coefficient vector equals the old sum minus the
deleted term. -/
theorem sum_deleteCoefficient {n : ℕ} (f : Fin n → ℝ) (j : Fin n) :
    (∑ k, deleteCoefficient f j k) = (∑ k, f k) - f j := by
  rw [show (fun k => deleteCoefficient f j k) = Function.update f j 0 from rfl,
    Finset.sum_update_of_mem (Finset.mem_univ j)]
  have h := Finset.add_sum_erase Finset.univ f (Finset.mem_univ j)
  rw [← Finset.sdiff_singleton_eq_erase] at h
  linarith

/-- Sum of products against a deleted coefficient vector. -/
theorem sum_deleteCoefficient_mul {n : ℕ} (f g : Fin n → ℝ) (j : Fin n) :
    (∑ k, deleteCoefficient f j k * g k) = (∑ k, f k * g k) - f j * g j := by
  have hfun : (fun k => deleteCoefficient f j k * g k) =
      Function.update (fun k => f k * g k) j 0 := by
    funext k
    by_cases hkj : k = j
    · subst hkj
      simp [deleteCoefficient]
    · simp only [deleteCoefficient, Function.update_of_ne hkj]
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ j)]
  have h := Finset.add_sum_erase Finset.univ (fun k => f k * g k)
    (Finset.mem_univ j)
  rw [← Finset.sdiff_singleton_eq_erase] at h
  linarith

/-- Sum of squares of a deleted coefficient vector. -/
theorem sum_deleteCoefficient_sq {n : ℕ} (f : Fin n → ℝ) (j : Fin n) :
    (∑ k, (deleteCoefficient f j k) ^ 2) = (∑ k, (f k) ^ 2) - (f j) ^ 2 := by
  have hfun : (fun k => (deleteCoefficient f j k) ^ 2) =
      deleteCoefficient (fun k => (f k) ^ 2) j := by
    funext k
    by_cases hkj : k = j
    · subst hkj
      simp [deleteCoefficient]
    · simp only [deleteCoefficient, Function.update_of_ne hkj]
  rw [hfun, sum_deleteCoefficient]

/-- `if`-zeroed sums telescope against filtered sums. -/
theorem sum_ite_zero {n : ℕ} (F : Finset (Fin n)) (g : Fin n → ℝ) :
    (∑ j, (if j ∈ F then (0 : ℝ) else g j)) = (∑ j, g j) - ∑ j ∈ F, g j := by
  have h1 : (∑ j, (if j ∈ F then (0 : ℝ) else g j)) =
      ∑ j, (if j ∉ F then g j else 0) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ F <;> simp [hj]
  rw [h1, ← Finset.sum_filter]
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ F) g
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter] at hsplit
  linarith

/-- Deleting a coefficient can only shrink the support. -/
theorem coeffSupport_deleteCoefficient_subset {n : ℕ} (b : Fin n → ℝ)
    (j : Fin n) : coeffSupport (deleteCoefficient b j) ⊆ coeffSupport b := by
  intro k hk
  rw [mem_coeffSupport] at hk ⊢
  rw [deleteCoefficient_apply] at hk
  split_ifs at hk with hkj
  · exact (hk rfl).elim
  · exact hk

/-- Deleting a *nonzero* coefficient strictly decreases the support
cardinality: the termination measure for the spread-deletion loop. -/
theorem coeffSupport_deleteCoefficient_lt {n : ℕ} {b : Fin n → ℝ} {j : Fin n}
    (hj : b j ≠ 0) :
    (coeffSupport (deleteCoefficient b j)).card < (coeffSupport b).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨coeffSupport_deleteCoefficient_subset b j, ?_⟩
  intro heq
  have hmem : j ∈ coeffSupport b := mem_coeffSupport.mpr hj
  rw [← heq, mem_coeffSupport, deleteCoefficient_apply] at hmem
  simp at hmem

/-! ## The row state -/

/-- Per-row state of the anchored update (paper §2.1, §4.1): the affine
representation `φᵢ(y) = c + bᵀy` with entry masses `pⱼ = bⱼ²`, remaining
mass `q = ∑ pⱼ`, and rational scale `r`. -/
structure RowState (n : ℕ) where
  /-- Offset `cᵢ` accumulating the fixed part of the row value. -/
  c : ℝ
  /-- Retained coefficients `bᵢ`. -/
  b : Fin n → ℝ
  /-- Entry masses `pᵢⱼ = bᵢⱼ²`. -/
  p : Fin n → ℝ
  /-- Remaining mass `qᵢ = ∑ pᵢⱼ`. -/
  q : ℝ
  /-- Rational scale `rᵢ` (paper Eq. (2.13)). -/
  r : ℝ

/-- The spread condition (paper Eq. (2.9)): every retained entry mass is
at most `q/64`. -/
def spreadCondition {n : ℕ} (q : ℝ) (p : Fin n → ℝ) : Prop :=
  ∀ j, p j ≤ q * spreadBound

/-- The scale window (paper Eq. (2.13)): `q ≤ r² < γ² q`. -/
def scaleWindow (q r : ℝ) : Prop := q ≤ r ^ 2 ∧ r ^ 2 < γ ^ 2 * q

/-- Scale invariant maintained across the whole update: either the
scale covers the remaining mass, or the row was never rescaled
(`r = Rmax`, e.g. large rows that carry deposits instead). -/
def scaleInvariant (q r : ℝ) : Prop := q ≤ r ^ 2 ∨ r = Rmax

/-- The scale invariant is preserved when `q` decreases and `r` is
fixed (this is why large rows, whose `r` stays at `Rmax`, acquire the
invariant the moment they become medium). -/
theorem scaleInvariant_of_le {q q' r : ℝ} (h : scaleInvariant q r)
    (h' : q' ≤ q) : scaleInvariant q' r := by
  rcases h with h | h
  · exact Or.inl (h'.trans h)
  · exact Or.inr h

namespace RowState

variable {n : ℕ}

/-- The stored `p` and `q` agree with `b` (paper Eq. (2.4)). -/
def Coherent (s : RowState n) : Prop :=
  (∀ j, s.p j = (s.b j) ^ 2) ∧ s.q = ∑ j, s.p j

theorem Coherent.q_eq_rowMass {s : RowState n} (hs : s.Coherent) :
    s.q = rowMass s.b := by
  rw [hs.2, rowMass]
  exact Finset.sum_congr rfl fun j _ => hs.1 j

theorem Coherent.p_nonneg {s : RowState n} (hs : s.Coherent) (j : Fin n) :
    0 ≤ s.p j := hs.1 j ▸ sq_nonneg _

theorem Coherent.q_nonneg {s : RowState n} (hs : s.Coherent) : 0 ≤ s.q := by
  rw [hs.2]
  exact Finset.sum_nonneg fun j _ => hs.p_nonneg j

theorem Coherent.entry_le_q {s : RowState n} (hs : s.Coherent) (j : Fin n) :
    (s.b j) ^ 2 ≤ s.q := by
  rw [← hs.1 j, hs.2]
  exact Finset.single_le_sum (fun k _ => hs.p_nonneg k) (Finset.mem_univ j)

/-- A coherent state with positive remaining mass has a nonzero
coefficient (used to show the scale update always applies to medium
anchored rows). -/
theorem Coherent.exists_coeff_ne_zero {s : RowState n} (hs : s.Coherent)
    (hq : 0 < s.q) : ∃ j, s.b j ≠ 0 := by
  by_contra hne
  simp only [ne_eq, not_exists, not_not] at hne
  have hsum : ∑ j, s.p j = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [hs.1 j, hne j]; norm_num
  rw [hs.2] at hq
  linarith

theorem Coherent.spread_iff {s : RowState n} (hs : s.Coherent)
    (h : ∀ j, ¬ (s.b j) ^ 2 > s.q * spreadBound) :
    spreadCondition s.q s.p := by
  intro j
  rw [hs.1 j]
  exact not_lt.mp (h j)

/-- The row satisfies the spread condition of paper Eq. (2.9). -/
def holdsSpreadCondition (s : RowState n) : Prop :=
  spreadCondition s.q s.p

/-! ### Single-entry transfer (paper Eq. (2.6)) -/

/-- Transfer of one entry into the offset: `c ← c + bⱼxⱼ`, `bⱼ ← 0`,
`q ← q − bⱼ²`; the scale is untouched. -/
def transfer (x : Fin n → ℝ) (s : RowState n) (j : Fin n) : RowState n where
  c := rowOffset s.c s.b x j
  b := deleteCoefficient s.b j
  p := deleteCoefficient s.p j
  q := s.q - (s.b j) ^ 2
  r := s.r

theorem transfer_r (x : Fin n → ℝ) (s : RowState n) (j : Fin n) :
    (transfer x s j).r = s.r := rfl

theorem transfer_q (x : Fin n → ℝ) (s : RowState n) (j : Fin n) :
    (transfer x s j).q = s.q - (s.b j) ^ 2 := rfl

/-- The remaining mass is nonincreasing under a transfer. -/
theorem transfer_q_le (x : Fin n → ℝ) (s : RowState n) (j : Fin n) :
    (transfer x s j).q ≤ s.q :=
  sub_le_self _ (sq_nonneg _)

/-- A transfer keeps the remaining mass nonnegative. -/
theorem transfer_q_nonneg (x : Fin n → ℝ) (s : RowState n) (j : Fin n)
    (hs : s.Coherent) : 0 ≤ (transfer x s j).q :=
  sub_nonneg.mpr (hs.entry_le_q j)

/-- Each loop step removes more than `q/64` of mass: `q' < q − q/64`,
i.e. `q` decreases geometrically (`q' < (63/64) q`). -/
theorem transfer_q_decrease (x : Fin n → ℝ) (s : RowState n) (j : Fin n)
    (hj : s.q * spreadBound < (s.b j) ^ 2) :
    (transfer x s j).q < s.q - s.q * spreadBound := by
  show s.q - (s.b j) ^ 2 < s.q - s.q * spreadBound
  linarith [hj]

/-- The exact affine identity `c + ∑ bⱼ xⱼ` is preserved by a transfer
(paper Eq. (2.6): `dᵢ` does not jump at a deletion). -/
theorem transfer_affine (x : Fin n → ℝ) (s : RowState n) (j : Fin n) :
    affineValue (transfer x s j).c (transfer x s j).b x =
      affineValue s.c s.b x := by
  show s.c + s.b j * x j + ∑ k, deleteCoefficient s.b j k * x k =
      s.c + ∑ k, s.b k * x k
  rw [sum_deleteCoefficient_mul]
  ring

/-- Transfers preserve coherence `pⱼ = bⱼ²`, `q = ∑ pⱼ`. -/
theorem transfer_coherent (x : Fin n → ℝ) (s : RowState n) (j : Fin n)
    (hs : s.Coherent) : (transfer x s j).Coherent := by
  refine ⟨?_, ?_⟩
  · intro k
    show deleteCoefficient s.p j k = (deleteCoefficient s.b j k) ^ 2
    rw [deleteCoefficient_apply, deleteCoefficient_apply]
    by_cases hkj : k = j
    · simp [hkj]
    · simp [hkj, hs.1 k]
  · show s.q - (s.b j) ^ 2 = ∑ k, deleteCoefficient s.p j k
    rw [sum_deleteCoefficient, hs.1 j, hs.2]

/-! ### Frozen-column transfer -/

/-- Step 1 of the cleanup: transfer *all* coefficients on frozen
(already signed) columns into the offset (paper §2.2: "cleanup first
removes entries in frozen columns using (2.6)"). -/
noncomputable def transferFixed (x : Fin n → ℝ) (s : RowState n) :
    RowState n where
  c := s.c + ∑ j ∈ frozenCoefficients x, rowErrorChangeEntry s.b x j
  b := fun j => if j ∈ frozenCoefficients x then 0 else s.b j
  p := fun j => if j ∈ frozenCoefficients x then 0 else s.p j
  q := s.q - ∑ j ∈ frozenCoefficients x, (s.b j) ^ 2
  r := s.r

theorem transferFixed_r (x : Fin n → ℝ) (s : RowState n) :
    (transferFixed x s).r = s.r := rfl

theorem transferFixed_q_le (x : Fin n → ℝ) (s : RowState n) :
    (transferFixed x s).q ≤ s.q :=
  sub_le_self _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem transferFixed_q_nonneg (x : Fin n → ℝ) (s : RowState n)
    (hs : s.Coherent) : 0 ≤ (transferFixed x s).q := by
  show 0 ≤ s.q - ∑ j ∈ frozenCoefficients x, (s.b j) ^ 2
  rw [sub_nonneg]
  calc ∑ j ∈ frozenCoefficients x, (s.b j) ^ 2
      = ∑ j ∈ frozenCoefficients x, s.p j :=
        Finset.sum_congr rfl fun j _ => (hs.1 j).symm
    _ ≤ ∑ j, s.p j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun j _ _ => hs.p_nonneg j
    _ = s.q := hs.2.symm

/-- Frozen coefficients are all zeroed by the batch transfer. -/
theorem transferFixed_b_of_frozen (x : Fin n → ℝ) (s : RowState n) {j : Fin n}
    (hj : j ∈ frozenCoefficients x) : (transferFixed x s).b j = 0 := by
  have hb : (transferFixed x s).b j =
      if j ∈ frozenCoefficients x then (0 : ℝ) else s.b j := rfl
  rw [hb]
  simp [hj]

/-- The batch frozen transfer preserves the affine identity. -/
theorem transferFixed_affine (x : Fin n → ℝ) (s : RowState n) :
    affineValue (transferFixed x s).c (transferFixed x s).b x =
      affineValue s.c s.b x := by
  show s.c + (∑ j ∈ frozenCoefficients x, s.b j * x j) +
      (∑ j, (if j ∈ frozenCoefficients x then (0 : ℝ) else s.b j) * x j) =
        s.c + ∑ j, s.b j * x j
  have hpt : ∀ j, (if j ∈ frozenCoefficients x then (0 : ℝ) else s.b j) * x j =
      if j ∈ frozenCoefficients x then (0 : ℝ) else s.b j * x j := by
    intro j
    by_cases hj : j ∈ frozenCoefficients x <;> simp [hj]
  simp_rw [hpt, sum_ite_zero]
  ring

/-- The batch frozen transfer preserves coherence. -/
theorem transferFixed_coherent (x : Fin n → ℝ) (s : RowState n)
    (hs : s.Coherent) : (transferFixed x s).Coherent := by
  refine ⟨?_, ?_⟩
  · intro j
    show (if j ∈ frozenCoefficients x then (0 : ℝ) else s.p j) =
      (if j ∈ frozenCoefficients x then 0 else s.b j) ^ 2
    by_cases hj : j ∈ frozenCoefficients x
    · simp [hj]
    · simp [hj, hs.1 j]
  · show s.q - ∑ j ∈ frozenCoefficients x, (s.b j) ^ 2 =
      ∑ j, (if j ∈ frozenCoefficients x then (0 : ℝ) else s.p j)
    rw [sum_ite_zero, hs.2,
      Finset.sum_congr rfl fun j _ => (hs.1 j).symm]

/-- The support can only shrink under the batch frozen transfer. -/
theorem transferFixed_support_subset (x : Fin n → ℝ) (s : RowState n) :
    coeffSupport (transferFixed x s).b ⊆ coeffSupport s.b := by
  intro k hk
  rw [mem_coeffSupport] at hk ⊢
  intro hbk
  have hbf : (transferFixed x s).b k =
      if k ∈ frozenCoefficients x then (0 : ℝ) else s.b k := rfl
  rw [hbf, hbk] at hk
  simp at hk

/-! ### The spread-deletion loop (paper Eq. (2.8)) -/

/-- Step 2 of the cleanup: while the row is medium
(`0 < q ≤ Rmax²`, so large rows are exempt) and some entry mass exceeds
`q/64`, transfer such an entry.  Each iteration zeroes a *nonzero*
coefficient, so the cardinality of the support strictly decreases and
the recursion terminates. -/
noncomputable def spreadLoop (x : Fin n → ℝ) (s : RowState n) : RowState n :=
  if h : 0 < s.q ∧ s.q ≤ Rmax ^ 2 ∧ ∃ j, (s.b j) ^ 2 > s.q * spreadBound then
    spreadLoop x (s.transfer x (Classical.choose h.2.2))
  else s
termination_by (coeffSupport s.b).card
decreasing_by
  have hgt := Classical.choose_spec h.2.2
  have hbne : s.b (Classical.choose h.2.2) ≠ 0 := by
    intro hbz
    rw [hbz] at hgt
    have hpos := mul_pos h.1 spreadBound_pos
    nlinarith
  show (coeffSupport (deleteCoefficient s.b (Classical.choose h.2.2))).card <
    (coeffSupport s.b).card
  exact coeffSupport_deleteCoefficient_lt hbne

/-- The invariants of the spread-deletion loop, proved by well-founded
induction on the support. -/
theorem spreadLoop_spec (x : Fin n → ℝ) (s : RowState n) (hs : s.Coherent) :
    (spreadLoop x s).Coherent ∧
      (spreadLoop x s).q ≤ s.q ∧ 0 ≤ (spreadLoop x s).q ∧
      affineValue (spreadLoop x s).c (spreadLoop x s).b x =
        affineValue s.c s.b x ∧
      (spreadLoop x s).r = s.r ∧
      ¬ (0 < (spreadLoop x s).q ∧ (spreadLoop x s).q ≤ Rmax ^ 2 ∧
          ∃ j, ((spreadLoop x s).b j) ^ 2 > (spreadLoop x s).q * spreadBound) ∧
      coeffSupport (spreadLoop x s).b ⊆ coeffSupport s.b := by
  fun_induction spreadLoop x s with
  | case1 s h ih =>
      obtain ⟨hco, hle, hpos, haff, hr, hexit, hsupp⟩ :=
        ih (transfer_coherent x s _ hs)
      refine ⟨hco, hle.trans (transfer_q_le x s _), hpos,
        haff.trans (transfer_affine x s _), hr.trans (transfer_r x s _), hexit,
        hsupp.trans (coeffSupport_deleteCoefficient_subset _ _)⟩
  | case2 s h =>
      exact ⟨hs, le_rfl, hs.q_nonneg, rfl, rfl, h, subset_rfl⟩

theorem spreadLoop_coherent (x : Fin n → ℝ) (s : RowState n) (hs : s.Coherent) :
    (spreadLoop x s).Coherent := (spreadLoop_spec x s hs).1

theorem spreadLoop_q_le (x : Fin n → ℝ) (s : RowState n) (hs : s.Coherent) :
    (spreadLoop x s).q ≤ s.q := (spreadLoop_spec x s hs).2.1

theorem spreadLoop_q_nonneg (x : Fin n → ℝ) (s : RowState n) (hs : s.Coherent) :
    0 ≤ (spreadLoop x s).q := (spreadLoop_spec x s hs).2.2.1

theorem spreadLoop_affine (x : Fin n → ℝ) (s : RowState n) (hs : s.Coherent) :
    affineValue (spreadLoop x s).c (spreadLoop x s).b x =
      affineValue s.c s.b x := (spreadLoop_spec x s hs).2.2.2.1

theorem spreadLoop_r (x : Fin n → ℝ) (s : RowState n) (hs : s.Coherent) :
    (spreadLoop x s).r = s.r := (spreadLoop_spec x s hs).2.2.2.2.1

/-- At loop exit the guard fails; in particular every noncompleted
*medium* row satisfies the spread condition (paper Eq. (2.9)). -/
theorem spreadLoop_spread (x : Fin n → ℝ) (s : RowState n) (hs : s.Coherent)
    (hq : 0 < (spreadLoop x s).q) (hmedium : (spreadLoop x s).q ≤ Rmax ^ 2) :
    (spreadLoop x s).holdsSpreadCondition := by
  obtain ⟨_, _, _, _, _, hexit, _⟩ := spreadLoop_spec x s hs
  exact (spreadLoop_coherent x s hs).spread_iff fun j hj =>
    hexit ⟨hq, hmedium, j, hj⟩

/-- The number of nonzero coefficients does not grow. -/
theorem spreadLoop_support_subset (x : Fin n → ℝ) (s : RowState n)
    (hs : s.Coherent) :
    coeffSupport (spreadLoop x s).b ⊆ coeffSupport s.b :=
  (spreadLoop_spec x s hs).2.2.2.2.2.2

/-! ### The rational scale (paper §2.3, Eqs. (2.13)–(2.14)) -/

/-- A coefficient of maximal absolute value exists whenever some
coefficient is nonzero. -/
theorem exists_abs_max {n : ℕ} {b : Fin n → ℝ} (hne : ∃ j, b j ≠ 0) :
    ∃ j, ∀ k, |b k| ≤ |b j| := by
  obtain ⟨j₀, _⟩ := hne
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun k => |b k|)
    ⟨j₀, Finset.mem_univ j₀⟩
  exact ⟨j, fun k => hj k (Finset.mem_univ k)⟩

/-- `a = max_j |bⱼ|` (paper §2.3), realized as `|b|` of a maximizer. -/
noncomputable def coeffRadius {s : RowState n} (hne : ∃ j, s.b j ≠ 0) : ℝ :=
  |s.b (Classical.choose (exists_abs_max hne))|

theorem coeffRadius_max {s : RowState n} (hne : ∃ j, s.b j ≠ 0) (k : Fin n) :
    |s.b k| ≤ coeffRadius hne :=
  Classical.choose_spec (exists_abs_max hne) k

theorem coeffRadius_pos {s : RowState n} (hne : ∃ j, s.b j ≠ 0) :
    0 < coeffRadius hne := by
  have hmax := coeffRadius_max hne
  obtain ⟨j₀, hj₀⟩ := hne
  exact (abs_pos.mpr hj₀).trans_le (hmax j₀)

/-- The `ℓ`-search of paper Eq. (2.14) has a solution: `(γ²)^ℓ` is
unbounded, so eventually `(γ^ℓ a)² ≥ q`. -/
theorem scaleExponent_exists (q a : ℝ) (ha : 0 < a) :
    ∃ ℓ : ℕ, q ≤ (γ ^ ℓ * a) ^ 2 := by
  obtain ⟨ℓ, hℓ⟩ := pow_unbounded_of_one_lt (q / a ^ 2) gamma_sq_gt_one
  refine ⟨ℓ, ?_⟩
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  rw [div_lt_iff₀ ha2] at hℓ
  have hconv : (γ ^ ℓ * a) ^ 2 = (γ ^ 2) ^ ℓ * a ^ 2 := by ring
  rw [hconv]
  linarith

/-- The least `ℓ ≥ 0` with `γ^{2ℓ} a² ≥ q` (paper Eq. (2.14)). -/
noncomputable def scaleExponent (q a : ℝ) (ha : 0 < a) : ℕ :=
  Nat.find (scaleExponent_exists q a ha)

theorem scaleExponent_spec (q a : ℝ) (ha : 0 < a) :
    q ≤ (γ ^ scaleExponent q a ha * a) ^ 2 :=
  Nat.find_spec (scaleExponent_exists q a ha)

theorem scaleExponent_min (q a : ℝ) (ha : 0 < a) {m : ℕ}
    (hm : m < scaleExponent q a ha) : ¬ q ≤ (γ ^ m * a) ^ 2 :=
  Nat.find_min _ hm

/-- The first candidate `γ^ℓ a` is strictly smaller than `γ√q`, also in
the `ℓ = 0` case where the hypothesis `a² < γ²q` (supplied by the
spread condition) is used (paper §2.3). -/
theorem scaleExponent_lt (q a : ℝ) (ha : 0 < a) (_hq : 0 < q)
    (haq : a ^ 2 < γ ^ 2 * q) :
    γ ^ scaleExponent q a ha * a < γ * Real.sqrt q := by
  set ℓ := scaleExponent q a ha with hℓ
  rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
  · have h1 : a < Real.sqrt (γ ^ 2 * q) := by
      rw [← Real.sqrt_sq ha.le]
      exact Real.sqrt_lt_sqrt (sq_nonneg a) haq
    have h2 : Real.sqrt (γ ^ 2 * q) = γ * Real.sqrt q := by
      rw [Real.sqrt_mul (sq_nonneg γ), Real.sqrt_sq gamma_pos.le]
    have hpow : γ ^ ℓ * a = a := by rw [h0]; simp
    rw [hpow]
    exact h1.trans_eq h2
  · obtain ⟨m, hm_eq⟩ : ∃ m, ℓ = m + 1 :=
      ⟨ℓ - 1, (Nat.sub_add_cancel hpos).symm⟩
    have hm : m < scaleExponent q a ha := by
      have hlt' : m < ℓ := by rw [hm_eq]; exact Nat.lt_succ_self m
      rwa [hℓ] at hlt'
    have hlt := not_le.mp (scaleExponent_min q a ha hm)
    have hnonneg : 0 ≤ γ ^ m * a := mul_nonneg (pow_nonneg gamma_pos.le _) ha.le
    have h3 : γ ^ m * a < Real.sqrt q := by
      rw [← Real.sqrt_sq hnonneg]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hlt
    have h4 : γ ^ ℓ * a = γ * (γ ^ m * a) := by
      rw [hm_eq, pow_succ']
      ring
    rw [h4]
    exact mul_lt_mul_of_pos_left h3 gamma_pos

/-- The scale update of paper §2.3: `min (γ^ℓ a, Rmax, r_old)` where `ℓ`
is least with `(γ^ℓ a)² ≥ q` and `a = max_j |bⱼ|`. -/
noncomputable def updateScale {s : RowState n} (hne : ∃ j, s.b j ≠ 0) : ℝ :=
  let a := coeffRadius hne
  min (min (γ ^ scaleExponent s.q a (coeffRadius_pos hne) * a) Rmax) s.r

/-- The updated scale satisfies the window `q ≤ r'² < γ² q` and is at
most the old scale and `Rmax` (paper Eq. (2.13)).  The spread
hypothesis is what makes the `ℓ = 0` case work; the disjunctive
invariant `scaleInvariant` supplies `√q ≤ r_old`. -/
theorem updateScale_spec {s : RowState n} (hne : ∃ j, s.b j ≠ 0)
    (hs : s.Coherent) (hq : 0 < s.q) (hmedium : s.q ≤ Rmax ^ 2)
    (hspread : s.holdsSpreadCondition) (hr : 0 ≤ s.r)
    (hinv : scaleInvariant s.q s.r) :
    s.q ≤ (updateScale hne) ^ 2 ∧ (updateScale hne) ^ 2 < γ ^ 2 * s.q ∧
      updateScale hne ≤ s.r ∧ updateScale hne ≤ Rmax ∧ 0 ≤ updateScale hne := by
  set a := coeffRadius hne with ha_def
  set ℓ := scaleExponent s.q a (coeffRadius_pos hne) with hℓ_def
  set r' := updateScale hne with hr'_def
  have ha_pos : 0 < a := coeffRadius_pos hne
  -- `a² = (b jmax)² ≤ q/64 < γ²q` by the spread condition.
  have hle : a ^ 2 ≤ s.q * spreadBound := by
    have h := hspread (Classical.choose (exists_abs_max hne))
    rw [hs.1 (Classical.choose (exists_abs_max hne))] at h
    show |s.b (Classical.choose (exists_abs_max hne))| ^ 2 ≤ s.q * spreadBound
    rwa [sq_abs]
  have ha2 : a ^ 2 < γ ^ 2 * s.q :=
    hle.trans_lt (by nlinarith [spreadBound_lt_gamma_sq, hq])
  have hlt : γ ^ ℓ * a < γ * Real.sqrt s.q :=
    scaleExponent_lt s.q a ha_pos hq ha2
  -- All three candidates are `≥ √q`.
  have hcand1 : Real.sqrt s.q ≤ γ ^ ℓ * a :=
    Real.sqrt_le_iff.mpr
      ⟨mul_nonneg (pow_nonneg gamma_pos.le _) ha_pos.le,
        scaleExponent_spec s.q a ha_pos⟩
  have hcand2 : Real.sqrt s.q ≤ Rmax :=
    Real.sqrt_le_iff.mpr ⟨Rmax_pos.le, hmedium⟩
  have hcand3 : Real.sqrt s.q ≤ s.r := by
    rcases hinv with h | h
    · exact Real.sqrt_le_iff.mpr ⟨hr, h⟩
    · rw [h]; exact hcand2
  -- Properties of the minimum.
  have hr'_ge : Real.sqrt s.q ≤ r' := le_min (le_min hcand1 hcand2) hcand3
  have hr'_nn : 0 ≤ r' := (Real.sqrt_nonneg s.q).trans hr'_ge
  have hr'_le_first : r' ≤ γ ^ ℓ * a :=
    (min_le_left _ _).trans (min_le_left _ _)
  refine ⟨?_, ?_, ?_, ?_, hr'_nn⟩
  · calc s.q = (Real.sqrt s.q) ^ 2 := (Real.sq_sqrt hq.le).symm
      _ ≤ r' ^ 2 := sq_le_sq' (by linarith [Real.sqrt_nonneg s.q]) hr'_ge
  · have hsq1 : (γ ^ ℓ * a) ^ 2 < γ ^ 2 * s.q := by
      have hz : γ * Real.sqrt s.q = Real.sqrt (γ ^ 2 * s.q) := by
        rw [Real.sqrt_mul (sq_nonneg γ), Real.sqrt_sq gamma_pos.le]
      calc (γ ^ ℓ * a) ^ 2 < (γ * Real.sqrt s.q) ^ 2 := by
            have hsum : 0 < γ ^ ℓ * a + γ * Real.sqrt s.q :=
              add_pos (mul_pos (pow_pos gamma_pos ℓ) ha_pos)
                (mul_pos gamma_pos (Real.sqrt_pos.mpr hq))
            nlinarith [hlt, mul_pos (sub_pos.mpr hlt) hsum]
        _ = γ ^ 2 * s.q := by
            rw [hz, Real.sq_sqrt (mul_nonneg (sq_nonneg γ) hq.le)]
    exact (sq_le_sq' (by linarith [hr'_nn, ha_pos]) hr'_le_first).trans_lt hsq1
  · show min (min (γ ^ ℓ * a) Rmax) s.r ≤ s.r
    exact min_le_right _ _
  · show min (min (γ ^ ℓ * a) Rmax) s.r ≤ Rmax
    exact (min_le_left _ _).trans (min_le_right _ _)

end RowState

/-! ## Row classes and the anchored update -/

/-- Row classes after cleanup (paper §2.2): `completed` rows have no
mass left, `retired` rows are stored and dropped from all spectral
computations, `anchored` rows keep being tracked (medium rows get an
updated scale, large rows carry a deposit). -/
inductive RowClass where
  | completed
  | retired
  | anchored
  deriving DecidableEq

/-- The class of a post-cleanup row state. -/
noncomputable def classify {n : ℕ} (qstar : ℝ) (s : RowState n) : RowClass :=
  if s.q = 0 then .completed else if s.q ≤ qstar then .retired else .anchored

theorem classify_eq_completed {n : ℕ} {qstar : ℝ} {s : RowState n} :
    classify qstar s = .completed ↔ s.q = 0 := by
  unfold classify
  by_cases h1 : s.q = 0
  · simp [h1]
  · by_cases h2 : s.q ≤ qstar <;> simp [h1, h2]

theorem classify_eq_retired {n : ℕ} {qstar : ℝ} {s : RowState n} :
    classify qstar s = .retired ↔ s.q ≠ 0 ∧ s.q ≤ qstar := by
  unfold classify
  by_cases h1 : s.q = 0
  · simp [h1]
  · by_cases h2 : s.q ≤ qstar <;> simp [h1, h2]

theorem classify_eq_anchored {n : ℕ} {qstar : ℝ} {s : RowState n} :
    classify qstar s = .anchored ↔ s.q ≠ 0 ∧ qstar < s.q := by
  unfold classify
  by_cases h1 : s.q = 0
  · simp [h1]
  · by_cases h2 : s.q ≤ qstar
    · simp [h1, h2]
    · simp [h1, h2]
      exact not_le.mp h2

/-- At loop exit exactly one of the three classes applies
(`0 ≤ q` suffices). -/
theorem classify_trichotomy {n : ℕ} {qstar : ℝ} {s : RowState n}
    (hq : 0 ≤ s.q) (_hqstar : 0 < qstar) :
    (classify qstar s = .completed ∧ s.q = 0) ∨
      (classify qstar s = .retired ∧ 0 < s.q ∧ s.q ≤ qstar) ∨
        (classify qstar s = .anchored ∧ qstar < s.q) := by
  unfold classify
  by_cases h1 : s.q = 0
  · left
    exact ⟨by simp [h1], h1⟩
  · by_cases h2 : s.q ≤ qstar
    · right; left
      exact ⟨by simp [h1, h2], lt_of_le_of_ne' hq h1, h2⟩
    · right; right
      exact ⟨by simp [h1, h2], not_le.mp h2⟩

namespace RowState

variable {n : ℕ}

/-- The anchored per-row update (Algorithm 1, step 3): transfer frozen
coefficients, run the spread-deletion loop, and for medium rows that
are not retired update the scale. -/
noncomputable def anchorUpdate (x : Fin n → ℝ) (s : RowState n) (qstar : ℝ) :
    RowState n :=
  if qstar < (spreadLoop x (transferFixed x s)).q ∧
      (spreadLoop x (transferFixed x s)).q ≤ Rmax ^ 2 then
    if hne : ∃ j, (spreadLoop x (transferFixed x s)).b j ≠ 0 then
      { spreadLoop x (transferFixed x s) with r := updateScale hne }
    else spreadLoop x (transferFixed x s)
  else spreadLoop x (transferFixed x s)

/-- The output of `anchorUpdate` is either the post-loop state or that
state with a rescaled `r`. -/
theorem anchorUpdate_cases (x : Fin n → ℝ) (s : RowState n) (qstar : ℝ) :
    anchorUpdate x s qstar = spreadLoop x (transferFixed x s) ∨
      (∃ hne : ∃ j, (spreadLoop x (transferFixed x s)).b j ≠ 0,
        qstar < (spreadLoop x (transferFixed x s)).q ∧
        (spreadLoop x (transferFixed x s)).q ≤ Rmax ^ 2 ∧
        anchorUpdate x s qstar =
          { spreadLoop x (transferFixed x s) with r := updateScale hne }) := by
  unfold anchorUpdate
  split_ifs with h hne
  · exact Or.inr ⟨hne, h.1, h.2, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl

theorem anchorUpdate_q_eq (x : Fin n → ℝ) (s : RowState n) (qstar : ℝ) :
    (anchorUpdate x s qstar).q = (spreadLoop x (transferFixed x s)).q := by
  unfold anchorUpdate
  split_ifs <;> rfl

theorem anchorUpdate_c_eq (x : Fin n → ℝ) (s : RowState n) (qstar : ℝ) :
    (anchorUpdate x s qstar).c = (spreadLoop x (transferFixed x s)).c := by
  unfold anchorUpdate
  split_ifs <;> rfl

theorem anchorUpdate_b_eq (x : Fin n → ℝ) (s : RowState n) (qstar : ℝ) :
    (anchorUpdate x s qstar).b = (spreadLoop x (transferFixed x s)).b := by
  unfold anchorUpdate
  split_ifs <;> rfl

theorem anchorUpdate_p_eq (x : Fin n → ℝ) (s : RowState n) (qstar : ℝ) :
    (anchorUpdate x s qstar).p = (spreadLoop x (transferFixed x s)).p := by
  unfold anchorUpdate
  split_ifs <;> rfl

/-- The remaining mass is nonincreasing along the whole update. -/
theorem anchorUpdate_q_le (x : Fin n → ℝ) (s : RowState n) (qstar : ℝ)
    (hs : s.Coherent) : (anchorUpdate x s qstar).q ≤ s.q := by
  rw [anchorUpdate_q_eq]
  exact (spreadLoop_q_le x _ (transferFixed_coherent x s hs)).trans
    (transferFixed_q_le x s)

/-- The remaining mass stays nonnegative. -/
theorem anchorUpdate_q_nonneg (x : Fin n → ℝ) (s : RowState n) (qstar : ℝ)
    (hs : s.Coherent) : 0 ≤ (anchorUpdate x s qstar).q := by
  rw [anchorUpdate_q_eq]
  exact spreadLoop_q_nonneg x _ (transferFixed_coherent x s hs)

/-- The update preserves coherence. -/
theorem anchorUpdate_coherent (x : Fin n → ℝ) (s : RowState n) (qstar : ℝ)
    (hs : s.Coherent) : (anchorUpdate x s qstar).Coherent := by
  have h2 : (spreadLoop x (transferFixed x s)).Coherent :=
    spreadLoop_coherent x _ (transferFixed_coherent x s hs)
  obtain h | ⟨hne, _, _, heq⟩ := anchorUpdate_cases x s qstar
  · rw [h]; exact h2
  · rw [heq]; exact h2

/-- The exact affine identity `rowValue = c + ∑ bⱼ xⱼ` is invariant
under the whole update. -/
theorem anchorUpdate_affine (x : Fin n → ℝ) (s : RowState n) (qstar : ℝ)
    (hs : s.Coherent) :
    affineValue (anchorUpdate x s qstar).c (anchorUpdate x s qstar).b x =
      affineValue s.c s.b x := by
  rw [anchorUpdate_c_eq, anchorUpdate_b_eq]
  exact (spreadLoop_affine x _ (transferFixed_coherent x s hs)).trans
    (transferFixed_affine x s)

/-- The scale invariant carries over the mass-reducing phases
(`transferFixed` and `spreadLoop` keep `r` fixed). -/
theorem scaleInvariant_postloop (x : Fin n → ℝ) (s : RowState n)
    (hs : s.Coherent) (hinv : scaleInvariant s.q s.r) :
    scaleInvariant (spreadLoop x (transferFixed x s)).q
      (spreadLoop x (transferFixed x s)).r := by
  have hs2 := transferFixed_coherent x s hs
  have hr2 : (spreadLoop x (transferFixed x s)).r = s.r := by
    rw [spreadLoop_r x _ hs2, transferFixed_r]
  rw [hr2]
  exact scaleInvariant_of_le hinv
    ((spreadLoop_q_le x _ hs2).trans (transferFixed_q_le x s))

/-- The scale is nonincreasing. -/
theorem anchorUpdate_r_le (x : Fin n → ℝ) (s : RowState n) (qstar : ℝ)
    (hs : s.Coherent) (hqstar : 0 < qstar)
    (hinv : scaleInvariant s.q s.r) (hr : 0 ≤ s.r) :
    (anchorUpdate x s qstar).r ≤ s.r := by
  have hs2 := transferFixed_coherent x s hs
  obtain h | ⟨hne, hq, hmed, heq⟩ := anchorUpdate_cases x s qstar
  · rw [h, spreadLoop_r x _ hs2, transferFixed_r]
  · have hspec := updateScale_spec hne (spreadLoop_coherent x _ hs2)
      (hqstar.trans hq) hmed
      (spreadLoop_spread x _ hs2 (hqstar.trans hq) hmed)
      (by rw [spreadLoop_r x _ hs2, transferFixed_r]; exact hr)
      (scaleInvariant_postloop x s hs hinv)
    rw [heq]
    show updateScale hne ≤ s.r
    exact hspec.2.2.1.trans
      (by rw [spreadLoop_r x _ hs2, transferFixed_r])

/-- The scale stays nonnegative. -/
theorem anchorUpdate_r_nonneg (x : Fin n → ℝ) (s : RowState n) (qstar : ℝ)
    (hs : s.Coherent) (hqstar : 0 < qstar)
    (hinv : scaleInvariant s.q s.r) (hr : 0 ≤ s.r) :
    0 ≤ (anchorUpdate x s qstar).r := by
  have hs2 := transferFixed_coherent x s hs
  obtain h | ⟨hne, hq, hmed, heq⟩ := anchorUpdate_cases x s qstar
  · rw [h, spreadLoop_r x _ hs2, transferFixed_r]; exact hr
  · have hspec := updateScale_spec hne (spreadLoop_coherent x _ hs2)
      (hqstar.trans hq) hmed
      (spreadLoop_spread x _ hs2 (hqstar.trans hq) hmed)
      (by rw [spreadLoop_r x _ hs2, transferFixed_r]; exact hr)
      (scaleInvariant_postloop x s hs hinv)
    rw [heq]
    exact hspec.2.2.2.2

/-- The scale stays at most `Rmax`. -/
theorem anchorUpdate_r_le_Rmax (x : Fin n → ℝ) (s : RowState n) (qstar : ℝ)
    (hs : s.Coherent) (hqstar : 0 < qstar)
    (hinv : scaleInvariant s.q s.r)
    (hr : 0 ≤ s.r) (hrmax : s.r ≤ Rmax) :
    (anchorUpdate x s qstar).r ≤ Rmax := by
  have hs2 := transferFixed_coherent x s hs
  obtain h | ⟨hne, hq, hmed, heq⟩ := anchorUpdate_cases x s qstar
  · rw [h, spreadLoop_r x _ hs2, transferFixed_r]; exact hrmax
  · have hspec := updateScale_spec hne (spreadLoop_coherent x _ hs2)
      (hqstar.trans hq) hmed
      (spreadLoop_spread x _ hs2 (hqstar.trans hq) hmed)
      (by rw [spreadLoop_r x _ hs2, transferFixed_r]; exact hr)
      (scaleInvariant_postloop x s hs hinv)
    rw [heq]
    exact hspec.2.2.2.1

/-- The scale invariant `q ≤ r² ∨ r = Rmax` is preserved. -/
theorem anchorUpdate_scale_invariant (x : Fin n → ℝ) (s : RowState n) (qstar : ℝ)
    (hs : s.Coherent) (hqstar : 0 < qstar)
    (hinv : scaleInvariant s.q s.r) (hr : 0 ≤ s.r) :
    scaleInvariant (anchorUpdate x s qstar).q (anchorUpdate x s qstar).r := by
  have hs2 := transferFixed_coherent x s hs
  have hinv2 := scaleInvariant_postloop x s hs hinv
  obtain h | ⟨hne, hq, hmed, heq⟩ := anchorUpdate_cases x s qstar
  · rwa [h]
  · have hspec := updateScale_spec hne (spreadLoop_coherent x _ hs2)
      (hqstar.trans hq) hmed
      (spreadLoop_spread x _ hs2 (hqstar.trans hq) hmed)
      (by rw [spreadLoop_r x _ hs2, transferFixed_r]; exact hr)
      hinv2
    rw [heq]
    exact Or.inl hspec.1

/-- After the update every noncompleted medium row satisfies the spread
condition (paper Eq. (2.9)). -/
theorem anchorUpdate_spread (x : Fin n → ℝ) (s : RowState n) (qstar : ℝ)
    (hs : s.Coherent)
    (hq : 0 < (anchorUpdate x s qstar).q)
    (hmedium : (anchorUpdate x s qstar).q ≤ Rmax ^ 2) :
    (anchorUpdate x s qstar).holdsSpreadCondition := by
  have hs2 := transferFixed_coherent x s hs
  rw [anchorUpdate_q_eq] at hq hmedium
  have hsp := spreadLoop_spread x _ hs2 hq hmedium
  intro j
  have := hsp j
  rwa [anchorUpdate_q_eq, anchorUpdate_p_eq]

/-- An anchored medium row always goes through the scale-update
branch (its post-loop mass is positive, so a nonzero coefficient
exists by coherence). -/
theorem anchorUpdate_eq_scale (x : Fin n → ℝ) (s : RowState n) (qstar : ℝ)
    (hs : s.Coherent) (hqstar : 0 < qstar)
    (hanch : qstar < (spreadLoop x (transferFixed x s)).q)
    (hmedium : (spreadLoop x (transferFixed x s)).q ≤ Rmax ^ 2) :
    ∃ hne : ∃ j, (spreadLoop x (transferFixed x s)).b j ≠ 0,
      anchorUpdate x s qstar =
        { spreadLoop x (transferFixed x s) with r := updateScale hne } := by
  have hco2 := spreadLoop_coherent x _ (transferFixed_coherent x s hs)
  have hne := hco2.exists_coeff_ne_zero (hqstar.trans hanch)
  refine ⟨hne, ?_⟩
  unfold anchorUpdate
  split_ifs
  all_goals
    first
      | rfl
      | exact absurd hne (by assumption)
      | exact absurd (And.intro hanch hmedium) (by assumption)

/-- For anchored medium rows the scale lands in the window
`q ≤ r² < γ² q` (paper Eq. (2.13)). -/
theorem anchorUpdate_scale_window (x : Fin n → ℝ) (s : RowState n) (qstar : ℝ)
    (hs : s.Coherent) (hqstar : 0 < qstar)
    (hinv : scaleInvariant s.q s.r) (hr : 0 ≤ s.r)
    (hcls : classify qstar (anchorUpdate x s qstar) = .anchored)
    (hmedium : (anchorUpdate x s qstar).q ≤ Rmax ^ 2) :
    scaleWindow (anchorUpdate x s qstar).q (anchorUpdate x s qstar).r := by
  have hs2 := transferFixed_coherent x s hs
  have hanch : qstar < (spreadLoop x (transferFixed x s)).q := by
    rw [← anchorUpdate_q_eq]
    exact (classify_eq_anchored.mp hcls).2
  have hmed : (spreadLoop x (transferFixed x s)).q ≤ Rmax ^ 2 := by
    rwa [anchorUpdate_q_eq] at hmedium
  obtain ⟨hne, heq⟩ := anchorUpdate_eq_scale x s qstar hs hqstar hanch hmed
  have hspec := updateScale_spec hne (spreadLoop_coherent x _ hs2)
    (hqstar.trans hanch) hmed
    (spreadLoop_spread x _ hs2 (hqstar.trans hanch) hmed)
    (by rw [spreadLoop_r x _ hs2, transferFixed_r]; exact hr)
    (scaleInvariant_postloop x s hs hinv)
  rw [heq]
  show scaleWindow (spreadLoop x (transferFixed x s)).q (updateScale hne)
  exact ⟨hspec.1, hspec.2.1⟩

/-- At the end of the update exactly one of the three row classes
applies. -/
theorem anchorUpdate_classify_trichotomy (x : Fin n → ℝ) (s : RowState n)
    (qstar : ℝ) (hs : s.Coherent) (hqstar : 0 < qstar) :
    (classify qstar (anchorUpdate x s qstar) = .completed ∧
        (anchorUpdate x s qstar).q = 0) ∨
      (classify qstar (anchorUpdate x s qstar) = .retired ∧
        0 < (anchorUpdate x s qstar).q ∧
        (anchorUpdate x s qstar).q ≤ qstar) ∨
      (classify qstar (anchorUpdate x s qstar) = .anchored ∧
        qstar < (anchorUpdate x s qstar).q) :=
  classify_trichotomy (anchorUpdate_q_nonneg x s qstar hs) hqstar

/-! ### Retirement (paper Eq. (2.11)) -/

/-- Retirement of a row: store its current value in the offset and drop
every coefficient (`c ← c + bᵀx`, `b ← 0`).  The analysis keeps the old
coefficient vector only on paper; here the old state is simply the
input. -/
noncomputable def retire (x : Fin n → ℝ) (s : RowState n) : RowState n where
  c := s.c + ∑ j, rowErrorChangeEntry s.b x j
  b := 0
  p := 0
  q := 0
  r := s.r

theorem retire_coherent (x : Fin n → ℝ) (s : RowState n) :
    (retire x s).Coherent := by
  refine ⟨fun j => by simp [retire], ?_⟩
  show (0 : ℝ) = ∑ _j, (0 : Fin n → ℝ) _
  simp

theorem retire_affine (x : Fin n → ℝ) (s : RowState n) :
    affineValue (retire x s).c (retire x s).b x = affineValue s.c s.b x := by
  show s.c + (∑ j, rowErrorChangeEntry s.b x j) +
      (∑ _j : Fin n, (0 : Fin n → ℝ) _ * x _) = s.c + ∑ j, s.b j * x j
  simp [rowErrorChangeEntry]

theorem retire_q (x : Fin n → ℝ) (s : RowState n) : (retire x s).q = 0 := rfl

theorem retire_classify (x : Fin n → ℝ) (s : RowState n) (qstar : ℝ) :
    classify qstar (retire x s) = .completed := by
  rw [classify_eq_completed]
  rfl

end RowState

end Komlos
