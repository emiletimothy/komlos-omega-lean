/-
# Finite-precision layer: rational grid rounding and transcript coupling

This module formalizes the deterministic half of the finite-precision
("dithered transcript") analysis of "The Komlós Problem in Near
Matrix-Multiplication Time" (Anand–Chen). Everything proved here is an
unconditional deterministic error bound; no probabilistic statement is made
and no new axioms are used.

## What is proved

* **Grid rounding.** `roundToGrid x s` rounds a rational `x` to the nearest
  multiple of `1/s`, with the two-sided bound
  `|x - roundToGrid x s| ≤ 1/(2s)` (`abs_sub_roundToGrid`), monotonicity
  (`roundToGrid_mono`) and idempotence (`roundToGrid_idem`). `floorToGrid`
  rounds down with the one-sided bounds `0 ≤ x - floorToGrid x s ≤ 1/s`
  (`floorToGrid_le`, `sub_floorToGrid_lt`, `abs_sub_floorToGrid`).
  `roundToGridR` is the real analogue, and `ratCast_roundToGrid` shows the
  rational construction casts to the real one.
* **Rounded input matrices.** `roundEntrywise A s` rounds each entry of a
  rational matrix; each row's L¹ error is at most `n/(2s)`
  (`roundEntrywise_row_l1`, `roundEntrywise_row_l1_real`). Chained through
  `input_rounding_error` and `accepted_output_sound`, checking a signing on
  the rounded input at threshold `9899/100` certifies exact discrepancy
  `< 99` once `n/(2s) ≤ 1/10000` (`verifyRounded_sound`), in particular
  whenever `5000 * n ≤ s` (`verifyRounded_sound_natPrecision`,
  `soundness_precision_suffices`, `binary_precision_suffices`). More
  generally, a check at threshold `T` on the rounded input gives exact
  discrepancy `T + n/(2s)` (`rounded_threshold_check`,
  `verifySigning_rounded_sound` for `T = 99`).
* **Deterministic transcript coupling.** Two transcripts whose states stay
  within `δ` coordinatewise and that are driven by the same coefficient
  sequence accumulate linear-functional drift at most `δ` times the total
  coefficient mass (`step_coupling_bound`, `transcript_drift_bound`,
  `transcript_drift_bound'`, `transcript_drift_of_total`,
  `coupled_affine_transcript_drift`). Under the deletion-charge hypotheses of
  `deleted_defect_bound`, the drift along the deleted direction is at most
  `δ * (291/200) * (8 + √63)` (`coupled_deleted_drift` — the `δ = 2`
  special case via `cube_difference_abs_le_two` recovers
  `deleted_defect_bound`). The tracked `energy` and `barrier` quantities are
  Lipschitz in their data (`energy_drift_bound`, `barrier_drift_bound`), and
  `step_affine_coupling`/`step_affine_coupling_bound` bound the defect of one
  affine tracked value under simultaneous changes of offset, coefficients and
  evaluation point. Rounding every state to the grid `1/s` couples a
  transcript to its dithered image with drift at most
  `(1/(2s)) *` total coefficient mass (`rounded_transcript_drift`).
* **Precision bookkeeping.** `grid_precision_suffices`,
  `soundness_precision_suffices` and `binary_precision_suffices` solve the
  rounding bound for the required grid; `roundToGrid_den_dvd`,
  `roundToGrid_den_le`, `roundToGrid_num_abs_le` and
  `ratBitSize_roundToGrid_le` bound the size of rounded entries so the
  runtime model of `Komlos/Runtime.lean` can quote a bit length.

## What is NOT proved here

The paper couples *randomized* roundings: it dithers the maintained state so
that the rounded transcript is a martingale whose increments are controlled
with high probability. That statement requires a measure-theoretic model of
the walk, which this module does not supply; the stochastic coupling, the
adaptive Gaussian density invariant, and the expected bit-complexity theorem
remain open. All bounds here are worst-case deterministic ones: they hold for
*every* pair of transcripts satisfying the stated per-step proximity — weaker
than, but strictly implied by, the high-probability coupling.
-/

import Komlos.Runtime
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Cast.Order

namespace Komlos

open scoped BigOperators

/-! ## Grid rounding on `ℚ` -/

/-- Round `x : ℚ` to the nearest multiple of `1/s`, i.e.
`roundToGrid x s = round (x * s) / s`. For `s = 0` this is junk (`0/0 = 0`);
all quantitative lemmas assume `0 < s`. -/
def roundToGrid (x : ℚ) (s : ℕ) : ℚ := (round (x * s) : ℚ) / s

/-- The values produced by `roundToGrid` are exactly the fractions `k/s`. -/
theorem roundToGrid_eq_divInt (x : ℚ) (s : ℕ) :
    roundToGrid x s = Rat.divInt (round (x * s)) (s : ℤ) := by
  rw [Rat.divInt_eq_div, roundToGrid, Int.cast_natCast]

/-- The two-sided rounding bound: `|x - roundToGrid x s| ≤ 1/(2s)`. -/
theorem abs_sub_roundToGrid (x : ℚ) {s : ℕ} (hs : 0 < s) :
    |x - roundToGrid x s| ≤ 1 / (2 * s) := by
  have hs' : (0 : ℚ) < s := by exact_mod_cast hs
  have h : x - roundToGrid x s = (x * s - (round (x * s) : ℚ)) / s := by
    show x - (round (x * s) : ℚ) / s = (x * s - (round (x * s) : ℚ)) / s
    exact sub_div' hs'.ne'
  rw [h, abs_div, abs_of_nonneg hs'.le]
  calc |x * s - (round (x * s) : ℚ)| / s ≤ (1 / 2) / s :=
        (div_le_div_iff_of_pos_right hs').mpr (abs_sub_round _)
    _ = 1 / (2 * s) := by rw [div_div]

theorem roundToGrid_le_add (x : ℚ) {s : ℕ} (hs : 0 < s) :
    roundToGrid x s ≤ x + 1 / (2 * s) := by
  have h := (abs_le.mp (abs_sub_roundToGrid x hs)).1
  linarith

theorem sub_le_roundToGrid (x : ℚ) {s : ℕ} (hs : 0 < s) :
    x - 1 / (2 * s) ≤ roundToGrid x s := by
  have h := (abs_le.mp (abs_sub_roundToGrid x hs)).2
  linarith

/-- `roundToGrid` is monotone in its argument (the grid is fixed). -/
theorem roundToGrid_mono {s : ℕ} (hs : 0 < s) :
    Monotone fun x : ℚ => roundToGrid x s := by
  intro x y hxy
  have hs' : (0 : ℚ) < s := by exact_mod_cast hs
  have hmul : x * s ≤ y * s := mul_le_mul_of_nonneg_right hxy hs'.le
  have hround : round (x * s) ≤ round (y * s) := by
    rw [round_eq, round_eq]
    exact Int.floor_mono (by linarith)
  exact (div_le_div_iff_of_pos_right hs').mpr (by exact_mod_cast hround)

/-- Grid points are fixed points: rounding an already-rounded value is a
no-op. -/
theorem roundToGrid_idem (x : ℚ) {s : ℕ} (hs : 0 < s) :
    roundToGrid (roundToGrid x s) s = roundToGrid x s := by
  have hs' : (0 : ℚ) < s := by exact_mod_cast hs
  unfold roundToGrid
  congr 1
  rw [div_mul_cancel₀ _ hs'.ne', round_intCast]

/-- The rounded value has denominator dividing `s` — this is what makes the
bit length of a rounded entry controllable. -/
theorem roundToGrid_den_dvd (x : ℚ) (s : ℕ) :
    (roundToGrid x s).den ∣ s := by
  rw [roundToGrid_eq_divInt]
  exact_mod_cast Rat.den_dvd (round (x * s)) (s : ℤ)

theorem roundToGrid_den_le (x : ℚ) {s : ℕ} (hs : 0 < s) :
    (roundToGrid x s).den ≤ s :=
  Nat.le_of_dvd hs (roundToGrid_den_dvd x s)

/-- The numerator of a rounded value is controlled by the magnitude of the
input: `|num (roundToGrid x s)| ≤ |x| * s + 1`. -/
theorem roundToGrid_num_abs_le (x : ℚ) {s : ℕ} (hs : 0 < s) :
    (|(roundToGrid x s).num| : ℚ) ≤ |x| * s + 1 := by
  have hdpos : (0 : ℚ) < (((roundToGrid x s).den : ℤ) : ℚ) := by
    exact_mod_cast (roundToGrid x s).den_pos
  have hnum : ((roundToGrid x s).num : ℚ) =
      roundToGrid x s * (((roundToGrid x s).den : ℤ) : ℚ) := by
    have h := Rat.num_divInt_den (roundToGrid x s)
    rw [Rat.divInt_eq_div] at h
    exact (div_eq_iff hdpos.ne').mp h
  rw [Int.cast_natCast] at hnum
  have habs : |((roundToGrid x s).num : ℚ)| =
      |roundToGrid x s| * (roundToGrid x s).den := by
    rw [hnum, abs_mul]
    congr 1
    exact abs_of_pos (Nat.cast_pos.mpr (roundToGrid x s).den_pos)
  have hqbound : |roundToGrid x s| ≤ |x| + 1 / (2 * s) := by
    have h1 : |roundToGrid x s| ≤ |x| + |x - roundToGrid x s| := by
      calc |roundToGrid x s| = |x - (x - roundToGrid x s)| := by
            rw [sub_sub_self]
        _ ≤ |x| + |x - roundToGrid x s| := abs_sub _ _
    linarith [abs_sub_roundToGrid x hs]
  have hdenle : ((roundToGrid x s).den : ℚ) ≤ s := by
    exact_mod_cast roundToGrid_den_le x hs
  have h2s : (0 : ℚ) ≤ 1 / (2 * s) := by positivity
  have hb : 0 ≤ |x| + 1 / (2 * s) := by linarith [abs_nonneg x]
  rw [habs]
  calc |roundToGrid x s| * ((roundToGrid x s).den : ℚ)
      ≤ (|x| + 1 / (2 * s)) * s :=
        mul_le_mul hqbound hdenle (Nat.cast_nonneg _) hb
    _ = |x| * s + 1 / 2 := by
        have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
        field_simp
    _ ≤ |x| * s + 1 := by linarith

/-- Bit size of a rounded entry: at most the numerator digits plus the
digits of `s` (the denominator is a divisor of `s`). -/
theorem ratBitSize_roundToGrid_le (x : ℚ) {s : ℕ} (hs : 0 < s) :
    ratBitSize (roundToGrid x s) ≤
      natBitSize (roundToGrid x s).num.natAbs + natBitSize s := by
  unfold ratBitSize
  exact Nat.add_le_add_left (natBitSize_mono (roundToGrid_den_le x hs)) _

/-! ## Rounding down: `floorToGrid` -/

/-- Round `x : ℚ` *down* to the grid `1/s`, i.e. `⌊x * s⌋ / s`. -/
def floorToGrid (x : ℚ) (s : ℕ) : ℚ := (⌊x * s⌋ : ℚ) / s

theorem floorToGrid_le (x : ℚ) {s : ℕ} (hs : 0 < s) : floorToGrid x s ≤ x := by
  have hs' : (0 : ℚ) < s := by exact_mod_cast hs
  calc floorToGrid x s ≤ (x * s) / s :=
        (div_le_div_iff_of_pos_right hs').mpr (Int.floor_le _)
    _ = x := mul_div_cancel_right₀ x hs'.ne'

theorem sub_floorToGrid_lt (x : ℚ) {s : ℕ} (hs : 0 < s) :
    x - floorToGrid x s < 1 / s := by
  have hs' : (0 : ℚ) < s := by exact_mod_cast hs
  have h : x - floorToGrid x s = Int.fract (x * s) / s := by
    show x - (⌊x * s⌋ : ℚ) / s = (x * s - (⌊x * s⌋ : ℚ)) / s
    exact sub_div' hs'.ne'
  rw [h]
  exact (div_lt_div_iff_of_pos_right hs').mpr (Int.fract_lt_one _)

/-- The one-sided floor error gives the two-sided bound `1/s`. -/
theorem abs_sub_floorToGrid (x : ℚ) {s : ℕ} (hs : 0 < s) :
    |x - floorToGrid x s| ≤ 1 / s := by
  rw [abs_of_nonneg (sub_nonneg.mpr (floorToGrid_le x hs))]
  exact (sub_floorToGrid_lt x hs).le

theorem floorToGrid_idem (x : ℚ) {s : ℕ} (hs : 0 < s) :
    floorToGrid (floorToGrid x s) s = floorToGrid x s := by
  have hs' : (0 : ℚ) < s := by exact_mod_cast hs
  unfold floorToGrid
  congr 1
  rw [div_mul_cancel₀ _ hs'.ne', Int.floor_intCast]

theorem floorToGrid_mono {s : ℕ} (hs : 0 < s) :
    Monotone fun x : ℚ => floorToGrid x s := by
  intro x y hxy
  have hs' : (0 : ℚ) < s := by exact_mod_cast hs
  have hmul : x * s ≤ y * s := mul_le_mul_of_nonneg_right hxy hs'.le
  have hfloor : ⌊x * s⌋ ≤ ⌊y * s⌋ := Int.floor_mono hmul
  exact (div_le_div_iff_of_pos_right hs').mpr (by exact_mod_cast hfloor)

/-! ## The real analogue `roundToGridR` -/

/-- Round `x : ℝ` to the nearest multiple of `1/s`. Noncomputable because the
real floor uses choice; for rational inputs it agrees with `roundToGrid`
(`ratCast_roundToGrid`). -/
noncomputable def roundToGridR (x : ℝ) (s : ℕ) : ℝ := (round (x * s) : ℝ) / s

theorem abs_sub_roundToGridR (x : ℝ) {s : ℕ} (hs : 0 < s) :
    |x - roundToGridR x s| ≤ 1 / (2 * s) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have h : x - roundToGridR x s = (x * s - (round (x * s) : ℝ)) / s := by
    show x - (round (x * s) : ℝ) / s = (x * s - (round (x * s) : ℝ)) / s
    exact sub_div' hs'.ne'
  rw [h, abs_div, abs_of_nonneg hs'.le]
  calc |x * s - (round (x * s) : ℝ)| / s ≤ (1 / 2) / s :=
        (div_le_div_iff_of_pos_right hs').mpr (abs_sub_round _)
    _ = 1 / (2 * s) := by rw [div_div]

theorem roundToGridR_mono {s : ℕ} (hs : 0 < s) :
    Monotone fun x : ℝ => roundToGridR x s := by
  intro x y hxy
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hmul : x * s ≤ y * s := mul_le_mul_of_nonneg_right hxy hs'.le
  have hround : round (x * s) ≤ round (y * s) := by
    rw [round_eq, round_eq]
    exact Int.floor_mono (by linarith)
  exact (div_le_div_iff_of_pos_right hs').mpr (by exact_mod_cast hround)

/-- Rational grid rounding is compatible with real grid rounding under the
cast `ℚ → ℝ`. -/
theorem ratCast_roundToGrid (x : ℚ) (s : ℕ) :
    ((roundToGrid x s : ℚ) : ℝ) = roundToGridR (x : ℝ) s := by
  have hmap : round ((Rat.castHom ℝ) (x * s)) = round (x * s) :=
    Int.map_round (Rat.castHom ℝ) Rat.cast_strictMono _
  rw [Rat.coe_castHom] at hmap
  push_cast at hmap
  unfold roundToGrid roundToGridR
  rw [hmap]
  push_cast
  rfl

/-! ## Rounded input matrices -/

/-- Entrywise rounding of a rational matrix to the grid `1/s`. The result is
still a rational matrix, so the exact rational checker `verifySigning` can be
run on it. -/
def roundEntrywise {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (s : ℕ) :
    Matrix (Fin m) (Fin n) ℚ := fun i j => roundToGrid (A i j) s

theorem roundEntrywise_entry_abs_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    {s : ℕ} (hs : 0 < s) (i : Fin m) (j : Fin n) :
    |roundEntrywise A s i j| ≤ |A i j| + 1 / (2 * s) := by
  have h : |A i j - roundEntrywise A s i j| ≤ 1 / (2 * s) :=
    abs_sub_roundToGrid (A i j) hs
  calc |roundEntrywise A s i j|
      = |A i j - (A i j - roundEntrywise A s i j)| := by rw [sub_sub_self]
    _ ≤ |A i j| + |A i j - roundEntrywise A s i j| := abs_sub _ _
    _ ≤ |A i j| + 1 / (2 * s) := by linarith

/-- Row L¹ error of the rounded matrix, over `ℚ`: at most `n/(2s)`. -/
theorem roundEntrywise_row_l1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    {s : ℕ} (hs : 0 < s) (i : Fin m) :
    ∑ j, |A i j - roundEntrywise A s i j| ≤ n / (2 * s) := by
  calc ∑ j, |A i j - roundEntrywise A s i j|
      ≤ ∑ _j : Fin n, (1 / (2 * s) : ℚ) :=
        Finset.sum_le_sum (fun j _ => abs_sub_roundToGrid _ hs)
    _ = n / (2 * s) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_one_div]

/-- Row L¹ error of the rounded matrix, over `ℝ`: at most `n/(2s)`. -/
theorem roundEntrywise_row_l1_real {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    {s : ℕ} (hs : 0 < s) (i : Fin m) :
    ∑ j, |(A i j : ℝ) - ((roundEntrywise A s i j : ℚ) : ℝ)| ≤
      (n : ℝ) / (2 * s) := by
  calc ∑ j, |(A i j : ℝ) - ((roundEntrywise A s i j : ℚ) : ℝ)|
      = ((∑ j, |A i j - roundEntrywise A s i j| : ℚ) : ℝ) := by
        rw [Rat.cast_sum]
        apply Finset.sum_congr rfl
        intro j _
        push_cast
        rfl
    _ ≤ (n : ℝ) / (2 * s) := by
        have h := roundEntrywise_row_l1 A hs i
        calc ((∑ j, |A i j - roundEntrywise A s i j| : ℚ) : ℝ)
            ≤ ((n / (2 * s) : ℚ) : ℝ) := by exact_mod_cast h
          _ = (n : ℝ) / (2 * s) := by push_cast; ring

/-- Cast of the exact rational checker quantity to `ℝ` agrees with
`rowValue` under `realSigning` (the cast step inside
`verifySigning_sound`, factored out for reuse). -/
theorem rationalRowValue_cast {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (ε : Fin n → Bool) (i : Fin m) :
    (rationalRowValue A ε i : ℝ) =
      rowValue (fun i j => (A i j : ℝ)) (realSigning ε) i := by
  unfold rowValue rationalRowValue realSigning
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  cases ε j <;> simp

/-- Row values computed on the rounded input differ from the exact row
values by at most `n/(2s)` — direct chaining of the grid bound through
`input_rounding_error`. -/
theorem rounded_verification_margin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    {ε : Fin n → ℝ} (hε : IsSigning ε) {s : ℕ} (hs : 0 < s) (i : Fin m) :
    |rowValue (fun i j => (A i j : ℝ)) ε i -
        rowValue (fun i j => ((roundEntrywise A s i j : ℚ) : ℝ)) ε i| ≤
      (n : ℝ) / (2 * s) :=
  input_rounding_error _ _ hε (fun i => roundEntrywise_row_l1_real A hs i) i

/-- Checking a signing on the rounded input at threshold `T` certifies exact
discrepancy `T + n/(2s)`: the two-sided version of the soundness chain. -/
theorem rounded_threshold_check {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    {ε : Fin n → ℝ} (hε : IsSigning ε) {s : ℕ} (hs : 0 < s) {T : ℝ}
    (hcheck : ∀ i,
      |rowValue (fun i j => ((roundEntrywise A s i j : ℚ) : ℝ)) ε i| ≤ T)
    (i : Fin m) :
    |rowValue (fun i j => (A i j : ℝ)) ε i| ≤ T + (n : ℝ) / (2 * s) := by
  have he := rounded_verification_margin A hε hs i
  have ht : |rowValue (fun i j => (A i j : ℝ)) ε i| ≤
      |rowValue (fun i j => (A i j : ℝ)) ε i -
        rowValue (fun i j => ((roundEntrywise A s i j : ℚ) : ℝ)) ε i| +
      |rowValue (fun i j => ((roundEntrywise A s i j : ℚ) : ℝ)) ε i| := by
    simpa using abs_add_le
      (rowValue (fun i j => (A i j : ℝ)) ε i -
        rowValue (fun i j => ((roundEntrywise A s i j : ℚ) : ℝ)) ε i)
      (rowValue (fun i j => ((roundEntrywise A s i j : ℚ) : ℝ)) ε i)
  linarith [hcheck i]

/-- Verifying on the rounded input at the checker threshold `9899/100`
certifies exact discrepancy `< 99`, provided the grid is fine enough that
`n/(2s) ≤ 1/10000`. This is `accepted_output_sound` instantiated at the
rounded input. -/
theorem verifyRounded_sound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (ε : Fin n → Bool) {s : ℕ} (hs : 0 < s)
    (hprecision : (n : ℝ) / (2 * s) ≤ 1 / 10000)
    (hcheck : ∀ i, |rationalRowValue (roundEntrywise A s) ε i| ≤ 9899 / 100) :
    HasDiscrepancyBelow (fun i j => (A i j : ℝ)) (realSigning ε) 99 := by
  apply accepted_output_sound _ _ (realSigning_isSigning ε)
  · intro i
    exact (roundEntrywise_row_l1_real A hs i).trans hprecision
  · intro i
    have h : |(rationalRowValue (roundEntrywise A s) ε i : ℝ)| ≤
        (9899 / 100 : ℝ) := by
      have hnum : ((9899 / 100 : ℚ) : ℝ) = 9899 / 100 := by norm_num
      rw [← hnum]
      exact_mod_cast hcheck i
    rw [rationalRowValue_cast] at h
    exact h

/-- The grid `s ≥ 5000 · n` suffices: `n/(2s) ≤ 1/10000` whenever
`5000 * n ≤ s`. -/
theorem soundness_precision_suffices {n s : ℕ} (h : 5000 * n ≤ s) :
    (n : ℝ) / (2 * s) ≤ 1 / 10000 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hs : 0 < s := by omega
    have hs' : (0 : ℝ) < 2 * s := by
      have hsc : (0 : ℝ) < s := by exact_mod_cast hs
      linarith
    rw [div_le_iff₀ hs']
    have h' : (n : ℝ) * 10000 ≤ 2 * s := by
      have hnat : 10000 * n ≤ 2 * s := by omega
      calc (n : ℝ) * 10000 = ((10000 * n : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = 2 * (s : ℝ) := by push_cast; ring
    linarith

/-- Same soundness statement with the grid given by the natural-number
hypothesis `5000 * n ≤ s`. -/
theorem verifyRounded_sound_natPrecision {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) (ε : Fin n → Bool) {s : ℕ}
    (hs : 5000 * n ≤ s)
    (hcheck : ∀ i, |rationalRowValue (roundEntrywise A s) ε i| ≤ 9899 / 100) :
    HasDiscrepancyBelow (fun i j => (A i j : ℝ)) (realSigning ε) 99 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨realSigning_isSigning ε, fun i => by simp [rowValue]⟩
  · have hs0 : 0 < s := by omega
    exact verifyRounded_sound A ε hs0 (soundness_precision_suffices hs) hcheck

/-- A binary grid `s = 2^k` with `5000 * n ≤ 2^k` is precise enough for the
soundness margin — the required bit length is `⌈log₂ (5000 n)⌉`. -/
theorem binary_precision_suffices {n k : ℕ} (h : 5000 * n ≤ 2 ^ k) :
    (n : ℝ) / (2 * 2 ^ k) ≤ 1 / 10000 := by
  have h' := soundness_precision_suffices (s := 2 ^ k) h
  push_cast at h' ⊢
  exact h'

/-- The exact rational checker `verifySigning` run on the rounded input
certifies exact discrepancy `< 99 + n/(2s)` on each row. -/
theorem verifySigning_rounded_sound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (ε : Fin n → Bool) {s : ℕ} (hs : 0 < s)
    (h : verifySigning (roundEntrywise A s) ε = true) (i : Fin m) :
    |rowValue (fun i j => (A i j : ℝ)) (realSigning ε) i| <
      99 + (n : ℝ) / (2 * s) := by
  have hcheck : ∀ i', |rationalRowValue (roundEntrywise A s) ε i'| < 99 :=
    of_decide_eq_true h
  have he := rounded_verification_margin A (realSigning_isSigning ε) hs i
  have h99 : |(rationalRowValue (roundEntrywise A s) ε i : ℝ)| < (99 : ℝ) := by
    exact_mod_cast hcheck i
  rw [rationalRowValue_cast] at h99
  have ht : |rowValue (fun i j => (A i j : ℝ)) (realSigning ε) i| ≤
      |rowValue (fun i j => (A i j : ℝ)) (realSigning ε) i -
        rowValue (fun i j => ((roundEntrywise A s i j : ℚ) : ℝ))
          (realSigning ε) i| +
      |rowValue (fun i j => ((roundEntrywise A s i j : ℚ) : ℝ))
        (realSigning ε) i| := by
    simpa using abs_add_le
      (rowValue (fun i j => (A i j : ℝ)) (realSigning ε) i -
        rowValue (fun i j => ((roundEntrywise A s i j : ℚ) : ℝ))
          (realSigning ε) i)
      (rowValue (fun i j => ((roundEntrywise A s i j : ℚ) : ℝ))
        (realSigning ε) i)
  linarith

/-! ## Deterministic transcript coupling -/

/-- One step of the coupling: if two states differ coordinatewise by at most
`δ`, any linear functional driven by coefficients `b` differs by at most
`δ * ‖b‖₁`. -/
theorem step_coupling_bound {n : ℕ} (b x y : Fin n → ℝ) {δ : ℝ}
    (h : ∀ j, |x j - y j| ≤ δ) :
    |∑ j, b j * (x j - y j)| ≤ δ * ∑ j, |b j| := by
  calc |∑ j, b j * (x j - y j)| ≤ ∑ j, |b j * (x j - y j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |b j| * δ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (h j) (abs_nonneg _)
    _ = δ * ∑ j, |b j| := by
        rw [← Finset.sum_mul, mul_comm]

/-- A transcript of `N` coupled steps: the accumulated drift of the same
coefficient sequence evaluated along two state sequences within `δ` is at
most `δ` times the total coefficient mass. -/
theorem transcript_drift_bound {n : ℕ} (b : ℕ → Fin n → ℝ)
    (x y : ℕ → Fin n → ℝ) (N : ℕ) {δ : ℝ}
    (h : ∀ t < N, ∀ j, |x t j - y t j| ≤ δ) :
    |∑ t ∈ Finset.range N, ∑ j, b t j * (x t j - y t j)| ≤
      δ * ∑ t ∈ Finset.range N, ∑ j, |b t j| := by
  calc |∑ t ∈ Finset.range N, ∑ j, b t j * (x t j - y t j)|
      ≤ ∑ t ∈ Finset.range N, |∑ j, b t j * (x t j - y t j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range N, δ * ∑ j, |b t j| :=
        Finset.sum_le_sum
          (fun t ht => step_coupling_bound _ _ _ (h t (Finset.mem_range.mp ht)))
    _ = δ * ∑ t ∈ Finset.range N, ∑ j, |b t j| := (Finset.mul_sum _ _ _).symm

/-- The same coupling with a per-step bound `δ t`. -/
theorem transcript_drift_bound' {n : ℕ} (b : ℕ → Fin n → ℝ)
    (x y : ℕ → Fin n → ℝ) (δ : ℕ → ℝ) (N : ℕ)
    (h : ∀ t < N, ∀ j, |x t j - y t j| ≤ δ t) :
    |∑ t ∈ Finset.range N, ∑ j, b t j * (x t j - y t j)| ≤
      ∑ t ∈ Finset.range N, δ t * ∑ j, |b t j| := by
  calc |∑ t ∈ Finset.range N, ∑ j, b t j * (x t j - y t j)|
      ≤ ∑ t ∈ Finset.range N, |∑ j, b t j * (x t j - y t j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range N, δ t * ∑ j, |b t j| :=
        Finset.sum_le_sum
          (fun t ht => step_coupling_bound _ _ _ (h t (Finset.mem_range.mp ht)))

/-- If the total coefficient mass is at most `B`, the drift is at most
`δ * B`. -/
theorem transcript_drift_of_total {n : ℕ} (b : ℕ → Fin n → ℝ)
    (x y : ℕ → Fin n → ℝ) (N : ℕ) {δ B : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ t < N, ∀ j, |x t j - y t j| ≤ δ)
    (hB : ∑ t ∈ Finset.range N, ∑ j, |b t j| ≤ B) :
    |∑ t ∈ Finset.range N, ∑ j, b t j * (x t j - y t j)| ≤ δ * B :=
  (transcript_drift_bound b x y N h).trans
    (mul_le_mul_of_nonneg_left hB hδ)

/-- Two affine tracked values with the same data, evaluated at different
points, differ exactly by the linear functional of the state difference. -/
theorem affineValue_sub_eval {n : ℕ} (c : ℝ) (b x y : Fin n → ℝ) :
    affineValue c b x - affineValue c b y = ∑ j, b j * (x j - y j) := by
  unfold affineValue
  have hsum : ∑ j, (b j * x j - b j * y j) = ∑ j, b j * (x j - y j) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [← hsum, Finset.sum_sub_distrib]
  ring

/-- The affine tracked quantities of two transcripts driven by the same
coefficient sequences drift by at most `δ *` total coefficient mass. -/
theorem coupled_affine_transcript_drift {n : ℕ} (c : ℕ → ℝ)
    (b : ℕ → Fin n → ℝ) (x y : ℕ → Fin n → ℝ) (N : ℕ) {δ : ℝ}
    (h : ∀ t < N, ∀ j, |x t j - y t j| ≤ δ) :
    |∑ t ∈ Finset.range N,
        (affineValue (c t) (b t) (x t) - affineValue (c t) (b t) (y t))| ≤
      δ * ∑ t ∈ Finset.range N, ∑ j, |b t j| := by
  simp_rw [affineValue_sub_eval]
  exact transcript_drift_bound b x y N h

/-- One-step defect when the offset, the coefficients and the evaluation
point all change: the offset defect plus the coefficient change applied to
`x` plus the new coefficients applied to `x - y`. -/
theorem step_affine_coupling {n : ℕ} (c c' : ℝ) (b b' x y : Fin n → ℝ) :
    affineValue c b x - affineValue c' b' y =
      (c - c') + ∑ j, (b j - b' j) * x j + ∑ j, b' j * (x j - y j) := by
  unfold affineValue
  have hsum : ∑ j, (b j - b' j) * x j + ∑ j, b' j * (x j - y j) =
      ∑ j, (b j * x j - b' j * y j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [add_assoc, hsum, Finset.sum_sub_distrib]
  ring

/-- Bound form of `step_affine_coupling` for cube-valued `x`: the defect is
at most `|c - c'| + δb * n + δ * ‖b'‖₁`. -/
theorem step_affine_coupling_bound {n : ℕ} (c c' : ℝ) (b b' x y : Fin n → ℝ)
    {δ δb : ℝ} (hx : ∀ j, |x j| ≤ 1)
    (hxy : ∀ j, |x j - y j| ≤ δ) (hbb : ∀ j, |b j - b' j| ≤ δb) :
    |affineValue c b x - affineValue c' b' y| ≤
      |c - c'| + δb * n + δ * ∑ j, |b' j| := by
  rw [step_affine_coupling]
  have h1 : |∑ j, (b j - b' j) * x j| ≤ δb * n := by
    calc |∑ j, (b j - b' j) * x j| ≤ ∑ j, |(b j - b' j) * x j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, δb * 1 := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          exact mul_le_mul (hbb j) (hx j) (abs_nonneg _)
            (le_trans (abs_nonneg _) (hbb j))
      _ = δb * n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
  have h2 : |∑ j, b' j * (x j - y j)| ≤ δ * ∑ j, |b' j| :=
    step_coupling_bound b' x y hxy
  calc |(c - c') + ∑ j, (b j - b' j) * x j + ∑ j, b' j * (x j - y j)|
      ≤ |c - c'| + |∑ j, (b j - b' j) * x j| +
          |∑ j, b' j * (x j - y j)| := by
        have h3 := abs_add_le ((c - c') + ∑ j, (b j - b' j) * x j)
          (∑ j, b' j * (x j - y j))
        have h4 := abs_add_le (c - c') (∑ j, (b j - b' j) * x j)
        linarith
    _ ≤ |c - c'| + δb * n + δ * ∑ j, |b' j| := by linarith

/-- Deletion-direction drift with a general proximity bound `δ`: under the
deletion-charge hypotheses (the same `q`/`b` bookkeeping as
`total_deleted_coefficient_bound`), two scalar transcripts within `δ`
differ by at most `δ * (291/200) * (8 + √63)` along the deleted direction.
`deleted_defect_bound` is the `δ = 2` special case via
`cube_difference_abs_le_two`. -/
theorem coupled_deleted_drift (q b x y : ℕ → ℝ) (N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hremove : ∀ t < N, (b t) ^ 2 ≤ q t)
    (hdelete : ∀ t < N, q t / 64 < (b t) ^ 2)
    (hnext : ∀ t < N, q (t + 1) ≤ q t - (b t) ^ 2)
    (hdrift : ∀ t < N, |y t - x t| ≤ δ)
    (hq0 : q 0 ≤ (291 / 200) ^ 2) :
    |∑ t ∈ Finset.range N, b t * (y t - x t)| ≤
      δ * (291 / 200) * (8 + Real.sqrt 63) := by
  have hsqrt : Real.sqrt (q 0) ≤ 291 / 200 := by
    calc
      Real.sqrt (q 0) ≤ Real.sqrt ((291 / 200 : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt hq0
      _ = 291 / 200 := by rw [Real.sqrt_sq (by norm_num)]
  have hcoeff := total_deleted_coefficient_bound q b N hremove hdelete hnext
  have hK : 0 ≤ 8 + Real.sqrt 63 := by positivity
  calc
    |∑ t ∈ Finset.range N, b t * (y t - x t)| ≤
        ∑ t ∈ Finset.range N, |b t * (y t - x t)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range N, δ * |b t| := by
      apply Finset.sum_le_sum
      intro t ht
      rw [abs_mul]
      have h1 := mul_le_mul_of_nonneg_left
        (hdrift t (Finset.mem_range.mp ht)) (abs_nonneg (b t))
      linarith
    _ = δ * ∑ t ∈ Finset.range N, |b t| := (Finset.mul_sum _ _ _).symm
    _ ≤ δ * ((8 + Real.sqrt 63) * Real.sqrt (q 0)) :=
      mul_le_mul_of_nonneg_left hcoeff hδ
    _ ≤ δ * (291 / 200) * (8 + Real.sqrt 63) := by
      have h := mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hδ hK)
      linarith

/-- The tracked `energy` is `2δ`-Lipschitz in the state on the unit cube,
per unit of total weight: states within `δ` coordinatewise give energy
within `2δ * ∑ p`. -/
theorem energy_drift_bound {n : ℕ} (p x y : Fin n → ℝ) {δ : ℝ}
    (hp : ∀ j, 0 ≤ p j) (hx : ∀ j, |x j| ≤ 1) (hy : ∀ j, |y j| ≤ 1)
    (h : ∀ j, |x j - y j| ≤ δ) :
    |energy p x - energy p y| ≤ 2 * δ * ∑ j, p j := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp [energy]
  · have hδnn : 0 ≤ δ := le_trans (abs_nonneg _) (h ⟨0, hn0⟩)
    have hdecomp : energy p x - energy p y =
        ∑ j, p j * ((y j) ^ 2 - (x j) ^ 2) := by
      unfold energy
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hdecomp]
    calc |∑ j, p j * (y j ^ 2 - x j ^ 2)|
        ≤ ∑ j, |p j * (y j ^ 2 - x j ^ 2)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, p j * (2 * δ) := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul, abs_of_nonneg (hp j)]
          have hsq : |y j ^ 2 - x j ^ 2| = |y j - x j| * |y j + x j| := by
            rw [← abs_mul]
            congr 1
            ring
          have hsum : |y j + x j| ≤ 2 := by
            have hadd := abs_add_le (y j) (x j)
            linarith [hx j, hy j]
          have hd : |y j - x j| ≤ δ := by rw [abs_sub_comm]; exact h j
          have h2 : |y j - x j| * |y j + x j| ≤ δ * 2 :=
            mul_le_mul hd hsum (abs_nonneg _) hδnn
          rw [hsq]
          have h3 := mul_le_mul_of_nonneg_left h2 (hp j)
          linarith
      _ = 2 * δ * ∑ j, p j := by
          rw [← Finset.sum_mul]
          ring

/-- The tracked `barrier` is Lipschitz in `(d, G)` with constants
`1/r` and `4/r²`: displacements `|d' - d| ≤ δd`, `|G' - G| ≤ δG` move the
barrier by at most `δd/r + 4δG/r²`. -/
theorem barrier_drift_bound {σ d d' r G G' : ℝ} (hr : 0 < r) (hσ : |σ| = 1)
    {δd δG : ℝ} (hd : |d' - d| ≤ δd) (hG' : |G' - G| ≤ δG) :
    |barrier σ d' r G' - barrier σ d r G| ≤ δd / r + 4 * δG / r ^ 2 := by
  have hincr := barrier_increment σ d r G (d' - d) (G' - G)
  rw [show d + (d' - d) = d' by ring, show G + (G' - G) = G' by ring] at hincr
  rw [hincr]
  have h1 : |σ * (d' - d) / r| ≤ δd / r := by
    rw [abs_div, abs_of_nonneg hr.le, abs_mul, hσ, one_mul]
    exact (div_le_div_iff_of_pos_right hr).mpr hd
  have h2 : |4 * (G' - G) / r ^ 2| ≤ 4 * δG / r ^ 2 := by
    have habs : |4 * (G' - G)| = 4 * |G' - G| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    have hbound : |4 * (G' - G)| ≤ 4 * δG := by
      rw [habs]
      exact mul_le_mul_of_nonneg_left hG' (by norm_num)
    rw [abs_div, abs_of_nonneg (sq_nonneg r)]
    exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hr)).mpr hbound
  linarith [abs_add_le (σ * (d' - d) / r) (4 * (G' - G) / r ^ 2)]

/-- Rounding every state to the grid `1/s` couples a transcript to its
dithered image: the drift is at most `(1/(2s)) *` total coefficient mass. -/
theorem rounded_transcript_drift {n : ℕ} (b : ℕ → Fin n → ℝ)
    (x : ℕ → Fin n → ℝ) (N : ℕ) {s : ℕ} (hs : 0 < s) :
    |∑ t ∈ Finset.range N, ∑ j,
        b t j * (x t j - roundToGridR (x t j) s)| ≤
      (1 / (2 * s)) * ∑ t ∈ Finset.range N, ∑ j, |b t j| := by
  apply transcript_drift_bound b x (fun t j => roundToGridR (x t j) s) N
  intro t _ j
  exact abs_sub_roundToGridR _ hs

/-! ## Precision-sufficiency bookkeeping -/

/-- To force `n/(2s) ≤ ε` it suffices that `2 * s * ε ≥ n`: the rounding
bound solved for the grid. -/
theorem grid_precision_suffices {n s : ℕ} {ε : ℝ} (hs : 0 < s)
    (h : (n : ℝ) ≤ 2 * s * ε) : (n : ℝ) / (2 * s) ≤ ε := by
  have hs' : (0 : ℝ) < 2 * s := by
    have hsc : (0 : ℝ) < s := by exact_mod_cast hs
    linarith
  rw [div_le_iff₀ hs']
  linarith

/-- ℕ-valued version: `n ≤ 2 * s * k` implies `n/(2s) ≤ k`. -/
theorem grid_precision_suffices_nat {n s k : ℕ} (h : n ≤ 2 * s * k) :
    (n : ℝ) / (2 * s) ≤ k := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  · have h' : (n : ℝ) ≤ 2 * (s : ℝ) * (k : ℝ) := by exact_mod_cast h
    exact grid_precision_suffices hs h'

end Komlos
