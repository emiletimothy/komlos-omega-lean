/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Komlos.TrialConcentration

/-!
# Markov and counting bounds over the uniform signing measure

This file closes the trial-concentration argument of
`Komlos/TrialConcentration.lean` by proving **Markov's inequality** for the
uniform probability measure on the `2 ^ n` sign vectors `ε : Fin n → Bool`
(the paper's signing sampler) and the counting corollaries that extract a
successful trial from it.

## Main results

* `card_univ_signing`: there are exactly `2 ^ n` sign vectors, as a real count.
* `signAvg_markov`: for pointwise-nonnegative `f` with `signAvg f ≤ B` and
  `0 < T`, the number of signings with `T * B < f ε` is at most
  `univ.card / T` — at most a `1 / T` fraction of all `2 ^ n` signings.
  Proved directly:
  `T * B * #bad ≤ ∑_{bad} f ≤ ∑_{all} f = 2 ^ n · signAvg f ≤ 2 ^ n · B`.
* `bad_signing_fraction_le`: the same statement instantiated at
  `f ε = badRowCount A T (realSigning ε)` via `signAvg_badRowCount_le` — the
  fraction of signings with more than `p * (n / T²)` bad rows is at most `1 / p`.
* `exists_good_signing`: the averaging pigeonhole — if `signAvg f ≤ B` then
  some signing satisfies `f ε ≤ B`.
* `good_signing_set_nonempty`: for `1 < p` the bad fraction `≤ 1 / p < 1`, so
  some signing has at most `p * (n / T²)` bad rows.

No measure theory is needed: every statement is a finite `Finset.univ`
argument over the `Fintype` `Fin n → Bool`.
-/

namespace Komlos

open scoped BigOperators

/-- `2 ^ n` is never zero as a real number. -/
private theorem two_pow_ne_zero (n : ℕ) : (2 : ℝ) ^ n ≠ 0 :=
  pow_ne_zero _ (by norm_num)

/-- The cube of sign vectors `ε : Fin n → Bool` has exactly `2 ^ n` elements,
as a real number. -/
theorem card_univ_signing (n : ℕ) :
    ((Finset.univ : Finset (Fin n → Bool)).card : ℝ) = (2 : ℝ) ^ n := by
  have h : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [h]
  simp

/-- **Markov's inequality** for the uniform sign average: if `0 ≤ f` pointwise
and `signAvg f ≤ B`, then at most `univ.card / T` signings satisfy
`T * B < f ε`. The `B = 0` case is handled separately (then `f ≡ 0` and the
bad set is empty); for `0 < B` one cancels `B` from
`T * B * #bad ≤ 2 ^ n * B`. -/
theorem signAvg_markov {n : ℕ} {f : (Fin n → Bool) → ℝ} {B : ℝ}
    (hf : ∀ ε, 0 ≤ f ε) (havg : signAvg f ≤ B) {T : ℝ} (hT : 0 < T) :
    ((Finset.univ.filter fun ε : Fin n → Bool => T * B < f ε).card : ℝ) ≤
      ((Finset.univ : Finset (Fin n → Bool)).card : ℝ) / T := by
  set S : Finset (Fin n → Bool) :=
    Finset.univ.filter fun ε : Fin n → Bool => T * B < f ε with hS
  have h2n : (2 : ℝ) ^ n ≠ 0 := two_pow_ne_zero n
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hsum_nn : 0 ≤ ∑ ε : Fin n → Bool, f ε :=
    Finset.sum_nonneg fun ε _ => hf ε
  have havg_nn : 0 ≤ signAvg f := by
    rw [signAvg]
    exact div_nonneg hsum_nn h2.le
  have hB : 0 ≤ B := havg_nn.trans havg
  -- The key counting inequality `T * B * #S ≤ 2 ^ n * B`.
  have hkey : T * B * (S.card : ℝ) ≤ (2 : ℝ) ^ n * B := by
    calc T * B * (S.card : ℝ)
        = ∑ _ε ∈ S, T * B := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
      _ ≤ ∑ ε ∈ S, f ε :=
            Finset.sum_le_sum fun ε hε =>
              le_of_lt (Finset.mem_filter.mp hε).2
      _ ≤ ∑ ε : Fin n → Bool, f ε :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun a _ _ => hf a
      _ ≤ (2 : ℝ) ^ n * B := by
            rw [← div_le_iff₀' h2]
            exact havg
  rcases hB.eq_or_lt with hB0 | hBpos
  · -- `B = 0`: `signAvg f = 0`, so `f ≡ 0` and the bad set is empty.
    subst hB0
    have havg0 : signAvg f = 0 := le_antisymm havg havg_nn
    have hsum0 : ∑ ε : Fin n → Bool, f ε = 0 := by
      rw [signAvg, div_eq_zero_iff] at havg0
      rcases havg0 with h | h
      · exact h
      · exact absurd h h2n
    have hall : ∀ ε : Fin n → Bool, f ε = 0 := fun ε =>
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hf i).mp hsum0 ε
        (Finset.mem_univ ε)
    have hS0 : S = ∅ := by
      rw [hS, Finset.eq_empty_iff_forall_notMem]
      intro ε hε
      have hlt := (Finset.mem_filter.mp hε).2
      rw [mul_zero, hall ε] at hlt
      exact lt_irrefl _ hlt
    rw [hS0, Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (Nat.cast_nonneg _) hT.le
  · -- `0 < B`: cancel `B` from `T * B * #S ≤ 2 ^ n * B`.
    have hkey' : T * (S.card : ℝ) * B ≤ (2 : ℝ) ^ n * B := by
      rwa [mul_right_comm] at hkey
    have hTcard : T * (S.card : ℝ) ≤ (2 : ℝ) ^ n :=
      le_of_mul_le_mul_right hkey' hBpos
    rw [card_univ_signing n, le_div_iff₀' hT]
    exact hTcard

/-- **Bad-signing fraction bound**: the fraction of the `2 ^ n` signings whose
bad-row count `badRowCount A T (realSigning ε)` exceeds `p` times its expected
bound `n / T²` is at most `1 / p`. This is `signAvg_markov` instantiated at
`f ε = badRowCount A T (realSigning ε)` and `B = n / T²`, using
`signAvg_badRowCount_le`. -/
theorem bad_signing_fraction_le {m n : ℕ} {A : Input m n}
    (hA : ColumnNormalized A) {T p : ℝ} (hT : 0 < T) (hp : 0 < p) :
    ((Finset.univ.filter fun ε : Fin n → Bool =>
          p * ((n : ℝ) / T ^ 2) < badRowCount A T (realSigning ε)).card : ℝ) /
        (2 : ℝ) ^ n ≤ 1 / p := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hmarkov := signAvg_markov (n := n)
    (f := fun ε : Fin n → Bool => badRowCount A T (realSigning ε))
    (B := (n : ℝ) / T ^ 2) (hf := fun ε => Nat.cast_nonneg _)
    (havg := signAvg_badRowCount_le hA hT) (hT := hp)
  rw [card_univ_signing n] at hmarkov
  rw [div_le_iff₀ h2]
  exact hmarkov.trans_eq (by ring)

/-- **Averaging pigeonhole**: if `signAvg f ≤ B` then at least one signing
satisfies `f ε ≤ B` — otherwise every term of the average would exceed `B`. -/
theorem exists_good_signing {n : ℕ} {f : (Fin n → Bool) → ℝ} {B : ℝ}
    (havg : signAvg f ≤ B) : ∃ ε : Fin n → Bool, f ε ≤ B := by
  have hsum : ∑ ε : Fin n → Bool, f ε ≤ ∑ _ε : Fin n → Bool, B := by
    rw [Finset.sum_const, nsmul_eq_mul, card_univ_signing,
      ← div_le_iff₀' (pow_pos (by norm_num : (0 : ℝ) < 2) n)]
    exact havg
  obtain ⟨ε, _, hε⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨ε, hε⟩

/-- **The good-signing set is nonempty** (the `1 / p < 1` form of
`bad_signing_fraction_le`): for `1 < p`, strictly less than all of the
`2 ^ n` signings can have more than `p * (n / T²)` bad rows, so some signing
has at most `p * (n / T²)` bad rows. -/
theorem good_signing_set_nonempty {m n : ℕ} {A : Input m n}
    (hA : ColumnNormalized A) {T p : ℝ} (hT : 0 < T) (hp : 1 < p) :
    ∃ ε : Fin n → Bool,
      badRowCount A T (realSigning ε) ≤ p * ((n : ℝ) / T ^ 2) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hfrac := bad_signing_fraction_le hA hT hp0
  have h1p : (1 : ℝ) / p < 1 := (div_lt_one hp0).mpr hp
  have hcardlt : ((Finset.univ.filter fun ε : Fin n → Bool =>
          p * ((n : ℝ) / T ^ 2) < badRowCount A T (realSigning ε)).card : ℝ) <
        (2 : ℝ) ^ n := by
    have hlt := lt_of_le_of_lt hfrac h1p
    rw [div_lt_iff₀ h2, one_mul] at hlt
    exact hlt
  obtain ⟨ε, hε⟩ : ∃ ε : Fin n → Bool,
      ε ∉ Finset.univ.filter (fun ε : Fin n → Bool =>
        p * ((n : ℝ) / T ^ 2) < badRowCount A T (realSigning ε)) := by
    by_contra hcon
    have hmem : ∀ ε : Fin n → Bool, ε ∈ Finset.univ.filter
        (fun ε : Fin n → Bool =>
          p * ((n : ℝ) / T ^ 2) < badRowCount A T (realSigning ε)) := fun ε => by
      by_contra h
      exact hcon ⟨ε, h⟩
    rw [Finset.eq_univ_iff_forall.mpr hmem, card_univ_signing n] at hcardlt
    exact lt_irrefl _ hcardlt
  exact ⟨ε, not_lt.mp fun hlt =>
    hε (Finset.mem_filter.mpr ⟨Finset.mem_univ ε, hlt⟩)⟩

end Komlos
