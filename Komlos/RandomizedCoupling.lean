/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Komlos.TrialConcentration
import Komlos.FinitePrecision
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Randomized coupling: the dithered transcript is a martingale

`Komlos/FinitePrecision.lean` proves the *deterministic* half of the
finite-precision coupling: rounding every state to the grid `1/s` couples a
transcript to its dithered image with worst-case drift at most `(1/2s)` times
the total coefficient mass. The paper actually couples *randomized*
roundings — the dithered transcript is a martingale whose increments are
controlled with high probability. This file supplies a finite, fully
explicit probability model of that randomized rounding and proves the
martingale/variance facts that do not need a measure-theoretic walk model.

## The probability model

Following `Komlos/TrialConcentration.lean`, randomness is a uniform average
`unifAvg f = (∑ a, f a) / card ι` over a finite type `ι` of coin flips —
for `ι = Fin n → Bool` this is exactly `signAvg` (`signAvg_eq_unifAvg`).

* `ditherRound x s ε` (`ε : Bool`) is the fair two-point rounding:
  `floorToGrid` on `false`, `ceilToGrid` on `true`. Its average over the
  coin is `(⌊x·s⌋ + ⌈x·s⌉)/(2s)`, exactly `x` when `x·s` is integral or
  half-integral and always within `1/(2s)` of `x`
  (`abs_boolDither_avg_sub`). This is the "cheap" version: unbiased only on
  the half-grid.
* `ditherRoundN x s N c` (`c : Fin Q`) is the exact randomized rounding:
  round up when `c.val < N`. When `N = Q·Int.fract (x·s)` — integrality is
  the hypothesis `hN` of `unifAvg_ditherRoundN` — the coin `c` is a uniform
  `Fin Q` draw realizing "round up with probability `Int.fract (x·s)`",
  so `E_c[ditherRoundN] = x` for *every* rational `x`
  (`unifAvg_ditherRoundN`). A uniform `Q` exists whenever every
  `(x i·s).den` divides `Q` (`dither_compatible_of_den_dvd`), e.g. `Q`
  a common denominator of all scaled states.

## What is proved unconditionally

* `unifAvg_ditherRoundN`, `sum_ditherErr`: the dithered rounding is
  unbiased — each martingale increment `ditherErr` is mean-zero.
* `unifAvg_ditherErr_sq`, `unifAvg_ditherErr_sq_le`: the single-step
  variance is `fract·(1 - fract)/s² ≤ (1/(2s))²`.
* `incSum_snoc`, `sum_incSum_fresh_coin`, `unifAvg_incSum_fresh_coin`:
  peeling the last coin is exactly conditional expectation — the
  elementary martingale property
  `E[M_{k+1} | first k coins] = M_k`.
* `unifAvg_incSum_eq_zero`, `unifAvg_incSum_sq`: for any family of
  mean-zero increments, `E[∑ ξᵢ(εᵢ)] = 0` and
  `E[(∑ ξᵢ(εᵢ))²] = ∑ E[ξᵢ²]` — independence kills the cross terms via
  the same coin-peeling recursion, no pairing argument needed.
* `unifAvg_ditherWalk`, `unifAvg_ditherWalk_sq`,
  `unifAvg_ditherWalk_sq_le`: the dithered partial sum
  `D_t = ∑ᵢ (ditherᵢ(εᵢ) - xᵢ)` satisfies `E[D_t] = 0` and
  `E[D_t²] = (1/s²)·∑ᵢ pᵢ(1-pᵢ) ≤ t·(1/(2s))²` where `pᵢ = Int.fract(xᵢ·s)`.
* `unifAvg_ditherWalk_conditional`: for every history `η`,
  `E_c[D_{k+1}(snoc η c)] = D_k(η)` — the martingale property, literally.
* `ditherWalk_tail_le`: Markov/Chebyshev in the finite model,
  `Pr[|D_t| ≥ u] ≤ t·(1/(2s))²/u²`, via
  `sq_mul_filter_card_le_sum_sq` from `TrialConcentration`.
* `unifAvg_transcriptDrift`, `transcriptDrift_sq_le`,
  `transcriptDrift_sq`: the stochastic strengthening of
  `transcript_drift_bound`/`rounded_transcript_drift` from
  `FinitePrecision.lean`: for coefficient sequence `b` and state sequence
  `x`, the dithered drift `drift(ε) = ∑ b·(x - dither(x, ε))` satisfies
  `E[drift] = 0` and
  `E[drift²] = (1/s²)·∑₍ₜ,ⱼ₎ (b t j)²·p_{tj}(1-p_{tj})
   ≤ (1/(2s))²·∑₍ₜ,ⱼ₎ (b t j)²` — expected squared drift at most
  `(1/2s)²` times the *squared* coefficient mass (compare the
  deterministic `≤ (1/2s)·∑|b|`). `transcriptDrift_tail_le` gives the
  Chebyshev tail `Pr[|drift| ≥ u] ≤ (1/(2s))²·∑b²/u²`.
* `abs_transcriptDrift_le`: the pointwise sanity check
  `|drift(ε)| ≤ (1/s)·∑|b|` — the randomized bound strictly refines the
  deterministic one (worst case `1/s` per step vs. variance `(1/2s)²`).

## What is NOT proved here

* A Hoeffding/Azuma exponential tail is *not* formalized: the finite
  model has no `exp`-moment machinery, and proving
  `E[e^{λδ}] ≤ e^{λ²/(8s²)}` for the two-point increment needs real
  convexity estimates out of scope here. The concentration supplied is
  the second-moment (Chebyshev) bound `O(t/s²u²)`, plus the exact
  variance identities.
* The integrality side condition `Q·Int.fract(x·s) = N` is the honest
  finite-model content of "flip a Bernoulli(`fract`) coin": exact
  unbiasedness is only available when the fractional part lands on the
  `1/Q` grid. `dither_compatible_of_den_dvd` shows this is automatic once
  `(x·s).den | Q`; for a transcript, a common `Q` always exists (e.g. the
  product of all state denominators times nothing extra — each
  `(x·s).den | x.den`, `rat_scaled_den_dvd`). The fair `Bool` coin
  `ditherRound` is unbiased only on the half-grid (bias `≤ 1/(2s)`,
  `abs_boolDither_avg_sub`) — the `Fin Q` model is the correct one.
* As in `FinitePrecision.lean`, the *adaptive* statement (the increments
  `xᵢ` themselves depending on past coins, and the high-probability
  coupling of the maintained state) needs a filtration; the finite model
  proves the marginal martingale/variance facts for a fixed increment
  family, which is the part the paper's dithered-transcript drift
  estimate uses.
-/

namespace Komlos

open scoped BigOperators

/-! ## The uniform average on an arbitrary finite type -/

/-- Uniform average over a finite type: `unifAvg f = (∑ a, f a) / card ι`.
This is the finite probability model for the randomized rounding, the
direct generalization of `signAvg` (which is `ι = Fin n → Bool`). -/
noncomputable def unifAvg {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℝ :=
  (∑ a, f a) / (Fintype.card ι : ℝ)

theorem unifAvg_zero {ι : Type*} [Fintype ι] :
    unifAvg (fun _ : ι => (0 : ℝ)) = 0 := by
  rw [unifAvg, Finset.sum_const_zero, zero_div]

theorem unifAvg_const {ι : Type*} [Fintype ι] [Nonempty ι] (c : ℝ) :
    unifAvg (fun _ : ι => c) = c := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  rw [unifAvg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hcard

theorem unifAvg_add {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    unifAvg (fun a => f a + g a) = unifAvg f + unifAvg g := by
  rw [unifAvg, unifAvg, unifAvg, Finset.sum_add_distrib, add_div]

theorem unifAvg_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (g : κ → ι → ℝ) :
    unifAvg (fun a => ∑ k, g k a) = ∑ k, unifAvg (g k) := by
  rw [unifAvg, Finset.sum_comm, Finset.sum_div]
  exact Finset.sum_congr rfl fun k _ => rfl

theorem unifAvg_mul_left {ι : Type*} [Fintype ι] (c : ℝ) (f : ι → ℝ) :
    unifAvg (fun a => c * f a) = c * unifAvg f := by
  rw [unifAvg, unifAvg, ← Finset.mul_sum, mul_div_assoc]

theorem unifAvg_neg {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    unifAvg (fun a => -f a) = -unifAvg f := by
  rw [unifAvg, unifAvg, Finset.sum_neg_distrib, neg_div]

theorem unifAvg_sub_const {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ)
    (c : ℝ) :
    unifAvg (fun a => f a - c) = unifAvg f - c := by
  have h := unifAvg_add f (fun _ => -c)
  simp_rw [sub_eq_add_neg] at h ⊢
  rw [h, unifAvg_const]

/-- A zero uniform average has zero total. -/
theorem sum_eq_zero_of_unifAvg {ι : Type*} [Fintype ι]
    (hcard : (Fintype.card ι : ℝ) ≠ 0) {f : ι → ℝ} (h : unifAvg f = 0) :
    ∑ a, f a = 0 := by
  have key : ∑ a, f a = unifAvg f * (Fintype.card ι : ℝ) := by
    rw [unifAvg, div_mul_cancel₀ _ hcard]
  rw [key, h, zero_mul]

/-- The uniform sign model of `TrialConcentration` is a special case of
`unifAvg`: `card (Fin n → Bool) = 2ⁿ`. -/
theorem signAvg_eq_unifAvg {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    signAvg f = unifAvg f := by
  rw [signAvg, unifAvg, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  norm_cast

/-- The cardinality of `k`-tuples over `C`. -/
theorem card_piFin {C : Type*} [Fintype C] (k : ℕ) :
    Fintype.card (Fin k → C) = Fintype.card C ^ k := by
  rw [Fintype.card_fun, Fintype.card_fin]

/-! ## Ceiling rounding to the grid -/

/-- Round `x : ℚ` *up* to the grid `1/s`, i.e. `⌈x * s⌉ / s` — the upward
partner of `floorToGrid`. -/
def ceilToGrid (x : ℚ) (s : ℕ) : ℚ := (⌈x * s⌉ : ℚ) / s

theorem le_ceilToGrid (x : ℚ) {s : ℕ} (hs : 0 < s) : x ≤ ceilToGrid x s := by
  have hs' : (0 : ℚ) < s := by exact_mod_cast hs
  calc x = (x * s) / s := (mul_div_cancel_right₀ x hs'.ne').symm
    _ ≤ (⌈x * s⌉ : ℚ) / s :=
        (div_le_div_iff_of_pos_right hs').mpr (Int.le_ceil _)

theorem ceilToGrid_sub_lt (x : ℚ) {s : ℕ} (hs : 0 < s) :
    ceilToGrid x s - x < 1 / s := by
  have hs' : (0 : ℚ) < s := by exact_mod_cast hs
  have h : ceilToGrid x s - x = (⌈x * s⌉ - x * s) / s := by
    unfold ceilToGrid
    rw [div_sub' hs'.ne']
    ring_nf
  rw [h]
  have h2 : (⌈x * s⌉ : ℚ) - x * s < 1 := by
    have h3 := Int.ceil_lt_add_one (x * s)
    linarith
  exact (div_lt_div_iff_of_pos_right hs').mpr (by linarith)

/-- The one-sided ceil error gives the two-sided bound `1/s`. -/
theorem abs_sub_ceilToGrid (x : ℚ) {s : ℕ} (hs : 0 < s) :
    |x - ceilToGrid x s| ≤ 1 / s := by
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (le_ceilToGrid x hs))]
  exact (ceilToGrid_sub_lt x hs).le

/-- On non-grid points the ceil rounding is the floor rounding plus one
grid step. -/
theorem ceilToGrid_eq_floorToGrid_add (x : ℚ) (s : ℕ)
    (h : Int.fract (x * s) ≠ 0) :
    ceilToGrid x s = floorToGrid x s + 1 / s := by
  have hnotint : x * s ∉ Set.range (Int.cast : ℤ → ℚ) :=
    (Int.fract_eq_zero_iff.not).mp h
  have hceil : ⌈x * s⌉ = ⌊x * s⌋ + 1 :=
    (Int.ceil_eq_floor_add_one_iff_notMem _).mpr hnotint
  unfold ceilToGrid floorToGrid
  rw [hceil]
  push_cast
  rw [add_div]

/-- On grid points ceil and floor rounding coincide. -/
theorem ceilToGrid_eq_floorToGrid (x : ℚ) (s : ℕ)
    (h : Int.fract (x * s) = 0) :
    ceilToGrid x s = floorToGrid x s := by
  obtain ⟨z, hz⟩ := Int.fract_eq_zero_iff.mp h
  unfold ceilToGrid floorToGrid
  rw [← hz, Int.ceil_intCast, Int.floor_intCast]

/-! ## The fair-coin dither `ditherRound` -/

/-- The fair-coin (unweighted) dithered rounding: `ε = false` rounds down,
`ε = true` rounds up to the `1/s` grid. This is a true randomized rounding
but it is unbiased only when `x·s` is integral or half-integral; see
`boolDither_avg`/`abs_boolDither_avg_sub`. The exactly-unbiased version
is `ditherRoundN`. -/
def ditherRound (x : ℚ) (s : ℕ) (ε : Bool) : ℚ :=
  if ε then ceilToGrid x s else floorToGrid x s

/-- Every fair-coin dither output is within `1/s` of `x`. -/
theorem abs_sub_ditherRound (x : ℚ) {s : ℕ} (hs : 0 < s) (ε : Bool) :
    |x - ditherRound x s ε| ≤ 1 / s := by
  cases ε
  · exact abs_sub_floorToGrid x hs
  · exact abs_sub_ceilToGrid x hs

/-- The fair-coin average of the dither is the midpoint of the two grid
neighbors: `E_ε[ditherRound x s ε] = (⌊x·s⌋ + ⌈x·s⌉)/(2s)`. -/
theorem boolDither_avg (x : ℚ) (s : ℕ) :
    ((ditherRound x s false + ditherRound x s true : ℚ) / 2 : ℝ) =
      ((⌊x * s⌋ + ⌈x * s⌉ : ℚ) / (2 * s) : ℝ) := by
  show ((floorToGrid x s + ceilToGrid x s : ℚ) / 2 : ℝ) = _
  unfold ceilToGrid floorToGrid
  push_cast
  ring

/-- The fair-coin dither is unbiased up to half a grid cell:
`|E_ε[ditherRound] - x| ≤ 1/(2s)`, with equality only off the half-grid. -/
theorem abs_boolDither_avg_sub (x : ℚ) {s : ℕ} (hs : 0 < s) :
    |((ditherRound x s false + ditherRound x s true : ℚ) / 2 : ℝ) - (x : ℝ)| ≤
      1 / (2 * s) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  rw [boolDither_avg]
  have hcast : ((⌊x * s⌋ + ⌈x * s⌉ : ℚ) / (2 * s) : ℝ) =
      ((⌊(x : ℝ) * s⌋ + ⌈(x : ℝ) * s⌉ : ℝ)) / (2 * s) := by
    have h1 : ((x * s : ℚ) : ℝ) = (x : ℝ) * s := by norm_cast
    push_cast
    rw [← h1, Rat.floor_cast, Rat.ceil_cast]
  rw [hcast]
  have hle : (⌊(x : ℝ) * s⌋ : ℝ) ≤ (x : ℝ) * s := Int.floor_le _
  have hge : (x : ℝ) * s ≤ (⌈(x : ℝ) * s⌉ : ℝ) := Int.le_ceil _
  have hgap : (⌈(x : ℝ) * s⌉ : ℝ) ≤ (⌊(x : ℝ) * s⌋ : ℝ) + 1 := by
    have h := Int.ceil_le_floor_add_one ((x : ℝ) * s)
    exact_mod_cast h
  have hbound : |(⌊(x : ℝ) * s⌋ : ℝ) + ⌈(x : ℝ) * s⌉ - 2 * (x * s)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [show ((⌊(x : ℝ) * s⌋ : ℝ) + ⌈(x : ℝ) * s⌉) / (2 * s) - (x : ℝ) =
      (⌊(x : ℝ) * s⌋ + ⌈(x : ℝ) * s⌉ - 2 * (x * s)) / (2 * s) by
        rw [div_sub' (by positivity : (2 * s : ℝ) ≠ 0)]
        ring_nf]
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * s)]
  exact (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * s)).mpr
    hbound

/-! ## The weighted dither `ditherRoundN` -/

/-- The exactly-weighted dithered rounding of `x : ℚ` to the grid `1/s`:
with coin `c : Fin Q`, round up when `c.val < N` and down otherwise. For
`N = Q · Int.fract (x·s)` the up-probability is exactly the fractional
part — the classical randomized rounding. -/
def ditherRoundN (x : ℚ) (s N : ℕ) {Q : ℕ} (c : Fin Q) : ℚ :=
  if c.val < N then ceilToGrid x s else floorToGrid x s

/-- The coins of `Fin Q` below `N` number exactly `min N Q`. -/
theorem card_fin_val_lt (Q N : ℕ) :
    (Finset.univ.filter fun c : Fin Q => c.val < N).card = min N Q := by
  rcases lt_or_ge N Q with h | h
  · rw [min_eq_left h.le]
    let e : {c : Fin Q // c.val < N} ≃ Fin N :=
      { toFun := fun c => ⟨c.1.val, c.2⟩
        invFun := fun v => ⟨⟨v.val, lt_of_lt_of_le v.isLt h.le⟩, v.isLt⟩
        left_inv := fun c => Subtype.ext (Fin.ext rfl)
        right_inv := fun v => Fin.ext rfl }
    have hcard : Fintype.card {c : Fin Q // c.val < N} = N :=
      (Fintype.card_congr e).trans (Fintype.card_fin N)
    calc (Finset.univ.filter fun c : Fin Q => c.val < N).card
        = Fintype.card {c : Fin Q // c.val < N} :=
          (Fintype.card_subtype _).symm
      _ = N := hcard
  · rw [min_eq_right h]
    rw [Finset.filter_true_of_mem (fun c _ => lt_of_lt_of_le c.isLt h),
      Finset.card_univ, Fintype.card_fin]

/-- The coins of `Fin Q` at or above `N` number `Q - min N Q`. -/
theorem card_fin_val_not_lt (Q N : ℕ) :
    (Finset.univ.filter fun c : Fin Q => ¬c.val < N).card = Q - min N Q := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ :
    Finset (Fin Q))) (p := fun c : Fin Q => c.val < N)
  rw [card_fin_val_lt, Finset.card_univ, Fintype.card_fin] at h
  omega

/-- Pointwise split of the dithered-rounding sum: `N` ceil outcomes and
`Q - N` floor outcomes. -/
theorem sum_ditherRoundN (x : ℚ) (s N : ℕ) {Q : ℕ} (hNQ : N ≤ Q) :
    ∑ c : Fin Q, ditherRoundN x s N c =
      (N : ℚ) * ceilToGrid x s + (Q - N : ℚ) * floorToGrid x s := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (Fin Q))) (p := fun c : Fin Q => c.val < N)
    (f := fun c => ditherRoundN x s N c)
  rw [← hsplit]
  have h1 : ∀ c ∈ Finset.univ.filter (fun c : Fin Q => c.val < N),
      ditherRoundN x s N c = ceilToGrid x s := fun c hc =>
    ite_eq_left (Finset.mem_filter.mp hc).2
  have h2 : ∀ c ∈ Finset.univ.filter (fun c : Fin Q => ¬c.val < N),
      ditherRoundN x s N c = floorToGrid x s := fun c hc =>
    ite_eq_right (Finset.mem_filter.mp hc).2
  rw [Finset.sum_congr rfl h1, Finset.sum_const, card_fin_val_lt,
    min_eq_left hNQ, nsmul_eq_mul,
    Finset.sum_congr rfl h2, Finset.sum_const, card_fin_val_not_lt,
    min_eq_left hNQ, nsmul_eq_mul, Nat.cast_sub hNQ]

/-- **Unbiasedness of randomized rounding**: for `N = Q·Int.fract(x·s)`,
the `Fin Q`-coin dithered rounding has expectation exactly `x`. This is
the mean-zero-increment (martingale) property of dithering. -/
theorem unifAvg_ditherRoundN (x : ℚ) {s : ℕ} (hs : 0 < s) {Q N : ℕ}
    (hQ : 0 < Q) (hN : (Q : ℚ) * Int.fract (x * s) = N) :
    unifAvg (fun c : Fin Q => ((ditherRoundN x s N c : ℚ) : ℝ)) = x := by
  have hNQ : N ≤ Q := by
    have hlt : (N : ℚ) < Q := by
      rw [← hN]
      have hf := Int.fract_lt_one (x * s)
      have hQ' : (0 : ℚ) < Q := by exact_mod_cast hQ
      calc (Q : ℚ) * Int.fract (x * s) < Q * 1 :=
            mul_lt_mul_of_pos_left hf hQ'
        _ = Q := mul_one _
    exact_mod_cast hlt.le
  have hsum : ∑ c : Fin Q, ditherRoundN x s N c = (Q : ℚ) * x := by
    rw [sum_ditherRoundN x s N hNQ]
    unfold ceilToGrid floorToGrid
    have hs' : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
    by_cases hf : Int.fract (x * s) = 0
    · have hN0 : (N : ℚ) = 0 := by rw [← hN, hf, mul_zero]
      have hN0' : N = 0 := by exact_mod_cast hN0
      subst hN0'
      obtain ⟨z, hz⟩ := Int.fract_eq_zero_iff.mp hf
      rw [← hz, Int.ceil_intCast, Int.floor_intCast]
      have hx : x = (z : ℚ) / s := by
        rw [eq_div_iff hs']
        exact hz.symm
      rw [hx]
      push_cast
      field_simp
      ring
    · have hceil : ⌈x * s⌉ = ⌊x * s⌋ + 1 := by
        have hnotint : x * s ∉ Set.range (Int.cast : ℤ → ℚ) :=
          (Int.fract_eq_zero_iff.not).mp hf
        exact (Int.ceil_eq_floor_add_one_iff_notMem _).mpr hnotint
      rw [hceil]
      have hN' : (N : ℚ) = Q * Int.fract (x * s) := hN.symm
      push_cast
      calc (N : ℚ) * (((⌊x * s⌋ : ℚ) + 1) / s) +
            ((Q : ℚ) - (N : ℚ)) * ((⌊x * s⌋ : ℚ) / s)
          = ((Q : ℚ) * ⌊x * s⌋ + N) / s := by
            field_simp
            ring
        _ = (Q : ℚ) * (⌊x * s⌋ + Int.fract (x * s)) / s := by
            rw [hN']
            ring
        _ = (Q : ℚ) * (x * s) / s := by rw [Int.floor_add_fract]
        _ = (Q : ℚ) * x := by
            rw [← mul_assoc, mul_div_cancel_right₀ _ hs']
  rw [unifAvg, Fintype.card_fin, ← Rat.cast_sum, hsum]
  push_cast
  have hQ' : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  exact mul_div_cancel_left₀ _ hQ'

/-- The rounding defect `dither - x` of one coin: the martingale
increment. -/
def ditherErr (x : ℚ) (s N : ℕ) {Q : ℕ} (c : Fin Q) : ℝ :=
  (ditherRoundN x s N c : ℝ) - x

/-- The defect sums to zero: exact unbiasedness, unnormalized. -/
theorem sum_ditherErr (x : ℚ) {s : ℕ} (hs : 0 < s) {Q N : ℕ} (hQ : 0 < Q)
    (hN : (Q : ℚ) * Int.fract (x * s) = N) :
    ∑ c : Fin Q, ditherErr x s N c = 0 := by
  have hunif := unifAvg_ditherRoundN x hs hQ hN
  have hcard : (Fintype.card (Fin Q) : ℝ) ≠ 0 := by
    rw [Fintype.card_fin]
    exact_mod_cast hQ.ne'
  have hsum : ∑ c : Fin Q, ((ditherRoundN x s N c : ℚ) : ℝ) = (Q : ℝ) * x := by
    have : unifAvg (fun c : Fin Q => ((ditherRoundN x s N c : ℚ) : ℝ)) =
        (∑ c : Fin Q, ((ditherRoundN x s N c : ℚ) : ℝ)) / Q := by
      rw [unifAvg, Fintype.card_fin]
    rw [hunif] at this
    field_simp at this ⊢
    linarith
  unfold ditherErr
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, sub_self]

/-- Every dither defect is bounded by one grid cell. -/
theorem abs_ditherErr_le (x : ℚ) {s : ℕ} (hs : 0 < s) {Q N : ℕ}
    (c : Fin Q) : |ditherErr x s N c| ≤ 1 / s := by
  unfold ditherErr ditherRoundN
  by_cases h : c.val < N
  · rw [ite_eq_left h]
    have hh : |x - ceilToGrid x s| ≤ 1 / s := abs_sub_ceilToGrid x hs
    rw [abs_sub_comm] at hh
    have hh' : ((|ceilToGrid x s - x| : ℚ) : ℝ) ≤ ((1 / s : ℚ) : ℝ) := by
      exact_mod_cast hh
    push_cast at hh'
    exact hh'
  · rw [ite_eq_right h]
    have hh : |x - floorToGrid x s| ≤ 1 / s := abs_sub_floorToGrid x hs
    rw [abs_sub_comm] at hh
    have hh' : ((|floorToGrid x s - x| : ℚ) : ℝ) ≤ ((1 / s : ℚ) : ℝ) := by
      exact_mod_cast hh
    push_cast at hh'
    exact hh'

/-- **Exact one-step variance**: `E_c[(dither - x)²] = p(1-p)/s²` with
`p = Int.fract (x·s)`. -/
theorem unifAvg_ditherErr_sq (x : ℚ) {s : ℕ} (hs : 0 < s) {Q N : ℕ}
    (hQ : 0 < Q) (hN : (Q : ℚ) * Int.fract (x * s) = N) :
    unifAvg (fun c : Fin Q => (ditherErr x s N c) ^ 2) =
      Int.fract (x * s) * (1 - Int.fract (x * s)) / (s : ℝ) ^ 2 := by
  have hNQ : N ≤ Q := by
    have hlt : (N : ℚ) < Q := by
      rw [← hN]
      have hf := Int.fract_lt_one (x * s)
      have hQ' : (0 : ℚ) < Q := by exact_mod_cast hQ
      calc (Q : ℚ) * Int.fract (x * s) < Q * 1 :=
            mul_lt_mul_of_pos_left hf hQ'
        _ = Q := mul_one _
    exact_mod_cast hlt.le
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  set p : ℝ := (Int.fract (x * s) : ℝ) with hp
  have hcast : ((x * s : ℚ) : ℝ) = (x : ℝ) * s := by norm_cast
  have hpcast : (Int.fract (x * s) : ℝ) = (x : ℝ) * s - ⌊(x : ℝ) * s⌋ := by
    simp only [Int.fract]
  -- The sum splits into N ceil-terms and (Q-N) floor-terms.
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (Fin Q))) (p := fun c : Fin Q => c.val < N)
    (f := fun c => (ditherErr x s N c) ^ 2)
  have hceil_val : ∀ c : Fin Q, c.val < N →
      (ditherErr x s N c : ℝ) = (⌈(x : ℝ) * s⌉ - x * s) / s := by
    intro c hc
    unfold ditherErr ditherRoundN
    rw [ite_eq_left hc, ceilToGrid]
    push_cast
    rw [← hcast, Rat.ceil_cast, div_sub' hs'.ne']
    push_cast
    ring
  have hfloor_val : ∀ c : Fin Q, ¬c.val < N →
      (ditherErr x s N c : ℝ) = (⌊(x : ℝ) * s⌋ - x * s) / s := by
    intro c hc
    unfold ditherErr ditherRoundN
    rw [ite_eq_right hc, floorToGrid]
    push_cast
    rw [← hcast, Rat.floor_cast, div_sub' hs'.ne']
    push_cast
    ring
  have hsum : ∑ c : Fin Q, (ditherErr x s N c) ^ 2 =
      (N : ℝ) * ((⌈(x : ℝ) * s⌉ - x * s) / s) ^ 2 +
        ((Q : ℝ) - N) * ((⌊(x : ℝ) * s⌋ - x * s) / s) ^ 2 := by
    rw [← hsplit]
    congr 1
    · rw [Finset.sum_congr rfl (fun c hc =>
          congrArg (· ^ 2) (hceil_val c (Finset.mem_filter.mp hc).2)),
        Finset.sum_const, card_fin_val_lt, min_eq_left hNQ, nsmul_eq_mul]
    · rw [Finset.sum_congr rfl (fun c hc =>
          congrArg (· ^ 2) (hfloor_val c (Finset.mem_filter.mp hc).2)),
        Finset.sum_const, card_fin_val_not_lt, min_eq_left hNQ, nsmul_eq_mul,
        Nat.cast_sub hNQ]
  -- The values of the two defect branches.
  have hN' : (N : ℝ) = (Q : ℝ) * p := by
    rw [hp]
    exact_mod_cast hN.symm
  rw [unifAvg, Fintype.card_fin, hsum]
  by_cases hf : Int.fract (x * s) = 0
  · -- integral case: N = 0, every defect is 0, p = 0
    have hN0 : (N : ℚ) = 0 := by rw [← hN, hf, mul_zero]
    have hN0' : N = 0 := by exact_mod_cast hN0
    subst hN0'
    obtain ⟨z, hz⟩ := Int.fract_eq_zero_iff.mp hf
    have hzr : (x : ℝ) * s = (z : ℝ) := by
      have hcast : ((x * s : ℚ) : ℝ) = (x : ℝ) * s := by norm_cast
      rw [← hcast, ← hz]
      norm_cast
    rw [hf, hzr, Int.ceil_intCast, Int.floor_intCast]
    simp
  · -- non-integral: ⌈u⌉ - u = 1 - p and ⌊u⌋ - u = -p
    have hceil : ⌈(x : ℝ) * s⌉ = ⌊(x : ℝ) * s⌋ + 1 := by
      have hnotint : (x : ℝ) * s ∉ Set.range (Int.cast : ℤ → ℝ) := by
        rintro ⟨z, hz⟩
        have hzq : (x * s : ℚ) = (z : ℚ) := by
          have hcast : ((x * s : ℚ) : ℝ) = (z : ℝ) := by
            have h1 : ((x * s : ℚ) : ℝ) = (x : ℝ) * s := by norm_cast
            rw [h1, ← hz]
          exact_mod_cast hcast
        exact hf (Int.fract_eq_zero_iff.mpr ⟨z, hzq.symm⟩)
      exact (Int.ceil_eq_floor_add_one_iff_notMem _).mpr hnotint
    have hceilv : (⌈(x : ℝ) * s⌉ : ℝ) - x * s = 1 - p := by
      rw [hceil]
      push_cast
      rw [hp, hpcast]
      ring
    have hfloorv : (⌊(x : ℝ) * s⌋ : ℝ) - x * s = -p := by
      rw [hp, hpcast]
      ring
    rw [hceilv, hfloorv, hN']
    have hpf : ((Int.fract (x * s) : ℚ) : ℝ) = p := by
      rw [hp, Rat.cast_fract, hcast]
    rw [hpf]
    have hs'' : (s : ℝ) ≠ 0 := hs'.ne'
    have hQ'' : (Q : ℝ) ≠ 0 := hQ'.ne'
    field_simp
    ring

/-- The one-step variance is at most `(1/(2s))²` — the maximum of
`p(1-p)` is `1/4`. -/
theorem unifAvg_ditherErr_sq_le (x : ℚ) {s : ℕ} (hs : 0 < s) {Q N : ℕ}
    (hQ : 0 < Q) (hN : (Q : ℚ) * Int.fract (x * s) = N) :
    unifAvg (fun c : Fin Q => (ditherErr x s N c) ^ 2) ≤ (1 / (2 * s)) ^ 2 := by
  rw [unifAvg_ditherErr_sq x hs hQ hN]
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hp0 : (0 : ℝ) ≤ ((Int.fract (x * s) : ℚ) : ℝ) := by
    exact_mod_cast Int.fract_nonneg (x * s)
  have hp1 : ((Int.fract (x * s) : ℚ) : ℝ) ≤ 1 := by
    exact_mod_cast (Int.fract_lt_one (x * s)).le
  have hquad : ((Int.fract (x * s) : ℚ) : ℝ) *
      (1 - ((Int.fract (x * s) : ℚ) : ℝ)) ≤ 1 / 4 := by
    have h := sq_nonneg (((Int.fract (x * s) : ℚ) : ℝ) - 1 / 2)
    linarith
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (s : ℝ) ^ 2)]
  calc ((Int.fract (x * s) : ℚ) : ℝ) * (1 - ((Int.fract (x * s) : ℚ) : ℝ))
      ≤ 1 / 4 := hquad
    _ = (1 / (2 * s)) ^ 2 * (s : ℝ) ^ 2 := by
        field_simp
        ring

/-! ## Independent increments: the `incSum` martingale -/

/-- A sum of `k` independent increments `ξᵢ` driven by coin `εᵢ`:
`incSum ξ ε = ∑ i, ξ i (ε i)`. -/
def incSum {C : Type*} {k : ℕ} (ξ : Fin k → C → ℝ) (ε : Fin k → C) : ℝ :=
  ∑ i, ξ i (ε i)

/-- Peeling the last coin: `M_{k+1}(snoc η c) = M_k(η) + ξ_{k}(c)`. -/
theorem incSum_snoc {C : Type*} {k : ℕ} (ξ : Fin (k + 1) → C → ℝ)
    (η : Fin k → C) (c : C) :
    incSum ξ (Fin.snoc η c) =
      incSum (fun i => ξ i.castSucc) η + ξ (Fin.last k) c := by
  unfold incSum
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [Fin.snoc_castSucc]
  · rw [Fin.snoc_last]

/-- Splitting the sum over `Fin (k+1) → C` into the first `k` coins and
the last coin, via `Fin.snocEquiv`. -/
theorem sum_pi_succ_snoc {C : Type*} [Fintype C] {k : ℕ}
    (F : (Fin (k + 1) → C) → ℝ) :
    ∑ ε : Fin (k + 1) → C, F ε =
      ∑ η : Fin k → C, ∑ c : C, F (Fin.snoc η c) := by
  have h := Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (k + 1) => C) F
  rw [← h, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η _
  apply Finset.sum_congr rfl
  intro c _
  rfl

/-- **The martingale property, unnormalized**: for a mean-zero last
increment, averaging over the fresh coin reproduces the accumulated sum
scaled by `card C`. -/
theorem sum_incSum_fresh_coin {C : Type*} [Fintype C] {k : ℕ}
    (ξ : Fin (k + 1) → C → ℝ) (hlast : ∑ c : C, ξ (Fin.last k) c = 0)
    (η : Fin k → C) :
    ∑ c : C, incSum ξ (Fin.snoc η c) =
      (Fintype.card C : ℝ) * incSum (fun i => ξ i.castSucc) η := by
  have step : ∀ c : C, incSum ξ (Fin.snoc η c) =
      incSum (fun i => ξ i.castSucc) η + ξ (Fin.last k) c :=
    fun c => incSum_snoc ξ η c
  rw [Finset.sum_congr rfl (fun c _ => step c), Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hlast, add_zero]

/-- **The martingale property**: `E_c[M_{k+1}(snoc η c)] = M_k(η)` for a
mean-zero last increment — conditional expectation given the first `k`
coins, in the finite model. -/
theorem unifAvg_incSum_fresh_coin {C : Type*} [Fintype C]
    (hC : (Fintype.card C : ℝ) ≠ 0) {k : ℕ}
    (ξ : Fin (k + 1) → C → ℝ) (hlast : ∑ c : C, ξ (Fin.last k) c = 0)
    (η : Fin k → C) :
    unifAvg (fun c : C => incSum ξ (Fin.snoc η c)) =
      incSum (fun i => ξ i.castSucc) η := by
  rw [unifAvg, sum_incSum_fresh_coin ξ hlast η,
    mul_div_cancel_left₀ _ hC]

/-- Unnormalized recursion: `∑_{ε} M_{k+1}(ε) = card C · ∑_{η} M_k(η)`. -/
theorem sum_incSum_succ {C : Type*} [Fintype C] {k : ℕ}
    (ξ : Fin (k + 1) → C → ℝ) (hlast : ∑ c : C, ξ (Fin.last k) c = 0) :
    ∑ ε : Fin (k + 1) → C, incSum ξ ε =
      (Fintype.card C : ℝ) *
        ∑ η : Fin k → C, incSum (fun i => ξ i.castSucc) η := by
  rw [sum_pi_succ_snoc,
    Finset.sum_congr rfl fun η _ => sum_incSum_fresh_coin ξ hlast η,
    ← Finset.mul_sum]

/-- Normalized recursion: `E[M_{k+1}] = E[M_k]`. -/
theorem unifAvg_incSum_succ {C : Type*} [Fintype C]
    (hC : (Fintype.card C : ℝ) ≠ 0) {k : ℕ}
    (ξ : Fin (k + 1) → C → ℝ) (hlast : ∑ c : C, ξ (Fin.last k) c = 0) :
    unifAvg (incSum ξ) = unifAvg (incSum fun i => ξ i.castSucc) := by
  rw [unifAvg, unifAvg, sum_incSum_succ ξ hlast, card_piFin, card_piFin]
  push_cast
  rw [pow_succ (Fintype.card C : ℝ) k,
    mul_comm ((Fintype.card C : ℝ) ^ k) (Fintype.card C : ℝ)]
  exact mul_div_mul_left _ _ hC

/-- For a family of mean-zero independent increments, `E[M_k] = 0`. -/
theorem unifAvg_incSum_eq_zero {C : Type*} [Fintype C]
    (hC : (Fintype.card C : ℝ) ≠ 0) :
    ∀ {k : ℕ} (ξ : Fin k → C → ℝ), (∀ i, ∑ c : C, ξ i c = 0) →
      unifAvg (incSum ξ) = 0 := by
  intro k
  induction k with
  | zero =>
    intro ξ _
    rw [unifAvg]
    simp [incSum]
  | succ k ih =>
    intro ξ h
    rw [unifAvg_incSum_succ hC ξ (h (Fin.last k))]
    exact ih _ (fun i => h i.castSucc)

/-- Unnormalized second-moment recursion:
`∑ M_{k+1}² = cardC·∑ M_k² + card^k·∑ ξ²` — the cross term
`2·M_k·E[ξ]` vanishes. -/
theorem sum_incSum_sq_succ {C : Type*} [Fintype C] {k : ℕ}
    (ξ : Fin (k + 1) → C → ℝ) (hlast : ∑ c : C, ξ (Fin.last k) c = 0) :
    ∑ ε : Fin (k + 1) → C, (incSum ξ ε) ^ 2 =
      (Fintype.card C : ℝ) *
          ∑ η : Fin k → C, (incSum (fun i => ξ i.castSucc) η) ^ 2 +
        (Fintype.card (Fin k → C) : ℝ) * ∑ c : C, (ξ (Fin.last k) c) ^ 2 := by
  rw [sum_pi_succ_snoc]
  have step : ∀ η : Fin k → C,
      ∑ c : C, (incSum ξ (Fin.snoc η c)) ^ 2 =
        (Fintype.card C : ℝ) * (incSum (fun i => ξ i.castSucc) η) ^ 2 +
          ∑ c : C, (ξ (Fin.last k) c) ^ 2 := by
    intro η
    have hexp : ∀ c : C, (incSum ξ (Fin.snoc η c)) ^ 2 =
        (incSum (fun i => ξ i.castSucc) η) ^ 2 +
          2 * incSum (fun i => ξ i.castSucc) η * ξ (Fin.last k) c +
            (ξ (Fin.last k) c) ^ 2 := by
      intro c
      rw [incSum_snoc]
      ring
    rw [Finset.sum_congr rfl (fun c _ => hexp c), Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hmid : ∑ c : C,
        2 * incSum (fun i => ξ i.castSucc) η * ξ (Fin.last k) c = 0 := by
      rw [← Finset.mul_sum, hlast, mul_zero]
    rw [hmid, add_zero]
  rw [Finset.sum_congr rfl (fun η _ => step η), Finset.sum_add_distrib,
    ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- Normalized second-moment recursion: `E[M_{k+1}²] = E[M_k²] + E[ξ²]`. -/
theorem unifAvg_incSum_sq_succ {C : Type*} [Fintype C]
    (hC : (Fintype.card C : ℝ) ≠ 0) {k : ℕ}
    (ξ : Fin (k + 1) → C → ℝ) (hlast : ∑ c : C, ξ (Fin.last k) c = 0) :
    unifAvg (fun ε => (incSum ξ ε) ^ 2) =
      unifAvg (fun η => (incSum (fun i => ξ i.castSucc) η) ^ 2) +
        unifAvg (fun c => (ξ (Fin.last k) c) ^ 2) := by
  have hCk : (Fintype.card (Fin k → C) : ℝ) =
      (Fintype.card C : ℝ) ^ k := by rw [card_piFin]; norm_cast
  have hD : (Fintype.card (Fin (k + 1) → C) : ℝ) =
      (Fintype.card C : ℝ) * (Fintype.card C : ℝ) ^ k := by
    rw [card_piFin]; push_cast; ring
  rw [unifAvg, sum_incSum_sq_succ ξ hlast, hD, add_div]
  congr 1
  · rw [unifAvg, hCk]
    exact mul_div_mul_left _ _ hC
  · rw [unifAvg, hCk, mul_comm ((Fintype.card C : ℝ) ^ k)
      (∑ c : C, ξ (Fin.last k) c ^ 2)]
    exact mul_div_mul_right _ _ (pow_ne_zero k hC)

/-- **Second-moment identity for independent increments**:
`E[(∑ ξᵢ)²] = ∑ E[ξᵢ²]` — all cross terms vanish. -/
theorem unifAvg_incSum_sq {C : Type*} [Fintype C]
    (hC : (Fintype.card C : ℝ) ≠ 0) :
    ∀ {k : ℕ} (ξ : Fin k → C → ℝ), (∀ i, ∑ c : C, ξ i c = 0) →
      unifAvg (fun ε => (incSum ξ ε) ^ 2) =
        ∑ i, unifAvg (fun c => (ξ i c) ^ 2) := by
  intro k
  induction k with
  | zero =>
    intro ξ _
    rw [unifAvg]
    simp [incSum]
  | succ k ih =>
    intro ξ h
    rw [unifAvg_incSum_sq_succ hC ξ (h (Fin.last k)),
      ih _ (fun i => h i.castSucc), Fin.sum_univ_castSucc]

/-! ## The dithered walk -/

/-- The dithered rounding walk: `ditherWalk x s Nd ε = ∑ᵢ (dither(xᵢ, εᵢ)
- xᵢ)`, where `Nd i` is the up-threshold `Q·Int.fract(xᵢ·s)`. The coins
`ε : Fin t → Fin Q` are the randomness of the dithered transcript. -/
def ditherWalk {t : ℕ} (x : Fin t → ℚ) (s : ℕ) (Nd : Fin t → ℕ) {Q : ℕ}
    (ε : Fin t → Fin Q) : ℝ :=
  incSum (fun i c => ditherErr (x i) s (Nd i) c) ε

/-- The dithered walk is unbiased: `E[D_t] = 0`. -/
theorem unifAvg_ditherWalk {t : ℕ} (x : Fin t → ℚ) {s : ℕ} (hs : 0 < s)
    (Nd : Fin t → ℕ) {Q : ℕ} (hQ : 0 < Q)
    (hN : ∀ i, (Q : ℚ) * Int.fract (x i * s) = Nd i) :
    unifAvg (ditherWalk (Q := Q) x s Nd) = 0 := by
  have hC : (Fintype.card (Fin Q) : ℝ) ≠ 0 := by
    rw [Fintype.card_fin]
    exact_mod_cast hQ.ne'
  exact unifAvg_incSum_eq_zero hC _ fun i =>
    sum_ditherErr (x i) hs hQ (hN i)

/-- **Expected squared drift**: `E[D_t²] = (1/s²)·∑ᵢ pᵢ(1-pᵢ)` with
`pᵢ = Int.fract(xᵢ·s)`. -/
theorem unifAvg_ditherWalk_sq {t : ℕ} (x : Fin t → ℚ) {s : ℕ} (hs : 0 < s)
    (Nd : Fin t → ℕ) {Q : ℕ} (hQ : 0 < Q)
    (hN : ∀ i, (Q : ℚ) * Int.fract (x i * s) = Nd i) :
    unifAvg (fun ε => (ditherWalk (Q := Q) x s Nd ε) ^ 2) =
      (1 / (s : ℝ) ^ 2) *
        ∑ i, Int.fract (x i * s) * (1 - Int.fract (x i * s)) := by
  have hC : (Fintype.card (Fin Q) : ℝ) ≠ 0 := by
    rw [Fintype.card_fin]
    exact_mod_cast hQ.ne'
  unfold ditherWalk
  rw [unifAvg_incSum_sq hC _ fun i =>
    sum_ditherErr (x i) hs hQ (hN i)]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (unifAvg_ditherErr_sq (x i) hs hQ (hN i)).trans (by push_cast; ring)

/-- The variance bound: `E[D_t²] ≤ t·(1/(2s))²`. -/
theorem unifAvg_ditherWalk_sq_le {t : ℕ} (x : Fin t → ℚ) {s : ℕ}
    (hs : 0 < s) (Nd : Fin t → ℕ) {Q : ℕ} (hQ : 0 < Q)
    (hN : ∀ i, (Q : ℚ) * Int.fract (x i * s) = Nd i) :
    unifAvg (fun ε => (ditherWalk (Q := Q) x s Nd ε) ^ 2) ≤
      t * (1 / (2 * s)) ^ 2 := by
  have hC : (Fintype.card (Fin Q) : ℝ) ≠ 0 := by
    rw [Fintype.card_fin]
    exact_mod_cast hQ.ne'
  unfold ditherWalk
  rw [unifAvg_incSum_sq hC _ fun i =>
    sum_ditherErr (x i) hs hQ (hN i)]
  calc ∑ i : Fin t, unifAvg (fun c => (ditherErr (x i) s (Nd i) c) ^ 2)
      ≤ ∑ _i : Fin t, (1 / (2 * (s : ℝ))) ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          unifAvg_ditherErr_sq_le (x i) hs hQ (hN i)
    _ = t * (1 / (2 * s)) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]

/-- **The martingale property for the dithered walk**: given the first `k`
coins `η`, the fresh coin average of `D_{k+1}` is `D_k(η)`. This is the
elementary conditional-expectation statement `E[D_{k+1} | η] = D_k(η)`. -/
theorem unifAvg_ditherWalk_conditional {k : ℕ} (x : Fin (k + 1) → ℚ)
    {s : ℕ} (hs : 0 < s) (Nd : Fin (k + 1) → ℕ) {Q : ℕ} (hQ : 0 < Q)
    (hN : (Q : ℚ) * Int.fract (x (Fin.last k) * s) = Nd (Fin.last k))
    (η : Fin k → Fin Q) :
    unifAvg (fun c : Fin Q =>
        ditherWalk x s Nd (Fin.snoc η c)) =
      ditherWalk (fun i => x i.castSucc) s (fun i => Nd i.castSucc) η := by
  have hC : (Fintype.card (Fin Q) : ℝ) ≠ 0 := by
    rw [Fintype.card_fin]
    exact_mod_cast hQ.ne'
  exact unifAvg_incSum_fresh_coin hC _
    (sum_ditherErr (x (Fin.last k)) hs hQ hN) η

/-- **Chebyshev tail in the finite model**: the fraction of coin tables on
which `|D_t| ≥ u` is at most `t·(1/(2s))²/u²`. -/
theorem ditherWalk_tail_le {t : ℕ} (x : Fin t → ℚ) {s : ℕ} (hs : 0 < s)
    (Nd : Fin t → ℕ) {Q : ℕ} (hQ : 0 < Q)
    (hN : ∀ i, (Q : ℚ) * Int.fract (x i * s) = Nd i) {u : ℝ}
    (hu : 0 < u) :
    unifAvg (fun ε : Fin t → Fin Q =>
        if u ≤ |ditherWalk x s Nd ε| then (1 : ℝ) else 0) ≤
      t * (1 / (2 * s)) ^ 2 / u ^ 2 := by
  have hcardQ : (0 : ℝ) < (Fintype.card (Fin t → Fin Q) : ℝ) := by
    rw [card_piFin, Fintype.card_fin]
    positivity
  have hu2 : (0 : ℝ) < u ^ 2 := sq_pos_of_pos hu
  have hcount : (Finset.univ.filter fun ε : Fin t → Fin Q =>
        u ≤ |ditherWalk x s Nd ε|).card ≤
        (t * (1 / (2 * s)) ^ 2) * (Fintype.card (Fin t → Fin Q) : ℝ) /
          u ^ 2 := by
    have hmarkov := sq_mul_filter_card_le_sum_sq
      (fun ε : Fin t → Fin Q => ditherWalk x s Nd ε) hu.le
    have hE := unifAvg_ditherWalk_sq_le x hs Nd hQ hN
    have hsum : ∑ ε : Fin t → Fin Q, (ditherWalk x s Nd ε) ^ 2 ≤
        (t * (1 / (2 * s)) ^ 2) * (Fintype.card (Fin t → Fin Q) : ℝ) := by
      have : ∑ ε : Fin t → Fin Q, (ditherWalk x s Nd ε) ^ 2 =
          unifAvg (fun ε : Fin t → Fin Q => (ditherWalk x s Nd ε) ^ 2) *
            (Fintype.card (Fin t → Fin Q) : ℝ) := by
        rw [unifAvg, div_mul_cancel₀ _ hcardQ.ne']
      rw [this]
      exact mul_le_mul_of_nonneg_right hE hcardQ.le
    have hb : ((Finset.univ.filter fun ε : Fin t → Fin Q =>
          u ≤ |ditherWalk x s Nd ε|).card : ℝ) ≤
          ((t * (1 / (2 * s)) ^ 2) *
            (Fintype.card (Fin t → Fin Q) : ℝ)) / u ^ 2 := by
      rw [le_div_iff₀ hu2]
      rw [mul_comm ((Finset.univ.filter
        (fun ε : Fin t → Fin Q => u ≤ |ditherWalk x s Nd ε|)).card : ℝ) (u ^ 2)]
      exact hmarkov.trans hsum
    exact_mod_cast hb
  have hcard : ∑ ε : Fin t → Fin Q,
      (if u ≤ |ditherWalk x s Nd ε| then (1 : ℝ) else 0) =
        ((Finset.univ.filter fun ε : Fin t → Fin Q =>
          u ≤ |ditherWalk x s Nd ε|).card : ℝ) :=
    Finset.sum_boole _ _
  rw [unifAvg, hcard, div_le_iff₀ hcardQ, div_mul_eq_mul_div]
  exact hcount

/-! ## The dithered transcript drift (connection to `FinitePrecision`) -/

/-- The flattened index for a transcript of `N` steps on `n` coordinates:
`Fin (N·n) ≅ Fin N × Fin n` via `finProdFinEquiv`. -/
noncomputable def flatIdx {N n : ℕ} : Fin (N * n) ≃ Fin N × Fin n :=
  finProdFinEquiv.symm

/-- The drift accumulated by the dithered transcript: `drift ε =
∑_{t,j} b t j · (x t j - dither(x t j, ε (t,j)))`, with the `(t,j)`-coin
living in `Fin (N·n)` via `finProdFinEquiv`. This is the stochastic
analogue of the quantity bounded by `transcript_drift_bound` and
`rounded_transcript_drift` in `FinitePrecision.lean`. -/
noncomputable def transcriptDrift {N n : ℕ} (b : Fin N → Fin n → ℝ)
    (x : Fin N → Fin n → ℚ) (s : ℕ) (Nd : Fin N → Fin n → ℕ) {Q : ℕ}
    (ε : Fin (N * n) → Fin Q) : ℝ :=
  incSum (fun k c =>
    (b (flatIdx k).1 (flatIdx k).2) *
      ((x (flatIdx k).1 (flatIdx k).2 : ℝ) -
        ((ditherRoundN (x (flatIdx k).1 (flatIdx k).2) s
          (Nd (flatIdx k).1 (flatIdx k).2) c : ℚ) : ℝ))) ε

/-- **Expected drift is zero** — the stochastic strengthening of the
deterministic worst-case bound: on average the dithered transcript does
not drift at all. -/
theorem unifAvg_transcriptDrift {N n : ℕ} (b : Fin N → Fin n → ℝ)
    (x : Fin N → Fin n → ℚ) {s : ℕ} (hs : 0 < s)
    (Nd : Fin N → Fin n → ℕ) {Q : ℕ} (hQ : 0 < Q)
    (hN : ∀ t : Fin N, ∀ j : Fin n,
      (Q : ℚ) * Int.fract (x t j * s) = Nd t j) :
    unifAvg (transcriptDrift (Q := Q) b x s Nd) = 0 := by
  have hC : (Fintype.card (Fin Q) : ℝ) ≠ 0 := by
    rw [Fintype.card_fin]
    exact_mod_cast hQ.ne'
  apply unifAvg_incSum_eq_zero hC
  intro k
  have hk : ∑ c : Fin Q, ((x (flatIdx k).1 (flatIdx k).2 : ℝ) -
      ((ditherRoundN (x (flatIdx k).1 (flatIdx k).2) s
        (Nd (flatIdx k).1 (flatIdx k).2) c : ℚ) : ℝ)) = 0 := by
    have h := sum_ditherErr (x (flatIdx k).1 (flatIdx k).2) hs hQ
      (hN (flatIdx k).1 (flatIdx k).2)
    have : ∀ c : Fin Q, (x (flatIdx k).1 (flatIdx k).2 : ℝ) -
        ((ditherRoundN (x (flatIdx k).1 (flatIdx k).2) s
          (Nd (flatIdx k).1 (flatIdx k).2) c : ℚ) : ℝ) =
          -ditherErr (x (flatIdx k).1 (flatIdx k).2) s
            (Nd (flatIdx k).1 (flatIdx k).2) c := by
      intro c
      unfold ditherErr
      ring
    rw [Finset.sum_congr rfl (fun c _ => this c), Finset.sum_neg_distrib, h,
      neg_zero]
  have h2 : ∑ c : Fin Q, (b (flatIdx k).1 (flatIdx k).2) *
      ((x (flatIdx k).1 (flatIdx k).2 : ℝ) -
        ((ditherRoundN (x (flatIdx k).1 (flatIdx k).2) s
          (Nd (flatIdx k).1 (flatIdx k).2) c : ℚ) : ℝ)) = 0 := by
    rw [← Finset.mul_sum, hk, mul_zero]
  exact h2

/-- The one-step variance of a coefficient-weighted defect. -/
theorem unifAvg_transcriptDrift_step_sq {N n : ℕ} (b : Fin N → Fin n → ℝ)
    (x : Fin N → Fin n → ℚ) {s : ℕ} (hs : 0 < s)
    (Nd : Fin N → Fin n → ℕ) {Q : ℕ} (hQ : 0 < Q)
    (hN : ∀ t : Fin N, ∀ j : Fin n,
      (Q : ℚ) * Int.fract (x t j * s) = Nd t j) (k : Fin (N * n)) :
    unifAvg (fun c : Fin Q =>
        ((b (flatIdx k).1 (flatIdx k).2) *
          ((x (flatIdx k).1 (flatIdx k).2 : ℝ) -
            ((ditherRoundN (x (flatIdx k).1 (flatIdx k).2) s
              (Nd (flatIdx k).1 (flatIdx k).2) c : ℚ) : ℝ))) ^ 2) =
      (b (flatIdx k).1 (flatIdx k).2) ^ 2 *
        (Int.fract (x (flatIdx k).1 (flatIdx k).2 * s) *
          (1 - Int.fract (x (flatIdx k).1 (flatIdx k).2 * s)) /
            (s : ℝ) ^ 2) := by
  have hdef : ∀ c : Fin Q,
      ((b (flatIdx k).1 (flatIdx k).2) *
        ((x (flatIdx k).1 (flatIdx k).2 : ℝ) -
          ((ditherRoundN (x (flatIdx k).1 (flatIdx k).2) s
            (Nd (flatIdx k).1 (flatIdx k).2) c : ℚ) : ℝ))) ^ 2 =
        (b (flatIdx k).1 (flatIdx k).2) ^ 2 *
          (ditherErr (x (flatIdx k).1 (flatIdx k).2) s
            (Nd (flatIdx k).1 (flatIdx k).2) c) ^ 2 := by
    intro c
    unfold ditherErr
    ring
  simp only [hdef]
  rw [unifAvg_mul_left,
    unifAvg_ditherErr_sq _ hs hQ (hN (flatIdx k).1 (flatIdx k).2)]

/-- **Expected squared drift**: `E[drift²] =
(1/s²)·∑_{t,j} (b t j)²·p_{tj}(1-p_{tj})` where `p_{tj} =
Int.fract (x t j·s)`. Compare the deterministic
`transcript_drift_bound`: the random drift has mean zero and second
moment controlled by the *squared* coefficient mass. -/
theorem transcriptDrift_sq {N n : ℕ} (b : Fin N → Fin n → ℝ)
    (x : Fin N → Fin n → ℚ) {s : ℕ} (hs : 0 < s)
    (Nd : Fin N → Fin n → ℕ) {Q : ℕ} (hQ : 0 < Q)
    (hN : ∀ t : Fin N, ∀ j : Fin n,
      (Q : ℚ) * Int.fract (x t j * s) = Nd t j) :
    unifAvg (fun ε => (transcriptDrift (Q := Q) b x s Nd ε) ^ 2) =
      (1 / (s : ℝ) ^ 2) * ∑ t : Fin N, ∑ j : Fin n,
        (b t j) ^ 2 *
          (Int.fract (x t j * s) * (1 - Int.fract (x t j * s))) := by
  have hC : (Fintype.card (Fin Q) : ℝ) ≠ 0 := by
    rw [Fintype.card_fin]
    exact_mod_cast hQ.ne'
  have hmean : ∀ k : Fin (N * n),
      ∑ c : Fin Q, (b (flatIdx k).1 (flatIdx k).2) *
        ((x (flatIdx k).1 (flatIdx k).2 : ℝ) -
          ((ditherRoundN (x (flatIdx k).1 (flatIdx k).2) s
            (Nd (flatIdx k).1 (flatIdx k).2) c : ℚ) : ℝ)) = 0 := by
    intro k
    have h := sum_ditherErr (x (flatIdx k).1 (flatIdx k).2) hs hQ
      (hN (flatIdx k).1 (flatIdx k).2)
    have step : ∀ c : Fin Q,
        (b (flatIdx k).1 (flatIdx k).2) *
          ((x (flatIdx k).1 (flatIdx k).2 : ℝ) -
            ((ditherRoundN (x (flatIdx k).1 (flatIdx k).2) s
              (Nd (flatIdx k).1 (flatIdx k).2) c : ℚ) : ℝ)) =
          -(b (flatIdx k).1 (flatIdx k).2) *
            ditherErr (x (flatIdx k).1 (flatIdx k).2) s
              (Nd (flatIdx k).1 (flatIdx k).2) c := by
      intro c
      unfold ditherErr
      ring
    rw [Finset.sum_congr rfl (fun c _ => step c),
      ← Finset.mul_sum, h, mul_zero]
  unfold transcriptDrift
  rw [unifAvg_incSum_sq hC _ hmean]
  push_cast
  refine (Finset.sum_congr rfl fun k _ =>
    unifAvg_transcriptDrift_step_sq b x hs Nd hQ hN k).trans ?_
  calc ∑ k : Fin (N * n), (b (flatIdx k).1 (flatIdx k).2) ^ 2 *
          (((Int.fract (x (flatIdx k).1 (flatIdx k).2 * s) : ℚ) : ℝ) *
            (1 - ((Int.fract (x (flatIdx k).1 (flatIdx k).2 * s) : ℚ) : ℝ)) /
              (s : ℝ) ^ 2)
      = ∑ p : Fin N × Fin n, (b p.1 p.2) ^ 2 *
          (((Int.fract (x p.1 p.2 * s) : ℚ) : ℝ) *
            (1 - ((Int.fract (x p.1 p.2 * s) : ℚ) : ℝ)) /
              (s : ℝ) ^ 2) :=
        Equiv.sum_comp flatIdx
          (fun p : Fin N × Fin n => (b p.1 p.2) ^ 2 *
            (((Int.fract (x p.1 p.2 * s) : ℚ) : ℝ) *
              (1 - ((Int.fract (x p.1 p.2 * s) : ℚ) : ℝ)) /
                (s : ℝ) ^ 2))
    _ = ∑ t : Fin N, ∑ j : Fin n, (b t j) ^ 2 *
          (((Int.fract (x t j * s) : ℚ) : ℝ) *
            (1 - ((Int.fract (x t j * s) : ℚ) : ℝ)) / (s : ℝ) ^ 2) :=
        Fintype.sum_prod_type _
    _ = (1 / (s : ℝ) ^ 2) * ∑ t : Fin N, ∑ j : Fin n,
          (b t j) ^ 2 * ((Int.fract (x t j * s) : ℝ) *
            (1 - (Int.fract (x t j * s) : ℝ))) := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro j _
        push_cast
        ring

/-- The stochastic strengthening of `rounded_transcript_drift`:
`E[drift²] ≤ (1/(2s))²·∑ (b t j)²`. -/
theorem transcriptDrift_sq_le {N n : ℕ} (b : Fin N → Fin n → ℝ)
    (x : Fin N → Fin n → ℚ) {s : ℕ} (hs : 0 < s)
    (Nd : Fin N → Fin n → ℕ) {Q : ℕ} (hQ : 0 < Q)
    (hN : ∀ t : Fin N, ∀ j : Fin n,
      (Q : ℚ) * Int.fract (x t j * s) = Nd t j) :
    unifAvg (fun ε => (transcriptDrift (Q := Q) b x s Nd ε) ^ 2) ≤
      (1 / (2 * s)) ^ 2 * ∑ t : Fin N, ∑ j : Fin n, (b t j) ^ 2 := by
  rw [transcriptDrift_sq b x hs Nd hQ hN]
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  push_cast
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  apply Finset.sum_le_sum
  intro j _
  have hp0 : (0 : ℝ) ≤ Int.fract ((x t j : ℝ) * s) := Int.fract_nonneg _
  have hp1 : Int.fract ((x t j : ℝ) * s) ≤ 1 := (Int.fract_lt_one _).le
  have hquad : Int.fract ((x t j : ℝ) * s) *
      (1 - Int.fract ((x t j : ℝ) * s)) ≤ 1 / 4 := by
    have h := sq_nonneg (Int.fract ((x t j : ℝ) * s) - 1 / 2)
    linarith
  have hb2 : (0 : ℝ) ≤ (b t j) ^ 2 := sq_nonneg _
  calc (1 / (s : ℝ) ^ 2) * ((b t j) ^ 2 *
        (Int.fract ((x t j : ℝ) * s) * (1 - Int.fract ((x t j : ℝ) * s))))
      = (b t j) ^ 2 *
          (Int.fract ((x t j : ℝ) * s) * (1 - Int.fract ((x t j : ℝ) * s)) /
            (s : ℝ) ^ 2) := by ring
    _ ≤ (b t j) ^ 2 * ((1 / 4) / (s : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hb2
        exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hs')).mpr hquad
    _ = (1 / (2 * s)) ^ 2 * (b t j) ^ 2 := by
        field_simp
        ring

/-- Chebyshev tail for the transcript drift:
`Pr[|drift| ≥ u] ≤ (1/(2s))²·∑b²/u²`. -/
theorem transcriptDrift_tail_le {N n : ℕ} (b : Fin N → Fin n → ℝ)
    (x : Fin N → Fin n → ℚ) {s : ℕ} (hs : 0 < s)
    (Nd : Fin N → Fin n → ℕ) {Q : ℕ} (hQ : 0 < Q)
    (hN : ∀ t : Fin N, ∀ j : Fin n,
      (Q : ℚ) * Int.fract (x t j * s) = Nd t j) {u : ℝ} (hu : 0 < u) :
    unifAvg (fun ε : Fin (N * n) → Fin Q =>
        if u ≤ |transcriptDrift b x s Nd ε| then (1 : ℝ) else 0) ≤
      (1 / (2 * s)) ^ 2 * (∑ t : Fin N, ∑ j : Fin n, (b t j) ^ 2) /
        u ^ 2 := by
  have hcardQ : (0 : ℝ) < (Fintype.card (Fin (N * n) → Fin Q) : ℝ) := by
    rw [card_piFin, Fintype.card_fin]
    positivity
  have hu2 : (0 : ℝ) < u ^ 2 := sq_pos_of_pos hu
  have hmarkov := sq_mul_filter_card_le_sum_sq
    (fun ε : Fin (N * n) → Fin Q => transcriptDrift b x s Nd ε) hu.le
  have hE := transcriptDrift_sq_le b x hs Nd hQ hN
  have hsum : ∑ ε : Fin (N * n) → Fin Q,
      (transcriptDrift b x s Nd ε) ^ 2 ≤
        (1 / (2 * s)) ^ 2 * (∑ t : Fin N, ∑ j : Fin n, (b t j) ^ 2) *
          (Fintype.card (Fin (N * n) → Fin Q) : ℝ) := by
    have : ∑ ε : Fin (N * n) → Fin Q, (transcriptDrift b x s Nd ε) ^ 2 =
        unifAvg (fun ε : Fin (N * n) → Fin Q =>
          (transcriptDrift b x s Nd ε) ^ 2) *
          (Fintype.card (Fin (N * n) → Fin Q) : ℝ) := by
      rw [unifAvg, div_mul_cancel₀ _ hcardQ.ne']
    rw [this]
    exact mul_le_mul_of_nonneg_right hE hcardQ.le
  have hcount : ((Finset.univ.filter fun ε : Fin (N * n) → Fin Q =>
        u ≤ |transcriptDrift b x s Nd ε|).card : ℝ) ≤
        ((1 / (2 * s)) ^ 2 * (∑ t : Fin N, ∑ j : Fin n, (b t j) ^ 2) *
          (Fintype.card (Fin (N * n) → Fin Q) : ℝ)) / u ^ 2 := by
    rw [le_div_iff₀ hu2, mul_comm _ (u ^ 2)]
    exact hmarkov.trans hsum
  have hcard : ∑ ε : Fin (N * n) → Fin Q,
      (if u ≤ |transcriptDrift b x s Nd ε| then (1 : ℝ) else 0) =
        ((Finset.univ.filter fun ε : Fin (N * n) → Fin Q =>
          u ≤ |transcriptDrift b x s Nd ε|).card : ℝ) :=
    Finset.sum_boole _ _
  rw [unifAvg, hcard, div_le_iff₀ hcardQ, div_mul_eq_mul_div]
  exact hcount

/-- Worst-case sanity check: for *every* coin table the drift is at most
`(1/s)` times the coefficient mass — the randomized variance bound
`transcriptDrift_sq_le` strictly refines this deterministic bound. -/
theorem abs_transcriptDrift_le {N n : ℕ} (b : Fin N → Fin n → ℝ)
    (x : Fin N → Fin n → ℚ) {s : ℕ} (hs : 0 < s)
    (Nd : Fin N → Fin n → ℕ) {Q : ℕ}
    (ε : Fin (N * n) → Fin Q) :
    |transcriptDrift b x s Nd ε| ≤
      (1 / s) * ∑ t : Fin N, ∑ j : Fin n, |b t j| := by
  unfold transcriptDrift incSum
  calc |∑ k : Fin (N * n), (b (flatIdx k).1 (flatIdx k).2) *
        ((x (flatIdx k).1 (flatIdx k).2 : ℝ) -
          ((ditherRoundN (x (flatIdx k).1 (flatIdx k).2) s
            (Nd (flatIdx k).1 (flatIdx k).2) (ε k) : ℚ) : ℝ))|
      ≤ ∑ k : Fin (N * n), |b (flatIdx k).1 (flatIdx k).2| * (1 / s) := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have h := abs_ditherErr_le (x (flatIdx k).1 (flatIdx k).2) hs
          (N := Nd (flatIdx k).1 (flatIdx k).2) (ε k)
        unfold ditherErr at h
        rw [abs_sub_comm] at h
        exact h
    _ = (1 / s) * ∑ k : Fin (N * n), |b (flatIdx k).1 (flatIdx k).2| := by
        rw [← Finset.sum_mul, mul_comm]
    _ = (1 / s) * ∑ t : Fin N, ∑ j : Fin n, |b t j| := by
        congr 1
        calc ∑ k : Fin (N * n), |b (flatIdx k).1 (flatIdx k).2|
            = ∑ p : Fin N × Fin n, |b p.1 p.2| :=
              Equiv.sum_comp flatIdx fun p : Fin N × Fin n => |b p.1 p.2|
          _ = ∑ t : Fin N, ∑ j : Fin n, |b t j| :=
              Fintype.sum_prod_type _

/-! ## Compatibility: denominators and the `Q`-grid -/

/-- The denominator of `x·s` divides the denominator of `x`. Hence any `Q`
divisible by all state denominators is compatible with every step. -/
theorem rat_scaled_den_dvd (x : ℚ) (s : ℕ) : (x * s).den ∣ x.den := by
  have h := Rat.mul_den_dvd x (s : ℚ)
  have hden : ((s : ℚ)).den = 1 := by
    rw [Rat.den_natCast]
  rw [hden, mul_one] at h
  exact h

/-- If `(x·s).den` divides `Q`, the `Fin Q` coin model can realize the
exact randomized rounding: `Q·Int.fract(x·s)` is a natural number. -/
theorem dither_compatible_of_den_dvd (x : ℚ) (s : ℕ) {Q : ℕ} (_hQ : 0 < Q)
    (h : (x * s).den ∣ Q) :
    ∃ N : ℕ, (Q : ℚ) * Int.fract (x * s) = N := by
  set u : ℚ := x * s
  have hden : (u.den : ℚ) * Int.fract u =
      ((u.num - ⌊u⌋ * u.den : ℤ) : ℚ) := by
    simp only [Int.fract]
    push_cast
    rw [mul_sub, mul_comm (u.den : ℚ) u, Rat.mul_den_eq_num]
    ring
  obtain ⟨m, hm⟩ := h
  refine ⟨m * (u.num - ⌊u⌋ * u.den).toNat, ?_⟩
  have hz : (0 : ℤ) ≤ u.num - ⌊u⌋ * u.den := by
    have hf : (0 : ℚ) ≤ (u.den : ℚ) * Int.fract u :=
      mul_nonneg (by exact_mod_cast u.den_pos.le) (Int.fract_nonneg u)
    rw [hden] at hf
    exact_mod_cast hf
  have hQu : (Q : ℚ) = u.den * m := by exact_mod_cast hm
  have hzu : ((u.num - ⌊u⌋ * u.den).toNat : ℚ) =
      ((u.num - ⌊u⌋ * u.den : ℤ) : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hz
  push_cast
  rw [hQu, hzu, mul_comm (u.den : ℚ) (m : ℚ), mul_assoc, hden]

/-- Every finite family of states admits a compatible grid: take `Q` to be
the product of all denominators `(x i·s).den`. -/
theorem exists_dither_compatible {t : ℕ} (x : Fin t → ℚ) (s : ℕ) :
    ∃ Q : ℕ, 0 < Q ∧
      ∃ Nd : Fin t → ℕ, ∀ i, (Q : ℚ) * Int.fract (x i * s) = Nd i := by
  refine ⟨∏ i, (x i * s).den,
    Finset.prod_pos fun i _ => (x i * s).den_pos, ?_⟩
  have key : ∀ i : Fin t, ∃ N : ℕ,
      ((∏ i', (x i' * s).den : ℕ) : ℚ) * Int.fract (x i * s) = N := by
    intro i
    have hdvd : (x i * s).den ∣ ∏ i', (x i' * s).den :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    exact dither_compatible_of_den_dvd (x i) s
      (Finset.prod_pos fun i' _ => (x i' * s).den_pos) hdvd
  exact ⟨fun i => (key i).choose, fun i => (key i).choose_spec⟩

end Komlos
