/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Komlos.RandomizedCoupling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Sub-Gaussian concentration for predictable sign sums — Appendix C, (C.2)

`Komlos/RandomizedCoupling.lean` builds the finite coin-flip probability
model `unifAvg` and proves second-moment (Chebyshev) control of the
`incSum` walk. This file adds the *exponential* moment machinery and
proves the Appendix C sub-Gaussian tail estimate for the terminal value of
a predictable sign-weighted walk on the same finite model.

## The setup

* `boolSign : Bool → ℝ` is the fair `±1` sign, matching `realSigning`.
* `Predictable a` means `a i ε` depends only on the coins strictly before
  `i` — exactly the paper's "`aₜ` is determined by `σ₁,…,σ_{t-1}`".
* `signSum a σ ε = ∑ i, a i ε * σ (ε i)` is the terminal sum `S_k`.
* `SubgaussianSign σ` is the one-step mgf hypothesis
  `E_c[e^{y·σ c}] ≤ e^{y²/2}` consumed at every step of the recursion;
  for the fair sign it holds with equality `E = cosh`
  (`unifAvg_exp_boolSign`), and `Real.cosh_le_exp_half_sq` (newly in
  Mathlib) closes it.

## What is proved

* `unifAvg_exp_step_le`: the conditional-mgf recursion — peeling the fresh
  coin can only decrease the exponential potential
  `exp(λS − (λ²/2)·Σaᵢ²)`, provided `E[e^{y·σc}] ≤ e^{y²/2}`.
* `unifAvg_exp_signSum_sub_le_one`: the exponential supermartingale
  `E[exp(λS_k − (λ²/2)Σaᵢ²)] ≤ 1`, by induction over coins via
  `sum_pi_succ_snoc`/`unifAvg_pi_succ`.
* `unifAvg_exp_signSum_le`: `E[e^{λS_k}] ≤ e^{λ²Q/2}` whenever
  `Σᵢ aᵢ² ≤ Q` pointwise.
* `unifAvg_ind_le_exp_mgf`: the Chernoff/Markov step
  `Pr[f ≥ u] ≤ e^{-λu}·E[e^{λf}]`.
* `signSum_tail_le`: **(C.2), terminal-sum version**
  `Pr[|S_k| ≥ u] ≤ 2·exp(−u²/(2Q))`.

The max-over-prefixes strengthening of (C.2) needs Doob's maximal
inequality (or optional stopping) and is not formalized here; the
terminal bound is the version whose proof only uses the mgf recursion.
-/

namespace Komlos

open scoped BigOperators

/-- The fair `±1` sign of a `Bool` coin, matching `realSigning`. -/
def boolSign (b : Bool) : ℝ := if b then 1 else -1

/-- A sign map `σ : C → ℝ` on a finite coin type is *subgaussian* when its
exponential moments are bounded by the Gaussian mgf:
`E_c[e^{y·σ c}] ≤ e^{y²/2}` for all `y`. This is the hypothesis consumed
at each step of the martingale recursion. -/
def SubgaussianSign {C : Type*} [Fintype C] (σ : C → ℝ) : Prop :=
  ∀ y : ℝ, unifAvg (fun c : C => Real.exp (y * σ c)) ≤ Real.exp (y ^ 2 / 2)

/-- A family `a : Fin k → (Fin k → C) → ℝ` is *predictable* when `a i ε`
depends only on the coins strictly before `i`. -/
def Predictable {C : Type*} {k : ℕ} (a : Fin k → (Fin k → C) → ℝ) : Prop :=
  ∀ i : Fin k, ∀ ε ε' : Fin k → C,
    (∀ j : Fin k, j < i → ε j = ε' j) → a i ε = a i ε'

/-- The predictable sign-weighted sum `S_k(ε) = ∑ᵢ aᵢ(ε)·σ(εᵢ)`. -/
def signSum {C : Type*} {k : ℕ} (a : Fin k → (Fin k → C) → ℝ) (σ : C → ℝ)
    (ε : Fin k → C) : ℝ :=
  ∑ i : Fin k, a i ε * σ (ε i)

/-- Restriction of a coefficient family on `k+1` coins to the first `k`,
picking the fresh coin to be `c₀`. For predictable `a` the value does not
depend on `c₀` (`predictable_snoc_castSucc`). -/
def predictRestrict {C : Type*} {k : ℕ} (c₀ : C)
    (a : Fin (k + 1) → (Fin (k + 1) → C) → ℝ) : Fin k → (Fin k → C) → ℝ :=
  fun i η => a i.castSucc (Fin.snoc η c₀)

/-! ## Finite-probability helpers -/

/-- `unifAvg` is monotone in the integrand. -/
theorem unifAvg_le_unifAvg {ι : Type*} [Fintype ι] {f g : ι → ℝ}
    (h : ∀ a, f a ≤ g a) : unifAvg f ≤ unifAvg g := by
  rw [unifAvg, unifAvg]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
  · rw [h0, Nat.cast_zero, div_zero, div_zero]
  · exact (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr h0)).mpr
      (Finset.sum_le_sum fun a _ => h a)

/-- A constant factor on the right pulls out of `unifAvg`. -/
theorem unifAvg_mul_right {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
    unifAvg (fun a => f a * c) = unifAvg f * c := by
  have hcomm : (fun a => f a * c) = fun a => c * f a :=
    funext fun a => mul_comm _ _
  rw [hcomm, unifAvg_mul_left, mul_comm]

/-- Iterating `unifAvg`: averaging over `Fin (k+1) → C` is averaging over
the last coin inside the average over the first `k` coins. This is the
tower property of conditional expectation in the finite model. -/
theorem unifAvg_pi_succ {C : Type*} [Fintype C] {k : ℕ}
    (F : (Fin (k + 1) → C) → ℝ) :
    unifAvg F = unifAvg (fun η : Fin k → C =>
      unifAvg (fun c : C => F (Fin.snoc η c))) := by
  have hCk : (Fintype.card (Fin k → C) : ℝ) = (Fintype.card C : ℝ) ^ k := by
    rw [card_piFin]; norm_cast
  have hCk1 : (Fintype.card (Fin (k + 1) → C) : ℝ) =
      (Fintype.card C : ℝ) * (Fintype.card C : ℝ) ^ k := by
    rw [card_piFin]; push_cast; ring
  simp only [unifAvg]
  rw [sum_pi_succ_snoc F, hCk1, hCk, ← Finset.sum_div, div_div]

/-- `snoc` evaluated at a non-last coordinate reads the base table. -/
theorem snoc_eq_of_lt {C : Type*} {k : ℕ} (η : Fin k → C) (c : C)
    {j : Fin (k + 1)} (hj : j.val < k) :
    Fin.snoc (α := fun _ : Fin (k + 1) => C) η c j = η (Fin.castLT j hj) := by
  conv_lhs => rw [← Fin.castSucc_castLT j hj]
  rw [Fin.snoc_castSucc]

/-- For predictable `a`, the last coefficient `a_{last k}` of
`snoc η c` does not depend on the fresh coin `c`. -/
theorem predictable_snoc_last {C : Type*} {k : ℕ}
    {a : Fin (k + 1) → (Fin (k + 1) → C) → ℝ} (ha : Predictable a)
    (η : Fin k → C) (c c' : C) :
    a (Fin.last k) (Fin.snoc η c) = a (Fin.last k) (Fin.snoc η c') := by
  apply ha
  intro j hj
  have hjk : j.val < k := hj
  rw [snoc_eq_of_lt η c hjk, snoc_eq_of_lt η c' hjk]

/-- For predictable `a`, every `castSucc`-indexed coefficient of
`snoc η c` does not depend on the fresh coin `c`. -/
theorem predictable_snoc_castSucc {C : Type*} {k : ℕ}
    {a : Fin (k + 1) → (Fin (k + 1) → C) → ℝ} (ha : Predictable a)
    (η : Fin k → C) (c c' : C) (i : Fin k) :
    a i.castSucc (Fin.snoc η c) = a i.castSucc (Fin.snoc η c') := by
  apply ha
  intro j hj
  have hjk : j.val < k := lt_trans hj i.isLt
  rw [snoc_eq_of_lt η c hjk, snoc_eq_of_lt η c' hjk]

/-- The restriction `predictRestrict c₀ a` of a predictable family is
predictable. -/
theorem predictable_predictRestrict {C : Type*} {k : ℕ} (c₀ : C)
    {a : Fin (k + 1) → (Fin (k + 1) → C) → ℝ} (ha : Predictable a) :
    Predictable (predictRestrict c₀ a) := by
  intro i η η' h
  show a i.castSucc (Fin.snoc η c₀) = a i.castSucc (Fin.snoc η' c₀)
  apply ha
  intro j hj
  have hjk : j.val < k := lt_trans hj i.isLt
  rw [snoc_eq_of_lt η c₀ hjk, snoc_eq_of_lt η' c₀ hjk]
  exact h (Fin.castLT j hjk) hj

/-- Peeling the last coin off the sign sum: `S_{k+1}(snoc η c) =
S_k(η) + a_{last k}(η)·σ(c)` (predictability makes `a_{last k}`
`c`-independent). -/
theorem signSum_snoc {C : Type*} {k : ℕ} (c₀ : C)
    {a : Fin (k + 1) → (Fin (k + 1) → C) → ℝ} (ha : Predictable a)
    (σ : C → ℝ) (η : Fin k → C) (c : C) :
    signSum a σ (Fin.snoc η c) =
      signSum (predictRestrict c₀ a) σ η +
        a (Fin.last k) (Fin.snoc η c) * σ c := by
  unfold signSum
  rw [Fin.sum_univ_castSucc, Fin.snoc_last]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.snoc_castSucc, predictable_snoc_castSucc ha η c c₀ i]
  rfl

/-- Peeling the last coin off the coefficient energy `Σaᵢ²`. -/
theorem sum_sq_snoc {C : Type*} {k : ℕ} (c₀ : C)
    {a : Fin (k + 1) → (Fin (k + 1) → C) → ℝ} (ha : Predictable a)
    (η : Fin k → C) (c : C) :
    ∑ i : Fin (k + 1), (a i (Fin.snoc η c)) ^ 2 =
      ∑ i : Fin k, (predictRestrict c₀ a i η) ^ 2 +
        (a (Fin.last k) (Fin.snoc η c)) ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [predictable_snoc_castSucc ha η c c₀ i]
  rfl

/-! ## The one-step mgf and the exponential supermartingale -/

/-- **The conditional one-step bound**: averaging the exponential
potential `exp(λS − (λ²/2)·Σaᵢ²)` over the fresh coin can only decrease
it. This is `E[Z_{k+1} | η] ≤ Z_k` for the exponential supermartingale
`Z_k = exp(λS_k − (λ²/2)Σᵢaᵢ²)`. -/
theorem unifAvg_exp_step_le {C : Type*} [Fintype C] {k : ℕ}
    {σ : C → ℝ} (hσ : SubgaussianSign σ) (lam : ℝ)
    {a : Fin (k + 1) → (Fin (k + 1) → C) → ℝ} (ha : Predictable a)
    (c₀ : C) (η : Fin k → C) :
    unifAvg (fun c : C => Real.exp (lam * signSum a σ (Fin.snoc η c) -
        lam ^ 2 / 2 * ∑ i : Fin (k + 1), (a i (Fin.snoc η c)) ^ 2)) ≤
      Real.exp (lam * signSum (predictRestrict c₀ a) σ η -
        lam ^ 2 / 2 * ∑ i : Fin k, (predictRestrict c₀ a i η) ^ 2) := by
  have hfun : (fun c : C => Real.exp (lam * signSum a σ (Fin.snoc η c) -
        lam ^ 2 / 2 * ∑ i : Fin (k + 1), (a i (Fin.snoc η c)) ^ 2)) =
      fun c : C => Real.exp (lam * signSum (predictRestrict c₀ a) σ η -
          lam ^ 2 / 2 * ∑ i : Fin k, (predictRestrict c₀ a i η) ^ 2 -
          lam ^ 2 * (a (Fin.last k) (Fin.snoc η c₀)) ^ 2 / 2) *
        Real.exp (lam * (a (Fin.last k) (Fin.snoc η c₀)) * σ c) := by
    funext c
    rw [signSum_snoc c₀ ha σ η c, sum_sq_snoc c₀ ha η c,
      predictable_snoc_last ha η c c₀, ← Real.exp_add]
    congr 1
    ring
  rw [hfun, unifAvg_mul_left]
  calc Real.exp _ * unifAvg (fun c : C =>
          Real.exp (lam * (a (Fin.last k) (Fin.snoc η c₀)) * σ c))
      ≤ Real.exp _ * Real.exp ((lam * (a (Fin.last k)
          (Fin.snoc η c₀))) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left
          (hσ (lam * (a (Fin.last k) (Fin.snoc η c₀))))
          (Real.exp_pos _).le
    _ = Real.exp (lam * signSum (predictRestrict c₀ a) σ η -
        lam ^ 2 / 2 * ∑ i : Fin k, (predictRestrict c₀ a i η) ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- **The exponential supermartingale**: for predictable `a` and a
subgaussian sign map, `E[exp(λS_k − (λ²/2)·Σᵢaᵢ²)] ≤ 1`. -/
theorem unifAvg_exp_signSum_sub_le_one {C : Type*} [Fintype C]
    (hC : (Fintype.card C : ℝ) ≠ 0)
    {σ : C → ℝ} (hσ : SubgaussianSign σ) (lam : ℝ) :
    ∀ {k : ℕ} (a : Fin k → (Fin k → C) → ℝ), Predictable a →
      unifAvg (fun ε : Fin k → C =>
        Real.exp (lam * signSum a σ ε -
          lam ^ 2 / 2 * ∑ i : Fin k, (a i ε) ^ 2)) ≤ 1 := by
  intro k
  induction k with
  | zero =>
    intro a _
    have hcard1 : (Fintype.card (Fin 0 → C) : ℝ) = 1 := by
      rw [card_piFin, pow_zero]; norm_cast
    have hfun : (fun ε : Fin 0 → C =>
        Real.exp (lam * signSum a σ ε - lam ^ 2 / 2 * ∑ i, (a i ε) ^ 2)) =
        fun _ => (1 : ℝ) := by
      funext ε
      simp [signSum]
    rw [hfun, unifAvg, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      hcard1]
    norm_num
  | succ k ih =>
    intro a ha
    have hCpos : 0 < Fintype.card C :=
      Nat.pos_of_ne_zero (Nat.cast_ne_zero.mp hC)
    obtain ⟨c₀⟩ := Fintype.card_pos_iff.mp hCpos
    rw [unifAvg_pi_succ]
    refine (unifAvg_le_unifAvg fun η => ?_).trans
      (ih _ (predictable_predictRestrict c₀ ha))
    exact unifAvg_exp_step_le hσ lam ha c₀ η

/-- **The sub-Gaussian mgf bound**: `E[e^{λS_k}] ≤ e^{λ²Q/2}` for a
predictable sign sum with `Σᵢ aᵢ² ≤ Q` pointwise. -/
theorem unifAvg_exp_signSum_le {C : Type*} [Fintype C]
    (hC : (Fintype.card C : ℝ) ≠ 0)
    {σ : C → ℝ} (hσ : SubgaussianSign σ) (lam : ℝ) {k : ℕ}
    (a : Fin k → (Fin k → C) → ℝ) (ha : Predictable a) {Q : ℝ}
    (hQ : ∀ ε : Fin k → C, ∑ i : Fin k, (a i ε) ^ 2 ≤ Q) :
    unifAvg (fun ε : Fin k → C => Real.exp (lam * signSum a σ ε)) ≤
      Real.exp (lam ^ 2 * Q / 2) := by
  have point : ∀ ε : Fin k → C,
      Real.exp (lam * signSum a σ ε) ≤
        Real.exp (lam * signSum a σ ε - lam ^ 2 / 2 * ∑ i, (a i ε) ^ 2) *
          Real.exp (lam ^ 2 * Q / 2) := by
    intro ε
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have key : (0 : ℝ) ≤ lam ^ 2 / 2 * (Q - ∑ i, (a i ε) ^ 2) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (hQ ε))
    linarith
  calc unifAvg (fun ε : Fin k → C => Real.exp (lam * signSum a σ ε))
      ≤ unifAvg (fun ε : Fin k → C =>
            Real.exp (lam * signSum a σ ε -
              lam ^ 2 / 2 * ∑ i, (a i ε) ^ 2) *
            Real.exp (lam ^ 2 * Q / 2)) :=
        unifAvg_le_unifAvg point
    _ = unifAvg (fun ε : Fin k → C =>
            Real.exp (lam * signSum a σ ε -
              lam ^ 2 / 2 * ∑ i, (a i ε) ^ 2)) *
          Real.exp (lam ^ 2 * Q / 2) :=
        unifAvg_mul_right _ _
    _ ≤ 1 * Real.exp (lam ^ 2 * Q / 2) :=
        mul_le_mul_of_nonneg_right
          (unifAvg_exp_signSum_sub_le_one hC hσ lam a ha)
          (Real.exp_pos _).le
    _ = Real.exp (lam ^ 2 * Q / 2) := one_mul _

/-! ## Chernoff–Markov and the tail bound -/

/-- **Chernoff/Markov in the finite model**: `Pr[f ≥ u] ≤
e^{-λu}·E[e^{λf}]` for `λ > 0`. -/
theorem unifAvg_ind_le_exp_mgf {ι : Type*} [Fintype ι]
    {f : ι → ℝ} {lam : ℝ} (hlam : 0 < lam) (u : ℝ) (B : ℝ)
    (h : unifAvg (fun ε => Real.exp (lam * f ε)) ≤ B) :
    unifAvg (fun ε => if u ≤ f ε then (1 : ℝ) else 0) ≤
      B * Real.exp (-(lam * u)) := by
  have hfact : ∀ ε : ι, Real.exp (lam * (f ε - u)) =
      Real.exp (lam * f ε) * Real.exp (-(lam * u)) := by
    intro ε
    rw [← Real.exp_add]
    congr 1
    ring
  calc unifAvg (fun ε => if u ≤ f ε then (1 : ℝ) else 0)
      ≤ unifAvg (fun ε => Real.exp (lam * (f ε - u))) := by
        apply unifAvg_le_unifAvg
        intro ε
        by_cases hε : u ≤ f ε
        · rw [ite_eq_left hε]
          have hnn : 0 ≤ lam * (f ε - u) :=
            mul_nonneg hlam.le (sub_nonneg.mpr hε)
          have hexp := Real.exp_le_exp.mpr hnn
          rw [Real.exp_zero] at hexp
          exact hexp
        · rw [ite_eq_right hε]
          exact (Real.exp_pos _).le
    _ = unifAvg (fun ε => Real.exp (lam * f ε) * Real.exp (-(lam * u))) :=
        congrArg unifAvg (funext hfact)
    _ = unifAvg (fun ε => Real.exp (lam * f ε)) * Real.exp (-(lam * u)) :=
        unifAvg_mul_right _ _
    _ ≤ B * Real.exp (-(lam * u)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

/-- The two-sided indicator is at most the sum of the two one-sided
indicators: `u ≤ |f|` iff `u ≤ f` or `u ≤ -f`. -/
theorem unifAvg_ind_abs_le {ι : Type*} [Fintype ι] (f : ι → ℝ) (u : ℝ) :
    unifAvg (fun ε => if u ≤ |f ε| then (1 : ℝ) else 0) ≤
      unifAvg (fun ε => if u ≤ f ε then (1 : ℝ) else 0) +
        unifAvg (fun ε => if u ≤ -f ε then (1 : ℝ) else 0) := by
  rw [← unifAvg_add]
  apply unifAvg_le_unifAvg
  intro ε
  by_cases h : u ≤ |f ε|
  · rw [ite_eq_left h]
    rcases le_abs.mp h with h1 | h1
    · rw [ite_eq_left h1]
      by_cases h2 : u ≤ -f ε <;> simp [h2]
    · rw [ite_eq_left h1]
      by_cases h2 : u ≤ f ε <;> simp [h2]
  · rw [ite_eq_right h]
    by_cases h2 : u ≤ f ε <;> by_cases h3 : u ≤ -f ε <;> simp [h2, h3]

/-- Negating the coefficients negates the sign sum. -/
theorem signSum_neg {C : Type*} {k : ℕ} (a : Fin k → (Fin k → C) → ℝ)
    (σ : C → ℝ) (ε : Fin k → C) :
    signSum (fun i η => -(a i η)) σ ε = -signSum a σ ε := by
  unfold signSum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [neg_mul]

/-- Negating a predictable family is predictable. -/
theorem predictable_neg {C : Type*} {k : ℕ} {a : Fin k → (Fin k → C) → ℝ}
    (ha : Predictable a) : Predictable (fun i η => -(a i η)) := by
  intro i ε ε' h
  show -a i ε = -a i ε'
  rw [ha i ε ε' h]

/-! ## The fair `±1` sign is subgaussian -/

/-- The one-step mgf of a fresh fair `±1` sign is exactly `cosh`:
`E_σ[e^{yσ}] = (e^y + e^{-y})/2`. -/
theorem unifAvg_exp_boolSign (y : ℝ) :
    unifAvg (fun b : Bool => Real.exp (y * boolSign b)) = Real.cosh y := by
  have hsum : ∑ b : Bool, Real.exp (y * boolSign b) =
      Real.exp y + Real.exp (-y) := by
    rw [Fintype.univ_bool]
    simp [boolSign]
  rw [unifAvg, hsum, Fintype.card_bool, Real.cosh_eq]
  norm_cast

/-- The fair `±1` sign satisfies the subgaussian mgf hypothesis: this is
`cosh y ≤ e^{y²/2}`, i.e. `E_σ[e^{yσ·a}] ≤ e^{(ya)²/2}` at `a = ±1`. -/
theorem boolSign_subgaussian : SubgaussianSign boolSign := by
  intro y
  rw [unifAvg_exp_boolSign]
  exact Real.cosh_le_exp_half_sq y

/-! ## (C.2): the sub-Gaussian tail bound -/

/-- **Appendix C, estimate (C.2), terminal-sum version**: for predictable
coefficients `aᵢ` (determined by the coins strictly before step `i`) with
`Σᵢ aᵢ² ≤ Q` for every coin table, and fresh fair `±1` signs `σᵢ`, the
fraction of coin tables on which the terminal sum `S_k = Σᵢ aᵢ·σᵢ`
satisfies `|S_k| ≥ u` is at most `2·exp(−u²/(2Q))`.

Proof: Chernoff at `λ = u/Q`, `Pr[S ≥ u] ≤ e^{λ²Q/2 − λu} = e^{−u²/2Q}`,
plus the symmetric bound for `−S`. -/
theorem signSum_tail_le {k : ℕ} (a : Fin k → (Fin k → Bool) → ℝ)
    (ha : Predictable a) {Q u : ℝ}
    (hQ : ∀ ε : Fin k → Bool, ∑ i : Fin k, (a i ε) ^ 2 ≤ Q)
    (hQ0 : 0 < Q) (hu : 0 < u) :
    unifAvg (fun ε : Fin k → Bool =>
        if u ≤ |signSum a boolSign ε| then (1 : ℝ) else 0) ≤
      2 * Real.exp (- u ^ 2 / (2 * Q)) := by
  have hC : (Fintype.card Bool : ℝ) ≠ 0 := by
    rw [Fintype.card_bool]; norm_num
  set lam : ℝ := u / Q with hlam_def
  have hlam : 0 < lam := div_pos hu hQ0
  have hexp : lam ^ 2 * Q / 2 + -(lam * u) = - u ^ 2 / (2 * Q) := by
    rw [hlam_def]
    have hQ0' : Q ≠ 0 := hQ0.ne'
    field_simp
    ring
  have hmgf_val : Real.exp (lam ^ 2 * Q / 2) * Real.exp (-(lam * u)) =
      Real.exp (- u ^ 2 / (2 * Q)) := by
    rw [← Real.exp_add, hexp]
  have hpos : unifAvg (fun ε : Fin k → Bool =>
        if u ≤ signSum a boolSign ε then (1 : ℝ) else 0) ≤
      Real.exp (- u ^ 2 / (2 * Q)) := by
    have hmgf : unifAvg (fun ε : Fin k → Bool =>
          Real.exp (lam * signSum a boolSign ε)) ≤
        Real.exp (lam ^ 2 * Q / 2) :=
      unifAvg_exp_signSum_le hC boolSign_subgaussian lam a ha hQ
    have h1 := unifAvg_ind_le_exp_mgf hlam u _ hmgf
    rwa [hmgf_val] at h1
  have hneg : unifAvg (fun ε : Fin k → Bool =>
        if u ≤ -signSum a boolSign ε then (1 : ℝ) else 0) ≤
      Real.exp (- u ^ 2 / (2 * Q)) := by
    have hfun : (fun ε : Fin k → Bool =>
          if u ≤ -signSum a boolSign ε then (1 : ℝ) else 0) =
        fun ε => if u ≤ signSum (fun i η => -(a i η)) boolSign ε then
          (1 : ℝ) else 0 := by
      funext ε
      rw [signSum_neg]
    have hQ' : ∀ ε : Fin k → Bool,
        ∑ i : Fin k, ((fun i η => -(a i η)) i ε) ^ 2 ≤ Q := by
      intro ε
      simpa using hQ ε
    have hmgf : unifAvg (fun ε : Fin k → Bool =>
          Real.exp (lam * signSum (fun i η => -(a i η)) boolSign ε)) ≤
        Real.exp (lam ^ 2 * Q / 2) :=
      unifAvg_exp_signSum_le hC boolSign_subgaussian lam _
        (predictable_neg ha) hQ'
    have h1 := unifAvg_ind_le_exp_mgf hlam u _ hmgf
    rw [hmgf_val] at h1
    rwa [hfun]
  calc unifAvg (fun ε : Fin k → Bool =>
        if u ≤ |signSum a boolSign ε| then (1 : ℝ) else 0)
      ≤ unifAvg (fun ε : Fin k → Bool =>
            if u ≤ signSum a boolSign ε then (1 : ℝ) else 0) +
          unifAvg (fun ε : Fin k → Bool =>
            if u ≤ -signSum a boolSign ε then (1 : ℝ) else 0) :=
        unifAvg_ind_abs_le _ u
    _ ≤ Real.exp (- u ^ 2 / (2 * Q)) + Real.exp (- u ^ 2 / (2 * Q)) :=
        add_le_add hpos hneg
    _ = 2 * Real.exp (- u ^ 2 / (2 * Q)) := by ring

end Komlos
