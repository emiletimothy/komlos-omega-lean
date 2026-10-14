/-
# One-dimensional Gaussian moments, the χ²₁ mgf, and the small-ball bound

This module proves the concrete real-Gaussian facts about `N(0,1)` used by
"The Komlós Problem in Near Matrix-Multiplication Time" (Anand–Chen),
Appendix D / Lemma D.1 and Section 4.4:

* `gaussianReal_integral_pow_two_mul`: the even moments
  `𝔼[X^{2q}] = (2q − 1)‼`, which feeds the bound
  `d^q · 𝔼[u₁^{2q}] ≤ (2q − 1)‼` in the paper.
* `gaussianReal_integral_exp_mul_sq`: the χ²₁ moment-generating function
  `𝔼[e^{tX²}] = (1 − 2t)^{-1/2}` for `t < 1/2` — the ingredient behind
  `𝔼 e^{dU₁²/8} ≤ (3/4)^{-1/2} < 2`.
* `gaussianReal_Icc_le` / `gaussianReal_real_Icc_le`: the Gaussian small-ball
  bound `Pr[|X| ≤ u] ≤ √(2/π) · u`, used for `Pr[|r⊤w| ≤ u | P] ≤ √(2/π)·u`
  in Appendix D (item 6 of the dependency inventory of `GaussianCompletion.lean`).
* `gaussianReal_integral_sq`, `gaussianReal_variance_fun_id`,
  `gaussianReal_integral_id`: `𝔼[X²] = 1`, `Var[X] = 1`, `𝔼[X] = 0`.

All statements are proved from Mathlib's `gaussianReal`, its density formula
(`gaussianReal_apply_eq_integral`, `integral_gaussianReal_eq_integral_smul`),
its mgf (`mgf_id_gaussianReal` together with `iteratedDeriv_mgf_zero`), and the
Gaussian integral `integral_gaussian`. Nothing is assumed.
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.Variance

namespace Komlos

open MeasureTheory ProbabilityTheory
open scoped Nat Real

noncomputable section

/-!
## A. Iterated derivatives of `t ↦ exp (t²/2)` at `0`

The moment-generating function of `gaussianReal 0 1` is `t ↦ exp (t²/2)`
(`mgf_id_gaussianReal`), and `iteratedDeriv_mgf_zero` identifies its `n`-th
derivative at `0` with the `n`-th moment. Since `deriv (t ↦ exp (t²/2)) t =
t · exp (t²/2)`, Leibniz' rule (`iteratedDeriv_mul`) gives the two-step
recurrence `d_{n+2} = (n+1) · d_n`, hence `d_{2q} = (2q−1)‼`.
-/

/-- The first derivative of `t ↦ exp (t²/2)` is `t ↦ t · exp (t²/2)`. -/
private theorem deriv_exp_sq_half :
    deriv (fun t : ℝ ↦ Real.exp (t ^ 2 / 2)) = fun t ↦ t * Real.exp (t ^ 2 / 2) := by
  funext t
  have h2 : HasDerivAt (fun t : ℝ ↦ t ^ 2 / 2) t t := by
    convert (hasDerivAt_pow 2 t).div_const (2 : ℝ) using 1
    ring
  rw [h2.exp.deriv]
  ring

/-- Two-step recurrence for the iterated derivatives of `t ↦ exp (t²/2)` at `0`:
`d_{n+2} = (n+1) · d_n`. This is the Leibniz rule applied to
`deriv g = id · g`. -/
private theorem iteratedDeriv_exp_sq_half_step (n : ℕ) :
    iteratedDeriv (n + 2) (fun t : ℝ ↦ Real.exp (t ^ 2 / 2)) 0
      = (n + 1) * iteratedDeriv n (fun t : ℝ ↦ Real.exp (t ^ 2 / 2)) 0 := by
  have hmul : (fun t : ℝ ↦ t * Real.exp (t ^ 2 / 2))
      = (fun t : ℝ ↦ t) * fun t : ℝ ↦ Real.exp (t ^ 2 / 2) := rfl
  have hf : ContDiffAt ℝ (↑(n + 1)) (fun t : ℝ ↦ t) (0 : ℝ) := contDiff_id.contDiffAt
  have hg : ContDiffAt ℝ (↑(n + 1)) (fun t : ℝ ↦ Real.exp (t ^ 2 / 2)) (0 : ℝ) :=
    ((contDiff_id.pow 2).div_const 2).exp.contDiffAt
  have hn : n + 2 = (n + 1) + 1 := by omega
  rw [hn, iteratedDeriv_succ', deriv_exp_sq_half, hmul, iteratedDeriv_mul hf hg]
  rw [Finset.sum_eq_single 1]
  · simp [iteratedDeriv_fun_id_zero, Nat.choose_one_right]
  · intro i _ hi
    simp [iteratedDeriv_fun_id_zero, hi]
  · intro h
    exact absurd (Finset.mem_range.mpr (show 1 < n + 2 by omega)) h

/-- The `2q`-th derivative of `t ↦ exp (t²/2)` at `0` is `(2q − 1)‼`. -/
private theorem iteratedDeriv_exp_sq_half_two_mul (q : ℕ) :
    iteratedDeriv (2 * q) (fun t : ℝ ↦ Real.exp (t ^ 2 / 2)) 0
      = ((2 * q - 1)‼ : ℝ) := by
  induction q with
  | zero => simp [iteratedDeriv_zero]
  | succ q ih =>
    have e1 : 2 * (q + 1) = 2 * q + 2 := by ring
    have e2 : 2 * q + 2 - 1 = 2 * q + 1 := by omega
    rw [e1, iteratedDeriv_exp_sq_half_step (2 * q), ih, e2,
      Nat.doubleFactorial_add_one]
    push_cast
    ring

/-!
## B. Even moments of the standard Gaussian
-/

/-- The even moments of the standard real Gaussian are the odd double
factorials: `𝔼[X^{2q}] = (2q − 1)‼`. This is the moment bound used in the
paper's estimate `d^q · 𝔼[u₁^{2q}] ≤ (2q − 1)‼`. -/
theorem gaussianReal_integral_pow_two_mul (q : ℕ) :
    ∫ x, x ^ (2 * q) ∂(gaussianReal (0 : ℝ) 1) = ((2 * q - 1)‼ : ℝ) := by
  have h0 : 0 ∈ interior (integrableExpSet id (gaussianReal (0 : ℝ) 1)) := by
    simp
  have key : iteratedDeriv (2 * q) (mgf id (gaussianReal (0 : ℝ) 1)) 0
      = ∫ x, x ^ (2 * q) ∂(gaussianReal (0 : ℝ) 1) := by
    simpa using iteratedDeriv_mgf_zero h0 (2 * q)
  have hmgf : mgf id (gaussianReal (0 : ℝ) 1) = fun t : ℝ ↦ Real.exp (t ^ 2 / 2) := by
    rw [mgf_id_gaussianReal]
    funext t
    simp
  rw [← key, hmgf]
  exact iteratedDeriv_exp_sq_half_two_mul q

/-- The second moment of the standard Gaussian: `𝔼[X²] = 1`. -/
theorem gaussianReal_integral_sq :
    ∫ x, x ^ 2 ∂(gaussianReal (0 : ℝ) 1) = 1 := by
  simpa using gaussianReal_integral_pow_two_mul 1

/-- Restatement of Mathlib's `variance_fun_id_gaussianReal` at `N(0,1)`:
the variance is `1`. -/
theorem gaussianReal_variance_fun_id :
    Var[fun x : ℝ ↦ x; gaussianReal (0 : ℝ) 1] = 1 := by
  simp

/-- The mean of `gaussianReal 0 1` is `0` (special case of Mathlib's
`integral_id_gaussianReal`). -/
theorem gaussianReal_integral_id :
    ∫ x, x ∂(gaussianReal (0 : ℝ) 1) = 0 := by
  simp

/-!
## C. The χ²₁ moment-generating function
-/

/-- The χ²₁ mgf: for `t < 1/2`, `𝔼[e^{tX²}] = 1 / √(1 − 2t)`.
The proof writes the expectation against the Gaussian density
`(2π)^{-1/2} e^{-x²/2}` and completes the square in the exponent:
`e^{-x²/2} · e^{tx²} = e^{-((1-2t)/2) x²}`, then applies `integral_gaussian`. -/
theorem gaussianReal_integral_exp_mul_sq (t : ℝ) (_ht : t < 1 / 2) :
    ∫ x, Real.exp (t * x ^ 2) ∂(gaussianReal (0 : ℝ) 1)
      = (Real.sqrt (1 - 2 * t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (v := 1) one_ne_zero]
  simp_rw [smul_eq_mul]
  have hint : ∀ x : ℝ, gaussianPDFReal (0 : ℝ) 1 x * Real.exp (t * x ^ 2)
      = (√(2 * π))⁻¹ * Real.exp (-((1 - 2 * t) / 2) * x ^ 2) := by
    intro x
    have h2 : gaussianPDFReal (0 : ℝ) 1 x
        = (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
      simp [gaussianPDFReal]
    rw [h2, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hfun : (fun x : ℝ ↦ gaussianPDFReal (0 : ℝ) 1 x * Real.exp (t * x ^ 2))
      = fun x : ℝ ↦ (√(2 * π))⁻¹ * Real.exp (-((1 - 2 * t) / 2) * x ^ 2) :=
    funext hint
  rw [hfun, integral_const_mul, integral_gaussian]
  have h2pi : (0 : ℝ) < 2 * π := mul_pos two_pos Real.pi_pos
  have hd : π / ((1 - 2 * t) / 2) = 2 * π / (1 - 2 * t) := by
    rw [div_div_eq_mul_div, mul_comm π 2]
  rw [hd, Real.sqrt_div h2pi.le, ← mul_div_assoc,
    inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr h2pi), one_div]

/-- The χ²₁ mgf in `rpow` form: `𝔼[e^{tX²}] = (1 − 2t)^{-1/2}`. -/
theorem gaussianReal_integral_exp_mul_sq_rpow (t : ℝ) (ht : t < 1 / 2) :
    ∫ x, Real.exp (t * x ^ 2) ∂(gaussianReal (0 : ℝ) 1)
      = (1 - 2 * t) ^ (-(1 / 2 : ℝ)) := by
  rw [gaussianReal_integral_exp_mul_sq t ht, Real.sqrt_eq_rpow,
    ← Real.rpow_neg (by linarith : (0 : ℝ) ≤ 1 - 2 * t)]

/-!
## D. The Gaussian small-ball bound
-/

/-- The Gaussian density `gaussianPDFReal 0 1` is uniformly bounded by
`(2π)^{-1/2}`, since `e^{-x²/2} ≤ 1`. -/
private theorem gaussianPDFReal_zero_one_le (x : ℝ) :
    gaussianPDFReal (0 : ℝ) 1 x ≤ (√(2 * π))⁻¹ := by
  have h2 : gaussianPDFReal (0 : ℝ) 1 x = (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
    simp [gaussianPDFReal]
  rw [h2]
  have h1 : Real.exp (-(x ^ 2) / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) two_pos.le
  calc (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2)
      ≤ (√(2 * π))⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (√(2 * π))⁻¹ := mul_one _

/-- The small-ball bound used in Appendix D of the paper: for `u ≥ 0`,
`Pr[|X| ≤ u] ≤ √(2/π) · u` when `X ~ N(0,1)`. The density is bounded by
`(2π)^{-1/2}` and the interval has length `2u`. -/
theorem gaussianReal_Icc_le (u : ℝ) (hu : 0 ≤ u) :
    gaussianReal (0 : ℝ) 1 (Set.Icc (-u) u)
      ≤ ENNReal.ofReal (Real.sqrt (2 / π) * u) := by
  rw [gaussianReal_apply_eq_integral (0 : ℝ) one_ne_zero (Set.Icc (-u) u)]
  apply ENNReal.ofReal_le_ofReal
  have hvol : volume.real (Set.Icc (-u) u) = 2 * u := by
    show (volume (Set.Icc (-u) u)).toReal = 2 * u
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ u - -u)]
    ring
  have hconst : volume.real (Set.Icc (-u) u) * (√(2 * π))⁻¹
      = Real.sqrt (2 / π) * u := by
    rw [hvol]
    have h2pi : (0 : ℝ) < 2 * π := mul_pos two_pos Real.pi_pos
    have h4 : (4 : ℝ) / (2 * π) = 2 / π := by
      have h42 : (4 : ℝ) = 2 * 2 := by norm_num
      rw [h42, mul_div_mul_left 2 π (by norm_num : (2 : ℝ) ≠ 0)]
    have e : Real.sqrt (2 / π) = 2 * (√(2 * π))⁻¹ := by
      rw [← h4, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 4),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num),
        div_eq_mul_inv]
    rw [e]
    ring
  calc ∫ x in Set.Icc (-u) u, gaussianPDFReal (0 : ℝ) 1 x
      ≤ ∫ _ in Set.Icc (-u) u, (√(2 * π))⁻¹ :=
        setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn
          (integrableOn_const (by simp)) measurableSet_Icc
          (fun x _ ↦ gaussianPDFReal_zero_one_le x)
    _ = volume.real (Set.Icc (-u) u) * (√(2 * π))⁻¹ := by
        rw [setIntegral_const, smul_eq_mul]
    _ = Real.sqrt (2 / π) * u := hconst

/-- The small-ball bound in `Measure.real` form. -/
theorem gaussianReal_real_Icc_le (u : ℝ) (hu : 0 ≤ u) :
    (gaussianReal (0 : ℝ) 1).real (Set.Icc (-u) u) ≤ Real.sqrt (2 / π) * u := by
  have hC : 0 ≤ Real.sqrt (2 / π) * u := by positivity
  have hle : (gaussianReal (0 : ℝ) 1 (Set.Icc (-u) u)).toReal
      ≤ Real.sqrt (2 / π) * u := by
    have h := (ENNReal.toReal_le_toReal (measure_ne_top _ _)
      ENNReal.ofReal_ne_top).mpr (gaussianReal_Icc_le u hu)
    rwa [ENNReal.toReal_ofReal hC] at h
  exact hle

end
