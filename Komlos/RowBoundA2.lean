import Komlos.InitializationMargin
import Komlos.Curvature
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The (A.2) row bound: `2·ν(16 − H₀/r)/r² ≤ (1000/1009)·bdep`

For row mass `r ∈ (0, Rmax]` with `Rmax = 291/200`, the normalized row weight
`f(r) = 2·ν(u(r))/r²`, where `u(r) = 16 − H₀/r` and `H₀ = 263/5`, is increasing
in `r`.  Combined with the evaluation `f(Rmax) ≤ (1000/1009)·(3/625)` proved in
`InitializationMargin.lean`, this gives the uniform (A.2) coefficient bound.

We compute `f'` in the factored form

  `f'(r) = (2ν(u(r))/r³)·(9998·(H₀/r) − 39968)/(19984 + H₀/r)`,

which is `(K−2)·(H₀/r) − 4K + 32` over `2K − 16 + H₀/r` for `K = 10000`,
prove it is positive on `(0, Rmax]`, and conclude monotonicity via the mean
value theorem (`monotoneOn_of_hasDerivWithinAt_nonneg`).  The main theorem
`a2_row_quadratic_bound` lifts this scalar bound to the quadratic-form
statement with the two barrier weights `ν(Φ(±1, 0, r, G))`.
-/

namespace Komlos

open scoped BigOperators

/-- The barrier argument `u(r) = 16 − H₀/r` (with `H₀ = 263/5`). -/
noncomputable def rowArg (r : ℝ) : ℝ := 16 - (263 / 5) / r

/-- The normalized row weight `f(r) = 2·ν(u(r))/r²` bounded in (A.2). -/
noncomputable def rowFactor (r : ℝ) : ℝ := 2 * weight (rowArg r) / r ^ 2

/-- Factored form of the derivative of `rowFactor`:
`f'(r) = (2ν(u(r))/r³)·(9998·(H₀/r) − 39968)/(19984 + H₀/r)`. -/
noncomputable def rowFactorDeriv (r : ℝ) : ℝ :=
  2 * weight (rowArg r) / r ^ 3 *
    ((9998 * ((263 / 5) / r) - 39968) / (19984 + (263 / 5) / r))

/-- Since `r ≤ 291/200`, `1/r ≥ 200/291` and hence `H₀/r ≥ 10520/291`. -/
theorem rowArg_inv_bound {r : ℝ} (hr : 0 < r) (hrmax : r ≤ 291 / 200) :
    (10520 : ℝ) / 291 ≤ (263 / 5) / r := by
  have h := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 263 / 5 by norm_num) hr hrmax
  rwa [show (263 : ℝ) / 5 / (291 / 200) = 10520 / 291 by norm_num] at h

/-- `u(r) ≤ u(Rmax) = −5864/291 < 0`. -/
theorem rowArg_nonpos {r : ℝ} (hr : 0 < r) (hrmax : r ≤ 291 / 200) :
    rowArg r ≤ 0 := by
  have hbound := rowArg_inv_bound hr hrmax
  have h16 : (16 : ℝ) ≤ 10520 / 291 := by norm_num
  unfold rowArg
  linarith

/-- `u'(r) = (263/5)/r²`. -/
theorem hasDerivAt_rowArg {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt rowArg ((263 / 5) / r ^ 2) r := by
  have h1 : HasDerivAt (fun r : ℝ => (263 / 5) / r) (-(263 / 5) / r ^ 2) r := by
    apply ((hasDerivAt_const r (263 / 5 : ℝ)).div (hasDerivAt_id' r) hr).congr_deriv
    ring
  apply ((hasDerivAt_const r (16 : ℝ)).sub h1).congr_deriv
  ring

/-- The derivative of the row factor in factored form, valid for all `r > 0`. -/
theorem hasDerivAt_rowFactor {r : ℝ} (hr : 0 < r) :
    HasDerivAt rowFactor (rowFactorDeriv r) r := by
  have hweq : (1 : ℝ) - rowArg r / 20000 = (19984 + (263 / 5) / r) / 20000 := by
    unfold rowArg
    ring
  have hw : (1 : ℝ) - rowArg r / 20000 ≠ 0 := by
    rw [hweq]
    exact ne_of_gt (by positivity)
  have hu := hasDerivAt_rowArg hr.ne'
  have hW := HasDerivAt.comp r (hasDerivAt_weight hw) hu
  have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    apply (hasDerivAt_pow 2 r).congr_deriv
    simp
  have hf := (hW.const_mul (2 : ℝ)).div hp (pow_ne_zero 2 hr.ne')
  apply hf.congr_deriv
  unfold rowFactorDeriv
  simp only [Function.comp_apply]
  rw [weightDeriv_eq hw, hweq,
    ← show ((263 / 5 : ℝ) / r) / r = (263 / 5) / r ^ 2 by rw [div_div, pow_two]]
  set s := (263 / 5 : ℝ) / r with hs
  have hs0 : (0 : ℝ) < s := by rw [hs]; positivity
  have hden : (19984 : ℝ) + s ≠ 0 := ne_of_gt (by positivity)
  field_simp [hr.ne', hden]
  ring

/-- `f'(r) > 0` for `0 < r ≤ 291/200`: the numerator is at least
`9998·10520/291 − 39968 = 93548272/291 > 0`. -/
theorem rowFactor_deriv_pos {r : ℝ} (hr : 0 < r) (hrmax : r ≤ 291 / 200) :
    0 < rowFactorDeriv r := by
  have hbound := rowArg_inv_bound hr hrmax
  have hnu : (0 : ℝ) < 9998 * ((263 / 5) / r) - 39968 := by
    have h := mul_le_mul_of_nonneg_left hbound (show (0 : ℝ) ≤ 9998 by norm_num)
    norm_num at h
    linarith
  have hν : 0 < weight (rowArg r) := weight_pos (rowArg_nonpos hr hrmax)
  unfold rowFactorDeriv
  positivity

/-- `f` is differentiable, hence continuous, on `(0, Rmax]`. -/
theorem rowFactor_differentiableOn :
    DifferentiableOn ℝ rowFactor (Set.Ioc 0 (291 / 200)) :=
  fun _x hx => (hasDerivAt_rowFactor hx.1).differentiableAt.differentiableWithinAt

/-- Monotonicity of the row factor on `(0, 291/200]` via the mean value
theorem. -/
theorem rowFactor_mono {r r' : ℝ} (hr : 0 < r) (hrr : r ≤ r')
    (hr' : r' ≤ 291 / 200) : rowFactor r ≤ rowFactor r' := by
  have hmono : MonotoneOn rowFactor (Set.Ioc 0 (291 / 200)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f := rowFactor)
        (f' := rowFactorDeriv) (convex_Ioc (0 : ℝ) (291 / 200))
        rowFactor_differentiableOn.continuousOn ?_ ?_
    · intro x hx
      rw [interior_Ioc] at hx
      exact (hasDerivAt_rowFactor hx.1).hasDerivWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      exact (rowFactor_deriv_pos hx.1 hx.2.le).le
  exact hmono ⟨hr, hrr.trans hr'⟩ ⟨hr.trans_le hrr, hr'⟩ hrr

/-- The scalar (A.2) row bound: for `0 < r ≤ Rmax`,
`2·ν(16 − H₀/r)/r² ≤ (1000/1009)·bdep`. -/
theorem rowFactor_le_bound {r : ℝ} (hr : 0 < r) (hrmax : r ≤ 291 / 200) :
    2 * weight (16 - (263 / 5) / r) / r ^ 2 ≤ (1000 / 1009) * (3 / 625) := by
  have hRmax : rowFactor (291 / 200) ≤ (1000 / 1009) * (3 / 625) := by
    have heq : rowFactor (291 / 200) =
        2 * weight (-5864 / 291) / (291 / 200) ^ 2 := by
      unfold rowFactor rowArg
      rw [barrier_at_Rmax]
    rw [heq]
    exact row_weight_bound_at_Rmax
  exact (rowFactor_mono hr hrmax le_rfl).trans hRmax

/-- The barrier `Φ(σ, 0, r, G)` is dominated by `u(r) = 16 − H₀/r`
when `G ≤ r²` (the `4G/r²` term contributes at most `4`). -/
theorem barrier_le_rowArg {r : ℝ} (hr : 0 < r) {G : ℝ} (hG : G ≤ r ^ 2) (σ : ℝ) :
    barrier σ 0 r G ≤ rowArg r := by
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hG4 : 4 * G / r ^ 2 ≤ 4 := by
    rw [div_le_iff₀ hr2]
    nlinarith [hG]
  have he : barrier σ 0 r G = -((263 / 5) / r) + 4 * G / r ^ 2 + 12 := by
    unfold barrier
    ring
  rw [he]
  unfold rowArg
  linarith

/-- The (A.2) coefficient bound, quadratic-form (Loewner) version:
the two signed barrier weights times `(∑ pⱼxⱼ/r²)²` are dominated by
`(1000/1009)·bdep·∑ pⱼxⱼ²`. -/
theorem a2_row_quadratic_bound {s : ℕ} (p x : Fin s → ℝ) {r : ℝ}
    (hr : 0 < r) (hrmax : r ≤ 291 / 200) (hp : ∀ j, 0 ≤ p j)
    (hq : ∑ j, p j ≤ r ^ 2) {G : ℝ} (hG : G ≤ r ^ 2) (_hG0 : 0 ≤ G) :
    weight (barrier 1 0 r G) * (∑ j, (p j / r ^ 2) * x j) ^ 2 +
        weight (barrier (-1) 0 r G) * (∑ j, (p j / r ^ 2) * x j) ^ 2 ≤
      (1000 / 1009) * (3 / 625) * ∑ j, p j * (x j) ^ 2 := by
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hT : (0 : ℝ) ≤ ∑ j, p j * (x j) ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hp j) (sq_nonneg _)
  have hA0 : rowArg r ≤ 0 := rowArg_nonpos hr hrmax
  have hw1 : weight (barrier 1 0 r G) ≤ weight (rowArg r) :=
    weight_mono (barrier_le_rowArg hr hG 1) hA0
  have hw2 : weight (barrier (-1) 0 r G) ≤ weight (rowArg r) :=
    weight_mono (barrier_le_rowArg hr hG (-1)) hA0
  have hWnn : 0 ≤ weight (barrier 1 0 r G) + weight (barrier (-1) 0 r G) :=
    add_nonneg (weight_pos ((barrier_le_rowArg hr hG 1).trans hA0)).le
      (weight_pos ((barrier_le_rowArg hr hG (-1)).trans hA0)).le
  -- Cauchy–Schwarz: `(∑ pⱼxⱼ)² ≤ (∑ pⱼ)(∑ pⱼxⱼ²)`.
  have hCS : (∑ j, p j * x j) ^ 2 ≤ (∑ j, p j) * ∑ j, p j * (x j) ^ 2 := by
    have h := weighted_rank_one_domination p (fun _ => 1) x hp (fun _ => one_pos)
    simpa using h
  -- Rescaling: `(∑ (pⱼ/r²)xⱼ)² ≤ (∑ pⱼxⱼ²)/r²`.
  have hS : (∑ j, (p j / r ^ 2) * x j) ^ 2 ≤ (∑ j, p j * (x j) ^ 2) / r ^ 2 := by
    have hSe : (∑ j, (p j / r ^ 2) * x j) = (∑ j, p j * x j) / r ^ 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hSe, div_pow]
    calc (∑ j, p j * x j) ^ 2 / (r ^ 2) ^ 2
        ≤ (∑ j, p j) * (∑ j, p j * (x j) ^ 2) / (r ^ 2) ^ 2 :=
          div_le_div_of_nonneg_right hCS (sq_nonneg _)
      _ ≤ r ^ 2 * (∑ j, p j * (x j) ^ 2) / (r ^ 2) ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hq hT) (sq_nonneg _)
      _ = (∑ j, p j * (x j) ^ 2) / r ^ 2 := by
          field_simp [pow_ne_zero 2 hr.ne']
  -- Assembly.
  have hsum : weight (barrier 1 0 r G) + weight (barrier (-1) 0 r G) ≤
      2 * weight (rowArg r) := by linarith [hw1, hw2]
  have hfac : rowFactor r ≤ (1000 / 1009) * (3 / 625) := by
    have hRmax : rowFactor (291 / 200) ≤ (1000 / 1009) * (3 / 625) := by
      have heq : rowFactor (291 / 200) =
          2 * weight (-5864 / 291) / (291 / 200) ^ 2 := by
        unfold rowFactor rowArg
        rw [barrier_at_Rmax]
      rw [heq]
      exact row_weight_bound_at_Rmax
    exact (rowFactor_mono hr hrmax le_rfl).trans hRmax
  calc weight (barrier 1 0 r G) * (∑ j, (p j / r ^ 2) * x j) ^ 2 +
          weight (barrier (-1) 0 r G) * (∑ j, (p j / r ^ 2) * x j) ^ 2
      = (weight (barrier 1 0 r G) + weight (barrier (-1) 0 r G)) *
          (∑ j, (p j / r ^ 2) * x j) ^ 2 := by ring
    _ ≤ (weight (barrier 1 0 r G) + weight (barrier (-1) 0 r G)) *
          ((∑ j, p j * (x j) ^ 2) / r ^ 2) :=
        mul_le_mul_of_nonneg_left hS hWnn
    _ ≤ 2 * weight (rowArg r) * ((∑ j, p j * (x j) ^ 2) / r ^ 2) :=
        mul_le_mul_of_nonneg_right hsum (div_nonneg hT hr2.le)
    _ = rowFactor r * (∑ j, p j * (x j) ^ 2) := by
        unfold rowFactor
        ring
    _ ≤ (1000 / 1009) * (3 / 625) * (∑ j, p j * (x j) ^ 2) :=
        mul_le_mul_of_nonneg_right hfac hT

end Komlos
