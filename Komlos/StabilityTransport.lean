import Komlos.HessianDecomposition

/-!
# Stability transport for the curvature bound (Appendix B)

The resolvent potential's curvature `∇²F_b = P − D` is controlled at the
anchor `x₀` by the spectral subspace (`exists_subspace_quadP_le`).  The
paper then transports this bound to every `x` in the window
`B = {x : ‖x − x₀‖∞ ≤ a}`: writing `y = x − x₀`, the estimates
(B.5)–(B.10) compare the resolvent, weights, and curvature matrices at
`x` with their anchor values.

This module develops the displacement-level ingredients:

* `barrierAt`: the quadratic row barrier `uᵢ(x₀ + y) = uᵢ + gᵢᵀy −
  4∑ⱼ zᵢⱼ yⱼ²` of (2.2), and its effective gradient
  `gᵢ(x) = gᵢ − 8·zᵢ∘y` (`gradAt`), which satisfies
  `uᵢ(x₀ + t·h)' = (gradAt g z (t·h))ᵀh`.
* The (B.6) bound `((gᵢ(x) − gᵢ)ᵀh)² ≤ 64 a²·∑ⱼ zᵢⱼ hⱼ²`, from
  `1ᵀzᵢ ≤ 1`, `‖y‖∞ ≤ a`, and weighted Cauchy–Schwarz.
* Barrier and slope increment bounds `|tᵢ| ≤ a`, `|Δuᵢ| ≤ |gᵢᵀy| + 4a²`
  used with the weight-stability factors of `Curvature.lean`.
-/

open Matrix Finset Real
open scoped BigOperators

namespace Komlos

/-! ## The displacement barrier and its effective gradient -/

/-- The quadratic row barrier (2.2): `uᵢ(x₀ + y) = uᵢ + gᵢᵀy −
4∑ⱼ zᵢⱼ yⱼ²`.  The negative quadratic energy term is what generates
the paper's diagonal `D` in `∇²F = P − D`. -/
noncomputable def barrierAt {s : ℕ} (u : ℝ) (g z y : Fin s → ℝ) : ℝ :=
  u + g ⬝ᵥ y - 4 * ∑ j, z j * y j ^ 2

/-- The effective gradient along the quadratic barrier:
`gᵢ(x₀ + y) = gᵢ − 8·zᵢ∘y`, so that `∇uᵢ(x₀+y)ᵀh = gᵢᵀh −
8∑ⱼ zᵢⱼ yⱼ hⱼ`. -/
noncomputable def gradAt {s : ℕ} (g z y : Fin s → ℝ) : Fin s → ℝ :=
  fun j => g j - 8 * z j * y j

/-- The gradient difference is `−8·zᵢ∘y`. -/
theorem gradAt_sub_dot {s : ℕ} {g z y h : Fin s → ℝ} :
    ((fun j => gradAt g z y j - g j) ⬝ᵥ h) =
      -8 * ∑ j, z j * y j * h j := by
  simp only [gradAt, dotProduct]
  rw [Finset.sum_congr rfl fun j _ => show
      (g j - 8 * z j * y j - g j) * h j =
        -(8 * (z j * y j * h j)) from by ring]
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

/-- `(gradAt g z y)ᵀh = gᵀh − 8∑ⱼ zᵢⱼ yⱼ hⱼ`. -/
theorem gradAt_dot {s : ℕ} {g z y h : Fin s → ℝ} :
    (gradAt g z y ⬝ᵥ h) = g ⬝ᵥ h - 8 * ∑ j, z j * y j * h j := by
  simp only [gradAt, dotProduct, sub_mul]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl fun j _ => show
      8 * z j * y j * h j = 8 * (z j * y j * h j) from by ring,
    ← Finset.mul_sum]

/-- The barrier increment splits into a linear and a nonpositive
quadratic part. -/
theorem barrierAt_sub {s : ℕ} {u : ℝ} {g z y : Fin s → ℝ} :
    barrierAt u g z y - u = g ⬝ᵥ y - 4 * ∑ j, z j * y j ^ 2 := by
  unfold barrierAt; ring

/-- For `z ≥ 0`, the quadratic part is nonpositive, so
`uᵢ(x₀ + y) ≤ uᵢ + gᵢᵀy`. -/
theorem barrierAt_le {s : ℕ} {u : ℝ} {g z y : Fin s → ℝ}
    (hz : ∀ j, 0 ≤ z j) :
    barrierAt u g z y ≤ u + g ⬝ᵥ y := by
  unfold barrierAt
  have : 0 ≤ ∑ j, z j * y j ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hz j) (sq_nonneg _)
  linarith

/-- Fixed rows are nonincreasing: `uᵢ(x) − uᵢ(x₀) = −4∑ⱼzᵢⱼyⱼ² ≤ 0`
when the linear coefficient vanishes. -/
theorem barrierAt_change_nonpos {s : ℕ} {u : ℝ} {g z y : Fin s → ℝ}
    (hz : ∀ j, 0 ≤ z j) (hg : g ⬝ᵥ y = 0) :
    barrierAt u g z y ≤ u := by
  unfold barrierAt
  rw [hg]
  have : 0 ≤ ∑ j, z j * y j ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hz j) (sq_nonneg _)
  linarith

/-- `|tᵢ| = |zᵢᵀy| ≤ a·∑ⱼzᵢⱼ` for `‖y‖∞ ≤ a`, `z ≥ 0`. -/
theorem abs_z_dot_le {s : ℕ} {z y : Fin s → ℝ} {a : ℝ}
    (hz : ∀ j, 0 ≤ z j) (hy : ∀ j, |y j| ≤ a) :
    |z ⬝ᵥ y| ≤ a * ∑ j, z j := by
  calc |z ⬝ᵥ y|
      = |∑ j, z j * y j| := rfl
    _ ≤ ∑ j, |z j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, z j * |y j| := by
        apply Finset.sum_congr rfl; intro j _
        rw [abs_mul, abs_of_nonneg (hz j)]
    _ ≤ ∑ j, z j * a :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hy j) (hz j)
    _ = a * ∑ j, z j := by
        rw [Finset.sum_congr rfl fun j _ => mul_comm (z j) a,
          ← Finset.mul_sum]

/-- `|tᵢ| ≤ a` when additionally `1ᵀzᵢ ≤ 1` and `a ≥ 0`. -/
theorem abs_z_dot_le_of_sum_le {s : ℕ} {z y : Fin s → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hz : ∀ j, 0 ≤ z j) (hz1 : ∑ j, z j ≤ 1)
    (hy : ∀ j, |y j| ≤ a) :
    |z ⬝ᵥ y| ≤ a := by
  refine le_trans (abs_z_dot_le hz hy) ?_
  have hs : 0 ≤ ∑ j, z j := Finset.sum_nonneg fun j _ => hz j
  calc a * ∑ j, z j ≤ a * 1 :=
        mul_le_mul_of_nonneg_left hz1 ha
    _ = a := mul_one a

/-- `|Δuᵢ| ≤ |gᵢᵀy| + 4a²·∑ⱼzᵢⱼ` for `‖y‖∞ ≤ a`, `z ≥ 0`. -/
theorem abs_barrierAt_sub_le {s : ℕ} {u : ℝ} {g z y : Fin s → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hz : ∀ j, 0 ≤ z j) (hy : ∀ j, |y j| ≤ a) :
    |barrierAt u g z y - u| ≤ |g ⬝ᵥ y| + 4 * a ^ 2 * ∑ j, z j := by
  rw [barrierAt_sub]
  have hq : |∑ j, z j * y j ^ 2| ≤ a ^ 2 * ∑ j, z j := by
    have hnn : ∀ j, 0 ≤ z j * y j ^ 2 :=
      fun j => mul_nonneg (hz j) (sq_nonneg _)
    calc |∑ j, z j * y j ^ 2|
        = ∑ j, z j * y j ^ 2 :=
          abs_of_nonneg (Finset.sum_nonneg fun j _ => hnn j)
      _ ≤ ∑ j, z j * a ^ 2 := by
          apply Finset.sum_le_sum; intro j _
          apply mul_le_mul_of_nonneg_left _ (hz j)
          exact sq_le_sq.mpr ((abs_of_nonneg ha).symm ▸ hy j)
      _ = a ^ 2 * ∑ j, z j := by
          rw [Finset.sum_congr rfl fun j _ => mul_comm (z j) (a ^ 2),
            ← Finset.mul_sum]
  calc |g ⬝ᵥ y - 4 * ∑ j, z j * y j ^ 2|
      ≤ |g ⬝ᵥ y| + |4 * ∑ j, z j * y j ^ 2| := abs_sub _ _
    _ = |g ⬝ᵥ y| + 4 * |∑ j, z j * y j ^ 2| := by rw [abs_mul]; norm_num
    _ ≤ |g ⬝ᵥ y| + 4 * (a ^ 2 * ∑ j, z j) := by linarith
    _ = |g ⬝ᵥ y| + 4 * a ^ 2 * ∑ j, z j := by ring

/-- **The (B.6) bound.** `((gᵢ(x) − gᵢ)ᵀh)² ≤ 64 a²·∑ⱼ zᵢⱼ hⱼ²` for
`‖y‖∞ ≤ a`, `z ≥ 0`, `1ᵀz ≤ 1`. -/
theorem gradDiff_sq_le {s : ℕ} {z y h : Fin s → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hz : ∀ j, 0 ≤ z j) (hz1 : ∑ j, z j ≤ 1)
    (hy : ∀ j, |y j| ≤ a) :
    (8 * ∑ j, z j * y j * h j) ^ 2 ≤ 64 * a ^ 2 * ∑ j, z j * h j ^ 2 := by
  have habs : |∑ j, z j * y j * h j| ≤ a * ∑ j, z j * |h j| := by
    calc |∑ j, z j * y j * h j|
        ≤ ∑ j, |z j * y j * h j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, z j * |y j| * |h j| := by
          apply Finset.sum_congr rfl; intro j _
          rw [abs_mul, abs_mul, abs_of_nonneg (hz j)]
      _ ≤ ∑ j, z j * a * |h j| :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hy j) (hz j)) (abs_nonneg _)
      _ = a * ∑ j, z j * |h j| := by
          rw [Finset.sum_congr rfl fun j _ => show
              z j * a * |h j| = a * (z j * |h j|) from by ring,
            ← Finset.mul_sum]
  have hcs : (∑ j, z j * |h j|) ^ 2 ≤
      (∑ j, z j) * ∑ j, z j * h j ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun j _ => hz j) (fun j _ => mul_nonneg (hz j) (sq_nonneg _))
    intro j _
    rw [mul_pow, sq_abs]
    exact le_of_eq (by ring)
  have hs : 0 ≤ ∑ j, z j := Finset.sum_nonneg fun j _ => hz j
  have hq : 0 ≤ ∑ j, z j * h j ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hz j) (sq_nonneg _)
  have hnn : 0 ≤ a * ∑ j, z j * |h j| :=
    mul_nonneg ha (Finset.sum_nonneg
      fun j _ => mul_nonneg (hz j) (abs_nonneg _))
  calc (8 * ∑ j, z j * y j * h j) ^ 2
      = 64 * (∑ j, z j * y j * h j) ^ 2 := by ring
    _ ≤ 64 * (a * ∑ j, z j * |h j|) ^ 2 :=
        mul_le_mul_of_nonneg_left (sq_le_sq.mpr
          ((abs_of_nonneg hnn).symm ▸ habs)) (by norm_num)
    _ = 64 * a ^ 2 * (∑ j, z j * |h j|) ^ 2 := by ring
    _ ≤ 64 * a ^ 2 * ((∑ j, z j) * ∑ j, z j * h j ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ ≤ 64 * a ^ 2 * (1 * ∑ j, z j * h j ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hz1 hq) (by positivity)
    _ = 64 * a ^ 2 * ∑ j, z j * h j ^ 2 := by ring

/-- (B.6) restated at the gradient: `((gᵢ(x) − gᵢ)ᵀh)² ≤
64 a²·∑ⱼ zᵢⱼ hⱼ²`. -/
theorem gradAt_sub_dot_sq_le {s : ℕ} {g z y h : Fin s → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hz : ∀ j, 0 ≤ z j) (hz1 : ∑ j, z j ≤ 1)
    (hy : ∀ j, |y j| ≤ a) :
    ((fun j => gradAt g z y j - g j) ⬝ᵥ h) ^ 2 ≤
      64 * a ^ 2 * ∑ j, z j * h j ^ 2 := by
  rw [gradAt_sub_dot]
  have hle := gradDiff_sq_le (h := h) ha hz hz1 hy
  rwa [neg_mul, neg_sq]

/-! ## The transport closing argument

The last step of the stability proof: the anchor margin
`P₀ ≤ (1−ρ)·D₀`, the additive transport `Pₓ ≤ P₀ + ε·D₀`, and the
relative diagonal stability `Dₓ ≥ (1−δ)·D₀` close to
`Pₓ ≤ (1−ρ/2)·Dₓ` whenever `ε + δ ≤ ρ/2` — the paper's conclusion
`Pₓ[h] − (1−ρ/2)Dₓ[h] ≤ 0` for `a ≤ cρ/(1+κ)²`. -/

/-- Scalar transport closing: margin + additive error + relative
diagonal stability give the window bound. -/
theorem transport_close {P0 D0 Px Dx ε δ ρ : ℝ}
    (hD0 : 0 ≤ D0) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hδ : 0 ≤ δ)
    (hanch : P0 ≤ (1 - ρ) * D0)
    (hPx : Px ≤ P0 + ε * D0)
    (hDx : (1 - δ) * D0 ≤ Dx)
    (hεδ : ε + δ ≤ ρ / 2) :
    Px ≤ (1 - ρ / 2) * Dx := by
  have h1 : (1 - ρ + ε) * D0 ≤ (1 - ρ / 2) * ((1 - δ) * D0) := by
    rw [show (1 - ρ / 2) * ((1 - δ) * D0) =
        ((1 - ρ / 2) * (1 - δ)) * D0 from by rw [← mul_assoc]]
    apply mul_le_mul_of_nonneg_right _ hD0
    nlinarith [mul_nonneg hρ hδ]
  calc Px
      ≤ P0 + ε * D0 := hPx
    _ ≤ (1 - ρ) * D0 + ε * D0 := by linarith
    _ = (1 - ρ + ε) * D0 := by ring
    _ ≤ (1 - ρ / 2) * ((1 - δ) * D0) := h1
    _ ≤ (1 - ρ / 2) * Dx :=
        mul_le_mul_of_nonneg_left hDx (by linarith)

/-- **Subspace transport.** If `E` is the nonpositive subspace of
`P₀ − (1−ρ)D₀` produced by `exists_subspace_quadP_le`, and for every
`h ∈ E` the moved quadratic forms satisfy `Pₜ[h] ≤ P₀[h] + ε·D₀[h]`
and `Dₜ[h] ≥ (1−δ)·D₀[h]` with `ε + δ ≤ ρ/2`, then the transported
bound `Pₜ[h] ≤ (1−ρ/2)·Dₜ[h]` holds on all of `E` — the hypothesis
of `concaveOn_of_transported_bound` with margin `ρ/2`. -/
theorem transported_subspace_bound {m s : ℕ} {θ ρ ε δ : ℝ}
    {z g : Fin m → Fin s → ℝ} {u : Fin m → ℝ} {v : Fin s → ℝ}
    {R : Matrix (Fin s) (Fin s) ℝ}
    (hR : R.PosSemidef) (hθ : 0 ≤ θ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 ≤ δ)
    (hz : ∀ i j, 0 ≤ z i j) (hu : ∀ i, u i ≤ 0)
    (hQD : ∀ j, Pmat z g u v R j j ≤ θ * ((1 - ρ) • Dmat z u v) j j)
    (Pt Dt : (Fin s → ℝ) → ℝ)
    (hPx : ∀ h, Pt h ≤ quadP z g u v h R + ε * quadD z u v h)
    (hDx : ∀ h, (1 - δ) * quadD z u v h ≤ Dt h)
    (hεδ : ε + δ ≤ ρ / 2) :
    ∃ E : Submodule ℝ (Fin s → ℝ),
      (s : ℝ) - θ * s ≤ Module.finrank ℝ E ∧
      ∀ h ∈ E, Pt h ≤ (1 - ρ / 2) * Dt h := by
  obtain ⟨E, hEdim, hE⟩ := exists_subspace_quadP_le hR hθ hρ1 hz hu hQD
  refine ⟨E, hEdim, fun h hh => ?_⟩
  have hD0 : 0 ≤ quadD z u v h := quadD_nonneg hz hu
  exact transport_close hD0 hρ0 hρ1 hδ (hE h hh) (hPx h) (hDx h) hεδ

/-! ## Diagonal stability (B.5)

`Dₓ[h] = 8∑ᵢ ν′(uᵢ(x))·tᵢ(x)²·∑ⱼ zᵢⱼ hⱼ²` with loads
`tᵢ = zᵢᵀv`.  Relative changes in the weights and loads give the
two-sided comparison `(1−δ)D₀ ≤ Dₓ ≤ (1+δ)D₀`. -/

/-- Loads are nonnegative when `z, v ≥ 0`. -/
theorem z_dot_nonneg {s : ℕ} {z v : Fin s → ℝ}
    (hz : ∀ j, 0 ≤ z j) (hv : ∀ j, 0 ≤ v j) :
    0 ≤ z ⬝ᵥ v :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hz j) (hv j)

/-- If `|tᵢ' − tᵢ| ≤ ε·tᵢ` with `tᵢ, ε ≥ 0`, then `tᵢ'² ≤ (1+ε)²·tᵢ²`. -/
theorem sq_le_of_abs_sub_le {t t' ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (h : |t' - t| ≤ ε * t) :
    t' ^ 2 ≤ (1 + ε) ^ 2 * t ^ 2 := by
  have h1 : t' - t ≤ ε * t := (abs_le.mp h).2
  have h2 : -(ε * t) ≤ t' - t := (abs_le.mp h).1
  have ht' : |t'| ≤ (1 + ε) * t := by
    apply abs_le.mpr
    constructor <;> nlinarith
  rw [← mul_pow, sq_le_sq,
    abs_of_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 + ε) ht)]
  exact ht'

/-- Upper `D` stability: if the weights and loads change by relative
factors at most `ε₁` and `ε₂`, then `Dₓ ≤ (1+ε₁)(1+ε₂)²·D₀`. -/
theorem quadD_rel_le {m s : ℕ} {z : Fin m → Fin s → ℝ}
    {u u' : Fin m → ℝ} {v v' : Fin s → ℝ} {h : Fin s → ℝ}
    {ε₁ ε₂ : ℝ}
    (hz : ∀ i j, 0 ≤ z i j) (hv : ∀ j, 0 ≤ v j)
    (hu : ∀ i, u i ≤ 0) (_hu' : ∀ i, u' i ≤ 0)
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (hν : ∀ i, weightDeriv (u' i) ≤ (1 + ε₁) * weightDeriv (u i))
    (ht : ∀ i, |z i ⬝ᵥ v' - z i ⬝ᵥ v| ≤ ε₂ * (z i ⬝ᵥ v)) :
    quadD z u' v' h ≤ (1 + ε₁) * (1 + ε₂) ^ 2 * quadD z u v h := by
  unfold quadD barrierQuad
  have key : ∀ i, weightDeriv (u' i) * (z i ⬝ᵥ v') ^ 2 * ∑ j, z i j * h j ^ 2
      ≤ (1 + ε₁) * (1 + ε₂) ^ 2 *
        (weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2 * ∑ j, z i j * h j ^ 2) := by
    intro i
    have ht0 : 0 ≤ z i ⬝ᵥ v := z_dot_nonneg (hz i) hv
    have hsq : (z i ⬝ᵥ v') ^ 2 ≤ (1 + ε₂) ^ 2 * (z i ⬝ᵥ v) ^ 2 :=
      sq_le_of_abs_sub_le ht0 hε₂ (ht i)
    have hbq : 0 ≤ ∑ j, z i j * h j ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hz i j) (sq_nonneg _)
    have hν0' : 0 ≤ (1 + ε₁) * weightDeriv (u i) :=
      mul_nonneg (by linarith) (weightDeriv_pos (hu i)).le
    calc weightDeriv (u' i) * (z i ⬝ᵥ v') ^ 2 * ∑ j, z i j * h j ^ 2
        ≤ (1 + ε₁) * weightDeriv (u i) * ((1 + ε₂) ^ 2 * (z i ⬝ᵥ v) ^ 2) *
            ∑ j, z i j * h j ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hbq
          exact mul_le_mul (hν i) hsq (sq_nonneg _) hν0'
        _ = (1 + ε₁) * (1 + ε₂) ^ 2 *
            (weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2 * ∑ j, z i j * h j ^ 2) := by
            ring
  calc 8 * ∑ i, weightDeriv (u' i) * (z i ⬝ᵥ v') ^ 2 * ∑ j, z i j * h j ^ 2
      ≤ 8 * ∑ i, (1 + ε₁) * (1 + ε₂) ^ 2 *
          (weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2 * ∑ j, z i j * h j ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => key i)
          (by norm_num)
    _ = (1 + ε₁) * (1 + ε₂) ^ 2 *
        (8 * ∑ i, weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2 * ∑ j, z i j * h j ^ 2) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring

/-- Lower `D` stability: `Dₓ ≥ (1−ε₁)(1−ε₂)²·D₀` under the
corresponding lower bounds on weights and loads. -/
theorem quadD_rel_ge {m s : ℕ} {z : Fin m → Fin s → ℝ}
    {u u' : Fin m → ℝ} {v v' : Fin s → ℝ} {h : Fin s → ℝ}
    {ε₁ ε₂ : ℝ}
    (hz : ∀ i j, 0 ≤ z i j) (hv : ∀ j, 0 ≤ v j)
    (_hu : ∀ i, u i ≤ 0) (hu' : ∀ i, u' i ≤ 0)
    (_hε₁ : ε₁ ≤ 1) (hε₂ : ε₂ ≤ 1)
    (hν : ∀ i, (1 - ε₁) * weightDeriv (u i) ≤ weightDeriv (u' i))
    (ht : ∀ i, |z i ⬝ᵥ v' - z i ⬝ᵥ v| ≤ ε₂ * (z i ⬝ᵥ v)) :
    (1 - ε₁) * (1 - ε₂) ^ 2 * quadD z u v h ≤ quadD z u' v' h := by
  unfold quadD barrierQuad
  have key : ∀ i, (1 - ε₁) * (1 - ε₂) ^ 2 *
      (weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2 * ∑ j, z i j * h j ^ 2)
      ≤ weightDeriv (u' i) * (z i ⬝ᵥ v') ^ 2 * ∑ j, z i j * h j ^ 2 := by
    intro i
    have ht0 : 0 ≤ z i ⬝ᵥ v := z_dot_nonneg (hz i) hv
    have ht'0 : (1 - ε₂) * (z i ⬝ᵥ v) ≤ z i ⬝ᵥ v' := by
      have h1 := (abs_le.mp (ht i)).1
      nlinarith
    have ht'nn : 0 ≤ z i ⬝ᵥ v' := le_trans
      (mul_nonneg (by linarith) ht0) ht'0
    have hsq : (1 - ε₂) ^ 2 * (z i ⬝ᵥ v) ^ 2 ≤ (z i ⬝ᵥ v') ^ 2 := by
      rw [← mul_pow, sq_le_sq,
        abs_of_nonneg (mul_nonneg (by linarith) ht0),
        abs_of_nonneg ht'nn]
      exact ht'0
    have hbq : 0 ≤ ∑ j, z i j * h j ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hz i j) (sq_nonneg _)
    have hb' : 0 ≤ weightDeriv (u' i) := (weightDeriv_pos (hu' i)).le
    calc (1 - ε₁) * (1 - ε₂) ^ 2 *
          (weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2 * ∑ j, z i j * h j ^ 2)
        = (1 - ε₁) * weightDeriv (u i) *
            ((1 - ε₂) ^ 2 * (z i ⬝ᵥ v) ^ 2) * ∑ j, z i j * h j ^ 2 := by
            ring
      _ ≤ weightDeriv (u' i) * (z i ⬝ᵥ v') ^ 2 * ∑ j, z i j * h j ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hbq
          exact mul_le_mul (hν i) hsq
            (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hb'
  calc (1 - ε₁) * (1 - ε₂) ^ 2 *
        (8 * ∑ i, weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2 * ∑ j, z i j * h j ^ 2)
      = 8 * ∑ i, (1 - ε₁) * (1 - ε₂) ^ 2 *
          (weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2 * ∑ j, z i j * h j ^ 2) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ ≤ 8 * ∑ i, weightDeriv (u' i) * (z i ⬝ᵥ v') ^ 2 * ∑ j, z i j * h j ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => key i)
          (by norm_num)

/-! ## `U`-term transport (B.7)

`Uₓ[h] = ∑ᵢ ν″(uᵢ(x))·tᵢ(x)²·(gᵢ(x)ᵀh)²`.  Splitting
`gᵢ(x)ᵀh = gᵢᵀh + (gᵢ(x)−gᵢ)ᵀh` via
`(a+b)² ≤ (1+δ)a² + (1+δ⁻¹)b²` and applying (B.6) gives an
additive bound `Uₓ ≤ cU₀ + ε·D₀` without any square roots. -/

/-- Young-type split `(a+b)² ≤ (1+δ)a² + (1+δ⁻¹)b²` for `δ > 0`. -/
theorem sq_add_le {a b δ : ℝ} (hδ : 0 < δ) :
    (a + b) ^ 2 ≤ (1 + δ) * a ^ 2 + (1 + δ⁻¹) * b ^ 2 := by
  have h2 : 2 * a * b ≤ δ * a ^ 2 + δ⁻¹ * b ^ 2 := by
    have hsq : 0 ≤ (δ * a - b) ^ 2 := sq_nonneg _
    have hδne : δ ≠ 0 := hδ.ne'
    nlinarith [hsq, mul_inv_cancel₀ hδne]
  nlinarith

/-- `U` transport: if per-row the `ν″·t²` weights move by factor `≤ c`
and are bounded by `c'·ν′·t²`, and the gradients satisfy the (B.6)
bound `((g'ᵢ−gᵢ)ᵀh)² ≤ 64a²·bqᵢ(h)`, then
`Uₓ ≤ (1+δ)c·U₀ + 8a²c'(1+δ⁻¹)·D₀`. -/
theorem quadU_transport {m s : ℕ} {z g g' : Fin m → Fin s → ℝ}
    {u u' : Fin m → ℝ} {v v' h : Fin s → ℝ}
    {a δ c c' : ℝ}
    (hz : ∀ i j, 0 ≤ z i j)
    (hu : ∀ i, u i ≤ 0) (_hu' : ∀ i, u' i ≤ 0)
    (hδ : 0 < δ) (_ha : 0 ≤ a) (_hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hν : ∀ i, weightDeriv2 (u' i) * (z i ⬝ᵥ v') ^ 2 ≤
      c * (weightDeriv2 (u i) * (z i ⬝ᵥ v) ^ 2))
    (hν' : ∀ i, weightDeriv2 (u' i) * (z i ⬝ᵥ v') ^ 2 ≤
      c' * (weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2))
    (hg : ∀ i, ((g' i - g i) ⬝ᵥ h) ^ 2 ≤
      64 * a ^ 2 * barrierQuad (z i) h) :
    quadU z g' u' v' h ≤
      (1 + δ) * c * quadU z g u v h +
        8 * a ^ 2 * c' * (1 + δ⁻¹) * quadD z u v h := by
  have key : ∀ i,
      weightDeriv2 (u' i) * (z i ⬝ᵥ v') ^ 2 * (g' i ⬝ᵥ h) ^ 2 ≤
        (1 + δ) * c *
          (weightDeriv2 (u i) * (z i ⬝ᵥ v) ^ 2 * (g i ⬝ᵥ h) ^ 2) +
        8 * a ^ 2 * c' * (1 + δ⁻¹) *
          (8 * (weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2 * barrierQuad (z i) h)) := by
    intro i
    have hw : 0 ≤ weightDeriv2 (u' i) * (z i ⬝ᵥ v') ^ 2 :=
      mul_nonneg (weightDeriv2_pos (_hu' i)).le (sq_nonneg _)
    have hgsplit : (g' i ⬝ᵥ h) ^ 2 ≤
        (1 + δ) * (g i ⬝ᵥ h) ^ 2 + (1 + δ⁻¹) * ((g' i - g i) ⬝ᵥ h) ^ 2 := by
      have e : g' i ⬝ᵥ h = g i ⬝ᵥ h + (g' i - g i) ⬝ᵥ h := by
        rw [sub_dotProduct]
        ring
      rw [e]
      exact sq_add_le hδ
    have hbq : 0 ≤ barrierQuad (z i) h :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hz i j) (sq_nonneg _)
    have hνi := hν i
    have hν'i := hν' i
    calc weightDeriv2 (u' i) * (z i ⬝ᵥ v') ^ 2 * (g' i ⬝ᵥ h) ^ 2
        ≤ weightDeriv2 (u' i) * (z i ⬝ᵥ v') ^ 2 *
            ((1 + δ) * (g i ⬝ᵥ h) ^ 2 + (1 + δ⁻¹) * ((g' i - g i) ⬝ᵥ h) ^ 2) :=
          mul_le_mul_of_nonneg_left hgsplit hw
      _ = weightDeriv2 (u' i) * (z i ⬝ᵥ v') ^ 2 * ((1 + δ) * (g i ⬝ᵥ h) ^ 2) +
            weightDeriv2 (u' i) * (z i ⬝ᵥ v') ^ 2 *
              ((1 + δ⁻¹) * ((g' i - g i) ⬝ᵥ h) ^ 2) := by ring
      _ ≤ c * (weightDeriv2 (u i) * (z i ⬝ᵥ v) ^ 2) *
            ((1 + δ) * (g i ⬝ᵥ h) ^ 2) +
            c' * (weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2) *
              ((1 + δ⁻¹) * (64 * a ^ 2 * barrierQuad (z i) h)) := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_right hνi
            exact mul_nonneg (by linarith) (sq_nonneg _)
          · exact mul_le_mul hν'i
              (mul_le_mul_of_nonneg_left (hg i)
                (by have : (0:ℝ) ≤ δ⁻¹ := inv_nonneg.mpr hδ.le; linarith))
              (mul_nonneg
                (by have : (0:ℝ) ≤ δ⁻¹ := inv_nonneg.mpr hδ.le; linarith)
                (sq_nonneg _))
              (mul_nonneg hc'
                (mul_nonneg (weightDeriv_pos (hu i)).le (sq_nonneg _)))
      _ = (1 + δ) * c *
            (weightDeriv2 (u i) * (z i ⬝ᵥ v) ^ 2 * (g i ⬝ᵥ h) ^ 2) +
          8 * a ^ 2 * c' * (1 + δ⁻¹) *
            (8 * (weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2 * barrierQuad (z i) h)) := by
          ring
  unfold quadU quadD barrierQuad
  calc ∑ i, weightDeriv2 (u' i) * (z i ⬝ᵥ v') ^ 2 * (g' i ⬝ᵥ h) ^ 2
      ≤ ∑ i, ((1 + δ) * c *
            (weightDeriv2 (u i) * (z i ⬝ᵥ v) ^ 2 * (g i ⬝ᵥ h) ^ 2) +
          8 * a ^ 2 * c' * (1 + δ⁻¹) *
            (8 * (weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2 *
              (∑ j, z i j * h j ^ 2)))) :=
        Finset.sum_le_sum fun i _ => key i
    _ = (1 + δ) * c * quadU z g u v h +
          8 * a ^ 2 * c' * (1 + δ⁻¹) * quadD z u v h := by
        unfold quadU quadD barrierQuad
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
        · simp only [Finset.mul_sum]

/-! ## Resolvent quadratic-form bounds

The `C`-transport bounds `xᵀRx` through the Loewner sandwich
`λI ⪯ R ⪯ μI`, avoiding any square roots: the Young split
`(x+y)ᵀR(x+y) ≤ (1+δ)xᵀRx + (1+δ⁻¹)yᵀRy` follows from
`0 ≤ (δx−y)ᵀR(δx−y)`. -/

/-- `R ⪯ μI` gives `xᵀRx ≤ μ·xᵀx`. -/
theorem dotProduct_mulVec_le_of_sub_posSemidef {s : ℕ}
    {R : Matrix (Fin s) (Fin s) ℝ} {μ : ℝ} (x : Fin s → ℝ)
    (h : (μ • (1 : Matrix (Fin s) (Fin s) ℝ) - R).PosSemidef) :
    x ⬝ᵥ (R *ᵥ x) ≤ μ * (x ⬝ᵥ x) := by
  have h0 := h.dotProduct_mulVec_nonneg x
  simp only [star_trivial] at h0
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at h0
  linarith

/-- `λI ⪯ R` gives `λ·xᵀx ≤ xᵀRx`. -/
theorem le_dotProduct_mulVec_of_sub_posSemidef {s : ℕ}
    {R : Matrix (Fin s) (Fin s) ℝ} {lam : ℝ} (x : Fin s → ℝ)
    (h : (R - lam • (1 : Matrix (Fin s) (Fin s) ℝ)).PosSemidef) :
    lam * (x ⬝ᵥ x) ≤ x ⬝ᵥ (R *ᵥ x) := by
  have h0 := h.dotProduct_mulVec_nonneg x
  simp only [star_trivial] at h0
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at h0
  linarith

/-- `xᵀRy = yᵀRx` for a symmetric real matrix. -/
theorem dotProduct_mulVec_comm_of_isSymm {s : ℕ}
    {R : Matrix (Fin s) (Fin s) ℝ} (hR : R.IsSymm) (x y : Fin s → ℝ) :
    x ⬝ᵥ (R *ᵥ y) = y ⬝ᵥ (R *ᵥ x) := by
  rw [dot_mulVec_eq_sum_sum, dot_mulVec_eq_sum_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hR.apply i j]
  ring

/-- The Young split for a PSD quadratic form:
`(x+y)ᵀR(x+y) ≤ (1+δ)xᵀRx + (1+δ⁻¹)yᵀRy`. -/
theorem dotProduct_mulVec_add_le {s : ℕ}
    {R : Matrix (Fin s) (Fin s) ℝ} (hR : R.PosSemidef)
    {δ : ℝ} (hδ : 0 < δ) (x y : Fin s → ℝ) :
    (x + y) ⬝ᵥ (R *ᵥ (x + y)) ≤
      (1 + δ) * (x ⬝ᵥ (R *ᵥ x)) + (1 + δ⁻¹) * (y ⬝ᵥ (R *ᵥ y)) := by
  have hRt : R.IsSymm := hR.1.isSymm
  -- `q(δx − y) = δ²qx − 2δ·b + qy ≥ 0` gives `δqx + δ⁻¹qy ≥ 2b`.
  have hw := hR.dotProduct_mulVec_nonneg (δ • x - y)
  simp only [star_trivial] at hw
  have hexp : (δ • x - y) ⬝ᵥ (R *ᵥ (δ • x - y)) =
      δ ^ 2 * (x ⬝ᵥ (R *ᵥ x)) - 2 * δ * (x ⬝ᵥ (R *ᵥ y)) +
        (y ⬝ᵥ (R *ᵥ y)) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
      sub_dotProduct, sub_dotProduct, smul_dotProduct, smul_dotProduct,
      dotProduct_smul, dotProduct_smul,
      dotProduct_mulVec_comm_of_isSymm hRt y x]
    ring
  rw [hexp] at hw
  -- Expand the goal's LHS.
  have hlhs : (x + y) ⬝ᵥ (R *ᵥ (x + y)) =
      x ⬝ᵥ (R *ᵥ x) + 2 * (x ⬝ᵥ (R *ᵥ y)) + y ⬝ᵥ (R *ᵥ y) := by
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
      dotProduct_mulVec_comm_of_isSymm hRt y x]
    ring
  rw [hlhs]
  have hmain : 2 * (x ⬝ᵥ (R *ᵥ y)) ≤
      δ * (x ⬝ᵥ (R *ᵥ x)) + δ⁻¹ * (y ⬝ᵥ (R *ᵥ y)) := by
    have h1 : 0 ≤ δ⁻¹ * (δ ^ 2 * (x ⬝ᵥ (R *ᵥ x)) -
        2 * δ * (x ⬝ᵥ (R *ᵥ y)) + (y ⬝ᵥ (R *ᵥ y))) :=
      mul_nonneg (inv_nonneg.mpr hδ.le) hw
    have h2 : δ⁻¹ * (δ ^ 2 * (x ⬝ᵥ (R *ᵥ x)) -
        2 * δ * (x ⬝ᵥ (R *ᵥ y)) + (y ⬝ᵥ (R *ᵥ y))) =
        δ * (x ⬝ᵥ (R *ᵥ x)) - 2 * (x ⬝ᵥ (R *ᵥ y)) +
        δ⁻¹ * (y ⬝ᵥ (R *ᵥ y)) := by
      field_simp
    rw [h2] at h1
    linarith
  linarith

/-- Euclidean norm squared as `xᵀx`. -/
theorem dotProduct_self_sq {s : ℕ} (x : Fin s → ℝ) :
    x ⬝ᵥ x = ∑ j, x j ^ 2 := by
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Weighted Cauchy–Schwarz per coordinate:
`(∑ᵢcᵢzᵢ)² ≤ (∑ᵢzᵢ)·(∑ᵢcᵢ²zᵢ)`. -/
theorem sq_sum_le_spread {m : ℕ} {z : Fin m → ℝ} (hz : ∀ i, 0 ≤ z i)
    (c : Fin m → ℝ) :
    (∑ i, c i * z i) ^ 2 ≤ (∑ i, z i) * ∑ i, c i ^ 2 * z i := by
  have e : (∑ i, c i * z i) =
      ∑ i, (c i * Real.sqrt (z i)) * Real.sqrt (z i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc, Real.mul_self_sqrt (hz i)]
  rw [e]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
    (fun i => c i * Real.sqrt (z i)) (fun i => Real.sqrt (z i))
  refine hcs.trans (le_of_eq ?_)
  rw [mul_comm (∑ i, z i) (∑ i, c i ^ 2 * z i)]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by
      rw [mul_pow, Real.sq_sqrt (hz i)]
  · exact Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hz i)

/-- The vector-level spread bound
`∑ⱼ(∑ᵢcᵢzᵢⱼ)² ≤ Λ·∑ᵢcᵢ²` under column spread `Λ` and row spread `1`. -/
theorem sum_sq_vec_le_spread {m s : ℕ} {z : Fin m → Fin s → ℝ}
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hz : ∀ i j, 0 ≤ z i j)
    (hcol : ∀ j, ∑ i, z i j ≤ Λ)
    (hrow : ∀ i, ∑ j, z i j ≤ 1)
    (c : Fin m → ℝ) :
    ∑ j, (∑ i, c i * z i j) ^ 2 ≤ Λ * ∑ i, c i ^ 2 := by
  calc ∑ j, (∑ i, c i * z i j) ^ 2
      ≤ ∑ j, Λ * ∑ i, c i ^ 2 * z i j := by
        apply Finset.sum_le_sum
        intro j _
        exact (sq_sum_le_spread (fun i => hz i j) c).trans
          (mul_le_mul_of_nonneg_right (hcol j)
            (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hz i j)))
    _ = Λ * ∑ i, c i ^ 2 * (∑ j, z i j) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.mul_sum]
    _ ≤ Λ * ∑ i, c i ^ 2 * 1 := by
        apply mul_le_mul_of_nonneg_left _ hΛ
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _)
    _ = Λ * ∑ i, c i ^ 2 := by simp

/-- The vector Young split `‖x+y‖² ≤ (1+δ)‖x‖² + (1+δ⁻¹)‖y‖²`. -/
theorem dotProduct_self_add_le {s : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (x y : Fin s → ℝ) :
    (x + y) ⬝ᵥ (x + y) ≤
      (1 + δ) * (x ⬝ᵥ x) + (1 + δ⁻¹) * (y ⬝ᵥ y) := by
  rw [dotProduct_self_sq (x + y), dotProduct_self_sq x, dotProduct_self_sq y]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  rw [Pi.add_apply]
  exact sq_add_le hδ

/-! ## `C`-term transport and the (B.10) bound

`(Cₓh − C₀h)ⱼ = ∑ᵢ (ν′(u′ᵢ)t′ᵢ − ν′(uᵢ)tᵢ)(gᵢᵀh)zᵢⱼ
              + ∑ᵢ ν′(u′ᵢ)t′ᵢ·((g′ᵢ−gᵢ)ᵀh)zᵢⱼ`.

Bounding `‖·‖²` by the spread lemma, then
`2Qₓ = 2(Cₓh)ᵀRₓ(Cₓh) ≤ 2μₓ‖Cₓh‖² ≤
  2μₓ(1+δ)lam₀⁻¹Q₀ + 2μₓ(1+δ⁻¹)‖(Cₓ−C₀)h‖²`
gives `Pₓ ≤ γP₀ + εD₀` without square roots. -/

/-- The `C`-vector difference decomposition. -/
theorem quadCvec_sub_eq {m s : ℕ} (z g g' : Fin m → Fin s → ℝ)
    (u u' : Fin m → ℝ) (v v' h : Fin s → ℝ) :
    quadCvec z g' u' v' h - quadCvec z g u v h =
      (fun j => ∑ i, (weightDeriv (u' i) * (z i ⬝ᵥ v') -
          weightDeriv (u i) * (z i ⬝ᵥ v)) * (g i ⬝ᵥ h) * z i j) +
      (fun j => ∑ i, weightDeriv (u' i) * (z i ⬝ᵥ v') *
        ((g' i - g i) ⬝ᵥ h) * z i j) := by
  funext j
  simp only [Pi.sub_apply, Pi.add_apply, quadCvec]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [sub_dotProduct]
  ring

/-- `‖(Cₓ−C₀)h‖²` bound: `(1+δ')Λce²·U₀ + (1+δ'⁻¹)·8Λcd·a²·D₀`. -/
theorem sqNorm_quadCvec_sub_le {m s : ℕ} {z g g' : Fin m → Fin s → ℝ}
    {u u' : Fin m → ℝ} {v v' h : Fin s → ℝ}
    {Λ δ' ce cd a : ℝ}
    (hΛ : 0 ≤ Λ) (hδ' : 0 < δ') (_ha : 0 ≤ a)
    (hz : ∀ i j, 0 ≤ z i j)
    (hcol : ∀ j, ∑ i, z i j ≤ Λ)
    (hrow : ∀ i, ∑ j, z i j ≤ 1)
    (he : ∀ i, (weightDeriv (u' i) * (z i ⬝ᵥ v') -
        weightDeriv (u i) * (z i ⬝ᵥ v)) ^ 2 ≤
      ce ^ 2 * (weightDeriv2 (u i) * (z i ⬝ᵥ v) ^ 2))
    (hcd : ∀ i, (weightDeriv (u' i) * (z i ⬝ᵥ v')) ^ 2 ≤
      cd * (weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2))
    (hg : ∀ i, ((g' i - g i) ⬝ᵥ h) ^ 2 ≤
      64 * a ^ 2 * barrierQuad (z i) h) :
    (quadCvec z g' u' v' h - quadCvec z g u v h) ⬝ᵥ
        (quadCvec z g' u' v' h - quadCvec z g u v h) ≤
      (1 + δ') * Λ * ce ^ 2 * quadU z g u v h +
        (1 + δ'⁻¹) * Λ * cd * (8 * a ^ 2) * quadD z u v h := by
  rw [quadCvec_sub_eq]
  refine (dotProduct_self_add_le hδ' _ _).trans ?_
  rw [dotProduct_self_sq, dotProduct_self_sq]
  -- `V` part: `∑ⱼ(∑ᵢeᵢ·(gᵢᵀh)·zᵢⱼ)² ≤ Λ·ce²·U₀`
  have hV : ∑ j, (∑ i, (weightDeriv (u' i) * (z i ⬝ᵥ v') -
        weightDeriv (u i) * (z i ⬝ᵥ v)) * (g i ⬝ᵥ h) * z i j) ^ 2 ≤
      Λ * ce ^ 2 * quadU z g u v h := by
    calc ∑ j, (∑ i, (weightDeriv (u' i) * (z i ⬝ᵥ v') -
          weightDeriv (u i) * (z i ⬝ᵥ v)) * (g i ⬝ᵥ h) * z i j) ^ 2
        ≤ Λ * ∑ i, ((weightDeriv (u' i) * (z i ⬝ᵥ v') -
            weightDeriv (u i) * (z i ⬝ᵥ v)) * (g i ⬝ᵥ h)) ^ 2 :=
          sum_sq_vec_le_spread hΛ hz hcol hrow _
      _ ≤ Λ * ∑ i, ce ^ 2 *
          (weightDeriv2 (u i) * (z i ⬝ᵥ v) ^ 2 * (g i ⬝ᵥ h) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hΛ
          apply Finset.sum_le_sum
          intro i _
          rw [mul_pow]
          exact (mul_le_mul_of_nonneg_right (he i) (sq_nonneg _)).trans
            (le_of_eq (by ring))
      _ = Λ * ce ^ 2 * quadU z g u v h := by
          unfold quadU
          rw [← Finset.mul_sum, mul_assoc]
  -- `W` part: `∑ⱼ(∑ᵢ(ν'ₓᵢt'ᵢ·gdᵢ)zᵢⱼ)² ≤ Λ·cd·8a²·D₀`
  have hW : ∑ j, (∑ i, weightDeriv (u' i) * (z i ⬝ᵥ v') *
        ((g' i - g i) ⬝ᵥ h) * z i j) ^ 2 ≤
      Λ * cd * (8 * a ^ 2) * quadD z u v h := by
    calc ∑ j, (∑ i, weightDeriv (u' i) * (z i ⬝ᵥ v') *
          ((g' i - g i) ⬝ᵥ h) * z i j) ^ 2
        ≤ Λ * ∑ i, (weightDeriv (u' i) * (z i ⬝ᵥ v') *
            ((g' i - g i) ⬝ᵥ h)) ^ 2 :=
          sum_sq_vec_le_spread hΛ hz hcol hrow _
      _ ≤ Λ * ∑ i, cd * 64 * a ^ 2 *
          (weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2 * barrierQuad (z i) h) := by
          apply mul_le_mul_of_nonneg_left _ hΛ
          apply Finset.sum_le_sum
          intro i _
          rw [mul_pow]
          have hbi := mul_le_mul (hcd i) (hg i) (sq_nonneg _)
            (le_trans (sq_nonneg _) (hcd i))
          exact hbi.trans (le_of_eq (by ring))
      _ = Λ * cd * (8 * a ^ 2) * quadD z u v h := by
          unfold quadD barrierQuad
          rw [mul_assoc (Λ * cd) (8 * a ^ 2)]
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
  exact add_le_add
    ((mul_le_mul_of_nonneg_left hV (by linarith)).trans (le_of_eq (by ring)))
    ((mul_le_mul_of_nonneg_left hW (by
      have : (0:ℝ) ≤ δ'⁻¹ := inv_nonneg.mpr hδ'.le
      linarith)).trans (le_of_eq (by ring)))

/-- The full `P`-transport (B.10): under `Rₓ ⪯ μₓI`, `lam₀I ⪯ R₀`,
per-row coefficient stability, the `U`-transport `hU`, and the (B.6)
gradient bound, `Pₓ ≤ γ·P₀ + ε·D₀` with explicit `γ, ε`. -/
theorem quadP_transport {m s : ℕ} {z g g' : Fin m → Fin s → ℝ}
    {u u' : Fin m → ℝ} {v v' h : Fin s → ℝ}
    {R₀ Rₓ : Matrix (Fin s) (Fin s) ℝ}
    {Λ δ δ' μₓ lam₀ a cd ce cU cD : ℝ}
    (hΛ : 0 ≤ Λ) (hδ : 0 < δ) (hδ' : 0 < δ') (ha : 0 ≤ a)
    (hμ : 0 < μₓ) (hlam : 0 < lam₀)
    (hz : ∀ i j, 0 ≤ z i j)
    (hcol : ∀ j, ∑ i, z i j ≤ Λ)
    (hrow : ∀ i, ∑ j, z i j ≤ 1)
    (hRₓ : (μₓ • (1 : Matrix (Fin s) (Fin s) ℝ) - Rₓ).PosSemidef)
    (hR₀ : (R₀ - lam₀ • (1 : Matrix (Fin s) (Fin s) ℝ)).PosSemidef)
    (he : ∀ i, (weightDeriv (u' i) * (z i ⬝ᵥ v') -
        weightDeriv (u i) * (z i ⬝ᵥ v)) ^ 2 ≤
      ce ^ 2 * (weightDeriv2 (u i) * (z i ⬝ᵥ v) ^ 2))
    (hcd : ∀ i, (weightDeriv (u' i) * (z i ⬝ᵥ v')) ^ 2 ≤
      cd * (weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2))
    (hg : ∀ i, ((g' i - g i) ⬝ᵥ h) ^ 2 ≤
      64 * a ^ 2 * barrierQuad (z i) h)
    (hU : quadU z g' u' v' h ≤
      cU * quadU z g u v h + cD * quadD z u v h) :
    quadP z g' u' v' h Rₓ ≤
      (cU + 2 * μₓ * (1 + δ⁻¹) * (1 + δ') * Λ * ce ^ 2) *
          quadU z g u v h +
        μₓ * lam₀⁻¹ * (1 + δ) * (2 * ((quadCvec z g u v h) ⬝ᵥ
          (R₀ *ᵥ (quadCvec z g u v h)))) +
        (cD + 2 * μₓ * (1 + δ⁻¹) * (1 + δ'⁻¹) * Λ * cd * (8 * a ^ 2)) *
          quadD z u v h := by
  have hCx := dotProduct_mulVec_le_of_sub_posSemidef
    (quadCvec z g' u' v' h) hRₓ
  have hnorm : (quadCvec z g' u' v' h) ⬝ᵥ (quadCvec z g' u' v' h) ≤
      (1 + δ) * ((quadCvec z g u v h) ⬝ᵥ (quadCvec z g u v h)) +
        (1 + δ⁻¹) * ((quadCvec z g' u' v' h - quadCvec z g u v h) ⬝ᵥ
          (quadCvec z g' u' v' h - quadCvec z g u v h)) := by
    have e : quadCvec z g' u' v' h =
        quadCvec z g u v h + (quadCvec z g' u' v' h - quadCvec z g u v h) := by
      funext j
      simp
    conv_lhs => rw [e]
    exact dotProduct_self_add_le hδ _ _
  have hC0 := le_dotProduct_mulVec_of_sub_posSemidef
    (quadCvec z g u v h) hR₀
  have hC0' : (quadCvec z g u v h) ⬝ᵥ (quadCvec z g u v h) ≤
      lam₀⁻¹ * ((quadCvec z g u v h) ⬝ᵥ
        (R₀ *ᵥ (quadCvec z g u v h))) :=
    (le_inv_mul_iff₀ hlam).mpr hC0
  have hsub := sqNorm_quadCvec_sub_le hΛ hδ' ha hz hcol hrow he hcd hg
  unfold quadP
  calc quadU z g' u' v' h + 2 * (quadCvec z g' u' v' h ⬝ᵥ
        (Rₓ *ᵥ quadCvec z g' u' v' h))
      ≤ cU * quadU z g u v h + cD * quadD z u v h +
          2 * (μₓ * ((quadCvec z g' u' v' h) ⬝ᵥ
            (quadCvec z g' u' v' h))) :=
        add_le_add hU (mul_le_mul_of_nonneg_left hCx (by norm_num))
    _ ≤ cU * quadU z g u v h + cD * quadD z u v h +
          2 * μₓ * ((1 + δ) * ((quadCvec z g u v h) ⬝ᵥ
              (quadCvec z g u v h)) +
            (1 + δ⁻¹) * ((quadCvec z g' u' v' h - quadCvec z g u v h) ⬝ᵥ
              (quadCvec z g' u' v' h - quadCvec z g u v h))) := by
        exact add_le_add_left
          (mul_le_mul_of_nonneg_left hnorm
            (mul_nonneg (by norm_num) hμ.le)) _
    _ ≤ cU * quadU z g u v h + cD * quadD z u v h +
          2 * μₓ * ((1 + δ) * (lam₀⁻¹ * ((quadCvec z g u v h) ⬝ᵥ
              (R₀ *ᵥ (quadCvec z g u v h)))) +
            (1 + δ⁻¹) * ((1 + δ') * Λ * ce ^ 2 * quadU z g u v h +
              (1 + δ'⁻¹) * Λ * cd * (8 * a ^ 2) * quadD z u v h)) := by
        apply add_le_add_left
        exact mul_le_mul_of_nonneg_left
          (add_le_add
            (mul_le_mul_of_nonneg_left hC0' (by linarith))
            (mul_le_mul_of_nonneg_left hsub
              (by have : (0:ℝ) ≤ δ⁻¹ := inv_nonneg.mpr hδ.le; linarith)))
          (mul_nonneg (by norm_num) hμ.le)
    _ = (cU + 2 * μₓ * (1 + δ⁻¹) * (1 + δ') * Λ * ce ^ 2) *
            quadU z g u v h +
          μₓ * lam₀⁻¹ * (1 + δ) * (2 * ((quadCvec z g u v h) ⬝ᵥ
            (R₀ *ᵥ (quadCvec z g u v h)))) +
          (cD + 2 * μₓ * (1 + δ⁻¹) * (1 + δ'⁻¹) * Λ * cd * (8 * a ^ 2)) *
            quadD z u v h := by ring

/-! ## Composed transport to the `1 − ρ/2` margin -/

/-- `U[h] ≥ 0` on nonpositive barriers. -/
theorem quadU_nonneg {m s : ℕ} (z g : Fin m → Fin s → ℝ)
    (u : Fin m → ℝ) (v h : Fin s → ℝ) (hu : ∀ i, u i ≤ 0) :
    0 ≤ quadU z g u v h := by
  unfold quadU
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (weightDeriv2_pos (hu i)).le (sq_nonneg _))
      (sq_nonneg _)

/-- `c • 1` is positive semidefinite for `c ≥ 0`. -/
theorem posSemidef_smul_one {s : ℕ} {c : ℝ} (hc : 0 ≤ c) :
    (c • (1 : Matrix (Fin s) (Fin s) ℝ)).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨Matrix.isHermitian_iff_isSymm.mpr (Matrix.isSymm_one.smul c),
    fun x => ?_⟩
  rw [star_trivial, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul]
  apply mul_nonneg hc
  rw [dotProduct_self_sq]
  exact Finset.sum_nonneg fun j _ => sq_nonneg _

/-- `R − lam • 1 ⪰ 0` with `lam ≥ 0` implies `R ⪰ 0`. -/
theorem posSemidef_of_sub_posSemidef_smul_one {s : ℕ}
    {R : Matrix (Fin s) (Fin s) ℝ} {lam : ℝ}
    (h : (R - lam • (1 : Matrix (Fin s) (Fin s) ℝ)).PosSemidef)
    (hlam : 0 ≤ lam) : R.PosSemidef := by
  have := h.add (posSemidef_smul_one hlam)
  simpa using this

/-- `xᵀRx ≥ 0` for a PSD real matrix (no `star`). -/
theorem dotProduct_mulVec_nonneg_of_posSemidef {s : ℕ}
    {R : Matrix (Fin s) (Fin s) ℝ} (hR : R.PosSemidef) (x : Fin s → ℝ) :
    0 ≤ x ⬝ᵥ (R *ᵥ x) := by
  have := hR.dotProduct_mulVec_nonneg x
  simpa only [star_trivial] using this

/-- **Subspace transport, γ-form.** On a subspace `E` where
`P₀[h] ≤ (1−ρ)D₀[h]`, a `γ`-transport bound
`Pₓ[h] ≤ γU·U₀[h] + γQ·(2Q₀[h]) + ε·D₀[h]` together with the diagonal
lower bound `Dₓ[h] ≥ (1−δ)D₀[h]` yields `Pₓ[h] ≤ (1−ρ/2)Dₓ[h]`
provided `max(γU,γQ)(1−ρ) + ε ≤ (1−ρ/2)(1−δ)`. -/
theorem quadP_transport_subspace {m s : ℕ}
    {z g g' : Fin m → Fin s → ℝ}
    {u u' : Fin m → ℝ} {v v' : Fin s → ℝ}
    {R₀ Rₓ : Matrix (Fin s) (Fin s) ℝ} {E : Submodule ℝ (Fin s → ℝ)}
    {ρ γU γQ ε δ : ℝ}
    (hρ1 : ρ ≤ 1)
    (hγU : 0 ≤ γU) (hγQ : 0 ≤ γQ)
    (hu : ∀ i, u i ≤ 0) (hz : ∀ i j, 0 ≤ z i j)
    (hR₀ : R₀.PosSemidef)
    (hE : ∀ h ∈ E,
      quadP z g u v h R₀ ≤ (1 - ρ) * quadD z u v h)
    (hPt : ∀ h ∈ E, quadP z g' u' v' h Rₓ ≤
        γU * quadU z g u v h +
        γQ * (2 * (quadCvec z g u v h ⬝ᵥ (R₀ *ᵥ quadCvec z g u v h))) +
        ε * quadD z u v h)
    (hDl : ∀ h ∈ E, (1 - δ) * quadD z u v h ≤ quadD z u' v' h)
    (hc : max γU γQ * (1 - ρ) + ε ≤ (1 - ρ / 2) * (1 - δ)) :
    ∀ h ∈ E, quadP z g' u' v' h Rₓ ≤ (1 - ρ / 2) * quadD z u' v' h := by
  intro h hh
  have hU0 : 0 ≤ quadU z g u v h := quadU_nonneg _ _ _ _ _ hu
  have hQ0 : 0 ≤ quadCvec z g u v h ⬝ᵥ (R₀ *ᵥ quadCvec z g u v h) :=
    dotProduct_mulVec_nonneg_of_posSemidef hR₀ _
  have hD0 : 0 ≤ quadD z u v h := quadD_nonneg hz hu
  have h1 : quadP z g' u' v' h Rₓ ≤
      max γU γQ * (quadU z g u v h +
        2 * (quadCvec z g u v h ⬝ᵥ (R₀ *ᵥ quadCvec z g u v h))) +
        ε * quadD z u v h := by
    refine (hPt h hh).trans ?_
    have hU' : γU * quadU z g u v h ≤ max γU γQ * quadU z g u v h :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hU0
    have hQ' : γQ * (2 * (quadCvec z g u v h ⬝ᵥ
        (R₀ *ᵥ quadCvec z g u v h))) ≤
        max γU γQ * (2 * (quadCvec z g u v h ⬝ᵥ
          (R₀ *ᵥ quadCvec z g u v h))) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _)
        (mul_nonneg (by norm_num) hQ0)
    linarith
  have h2 : max γU γQ * (quadU z g u v h +
        2 * (quadCvec z g u v h ⬝ᵥ (R₀ *ᵥ quadCvec z g u v h))) +
        ε * quadD z u v h ≤
      (1 - ρ / 2) * ((1 - δ) * quadD z u v h) := by
    have hP0le : quadU z g u v h +
        2 * (quadCvec z g u v h ⬝ᵥ (R₀ *ᵥ quadCvec z g u v h)) ≤
        (1 - ρ) * quadD z u v h := hE h hh
    have hγ0 : 0 ≤ max γU γQ := le_max_of_le_left hγU
    have h3 := mul_le_mul_of_nonneg_left hP0le hγ0
    have h4 := mul_le_mul_of_nonneg_right hc hD0
    linarith
  have h5 : (1 - ρ / 2) * ((1 - δ) * quadD z u v h) ≤
      (1 - ρ / 2) * quadD z u' v' h :=
    mul_le_mul_of_nonneg_left (hDl h hh) (by linarith)
  exact h1.trans (h2.trans h5)

/-- **End-to-end subspace transport.** The anchor bound
`P₀ⱼⱼ ≤ θ·(1−ρ)D₀ⱼⱼ` produces the subspace `E` (via
`exists_subspace_quadP_le`), and the γ-form transport plus the
diagonal lower bound close the `1−ρ/2` margin on `E`. -/
theorem transported_subspace_bound_quad {m s : ℕ} {θ ρ γU γQ ε δ : ℝ}
    {z g g' : Fin m → Fin s → ℝ} {u u' : Fin m → ℝ} {v v' : Fin s → ℝ}
    {R₀ Rₓ : Matrix (Fin s) (Fin s) ℝ}
    (hR : R₀.PosSemidef) (hθ : 0 ≤ θ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hδ : δ ≤ 1)
    (hz : ∀ i j, 0 ≤ z i j) (hu : ∀ i, u i ≤ 0)
    (hQD : ∀ j, Pmat z g u v R₀ j j ≤
      θ * ((1 - ρ) • Dmat z u v) j j)
    (hγU : 0 ≤ γU) (hγQ : 0 ≤ γQ)
    (hPt : ∀ h : Fin s → ℝ, quadP z g' u' v' h Rₓ ≤
        γU * quadU z g u v h +
        γQ * (2 * (quadCvec z g u v h ⬝ᵥ (R₀ *ᵥ quadCvec z g u v h))) +
        ε * quadD z u v h)
    (hDl : ∀ h : Fin s → ℝ,
      (1 - δ) * quadD z u v h ≤ quadD z u' v' h)
    (hc : max γU γQ * (1 - ρ) + ε ≤ (1 - ρ / 2) * (1 - δ)) :
    ∃ E : Submodule ℝ (Fin s → ℝ),
      (s : ℝ) - θ * s ≤ Module.finrank ℝ E ∧
      ∀ h ∈ E, quadP z g' u' v' h Rₓ ≤ (1 - ρ / 2) * quadD z u' v' h := by
  obtain ⟨E, hEdim, hE⟩ :=
    exists_subspace_quadP_le hR hθ hρ1 hz hu hQD
  exact ⟨E, hEdim,
    quadP_transport_subspace hρ1 hγU hγQ hu hz hR hE hPt hDl hc⟩

end Komlos
