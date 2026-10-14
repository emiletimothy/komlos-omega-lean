import Komlos.Curvature
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

namespace Komlos
open scoped BigOperators
open Matrix Filter Topology
noncomputable section

-- test 1: the numeric margin
example : 1 / (291 / 200 : ℝ) ^ 2 + 5 * (65 / 64) ^ 4 / 238 +
      1 / (64 * (4 / 25 - 3 / 625)) + 1 / 2048 +
      (1 + 4 / 25) * (1 + 1 / 10000) / (4 * (1 - 4 / 25) * (1 - 1 / 64)) <
      31 / 32 := by
  norm_num

-- test 2: spectral_dimension_margin body
example {s : ℝ} (c₁ c₂ c₃ c₄ c₅ : ℝ)
    (h₁ : c₁ ≤ (1 / (291 / 200) ^ 2) * s)
    (h₂ : c₂ ≤ (5 * (65 / 64) ^ 4 / 238) * s)
    (h₃ : c₃ ≤ (1 / (64 * (4 / 25 - 3 / 625))) * s)
    (h₄ : c₄ ≤ (1 / 2048) * s)
    (h₅ : c₅ ≤ ((1 + 4 / 25) * (1 + 1 / 10000) /
        (4 * (1 - 4 / 25) * (1 - 1 / 64))) * s)
    (hs : 0 < s) :
    c₁ + c₂ + c₃ + c₄ + c₅ < (31 / 32) * s := by
  have hTlt : 1 / (291 / 200 : ℝ) ^ 2 + 5 * (65 / 64) ^ 4 / 238 +
      1 / (64 * (4 / 25 - 3 / 625)) + 1 / 2048 +
      (1 + 4 / 25) * (1 + 1 / 10000) / (4 * (1 - 4 / 25) * (1 - 1 / 64)) <
      31 / 32 := by
    norm_num
  linarith [h₁, h₂, h₃, h₄, h₅, mul_lt_mul_of_pos_right hTlt hs]

-- test 3: tendsto_pathW alternative
example {s : ℕ} (N₁ N₂ : Input s s) (v : Fin s → ℝ) :
    Tendsto (fun t : ℝ => (N₁ + t • N₂) *ᵥ v) (𝓝 0) (𝓝 (N₁ *ᵥ v)) := by
  have heq : (fun t : ℝ => (N₁ + t • N₂) *ᵥ v) =
      fun t : ℝ => N₁ *ᵥ v + t • (N₂ *ᵥ v) := by
    funext t
    rw [Matrix.add_mulVec, Matrix.smul_mulVec]
  rw [heq]
  have hC : Continuous (fun t : ℝ => N₁ *ᵥ v + t • (N₂ *ᵥ v)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have h := hC.tendsto 0
  simpa using h

-- test 4: exp bound
example : Real.exp (1 / 2) < 595 / 357 := by
  rw [Real.exp_half]
  rw [Real.sqrt_lt (Real.exp_nonneg 1) (by norm_num : (0 : ℝ) ≤ 595 / 357)]
  calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    _ < (595 / 357) ^ 2 := by norm_num

-- test 5: batchPerturbation_apply fix
example {m s : ℕ} (z : Fin m → Fin s → ℝ) (c : Fin m → ℝ)
    (j k : Fin s) :
    batchPerturbation z c j k = ∑ i, c i * z i j * z i k := by
  simp only [batchPerturbation, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    rankOne]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end Komlos
