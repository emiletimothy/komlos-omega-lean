/-
# Bit-cost model and the runtime statement of Theorem 1.1

This module supplies the vocabulary needed to *state* the runtime half of
Theorem 1.1 of "The Komlós Problem in Near Matrix-Multiplication Time"
(Anand–Chen). `DiscrepancyPartOfTheorem11` in `Komlos.lean` records only the
discrepancy conclusion and has no runtime component. The present file adds:

* `natBitSize` and `ratBitSize`: a bit-size measure for naturals and
  rationals, counting `⌊log₂ ·⌋ + 1` digits for the numerator magnitude and
  for the denominator;
* `inputBitSize`: the total bit size of a rational matrix;
* `BitCostModel`: a bundled cost model assigning natural-number bit-costs to
  the elementary rational operations (add, multiply, divide, compare) and to
  `n × n` rational matrix multiplication. The matrix-multiplication exponent
  `ω : ℝ` is an abstract parameter constrained only by `2 ≤ ω`, together with
  a uniform `O(n^ω · B)` bound `matmulCost_le`. Everything is a structure
  field or hypothesis, so every statement is conditional on a model — there
  are no axioms anywhere in this file;
* `verificationBitCost`: an abstract operation count for producing a Boolean
  signing and checking it with the exact rational verifier `verifySigning`;
* `runtimeEnvelope`: the claimed `O((m + n)^ω · B² · (1 + log δ⁻¹)²)` bound;
* `DiscrepancyRuntimeBound` and `Theorem11WithRuntime`: the runtime half of
  Theorem 1.1, packaged as `Prop`s analogous to `DiscrepancyPartOfTheorem11`.

**Status: definitions and statement only.** The fast dynamic inverse
implementation and the expected bit-complexity proof remain open. Nothing in
this file proves that the claimed envelope is achieved.
-/

import Komlos
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

namespace Komlos

open scoped BigOperators

/-! ## Bit sizes of naturals, rationals, and matrices -/

/-- Number of bits used to write `n : ℕ` in binary; `0` and `1` each cost one
bit. Defined as `⌊log₂ n⌋ + 1`. -/
def natBitSize (n : ℕ) : ℕ := Nat.log 2 n + 1

theorem natBitSize_pos (n : ℕ) : 0 < natBitSize n :=
  Nat.succ_pos _

theorem natBitSize_mono : Monotone natBitSize :=
  fun _ _ h => Nat.succ_le_succ (Nat.log_mono_right h)

/-- Bit size of a rational `q = num/den`: the digits of `|num|` plus the
digits of `den`. -/
def ratBitSize (q : ℚ) : ℕ := natBitSize q.num.natAbs + natBitSize q.den

theorem ratBitSize_pos (q : ℚ) : 0 < ratBitSize q := by
  have h₁ := natBitSize_pos q.num.natAbs
  have h₂ := natBitSize_pos q.den
  unfold ratBitSize
  omega

theorem ratBitSize_two_le (q : ℚ) : 2 ≤ ratBitSize q := by
  have h₁ := natBitSize_pos q.num.natAbs
  have h₂ := natBitSize_pos q.den
  unfold ratBitSize
  omega

theorem ratBitSize_zero : ratBitSize 0 = 2 := by decide

theorem ratBitSize_one : ratBitSize 1 = 2 := by decide

theorem ratBitSize_neg_one : ratBitSize (-1) = 2 := by decide

theorem ratBitSize_two : ratBitSize 2 = 3 := by decide

theorem ratBitSize_99 : ratBitSize 99 = 8 := by decide

/-- Total bit size of a rational matrix: the sum of the entry bit sizes. -/
def inputBitSize {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : ℕ :=
  ∑ i, ∑ j, ratBitSize (A i j)

theorem inputBitSize_pos {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (hm : 0 < m) (hn : 0 < n) : 0 < inputBitSize A := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Finset.sum_pos
    (fun _ _ => Finset.sum_pos (fun _ _ => ratBitSize_pos _) Finset.univ_nonempty)
    Finset.univ_nonempty

/-- If every entry of `A` fits in `B` bits, the whole matrix fits in
`m * n * B` bits. -/
theorem inputBitSize_le {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℚ} {B : ℕ}
    (h : ∀ i j, ratBitSize (A i j) ≤ B) : inputBitSize A ≤ m * n * B := by
  calc inputBitSize A ≤ ∑ _i : Fin m, ∑ _j : Fin n, B :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => h _ _
    _ = m * n * B := by simp [Finset.sum_const, mul_assoc]

/-! ## The bundled bit-cost model -/

/-- A bundled bit-cost model for exact rational arithmetic and `n × n`
rational matrix multiplication. All entries are data (natural-number cost
functions or real constants) together with hypotheses, so every theorem
quantifying over `BitCostModel` is conditional on the model — nothing here is
an axiom.

* `ω` is the abstract matrix-multiplication exponent, constrained only by
  `two_le_ω : 2 ≤ ω`.
* `addCost B`, `mulCost B`, `divCost B`, `cmpCost B` bound the bit-cost of
  one elementary rational operation on operands of bit size at most `B`.
* `matmulCost n B` bounds the bit-cost of multiplying two `n × n` rational
  matrices whose entries have bit size at most `B`; `matmulCost_le` asserts
  the uniform `O(n^ω · B)` estimate.
* The scalar-operation bounds are linear in `B` for addition and comparison
  and quadratic in `B` for multiplication and division (schoolbook-style
  shapes, recorded through the constant `scalarConst`). -/
structure BitCostModel where
  /-- Matrix-multiplication exponent. -/
  ω : ℝ
  /-- Leading constant in the `O(n^ω · B)` matrix-multiplication bound. -/
  matmulLeadingConst : ℝ
  /-- Leading constant in the scalar-operation bounds. -/
  scalarConst : ℝ
  /-- Bit-cost of adding two rationals of bit size at most `B`. -/
  addCost : ℕ → ℕ
  /-- Bit-cost of multiplying two rationals of bit size at most `B`. -/
  mulCost : ℕ → ℕ
  /-- Bit-cost of dividing two rationals of bit size at most `B`. -/
  divCost : ℕ → ℕ
  /-- Bit-cost of comparing two rationals of bit size at most `B`. -/
  cmpCost : ℕ → ℕ
  /-- Bit-cost of `n × n` rational matrix multiplication with entries of bit
  size at most `B`. -/
  matmulCost : ℕ → ℕ → ℕ
  /-- The matrix-multiplication exponent is at least `2`. -/
  two_le_ω : 2 ≤ ω
  /-- The leading constants are nonnegative. -/
  matmulLeadingConst_nonneg : 0 ≤ matmulLeadingConst
  /-- The scalar-operation leading constant is nonnegative. -/
  scalarConst_nonneg : 0 ≤ scalarConst
  /-- Addition costs at most `scalarConst * B` bit operations. -/
  addCost_le : ∀ B, (addCost B : ℝ) ≤ scalarConst * (B : ℝ)
  /-- Multiplication costs at most `scalarConst * B²` bit operations. -/
  mulCost_le : ∀ B, (mulCost B : ℝ) ≤ scalarConst * (B : ℝ) ^ 2
  /-- Division costs at most `scalarConst * B²` bit operations. -/
  divCost_le : ∀ B, (divCost B : ℝ) ≤ scalarConst * (B : ℝ) ^ 2
  /-- Comparison costs at most `scalarConst * B` bit operations. -/
  cmpCost_le : ∀ B, (cmpCost B : ℝ) ≤ scalarConst * (B : ℝ)
  /-- The `O(n^ω · B)` matrix-multiplication bit-cost bound. -/
  matmulCost_le : ∀ n B,
    (matmulCost n B : ℝ) ≤ matmulLeadingConst * (n : ℝ) ^ ω * (B : ℝ)

theorem BitCostModel.addCost_nonneg (c : BitCostModel) (B : ℕ) :
    0 ≤ (c.addCost B : ℝ) := Nat.cast_nonneg _

theorem BitCostModel.mulCost_nonneg (c : BitCostModel) (B : ℕ) :
    0 ≤ (c.mulCost B : ℝ) := Nat.cast_nonneg _

theorem BitCostModel.divCost_nonneg (c : BitCostModel) (B : ℕ) :
    0 ≤ (c.divCost B : ℝ) := Nat.cast_nonneg _

theorem BitCostModel.cmpCost_nonneg (c : BitCostModel) (B : ℕ) :
    0 ≤ (c.cmpCost B : ℝ) := Nat.cast_nonneg _

theorem BitCostModel.matmulCost_nonneg (c : BitCostModel) (n B : ℕ) :
    0 ≤ (c.matmulCost n B : ℝ) := Nat.cast_nonneg _

/-- Since `2 ≤ ω`, the abstract `n^ω` bound dominates the quadratic input
size `n²` for `n ≥ 1`. -/
theorem BitCostModel.rpow_two_le_rpow_ω (c : BitCostModel) {n : ℕ}
    (hn : 1 ≤ n) : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ c.ω :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) c.two_le_ω

/-- A concrete admissible cost model with exponent `ω = 2`, unit leading
constants and schoolbook-shaped scalar costs. Its only purpose is to show
that `BitCostModel` is inhabited, so statements conditional on a cost model
are non-vacuous. -/
def BitCostModel.quadratic : BitCostModel where
  ω := 2
  matmulLeadingConst := 1
  scalarConst := 1
  addCost := fun B => B
  mulCost := fun B => B ^ 2
  divCost := fun B => B ^ 2
  cmpCost := fun B => B
  matmulCost := fun n B => n ^ 2 * B
  two_le_ω := le_refl 2
  matmulLeadingConst_nonneg := zero_le_one
  scalarConst_nonneg := zero_le_one
  addCost_le := fun _ => by simp
  mulCost_le := fun _ => by simp
  divCost_le := fun _ => by simp
  cmpCost_le := fun _ => by simp
  matmulCost_le := fun n B => by
    push_cast
    rw [Real.rpow_two, one_mul]

/-- Sequential composition of two bounded costs is bounded by the sum of the
bounds. -/
theorem cost_add_le {t₁ t₂ b₁ b₂ : ℕ} (h₁ : t₁ ≤ b₁) (h₂ : t₂ ≤ b₂) :
    t₁ + t₂ ≤ b₁ + b₂ := Nat.add_le_add h₁ h₂

/-! ## Accounted verification cost and the runtime envelope -/

/-- Accounted bit-cost of producing a signing and verifying it exactly: one
`n × n` matrix multiplication (the dominant inverse-maintenance block), one
scalar multiply–add pair per matrix entry for the `m` row values, and one
comparison per row against the threshold `99`. This is the abstract cost
account that the runtime statement bounds; it is not an executable model of
the algorithm. -/
def verificationBitCost (c : BitCostModel) (m n B : ℕ) : ℕ :=
  c.matmulCost n B + m * n * (c.mulCost B + c.addCost B) + m * c.cmpCost B

theorem verificationBitCost_nonneg (c : BitCostModel) (m n B : ℕ) :
    0 ≤ (verificationBitCost c m n B : ℝ) := Nat.cast_nonneg _

/-- The accounted verification cost satisfies the field-wise bounds of the
cost model: at most `matmulLeadingConst · n^ω · B` for the multiplication
block plus `scalarConst` times the elementary-operation counts. -/
theorem verificationBitCost_le (c : BitCostModel) (m n B : ℕ) :
    (verificationBitCost c m n B : ℝ) ≤
      c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ) +
        (m : ℝ) * (n : ℝ) *
          (c.scalarConst * (B : ℝ) ^ 2 + c.scalarConst * (B : ℝ)) +
        (m : ℝ) * (c.scalarConst * (B : ℝ)) := by
  have h1 : (c.matmulCost n B : ℝ) ≤
      c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ) :=
    c.matmulCost_le n B
  have h2 : (m : ℝ) * (n : ℝ) * ((c.mulCost B : ℝ) + (c.addCost B : ℝ)) ≤
      (m : ℝ) * (n : ℝ) *
        (c.scalarConst * (B : ℝ) ^ 2 + c.scalarConst * (B : ℝ)) :=
    mul_le_mul_of_nonneg_left
      (add_le_add (c.mulCost_le B) (c.addCost_le B))
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have h3 : (m : ℝ) * (c.cmpCost B : ℝ) ≤ (m : ℝ) * (c.scalarConst * (B : ℝ)) :=
    mul_le_mul_of_nonneg_left (c.cmpCost_le B) (Nat.cast_nonneg _)
  unfold verificationBitCost
  push_cast
  exact add_le_add (add_le_add h1 h2) h3

/-- The claimed asymptotic envelope of Theorem 1.1:
`matmulLeadingConst · (m + n)^ω · B² · (1 + log δ⁻¹)²`, i.e. near
matrix-multiplication time up to a polynomial in the input bit size and the
logarithm of the inverse failure probability. Kept real-valued so that `ω`
can be an abstract real exponent. -/
noncomputable def runtimeEnvelope (c : BitCostModel) (m n B : ℕ)
    (logInvδ : ℝ) : ℝ :=
  c.matmulLeadingConst * ((m : ℝ) + (n : ℝ)) ^ c.ω * (B : ℝ) ^ 2 *
    (1 + logInvδ) ^ 2

theorem runtimeEnvelope_nonneg (c : BitCostModel) (m n B : ℕ) (logInvδ : ℝ) :
    0 ≤ runtimeEnvelope c m n B logInvδ :=
  mul_nonneg
    (mul_nonneg
      (mul_nonneg c.matmulLeadingConst_nonneg
        (Real.rpow_nonneg (by positivity) _))
      (sq_nonneg _))
    (sq_nonneg _)

/-- The envelope is monotone in the input bit size `B`. -/
theorem runtimeEnvelope_mono_bits (c : BitCostModel) (m n : ℕ) {B B' : ℕ}
    (logInvδ : ℝ) (h : B ≤ B') :
    runtimeEnvelope c m n B logInvδ ≤ runtimeEnvelope c m n B' logInvδ := by
  unfold runtimeEnvelope
  have hK : 0 ≤ c.matmulLeadingConst * ((m : ℝ) + (n : ℝ)) ^ c.ω :=
    mul_nonneg c.matmulLeadingConst_nonneg
      (Real.rpow_nonneg (by positivity) _)
  have hBB : (B : ℝ) ^ 2 ≤ (B' : ℝ) ^ 2 := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast h
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBB hK)
    (sq_nonneg _)

/-- The envelope is monotone in `log δ⁻¹` on the nonnegative range. -/
theorem runtimeEnvelope_mono_log (c : BitCostModel) (m n B : ℕ) {l l' : ℝ}
    (hl : 0 ≤ l) (h : l ≤ l') :
    runtimeEnvelope c m n B l ≤ runtimeEnvelope c m n B l' := by
  unfold runtimeEnvelope
  have hK : 0 ≤ c.matmulLeadingConst * ((m : ℝ) + (n : ℝ)) ^ c.ω * (B : ℝ) ^ 2 :=
    mul_nonneg
      (mul_nonneg c.matmulLeadingConst_nonneg
        (Real.rpow_nonneg (by positivity) _))
      (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hK
  apply pow_le_pow_left₀ (by linarith)
  linarith

/-- For `δ ∈ (0, 1]`, `log δ⁻¹` is nonnegative, so the log factor of the
envelope is meaningful. -/
theorem log_inv_nonneg {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ Real.log δ⁻¹ :=
  Real.log_nonneg ((one_le_inv₀ hδ).mpr hδ1)

/-! ## The runtime statement of Theorem 1.1 -/

/-- The runtime half of Theorem 1.1, conditional on a bit-cost model `c`.

For every rational matrix `A` whose real embedding is column-normalized and
every failure-probability parameter `δ ∈ (0, 1]`, there exists a Boolean
signing `ε` certified by the exact rational checker `verifySigning` — hence
satisfying `|rowValue| < 99` by `verifySigning_sound` — such that the
accounted verification cost `verificationBitCost c m n (inputBitSize A)`
fits inside `runtimeEnvelope c m n (inputBitSize A) (Real.log δ⁻¹)`.

**This is a statement, not a proof.** It is a `def ... : Prop` in the same
style as `DiscrepancyPartOfTheorem11`; the fast dynamic inverse
implementation and the expected bit-complexity analysis remain open. -/
def DiscrepancyRuntimeBound (c : BitCostModel) : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ) (δ : ℝ),
    ColumnNormalized (fun i j => (A i j : ℝ)) → 0 < δ → δ ≤ 1 →
      ∃ ε : Fin n → Bool,
        verifySigning A ε = true ∧
        (verificationBitCost c m n (inputBitSize A) : ℝ) ≤
          runtimeEnvelope c m n (inputBitSize A) (Real.log δ⁻¹)

/-- Theorem 1.1 with its runtime component: for every admissible bit-cost
model (every `BitCostModel` satisfying its field constraints, in particular
`2 ≤ ω` and the `O(n^ω · B)` matrix-multiplication bound), the discrepancy
half — existence of a certified signing with `|rowValue| < 99` — and the
runtime half — `verificationBitCost` bounded by `runtimeEnvelope` — hold
simultaneously.

**This is a statement, not a proof.** Together with `verifySigning_sound`,
its proof would immediately imply `DiscrepancyPartOfTheorem11`. -/
def Theorem11WithRuntime : Prop :=
  ∀ c : BitCostModel, DiscrepancyRuntimeBound c

end Komlos
