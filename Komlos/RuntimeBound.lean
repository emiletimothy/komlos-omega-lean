/-
# The runtime half of Theorem 1.1, conditional on discrepancy existence

`Komlos/Runtime.lean` defines `BitCostModel`, `verificationBitCost`,
`runtimeEnvelope`, and the statement-level `Prop`s `DiscrepancyRuntimeBound`
and `Theorem11WithRuntime`. This file supplies the *arithmetic* content of
that statement, modulo the discrepancy existence supplied by the random
walk, and records honestly that the unconditional `∀ c` statement is too
strong.

## The admissibility gap: `BitCostModel.WellScaled`

`Theorem11WithRuntime` quantifies over **all** admissible `BitCostModel`s,
but nothing in the structure fields bounds `scalarConst` against
`matmulLeadingConst`. A model with `matmulLeadingConst = 0` forces
`matmulCost = 0` and hence a zero envelope, while the scalar-operation
account stays positive — so `DiscrepancyRuntimeBound` fails. We make this
concrete with `BitCostModel.badlyScaled`
(`not_discrepancyRuntimeBound_badlyScaled`, `not_theorem11WithRuntime`):
the unconditional statement is *refutable*, not merely unproved.

The honest hypothesis is `BitCostModel.WellScaled c`, namely
`c.scalarConst ≤ c.matmulLeadingConst`. No factor `2` is lost: the scalar
account `mn·(B² + B) + m·B` is bounded by `((m + n)² − n²)·B² =
(m² + 2mn)·B²` for `m, n, B ≥ 1` (via `mn·B ≤ mn·B²`, `m·B ≤ m·B² ≤ m²·B²`
and `m ≤ m²`), and the residual `(m + n)^ω − n^ω` dominates
`(m + n)² − n²` because `x ↦ x^ω` grows faster than `x ↦ x²` on `x ≥ 1`
(`rpow_sub_le_rpow_sub`). The matrix-multiplication term
`matmulLeadingConst·n^ω·B` occupies the remaining `n^ω·B²` of the envelope,
and `1 ≤ (1 + log δ⁻¹)²` supplies the final slack.

## What is proved here

* `verificationBitCost_le_envelope`: under `WellScaled`, `m, n, B ≥ 1` and
  `0 ≤ l`, the accounted cost fits
  `matmulLeadingConst·(m + n)^ω·B²·(1 + l)²` exactly (no extra constant —
  the residual bound above is what makes `scalar ≤ matmul` suffice).
* `verifySigning_accepts_of_rowValue_lt`: the exact rational verifier
  accepts a Boolean signing whose *real* row values are all `< 99`, since
  the rational row value casts to the real one (`Rat.cast_abs`).
* `BoolSigningExists`: the discrepancy-existence input expressed over
  Boolean signings, kept as a hypothesis — it is the output of the paper's
  walk assembly, which is a separate formalization effort.
  `discrepancyPart_of_boolSigningExists` shows it implies
  `DiscrepancyPartOfTheorem11`.
* `discrepancyRuntimeBound_of_existence`: `WellScaled c` together with
  `BoolSigningExists` yields `DiscrepancyRuntimeBound c`. Degenerate
  inputs (`m = 0`, `n = 0`, or `inputBitSize A = 0`) are discharged
  separately: bit size `0` forces every field cost to `0` through the model
  bounds, so `verificationBitCost = 0` and the nonnegative envelope covers
  it.
* `discrepancyRuntimeBound_quadratic`: instantiation at
  `BitCostModel.quadratic`, which is well-scaled
  (`scalarConst = matmulLeadingConst = 1`).

**Status.** The only unformalized input is `BoolSigningExists` itself —
the signing produced by the iterative walk. Everything else (envelope
arithmetic, verifier acceptance, and the refutation of the unconditional
`∀ c` statement) is proved without `sorry` or new axioms.
-/

import Komlos.Runtime

namespace Komlos

open scoped BigOperators

/-! ## The well-scaled condition on cost models -/

/-- A bit-cost model is *well-scaled* when the scalar-operation constant is
dominated by the matrix-multiplication leading constant:
`c.scalarConst ≤ c.matmulLeadingConst`. This is the margin the envelope
arithmetic needs: `Theorem11WithRuntime` cannot hold for arbitrary models —
see `BitCostModel.badlyScaled` — while `scalarConst ≤ matmulLeadingConst`
suffices because the residual `(m + n)^ω − n^ω` already covers
`(m + n)² − n² = m² + 2mn`. -/
def BitCostModel.WellScaled (c : BitCostModel) : Prop :=
  c.scalarConst ≤ c.matmulLeadingConst

/-- The schoolbook model `BitCostModel.quadratic` is well-scaled: both
leading constants are `1`. -/
theorem BitCostModel.quadratic_wellScaled : BitCostModel.quadratic.WellScaled :=
  le_refl _

/-! ## The cost-envelope arithmetic -/

/-- If `1 ≤ b ≤ a` and `2 ≤ ω`, then `a² − b² ≤ a^ω − b^ω`: the real-power
gap dominates the square gap. Writing `x^ω = x²·x^{ω−2}` reduces this to
`b²(b^{ω−2} − 1) ≤ a²(a^{ω−2} − 1)`, which holds because `a ≥ b ≥ 1` and
`ω − 2 ≥ 0` give `b^{ω−2} ≤ a^{ω−2}` and `a² ≥ b²`. Used to absorb the
scalar-operation costs into the matrix-multiplication term of
`runtimeEnvelope`. -/
theorem rpow_sub_le_rpow_sub {a b ω : ℝ} (hb : 1 ≤ b) (hba : b ≤ a)
    (hω : 2 ≤ ω) :
    a ^ 2 - b ^ 2 ≤ a ^ ω - b ^ ω := by
  have ha : 1 ≤ a := le_trans hb hba
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb
  have hω2 : 0 ≤ ω - 2 := by linarith
  have hae : a ^ ω = a ^ 2 * a ^ (ω - 2) := by
    have h := Real.rpow_add ha0 (2 : ℝ) (ω - 2)
    rw [show (2 : ℝ) + (ω - 2) = ω by ring] at h
    rw [h, Real.rpow_two]
  have hbe : b ^ ω = b ^ 2 * b ^ (ω - 2) := by
    have h := Real.rpow_add hb0 (2 : ℝ) (ω - 2)
    rw [show (2 : ℝ) + (ω - 2) = ω by ring] at h
    rw [h, Real.rpow_two]
  have hbX : 1 ≤ b ^ (ω - 2) := Real.one_le_rpow hb hω2
  have habX : b ^ (ω - 2) ≤ a ^ (ω - 2) :=
    Real.rpow_le_rpow (le_trans zero_le_one hb) hba hω2
  have hab2 : b ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (le_trans zero_le_one hb) hba 2
  have hterm : b ^ 2 * (b ^ (ω - 2) - 1) ≤ a ^ 2 * (a ^ (ω - 2) - 1) :=
    calc b ^ 2 * (b ^ (ω - 2) - 1)
        ≤ b ^ 2 * (a ^ (ω - 2) - 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg b)
      _ ≤ a ^ 2 * (a ^ (ω - 2) - 1) :=
          mul_le_mul_of_nonneg_right hab2 (by linarith)
  rw [hae, hbe]
  nlinarith [hterm]

/-- Under `WellScaled c`, the accounted verification cost fits the runtime
envelope whenever `m, n, B ≥ 1` and `l = log δ⁻¹ ≥ 0`. Chains
`verificationBitCost_le` with:

* `matmulLeadingConst·n^ω·B ≤ matmulLeadingConst·n^ω·B²` (`B ≤ B²`),
* `mn(B² + B) + mB ≤ ((m + n)² − n²)·B²`
  (`mn·B ≤ mn·B²`, `m·B ≤ m·B² ≤ m²·B²`, using `m ≤ m²`),
* `scalarConst·((m + n)² − n²)·B² ≤
   matmulLeadingConst·((m + n)^ω − n^ω)·B²`
  (`rpow_sub_le_rpow_sub` and `scalarConst ≤ matmulLeadingConst`),
* `n^ω + ((m + n)^ω − n^ω) = (m + n)^ω` and `1 ≤ (1 + l)²`. -/
theorem verificationBitCost_le_envelope (c : BitCostModel)
    (hs : c.WellScaled) {m n B : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hB : 1 ≤ B)
    {l : ℝ} (hl : 0 ≤ l) :
    (verificationBitCost c m n B : ℝ) ≤ runtimeEnvelope c m n B l := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hmn1 : (1 : ℝ) ≤ (m : ℝ) + n := by linarith
  have hmn0 : (0 : ℝ) ≤ (m : ℝ) + n := le_trans zero_le_one hmn1
  have hω0 : (0 : ℝ) ≤ c.ω := le_trans (by norm_num) c.two_le_ω
  have hBB : (B : ℝ) ≤ (B : ℝ) ^ 2 := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left hBR hB0
  have hmm : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left hmR hm0
  have hpow : (n : ℝ) ^ c.ω ≤ ((m : ℝ) + n) ^ c.ω :=
    Real.rpow_le_rpow hn0 (by linarith) hω0
  have he1 : (m : ℝ) * (n : ℝ) * (B : ℝ) ≤ (m : ℝ) * (n : ℝ) * (B : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hBB (mul_nonneg hm0 hn0)
  have he2 : (m : ℝ) * (B : ℝ) ≤ (m : ℝ) * (B : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hBB hm0
  have he3 : (m : ℝ) * (B : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 * (B : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hmm (sq_nonneg _)
  have hscalar : (m : ℝ) * (n : ℝ) * ((B : ℝ) ^ 2 + (B : ℝ)) + (m : ℝ) * (B : ℝ) ≤
      (((m : ℝ) + n) ^ 2 - (n : ℝ) ^ 2) * (B : ℝ) ^ 2 := by
    nlinarith [he1, he2, he3]
  have hresid : ((m : ℝ) + n) ^ 2 - (n : ℝ) ^ 2 ≤
      ((m : ℝ) + n) ^ c.ω - (n : ℝ) ^ c.ω :=
    rpow_sub_le_rpow_sub hnR (by linarith) c.two_le_ω
  have hsc1 : (m : ℝ) * (n : ℝ) * ((B : ℝ) ^ 2 + (B : ℝ)) + (m : ℝ) * (B : ℝ) ≤
      (((m : ℝ) + n) ^ c.ω - (n : ℝ) ^ c.ω) * (B : ℝ) ^ 2 :=
    le_trans hscalar (mul_le_mul_of_nonneg_right hresid (sq_nonneg _))
  have hX0 : (0 : ℝ) ≤ (((m : ℝ) + n) ^ c.ω - (n : ℝ) ^ c.ω) * (B : ℝ) ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hpow) (sq_nonneg _)
  have hsc : c.scalarConst *
        ((m : ℝ) * (n : ℝ) * ((B : ℝ) ^ 2 + (B : ℝ)) + (m : ℝ) * (B : ℝ)) ≤
      c.matmulLeadingConst *
        ((((m : ℝ) + n) ^ c.ω - (n : ℝ) ^ c.ω) * (B : ℝ) ^ 2) :=
    le_trans (mul_le_mul_of_nonneg_left hsc1 c.scalarConst_nonneg)
      (mul_le_mul_of_nonneg_right hs hX0)
  have hmat : c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ) ≤
      c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hBB
      (mul_nonneg c.matmulLeadingConst_nonneg (Real.rpow_nonneg hn0 _))
  have hcomb : (m : ℝ) * (n : ℝ) *
        (c.scalarConst * (B : ℝ) ^ 2 + c.scalarConst * (B : ℝ)) +
        (m : ℝ) * (c.scalarConst * (B : ℝ)) =
      c.scalarConst *
        ((m : ℝ) * (n : ℝ) * ((B : ℝ) ^ 2 + (B : ℝ)) + (m : ℝ) * (B : ℝ)) := by
    ring
  have hsum : c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ) +
        (m : ℝ) * (n : ℝ) *
          (c.scalarConst * (B : ℝ) ^ 2 + c.scalarConst * (B : ℝ)) +
        (m : ℝ) * (c.scalarConst * (B : ℝ)) ≤
      c.matmulLeadingConst * ((m : ℝ) + n) ^ c.ω * (B : ℝ) ^ 2 := by
    rw [add_assoc, hcomb]
    calc c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ) +
          c.scalarConst *
            ((m : ℝ) * (n : ℝ) * ((B : ℝ) ^ 2 + (B : ℝ)) + (m : ℝ) * (B : ℝ))
        ≤ c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ) ^ 2 +
          c.matmulLeadingConst *
            ((((m : ℝ) + n) ^ c.ω - (n : ℝ) ^ c.ω) * (B : ℝ) ^ 2) :=
        add_le_add hmat hsc
      _ = c.matmulLeadingConst * ((m : ℝ) + n) ^ c.ω * (B : ℝ) ^ 2 := by ring
  have hl2 : (1 : ℝ) ≤ (1 + l) ^ 2 := by nlinarith
  have hK : (0 : ℝ) ≤ c.matmulLeadingConst * ((m : ℝ) + n) ^ c.ω * (B : ℝ) ^ 2 :=
    mul_nonneg (mul_nonneg c.matmulLeadingConst_nonneg (Real.rpow_nonneg hmn0 _))
      (sq_nonneg _)
  calc (verificationBitCost c m n B : ℝ)
      ≤ c.matmulLeadingConst * (n : ℝ) ^ c.ω * (B : ℝ) +
          (m : ℝ) * (n : ℝ) *
            (c.scalarConst * (B : ℝ) ^ 2 + c.scalarConst * (B : ℝ)) +
          (m : ℝ) * (c.scalarConst * (B : ℝ)) :=
        verificationBitCost_le c m n B
    _ ≤ c.matmulLeadingConst * ((m : ℝ) + n) ^ c.ω * (B : ℝ) ^ 2 := hsum
    _ = c.matmulLeadingConst * ((m : ℝ) + n) ^ c.ω * (B : ℝ) ^ 2 * 1 := by ring
    _ ≤ c.matmulLeadingConst * ((m : ℝ) + n) ^ c.ω * (B : ℝ) ^ 2 * (1 + l) ^ 2 :=
        mul_le_mul_of_nonneg_left hl2 hK
    _ = runtimeEnvelope c m n B l := rfl

/-! ## Verifier acceptance from real row-value bounds -/

/-- The real row value of a Boolean signing equals the cast of the rational
row value. (Extracted from the proof of `verifySigning_sound`.) -/
theorem rowValue_realSigning_eq_ratCast {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) (ε : Fin n → Bool) (i : Fin m) :
    rowValue (fun i j => (A i j : ℝ)) (realSigning ε) i =
      (rationalRowValue A ε i : ℝ) := by
  unfold rowValue rationalRowValue realSigning
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  cases ε j <;> simp

/-- `verifySigning` accepts when every rational row value is below `99`:
the converse direction of `verifySigning_sound`, unfolding the `decide`. -/
theorem verifySigning_accepts {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (ε : Fin n → Bool) (h : ∀ i, |rationalRowValue A ε i| < 99) :
    verifySigning A ε = true := by
  unfold verifySigning
  rw [decide_eq_true_eq]
  exact h

/-- If a Boolean signing has all real row values below `99`, the exact
rational verifier accepts it: `Rat.cast_abs` transports `|·| < 99` between
`ℚ` and `ℝ`. -/
theorem verifySigning_accepts_of_rowValue_lt {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) (ε : Fin n → Bool)
    (h : ∀ i, |rowValue (fun i j => (A i j : ℝ)) (realSigning ε) i| < 99) :
    verifySigning A ε = true := by
  apply verifySigning_accepts
  intro i
  have hi := h i
  rw [rowValue_realSigning_eq_ratCast, ← Rat.cast_abs] at hi
  exact_mod_cast hi

/-! ## The discrepancy-existence input and the conditional theorem -/

/-- A bit size of `0` forces every field cost — hence the whole accounted
verification cost — to `0`: each cost bound `f B ≤ const·B^k` collapses at
`B = 0`. This discharges the degenerate `inputBitSize A = 0` case (which is
exactly what happens when `m = 0` or `n = 0`). -/
theorem verificationBitCost_bitsize_zero (c : BitCostModel) (m n : ℕ) :
    verificationBitCost c m n 0 = 0 := by
  have key : ∀ x : ℕ, ((x : ℝ) ≤ 0) → x = 0 :=
    fun x h => Nat.cast_eq_zero.mp (le_antisymm h (Nat.cast_nonneg x))
  have hmat : c.matmulCost n 0 = 0 := key _ (by simpa using c.matmulCost_le n 0)
  have hmul : c.mulCost 0 = 0 := key _ (by simpa using c.mulCost_le 0)
  have hadd : c.addCost 0 = 0 := key _ (by simpa using c.addCost_le 0)
  have hcmp : c.cmpCost 0 = 0 := key _ (by simpa using c.cmpCost_le 0)
  simp [verificationBitCost, hmat, hmul, hadd, hcmp]

/-- The discrepancy-existence input, expressed over Boolean signings so that
it feeds directly into `verifySigning`: for every column-normalized
rational matrix there is a Boolean signing whose real row values are all
below `99`. This is the content supplied by the random-walk analysis of the
paper; in this file it remains a *hypothesis* (the walk assembly is a
separate effort). It implies `DiscrepancyPartOfTheorem11` via
`realSigning_isSigning`. -/
def BoolSigningExists : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ),
    ColumnNormalized (fun i j => (A i j : ℝ)) →
      ∃ ε : Fin n → Bool,
        ∀ i, |rowValue (fun i j => (A i j : ℝ)) (realSigning ε) i| < 99

/-- `BoolSigningExists` implies the discrepancy half of Theorem 1.1: take
the real signing associated to the Boolean one. -/
theorem discrepancyPart_of_boolSigningExists (h : BoolSigningExists) :
    DiscrepancyPartOfTheorem11 := by
  intro m n A hA
  obtain ⟨ε, hε⟩ := h m n A hA
  exact ⟨realSigning ε, realSigning_isSigning ε, hε⟩

/-- The conditional runtime theorem: if the cost model is well-scaled and
every column-normalized rational matrix admits a Boolean signing with real
row values below `99`, then `DiscrepancyRuntimeBound c` holds — the
existential signing is produced by the input, `verifySigning` accepts it,
and `verificationBitCost_le_envelope` bounds the accounted cost by
`runtimeEnvelope c m n (inputBitSize A) (log δ⁻¹)`. -/
theorem discrepancyRuntimeBound_of_existence (c : BitCostModel)
    (hs : c.WellScaled) (hex : BoolSigningExists) :
    DiscrepancyRuntimeBound c := by
  intro m n A δ hA hδ0 hδ1
  obtain ⟨ε, hε⟩ := hex m n A hA
  refine ⟨ε, verifySigning_accepts_of_rowValue_lt A ε hε, ?_⟩
  have hl : 0 ≤ Real.log δ⁻¹ := log_inv_nonneg hδ0 hδ1
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hB0 : inputBitSize A = 0 := by simp [inputBitSize]
    rw [hB0, verificationBitCost_bitsize_zero]
    simpa using runtimeEnvelope_nonneg c 0 n 0 (Real.log δ⁻¹)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hB0 : inputBitSize A = 0 := by simp [inputBitSize]
    rw [hB0, verificationBitCost_bitsize_zero]
    simpa using runtimeEnvelope_nonneg c m 0 0 (Real.log δ⁻¹)
  rcases Nat.eq_zero_or_pos (inputBitSize A) with hB | hB
  · rw [hB, verificationBitCost_bitsize_zero]
    simpa using runtimeEnvelope_nonneg c m n 0 (Real.log δ⁻¹)
  · exact verificationBitCost_le_envelope c hs hm hn hB hl

/-- Instantiation at the schoolbook model: if Boolean signings below `99`
always exist, then `DiscrepancyRuntimeBound` holds for
`BitCostModel.quadratic`. -/
theorem discrepancyRuntimeBound_quadratic (h : BoolSigningExists) :
    DiscrepancyRuntimeBound BitCostModel.quadratic :=
  discrepancyRuntimeBound_of_existence _ BitCostModel.quadratic_wellScaled h

/-! ## The `∀ c` statement is too strong: a badly-scaled countermodel -/

/-- A deliberately *badly scaled* cost model: unit scalar constant but zero
matrix-multiplication constant, witnessed by the zero matrix-multiplication
cost function. It satisfies every `BitCostModel` field constraint, yet
`DiscrepancyRuntimeBound` fails for it: on the `1 × 1` matrix `[[1]]` the
envelope is `0` while the scalar account is `8`. This demonstrates that the
unconditional `∀ c, DiscrepancyRuntimeBound c` is not provable — some
admissibility condition like `WellScaled` is genuinely needed. -/
def BitCostModel.badlyScaled : BitCostModel where
  ω := 2
  matmulLeadingConst := 0
  scalarConst := 1
  addCost := fun B => B
  mulCost := fun B => B ^ 2
  divCost := fun B => B ^ 2
  cmpCost := fun B => B
  matmulCost := fun _ _ => 0
  two_le_ω := le_refl 2
  matmulLeadingConst_nonneg := le_refl 0
  scalarConst_nonneg := zero_le_one
  addCost_le := fun _ => by simp
  mulCost_le := fun _ => by simp
  divCost_le := fun _ => by simp
  cmpCost_le := fun _ => by simp
  matmulCost_le := fun _ _ => by simp

/-- `badlyScaled` is indeed not well-scaled: `1 ≤ 0` fails. -/
theorem badlyScaled_not_wellScaled : ¬ BitCostModel.badlyScaled.WellScaled := by
  intro h
  exact (by norm_num : ¬ ((1 : ℝ) ≤ 0)) h

/-- `DiscrepancyRuntimeBound` fails for the badly-scaled model: on
`A = [[1]]` (bit size `2`, `δ = 1`) the accounted cost is `8 > 0` while the
envelope is `0`, so no signing can satisfy the bound. -/
theorem not_discrepancyRuntimeBound_badlyScaled :
    ¬ DiscrepancyRuntimeBound BitCostModel.badlyScaled := by
  intro h
  obtain ⟨ε, -, hcost⟩ := h 1 1 (fun _ _ => (1 : ℚ)) 1
    (by intro j; simp) zero_lt_one (le_refl 1)
  have hB : inputBitSize (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℚ)) = 2 := by
    simp [inputBitSize, ratBitSize_one]
  have hcost8 : verificationBitCost BitCostModel.badlyScaled 1 1 2 = 8 := by
    decide
  have henv : runtimeEnvelope BitCostModel.badlyScaled 1 1 2
      (Real.log (1 : ℝ)⁻¹) = 0 := by
    simp [runtimeEnvelope, BitCostModel.badlyScaled]
  rw [hB, hcost8, henv] at hcost
  norm_num at hcost

/-- Consequently the unconditional `Theorem11WithRuntime` — the runtime
statement for *every* admissible cost model — is refutable. The correct
formulation is `discrepancyRuntimeBound_of_existence` with its `WellScaled`
hypothesis. -/
theorem not_theorem11WithRuntime : ¬ Theorem11WithRuntime :=
  fun h => not_discrepancyRuntimeBound_badlyScaled (h _)

end Komlos
