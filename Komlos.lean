import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Komlos

open scoped BigOperators

abbrev Input (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

def IsSigning {n : ℕ} (ε : Fin n → ℝ) : Prop :=
  ∀ j, ε j = -1 ∨ ε j = 1

def ColumnNormalized {m n : ℕ} (A : Input m n) : Prop :=
  ∀ j, ∑ i, (A i j) ^ 2 ≤ 1

def rowValue {m n : ℕ} (A : Input m n) (x : Fin n → ℝ) (i : Fin m) : ℝ :=
  ∑ j, A i j * x j

def HasDiscrepancyBelow {m n : ℕ} (A : Input m n) (ε : Fin n → ℝ) (C : ℝ) : Prop :=
  IsSigning ε ∧ ∀ i, |rowValue A ε i| < C

def DiscrepancyPartOfTheorem11 : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ),
    ColumnNormalized (fun i j => (A i j : ℝ)) →
      ∃ ε, HasDiscrepancyBelow (fun i j => (A i j : ℝ)) ε 99

theorem signing_abs {n : ℕ} {ε : Fin n → ℝ} (hε : IsSigning ε) (j : Fin n) :
    |ε j| = 1 := by
  rcases hε j with h | h <;> rw [h] <;> norm_num

theorem rowValue_abs_le_l1 {m n : ℕ} (A : Input m n) {ε : Fin n → ℝ}
    (hε : IsSigning ε) (i : Fin m) :
    |rowValue A ε i| ≤ ∑ j, |A i j| := by
  unfold rowValue
  calc
    |∑ j, A i j * ε j| ≤ ∑ j, |A i j * ε j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |A i j| := by simp [abs_mul, signing_abs hε]

theorem discarded_row_bound {m n : ℕ} (A : Input m n) {ε : Fin n → ℝ}
    (hε : IsSigning ε) (i : Fin m) (hi : ∑ j, |A i j| ≤ 1) :
    |rowValue A ε i| ≤ 1 :=
  (rowValue_abs_le_l1 A hε i).trans hi

theorem normalized_entry_abs_le_one {m n : ℕ} {A : Input m n}
    (hA : ColumnNormalized A) (i : Fin m) (j : Fin n) : |A i j| ≤ 1 := by
  have hsq : (A i j) ^ 2 ≤ 1 :=
    (Finset.single_le_sum (fun k _ => sq_nonneg (A k j)) (Finset.mem_univ i)).trans (hA j)
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem total_mass_le_dimension {m n : ℕ} {A : Input m n}
    (hA : ColumnNormalized A) : ∑ i, ∑ j, (A i j) ^ 2 ≤ (n : ℝ) := by
  calc
    ∑ i, ∑ j, (A i j) ^ 2 = ∑ j, ∑ i, (A i j) ^ 2 := Finset.sum_comm
    _ ≤ ∑ _j : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hA j)
    _ = n := by simp

theorem row_l1_sq_le_dimension_mul_mass {m n : ℕ} (A : Input m n) (i : Fin m) :
    (∑ j, |A i j|) ^ 2 ≤ (n : ℝ) * ∑ j, (A i j) ^ 2 := by
  simpa [sq_abs] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n => (1 : ℝ))
      (fun j => |A i j|))

theorem retained_row_count {m n : ℕ} {A : Input m n}
    (hA : ColumnNormalized A) (hn : 0 < n) (S : Finset (Fin m))
    (hS : ∀ i ∈ S, 1 < ∑ j, |A i j|) : S.card < n ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hne : S.Nonempty
  · have hrow : ∀ i ∈ S, (1 : ℝ) < n * ∑ j, (A i j) ^ 2 := by
      intro i hi
      have hcs := row_l1_sq_le_dimension_mul_mass A i
      have hi' := hS i hi
      nlinarith
    have hstrict : (S.card : ℝ) < ∑ i ∈ S, (n : ℝ) * ∑ j, (A i j) ^ 2 := by
      simpa using Finset.sum_lt_sum_of_nonempty hne hrow
    have hmass : (∑ i ∈ S, ∑ j, (A i j) ^ 2) ≤ (n : ℝ) := by
      calc
        (∑ i ∈ S, ∑ j, (A i j) ^ 2) ≤ ∑ i, ∑ j, (A i j) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            (fun i _ _ => Finset.sum_nonneg (fun j _ => sq_nonneg (A i j)))
        _ ≤ n := total_mass_le_dimension hA
    rw [← Finset.mul_sum] at hstrict
    have hcard : (S.card : ℝ) < (n : ℝ) ^ 2 := by nlinarith
    exact_mod_cast hcard
  · have hzero : S.card = 0 := by simp [Finset.not_nonempty_iff_eq_empty.mp hne]
    rw [hzero]
    exact pow_pos hn 2

theorem small_dimension_signing {m n : ℕ} {A : Input m n}
    (hA : ColumnNormalized A) (hn : n < 64) {ε : Fin n → ℝ}
    (hε : IsSigning ε) : HasDiscrepancyBelow A ε 99 := by
  refine ⟨hε, fun i => ?_⟩
  have hrow : |rowValue A ε i| ≤ (n : ℝ) := calc
    |rowValue A ε i| ≤ ∑ j, |A i j| := rowValue_abs_le_l1 A hε i
    _ ≤ ∑ _j : Fin n, (1 : ℝ) :=
      Finset.sum_le_sum (fun j _ => normalized_entry_abs_le_one hA i j)
    _ = n := by simp
  have hn' : (n : ℝ) < 64 := by exact_mod_cast hn
  exact lt_of_le_of_lt hrow (by linarith)

theorem small_dimension_exists {m n : ℕ} {A : Input m n}
    (hA : ColumnNormalized A) (hn : n < 64) :
    ∃ ε, HasDiscrepancyBelow A ε 99 := by
  exact ⟨fun _ => 1, small_dimension_signing hA hn (fun _ => Or.inr rfl)⟩

theorem spread_mass_zero_in_small_dimension {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hn : n < 64)
    (hspread : ∀ j, p j ≤ (∑ k, p k) / 64) : ∑ j, p j = 0 := by
  have hq : 0 ≤ ∑ j, p j := Finset.sum_nonneg (fun j _ => hp j)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hspread j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hn' : (n : ℝ) < 64 := by exact_mod_cast hn
  nlinarith

theorem symmetric_coordinate_energy (x h t : ℝ) :
    ((x + t * h) ^ 2 + (x - t * h) ^ 2) / 2 = x ^ 2 + t ^ 2 * h ^ 2 := by
  ring

theorem symmetric_energy {n : ℕ} (x h : Fin n → ℝ) (t : ℝ) :
    ((∑ j, (x j + t * h j) ^ 2) + (∑ j, (x j - t * h j) ^ 2)) / 2 =
      (∑ j, (x j) ^ 2) + t ^ 2 * ∑ j, (h j) ^ 2 := by
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  simp_rw [symmetric_coordinate_energy]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

def energy {n : ℕ} (p x : Fin n → ℝ) : ℝ :=
  ∑ j, p j * (1 - (x j) ^ 2)

noncomputable def barrier (σ d r G : ℝ) : ℝ :=
  (σ * d - 263 / 5) / r + 4 * G / r ^ 2 + 12

theorem energy_nonneg {n : ℕ} (p x : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hx : ∀ j, |x j| ≤ 1) : 0 ≤ energy p x := by
  apply Finset.sum_nonneg
  intro j _
  have hj := abs_le.mp (hx j)
  exact mul_nonneg (hp j) (by nlinarith [sq_nonneg (x j)])

theorem energy_le_mass {n : ℕ} (p x : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) : energy p x ≤ ∑ j, p j := by
  apply Finset.sum_le_sum
  intro j _
  nlinarith [mul_nonneg (hp j) (sq_nonneg (x j))]

theorem energy_increment {n : ℕ} (p x y : Fin n → ℝ) :
    energy p (fun j => x j + y j) - energy p x =
      ∑ j, (-2 * p j * x j * y j - p j * (y j) ^ 2) := by
  rw [energy, energy, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem barrier_increment (σ d r G δd δG : ℝ) :
    barrier σ (d + δd) r (G + δG) - barrier σ d r G =
      σ * δd / r + 4 * δG / r ^ 2 := by
  unfold barrier
  ring

theorem barrier_displacement {n : ℕ} (p b x y : Fin n → ℝ) (σ d r : ℝ) :
    barrier σ (d + ∑ j, b j * y j) r (energy p (fun j => x j + y j)) -
      barrier σ d r (energy p x) =
      (∑ j, (σ * b j / r - 8 * p j / r ^ 2 * x j) * y j) -
        4 * ∑ j, p j / r ^ 2 * (y j) ^ 2 := by
  have he : energy p (fun j => x j + y j) =
      energy p x + ∑ j, (-2 * p j * x j * y j - p j * (y j) ^ 2) := by
    linarith [energy_increment p x y]
  rw [he, barrier_increment]
  simp_rw [Finset.mul_sum, Finset.sum_div]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem protected_barrier_nonincrease {n : ℕ} (p b x y : Fin n → ℝ) (σ d r : ℝ)
    (hp : ∀ j, 0 ≤ p j)
    (hgradient : ∑ j, (σ * b j / r - 8 * p j / r ^ 2 * x j) * y j = 0) :
    barrier σ (d + ∑ j, b j * y j) r (energy p (fun j => x j + y j)) ≤
      barrier σ d r (energy p x) := by
  have he := barrier_displacement p b x y σ d r
  rw [hgradient] at he
  have hnonneg : 0 ≤ ∑ j, p j / r ^ 2 * (y j) ^ 2 :=
    Finset.sum_nonneg (fun j _ =>
      mul_nonneg (div_nonneg (hp j) (sq_nonneg r)) (sq_nonneg (y j)))
  linarith

theorem spread_gradient_bound {a z x σ : ℝ} (haz : a ^ 2 = z)
    (hz : z ≤ 1 / 64) (hx : |x| ≤ 1) (hσ : |σ| = 1) :
    (σ * a - 8 * z * x) ^ 2 ≤ 4 * z := by
  have hz0 : 0 ≤ z := by nlinarith [sq_nonneg a]
  have ha0 := abs_nonneg a
  have ha2 := sq_abs a
  have h8 : 8 * z ≤ |a| := by nlinarith
  have hterm : |8 * z * x| ≤ 8 * z := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8),
      abs_of_nonneg hz0]
    nlinarith
  have hbound : |σ * a - 8 * z * x| ≤ 2 * |a| := by
    have ht := abs_sub (σ * a) (8 * z * x)
    rw [abs_mul, hσ, one_mul] at ht
    linarith
  nlinarith [sq_abs (σ * a - 8 * z * x), abs_nonneg (σ * a - 8 * z * x)]

theorem barrier_controls_signed_value {σ d r G : ℝ} (hr : 0 < r)
    (hG : 0 ≤ G) (hu : barrier σ d r G ≤ 0) : σ * d < 263 / 5 := by
  have hterm : 0 ≤ 4 * G / r ^ 2 := div_nonneg (by positivity) (sq_nonneg r)
  have hquot : (σ * d - 263 / 5) / r < 0 := by
    unfold barrier at hu
    linarith
  have hnum : σ * d - 263 / 5 < 0 := by
    simpa using (div_lt_iff₀ hr).mp hquot
  linarith

theorem barriers_control_abs_value {d r G : ℝ} (hr : 0 < r) (hG : 0 ≤ G)
    (hplus : barrier 1 d r G ≤ 0) (hminus : barrier (-1) d r G ≤ 0) :
    |d| < 263 / 5 := by
  have hp := barrier_controls_signed_value hr hG hplus
  have hm := barrier_controls_signed_value hr hG hminus
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem initial_barrier_lt_neg20 {r G : ℝ} (σ : ℝ) (hr : 0 < r)
    (hrmax : r ≤ 291 / 200) (hG : G ≤ r ^ 2) : barrier σ 0 r G < -20 := by
  have hq : (σ * 0 - 263 / 5) / r < -36 :=
    (div_lt_iff₀ hr).mpr (by nlinarith)
  have he : 4 * G / r ^ 2 ≤ 4 :=
    (div_le_iff₀ (sq_pos_of_pos hr)).mpr (by nlinarith)
  unfold barrier
  linarith

theorem barrier_pair_sum {d r G : ℝ} (hr : 0 < r)
    (hrmax : r ≤ 291 / 200) (hG : G ≤ r ^ 2) :
    barrier 1 d r G + barrier (-1) d r G < -2 := by
  have hid : barrier 1 d r G + barrier (-1) d r G = 2 * barrier 1 0 r G := by
    unfold barrier
    ring
  rw [hid]
  linarith [initial_barrier_lt_neg20 1 hr hrmax hG]

theorem protected_signs_exclusive {d r G : ℝ} (hr : 0 < r)
    (hrmax : r ≤ 291 / 200) (hG : G ≤ r ^ 2) :
    ¬ (-1 ≤ barrier 1 d r G ∧ -1 ≤ barrier (-1) d r G) := by
  have hs := barrier_pair_sum (d := d) hr hrmax hG
  rintro ⟨hp, hm⟩
  linarith

theorem curvature_dimension_margin :
    (1 : ℝ) - 1 / (291 / 200) ^ 2 - 5 * (65 / 64) ^ 4 / 238 -
      1 / (64 * (4 / 25 - 3 / 625)) - 1 / 2048 -
      ((1 + 4 / 25) * (1 + 1 / 10000)) / (4 * (1 - 4 / 25) * (1 - 1 / 64)) >
      1 / 32 := by
  norm_num

theorem deletion_charge {q b : ℝ} (hbq : b ^ 2 ≤ q) (hdelete : q / 64 < b ^ 2) :
    |b| < (8 + Real.sqrt 63) * (Real.sqrt q - Real.sqrt (q - b ^ 2)) := by
  have hq : 0 ≤ q := (sq_nonneg b).trans hbq
  have hrem : 0 ≤ q - b ^ 2 := sub_nonneg.mpr hbq
  have hs := Real.sq_sqrt hq
  have ht := Real.sq_sqrt hrem
  have hs0 := Real.sqrt_nonneg q
  have ht0 := Real.sqrt_nonneg (q - b ^ 2)
  have hk := Real.sq_sqrt (show (0 : ℝ) ≤ 63 by norm_num)
  have hk0 := Real.sqrt_nonneg (63 : ℝ)
  have hbabs := sq_abs b
  have hbpos : 0 < |b| := by nlinarith [abs_nonneg b]
  have hsbound : Real.sqrt q < 8 * |b| := by nlinarith
  have htbound : Real.sqrt (q - b ^ 2) < Real.sqrt 63 * |b| := by
    have heq : (Real.sqrt 63 * |b|) ^ 2 = 63 * b ^ 2 := by
      rw [mul_pow, hk, hbabs]
    have hnonneg := mul_nonneg hk0 (abs_nonneg b)
    nlinarith
  have hdiff : 0 < Real.sqrt q - Real.sqrt (q - b ^ 2) := by nlinarith
  have hsum : 0 < (8 + Real.sqrt 63) * |b| -
      (Real.sqrt q + Real.sqrt (q - b ^ 2)) := by nlinarith
  apply (mul_lt_mul_iff_of_pos_left hbpos).mp
  nlinarith [mul_pos hdiff hsum]

theorem sqrt63_lt : Real.sqrt 63 < 127 / 16 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 63 by norm_num)
  have hn := Real.sqrt_nonneg (63 : ℝ)
  nlinarith

theorem deletion_constant_bound :
    (263 / 5 : ℝ) + 2 * (291 / 200) * (8 + Real.sqrt 63) < 31673 / 320 := by
  nlinarith [sqrt63_lt]

theorem final_constant_margin :
    (31673 / 320 : ℝ) + 1 / 100 + 1 / 1000 + 1 / 10000 < 9899 / 100 := by
  norm_num

theorem input_rounding_error {m n : ℕ} (A B : Input m n) {ε : Fin n → ℝ}
    (hε : IsSigning ε) {δ : ℝ} (herr : ∀ i, ∑ j, |A i j - B i j| ≤ δ)
    (i : Fin m) : |rowValue A ε i - rowValue B ε i| ≤ δ := by
  have heq : rowValue A ε i - rowValue B ε i =
      rowValue (fun i j => A i j - B i j) ε i := by
    unfold rowValue
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  exact (rowValue_abs_le_l1 _ hε i).trans (herr i)

theorem accepted_output_sound {m n : ℕ} (A B : Input m n) {ε : Fin n → ℝ}
    (hε : IsSigning ε)
    (herr : ∀ i, ∑ j, |A i j - B i j| ≤ 1 / 10000)
    (hcheck : ∀ i, |rowValue B ε i| ≤ 9899 / 100) :
    HasDiscrepancyBelow A ε 99 := by
  refine ⟨hε, fun i => ?_⟩
  have he := input_rounding_error A B hε herr i
  have ht : |rowValue A ε i| ≤
      |rowValue A ε i - rowValue B ε i| + |rowValue B ε i| := by
    simpa using abs_add_le (rowValue A ε i - rowValue B ε i) (rowValue B ε i)
  linarith [hcheck i]

def realSigning {n : ℕ} (ε : Fin n → Bool) : Fin n → ℝ :=
  fun j => if ε j then 1 else -1

def rationalRowValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (ε : Fin n → Bool) (i : Fin m) : ℚ :=
  ∑ j, A i j * (if ε j then 1 else -1)

def verifySigning {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (ε : Fin n → Bool) : Bool :=
  decide (∀ i, |rationalRowValue A ε i| < 99)

theorem realSigning_isSigning {n : ℕ} (ε : Fin n → Bool) : IsSigning (realSigning ε) := by
  intro j
  cases h : ε j <;> simp [realSigning, h]

theorem verifySigning_sound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (ε : Fin n → Bool) (h : verifySigning A ε = true) :
    HasDiscrepancyBelow (fun i j => (A i j : ℝ)) (realSigning ε) 99 := by
  have hcheck : ∀ i, |rationalRowValue A ε i| < 99 := of_decide_eq_true h
  refine ⟨realSigning_isSigning ε, fun i => ?_⟩
  have hcast : rowValue (fun i j => (A i j : ℝ)) (realSigning ε) i =
      (rationalRowValue A ε i : ℝ) := by
    unfold rowValue rationalRowValue realSigning
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    cases ε j <;> simp
  rw [hcast]
  exact_mod_cast hcheck i

theorem verify_zero_matrix {m n : ℕ} (ε : Fin n → Bool) :
    verifySigning (fun (_ : Fin m) (_ : Fin n) => (0 : ℚ)) ε = true := by
  simp [verifySigning, rationalRowValue]

theorem verify_accepts_below_threshold :
    verifySigning (fun (_ : Fin 1) (_ : Fin 98) => (1 : ℚ)) (fun _ => true) = true := by
  norm_num [verifySigning, rationalRowValue]

theorem verify_rejects_at_threshold :
    verifySigning (fun (_ : Fin 1) (_ : Fin 99) => (1 : ℚ)) (fun _ => true) = false := by
  norm_num [verifySigning, rationalRowValue]

def affineValue {n : ℕ} (c : ℝ) (b x : Fin n → ℝ) : ℝ :=
  c + ∑ j, b j * x j

theorem affine_change_defect {n : ℕ} (c c' : ℝ) (b b' x y : Fin n → ℝ) :
    affineValue c b y - affineValue c' b' y =
      -(affineValue c' b' x - affineValue c b x) -
        ∑ j, (b' j - b j) * (y j - x j) := by
  unfold affineValue
  simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

theorem affine_history_defect {n : ℕ} (c : ℕ → ℝ) (b x : ℕ → Fin n → ℝ)
    (y : Fin n → ℝ) (N : ℕ) :
    affineValue (c 0) (b 0) y - affineValue (c N) (b N) y =
      ∑ t ∈ Finset.range N,
        (-(affineValue (c (t + 1)) (b (t + 1)) (x t) -
            affineValue (c t) (b t) (x t)) -
          ∑ j, (b (t + 1) j - b t j) * (y j - x t j)) := by
  rw [← Finset.sum_range_sub' (fun t => affineValue (c t) (b t) y) N]
  apply Finset.sum_congr rfl
  intro t _
  exact affine_change_defect (c t) (c (t + 1)) (b t) (b (t + 1)) (x t) y

theorem total_deleted_coefficient_bound (q b : ℕ → ℝ) (N : ℕ)
    (hremove : ∀ t < N, (b t) ^ 2 ≤ q t)
    (hdelete : ∀ t < N, q t / 64 < (b t) ^ 2)
    (hnext : ∀ t < N, q (t + 1) ≤ q t - (b t) ^ 2) :
    ∑ t ∈ Finset.range N, |b t| ≤ (8 + Real.sqrt 63) * Real.sqrt (q 0) := by
  have hK : 0 ≤ 8 + Real.sqrt 63 := by positivity
  calc
    (∑ t ∈ Finset.range N, |b t|) ≤
        ∑ t ∈ Finset.range N,
          (8 + Real.sqrt 63) * (Real.sqrt (q t) - Real.sqrt (q (t + 1))) := by
      apply Finset.sum_le_sum
      intro t ht
      have ht' := Finset.mem_range.mp ht
      have hc := deletion_charge (hremove t ht') (hdelete t ht')
      have hs := Real.sqrt_le_sqrt (hnext t ht')
      exact hc.le.trans (mul_le_mul_of_nonneg_left (by linarith) hK)
    _ = (8 + Real.sqrt 63) * (Real.sqrt (q 0) - Real.sqrt (q N)) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub']
    _ ≤ (8 + Real.sqrt 63) * Real.sqrt (q 0) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_nonneg (q N)]) hK

theorem cube_difference_abs_le_two {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |y - x| ≤ 2 := by
  have h := abs_sub y x
  linarith

theorem deleted_defect_bound (q b x y : ℕ → ℝ) (N : ℕ)
    (hremove : ∀ t < N, (b t) ^ 2 ≤ q t)
    (hdelete : ∀ t < N, q t / 64 < (b t) ^ 2)
    (hnext : ∀ t < N, q (t + 1) ≤ q t - (b t) ^ 2)
    (hx : ∀ t < N, |x t| ≤ 1) (hy : ∀ t < N, |y t| ≤ 1)
    (hq0 : q 0 ≤ (291 / 200) ^ 2) :
    |∑ t ∈ Finset.range N, b t * (y t - x t)| ≤
      2 * (291 / 200) * (8 + Real.sqrt 63) := by
  have hsqrt : Real.sqrt (q 0) ≤ 291 / 200 := by
    calc
      Real.sqrt (q 0) ≤ Real.sqrt ((291 / 200 : ℝ) ^ 2) := Real.sqrt_le_sqrt hq0
      _ = 291 / 200 := by rw [Real.sqrt_sq (by norm_num)]
  have hcoeff := total_deleted_coefficient_bound q b N hremove hdelete hnext
  have hK : 0 ≤ 8 + Real.sqrt 63 := by positivity
  calc
    |∑ t ∈ Finset.range N, b t * (y t - x t)| ≤
        ∑ t ∈ Finset.range N, |b t * (y t - x t)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range N, 2 * |b t| := by
      apply Finset.sum_le_sum
      intro t ht
      have ht' := Finset.mem_range.mp ht
      rw [abs_mul]
      nlinarith [cube_difference_abs_le_two (hx t ht') (hy t ht'), abs_nonneg (b t)]
    _ = 2 * ∑ t ∈ Finset.range N, |b t| := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * ((8 + Real.sqrt 63) * Real.sqrt (q 0)) := by linarith
    _ ≤ 2 * (291 / 200) * (8 + Real.sqrt 63) := by nlinarith

theorem completed_row_error_bound {value tracked deletion retirement offset δret δoff : ℝ}
    (hvalue : value = tracked + deletion + retirement + offset)
    (htracked : |tracked| < 263 / 5)
    (hdeletion : |deletion| ≤ 2 * (291 / 200) * (8 + Real.sqrt 63))
    (hretirement : |retirement| ≤ δret) (hoffset : |offset| ≤ δoff) :
    |value| < 31673 / 320 + δret + δoff := by
  have ht : |value| ≤ |tracked| + |deletion| + |retirement| + |offset| := by
    rw [hvalue]
    calc
      |tracked + deletion + retirement + offset| ≤
          |tracked + deletion + retirement| + |offset| := abs_add_le _ _
      _ ≤ |tracked + deletion| + |retirement| + |offset| := by
        linarith [abs_add_le (tracked + deletion) retirement]
      _ ≤ |tracked| + |deletion| + |retirement| + |offset| := by
        linarith [abs_add_le tracked deletion]
  linarith [deletion_constant_bound]

theorem live_row_count {m n : ℕ} {A : Input m n} (hA : ColumnNormalized A)
    (S : Finset (Fin m)) {qstar : ℝ} (hqstar : 0 < qstar)
    (hlive : ∀ i ∈ S, qstar ≤ ∑ j, (A i j) ^ 2) : (S.card : ℝ) ≤ n / qstar := by
  apply (le_div_iff₀ hqstar).mpr
  calc
    (S.card : ℝ) * qstar = ∑ _i ∈ S, qstar := by simp
    _ ≤ ∑ i ∈ S, ∑ j, (A i j) ^ 2 := Finset.sum_le_sum hlive
    _ ≤ ∑ i, ∑ j, (A i j) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun i _ _ => Finset.sum_nonneg (fun j _ => sq_nonneg (A i j)))
    _ ≤ n := total_mass_le_dimension hA

end Komlos
