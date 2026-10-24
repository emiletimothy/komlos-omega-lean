/-
# Predictable iteration and ε-net arguments for the adaptive Gaussian invariant

This module develops the *iteration* and *covering* parts of the paper's
Lemma D.1 → Theorem 4.1 chain (the `gauss_inv` node), on top of the
conditioning core proved in `Komlos/GaussianDisintegration.lean`.

## What is proved unconditionally

* `MetricNet` — a finite internal `ε`-net of a set `K` in a (pseudo)metric
  space — and `exists_metricNet`: every compact set admits one.
  Instantiations `exists_metricNet_sphere_pi` (`Fin n → ℝ`, sup metric) and
  `exists_metricNet_euclideanSphere` (`EuclideanSpace ℝ (Fin n)`).
* `measure_biUnion_finset_le_const`: the union bound
  `μ (⋃ x ∈ s, bad x) ≤ s.card • c` over a `Finset`.
* `tail_transfer_lipschitz`, `abs_inner_sub_le`, `inner_tail_transfer`: the
  Lipschitz/continuity-extension step — in particular for the inner-product
  statistic `u ↦ ⟪u, g ω⟫_ℝ` (Cauchy–Schwarz), the Gaussian-facing statistic
  of Appendix D.
* `measure_iUnion_le_net` (**the D.7–D.9 pattern**): pointwise measure bounds
  `μ (badNet x) ≤ c` at every net point + a transfer property
  `bad y ⊆ badNet x` for `dist y x < ε` ⇒ `μ (⋃ y ∈ K, bad y) ≤ N.card • c`.
  Corollaries `measure_iUnion_lipschitz_tail_le` (scalar Lipschitz statistic)
  and `measure_iUnion_inner_tail_le` (inner-product statistic).
* `PredictableSteps` / `PredictableSteps.jointLaw`: an adapted sequence over
  `ℕ` whose step-`t` law is a Markov kernel evaluated on the length-`t`
  transcript; `jointLaw (t+1) = (jointLaw t ⊗ₘ step t).map snocAppend`.
  `jointLaw_map_histTrunc` proves the transcript marginal is preserved
  (adaptedness).  `jointLaw_iid` shows the i.i.d. chain has law
  `Measure.pi fun _ ↦ μ`.
* `ae_goodHist_jointLaw` (**the predictable-induction lemma**): if a
  measurable transcript invariant `φ` holds at step `0` and is preserved a.e.
  by each conditional draw on every good history, then the joint law at every
  time `t` satisfies the whole history invariant `GoodHist φ` a.e.

## What is encapsulated

`AdaptiveGaussianSteps` packages the step-`t` conditional Gaussian law
`gaussCondKernel (exposed t h) (obs t h)` (kernel `ker` Gaussian shifted by
the Moore–Penrose lift — the per-step content of Lemma D.1, whose core is
`stdGaussian_map_prodMk_compProd`), together with the measurability field
`step_measurable`.  `GaussianInvariantInput` adds the remaining analytic
input `step_ae` — the per-step density invariant a.e. on good histories — as
a named hypothesis field.  `GaussianInvariantInput.ae_jointLaw` then produces
the terminal a.e. invariant from these inputs.
-/

import Komlos.GaussianDisintegration
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

namespace Komlos

open InnerProductSpace MeasureTheory ProbabilityTheory Metric Finset
open scoped ENNReal

noncomputable section

/-! ## Finite ε-nets on compact sets -/

/-- A finite `ε`-net for `K`: a `Finset` of points of `K` whose `ε`-balls
cover `K`.  This is the covering object used by the net arguments
(equations D.7–D.9 of the paper). -/
structure MetricNet {X : Type*} [PseudoMetricSpace X] (K : Set X) (ε : ℝ) where
  /-- The finite set of centers. -/
  carrier : Finset X
  /-- Net points lie in `K` (an internal net). -/
  carrier_subset : ∀ x ∈ carrier, x ∈ K
  /-- The `ε`-balls around the centers cover `K`. -/
  covers : K ⊆ ⋃ x ∈ carrier, Metric.ball x ε

/-- Compact sets admit finite `ε`-nets (Mathlib's
`finite_cover_balls_of_compact`, repackaged). -/
theorem exists_metricNet {X : Type*} [PseudoMetricSpace X] {K : Set X}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) : Nonempty (MetricNet K ε) := by
  obtain ⟨t, hts, htfin, hcover⟩ := finite_cover_balls_of_compact hK hε
  refine ⟨{ carrier := htfin.toFinset,
            carrier_subset := fun x hx ↦ hts (htfin.mem_toFinset.mp hx),
            covers := ?_ }⟩
  intro x hx
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hcover hx)
  obtain ⟨hyt, hxy⟩ := Set.mem_iUnion.mp hy
  exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr
    ⟨htfin.mem_toFinset.mpr hyt, hxy⟩⟩

/-- The unit sphere of `Fin n → ℝ` (product sup metric) admits finite nets. -/
theorem exists_metricNet_sphere_pi (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (MetricNet (sphere (0 : Fin n → ℝ) 1) ε) :=
  exists_metricNet (isCompact_sphere _ _) hε

/-- The unit sphere of `EuclideanSpace ℝ (Fin n)` admits finite nets. -/
theorem exists_metricNet_euclideanSphere (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (MetricNet (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ε) :=
  exists_metricNet (isCompact_sphere _ _) hε

/-! ## The union bound over a finite net -/

/-- Finite union bound with a uniform per-point bound: a union over a
`Finset` of events of measure `≤ c` has measure `≤ s.card • c`.  This is the
union-bound step of the net argument. -/
theorem measure_biUnion_finset_le_const {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset X) (bad : X → Set Ω) {c : ℝ≥0∞}
    (h : ∀ x ∈ s, μ (bad x) ≤ c) :
    μ (⋃ x ∈ s, bad x) ≤ s.card • c :=
  calc μ (⋃ x ∈ s, bad x)
      ≤ ∑ x ∈ s, μ (bad x) := measure_biUnion_finset_le (μ := μ) s bad
    _ ≤ ∑ _x ∈ s, c := Finset.sum_le_sum fun x hx ↦ h x hx
    _ = s.card • c := Finset.sum_const _

/-! ## The continuity-extension step -/

/-- **Slack transfer for a Lipschitz scalar statistic**: if `x ↦ φ x ω` is
`L`-Lipschitz in `x` for every `ω`, then the level-`τ` tail event at `x`
entails the level-`(τ − L·ε)` tail event at every `y` within `ε`. -/
theorem tail_transfer_lipschitz {Ω X : Type*} [PseudoMetricSpace X]
    (φ : X → Ω → ℝ) {L ε : ℝ} (hL : 0 ≤ L)
    (hφ : ∀ (x y : X) (ω : Ω), |φ x ω - φ y ω| ≤ L * dist x y)
    {x y : X} (hd : dist x y < ε) {τ : ℝ} :
    {ω : Ω | τ ≤ φ x ω} ⊆ {ω : Ω | τ - L * ε ≤ φ y ω} := by
  intro ω hω
  have hω' : τ ≤ φ x ω := hω
  have h1 : |φ x ω - φ y ω| ≤ L * ε :=
    (hφ x y ω).trans (mul_le_mul_of_nonneg_left (le_of_lt hd) hL)
  have h2 : φ x ω - φ y ω ≤ L * ε := (le_abs_self _).trans h1
  have : τ - L * ε ≤ φ y ω := by linarith
  exact this

/-- `u ↦ ⟪u, g⟫_ℝ` is `‖g‖`-Lipschitz (Cauchy–Schwarz).  This is the concrete
form of the continuity step for the Gaussian statistic `u ↦ ⟨u, hidden⟩`. -/
theorem abs_inner_sub_le {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (u v g : X) :
    |⟪u, g⟫_ℝ - ⟪v, g⟫_ℝ| ≤ ‖u - v‖ * ‖g‖ := by
  rw [← inner_sub_left]
  exact abs_real_inner_le_norm _ _

/-- Inner-product tail transfer: for `‖g ω‖ ≤ R` and `dist v u < ε`,
`|⟪v, g ω⟫| ≥ τ + ε·R` implies `|⟪u, g ω⟫| ≥ τ`. -/
theorem inner_tail_transfer {Ω : Type*} {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] {g : Ω → X} {R τ ε : ℝ} (_hR : 0 ≤ R)
    (hg : ∀ ω, ‖g ω‖ ≤ R) {u v : X} (hd : dist v u < ε) :
    {ω : Ω | τ + ε * R ≤ |⟪v, g ω⟫_ℝ|} ⊆ {ω : Ω | τ ≤ |⟪u, g ω⟫_ℝ|} := by
  intro ω hω
  have hω' : τ + ε * R ≤ |⟪v, g ω⟫_ℝ| := hω
  have hsub : |⟪v, g ω⟫_ℝ - ⟪u, g ω⟫_ℝ| ≤ ‖v - u‖ * ‖g ω‖ :=
    abs_inner_sub_le v u (g ω)
  have hd' : ‖v - u‖ ≤ ε := by
    have := hd.le
    rwa [dist_eq_norm] at this
  have h1 : |⟪v, g ω⟫_ℝ - ⟪u, g ω⟫_ℝ| ≤ ε * R :=
    hsub.trans (mul_le_mul hd' (hg ω) (norm_nonneg _)
      ((norm_nonneg _).trans hd'))
  have h2 : |⟪v, g ω⟫_ℝ| - |⟪u, g ω⟫_ℝ| ≤ ε * R :=
    (abs_sub_abs_le_abs_sub _ _).trans h1
  have : τ ≤ |⟪u, g ω⟫_ℝ| := by linarith
  exact this

/-! ## The net concentration argument (the D.7–D.9 pattern) -/

/-- **Generic net concentration theorem** (the abstract form of the paper's
D.7–D.9 argument).  Let `μ` be a measure on `Ω` and `N` a finite `ε`-net of
`K`.  If the bad event *transfers* — `ω ∈ bad y` at `y ∈ K` implies
`ω ∈ badNet x` for a covering net point `x` — and each net point satisfies
`μ (badNet x) ≤ c`, then the uniform bad event `⋃ y ∈ K, bad y` has measure
at most `N.card • c`.  No measurability is needed: the outer measure bound
suffices for subadditivity. -/
theorem measure_iUnion_le_net {Ω X : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace X] (μ : Measure Ω) {K : Set X} {ε : ℝ}
    (N : MetricNet K ε) (badNet bad : X → Set Ω) {c : ℝ≥0∞}
    (hext : ∀ x ∈ N.carrier, ∀ y ∈ K, dist y x < ε → bad y ⊆ badNet x)
    (hbad : ∀ x ∈ N.carrier, μ (badNet x) ≤ c) :
    μ (⋃ y ∈ K, bad y) ≤ N.carrier.card • c := by
  have hsub : (⋃ y ∈ K, bad y) ⊆ ⋃ x ∈ N.carrier, badNet x := by
    intro ω hω
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hω
    obtain ⟨hyK, hbad'⟩ := Set.mem_iUnion.mp hy
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (N.covers hyK)
    obtain ⟨hxN, hxy⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr
      ⟨hxN, hext x hxN y hyK (mem_ball.mp hxy) hbad'⟩⟩
  calc μ (⋃ y ∈ K, bad y)
      ≤ μ (⋃ x ∈ N.carrier, badNet x) := measure_mono hsub
    _ ≤ N.carrier.card • c :=
        measure_biUnion_finset_le_const μ N.carrier badNet hbad

/-- Instantiation for an `L`-Lipschitz scalar statistic: pointwise level-`τ`
bad events at net points give a uniform level-`(τ + L·ε)` bound on `K`. -/
theorem measure_iUnion_lipschitz_tail_le {Ω X : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace X] (μ : Measure Ω) {K : Set X} {ε : ℝ}
    (N : MetricNet K ε) (φ : X → Ω → ℝ) {L τ : ℝ} {c : ℝ≥0∞} (hL : 0 ≤ L)
    (hφ : ∀ (x y : X) (ω : Ω), |φ x ω - φ y ω| ≤ L * dist x y)
    (hbad : ∀ x ∈ N.carrier, μ {ω | τ ≤ φ x ω} ≤ c) :
    μ (⋃ y ∈ K, {ω | τ + L * ε ≤ φ y ω}) ≤ N.carrier.card • c := by
  refine measure_iUnion_le_net μ N _ _ ?_ hbad
  intro x _ y _ hd
  have h := tail_transfer_lipschitz φ hL hφ hd (τ := τ + L * ε)
  rwa [add_sub_cancel_right] at h

/-- Instantiation for the inner-product statistic `u ↦ ⟪u, g ω⟫_ℝ` against a
pointwise norm-bounded random vector: pointwise `|⟪x, g⟫| ≥ τ` bounds at the
net points upgrade to a uniform `|⟪y, g⟫| ≥ τ + ε·R` bound over `K`.  This is
the shape of the Gaussian `⟨u, g⟩` sup bound of Appendix D. -/
theorem measure_iUnion_inner_tail_le {Ω : Type*} [MeasurableSpace Ω]
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (μ : Measure Ω) {K : Set X} {ε : ℝ} (N : MetricNet K ε)
    (g : Ω → X) {R τ : ℝ} {c : ℝ≥0∞} (hR : 0 ≤ R) (hg : ∀ ω, ‖g ω‖ ≤ R)
    (hbad : ∀ x ∈ N.carrier, μ {ω | τ ≤ |⟪x, g ω⟫_ℝ|} ≤ c) :
    μ (⋃ y ∈ K, {ω | τ + ε * R ≤ |⟪y, g ω⟫_ℝ|}) ≤ N.carrier.card • c :=
  measure_iUnion_le_net μ N _ _
    (fun _x _ _y _ hd ↦ inner_tail_transfer hR hg hd) hbad

/-! ## Predictable iteration -/

/-- The empty transcript. -/
def emptyHist {X : Type*} : Fin 0 → X := fun i ↦ i.elim0

/-- Restriction of a length-`t` transcript to its first `s ≤ t` entries. -/
def histTrunc {X : Type*} {t : ℕ} (h : Fin t → X) {s : ℕ} (hs : s ≤ t) :
    Fin s → X :=
  fun i ↦ h (Fin.castLE hs i)

theorem histTrunc_apply {X : Type*} {t s : ℕ} {hs : s ≤ t} (h : Fin t → X)
    (i : Fin s) : histTrunc h hs i = h (Fin.castLE hs i) := rfl

theorem measurable_histTrunc {X : Type*} [MeasurableSpace X] {t s : ℕ}
    (hs : s ≤ t) : Measurable fun h : Fin t → X ↦ histTrunc h hs :=
  Measurable.of_eval fun _ ↦ measurable_pi_apply _

/-- Truncating at the full length is the identity (up to the bound proof). -/
theorem histTrunc_self {X : Type*} {t : ℕ} (h : Fin t → X) (hs : t ≤ t) :
    histTrunc h hs = h := by
  funext i
  show h (Fin.castLE hs i) = h i
  rfl

/-- Truncating the empty transcript gives the empty transcript. -/
theorem histTrunc_empty {X : Type*} (hs : 0 ≤ 0) :
    histTrunc (emptyHist : Fin 0 → X) hs = emptyHist :=
  funext fun i ↦ i.elim0

/-- Appending the new draw `x` to a transcript `h`, bundled as a map on
`(h, x) : (Fin t → X) × X`. -/
def snocAppend {X : Type*} {t : ℕ} : (Fin t → X) × X → Fin (t + 1) → X :=
  fun p ↦ Fin.snoc p.1 p.2

theorem snocAppend_apply {X : Type*} {t : ℕ} (p : (Fin t → X) × X) :
    snocAppend p = Fin.snoc p.1 p.2 := rfl

/-- The first `s` entries of `Fin.snoc h x` are those of `h`. -/
theorem histTrunc_snoc {X : Type*} {t s : ℕ} (h : Fin t → X) (x : X)
    (hs : s ≤ t) (hs' : s ≤ t + 1) :
    histTrunc (Fin.snoc h x) hs' = histTrunc h hs := by
  funext i
  show snocAppend (h, x) (Fin.castLE hs' i) = h (Fin.castLE hs i)
  rw [snocAppend_apply,
    show Fin.castLE hs' i = (Fin.castLE hs i).castSucc from Fin.ext (by simp),
    Fin.snoc_castSucc]

/-- Appending then truncating to the first `t` entries recovers `h`. -/
theorem histTrunc_snoc_self {X : Type*} {t : ℕ} (h : Fin t → X) (x : X)
    (hs : t ≤ t + 1) : histTrunc (Fin.snoc h x) hs = h := by
  rw [histTrunc_snoc h x (Nat.le_refl t) hs, histTrunc_self h _]

/-- `snocAppend` is measurable: it is the evaluation-wise map appending the
new draw to the transcript. -/
theorem measurable_snocAppend {X : Type*} [MeasurableSpace X] (t : ℕ) :
    Measurable (snocAppend (X := X) (t := t)) := by
  refine Measurable.of_eval fun j ↦ ?_
  induction j using Fin.lastCases with
  | last =>
      have h : (fun p : (Fin t → X) × X ↦ snocAppend p (Fin.last t)) =
          Prod.snd := funext fun _ ↦ Fin.snoc_last ..
      rw [h]
      exact measurable_snd
  | cast j' =>
      have h : (fun p : (Fin t → X) × X ↦ snocAppend p (Fin.castSucc j')) =
          fun p ↦ p.1 j' := funext fun _ ↦ Fin.snoc_castSucc ..
      rw [h]
      exact (measurable_pi_apply j').comp measurable_fst

section Predictable

/-- A **predictable step family** on `X`: the law of the `t`-th draw is the
Markov kernel `step t` evaluated on the length-`t` transcript — step `t`
depends only on times `< t`.  This is the discrete-time "predictable"
conditioning structure used by the paper's adaptive Gaussian chain. -/
structure PredictableSteps (X : Type*) [MeasurableSpace X] where
  /-- The step kernel: the law of `x_t` given the transcript `h : Fin t → X`. -/
  step : (t : ℕ) → Kernel (Fin t → X) X
  /-- Each step law is a Markov kernel. -/
  step_markov : ∀ t, IsMarkovKernel (step t)

namespace PredictableSteps

variable {X : Type*} [MeasurableSpace X]

instance step_isMarkov (P : PredictableSteps X) (t : ℕ) :
    IsMarkovKernel (P.step t) := P.step_markov t

/-- Joint trajectory law, packaged with its `SFinite` certificate so that the
`⊗ₘ` instance arguments resolve inside the recursion. -/
private def jointLawAux (P : PredictableSteps X) :
    (t : ℕ) → {μ : Measure (Fin t → X) // SFinite μ}
  | 0 => ⟨Measure.dirac emptyHist, inferInstance⟩
  | t + 1 =>
      letI := (jointLawAux P t).2
      haveI := P.step_markov t
      ⟨((jointLawAux P t).1 ⊗ₘ P.step t).map snocAppend, inferInstance⟩

/-- The joint law of the length-`t` transcript of a predictable chain:
`jointLaw 0` is the point mass at the empty transcript and
`jointLaw (t+1)` pushes `(jointLaw t) ⊗ₘ (step t)` forward by `snocAppend`. -/
def jointLaw (P : PredictableSteps X) (t : ℕ) : Measure (Fin t → X) :=
  (P.jointLawAux t).1

instance jointLaw_sfinite (P : PredictableSteps X) (t : ℕ) :
    SFinite (P.jointLaw t) :=
  (P.jointLawAux t).2

instance jointLaw_isProbability (P : PredictableSteps X) (t : ℕ) :
    IsProbabilityMeasure (P.jointLaw t) := by
  unfold jointLaw
  induction t with
  | zero =>
      exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac emptyHist))
  | succ t ih =>
      have : SFinite (P.jointLawAux t).1 := (P.jointLawAux t).2
      have := P.step_markov t
      have := ih
      show IsProbabilityMeasure
        (((P.jointLawAux t).1 ⊗ₘ P.step t).map snocAppend)
      infer_instance

theorem jointLaw_zero (P : PredictableSteps X) :
    P.jointLaw 0 = Measure.dirac emptyHist := rfl

theorem jointLaw_succ (P : PredictableSteps X) (t : ℕ) :
    P.jointLaw (t + 1) =
      (P.jointLaw t ⊗ₘ P.step t).map snocAppend := rfl

/-- Adaptedness/consistency: the `t`-truncation of `jointLaw (t+1)` is
`jointLaw t` — the transcript marginal is preserved. -/
theorem jointLaw_map_histTrunc (P : PredictableSteps X) (t : ℕ) :
    (P.jointLaw (t + 1)).map (fun h : Fin (t + 1) → X ↦
        histTrunc h (Nat.le_succ t)) = P.jointLaw t := by
  have := P.step_markov t
  rw [jointLaw_succ, Measure.map_map (measurable_histTrunc _)
    (measurable_snocAppend t)]
  have hcomp : (fun h : Fin (t + 1) → X ↦ histTrunc h (Nat.le_succ t)) ∘
      snocAppend = Prod.fst := by
    funext p
    exact histTrunc_snoc_self p.1 p.2 (Nat.le_succ t)
  rw [hcomp]
  show (P.jointLaw t ⊗ₘ P.step t).fst = P.jointLaw t
  exact Measure.fst_compProd _ _

/-- The i.i.d. predictable chain: every step is `Kernel.const μ`. -/
def iid (μ : Measure X) [IsProbabilityMeasure μ] : PredictableSteps X where
  step _ := Kernel.const _ μ
  step_markov _ := inferInstance

/-- The joint law of the i.i.d. chain is the product measure — the
predictable-iteration construction recovers the independent sequence. -/
theorem jointLaw_iid (μ : Measure X) [IsProbabilityMeasure μ] (t : ℕ) :
    (PredictableSteps.iid μ).jointLaw t = Measure.pi fun _ : Fin t ↦ μ := by
  induction t with
  | zero =>
      rw [jointLaw_zero]
      exact (Measure.pi_of_empty (fun _ : Fin 0 ↦ μ) emptyHist).symm
  | succ t ih =>
      rw [jointLaw_succ,
        show (PredictableSteps.iid μ).step t = Kernel.const _ μ from rfl,
        Measure.compProd_const, ih]
      have hmp := measurePreserving_piFinSuccAbove
        (fun _ : Fin (t + 1) ↦ μ) (Fin.last t)
      have hsymm : snocAppend (t := t) =
          ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ X)
            (Fin.last t)).symm ∘ Prod.swap := by
        funext p
        rcases p with ⟨h, x⟩
        funext j
        show snocAppend (h, x) j =
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ X)
            (Fin.last t)).symm (x, h) j
        simp [snocAppend, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.snocEquiv_apply]
      rw [hsymm,
        ← Measure.map_map
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ X)
            (Fin.last t)).symm.measurable measurable_swap,
        Measure.prod_swap]
      exact (MeasurePreserving.symm _ hmp).map_eq

end PredictableSteps

open PredictableSteps

/-- `GoodHist φ h`: every truncation of the length-`t` transcript `h`
satisfies the corresponding invariant `φ s` — the trajectory-wide invariant
propagated by the predictable induction.  The index is a `Fin (t+1)` so that
measurability is a finite `⋂`. -/
def GoodHist {X : Type*} (φ : (t : ℕ) → (Fin t → X) → Prop) {t : ℕ}
    (h : Fin t → X) : Prop :=
  ∀ s : Fin (t + 1), φ s.val (histTrunc h (Nat.lt_succ_iff.mp s.isLt))

theorem measurableSet_goodHist {X : Type*} [MeasurableSpace X]
    {φ : (t : ℕ) → (Fin t → X) → Prop}
    (hφ : ∀ t, MeasurableSet {h : Fin t → X | φ t h}) {t : ℕ} :
    MeasurableSet {h : Fin t → X | GoodHist φ h} := by
  have hset : {h : Fin t → X | GoodHist φ h} =
      ⋂ s : Fin (t + 1), (fun h : Fin t → X ↦
        histTrunc h (Nat.lt_succ_iff.mp s.isLt)) ⁻¹' {h' | φ s.val h'} := by
    ext h
    simp only [Set.mem_iInter, Set.mem_preimage]
    exact Iff.rfl
  rw [hset]
  exact MeasurableSet.iInter fun s ↦
    (hφ s.val).preimage (measurable_histTrunc _)

/-- A good transcript extended by a good step stays good, and conversely. -/
theorem goodHist_snoc {X : Type*} {φ : (t : ℕ) → (Fin t → X) → Prop} {t : ℕ}
    (h : Fin t → X) (x : X) :
    GoodHist φ (Fin.snoc h x) ↔
      GoodHist φ h ∧ φ (t + 1) (Fin.snoc h x) := by
  constructor
  · intro H
    refine ⟨fun s ↦ ?_, ?_⟩
    · have hH := H (Fin.castSucc s)
      rw [histTrunc_snoc h x (Nat.lt_succ_iff.mp s.isLt) _] at hH
      exact hH
    · have hH := H (Fin.last (t + 1))
      rwa [histTrunc_self _ _] at hH
  · rintro ⟨H, Hx⟩ s
    induction s using Fin.lastCases with
    | last =>
        rw [histTrunc_self _ _]
        exact Hx
    | cast s' =>
        rw [histTrunc_snoc h x (Nat.lt_succ_iff.mp s'.isLt) _]
        exact H s'

/-- **Predictable induction** (propagation of a per-step invariant to the
joint trajectory law).  If `φ 0` holds at the empty transcript and every
step kernel preserves `φ` a.e. on good histories, then a.e. length-`t`
transcript under `jointLaw` satisfies `GoodHist φ`.  This is the inductive
half of the Lemma D.1 density-invariant argument. -/
theorem ae_goodHist_jointLaw {X : Type*} [MeasurableSpace X]
    (P : PredictableSteps X) {φ : (t : ℕ) → (Fin t → X) → Prop}
    (hφ : ∀ t, MeasurableSet {h : Fin t → X | φ t h})
    (h0 : φ 0 emptyHist)
    (hstep : ∀ (t : ℕ) (h : Fin t → X), GoodHist φ h →
      ∀ᵐ x ∂(P.step t h), φ (t + 1) (Fin.snoc h x)) :
    ∀ t, ∀ᵐ h ∂(P.jointLaw t), GoodHist φ h := by
  intro t
  induction t with
  | zero =>
      rw [jointLaw_zero, ae_dirac_iff (measurableSet_goodHist hφ)]
      rintro ⟨i, hi⟩
      have : i = 0 := Nat.lt_one_iff.mp hi
      subst this
      exact h0
  | succ t ih =>
      have := P.step_markov t
      rw [jointLaw_succ,
        ae_map_iff (measurable_snocAppend t).aemeasurable
          (measurableSet_goodHist hφ)]
      have hS : MeasurableSet {p : (Fin t → X) × X |
          GoodHist φ (snocAppend p)} := by
        have hset : {p : (Fin t → X) × X | GoodHist φ (snocAppend p)} =
            {p | GoodHist φ p.1} ∩ {p | φ (t + 1) (snocAppend p)} := by
          ext p
          show GoodHist φ (Fin.snoc p.1 p.2) ↔
            GoodHist φ p.1 ∧ φ (t + 1) (Fin.snoc p.1 p.2)
          exact goodHist_snoc _ _
        rw [hset]
        exact ((measurableSet_goodHist hφ).preimage measurable_fst).inter
          ((hφ (t + 1)).preimage (measurable_snocAppend t))
      rw [Measure.ae_compProd_iff hS]
      filter_upwards [ih] with h hh
      filter_upwards [hstep t h hh] with x hx
      exact (goodHist_snoc h x).mpr ⟨hh, hx⟩

/-- The terminal-step predicate alone holds a.e. under the joint law. -/
theorem ae_last_jointLaw {X : Type*} [MeasurableSpace X]
    (P : PredictableSteps X) {φ : (t : ℕ) → (Fin t → X) → Prop}
    (hφ : ∀ t, MeasurableSet {h : Fin t → X | φ t h})
    (h0 : φ 0 emptyHist)
    (hstep : ∀ (t : ℕ) (h : Fin t → X), GoodHist φ h →
      ∀ᵐ x ∂(P.step t h), φ (t + 1) (Fin.snoc h x)) (t : ℕ) :
    ∀ᵐ h ∂(P.jointLaw t), φ t h := by
  filter_upwards [ae_goodHist_jointLaw P hφ h0 hstep t] with h H
  have hH := H ⟨t, Nat.lt_succ_self t⟩
  rwa [histTrunc_self h _] at hH

/-- Unguarded variant: if every step satisfies `φ` a.e. on *every* history
(no goodness guard needed), the last coordinate satisfies `φ` a.e. -/
theorem ae_jointLaw_last_step {X : Type*} [MeasurableSpace X]
    (P : PredictableSteps X) {φ : (t : ℕ) → (Fin t → X) → Prop}
    (hφ : ∀ t, MeasurableSet {h : Fin t → X | φ t h})
    (hstep : ∀ (t : ℕ) (h : Fin t → X),
      ∀ᵐ x ∂(P.step t h), φ (t + 1) (Fin.snoc h x)) (t : ℕ) :
    ∀ᵐ h ∂(P.jointLaw (t + 1)), φ (t + 1) h := by
  have := P.step_markov t
  rw [jointLaw_succ, ae_map_iff (measurable_snocAppend t).aemeasurable
    (hφ (t + 1))]
  have hS : MeasurableSet {p : (Fin t → X) × X | φ (t + 1) (snocAppend p)} := by
    have hset : {p : (Fin t → X) × X | φ (t + 1) (snocAppend p)} =
        snocAppend ⁻¹' {h : Fin (t + 1) → X | φ (t + 1) h} := rfl
    rw [hset]
    exact (hφ (t + 1)).preimage (measurable_snocAppend t)
  rw [Measure.ae_compProd_iff hS]
  exact Filter.Eventually.of_forall fun h ↦ hstep t h

end Predictable

/-! ## The adaptive Gaussian chain and its invariant interface -/

section GaussianAdaptive

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- **Adaptive Gaussian step data.**  At time `t` the transcript `h` of
hidden Gaussian draws determines a continuous linear map `exposed t h` (the
linear functionals of the hidden state that the algorithm has exposed so
far) and an observed value `obs t h`.  The next hidden state is distributed
as the conditional Gaussian law `gaussCondKernel (exposed t h) (obs t h)` —
standard Gaussian on `ker (exposed t h)` shifted by the Moore–Penrose lift —
which is the per-step "hidden Gaussian stays Gaussian" content of Lemma D.1
(`stdGaussian_map_prodMk_compProd`).

The field `step_measurable` records, precisely, the regularity requirement
that the conditional law is measurable in the transcript. -/
structure AdaptiveGaussianSteps (E F : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
    [BorelSpace E] [MeasurableSpace F] [BorelSpace F] where
  /-- The linear map exposed by the algorithm given the transcript. -/
  exposed : (t : ℕ) → (Fin t → E) → (E →L[ℝ] F)
  /-- The observed value of `exposed` given the transcript. -/
  obs : (t : ℕ) → (Fin t → E) → F
  /-- The conditional Gaussian law is measurable in the transcript. -/
  step_measurable : ∀ t, Measurable fun h : Fin t → E ↦
      gaussCondKernel (exposed t h) (obs t h)

/-- The predictable step family generated by an adaptive Gaussian chain. -/
noncomputable def AdaptiveGaussianSteps.predictableSteps
    (D : AdaptiveGaussianSteps E F) : PredictableSteps E where
  step t := ⟨fun h ↦ gaussCondKernel (D.exposed t h) (D.obs t h),
    D.step_measurable t⟩
  step_markov t := ⟨fun h ↦ by
    show IsProbabilityMeasure
      (gaussCondKernel (D.exposed t h) (D.obs t h))
    infer_instance⟩

theorem AdaptiveGaussianSteps.predictableSteps_apply
    (D : AdaptiveGaussianSteps E F) (t : ℕ) (h : Fin t → E) :
    D.predictableSteps.step t h =
      gaussCondKernel (D.exposed t h) (D.obs t h) :=
  rfl

/-- **Input interface for the adaptive Gaussian density invariant**
(Lemma D.1): Gaussian step data plus the per-step transcript invariant.
`step_ae` is the remaining analytic input — on every good transcript the
next conditional-Gaussian draw preserves the invariant almost surely. -/
structure GaussianInvariantInput (E F : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E]
    [BorelSpace E] [MeasurableSpace F] [BorelSpace F] where
  steps : AdaptiveGaussianSteps E F
  /-- The step-`t` transcript predicate (the "density invariant" event). -/
  φ : (t : ℕ) → (Fin t → E) → Prop
  φ_measurable : ∀ t, MeasurableSet {h : Fin t → E | φ t h}
  /-- The invariant at the empty transcript. -/
  base : φ 0 emptyHist
  /-- Preservation of the invariant by one conditional Gaussian step on any
  good transcript (the deep Lemma-D.1 input, stated precisely). -/
  step_ae : ∀ (t : ℕ) (h : Fin t → E), GoodHist φ h →
    ∀ᵐ x ∂(gaussCondKernel (steps.exposed t h) (steps.obs t h)),
      φ (t + 1) (Fin.snoc h x)

/-- **The adaptive Gaussian density invariant**: under
`GaussianInvariantInput`, the joint trajectory law at every time satisfies
the whole history invariant almost surely — the predictable-iteration half
of Lemma D.1 → Theorem 4.1. -/
theorem GaussianInvariantInput.ae_jointLaw (G : GaussianInvariantInput E F)
    (t : ℕ) :
    ∀ᵐ h ∂(G.steps.predictableSteps.jointLaw t), GoodHist G.φ h :=
  ae_goodHist_jointLaw _ G.φ_measurable G.base (fun t h hh ↦ by
    rw [AdaptiveGaussianSteps.predictableSteps_apply]
    exact G.step_ae t h hh) t

/-- The terminal invariant alone holds a.e. under the joint law. -/
theorem GaussianInvariantInput.ae_terminal (G : GaussianInvariantInput E F)
    (t : ℕ) :
    ∀ᵐ h ∂(G.steps.predictableSteps.jointLaw t), G.φ t h :=
  ae_last_jointLaw _ G.φ_measurable G.base (fun t h hh ↦ by
    rw [AdaptiveGaussianSteps.predictableSteps_apply]
    exact G.step_ae t h hh) t

end GaussianAdaptive

end

end Komlos
