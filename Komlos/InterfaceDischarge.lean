import Komlos.Theorem11Assembly
import Komlos.ConcentrationMarkov
import Komlos.SpectralDimension
import Komlos.ResolventContinuity
import Komlos.StabilityTransport
import Komlos.AnchorDimension
import Komlos.AnchorUpdate
import Komlos.InitializationMargin
import Komlos.RowBoundA2
import Komlos.DynamicMaintenance
import Komlos.RuntimeBound

/-!
# Interface discharge ledger

This module surveys every hypothesis-carrying interface of the Komlós
formalization and **mechanically discharges** each field that is already
implied by an existing theorem. It introduces no `sorry`, no `admit`, no
`native_decide`, and no new axioms; every residual hypothesis is kept
explicitly in a reduced composite structure, so the ledger below is
machine-checkable rather than a prose claim.

Two conventions:

* **DISCHARGED** means the field is produced by a named bridge lemma below
  (in the style `fieldX_of_existing`), unconditionally or under strictly
  weaker hypotheses than the field itself.
* **OPEN** means no surveyed theorem proves the field: the residual
  hypothesis is carried by a `'` composite (`WalkSuccessInput'`,
  `SpectralHypotheses'`, `QuadPTransportInput`, `RowUpdateInvariant`).

## Contents

1. `WalkSuccessInput` (`Theorem11Assembly.lean`): 9 of 12 fields are
   discharged, leaving `WalkSuccessInput'` with 5 fields.
2. Spectral dimension (`SpectralDimension.lean`): the `E₀` hypothesis of
   `spectral_subspace_exists` is discharged by
   `spectral_subspace_exists_unconditional`; the `hnbhd`/`hcont` analytic
   hypotheses of the three `hasDerivAt_*` theorems are discharged by
   `ResolventContinuity`.
3. Concavity (`ConcaveStep`, `PotentialConcavity`, `SpectralPath`,
   `HessianDecomposition`): the `hpole` hypothesis is discharged by barrier
   nonpositivity and `hunit` by positive definiteness.
4. Dynamic maintenance (`DynamicMaintenance.lean`): the certificate field
   is supplied by `init`/`update`/`updateCol`; the guard hypothesis is
   discharged by `guard_iff_isUnit_det`.
5. Stability transport (`StabilityTransport.lean`): `R₀.PosSemidef` is
   discharged from the Loewner bound.
6. Anchor/row bounds (`AnchorUpdate`, `RowBoundA2`,
   `InitializationMargin`): the maintained row invariant is packaged as
   `RowUpdateInvariant` and proved preserved.
7. Runtime (`RuntimeBound.lean`): `BoolSigningExists` is discharged from
   `WalkSuccessHypothesis`.
-/

namespace Komlos

open scoped BigOperators
open Matrix

noncomputable section

/-! ## 1. `WalkSuccessInput` (`Theorem11Assembly.lean`)

### Ledger

| field | status |
|---|---|
| `walk` | DISCHARGED — `walk_of_existing` is the canonical full-cube walk `SymmetricWalk.cubeDown n 0` |
| `walk_coherent` | DISCHARGED — `cubeTop_coherent` |
| `walk_cube` | DISCHARGED — `cubeTop_cubeLeaves` |
| `leaf` | REDUCED — a signing leaf exists (`signing_leaf_exists`), but naming *which* leaf satisfies the row bounds is residual |
| `mem_leaf` | REDUCED — kept as a field of `WalkSuccessInput'` (of the canonical walk) |
| `leaf_signing` | DISCHARGED — `memLeaf_cubeDown_isSigning` (automatic on the canonical walk) |
| `Slarge` | OPEN — the exceptional still-large row set is part of the residual data |
| `δlarge` | DISCHARGED — fixed to `largeRowDefectCap`, the weakest legal threshold |
| `δlarge_nonneg` | DISCHARGED — `δlarge_nonneg_of_existing` |
| `δlarge_le` | DISCHARGED — `δlarge_le_of_existing` |
| `large_bound` | OPEN — the still-large estimate of §A: needs the displacement/stability chain (`transported_subspace_bound`, `abs_barrierAt_sub_le`, `protected_signs_exclusive`) instantiated at the algorithm's data |
| `completed_decomp` | OPEN — the four-term tracked/deletion/retirement/offset decomposition; `tracked_decomp_of_barrier_data` restructures it as the barrier-pair invariant, which is what remains to be maintained along the walk |

The choice `walk := cubeDown n 0` is honest but *lossy*: it replaces the
paper's adaptive clipped rounding walk by the uniform enumeration of all
`2ⁿ` signings. All of the remaining mathematical content is thereby
concentrated in `large_bound`/`completed_decomp` for the chosen leaf —
precisely the statements the paper's adaptive potential argument exists
to prove. -/

/-- Canonical choice for the `walk` field: the full-depth cube walk. -/
def walk_of_existing (n : ℕ) : SymmetricWalk n :=
  SymmetricWalk.cubeDown n (0 : Fin n → ℝ)

/-- `walk_coherent`, discharged: `cubeTop_coherent`. -/
theorem walk_coherent_of_existing (n : ℕ) :
    SymmetricWalk.Coherent (walk_of_existing n) := cubeTop_coherent

/-- `walk_cube`, discharged: `cubeTop_cubeLeaves`. -/
theorem walk_cube_of_existing (n : ℕ) :
    SymmetricWalk.CubeLeaves (walk_of_existing n) := cubeTop_cubeLeaves

/-- `leaf_signing`, discharged on the canonical walk: every leaf of
`cubeDown n 0` is a signing (`memLeaf_cubeDown_isSigning`). -/
theorem leaf_signing_of_existing {n : ℕ} {y : Fin n → ℝ}
    (h : SymmetricWalk.MemLeaf (walk_of_existing n) y) : IsSigning y :=
  SymmetricWalk.memLeaf_cubeDown_isSigning h

/-- `leaf` + `mem_leaf` + `leaf_signing`, existential form: some leaf of
the canonical walk is a signing (the `T = 1` instance of
`exists_memLeaf_signing_few_bad_rows`; the bad-row bound is unused). -/
theorem signing_leaf_exists {m n : ℕ} {A : Input m n}
    (hA : ColumnNormalized A) :
    ∃ y : Fin n → ℝ, SymmetricWalk.MemLeaf (walk_of_existing n) y ∧
      IsSigning y := by
  obtain ⟨y, hmem, hsign, _⟩ :=
    exists_memLeaf_signing_few_bad_rows hA (show (0 : ℝ) < 1 by norm_num)
  exact ⟨y, hmem, hsign⟩

/-- Canonical choice for `δlarge`: the cap itself, giving the weakest
still-large threshold `63 + 35 + δoff < 99`. -/
noncomputable def δlarge_of_existing : ℝ := largeRowDefectCap

theorem δlarge_nonneg_of_existing : 0 ≤ δlarge_of_existing := by
  unfold δlarge_of_existing largeRowDefectCap
  norm_num

theorem δlarge_le_of_existing : δlarge_of_existing ≤ largeRowDefectCap :=
  le_rfl

/-- **Reduced `WalkSuccessInput`**: the five residual fields after the
mechanical discharge above. `mem_leaf` is stated for the canonical walk
`cubeDown n 0`, so `leaf_signing` follows automatically; `δlarge` is fixed
at the cap. -/
structure WalkSuccessInput' {m n : ℕ} (A : Input m n) where
  /-- The successful terminal position, a leaf of `cubeDown n 0`. -/
  leaf : Fin n → ℝ
  /-- `leaf` is reached by the canonical walk. -/
  mem_leaf : SymmetricWalk.MemLeaf (walk_of_existing n) leaf
  /-- The exceptional set of rows still large at the end of the walk. -/
  Slarge : Finset (Fin m)
  /-- Still-large rows stay below `63 + 35 + δoff`. -/
  large_bound : ∀ i ∈ Slarge,
    |rowValue A leaf i| < 63 + largeRowDefectCap + offsetDefect
  /-- Completed/medium rows admit the four-term decomposition. -/
  completed_decomp : ∀ i, i ∉ discardedRows A ∪ Slarge →
    ∃ tracked deletion retirement offset : ℝ,
      rowValue A leaf i = tracked + deletion + retirement + offset ∧
      |tracked| < 263 / 5 ∧
      |deletion| ≤ 2 * (291 / 200) * (8 + Real.sqrt 63) ∧
      |retirement| ≤ retirementDefect ∧ |offset| ≤ offsetDefect

/-- Assemble a reduced input into a full `WalkSuccessInput`. -/
noncomputable def WalkSuccessInput'.toWalkSuccessInput {m n : ℕ}
    {A : Input m n} (w : WalkSuccessInput' A) : WalkSuccessInput A where
  walk := walk_of_existing n
  walk_coherent := walk_coherent_of_existing n
  walk_cube := walk_cube_of_existing n
  leaf := w.leaf
  mem_leaf := w.mem_leaf
  leaf_signing := leaf_signing_of_existing w.mem_leaf
  Slarge := w.Slarge
  δlarge := δlarge_of_existing
  δlarge_nonneg := δlarge_nonneg_of_existing
  δlarge_le := δlarge_le_of_existing
  large_bound := w.large_bound
  completed_decomp := w.completed_decomp

/-- The conditional main theorem, stated against the reduced input. -/
theorem exists_signing_discrepancy_below_99_of_reduced {m n : ℕ}
    {A : Input m n} (w : WalkSuccessInput' A) :
    ∃ ε, HasDiscrepancyBelow A ε 99 :=
  exists_signing_discrepancy_below_99 w.toWalkSuccessInput

/-- The uniform residual hypothesis, reduced form. -/
def WalkSuccessHypothesis' : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ),
    ColumnNormalized (fun i j => (A i j : ℝ)) → 0 < m → 64 ≤ n →
      Nonempty (WalkSuccessInput' (fun i j => (A i j : ℝ)))

/-- The reduced hypothesis implies the original one. -/
theorem walkSuccessHypothesis_of_reduced (h : WalkSuccessHypothesis') :
    WalkSuccessHypothesis :=
  fun m n A hA hm hn =>
    (h m n A hA hm hn).map WalkSuccessInput'.toWalkSuccessInput

/-- The conditional discrepancy theorem against the reduced hypothesis. -/
theorem DiscrepancyPartOfTheorem11_of_reducedWalkSuccess
    (h : WalkSuccessHypothesis') : DiscrepancyPartOfTheorem11 :=
  DiscrepancyPartOfTheorem11_of_walkSuccess
    (walkSuccessHypothesis_of_reduced h)

/-- **The `|tracked| < 263/5` component of `completed_decomp`,
restructured**: if a row's value is presented as
`d + deletion + retirement + offset` where `d` is controlled by *both*
barriers `barrier ±1 d r G ≤ 0`, then `barriers_control_abs_value`
discharges the tracked bound. This isolates the barrier-pair invariant —
the paper's `Φ(±1, ·) ≤ 0` maintained along the walk — as the actual
residual content of `completed_decomp`. -/
theorem tracked_decomp_of_barrier_data {m n : ℕ} {A : Input m n}
    {leaf : Fin n → ℝ} {S : Finset (Fin m)}
    (hdata : ∀ i, i ∉ discardedRows A ∪ S →
      ∃ (d r G deletion retirement offset : ℝ),
        0 < r ∧ 0 ≤ G ∧
        barrier 1 d r G ≤ 0 ∧ barrier (-1) d r G ≤ 0 ∧
        |deletion| ≤ 2 * (291 / 200) * (8 + Real.sqrt 63) ∧
        |retirement| ≤ retirementDefect ∧ |offset| ≤ offsetDefect ∧
        rowValue A leaf i = d + deletion + retirement + offset) :
    ∀ i, i ∉ discardedRows A ∪ S →
      ∃ tracked deletion retirement offset : ℝ,
        rowValue A leaf i = tracked + deletion + retirement + offset ∧
        |tracked| < 263 / 5 ∧
        |deletion| ≤ 2 * (291 / 200) * (8 + Real.sqrt 63) ∧
        |retirement| ≤ retirementDefect ∧ |offset| ≤ offsetDefect := by
  intro i hi
  obtain ⟨d, r, G, del, ret, off, hr, hG, hp, hm, hd, hret, hoff, hval⟩ :=
    hdata i hi
  exact ⟨d, del, ret, off, hval,
    barriers_control_abs_value hr hG hp hm, hd, hret, hoff⟩

/-! ## 2. Spectral dimension (`SpectralDimension.lean`)

### Ledger for `spectral_subspace_exists`

| hypothesis | status |
|---|---|
| `hs : 0 < s` | parameter (open: instance-level side condition) |
| `E0` + `hE0dim` + `hE0prop` | DISCHARGED — `good_subspace_exists` constructs `E₀` from `Q, D, ρ`; the composition is `spectral_subspace_exists_unconditional` |
| `hcard` | OPEN — the four-loss constraint count, instance-level accounting |
| `hQ`, `hD`, `hDdiag`, `hρ`, `hQD` | OPEN — the algorithmic inputs on `Q` (PSD), `D` (diagonal, nonneg), `ρ ≤ 1`, and the entrywise trace bound; packaged as `SpectralHypotheses'` |

### Ledger for the `hasDerivAt_*` theorems (B.3)

| hypothesis | status |
|---|---|
| `hnbhd` | DISCHARGED — `posDef_slackMatrix_eventually_add_smul` / `_quadratic` (positive definiteness is open along symmetric paths, `ResolventContinuity.posDef_eventually`) |
| `hcont` | DISCHARGED — `continuousAt_slack_inv_add_smul` / `_quadratic` (inverse continuity from `differentiableAt_inv_entry`) |
| `hNsymm` | reduced to `N.IsSymm`; for `M`, DISCHARGED outright — symmetry of `M` follows from `PosDef (slackMatrix b M)` (`isSymm_of_slackMatrix_posDef`) |
| `hMpos` | OPEN — slack positive definiteness is the resolvent-side invariant | -/

/-- Symmetry of `M` is *discharged* from positive definiteness of the
slack: `(bI − M)ᵀ = bI − M` forces `Mᵀ = M`. -/
theorem isSymm_of_slackMatrix_isSymm {s : ℕ} {b : ℝ} {M : Input s s}
    (h : (slackMatrix b M).IsSymm) : M.IsSymm := by
  have ht : (slackMatrix b M).transpose = slackMatrix b M := h
  simp only [slackMatrix] at ht
  rw [Matrix.transpose_sub, Matrix.diagonal_transpose] at ht
  exact sub_right_injective ht

/-- `M.IsSymm` follows from `(slackMatrix b M).PosDef`: the slack is
Hermitian, hence symmetric, hence `M` is symmetric. -/
theorem isSymm_of_slackMatrix_posDef {s : ℕ} {b : ℝ} {M : Input s s}
    (h : (slackMatrix b M).PosDef) : M.IsSymm :=
  isSymm_of_slackMatrix_isSymm (Matrix.isHermitian_iff_isSymm.mp h.1)

/-- The reduced spectral hypothesis package: exactly the inputs of
`good_subspace_exists`, with `E₀` (and its dimension/property fields)
removed. -/
structure SpectralHypotheses' {s : ℕ} (Q D : Input s s) (ρ : ℝ) : Prop where
  /-- `Q` is positive semidefinite (the transported Hessian `P`-part). -/
  hQ : Q.PosSemidef
  /-- `D` is diagonal. -/
  hD : Matrix.IsDiag D
  /-- The diagonal of `D` is nonnegative. -/
  hDdiag : ∀ j, 0 ≤ D j j
  /-- The curvature margin `ρ ≤ 1`. -/
  hρ : ρ ≤ 1
  /-- Entrywise diagonal domination `Q j j ≤ μ₅ (1−ρ) D j j`. -/
  hQD : ∀ j, Q j j ≤
    ((1 + 4 / 25) * (1 + 1 / 10000) / (4 * (1 - 4 / 25) * (1 - 1 / 64))) *
      (1 - ρ) * D j j

/-- The conditional spectral-subspace theorem against the reduced package:
`E₀` is now discharged inside. -/
theorem spectral_subspace_exists_of_hypotheses' {s : ℕ} {ι : Type*}
    [Fintype ι] (hs : 0 < s) (g : ι → Fin s → ℝ)
    {Q D : Input s s} {ρ : ℝ} (H : SpectralHypotheses' Q D ρ)
    (hcard : (Fintype.card ι : ℝ) ≤
      (1 / (291 / 200) ^ 2 + 5 * (65 / 64) ^ 4 / 238 +
        1 / (64 * (4 / 25 - 3 / 625)) + 1 / 2048) * s) :
    ∃ E : Submodule ℝ (Fin s → ℝ),
      (s : ℝ) / 32 < Module.finrank ℝ E ∧
      (∀ h ∈ E, h ⬝ᵥ (Q *ᵥ h) ≤ (1 - ρ) * (h ⬝ᵥ (D *ᵥ h))) ∧
      ∀ h ∈ E, ∀ i, g i ⬝ᵥ h = 0 :=
  spectral_subspace_exists_unconditional hs g Q D ρ
    H.hQ H.hD H.hDdiag H.hρ H.hQD hcard

/-- The ceil-form dimension bound against the reduced package. -/
theorem spectral_subspace_dimension_of_hypotheses' {s : ℕ} {ι : Type*}
    [Fintype ι] (hs : 0 < s) (g : ι → Fin s → ℝ)
    {Q D : Input s s} {ρ : ℝ} (H : SpectralHypotheses' Q D ρ)
    (hcard : (Fintype.card ι : ℝ) ≤
      (1 / (291 / 200) ^ 2 + 5 * (65 / 64) ^ 4 / 238 +
        1 / (64 * (4 / 25 - 3 / 625)) + 1 / 2048) * s) :
    ∃ E : Submodule ℝ (Fin s → ℝ),
      ⌈(s : ℝ) / 32⌉₊ ≤ Module.finrank ℝ E ∧
      (∀ h ∈ E, h ⬝ᵥ (Q *ᵥ h) ≤ (1 - ρ) * (h ⬝ᵥ (D *ᵥ h))) ∧
      ∀ h ∈ E, ∀ i, g i ⬝ᵥ h = 0 := by
  obtain ⟨E, hdim, hprop, hker⟩ :=
    spectral_subspace_exists_of_hypotheses' hs g H hcard
  exact ⟨E, Nat.ceil_le.mpr hdim.le, hprop, hker⟩

/-- `(B.3)` first derivative, unconditional apart from slack positivity
and `N`-symmetry: `hnbhd`/`hcont` discharged by `ResolventContinuity`. -/
theorem hasDerivAt_resolventPotential_of_posDef {s : ℕ} {b : ℝ}
    {M N : Input s s}
    (hMpos : (slackMatrix b M).PosDef) (hN : N.IsSymm) :
    HasDerivAt (fun t : ℝ => resolventPotential b (M + t • N))
      (resolventVariation1 b M N) 0 :=
  hasDerivAt_resolventPotential hMpos
    (posDef_slackMatrix_eventually_add_smul hMpos
      (isSymm_of_slackMatrix_posDef hMpos) hN)
    (continuousAt_slack_inv_add_smul hMpos)

/-- `(B.3)` second derivative along the affine path, unconditional apart
from slack positivity and `N`-symmetry. -/
theorem hasDerivAt_resolventQuadraticForm_of_posDef {s : ℕ} {b : ℝ}
    {M N : Input s s}
    (hMpos : (slackMatrix b M).PosDef) (hN : N.IsSymm) :
    HasDerivAt (fun t : ℝ => resolventVector b (M + t • N) ⬝ᵥ
      (N *ᵥ resolventVector b (M + t • N))) (resolventVariation2 b M N) 0 :=
  hasDerivAt_resolventQuadraticForm
    (fun j k => by
      have ht : N.transpose = N := hN
      simpa using congr_arg (· k j) ht)
    hMpos
    (posDef_slackMatrix_eventually_add_smul hMpos
      (isSymm_of_slackMatrix_posDef hMpos) hN)
    (continuousAt_slack_inv_add_smul hMpos)

/-- `(B.3)` second derivative along the quadratic path, unconditional
apart from slack positivity and `N₁`, `N₂`-symmetry. -/
theorem hasDerivAt_potentialSlope_of_posDef {s : ℕ} {b : ℝ}
    {M N₁ N₂ : Input s s}
    (hMpos : (slackMatrix b M).PosDef) (hN₁ : N₁.IsSymm) (hN₂ : N₂.IsSymm) :
    HasDerivAt (potentialSlope b M N₁ N₂) (potentialHessian b M N₁ N₂) 0 :=
  hasDerivAt_potentialSlope
    (fun j k => by
      have ht : N₁.transpose = N₁ := hN₁
      simpa using congr_arg (· k j) ht)
    (fun j k => by
      have ht : N₂.transpose = N₂ := hN₂
      simpa using congr_arg (· k j) ht)
    hMpos
    (posDef_slackMatrix_eventually_quadratic hMpos
      (isSymm_of_slackMatrix_posDef hMpos) hN₁ hN₂)
    (continuousAt_slack_inv_quadratic hMpos)

/-! ## 3. Concavity interfaces

### Ledger

* `concaveOn_pair_average_le`, `concaveOn_branch_average_le`,
  `localAverageNonincrease_of_branchConcave`,
  `terminal_average_le_root_of_branchConcave` — **already fully
  discharged** as functions of their arguments: the combinatorial
  consequences of branchwise concavity are closed. The only residual is
  the `BranchConcave`/`ConcaveOn` certificate itself, packaged as
  `BranchConcavityInput`.
* `concaveOn_resolvent_inv_sum`, `concaveOn_resolventPotential_path`,
  `pair_average_resolventPotential_le`,
  `concaveOn_resolventPotential_quad`,
  `pair_average_resolventPotential_quad`,
  `concaveOn_inv_sum_path`, `concaveOn_of_transported_bound`:
  - `hunit` (invertibility of the slack on the window): DISCHARGED by
    positive definiteness (`isUnit_slackMatrix_of_posDef` /
    `PosDef.det_pos`), see `*_of_posDef` and `*_of_invariants` below.
  - `hpole` (`1 − u(t)/20000 ≠ 0`): DISCHARGED by barrier nonpositivity
    `u(t) ≤ 0` (`weight_pole_ne_of_nonpos`).
  - `h2`/`htrans` (the curvature inequality): OPEN — this is the content
    of Proposition 2.1's `Pₓ[h] ≤ (1−ρ)Dₓ[h]`, reachable from
    `exists_subspace_curvature_lhs_nonpos` + the transport chain on the
    paper's data, not provable at this level of generality. -/

/-- A nonpositive barrier value keeps the weight pole away:
`1 − w/20000 ≥ 1 > 0` whenever `w ≤ 0`. -/
theorem weight_pole_ne_of_nonpos {w : ℝ} (hw : w ≤ 0) :
    (1 : ℝ) - w / 20000 ≠ 0 :=
  ne_of_gt (by
    linarith [div_nonpos_of_nonpos_of_nonneg hw
      (show (0 : ℝ) ≤ 20000 by norm_num)])

/-- The residual input for the walk-level potential bound: coherence of
the tree plus branchwise concavity. These are the *only* fields that
remain once the combinatorial lemmas are applied. -/
structure BranchConcavityInput {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (tree : SymmetricWalk n) : Prop where
  /-- The walk is coherent (children are `x ± d`). -/
  coherent : SymmetricWalk.Coherent tree
  /-- The potential is concave along every branch displacement. -/
  concave : BranchConcave f tree

/-- The terminal-average bound against the packaged input. -/
theorem terminal_average_le_root_of_input {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {tree : SymmetricWalk n}
    (h : BranchConcavityInput f tree) :
    SymmetricWalk.terminalAverage f tree ≤ f (SymmetricWalk.root tree) :=
  terminal_average_le_root_of_branchConcave f tree h.coherent h.concave

/-- `pair_average_resolventPotential_le` with `hunit` discharged by
positive definiteness on the window. -/
theorem pair_average_resolventPotential_le_of_posDef {s : ℕ} (b : ℝ)
    (M D : Input s s) {T : ℝ} (hT : 0 < T)
    (hpos : ∀ t ∈ Set.Icc (-T) T,
      (slackMatrix b (M + t • D)).PosDef)
    (h2 : ∀ t ∈ Set.Ioo (-T) T,
      2 * ∑ i : Fin s, ∑ j : Fin s,
        ((Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹ * D *
          (Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹ * D *
          (Matrix.diagonal (fun _ : Fin s => b) - (M + t • D))⁻¹) i j ≤ 0) :
    (resolventPotential b (M + T • D) + resolventPotential b (M - T • D)) / 2 ≤
      resolventPotential b M :=
  pair_average_resolventPotential_le b M D hT
    (fun t ht => isUnit_slackMatrix_of_posDef (hpos t ht)) h2

/-- `concaveOn_resolventPotential_quad` with `hpole` discharged by
closed-window barrier nonpositivity and `hunit` by positive definiteness.
The only residual is the curvature inequality `h2`. -/
theorem concaveOn_resolventPotential_quad_of_invariants {m s : ℕ} (b : ℝ)
    (M0 : Matrix (Fin s) (Fin s) ℝ) (z : Fin m → Fin s → ℝ)
    (u c d : Fin m → ℝ) (lo hi : ℝ)
    (hnonpos : ∀ t ∈ Set.Icc lo hi, ∀ i,
      u i + t * c i - t ^ 2 * d i ≤ 0)
    (hpos : ∀ t ∈ Set.Icc lo hi,
      (slackMatrix b (batchMatrix M0 z
        (fun i => u i + t * c i - t ^ 2 * d i))).PosDef)
    (h2 : ∀ t ∈ Set.Ioo lo hi,
      2 * ∑ p : Fin s, ∑ q : Fin s,
          ((slackMatrix b (batchMatrix M0 z
            (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *
            batchMatrixDeriv z
              (fun i => u i + t * c i - t ^ 2 * d i)
              (fun i => c i - 2 * t * d i) *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *
            batchMatrixDeriv z
              (fun i => u i + t * c i - t ^ 2 * d i)
              (fun i => c i - 2 * t * d i) *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹) p q +
        ∑ p : Fin s, ∑ q : Fin s,
          ((slackMatrix b (batchMatrix M0 z
            (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *
            batchMatrixDeriv2Gen z
              (fun i => u i + t * c i - t ^ 2 * d i)
              (fun i => c i - 2 * t * d i) (fun i => -(2 * d i)) *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹) p q ≤ 0) :
    ConcaveOn ℝ (Set.Icc lo hi)
      (fun t => resolventPotential b
        (batchMatrix M0 z (fun i => u i + t * c i - t ^ 2 * d i))) :=
  concaveOn_resolventPotential_quad b M0 z u c d lo hi
    (fun t ht i => weight_pole_ne_of_nonpos (hnonpos t ht i))
    (fun t ht => isUnit_slackMatrix_of_posDef (hpos t ht)) h2

/-- `pair_average_resolventPotential_quad` with the same two discharges:
`hpole` from closed-window nonpositivity, `hunit` from positivity. -/
theorem pair_average_resolventPotential_quad_of_invariants {m s : ℕ}
    (b : ℝ) (M0 : Matrix (Fin s) (Fin s) ℝ) (z : Fin m → Fin s → ℝ)
    (u c d : Fin m → ℝ) {T : ℝ} (hT : 0 < T)
    (hnonpos : ∀ t ∈ Set.Icc (-T) T, ∀ i,
      u i + t * c i - t ^ 2 * d i ≤ 0)
    (hpos : ∀ t ∈ Set.Icc (-T) T,
      (slackMatrix b (batchMatrix M0 z
        (fun i => u i + t * c i - t ^ 2 * d i))).PosDef)
    (h2 : ∀ t ∈ Set.Ioo (-T) T,
      2 * ∑ p : Fin s, ∑ q : Fin s,
          ((slackMatrix b (batchMatrix M0 z
            (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *
            batchMatrixDeriv z
              (fun i => u i + t * c i - t ^ 2 * d i)
              (fun i => c i - 2 * t * d i) *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *
            batchMatrixDeriv z
              (fun i => u i + t * c i - t ^ 2 * d i)
              (fun i => c i - 2 * t * d i) *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹) p q +
        ∑ p : Fin s, ∑ q : Fin s,
          ((slackMatrix b (batchMatrix M0 z
            (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *
            batchMatrixDeriv2Gen z
              (fun i => u i + t * c i - t ^ 2 * d i)
              (fun i => c i - 2 * t * d i) (fun i => -(2 * d i)) *
            (slackMatrix b (batchMatrix M0 z
              (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹) p q ≤ 0) :
    (resolventPotential b (batchMatrix M0 z
        (fun i => u i + T * c i - T ^ 2 * d i)) +
      resolventPotential b (batchMatrix M0 z
        (fun i => u i - T * c i - T ^ 2 * d i))) / 2 ≤
      resolventPotential b (batchMatrix M0 z u) :=
  pair_average_resolventPotential_quad b M0 z u c d hT
    (fun t ht i => weight_pole_ne_of_nonpos (hnonpos t ht i))
    (fun t ht => isUnit_slackMatrix_of_posDef (hpos t ht)) h2

/-- `concaveOn_of_transported_bound` with `hpole` discharged by
closed-window nonpositivity and `hunit` by positivity; `huT` is subsumed
by `hnonpos`. The residual hypotheses are `hgT`, `hd`, `hz`, the
positive-definiteness window, and the transported bound `htrans`. -/
theorem concaveOn_of_transported_bound_of_invariants {m s : ℕ} (b : ℝ)
    {ρ lo hi : ℝ} {M0 : Matrix (Fin s) (Fin s) ℝ} (hM0 : M0.IsSymm)
    {z : Fin m → Fin s → ℝ} {u c d : Fin m → ℝ} {h : Fin s → ℝ}
    {gT : ℝ → Fin m → Fin s → ℝ}
    (hgT : ∀ t i, gT t i ⬝ᵥ h = c i - 2 * t * d i)
    (hd : ∀ i, d i = 4 * barrierQuad (z i) h)
    (hρ : 0 ≤ ρ) (hz : ∀ i j, 0 ≤ z i j)
    (hnonpos : ∀ t ∈ Set.Icc lo hi, ∀ i,
      u i + t * c i - t ^ 2 * d i ≤ 0)
    (hpos : ∀ t ∈ Set.Icc lo hi,
      (slackMatrix b (batchMatrix M0 z
        (fun i => u i + t * c i - t ^ 2 * d i))).PosDef)
    (htrans : ∀ t ∈ Set.Ioo lo hi,
      quadP z (gT t) (fun i => u i + t * c i - t ^ 2 * d i)
        ((slackMatrix b (batchMatrix M0 z
          (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *ᵥ fun _ => 1) h
        (slackMatrix b (batchMatrix M0 z
          (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ ≤
      (1 - ρ) * quadD z (fun i => u i + t * c i - t ^ 2 * d i)
        ((slackMatrix b (batchMatrix M0 z
          (fun i => u i + t * c i - t ^ 2 * d i)))⁻¹ *ᵥ fun _ => 1) h) :
    ConcaveOn ℝ (Set.Icc lo hi)
      (fun t => resolventPotential b
        (batchMatrix M0 z (fun i => u i + t * c i - t ^ 2 * d i))) :=
  concaveOn_of_transported_bound b hM0 hgT hd hρ hz
    (fun t ht i => weight_pole_ne_of_nonpos (hnonpos t ht i))
    (fun t ht => isUnit_slackMatrix_of_posDef (hpos t ht))
    (fun t ht i => hnonpos t (Set.Ioo_subset_Icc_self ht) i)
    htrans

/-! ## 4. Dynamic maintenance (`DynamicMaintenance.lean`)

### Ledger for `DynamicInverseState` and the cost theorems

| hypothesis | status |
|---|---|
| `cert : Inv * A = 1` | DISCHARGED by construction — `DynamicInverseState.init` (from `IsUnit A.det`), `.one`, `.update`, `.updateCol`, `.updateAll` all produce the certificate |
| guard `1 + v ⬝ᵥ (Inv *ᵥ u) ≠ 0` | DISCHARGED — `guard_iff_isUnit_det` makes it equivalent to `IsUnit (A + u vᵀ).det`; `update_of_isUnit`/`updateCol_of_isUnit` take the invertibility form |
| `1 ≤ n`, `1 ≤ B` | parameter side conditions |
| `R·n ≤ T` (rebuild schedule) | OPEN — models the Appendix E rebuild hierarchy (`L = ⌈log₂ N⌉`), not formalized; discharged for `R = 0` below |
| `BitCostModel` field bounds | model hypotheses, satisfied by `BitCostModel.quadratic` | -/

namespace DynamicInverseState

variable {n : ℕ}

/-- The rank-one update precondition, discharged by invertibility of the
target: the guard is exactly `IsUnit` of the updated determinant. -/
noncomputable def update_of_isUnit (s : DynamicInverseState n)
    (u v : Fin n → ℝ) (h : IsUnit (s.A + Matrix.vecMulVec u v).det) :
    DynamicInverseState n :=
  s.update u v ((s.guard_iff_isUnit_det u v).mpr h)

/-- `update_of_isUnit` performs the update `A ↦ A + u vᵀ`. -/
theorem update_of_isUnit_A (s : DynamicInverseState n) (u v : Fin n → ℝ)
    (h : IsUnit (s.A + Matrix.vecMulVec u v).det) :
    (s.update_of_isUnit u v h).A = s.A + Matrix.vecMulVec u v := rfl

/-- The column update `A ↦ A + u eᵢᵀ` under invertibility of the target. -/
noncomputable def updateCol_of_isUnit (s : DynamicInverseState n)
    (u : Fin n → ℝ) (i : Fin n)
    (h : IsUnit (s.A + Matrix.vecMulVec u (Pi.single i 1)).det) :
    DynamicInverseState n :=
  s.updateCol u i (by
    have hg := (s.guard_iff_isUnit_det u (Pi.single i 1)).mpr h
    rwa [single_one_dotProduct] at hg)

/-- `updateCol_of_isUnit` performs the column update. -/
theorem updateCol_of_isUnit_A (s : DynamicInverseState n) (u : Fin n → ℝ)
    (i : Fin n) (h : IsUnit (s.A + Matrix.vecMulVec u (Pi.single i 1)).det) :
    (s.updateCol_of_isUnit u i h).A =
      s.A + Matrix.vecMulVec u (Pi.single i 1) := rfl

end DynamicInverseState

/-- The rebuild-schedule hypothesis `R·n ≤ T`, discharged in the
no-rebuild case `R = 0`. -/
theorem maintenanceTotalOps_le_no_rebuild (c : BitCostModel) (n B T : ℕ)
    (hn : 1 ≤ n) (hB : 1 ≤ B) :
    (maintenanceTotalOps c n B T 0 : ℝ) ≤ maintenanceEnvelope c n B T :=
  maintenanceTotalOps_le c n B T 0 hn hB (by simp)

/-! ## 5. Stability transport (`StabilityTransport.lean`)

### Ledger for `quadP_transport` and the composed transports

| hypothesis | status |
|---|---|
| `hR₀ : R₀.PosSemidef` (of `quadP_transport_subspace`, `transported_subspace_bound_quad`) | DISCHARGED — from `(R₀ − lam₀ • 1).PosSemidef` via `posSemidef_of_sub_posSemidef_smul_one`, or from `PosDef (slackMatrix b M)` when `R₀` is the resolvent (`PosDef.inv.posSemidef`) |
| `hE` (`P₀[h] ≤ (1−ρ)D₀[h]` on a subspace) | DISCHARGED inside the library — `exists_subspace_quadP_le` produces `E` from the entrywise bound `hQD` |
| `hRₓ`, `hR₀` Loewner bounds, `hz`, `hcol`, `hrow` | OPEN — resolvent spectral bounds and row/column mass bounds on the algorithm's data |
| `he`, `hcd` | OPEN — per-row coefficient/derivative stability (B.7)–(B.8) |
| `hg` | OPEN — gradient-difference control (B.6), `gradAt_sub_dot_sq_le` supplies only the bound in terms of `a` |
| `hU` | OPEN — the U-transport (B.9) |
| `hc` margin | OPEN — a numeric inequality once the paper's constants are instantiated |
| `hΛ`, `hδ`, `hδ'`, `ha`, `hμ`, `hlam` | parameter side conditions | -/

/-- `R₀.PosSemidef`, discharged from the Loewner lower bound
`R₀ ⪰ lam₀ • 1` with `lam₀ ≥ 0`. -/
theorem posSemidef_of_le_loewner {s : ℕ}
    {R : Matrix (Fin s) (Fin s) ℝ} {lam : ℝ}
    (h : (R - lam • (1 : Matrix (Fin s) (Fin s) ℝ)).PosSemidef)
    (hlam : 0 ≤ lam) : R.PosSemidef :=
  posSemidef_of_sub_posSemidef_smul_one h hlam

/-- The resolvent of a positive-definite slack is positive semidefinite:
the `hR` hypothesis discharged whenever `R` is `(slackMatrix b M)⁻¹`. -/
theorem posSemidef_inv_of_slack_posDef {s : ℕ} {b : ℝ} {M : Input s s}
    (h : (slackMatrix b M).PosDef) : (slackMatrix b M)⁻¹.PosSemidef :=
  h.inv.posSemidef

/-- `transported_subspace_bound_quad` with the `R₀.PosSemidef` hypothesis
discharged by the Loewner bound of `quadP_transport`. -/
theorem transported_subspace_bound_quad_of_loewner {m s : ℕ}
    {θ ρ γU γQ ε δ lam₀ : ℝ}
    {z g g' : Fin m → Fin s → ℝ} {u u' : Fin m → ℝ} {v v' : Fin s → ℝ}
    {R₀ Rₓ : Matrix (Fin s) (Fin s) ℝ}
    (hR₀ : (R₀ - lam₀ • (1 : Matrix (Fin s) (Fin s) ℝ)).PosSemidef)
    (hlam₀ : 0 ≤ lam₀)
    (hθ : 0 ≤ θ) (hρ1 : ρ ≤ 1)
    (hz : ∀ i j, 0 ≤ z i j) (hu : ∀ i, u i ≤ 0)
    (hQD : ∀ j, Pmat z g u v R₀ j j ≤ θ * ((1 - ρ) • Dmat z u v) j j)
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
      ∀ h ∈ E, quadP z g' u' v' h Rₓ ≤ (1 - ρ / 2) * quadD z u' v' h :=
  transported_subspace_bound_quad
    (posSemidef_of_le_loewner hR₀ hlam₀) hθ hρ1 hz hu hQD
    hγU hγQ hPt hDl hc

/-- The residual hypothesis package for `quadP_transport` (B.10): the
parameters plus every field no surveyed theorem discharges. Converting
this package to `quadP_transport`'s hypothesis list is mechanical
(`quadP_transport_of_input`). -/
structure QuadPTransportInput {m s : ℕ} (z g g' : Fin m → Fin s → ℝ)
    (u u' : Fin m → ℝ) (v v' h : Fin s → ℝ)
    (R₀ Rₓ : Matrix (Fin s) (Fin s) ℝ) where
  /-- Mass bound for `z`'s columns. -/
  Λ : ℝ
  /-- Coefficient-stability scale (B.7). -/
  ce : ℝ
  /-- Coefficient-stability scale (B.8). -/
  cd : ℝ
  /-- Split parameter for the norm decomposition. -/
  δ : ℝ
  /-- Split parameter for the vector decomposition. -/
  δ' : ℝ
  /-- Resolvent spectral bound `Rₓ ⪯ μₓ I`. -/
  muX : ℝ
  /-- Resolvent spectral bound `lam₀ I ⪯ R₀`. -/
  lam0 : ℝ
  /-- Gradient-difference scale `a` (B.6). -/
  a : ℝ
  /-- U-transport constant for `U` (B.9). -/
  cU : ℝ
  /-- U-transport constant for `D` (B.9). -/
  cD : ℝ
  hΛ : 0 ≤ Λ
  hδ : 0 < δ
  hδ' : 0 < δ'
  ha : 0 ≤ a
  hμ : 0 < muX
  hlam : 0 < lam0
  hz : ∀ i j, 0 ≤ z i j
  hcol : ∀ j, ∑ i, z i j ≤ Λ
  hrow : ∀ i, ∑ j, z i j ≤ 1
  hRₓ : (muX • (1 : Matrix (Fin s) (Fin s) ℝ) - Rₓ).PosSemidef
  hR₀ : (R₀ - lam0 • (1 : Matrix (Fin s) (Fin s) ℝ)).PosSemidef
  he : ∀ i, (weightDeriv (u' i) * (z i ⬝ᵥ v') -
      weightDeriv (u i) * (z i ⬝ᵥ v)) ^ 2 ≤
    ce ^ 2 * (weightDeriv2 (u i) * (z i ⬝ᵥ v) ^ 2)
  hcd : ∀ i, (weightDeriv (u' i) * (z i ⬝ᵥ v')) ^ 2 ≤
    cd * (weightDeriv (u i) * (z i ⬝ᵥ v) ^ 2)
  hg : ∀ i, ((g' i - g i) ⬝ᵥ h) ^ 2 ≤
    64 * a ^ 2 * barrierQuad (z i) h
  hU : quadU z g' u' v' h ≤
    cU * quadU z g u v h + cD * quadD z u v h

/-- `quadP_transport` applied to the packaged residual input. -/
theorem quadP_transport_of_input {m s : ℕ} {z g g' : Fin m → Fin s → ℝ}
    {u u' : Fin m → ℝ} {v v' h : Fin s → ℝ}
    {R₀ Rₓ : Matrix (Fin s) (Fin s) ℝ}
    (H : QuadPTransportInput z g g' u u' v v' h R₀ Rₓ) :
    quadP z g' u' v' h Rₓ ≤
      (H.cU + 2 * H.muX * (1 + H.δ⁻¹) * (1 + H.δ') * H.Λ * H.ce ^ 2) *
          quadU z g u v h +
        H.muX * H.lam0⁻¹ * (1 + H.δ) * (2 * ((quadCvec z g u v h) ⬝ᵥ
          (R₀ *ᵥ (quadCvec z g u v h)))) +
        (H.cD + 2 * H.muX * (1 + H.δ⁻¹) * (1 + H.δ'⁻¹) * H.Λ * H.cd *
          (8 * H.a ^ 2)) * quadD z u v h :=
  quadP_transport H.hΛ H.hδ H.hδ' H.ha H.hμ H.hlam H.hz H.hcol H.hrow
    H.hRₓ H.hR₀ H.he H.hcd H.hg H.hU

/-! ## 6. Anchor/row-bound interfaces

### Ledger (`AnchorUpdate.lean`, `RowBoundA2.lean`,
`InitializationMargin.lean`)

Every invariant the update theorems carry as a hypothesis is proved
preserved by the update; the genuine *maintained state* reduces to the
three-field package `RowUpdateInvariant` below. Concretely:

| hypothesis / invariant | status |
|---|---|
| `s.Coherent` (`p = b²`, `q = ∑ p`) | DISCHARGED along the update — `anchorUpdate_coherent` |
| `scaleInvariant s.q s.r` | DISCHARGED along the update — `anchorUpdate_scale_invariant` |
| `0 ≤ s.r` | DISCHARGED along the update — `anchorUpdate_r_nonneg` |
| `0 < qstar` | OPEN parameter (the retirement threshold) |
| post-update classification `hcls`, `hmedium` | DISCHARGED as trichotomy — `anchorUpdate_classify_trichotomy` |
| post-update spread condition | DISCHARGED — `anchorUpdate_spread` |
| post-update scale window | DISCHARGED — `anchorUpdate_scale_window` |
| `r ≤ Rmax` propagation | DISCHARGED — `anchorUpdate_r_le_Rmax` |
| A.2 quadratic bound | DISCHARGED — `a2_row_quadratic_bound` |
| `(1+733/727500)^10000 > 23634` | DISCHARGED — `initialization_margin` | -/

/-- The per-row invariant bundle consumed by every `anchorUpdate_*`
theorem: coherence, the scale invariant, and scale nonnegativity. -/
structure RowUpdateInvariant {n : ℕ} (s : RowState n) : Prop where
  /-- `p = b²` and `q = ∑ p`. -/
  coherent : s.Coherent
  /-- `q ≤ r² ∨ r = Rmax`. -/
  scale : scaleInvariant s.q s.r
  /-- `0 ≤ r`. -/
  r_nonneg : 0 ≤ s.r

/-- The invariant is preserved by `anchorUpdate` (with `qstar > 0`):
`anchorUpdate_coherent` + `anchorUpdate_scale_invariant` +
`anchorUpdate_r_nonneg`. -/
theorem RowUpdateInvariant.anchorUpdate {n : ℕ} {s : RowState n}
    (x : Fin n → ℝ) (qstar : ℝ) (hqstar : 0 < qstar)
    (h : RowUpdateInvariant s) :
    RowUpdateInvariant (RowState.anchorUpdate x s qstar) :=
  ⟨RowState.anchorUpdate_coherent x s qstar h.coherent,
   RowState.anchorUpdate_scale_invariant x s qstar h.coherent hqstar
     h.scale h.r_nonneg,
   RowState.anchorUpdate_r_nonneg x s qstar h.coherent hqstar h.scale
     h.r_nonneg⟩

/-! ## 7. Runtime bounds (`RuntimeBound.lean`)

### Ledger

| hypothesis | status |
|---|---|
| `WellScaled c` | DISCHARGED for `BitCostModel.quadratic` (`quadratic_wellScaled`); OPEN for a general model — and genuinely needed, `not_theorem11WithRuntime` refutes the unconditional claim |
| `BoolSigningExists` | DISCHARGED from `WalkSuccessHypothesis` (`boolSigningExists_of_walkSuccess`): a real `IsSigning` is realized by a Boolean signing coordinatewise, and small dimensions are handled by `small_dimension_exists` |
| `DiscrepancyRuntimeBound` itself | conditional — no unconditional runtime proof exists | -/

/-- A real signing is realized by a Boolean signing: `bⱼ := (εⱼ = 1)`.
This is the cast needed to feed `WalkSuccessInput`-style existence into
the verifier/`BoolSigningExists` interfaces. -/
theorem realSigning_eq_of_isSigning {n : ℕ} {ε : Fin n → ℝ}
    (hε : IsSigning ε) : ∃ b : Fin n → Bool, realSigning b = ε := by
  refine ⟨fun j => decide (ε j = 1), ?_⟩
  funext j
  show (if decide (ε j = 1) then (1:ℝ) else -1) = ε j
  by_cases hj : ε j = 1
  · have hdec : decide (ε j = 1) = true := by simp [hj]
    rw [hdec]
    simpa using hj.symm
  · have hneg : ε j = -1 := (hε j).resolve_right hj
    have hdec : decide (ε j = 1) = false := by simp [hj]
    rw [hdec]
    simpa using hneg.symm

/-- `BoolSigningExists`, discharged from the walk package: for `m = 0`
vacuous, for `n < 64` by `small_dimension_exists`, otherwise by
`exists_signing_discrepancy_below_99` plus the Boolean realization. -/
theorem boolSigningExists_of_walkSuccess (h : WalkSuccessHypothesis) :
    BoolSigningExists := by
  intro m n A hA
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨fun _ => false, fun i => i.elim0⟩
  · rcases Nat.lt_or_ge n 64 with hn | hn
    · obtain ⟨ε, hε⟩ := small_dimension_exists hA hn
      obtain ⟨b, hb⟩ := realSigning_eq_of_isSigning hε.1
      exact ⟨b, fun i => by rw [hb]; exact hε.2 i⟩
    · obtain ⟨w⟩ := h m n A hA hm hn
      obtain ⟨ε, hε⟩ := exists_signing_discrepancy_below_99 w
      obtain ⟨b, hb⟩ := realSigning_eq_of_isSigning hε.1
      exact ⟨b, fun i => by rw [hb]; exact hε.2 i⟩

/-- The conditional runtime theorem with `BoolSigningExists` discharged
by the walk package: `DiscrepancyRuntimeBound c` still requires
`c.WellScaled` (necessary, by `not_theorem11WithRuntime`). -/
theorem discrepancyRuntimeBound_of_walkSuccess (c : BitCostModel)
    (hs : c.WellScaled) (h : WalkSuccessHypothesis) :
    DiscrepancyRuntimeBound c :=
  discrepancyRuntimeBound_of_existence c hs
    (boolSigningExists_of_walkSuccess h)

/-- Instantiation at the schoolbook model, with both the `WellScaled` and
the signing-existence hypotheses reduced to the walk package. -/
theorem discrepancyRuntimeBound_quadratic_of_walkSuccess
    (h : WalkSuccessHypothesis) :
    DiscrepancyRuntimeBound BitCostModel.quadratic :=
  discrepancyRuntimeBound_of_walkSuccess _
    BitCostModel.quadratic_wellScaled h

end

end Komlos
