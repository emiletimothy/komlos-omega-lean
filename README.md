# komlos-omega-lean

A work-in-progress Lean 4 / Mathlib formalization of the paper

> **"The Komlós Problem in Near Matrix-Multiplication Time"**
> Emile Anand and Peter Chen

The goal is a machine-checked certificate of the paper's main result (Theorem 1.1):
a signing algorithm with low discrepancy whose running time is near matrix-multiplication
time, together with its analysis (resolvent barriers, spectral dimension, adaptive
Gaussian concentration, dynamic inverse maintenance, and bit-complexity accounting).

## Status

**Partial / conditional — this is not yet a complete certificate of Theorem 1.1.**

- The project builds cleanly (`lake build`) and passes a strict axiom audit
  (`-DwarningAsError=true`): ~1,179 `Komlos`-namespaced theorem declarations,
  depending only on `propext`, `Classical.choice`, and `Quot.sound`.
  No `sorry`, `admit`, `native_decide`, or custom axioms.
- `DiscrepancyPartOfTheorem11` is a *definition* of the discrepancy proposition.
  `Theorem11Assembly` proves it **conditional** on a 12-field `WalkSuccessInput`
  package (coherent cube-leaf walk, leaf-is-signing, still-large bound,
  completed/medium decomposition, ...).
- `DiscrepancyRuntimeBound` is proved only for `WellScaled` cost models and
  conditional on signing existence; `not_theorem11WithRuntime` shows the
  unrestricted runtime statement is false for badly-scaled models.
- Main remaining gaps: the full Lemma D.1 / Theorem 4.1 adaptive-Gaussian
  concentration chain (predictable iteration, net arguments D.7–D.9), the explicit
  conditional-density / Gram-Jacobian (Wishart-type) calculation, and inhabiting
  `WalkSuccessInput`.

## Building

Requires Lean 4 via [elan](https://github.com/leanprover/elan). The toolchain is
pinned to `leanprover/lean4:v4.34.1` and Mathlib to `v4.34.1`
(`lake-manifest.json` pins dependency commits — keep it).

```bash
lake build                 # builds Komlos + KomlosAudit
lake env lean -DwarningAsError=true KomlosAudit.lean   # axiom audit
```

The audit traverses the proof dependencies of every theorem in the `Komlos`
namespace and fails on anything other than the three allowed axioms.

## Layout

- `Komlos.lean` — row estimates, barriers, representation/deletion accounting,
  constants, exact rational signing checker (soundness + threshold tests).
- `Komlos/Resolvent.lean`, `Komlos/MatrixInverse.lean` — rational barrier weight
  `119/(1-u/20000)^10000`, ground-state identity, weighted Gram domination,
  inverse positivity, resolvent perturbation bounds.
- `Komlos/Walk.lean` — adaptive binary-tree averages, symmetric-walk energy,
  clipping geometry.
- Appendix B (spectral dimension / curvature):
  `Curvature.lean`, `SpectralDimension.lean`, `ResolventContinuity.lean`,
  `CurvatureGeneral.lean`, `SpectralPath.lean`, `PotentialConcavity.lean`,
  `ConcaveStep.lean`, `NonpositiveSubspace.lean`, `StabilityTransport.lean`,
  `HessianDecomposition.lean`, `AnchorUpdate.lean`, `AnchorDimension.lean`,
  `InitializationMargin.lean`, `ResolventStability.lean`, `RowBoundA2.lean`.
- Gaussian / Appendix D:
  `GaussianCompletion.lean`, `GaussianMoments.lean`,
  `GaussianDisintegration.lean`, `GaussianDensity.lean`,
  `CompletionSampler.lean`, `UniformSphere.lean`.
- Algorithm / maintenance / precision / runtime:
  `InverseMaintenanceBlock.lean`, `InverseUpdate.lean`, `DynamicMaintenance.lean`,
  `FinitePrecision.lean`, `FiniteRounding.lean`, `Runtime.lean`,
  `RuntimeBound.lean`, `TrialConcentration.lean`, `ConcentrationMarkov.lean`,
  `RandomizedCoupling.lean`, `DiscrepancyReduction.lean`,
  `Theorem11Assembly.lean`.
- `KomlosAudit.lean` — imports all audited modules and runs the axiom audit.
- `progress/` — self-contained progress-graph generator and viewer
  (`generate_graph.py` scans sources → `graph_data.json`/`graph_data.js`;
  open `index.html` or serve with `python3 -m http.server` from `progress/`).
- `AGENTS.md` — detailed module inventory, build/verification rules, and the
  honest list of remaining gaps.
