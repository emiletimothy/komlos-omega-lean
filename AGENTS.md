# Lean formalization project

## Build and verification

- Lean and Mathlib4 are pinned to v4.34.1. Keep lake-manifest.json, which pins dependency commits.
- Run `lake build` from this directory. Default targets include KomlosAudit, which imports all currently developed modules.
- Run `lake env lean -DwarningAsError=true KomlosAudit.lean` to rerun the axiom audit with warnings treated as errors.
- The audit traverses dependencies of every theorem in the Komlos namespace. Only propext, Classical.choice, and Quot.sound are allowed. Its count includes compiler-generated theorem declarations.
- Add new proof modules to the audit imports. Do not use sorry, new axioms, or native_decide to fill gaps.

## Progress graph

- `progress/generate_graph.py` scans the .lean sources and writes `progress/graph_data.json` (declarations, sorry/axiom detection, audited import closure, per-node status). Run it after builds; `--watch` regenerates on source changes.
- `progress/index.html` renders the graph; serve with `python3 -m http.server` from `progress/` and it auto-refreshes the JSON every 15s.
- Node→Lean-declaration mapping lives in the `NODES`/`EDGES` manifest at the top of the script; update it when adding modules. `progress/last_audit.json` records the latest audit count.
- Green = declarations in the audited closure; amber-dashed = proved modulo undischarged hypotheses; orange = exists but outside the audited build; red = not formalized; hatched green = Mathlib/axioms.

## Mathematical scope

This is an incomplete formalization of the 27-page paper "The Komlós Problem in Near Matrix-Multiplication Time" by Emile Anand and Peter Chen, dated October 12, 2026. The source PDF supplied by the user is `/Users/emile/Downloads/Komlos_problem_in_matrix_multiplication_time.pdf`.

`DiscrepancyPartOfTheorem11` is only a definition of the rational-input discrepancy proposition. It has no proof, and it does not specify runtime. Successful compilation or verification of an individual signing must not be reported as a certificate of Theorem 1.1.

Core:
- Komlos.lean: row estimates, barriers, representation/deletion accounting, constants, and an exact rational signing checker with soundness and threshold tests.
- Komlos/Resolvent.lean: rational weight `weight u = 119/(1-u/20000)^10000` monotonicity, the ground-state identity with general right-hand side, and weighted Gram quadratic-form domination.
- Komlos/MatrixInverse.lean: actual matrix inverse positivity from positive-definite slack and entrywise nonnegative M; positive resolvent vectors; potential comparisons under entrywise changes, principal deletion, and barrier increases; soundness of the anchor guard; relative resolvent perturbation bounds.
- Komlos/Walk.lean: finite adaptive binary-tree averages, symmetric-walk energy accounting, and clipping geometry.

Appendix B (spectral dimension / curvature):
- Komlos/Curvature.lean: weight derivatives `weightDeriv`/`weightDeriv2`, `HasDerivAt` certificates, relative-change bounds, and the matrix/resolvent derivative chain (`hasDerivAt_resolvent_inv_*`, `differentiableAt_det/adjugate/inv_entry`).
- Komlos/SpectralDimension.lean: exact resolvent step identities, `potentialSlope`/`potentialHessian`, batch relative-change bounds, dimension-margin bookkeeping, conditional `dim > s/32` spectral-subspace theorem.
- Komlos/ResolventContinuity.lean, Komlos/CurvatureGeneral.lean, Komlos/SpectralPath.lean, Komlos/PotentialConcavity.lean, Komlos/ConcaveStep.lean: pathwise resolvent calculus and potential concavity along the batch quadratic path.
- Komlos/NonpositiveSubspace.lean: the spectral counting lemma (PSD Q with diagonal dominated by D admits a large-dimension Q−D-nonpositive subspace).

Gaussian / Appendix D:
- Komlos/GaussianCompletion.lean: quadratic-form lower/upper bounds and Loewner inverse propagation (QF machinery for Lemma D.1).
- Komlos/GaussianMoments.lean: Gaussian even moments `(2q−1)‼`, χ²₁ mgf `E[e^{tX²}] = (1−2t)^{-1/2}`, Gaussian small-ball bound.
- Komlos/GaussianDisintegration.lean: conditional standard-Gaussian laws under linear maps — `stdGaussian` splits across K ⊕ Kᗮ, `gaussLift` (Moore–Penrose lift), joint law `Law(LZ) ⊗ₘ gaussCondKernel`. The "hidden Gaussian stays Gaussian after conditioning" core.
- Komlos/GaussianDensity.lean: adaptive Gaussian density invariant development.
- Komlos/CompletionSampler.lean: sampler-side definitions.

Algorithm / maintenance / precision / runtime:
- Komlos/InverseMaintenanceBlock.lean: the eq. (4.5) augmented block inverse and Frobenius bookkeeping.
- Komlos/InverseUpdate.lean: Sherman–Morrison rank-one inverse update and the matrix determinant lemma.
- Komlos/DynamicMaintenance.lean: `DynamicInverseState` certificate preservation, guard ⇔ `IsUnit`, amortized `maintenanceTotalOps_le` cost bound inside the bit-cost envelope.
- Komlos/FinitePrecision.lean: rational grid rounding, rounded-input soundness, deterministic transcript coupling.
- Komlos/FiniteRounding.lean: further rounding/precision development.
- Komlos/Runtime.lean: `BitCostModel` with abstract `ω`, `inputBitSize`, `DiscrepancyRuntimeBound`/`Theorem11WithRuntime` Props (statement, not proof).
- Komlos/TrialConcentration.lean: uniform finite model over `Fin n → Bool` signings, second-moment identity `E[(Aε)ᵢ²] = ΣⱼAᵢⱼ²`, existence of a signing with ≤ n/T² bad rows, and the `terminalAverage_cubeTop` bridge to SymmetricWalk leaf averages.
- Komlos/AnchorUpdate.lean, Komlos/InitializationMargin.lean, Komlos/RowBoundA2.lean, Komlos/DiscrepancyReduction.lean: anchor-update, initialization and row-bound bookkeeping.
- Komlos/StabilityTransport.lean: (B.5)–(B.10) displacement bounds transporting the curvature bound from the anchor to the trust window.
- Komlos/HessianDecomposition.lean: the `∇²F_b = P − D` identification (in the audit).
- Komlos/UniformSphere.lean: `dirRV` law invariance under the `range Z` stabilizer, fair orientation (`dirRV_law_neg`), support on `sphere ∩ rangeZ` — the invariance surrogate for "uniform on the sphere" (Mathlib has no normalized sphere measure).
- Komlos/RandomizedCoupling.lean: finite coin-flip model of dithered rounding — unbiasedness, `p(1−p)` variance identity, `incSum` martingale recursion, `transcriptDrift` variance/tail bounds.
- Komlos/RuntimeBound.lean: `WellScaled` cost-model predicate, `verificationBitCost ≤ runtimeEnvelope`, `discrepancyRuntimeBound_of_existence` (conditional runtime theorem), and a countermodel proving `Theorem11WithRuntime` is false for badly-scaled models.
- Komlos/Theorem11Assembly.lean: `DiscrepancyPartOfTheorem11_of_walkSuccess` — Theorem 1.1 (discrepancy half) conditional on a 12-field `WalkSuccessInput`; docstring lists the residual checklist.

Still open / conditional:
- The adaptive Gaussian density invariant is only partially discharged (conditioning core proved; the full Lemma D.1 / Thm 4.1 chain, predictable iteration, and net arguments D.7–D.9 remain).
- The `dirRV` law is proved invariant + fairly oriented; the remaining step to Thm 4.1's concentration conclusions is the martingale/predictable-iteration chain.
- `WalkSuccessInput`'s fields (coherent cube-leaf walk, leaf-is-signing, still-large bound, completed/medium decomposition) are the residual checklist for `DiscrepancyPartOfTheorem11`.
- `DiscrepancyRuntimeBound` proved only for `WellScaled` models conditional on signing existence; `Theorem11WithRuntime` as literally stated is refuted (`not_theorem11WithRuntime`).
- Nothing certifies Theorem 1.1 unconditionally.
