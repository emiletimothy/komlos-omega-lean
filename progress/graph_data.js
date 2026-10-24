const EMBEDDED_GRAPH = {
  "generated": "2026-10-14 23:41:39",
  "nodes": [
    {
      "id": "thm11",
      "kind": "milestone",
      "tier": 0,
      "order": 0,
      "label": "Theorem 1.1",
      "sub": "Koml\u00f3s conjecture",
      "notes": "Signing of a column-normalized matrix with discrepancy < 100, certified in near matrix-multiplication expected time. Not yet proved end-to-end.",
      "decls": [],
      "resolved": [],
      "status": "conditional"
    },
    {
      "id": "stmt",
      "kind": "result",
      "tier": 1,
      "order": 0,
      "label": "Statement + verifier",
      "sub": "Thm 1.1 Prop \u00b7 rational checker",
      "decls": [
        "DiscrepancyPartOfTheorem11",
        "IsSigning",
        "HasDiscrepancyBelow",
        "verifySigning",
        "verifySigning_sound",
        "verify_zero_matrix",
        "verify_accepts_below_threshold",
        "verify_rejects_at_threshold",
        "realSigning_isSigning",
        "input_rounding_error",
        "accepted_output_sound"
      ],
      "notes": "The discrepancy proposition is stated and an exact rational signing checker is proved sound. This formalizes the *claim*, not its proof.",
      "resolved": [
        {
          "name": "DiscrepancyPartOfTheorem11",
          "file": "Komlos.lean",
          "line": 29
        },
        {
          "name": "IsSigning",
          "file": "Komlos.lean",
          "line": 17
        },
        {
          "name": "HasDiscrepancyBelow",
          "file": "Komlos.lean",
          "line": 26
        },
        {
          "name": "verifySigning",
          "file": "Komlos.lean",
          "line": 327
        },
        {
          "name": "verifySigning_sound",
          "file": "Komlos.lean",
          "line": 334
        },
        {
          "name": "verify_zero_matrix",
          "file": "Komlos.lean",
          "line": 349
        },
        {
          "name": "verify_accepts_below_threshold",
          "file": "Komlos.lean",
          "line": 353
        },
        {
          "name": "verify_rejects_at_threshold",
          "file": "Komlos.lean",
          "line": 357
        },
        {
          "name": "realSigning_isSigning",
          "file": "Komlos.lean",
          "line": 330
        },
        {
          "name": "input_rounding_error",
          "file": "Komlos.lean",
          "line": 295
        },
        {
          "name": "accepted_output_sound",
          "file": "Komlos.lean",
          "line": 308
        }
      ],
      "status": "done"
    },
    {
      "id": "disc",
      "kind": "milestone",
      "tier": 1,
      "order": 1,
      "label": "Discrepancy bound < 100",
      "sub": "existence half",
      "notes": "Every row of the produced signing stays below the 100 threshold. A conditional assembly exists (DiscrepancyPartOfTheorem11_of_walkSuccess); the 12-field walk-success hypothesis is still open.",
      "decls": [],
      "resolved": [],
      "status": "conditional"
    },
    {
      "id": "runtime",
      "kind": "milestone",
      "tier": 1,
      "order": 2,
      "label": "Runtime \u2248 n^\u03c9 bit ops",
      "sub": "efficiency half",
      "notes": "Expected bit-complexity bound for the whole algorithm. RuntimeBound.lean proves a *conditional* version for `WellScaled` cost models, and refutes the naive universally-quantified statement via a badly-scaled countermodel.",
      "decls": [],
      "resolved": [],
      "status": "conditional"
    },
    {
      "id": "propA1",
      "kind": "result",
      "tier": 2,
      "order": 0,
      "conditional": true,
      "label": "Prop A.1 reduction",
      "sub": "deterministic + walk assembly",
      "decls": [
        "deterministic_discrepancy_reduction",
        "discrepancy_below_99",
        "WalkSuccessInput",
        "exists_signing_discrepancy_below_99",
        "DiscrepancyPartOfTheorem11_of_walkSuccess"
      ],
      "notes": "Conditional: `discrepancy_below_99` derives the < 99 max-bound from per-row hypotheses, and Theorem11Assembly packages them into a 12-field `WalkSuccessInput` proving the existence half modulo walk success. Discharging that structure is the remaining surface.",
      "resolved": [
        {
          "name": "deterministic_discrepancy_reduction",
          "file": "Komlos/DiscrepancyReduction.lean",
          "line": 8
        },
        {
          "name": "discrepancy_below_99",
          "file": "Komlos/DiscrepancyReduction.lean",
          "line": 31
        },
        {
          "name": "WalkSuccessInput",
          "file": "Komlos/Theorem11Assembly.lean",
          "line": 43
        },
        {
          "name": "exists_signing_discrepancy_below_99",
          "file": "Komlos/Theorem11Assembly.lean",
          "line": 76
        },
        {
          "name": "DiscrepancyPartOfTheorem11_of_walkSuccess",
          "file": "Komlos/Theorem11Assembly.lean",
          "line": 100
        }
      ],
      "status": "conditional"
    },
    {
      "id": "gauss_inv",
      "kind": "result",
      "tier": 2,
      "order": 1,
      "conditional": true,
      "label": "Adaptive Gaussian invariant",
      "sub": "App. C/D \u00b7 uniformity half done",
      "decls": [
        "dirRV_equivariance",
        "ae_dirRV_equivariance",
        "dirRV_law_invariant",
        "dirRV_law_neg",
        "dirRV_law_uniform",
        "measurePreserving_stabSourceMap",
        "dirRVUniformStatement_holds"
      ],
      "notes": "The distributional half of Thm 4.1 now exists: UniformSphere.lean proves stabilizer invariance, equivariance, sign decoupling and range support of the completion-direction law (`dirRV` pushforward is orthogonal-invariant \u2014 the uniform-sphere surrogate). Still missing: the per-iteration concentration bounds (4.4)/(D.5) and the adaptive filtration.",
      "resolved": [
        {
          "name": "dirRV_equivariance",
          "file": "Komlos/UniformSphere.lean",
          "line": 530
        },
        {
          "name": "ae_dirRV_equivariance",
          "file": "Komlos/UniformSphere.lean",
          "line": 639
        },
        {
          "name": "dirRV_law_invariant",
          "file": "Komlos/UniformSphere.lean",
          "line": 678
        },
        {
          "name": "dirRV_law_neg",
          "file": "Komlos/UniformSphere.lean",
          "line": 720
        },
        {
          "name": "dirRV_law_uniform",
          "file": "Komlos/UniformSphere.lean",
          "line": 795
        },
        {
          "name": "measurePreserving_stabSourceMap",
          "file": "Komlos/UniformSphere.lean",
          "line": 162
        },
        {
          "name": "dirRVUniformStatement_holds",
          "file": "Komlos/UniformSphere.lean",
          "line": 805
        }
      ],
      "status": "conditional"
    },
    {
      "id": "conc",
      "kind": "gap",
      "tier": 2,
      "order": 2,
      "label": "Adaptive trial concentration",
      "sub": "missing",
      "notes": "Concentration for the *adaptive Gaussian* trials. The net/union-bound/predictable-iteration machinery now exists in GaussianInvariant.lean; the per-step density invariant (`step_ae`) and the Gaussian small-ball instantiation remain hypothesis fields.",
      "decls": [],
      "resolved": [],
      "status": "missing"
    },
    {
      "id": "gaussinvariant",
      "kind": "result",
      "tier": 3,
      "order": 1.5,
      "conditional": true,
      "label": "Predictable Gaussian iteration",
      "sub": "GaussianInvariant.lean",
      "decls": [
        "MetricNet",
        "exists_metricNet",
        "exists_metricNet_sphere_pi",
        "exists_metricNet_euclideanSphere",
        "measure_biUnion_finset_le_const",
        "inner_tail_transfer",
        "measure_iUnion_le_net",
        "measure_iUnion_inner_tail_le",
        "PredictableSteps",
        "jointLaw",
        "jointLaw_map_histTrunc",
        "jointLaw_iid",
        "ae_goodHist_jointLaw",
        "AdaptiveGaussianSteps",
        "GaussianInvariantInput",
        "GaussianInvariantInput.ae_jointLaw"
      ],
      "notes": "The D.7\u2013D.9 machinery: finite \u03b5-nets on compact sets/spheres, finite union bounds, Lipschitz tail transfer, predictable-iteration joint law (`jointLaw` via iterated compProd), and `ae_goodHist_jointLaw` \u2014 induction propagating a per-step a.e. invariant to the whole trajectory. The per-step Gaussian invariant itself remains an encapsulated field of `GaussianInvariantInput`.",
      "resolved": [
        {
          "name": "MetricNet",
          "file": "Komlos/GaussianInvariant.lean",
          "line": 23
        },
        {
          "name": "exists_metricNet",
          "file": "Komlos/GaussianInvariant.lean",
          "line": 32
        },
        {
          "name": "exists_metricNet_sphere_pi",
          "file": "Komlos/GaussianInvariant.lean",
          "line": 45
        },
        {
          "name": "exists_metricNet_euclideanSphere",
          "file": "Komlos/GaussianInvariant.lean",
          "line": 50
        },
        {
          "name": "measure_biUnion_finset_le_const",
          "file": "Komlos/GaussianInvariant.lean",
          "line": 57
        },
        {
          "name": "inner_tail_transfer",
          "file": "Komlos/GaussianInvariant.lean",
          "line": 90
        },
        {
          "name": "measure_iUnion_le_net",
          "file": "Komlos/GaussianInvariant.lean",
          "line": 112
        },
        {
          "name": "measure_iUnion_inner_tail_le",
          "file": "Komlos/GaussianInvariant.lean",
          "line": 144
        },
        {
          "name": "PredictableSteps",
          "file": "Komlos/GaussianInvariant.lean",
          "line": 223
        },
        {
          "name": "jointLaw",
          "file": "Komlos/GaussianInvariant.lean",
          "line": 246
        },
        {
          "name": "jointLaw_map_histTrunc",
          "file": "Komlos/GaussianInvariant.lean",
          "line": 275
        },
        {
          "name": "jointLaw_iid",
          "file": "Komlos/GaussianInvariant.lean",
          "line": 295
        },
        {
          "name": "ae_goodHist_jointLaw",
          "file": "Komlos/GaussianInvariant.lean",
          "line": 371
        },
        {
          "name": "AdaptiveGaussianSteps",
          "file": "Komlos/GaussianInvariant.lean",
          "line": 449
        },
        {
          "name": "GaussianInvariantInput",
          "file": "Komlos/GaussianInvariant.lean",
          "line": 478
        },
        {
          "name": "GaussianInvariantInput.ae_jointLaw",
          "file": "Komlos/GaussianInvariant.lean",
          "line": 494
        }
      ],
      "status": "conditional"
    },
    {
      "id": "dyninv",
      "kind": "result",
      "tier": 2,
      "order": 3,
      "conditional": true,
      "label": "Fast dynamic inverse",
      "sub": "DynamicMaintenance.lean",
      "decls": [
        "DynamicInverseState",
        "update_A",
        "update_Inv",
        "updateCol_A",
        "maintenanceTotalOps",
        "maintenanceTotalOps_le"
      ],
      "notes": "Abstract Sherman\u2013Morrison/state model: certificate preservation across updates and an amortized `maintenanceTotalOps_le` cost bound inside the bit-cost envelope. The concrete algorithmic implementation is still an abstract hypothesis.",
      "resolved": [
        {
          "name": "DynamicInverseState",
          "file": "Komlos/DynamicMaintenance.lean",
          "line": 16
        },
        {
          "name": "update_A",
          "file": "Komlos/DynamicMaintenance.lean",
          "line": 85
        },
        {
          "name": "update_Inv",
          "file": "Komlos/DynamicMaintenance.lean",
          "line": 91
        },
        {
          "name": "updateCol_A",
          "file": "Komlos/DynamicMaintenance.lean",
          "line": 104
        },
        {
          "name": "maintenanceTotalOps",
          "file": "Komlos/DynamicMaintenance.lean",
          "line": 428
        },
        {
          "name": "maintenanceTotalOps_le",
          "file": "Komlos/DynamicMaintenance.lean",
          "line": 437
        }
      ],
      "status": "conditional"
    },
    {
      "id": "dither",
      "kind": "result",
      "tier": 2,
      "order": 4,
      "conditional": true,
      "label": "Randomized dither coupling",
      "sub": "RandomizedCoupling.lean \u00b7 finite model",
      "decls": [
        "unifAvg_ditherErr_sq",
        "unifAvg_ditherErr_sq_le",
        "unifAvg_ditherWalk_conditional",
        "ditherWalk_tail_le",
        "unifAvg_transcriptDrift",
        "transcriptDrift_sq_le",
        "transcriptDrift_tail_le"
      ],
      "notes": "Finite uniform model: unbiased dithered rounding, p(1\u2212p) variance identity, `incSum` martingale recursion and Markov tail bounds for transcript drift. The paper's full filtration/coupling to the adaptive Gaussian walk is still a hypothesis.",
      "resolved": [
        {
          "name": "unifAvg_ditherErr_sq",
          "file": "Komlos/RandomizedCoupling.lean",
          "line": 330
        },
        {
          "name": "unifAvg_ditherErr_sq_le",
          "file": "Komlos/RandomizedCoupling.lean",
          "line": 429
        },
        {
          "name": "unifAvg_ditherWalk_conditional",
          "file": "Komlos/RandomizedCoupling.lean",
          "line": 666
        },
        {
          "name": "ditherWalk_tail_le",
          "file": "Komlos/RandomizedCoupling.lean",
          "line": 680
        },
        {
          "name": "unifAvg_transcriptDrift",
          "file": "Komlos/RandomizedCoupling.lean",
          "line": 740
        },
        {
          "name": "transcriptDrift_sq_le",
          "file": "Komlos/RandomizedCoupling.lean",
          "line": 871
        },
        {
          "name": "transcriptDrift_tail_le",
          "file": "Komlos/RandomizedCoupling.lean",
          "line": 906
        }
      ],
      "status": "conditional"
    },
    {
      "id": "algcost",
      "kind": "result",
      "tier": 2,
      "order": 6,
      "conditional": true,
      "label": "Concrete algorithm bit-cost",
      "sub": "AlgorithmCost.lean",
      "decls": [
        "WalkStep",
        "bitCost",
        "accountedBound",
        "bitCost_le_accountedBound",
        "WalkProfile",
        "WalkBudget",
        "totalBitCost",
        "totalBitCost_le_envelope",
        "algorithmCostModel",
        "algorithmCostModel_wellScaled",
        "discrepancyRuntimeBound_algorithmCostModel",
        "Theorem11WithRuntime'",
        "theorem11WithRuntime'"
      ],
      "notes": "A concrete step-level model of the algorithm (batch sampling, Gram/resolvent evaluation, rank-one/block updates, guard checks, grid rounding) with per-step bit costs. `totalBitCost_le_envelope` bounds the walk inside 48\u00b7envelope, `algorithmCostModel \u03c9` is WellScaled, and `theorem11WithRuntime'` proves the corrected runtime statement conditional on signing existence.",
      "resolved": [
        {
          "name": "WalkStep",
          "file": "Komlos/AlgorithmCost.lean",
          "line": 13
        },
        {
          "name": "bitCost",
          "file": "Komlos/AlgorithmCost.lean",
          "line": 25
        },
        {
          "name": "accountedBound",
          "file": "Komlos/AlgorithmCost.lean",
          "line": 51
        },
        {
          "name": "bitCost_le_accountedBound",
          "file": "Komlos/AlgorithmCost.lean",
          "line": 62
        },
        {
          "name": "WalkProfile",
          "file": "Komlos/AlgorithmCost.lean",
          "line": 146
        },
        {
          "name": "WalkBudget",
          "file": "Komlos/AlgorithmCost.lean",
          "line": 225
        },
        {
          "name": "totalBitCost",
          "file": "Komlos/AlgorithmCost.lean",
          "line": 140
        },
        {
          "name": "totalBitCost_le_envelope",
          "file": "Komlos/AlgorithmCost.lean",
          "line": 242
        },
        {
          "name": "algorithmCostModel",
          "file": "Komlos/AlgorithmCost.lean",
          "line": 453
        },
        {
          "name": "algorithmCostModel_wellScaled",
          "file": "Komlos/AlgorithmCost.lean",
          "line": 489
        },
        {
          "name": "discrepancyRuntimeBound_algorithmCostModel",
          "file": "Komlos/AlgorithmCost.lean",
          "line": 506
        },
        {
          "name": "Theorem11WithRuntime'",
          "file": "Komlos/AlgorithmCost.lean",
          "line": 515
        },
        {
          "name": "theorem11WithRuntime'",
          "file": "Komlos/AlgorithmCost.lean",
          "line": 519
        }
      ],
      "status": "conditional"
    },
    {
      "id": "bitmodel",
      "kind": "result",
      "tier": 2,
      "order": 5,
      "label": "Bit-cost vocabulary",
      "sub": "Runtime.lean",
      "decls": [
        "natBitSize",
        "ratBitSize",
        "inputBitSize",
        "BitCostModel",
        "BitCostModel.quadratic",
        "verificationBitCost",
        "runtimeEnvelope",
        "DiscrepancyRuntimeBound",
        "Theorem11WithRuntime"
      ],
      "notes": "Bit sizes, abstract \u03c9, operation costs and the runtime envelope are *defined*. The bound itself is unproven.",
      "resolved": [
        {
          "name": "natBitSize",
          "file": "Komlos/Runtime.lean",
          "line": 15
        },
        {
          "name": "ratBitSize",
          "file": "Komlos/Runtime.lean",
          "line": 24
        },
        {
          "name": "inputBitSize",
          "file": "Komlos/Runtime.lean",
          "line": 49
        },
        {
          "name": "BitCostModel",
          "file": "Komlos/Runtime.lean",
          "line": 70
        },
        {
          "name": "BitCostModel.quadratic",
          "file": "Komlos/Runtime.lean",
          "line": 126
        },
        {
          "name": "verificationBitCost",
          "file": "Komlos/Runtime.lean",
          "line": 153
        },
        {
          "name": "runtimeEnvelope",
          "file": "Komlos/Runtime.lean",
          "line": 182
        },
        {
          "name": "DiscrepancyRuntimeBound",
          "file": "Komlos/Runtime.lean",
          "line": 232
        },
        {
          "name": "Theorem11WithRuntime",
          "file": "Komlos/Runtime.lean",
          "line": 241
        }
      ],
      "status": "done"
    },
    {
      "id": "walk",
      "kind": "result",
      "tier": 3,
      "order": 0,
      "label": "Symmetric walk accounting",
      "sub": "Walk.lean",
      "decls": [
        "energy_accounting",
        "terminal_energy_bound",
        "squared_move_budget",
        "large_move_cost_bound",
        "full_step_count_bound",
        "terminal_average_bound",
        "terminal_average_le_root",
        "marked_progress_accounting",
        "marked_step_count_bound",
        "symmetric_boundary_hit",
        "clipped_endpoint_hits_boundary",
        "symmetric_endpoints_in_cube"
      ],
      "resolved": [
        {
          "name": "energy_accounting",
          "file": "Komlos/Walk.lean",
          "line": 57
        },
        {
          "name": "terminal_energy_bound",
          "file": "Komlos/Walk.lean",
          "line": 70
        },
        {
          "name": "squared_move_budget",
          "file": "Komlos/Walk.lean",
          "line": 80
        },
        {
          "name": "large_move_cost_bound",
          "file": "Komlos/Walk.lean",
          "line": 87
        },
        {
          "name": "full_step_count_bound",
          "file": "Komlos/Walk.lean",
          "line": 97
        },
        {
          "name": "terminal_average_bound",
          "file": "Komlos/Walk.lean",
          "line": 119
        },
        {
          "name": "terminal_average_le_root",
          "file": "Komlos/Walk.lean",
          "line": 129
        },
        {
          "name": "marked_progress_accounting",
          "file": "Komlos/Walk.lean",
          "line": 179
        },
        {
          "name": "marked_step_count_bound",
          "file": "Komlos/Walk.lean",
          "line": 191
        },
        {
          "name": "symmetric_boundary_hit",
          "file": "Komlos/Walk.lean",
          "line": 201
        },
        {
          "name": "clipped_endpoint_hits_boundary",
          "file": "Komlos/Walk.lean",
          "line": 221
        },
        {
          "name": "symmetric_endpoints_in_cube",
          "file": "Komlos/Walk.lean",
          "line": 227
        }
      ],
      "status": "done"
    },
    {
      "id": "concave",
      "kind": "result",
      "tier": 3,
      "order": 1,
      "conditional": true,
      "label": "Per-step concavity",
      "sub": "ConcaveStep.lean",
      "decls": [
        "concaveOn_pair_average_le",
        "concaveOn_branch_average_le",
        "localAverageNonincrease_of_branchConcave",
        "terminal_average_le_root_of_branchConcave"
      ],
      "notes": "Conditional: branch concavity of the resolvent potential is taken as a `ConcaveOn` hypothesis; the analytic Hessian argument is not yet formalized.",
      "resolved": [
        {
          "name": "concaveOn_pair_average_le",
          "file": "Komlos/ConcaveStep.lean",
          "line": 10
        },
        {
          "name": "concaveOn_branch_average_le",
          "file": "Komlos/ConcaveStep.lean",
          "line": 26
        },
        {
          "name": "localAverageNonincrease_of_branchConcave",
          "file": "Komlos/ConcaveStep.lean",
          "line": 51
        },
        {
          "name": "terminal_average_le_root_of_branchConcave",
          "file": "Komlos/ConcaveStep.lean",
          "line": 65
        }
      ],
      "status": "conditional"
    },
    {
      "id": "spectral",
      "kind": "result",
      "tier": 3,
      "order": 2,
      "conditional": true,
      "label": "Spectral dim. & stability",
      "sub": "App. B \u00b7 SpectralDimension.lean",
      "decls": [
        "resolvent_step_eq",
        "resolventPotential_step",
        "resolventPotential_step_taylor",
        "resolventPotential_symmetric_difference",
        "resolventVariation1_batch",
        "resolvent_vector_batch_relative_bounds",
        "resolventPotential_batch_change",
        "weight_abs_sub_le",
        "udiag_curvature_le",
        "curvature_drift_le",
        "light_gram_resolvent_form_le",
        "large_row_count",
        "nearly_tight_row_count",
        "four_loss_card",
        "spectral_dimension_margin",
        "finrank_inf_ker_constraintMap_ge",
        "spectral_subspace_exists",
        "spectral_subspace_dimension",
        "hasDerivAt_resolventPotential",
        "hasDerivAt_potentialSlope"
      ],
      "notes": "Batch perturbation, potential Taylor identities, curvature comparisons and constraint-kernel dimension bookkeeping. `spectral_subspace_exists` is conditional: it takes a good subspace E\u2080 as a hypothesis \u2014 that construction exists unconditionally in NonpositiveSubspace.lean, and StabilityTransport.lean adds the (B.5)\u2013(B.10) displacement bounds. All audited.",
      "resolved": [
        {
          "name": "resolvent_step_eq",
          "file": "Komlos/SpectralDimension.lean",
          "line": 106
        },
        {
          "name": "resolventPotential_step",
          "file": "Komlos/SpectralDimension.lean",
          "line": 136
        },
        {
          "name": "resolventPotential_step_taylor",
          "file": "Komlos/SpectralDimension.lean",
          "line": 167
        },
        {
          "name": "resolventPotential_symmetric_difference",
          "file": "Komlos/SpectralDimension.lean",
          "line": 191
        },
        {
          "name": "resolventVariation1_batch",
          "file": "Komlos/SpectralDimension.lean",
          "line": 230
        },
        {
          "name": "resolvent_vector_batch_relative_bounds",
          "file": "Komlos/SpectralDimension.lean",
          "line": 305
        },
        {
          "name": "resolventPotential_batch_change",
          "file": "Komlos/SpectralDimension.lean",
          "line": 336
        },
        {
          "name": "weight_abs_sub_le",
          "file": "Komlos/SpectralDimension.lean",
          "line": 365
        },
        {
          "name": "udiag_curvature_le",
          "file": "Komlos/SpectralDimension.lean",
          "line": 442
        },
        {
          "name": "curvature_drift_le",
          "file": "Komlos/SpectralDimension.lean",
          "line": 529
        },
        {
          "name": "light_gram_resolvent_form_le",
          "file": "Komlos/SpectralDimension.lean",
          "line": 576
        },
        {
          "name": "large_row_count",
          "file": "Komlos/SpectralDimension.lean",
          "line": 610
        },
        {
          "name": "nearly_tight_row_count",
          "file": "Komlos/SpectralDimension.lean",
          "line": 617
        },
        {
          "name": "four_loss_card",
          "file": "Komlos/SpectralDimension.lean",
          "line": 665
        },
        {
          "name": "spectral_dimension_margin",
          "file": "Komlos/SpectralDimension.lean",
          "line": 683
        },
        {
          "name": "finrank_inf_ker_constraintMap_ge",
          "file": "Komlos/SpectralDimension.lean",
          "line": 728
        },
        {
          "name": "spectral_subspace_exists",
          "file": "Komlos/SpectralDimension.lean",
          "line": 742
        },
        {
          "name": "spectral_subspace_dimension",
          "file": "Komlos/SpectralDimension.lean",
          "line": 789
        },
        {
          "name": "hasDerivAt_resolventPotential",
          "file": "Komlos/SpectralDimension.lean",
          "line": 937
        },
        {
          "name": "hasDerivAt_potentialSlope",
          "file": "Komlos/SpectralDimension.lean",
          "line": 1188
        }
      ],
      "status": "conditional"
    },
    {
      "id": "idischarge",
      "kind": "result",
      "tier": 3,
      "order": 2.5,
      "conditional": true,
      "label": "Interface discharge ledger",
      "sub": "InterfaceDischarge.lean",
      "decls": [
        "walk_of_existing",
        "signing_leaf_exists",
        "WalkSuccessInput'",
        "WalkSuccessInput'.toWalkSuccessInput",
        "exists_signing_discrepancy_below_99_of_reduced",
        "WalkSuccessHypothesis'",
        "DiscrepancyPartOfTheorem11_of_reducedWalkSuccess",
        "tracked_decomp_of_barrier_data",
        "SpectralHypotheses'",
        "spectral_subspace_exists_of_hypotheses'",
        "QuadPTransportInput",
        "quadP_transport_of_input",
        "RowUpdateInvariant",
        "RowUpdateInvariant.anchorUpdate",
        "maintenanceTotalOps_le_no_rebuild"
      ],
      "notes": "Machine-checked ledger reducing conditional interfaces to their residual fields: WalkSuccessInput shrinks 12 \u2192 5 fields (canonical cube walk, leaf-signing, defect cap discharged), spectral/concavity/maintenance preconditions bridged. The remaining fields are the real open math.",
      "resolved": [
        {
          "name": "walk_of_existing",
          "file": "Komlos/InterfaceDischarge.lean",
          "line": 25
        },
        {
          "name": "signing_leaf_exists",
          "file": "Komlos/InterfaceDischarge.lean",
          "line": 42
        },
        {
          "name": "WalkSuccessInput'",
          "file": "Komlos/InterfaceDischarge.lean",
          "line": 61
        },
        {
          "name": "WalkSuccessInput'.toWalkSuccessInput",
          "file": "Komlos/InterfaceDischarge.lean",
          "line": 80
        },
        {
          "name": "exists_signing_discrepancy_below_99_of_reduced",
          "file": "Komlos/InterfaceDischarge.lean",
          "line": 96
        },
        {
          "name": "WalkSuccessHypothesis'",
          "file": "Komlos/InterfaceDischarge.lean",
          "line": 102
        },
        {
          "name": "DiscrepancyPartOfTheorem11_of_reducedWalkSuccess",
          "file": "Komlos/InterfaceDischarge.lean",
          "line": 114
        },
        {
          "name": "tracked_decomp_of_barrier_data",
          "file": "Komlos/InterfaceDischarge.lean",
          "line": 120
        },
        {
          "name": "SpectralHypotheses'",
          "file": "Komlos/InterfaceDischarge.lean",
          "line": 157
        },
        {
          "name": "spectral_subspace_exists_of_hypotheses'",
          "file": "Komlos/InterfaceDischarge.lean",
          "line": 172
        },
        {
          "name": "QuadPTransportInput",
          "file": "Komlos/InterfaceDischarge.lean",
          "line": 471
        },
        {
          "name": "quadP_transport_of_input",
          "file": "Komlos/InterfaceDischarge.lean",
          "line": 516
        },
        {
          "name": "RowUpdateInvariant",
          "file": "Komlos/InterfaceDischarge.lean",
          "line": 533
        },
        {
          "name": "RowUpdateInvariant.anchorUpdate",
          "file": "Komlos/InterfaceDischarge.lean",
          "line": 542
        },
        {
          "name": "maintenanceTotalOps_le_no_rebuild",
          "file": "Komlos/InterfaceDischarge.lean",
          "line": 426
        }
      ],
      "status": "conditional"
    },
    {
      "id": "rows",
      "kind": "result",
      "tier": 3,
      "order": 3,
      "label": "Row & barrier estimates",
      "sub": "Komlos.lean",
      "decls": [
        "discarded_row_bound",
        "normalized_entry_abs_le_one",
        "total_mass_le_dimension",
        "retained_row_count",
        "small_dimension_signing",
        "deletion_charge",
        "deletion_constant_bound",
        "final_constant_margin",
        "live_row_count",
        "completed_row_error_bound",
        "deleted_defect_bound",
        "total_deleted_coefficient_bound",
        "protected_signs_exclusive",
        "barrier_pair_sum",
        "barriers_control_abs_value",
        "protected_barrier_nonincrease",
        "spread_gradient_bound",
        "curvature_dimension_margin",
        "affine_history_defect",
        "sqrt63_lt"
      ],
      "resolved": [
        {
          "name": "discarded_row_bound",
          "file": "Komlos.lean",
          "line": 46
        },
        {
          "name": "normalized_entry_abs_le_one",
          "file": "Komlos.lean",
          "line": 51
        },
        {
          "name": "total_mass_le_dimension",
          "file": "Komlos.lean",
          "line": 57
        },
        {
          "name": "retained_row_count",
          "file": "Komlos.lean",
          "line": 70
        },
        {
          "name": "small_dimension_signing",
          "file": "Komlos.lean",
          "line": 95
        },
        {
          "name": "deletion_charge",
          "file": "Komlos.lean",
          "line": 258
        },
        {
          "name": "deletion_constant_bound",
          "file": "Komlos.lean",
          "line": 287
        },
        {
          "name": "final_constant_margin",
          "file": "Komlos.lean",
          "line": 291
        },
        {
          "name": "live_row_count",
          "file": "Komlos.lean",
          "line": 454
        },
        {
          "name": "completed_row_error_bound",
          "file": "Komlos.lean",
          "line": 437
        },
        {
          "name": "deleted_defect_bound",
          "file": "Komlos.lean",
          "line": 410
        },
        {
          "name": "total_deleted_coefficient_bound",
          "file": "Komlos.lean",
          "line": 384
        },
        {
          "name": "protected_signs_exclusive",
          "file": "Komlos.lean",
          "line": 244
        },
        {
          "name": "barrier_pair_sum",
          "file": "Komlos.lean",
          "line": 235
        },
        {
          "name": "barriers_control_abs_value",
          "file": "Komlos.lean",
          "line": 219
        },
        {
          "name": "protected_barrier_nonincrease",
          "file": "Komlos.lean",
          "line": 180
        },
        {
          "name": "spread_gradient_bound",
          "file": "Komlos.lean",
          "line": 192
        },
        {
          "name": "curvature_dimension_margin",
          "file": "Komlos.lean",
          "line": 251
        },
        {
          "name": "affine_history_defect",
          "file": "Komlos.lean",
          "line": 372
        },
        {
          "name": "sqrt63_lt",
          "file": "Komlos.lean",
          "line": 282
        }
      ],
      "status": "done"
    },
    {
      "id": "init",
      "kind": "result",
      "tier": 3,
      "order": 3.5,
      "label": "Initialization margin (A.2)",
      "sub": "InitializationMargin.lean",
      "decls": [
        "termSeq_partial_sum_lower",
        "termSeq_partial_sum_lower_real",
        "initialization_margin",
        "barrier_at_Rmax",
        "weight_at_barrier_Rmax",
        "row_weight_bound_at_Rmax"
      ],
      "notes": "Certifies (1+733/727500)^10000 > 23634 via a kernel-checked rational partial sum, giving the (A.2) row bound 2\u03bd(16\u2212H\u2080/Rmax)/Rmax\u00b2 \u2264 (1000/1009)\u00b7bdep.",
      "resolved": [
        {
          "name": "termSeq_partial_sum_lower",
          "file": "Komlos/InitializationMargin.lean",
          "line": 45
        },
        {
          "name": "termSeq_partial_sum_lower_real",
          "file": "Komlos/InitializationMargin.lean",
          "line": 51
        },
        {
          "name": "initialization_margin",
          "file": "Komlos/InitializationMargin.lean",
          "line": 57
        },
        {
          "name": "barrier_at_Rmax",
          "file": "Komlos/InitializationMargin.lean",
          "line": 90
        },
        {
          "name": "weight_at_barrier_Rmax",
          "file": "Komlos/InitializationMargin.lean",
          "line": 94
        },
        {
          "name": "row_weight_bound_at_Rmax",
          "file": "Komlos/InitializationMargin.lean",
          "line": 100
        }
      ],
      "status": "done"
    },
    {
      "id": "gauss_cond",
      "kind": "result",
      "tier": 3,
      "order": 4,
      "label": "Gaussian disintegration",
      "sub": "App. D \u00b7 conditional law",
      "decls": [
        "stdGaussian_eq_prod_map_add",
        "stdGaussian_map_orthogonalProjectionOnto_prod",
        "gaussLift",
        "gaussLift_lifting",
        "gaussCondKernel",
        "stdGaussian_map_prodMk_compProd",
        "stdGaussian_eq_prod_map_add_gaussLift"
      ],
      "notes": "Regular conditional law of a standard Gaussian under a continuous linear map: Law(LZ,Z) = Law(LZ) \u2297\u2098 kernel, with shifted standard Gaussian on ker L.",
      "resolved": [
        {
          "name": "stdGaussian_eq_prod_map_add",
          "file": "Komlos/GaussianDisintegration.lean",
          "line": 30
        },
        {
          "name": "stdGaussian_map_orthogonalProjectionOnto_prod",
          "file": "Komlos/GaussianDisintegration.lean",
          "line": 82
        },
        {
          "name": "gaussLift",
          "file": "Komlos/GaussianDisintegration.lean",
          "line": 174
        },
        {
          "name": "gaussLift_lifting",
          "file": "Komlos/GaussianDisintegration.lean",
          "line": 187
        },
        {
          "name": "gaussCondKernel",
          "file": "Komlos/GaussianDisintegration.lean",
          "line": 274
        },
        {
          "name": "stdGaussian_map_prodMk_compProd",
          "file": "Komlos/GaussianDisintegration.lean",
          "line": 310
        },
        {
          "name": "stdGaussian_eq_prod_map_add_gaussLift",
          "file": "Komlos/GaussianDisintegration.lean",
          "line": 217
        }
      ],
      "status": "done"
    },
    {
      "id": "sphere_measure",
      "kind": "result",
      "tier": 3,
      "order": 4.5,
      "conditional": true,
      "label": "Uniform sphere measure",
      "sub": "SphereMeasure.lean",
      "decls": [
        "normalizeVec",
        "sphereLaw",
        "ae_sphereLaw_norm",
        "sphereLaw_map_isometry",
        "sphereLaw_neg",
        "sphereSubtypeMeasure",
        "sphereVecLaw",
        "sphereLawOn",
        "sphereLawOn_map_stabilizer",
        "uniformSphereMeasure",
        "uniformSphereMeasure_isUniform",
        "IsUniformSphereLaw",
        "IsUniformSphereLaw.meas_abs_inner_le"
      ],
      "notes": "The normalized uniform measure on the unit sphere built as the Gaussian pushforward x \u21a6 x/\u2016x\u2016: isometry-invariant, fair-oriented, supported on sphere \u2229 rangeZ. Bridges the dirRV surrogate to a real measure; uniqueness of the invariant measure on the homogeneous space remains encapsulated.",
      "resolved": [
        {
          "name": "normalizeVec",
          "file": "Komlos/SphereMeasure.lean",
          "line": 23
        },
        {
          "name": "sphereLaw",
          "file": "Komlos/SphereMeasure.lean",
          "line": 71
        },
        {
          "name": "ae_sphereLaw_norm",
          "file": "Komlos/SphereMeasure.lean",
          "line": 80
        },
        {
          "name": "sphereLaw_map_isometry",
          "file": "Komlos/SphereMeasure.lean",
          "line": 97
        },
        {
          "name": "sphereLaw_neg",
          "file": "Komlos/SphereMeasure.lean",
          "line": 111
        },
        {
          "name": "sphereSubtypeMeasure",
          "file": "Komlos/SphereMeasure.lean",
          "line": 149
        },
        {
          "name": "sphereVecLaw",
          "file": "Komlos/SphereMeasure.lean",
          "line": 240
        },
        {
          "name": "sphereLawOn",
          "file": "Komlos/SphereMeasure.lean",
          "line": 318
        },
        {
          "name": "sphereLawOn_map_stabilizer",
          "file": "Komlos/SphereMeasure.lean",
          "line": 366
        },
        {
          "name": "uniformSphereMeasure",
          "file": "Komlos/SphereMeasure.lean",
          "line": 424
        },
        {
          "name": "uniformSphereMeasure_isUniform",
          "file": "Komlos/SphereMeasure.lean",
          "line": 433
        },
        {
          "name": "IsUniformSphereLaw",
          "file": "Komlos/UniformSphere.lean",
          "line": 785
        },
        {
          "name": "IsUniformSphereLaw.meas_abs_inner_le",
          "file": "Komlos/SphereMeasure.lean",
          "line": 687
        }
      ],
      "status": "conditional"
    },
    {
      "id": "density_d5",
      "kind": "gap",
      "tier": 3,
      "order": 5,
      "label": "Explicit density (D.5)",
      "sub": "Gram Jacobian \u00b7 Wishart",
      "notes": "The explicit conditional density formula, Gram-map/QR Jacobian and Wishart-density calculations remain open.",
      "decls": [],
      "resolved": [],
      "status": "missing"
    },
    {
      "id": "conc_finite",
      "kind": "result",
      "tier": 3,
      "order": 6,
      "label": "Finite sign-model concentration",
      "sub": "TrialConcentration.lean",
      "decls": [
        "signAvg_rowValue_sq",
        "signAvg_sum_rowValue_sq_le",
        "sum_badRowCount_le",
        "exists_signing_few_bad_rows",
        "row_tail_fraction_le",
        "exists_in_support_few_bad_rows",
        "terminalAverage_cubeTop",
        "exists_memLeaf_signing_few_bad_rows"
      ],
      "notes": "Uniform model over Fin n \u2192 Bool: second-moment identities, Markov bad-row counting, and a bridge to SymmetricWalk. Not the adaptive Gaussian tails the paper needs.",
      "resolved": [
        {
          "name": "signAvg_rowValue_sq",
          "file": "Komlos/TrialConcentration.lean",
          "line": 160
        },
        {
          "name": "signAvg_sum_rowValue_sq_le",
          "file": "Komlos/TrialConcentration.lean",
          "line": 179
        },
        {
          "name": "sum_badRowCount_le",
          "file": "Komlos/TrialConcentration.lean",
          "line": 219
        },
        {
          "name": "exists_signing_few_bad_rows",
          "file": "Komlos/TrialConcentration.lean",
          "line": 259
        },
        {
          "name": "row_tail_fraction_le",
          "file": "Komlos/TrialConcentration.lean",
          "line": 274
        },
        {
          "name": "exists_in_support_few_bad_rows",
          "file": "Komlos/TrialConcentration.lean",
          "line": 306
        },
        {
          "name": "terminalAverage_cubeTop",
          "file": "Komlos/TrialConcentration.lean",
          "line": 678
        },
        {
          "name": "exists_memLeaf_signing_few_bad_rows",
          "file": "Komlos/TrialConcentration.lean",
          "line": 711
        }
      ],
      "status": "done"
    },
    {
      "id": "conc_markov",
      "kind": "result",
      "tier": 3,
      "order": 6.5,
      "label": "Markov sign counting",
      "sub": "ConcentrationMarkov.lean",
      "decls": [
        "card_univ_signing",
        "signAvg_markov",
        "bad_signing_fraction_le",
        "exists_good_signing",
        "good_signing_set_nonempty"
      ],
      "notes": "Markov's inequality over the uniform 2\u207f signing measure proved directly by Finset counting: at most a 1/p fraction of signings exceed p\u00b7(n/T\u00b2) bad rows, so a good signing exists. Still the finite uniform model, not the adaptive Gaussian tails.",
      "resolved": [
        {
          "name": "card_univ_signing",
          "file": "Komlos/ConcentrationMarkov.lean",
          "line": 15
        },
        {
          "name": "signAvg_markov",
          "file": "Komlos/ConcentrationMarkov.lean",
          "line": 23
        },
        {
          "name": "bad_signing_fraction_le",
          "file": "Komlos/ConcentrationMarkov.lean",
          "line": 81
        },
        {
          "name": "exists_good_signing",
          "file": "Komlos/ConcentrationMarkov.lean",
          "line": 96
        },
        {
          "name": "good_signing_set_nonempty",
          "file": "Komlos/ConcentrationMarkov.lean",
          "line": 106
        }
      ],
      "status": "done"
    },
    {
      "id": "invblock",
      "kind": "result",
      "tier": 3,
      "order": 7,
      "label": "Block inverse update",
      "sub": "Eq. 4.5 \u00b7 InverseMaintenanceBlock",
      "decls": [
        "augmentedMatrix",
        "augmentedMatrix_inv",
        "augmentedMatrix_inv_mulVec",
        "frobenius_norm_sq_fromBlocks",
        "augmentedMatrix_inv_norm_sq_le"
      ],
      "resolved": [
        {
          "name": "augmentedMatrix",
          "file": "Komlos/InverseMaintenanceBlock.lean",
          "line": 17
        },
        {
          "name": "augmentedMatrix_inv",
          "file": "Komlos/InverseMaintenanceBlock.lean",
          "line": 22
        },
        {
          "name": "augmentedMatrix_inv_mulVec",
          "file": "Komlos/InverseMaintenanceBlock.lean",
          "line": 33
        },
        {
          "name": "frobenius_norm_sq_fromBlocks",
          "file": "Komlos/InverseMaintenanceBlock.lean",
          "line": 55
        },
        {
          "name": "augmentedMatrix_inv_norm_sq_le",
          "file": "Komlos/InverseMaintenanceBlock.lean",
          "line": 80
        }
      ],
      "status": "done"
    },
    {
      "id": "rankone",
      "kind": "result",
      "tier": 3,
      "order": 8,
      "label": "Rank-one inverse updates",
      "sub": "Sherman\u2013Morrison \u00b7 InverseUpdate",
      "decls": [
        "sherman_morrison",
        "sherman_morrison_col",
        "frobenius_norm_sq_vecMulVec",
        "det_one_add_vecMulVec",
        "det_add_vecMulVec"
      ],
      "resolved": [
        {
          "name": "sherman_morrison",
          "file": "Komlos/InverseUpdate.lean",
          "line": 19
        },
        {
          "name": "sherman_morrison_col",
          "file": "Komlos/InverseUpdate.lean",
          "line": 53
        },
        {
          "name": "frobenius_norm_sq_vecMulVec",
          "file": "Komlos/InverseUpdate.lean",
          "line": 96
        },
        {
          "name": "det_one_add_vecMulVec",
          "file": "Komlos/InverseUpdate.lean",
          "line": 102
        },
        {
          "name": "det_add_vecMulVec",
          "file": "Komlos/InverseUpdate.lean",
          "line": 107
        }
      ],
      "status": "done"
    },
    {
      "id": "cont",
      "kind": "result",
      "tier": 3,
      "order": 9,
      "label": "Resolvent continuity",
      "sub": "ResolventContinuity.lean",
      "decls": [
        "continuousAt_slack_inv",
        "isUnit_slackMatrix_of_posDef",
        "continuousAt_slack_inv_quadratic",
        "posDef_eventually",
        "posDef_slackMatrix_eventually_add_smul",
        "posDef_slackMatrix_eventually_quadratic"
      ],
      "resolved": [
        {
          "name": "continuousAt_slack_inv",
          "file": "Komlos/ResolventContinuity.lean",
          "line": 29
        },
        {
          "name": "isUnit_slackMatrix_of_posDef",
          "file": "Komlos/ResolventContinuity.lean",
          "line": 37
        },
        {
          "name": "continuousAt_slack_inv_quadratic",
          "file": "Komlos/ResolventContinuity.lean",
          "line": 79
        },
        {
          "name": "posDef_eventually",
          "file": "Komlos/ResolventContinuity.lean",
          "line": 168
        },
        {
          "name": "posDef_slackMatrix_eventually_add_smul",
          "file": "Komlos/ResolventContinuity.lean",
          "line": 269
        },
        {
          "name": "posDef_slackMatrix_eventually_quadratic",
          "file": "Komlos/ResolventContinuity.lean",
          "line": 279
        }
      ],
      "status": "done"
    },
    {
      "id": "prec",
      "kind": "result",
      "tier": 3,
      "order": 10,
      "label": "Finite-precision transcript",
      "sub": "FinitePrecision.lean",
      "decls": [
        "roundToGrid",
        "abs_sub_roundToGrid",
        "roundEntrywise",
        "verifyRounded_sound",
        "verifySigning_rounded_sound",
        "soundness_precision_suffices",
        "step_coupling_bound",
        "transcript_drift_bound",
        "coupled_affine_transcript_drift",
        "coupled_deleted_drift",
        "energy_drift_bound",
        "barrier_drift_bound",
        "rounded_transcript_drift"
      ],
      "notes": "Deterministic rational-grid rounding, verification soundness, and transcript drift/coupling bounds.",
      "resolved": [
        {
          "name": "roundToGrid",
          "file": "Komlos/FinitePrecision.lean",
          "line": 15
        },
        {
          "name": "abs_sub_roundToGrid",
          "file": "Komlos/FinitePrecision.lean",
          "line": 23
        },
        {
          "name": "roundEntrywise",
          "file": "Komlos/FinitePrecision.lean",
          "line": 197
        },
        {
          "name": "verifyRounded_sound",
          "file": "Komlos/FinitePrecision.lean",
          "line": 277
        },
        {
          "name": "verifySigning_rounded_sound",
          "file": "Komlos/FinitePrecision.lean",
          "line": 330
        },
        {
          "name": "soundness_precision_suffices",
          "file": "Komlos/FinitePrecision.lean",
          "line": 295
        },
        {
          "name": "step_coupling_bound",
          "file": "Komlos/FinitePrecision.lean",
          "line": 358
        },
        {
          "name": "transcript_drift_bound",
          "file": "Komlos/FinitePrecision.lean",
          "line": 372
        },
        {
          "name": "coupled_affine_transcript_drift",
          "file": "Komlos/FinitePrecision.lean",
          "line": 419
        },
        {
          "name": "coupled_deleted_drift",
          "file": "Komlos/FinitePrecision.lean",
          "line": 474
        },
        {
          "name": "energy_drift_bound",
          "file": "Komlos/FinitePrecision.lean",
          "line": 508
        },
        {
          "name": "barrier_drift_bound",
          "file": "Komlos/FinitePrecision.lean",
          "line": 547
        },
        {
          "name": "rounded_transcript_drift",
          "file": "Komlos/FinitePrecision.lean",
          "line": 567
        }
      ],
      "status": "done"
    },
    {
      "id": "resolv",
      "kind": "result",
      "tier": 4,
      "order": 0,
      "label": "Resolvent machinery",
      "sub": "Resolvent + MatrixInverse",
      "decls": [
        "weight_pos",
        "weight_mono",
        "weight_le_119",
        "protected_weight_majorant",
        "ground_state_identity",
        "ground_state_identity_with_rhs",
        "ground_state_lower_bound",
        "weighted_rank_one_domination",
        "weighted_gram_slack_domination",
        "slack_solution_nonneg",
        "slack_inverse_entrywise_nonneg",
        "resolvent_equation",
        "resolventVector_pos",
        "resolventVector_entrywise_mono",
        "resolventPotential_entrywise_mono",
        "resolventVector_comparison_with_guard",
        "slackMatrix_principal_posDef",
        "resolventVector_principal_le",
        "resolventPotential_eq_sum_excess",
        "resolventPotential_barrier_antitone",
        "slack_posDef_of_positive_supersolution",
        "anchor_guard_sound",
        "resolvent_vector_relative_change",
        "resolvent_vector_relative_bounds"
      ],
      "resolved": [
        {
          "name": "weight_pos",
          "file": "Komlos/Resolvent.lean",
          "line": 10
        },
        {
          "name": "weight_mono",
          "file": "Komlos/Resolvent.lean",
          "line": 14
        },
        {
          "name": "weight_le_119",
          "file": "Komlos/Resolvent.lean",
          "line": 19
        },
        {
          "name": "protected_weight_majorant",
          "file": "Komlos/Resolvent.lean",
          "line": 23
        },
        {
          "name": "ground_state_identity",
          "file": "Komlos/Resolvent.lean",
          "line": 89
        },
        {
          "name": "ground_state_identity_with_rhs",
          "file": "Komlos/Resolvent.lean",
          "line": 36
        },
        {
          "name": "ground_state_lower_bound",
          "file": "Komlos/Resolvent.lean",
          "line": 104
        },
        {
          "name": "weighted_rank_one_domination",
          "file": "Komlos/Resolvent.lean",
          "line": 123
        },
        {
          "name": "weighted_gram_slack_domination",
          "file": "Komlos/Resolvent.lean",
          "line": 178
        },
        {
          "name": "slack_solution_nonneg",
          "file": "Komlos/MatrixInverse.lean",
          "line": 32
        },
        {
          "name": "slack_inverse_entrywise_nonneg",
          "file": "Komlos/MatrixInverse.lean",
          "line": 79
        },
        {
          "name": "resolvent_equation",
          "file": "Komlos/MatrixInverse.lean",
          "line": 94
        },
        {
          "name": "resolventVector_pos",
          "file": "Komlos/MatrixInverse.lean",
          "line": 115
        },
        {
          "name": "resolventVector_entrywise_mono",
          "file": "Komlos/MatrixInverse.lean",
          "line": 148
        },
        {
          "name": "resolventPotential_entrywise_mono",
          "file": "Komlos/MatrixInverse.lean",
          "line": 161
        },
        {
          "name": "resolventVector_comparison_with_guard",
          "file": "Komlos/MatrixInverse.lean",
          "line": 177
        },
        {
          "name": "slackMatrix_principal_posDef",
          "file": "Komlos/MatrixInverse.lean",
          "line": 208
        },
        {
          "name": "resolventVector_principal_le",
          "file": "Komlos/MatrixInverse.lean",
          "line": 214
        },
        {
          "name": "resolventPotential_eq_sum_excess",
          "file": "Komlos/MatrixInverse.lean",
          "line": 231
        },
        {
          "name": "resolventPotential_barrier_antitone",
          "file": "Komlos/MatrixInverse.lean",
          "line": 262
        },
        {
          "name": "slack_posDef_of_positive_supersolution",
          "file": "Komlos/MatrixInverse.lean",
          "line": 289
        },
        {
          "name": "anchor_guard_sound",
          "file": "Komlos/MatrixInverse.lean",
          "line": 317
        },
        {
          "name": "resolvent_vector_relative_change",
          "file": "Komlos/MatrixInverse.lean",
          "line": 338
        },
        {
          "name": "resolvent_vector_relative_bounds",
          "file": "Komlos/MatrixInverse.lean",
          "line": 361
        }
      ],
      "status": "done"
    },
    {
      "id": "resstab",
      "kind": "result",
      "tier": 4,
      "order": 0.4,
      "label": "Resolvent stability (B.5)",
      "sub": "ResolventStability.lean",
      "decls": [
        "resolvent_vector_diff_eq",
        "resolvent_vector_stability_correction",
        "resolvent_vector_stability",
        "resolvent_vector_stability_rel",
        "weighted_gram_qf_perturbation",
        "slackQuadratic_sub_eq",
        "slackQuadratic_stability"
      ],
      "notes": "Entrywise/quadratic-form level of the (B.5) displacement chain: vx \u2212 v\u2080 = Ax\u207b\u00b9*\u1d65((Mx\u2212M\u2080)v\u2080), relative-error correction bounds, and slack-form stability Ax[h] \u2265 (1\u2212\u03b5\u03ba)\u00b7A\u2080[h] under relative weight perturbations.",
      "resolved": [
        {
          "name": "resolvent_vector_diff_eq",
          "file": "Komlos/ResolventStability.lean",
          "line": 31
        },
        {
          "name": "resolvent_vector_stability_correction",
          "file": "Komlos/ResolventStability.lean",
          "line": 65
        },
        {
          "name": "resolvent_vector_stability",
          "file": "Komlos/ResolventStability.lean",
          "line": 112
        },
        {
          "name": "resolvent_vector_stability_rel",
          "file": "Komlos/ResolventStability.lean",
          "line": 171
        },
        {
          "name": "weighted_gram_qf_perturbation",
          "file": "Komlos/ResolventStability.lean",
          "line": 279
        },
        {
          "name": "slackQuadratic_sub_eq",
          "file": "Komlos/ResolventStability.lean",
          "line": 298
        },
        {
          "name": "slackQuadratic_stability",
          "file": "Komlos/ResolventStability.lean",
          "line": 316
        }
      ],
      "status": "done"
    },
    {
      "id": "anchordim",
      "kind": "result",
      "tier": 4,
      "order": 0.6,
      "label": "Anchor dimension bookkeeping",
      "sub": "AnchorDimension.lean",
      "decls": [
        "finrank_inf_ge_add_sub",
        "finrank_inf_inf_inf_inf_ge",
        "finrank_inf_inf_inf_inf_ge_real",
        "finrank_finset_inf_ge",
        "finrank_intersection_ge_of_codim_bounds",
        "finrank_intersection_ge_of_theta_bounds",
        "anchor_subspace_of_intersection"
      ],
      "notes": "Codimension accounting for the anchor subspace: each intersection loses at most n dimensions, so five large subspaces (\u03b8\u1d62\u00b7n codim) intersect in dimension \u2265 n \u2212 (\u2211\u03b8\u1d62)\u00b7n. Supplies the dimension side of the anchor construction.",
      "resolved": [
        {
          "name": "finrank_inf_ge_add_sub",
          "file": "Komlos/AnchorDimension.lean",
          "line": 14
        },
        {
          "name": "finrank_inf_inf_inf_inf_ge",
          "file": "Komlos/AnchorDimension.lean",
          "line": 52
        },
        {
          "name": "finrank_inf_inf_inf_inf_ge_real",
          "file": "Komlos/AnchorDimension.lean",
          "line": 39
        },
        {
          "name": "finrank_finset_inf_ge",
          "file": "Komlos/AnchorDimension.lean",
          "line": 67
        },
        {
          "name": "finrank_intersection_ge_of_codim_bounds",
          "file": "Komlos/AnchorDimension.lean",
          "line": 82
        },
        {
          "name": "finrank_intersection_ge_of_theta_bounds",
          "file": "Komlos/AnchorDimension.lean",
          "line": 96
        },
        {
          "name": "anchor_subspace_of_intersection",
          "file": "Komlos/AnchorDimension.lean",
          "line": 112
        }
      ],
      "status": "done"
    },
    {
      "id": "nonpos",
      "kind": "result",
      "tier": 4,
      "order": 0.5,
      "label": "Nonpositive subspace (B.4)",
      "sub": "NonpositiveSubspace.lean",
      "decls": [
        "posSemidef_eq_zero_of_diag_eq_zero",
        "exists_nonpositive_subspace_of_trace"
      ],
      "notes": "Unconditional spectral-counting lemma: if Q\u2c7c\u2c7c \u2264 \u03b8\u00b7D\u2c7c\u2c7c then Q\u2212D is nonpositive on a subspace of dimension \u2265 n\u2212\u03b8n, built from eigenvectors of D\u207b\u00b9\u141f\u00b2QD\u207b\u00b9\u141f\u00b2. Supplies the E\u2080 needed by spectral_subspace_exists.",
      "resolved": [
        {
          "name": "posSemidef_eq_zero_of_diag_eq_zero",
          "file": "Komlos/NonpositiveSubspace.lean",
          "line": 19
        },
        {
          "name": "exists_nonpositive_subspace_of_trace",
          "file": "Komlos/NonpositiveSubspace.lean",
          "line": 41
        }
      ],
      "status": "done"
    },
    {
      "id": "curv",
      "kind": "result",
      "tier": 4,
      "order": 1,
      "label": "Weight & curvature stability",
      "sub": "Curvature.lean",
      "decls": [
        "hasDerivAt_weight",
        "weightDeriv_nonneg",
        "weightDeriv2_pos",
        "weight_relative_change",
        "weight_abs_change",
        "weightDeriv_abs_change",
        "weightDeriv2_abs_change",
        "one_sub_inv_pow_le_exp",
        "differentiableAt_inv_entry",
        "hasDerivAt_inv_entry_add_smul",
        "hasDerivAt_resolvent_inv_sum"
      ],
      "resolved": [
        {
          "name": "hasDerivAt_weight",
          "file": "Komlos/Curvature.lean",
          "line": 28
        },
        {
          "name": "weightDeriv_nonneg",
          "file": "Komlos/Curvature.lean",
          "line": 60
        },
        {
          "name": "weightDeriv2_pos",
          "file": "Komlos/Curvature.lean",
          "line": 68
        },
        {
          "name": "weight_relative_change",
          "file": "Komlos/Curvature.lean",
          "line": 128
        },
        {
          "name": "weight_abs_change",
          "file": "Komlos/Curvature.lean",
          "line": 285
        },
        {
          "name": "weightDeriv_abs_change",
          "file": "Komlos/Curvature.lean",
          "line": 302
        },
        {
          "name": "weightDeriv2_abs_change",
          "file": "Komlos/Curvature.lean",
          "line": 326
        },
        {
          "name": "one_sub_inv_pow_le_exp",
          "file": "Komlos/Curvature.lean",
          "line": 105
        },
        {
          "name": "differentiableAt_inv_entry",
          "file": "Komlos/Curvature.lean",
          "line": 405
        },
        {
          "name": "hasDerivAt_inv_entry_add_smul",
          "file": "Komlos/Curvature.lean",
          "line": 422
        },
        {
          "name": "hasDerivAt_resolvent_inv_sum",
          "file": "Komlos/Curvature.lean",
          "line": 517
        }
      ],
      "status": "done"
    },
    {
      "id": "gauss_mom",
      "kind": "result",
      "tier": 4,
      "order": 2,
      "label": "Gaussian moments & small-ball",
      "sub": "GaussianMoments.lean",
      "decls": [
        "gaussianReal_integral_pow_two_mul",
        "gaussianReal_integral_sq",
        "gaussianReal_integral_id",
        "gaussianReal_integral_exp_mul_sq",
        "gaussianReal_integral_exp_mul_sq_rpow",
        "gaussianReal_Icc_le",
        "gaussianReal_real_Icc_le"
      ],
      "resolved": [
        {
          "name": "gaussianReal_integral_pow_two_mul",
          "file": "Komlos/GaussianMoments.lean",
          "line": 63
        },
        {
          "name": "gaussianReal_integral_sq",
          "file": "Komlos/GaussianMoments.lean",
          "line": 78
        },
        {
          "name": "gaussianReal_integral_id",
          "file": "Komlos/GaussianMoments.lean",
          "line": 88
        },
        {
          "name": "gaussianReal_integral_exp_mul_sq",
          "file": "Komlos/GaussianMoments.lean",
          "line": 95
        },
        {
          "name": "gaussianReal_integral_exp_mul_sq_rpow",
          "file": "Komlos/GaussianMoments.lean",
          "line": 120
        },
        {
          "name": "gaussianReal_Icc_le",
          "file": "Komlos/GaussianMoments.lean",
          "line": 142
        },
        {
          "name": "gaussianReal_real_Icc_le",
          "file": "Komlos/GaussianMoments.lean",
          "line": 174
        }
      ],
      "status": "done"
    },
    {
      "id": "gcomplete",
      "kind": "result",
      "tier": 4,
      "order": 3,
      "label": "QF / Loewner bounds",
      "sub": "GaussianCompletion.lean",
      "decls": [
        "qfLower_posDef",
        "qfLower_inv_le",
        "qfLower_inv_ge",
        "qfLower_submatrix",
        "qfUpper_submatrix",
        "gram_whiten",
        "gram_whiten_symm"
      ],
      "resolved": [
        {
          "name": "qfLower_posDef",
          "file": "Komlos/GaussianCompletion.lean",
          "line": 30
        },
        {
          "name": "qfLower_inv_le",
          "file": "Komlos/GaussianCompletion.lean",
          "line": 36
        },
        {
          "name": "qfLower_inv_ge",
          "file": "Komlos/GaussianCompletion.lean",
          "line": 70
        },
        {
          "name": "qfLower_submatrix",
          "file": "Komlos/GaussianCompletion.lean",
          "line": 235
        },
        {
          "name": "qfUpper_submatrix",
          "file": "Komlos/GaussianCompletion.lean",
          "line": 244
        },
        {
          "name": "gram_whiten",
          "file": "Komlos/GaussianCompletion.lean",
          "line": 253
        },
        {
          "name": "gram_whiten_symm",
          "file": "Komlos/GaussianCompletion.lean",
          "line": 260
        }
      ],
      "status": "done"
    },
    {
      "id": "mathlib",
      "kind": "external",
      "tier": 5,
      "order": 0,
      "label": "Mathlib4 v4.34.1",
      "sub": "external library",
      "notes": "Linear algebra, measure/probability theory, calculus and matrix analysis imported as-is.",
      "decls": [],
      "resolved": [],
      "status": "external"
    },
    {
      "id": "axioms",
      "kind": "external",
      "tier": 5,
      "order": 1,
      "label": "Lean axioms",
      "sub": "propext \u00b7 choice \u00b7 Quot.sound",
      "notes": "The three foundational axioms permitted by the audit. No sorry, no custom axioms, no native_decide.",
      "decls": [],
      "resolved": [],
      "status": "external"
    },
    {
      "id": "audit",
      "kind": "audit",
      "tier": 5,
      "order": 2,
      "label": "Axiom audit gate",
      "sub": "KomlosAudit.lean",
      "notes": "Traverses every Komlos theorem's dependency closure and rejects anything beyond propext / Classical.choice / Quot.sound.",
      "decls": [],
      "resolved": [],
      "status": "done"
    }
  ],
  "edges": [
    [
      "disc",
      "thm11"
    ],
    [
      "runtime",
      "thm11"
    ],
    [
      "stmt",
      "thm11"
    ],
    [
      "propA1",
      "disc"
    ],
    [
      "gauss_inv",
      "disc"
    ],
    [
      "conc",
      "gauss_inv"
    ],
    [
      "gaussinvariant",
      "conc"
    ],
    [
      "walk",
      "propA1"
    ],
    [
      "concave",
      "propA1"
    ],
    [
      "rows",
      "propA1"
    ],
    [
      "spectral",
      "propA1"
    ],
    [
      "idischarge",
      "propA1"
    ],
    [
      "resolv",
      "spectral"
    ],
    [
      "curv",
      "spectral"
    ],
    [
      "nonpos",
      "spectral"
    ],
    [
      "resstab",
      "spectral"
    ],
    [
      "anchordim",
      "spectral"
    ],
    [
      "init",
      "propA1"
    ],
    [
      "gauss_cond",
      "gauss_inv"
    ],
    [
      "density_d5",
      "gauss_inv"
    ],
    [
      "sphere_measure",
      "gauss_inv"
    ],
    [
      "gcomplete",
      "gauss_cond"
    ],
    [
      "gauss_mom",
      "density_d5"
    ],
    [
      "gauss_mom",
      "conc"
    ],
    [
      "conc_finite",
      "conc"
    ],
    [
      "conc_markov",
      "conc"
    ],
    [
      "dyninv",
      "runtime"
    ],
    [
      "dither",
      "runtime"
    ],
    [
      "bitmodel",
      "runtime"
    ],
    [
      "algcost",
      "runtime"
    ],
    [
      "invblock",
      "dyninv"
    ],
    [
      "rankone",
      "dyninv"
    ],
    [
      "cont",
      "dyninv"
    ],
    [
      "prec",
      "dither"
    ],
    [
      "mathlib",
      "resolv"
    ],
    [
      "mathlib",
      "gauss_cond"
    ],
    [
      "mathlib",
      "spectral"
    ],
    [
      "axioms",
      "audit"
    ]
  ],
  "stats": {
    "counts": {
      "done": 20,
      "conditional": 13,
      "partial": 0,
      "missing": 2,
      "external": 2
    },
    "declarations": 1301,
    "files": {
      "Komlos/AlgorithmCost.lean": {
        "decls": 27,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/AnchorDimension.lean": {
        "decls": 12,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/AnchorUpdate.lean": {
        "decls": 104,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/CompletionSampler.lean": {
        "decls": 17,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/ConcaveStep.lean": {
        "decls": 5,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/ConcentrationMarkov.lean": {
        "decls": 5,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/Curvature.lean": {
        "decls": 27,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/CurvatureGeneral.lean": {
        "decls": 6,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/DensityD5.lean": {
        "decls": 50,
        "sorry": false,
        "axioms": [],
        "audited": false
      },
      "Komlos/DiscrepancyReduction.lean": {
        "decls": 2,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/DynamicMaintenance.lean": {
        "decls": 37,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/EpochBound.lean": {
        "decls": 18,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/FinitePrecision.lean": {
        "decls": 47,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/FiniteRounding.lean": {
        "decls": 67,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/GaussianCompletion.lean": {
        "decls": 14,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/GaussianDensity.lean": {
        "decls": 39,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/GaussianDisintegration.lean": {
        "decls": 16,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/GaussianInvariant.lean": {
        "decls": 44,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/GaussianMoments.lean": {
        "decls": 8,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/HessianDecomposition.lean": {
        "decls": 42,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/InitializationMargin.lean": {
        "decls": 8,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/InterfaceDischarge.lean": {
        "decls": 46,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/InverseMaintenanceBlock.lean": {
        "decls": 9,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/InverseUpdate.lean": {
        "decls": 10,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/MatrixInverse.lean": {
        "decls": 35,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/NonpositiveSubspace.lean": {
        "decls": 2,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/PotentialConcavity.lean": {
        "decls": 5,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/RandomizedCoupling.lean": {
        "decls": 59,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/Resolvent.lean": {
        "decls": 16,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/ResolventContinuity.lean": {
        "decls": 15,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/ResolventStability.lean": {
        "decls": 20,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/RowBoundA2.lean": {
        "decls": 13,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/Runtime.lean": {
        "decls": 33,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/RuntimeBound.lean": {
        "decls": 16,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/SpectralDimension.lean": {
        "decls": 60,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/SpectralPath.lean": {
        "decls": 25,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/SphereMeasure.lean": {
        "decls": 54,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/StabilityTransport.lean": {
        "decls": 41,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/SubGaussianBound.lean": {
        "decls": 24,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/Theorem11Assembly.lean": {
        "decls": 13,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/TrialConcentration.lean": {
        "decls": 43,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/UniformSphere.lean": {
        "decls": 54,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/Walk.lean": {
        "decls": 29,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "Komlos/WalkCoins.lean": {
        "decls": 30,
        "sorry": false,
        "axioms": [],
        "audited": false
      },
      "Komlos.lean": {
        "decls": 55,
        "sorry": false,
        "axioms": [],
        "audited": true
      },
      "KomlosAudit.lean": {
        "decls": 0,
        "sorry": false,
        "axioms": [],
        "audited": true
      }
    },
    "auditedFiles": [
      "Komlos.lean",
      "Komlos/AlgorithmCost.lean",
      "Komlos/AnchorDimension.lean",
      "Komlos/AnchorUpdate.lean",
      "Komlos/CompletionSampler.lean",
      "Komlos/ConcaveStep.lean",
      "Komlos/ConcentrationMarkov.lean",
      "Komlos/Curvature.lean",
      "Komlos/CurvatureGeneral.lean",
      "Komlos/DiscrepancyReduction.lean",
      "Komlos/DynamicMaintenance.lean",
      "Komlos/EpochBound.lean",
      "Komlos/FinitePrecision.lean",
      "Komlos/FiniteRounding.lean",
      "Komlos/GaussianCompletion.lean",
      "Komlos/GaussianDensity.lean",
      "Komlos/GaussianDisintegration.lean",
      "Komlos/GaussianInvariant.lean",
      "Komlos/GaussianMoments.lean",
      "Komlos/HessianDecomposition.lean",
      "Komlos/InitializationMargin.lean",
      "Komlos/InterfaceDischarge.lean",
      "Komlos/InverseMaintenanceBlock.lean",
      "Komlos/InverseUpdate.lean",
      "Komlos/MatrixInverse.lean",
      "Komlos/NonpositiveSubspace.lean",
      "Komlos/PotentialConcavity.lean",
      "Komlos/RandomizedCoupling.lean",
      "Komlos/Resolvent.lean",
      "Komlos/ResolventContinuity.lean",
      "Komlos/ResolventStability.lean",
      "Komlos/RowBoundA2.lean",
      "Komlos/Runtime.lean",
      "Komlos/RuntimeBound.lean",
      "Komlos/SpectralDimension.lean",
      "Komlos/SpectralPath.lean",
      "Komlos/SphereMeasure.lean",
      "Komlos/StabilityTransport.lean",
      "Komlos/SubGaussianBound.lean",
      "Komlos/Theorem11Assembly.lean",
      "Komlos/TrialConcentration.lean",
      "Komlos/UniformSphere.lean",
      "Komlos/Walk.lean",
      "KomlosAudit.lean"
    ],
    "lastAudit": {
      "declarations": 1517,
      "allowedAxioms": [
        "propext",
        "Classical.choice",
        "Quot.sound"
      ],
      "command": "lake env lean -DwarningAsError=true KomlosAudit.lean",
      "ranAt": "2026-10-14",
      "note": "lake build succeeded (3851 jobs); audit reported 1517 theorem declarations with only permitted axioms"
    }
  }
};
