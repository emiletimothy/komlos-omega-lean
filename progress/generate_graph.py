#!/usr/bin/env python3
"""Regenerate progress/graph_data.json from the Lean sources.

Scans every project .lean file (excluding .lake), extracts top-level
declarations, detects `sorry`/`admit`/`axiom`/`native_decide`, computes the
import closure audited by KomlosAudit.lean, and resolves the status of each
node in the proof-progress manifest below.

Usage:
    python3 progress/generate_graph.py            # one-shot
    python3 progress/generate_graph.py --watch    # regenerate when sources change

Statuses:
    done        all mapped declarations exist in files inside the audited
                import closure, with no sorry/admit/axiom/native_decide
    conditional like `done`, but the result is proved only modulo hypotheses
                that have not been discharged (flagged in the manifest)
    partial     declarations exist but some are missing, or their files are
                outside the audited closure / contain forbidden tokens
    missing     the component is not formalized at all
    external    Mathlib / Lean-foundation results used as-is (shaded green)
"""

from __future__ import annotations

import json
import re
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HERE = Path(__file__).resolve().parent
OUT = HERE / "graph_data.json"
OUT_JS = HERE / "graph_data.js"
AUDIT_FILE = HERE / "last_audit.json"
# Optional: {"failed": ["Komlos/Foo.lean", ...]} written after a `lake build`
# to downgrade nodes whose files did not compile.
BUILD_FILE = HERE / "build_state.json"

DECL_RE = re.compile(
    r"^(?:theorem|lemma|def|structure|instance|abbrev|inductive)\s+([\w'.]+)"
    r"|^noncomputable\s+def\s+([\w'.]+)",
    re.M,
)
IMPORT_RE = re.compile(r"^import\s+(Komlos[\w.]*)", re.M)
SORRY_RE = re.compile(r"\bsorry\b|\badmit\b|\bproof_wanted\b|\bnative_decide\b")
AXIOM_RE = re.compile(r"^axiom\s+([\w'.]+)", re.M)

# ---------------------------------------------------------------------------
# Proof-progress manifest.
#
# kind:
#   milestone  status rolled up from its supporters (nodes with edges into it)
#   result     status resolved from `decls`
#   gap        known-missing component (red)
#   external   Mathlib / Lean foundations, used as-is (shaded green)
#   audit      the axiom-audit gate itself
#
# tier: vertical layer (0 = top). order: horizontal order within the tier.
# ---------------------------------------------------------------------------

NODES = [
    # -- top -------------------------------------------------------------
    dict(id="thm11", kind="milestone", tier=0, order=0,
         label="Theorem 1.1",
         sub="Komlós conjecture",
         notes="Signing of a column-normalized matrix with discrepancy < 100, "
               "certified in near matrix-multiplication expected time. "
               "Not yet proved end-to-end."),

    # -- tier 1: the two halves + the formalized statement ----------------
    dict(id="stmt", kind="result", tier=1, order=0,
         label="Statement + verifier",
         sub="Thm 1.1 Prop · rational checker",
         decls=["DiscrepancyPartOfTheorem11", "IsSigning", "HasDiscrepancyBelow",
                "verifySigning", "verifySigning_sound", "verify_zero_matrix",
                "verify_accepts_below_threshold", "verify_rejects_at_threshold",
                "realSigning_isSigning", "input_rounding_error",
                "accepted_output_sound"],
         notes="The discrepancy proposition is stated and an exact rational "
               "signing checker is proved sound. This formalizes the *claim*, "
               "not its proof."),
    dict(id="disc", kind="milestone", tier=1, order=1,
         label="Discrepancy bound < 100",
         sub="existence half",
         notes="Every row of the produced signing stays below the 100 "
               "threshold. A conditional assembly exists "
               "(DiscrepancyPartOfTheorem11_of_walkSuccess); the "
               "12-field walk-success hypothesis is still open."),
    dict(id="runtime", kind="milestone", tier=1, order=2,
         label="Runtime ≈ n^ω bit ops",
         sub="efficiency half",
         notes="Expected bit-complexity bound for the whole algorithm. "
               "RuntimeBound.lean proves a *conditional* version for "
               "`WellScaled` cost models, and refutes the naive "
               "universally-quantified statement via a badly-scaled "
               "countermodel."),

    # -- tier 2: discrepancy children -------------------------------------
    dict(id="propA1", kind="result", tier=2, order=0, conditional=True,
         label="Prop A.1 reduction",
         sub="deterministic + walk assembly",
         decls=["deterministic_discrepancy_reduction", "discrepancy_below_99",
                "WalkSuccessInput", "exists_signing_discrepancy_below_99",
                "DiscrepancyPartOfTheorem11_of_walkSuccess"],
         notes="Conditional: `discrepancy_below_99` derives the < 99 "
               "max-bound from per-row hypotheses, and "
               "Theorem11Assembly packages them into a 12-field "
               "`WalkSuccessInput` proving the existence half modulo "
               "walk success. Discharging that structure is the "
               "remaining surface."),
    dict(id="gauss_inv", kind="result", tier=2, order=1, conditional=True,
         label="Adaptive Gaussian invariant",
         sub="App. C/D · uniformity half done",
         decls=["dirRV_equivariance", "ae_dirRV_equivariance",
                "dirRV_law_invariant", "dirRV_law_neg", "dirRV_law_uniform",
                "measurePreserving_stabSourceMap",
                "dirRVUniformStatement_holds"],
         notes="The distributional half of Thm 4.1 now exists: "
               "UniformSphere.lean proves stabilizer invariance, "
               "equivariance, sign decoupling and range support of the "
               "completion-direction law (`dirRV` pushforward is "
               "orthogonal-invariant — the uniform-sphere surrogate). "
               "Still missing: the per-iteration concentration bounds "
               "(4.4)/(D.5) and the adaptive filtration."),
    dict(id="conc", kind="gap", tier=2, order=2,
         label="Adaptive trial concentration",
         sub="missing",
         notes="Concentration for the *adaptive Gaussian* trials. Only a "
               "finite uniform sign-model version exists so far."),
    dict(id="dyninv", kind="result", tier=2, order=3, conditional=True,
         label="Fast dynamic inverse",
         sub="DynamicMaintenance.lean",
         decls=["DynamicInverseState", "update_A", "update_Inv",
                "updateCol_A", "maintenanceTotalOps",
                "maintenanceTotalOps_le"],
         notes="Abstract Sherman–Morrison/state model: certificate "
               "preservation across updates and an amortized "
               "`maintenanceTotalOps_le` cost bound inside the bit-cost "
               "envelope. The concrete algorithmic implementation is "
               "still an abstract hypothesis."),
    dict(id="dither", kind="result", tier=2, order=4, conditional=True,
         label="Randomized dither coupling",
         sub="RandomizedCoupling.lean · finite model",
         decls=["unifAvg_ditherErr_sq", "unifAvg_ditherErr_sq_le",
                "unifAvg_ditherWalk_conditional", "ditherWalk_tail_le",
                "unifAvg_transcriptDrift", "transcriptDrift_sq_le",
                "transcriptDrift_tail_le"],
         notes="Finite uniform model: unbiased dithered rounding, "
               "p(1−p) variance identity, `incSum` martingale recursion "
               "and Markov tail bounds for transcript drift. The "
               "paper's full filtration/coupling to the adaptive "
               "Gaussian walk is still a hypothesis."),
    dict(id="bitmodel", kind="result", tier=2, order=5,
         label="Bit-cost vocabulary",
         sub="Runtime.lean",
         decls=["natBitSize", "ratBitSize", "inputBitSize", "BitCostModel",
                "BitCostModel.quadratic", "verificationBitCost",
                "runtimeEnvelope", "DiscrepancyRuntimeBound",
                "Theorem11WithRuntime"],
         notes="Bit sizes, abstract ω, operation costs and the runtime "
               "envelope are *defined*. The bound itself is unproven."),

    # -- tier 3: support lemmas -------------------------------------------
    dict(id="walk", kind="result", tier=3, order=0,
         label="Symmetric walk accounting",
         sub="Walk.lean",
         decls=["energy_accounting", "terminal_energy_bound",
                "squared_move_budget", "large_move_cost_bound",
                "full_step_count_bound", "terminal_average_bound",
                "terminal_average_le_root", "marked_progress_accounting",
                "marked_step_count_bound", "symmetric_boundary_hit",
                "clipped_endpoint_hits_boundary",
                "symmetric_endpoints_in_cube"]),
    dict(id="concave", kind="result", tier=3, order=1, conditional=True,
         label="Per-step concavity",
         sub="ConcaveStep.lean",
         decls=["concaveOn_pair_average_le", "concaveOn_branch_average_le",
                "localAverageNonincrease_of_branchConcave",
                "terminal_average_le_root_of_branchConcave"],
         notes="Conditional: branch concavity of the resolvent potential is "
               "taken as a `ConcaveOn` hypothesis; the analytic Hessian "
               "argument is not yet formalized."),
    dict(id="spectral", kind="result", tier=3, order=2, conditional=True,
         label="Spectral dim. & stability",
         sub="App. B · SpectralDimension.lean",
         decls=["resolvent_step_eq", "resolventPotential_step",
                "resolventPotential_step_taylor",
                "resolventPotential_symmetric_difference",
                "resolventVariation1_batch",
                "resolvent_vector_batch_relative_bounds",
                "resolventPotential_batch_change", "weight_abs_sub_le",
                "udiag_curvature_le", "curvature_drift_le",
                "light_gram_resolvent_form_le", "large_row_count",
                "nearly_tight_row_count", "four_loss_card",
                "spectral_dimension_margin", "finrank_inf_ker_constraintMap_ge",
                "spectral_subspace_exists", "spectral_subspace_dimension",
                "hasDerivAt_resolventPotential", "hasDerivAt_potentialSlope"],
         notes="Batch perturbation, potential Taylor identities, curvature "
               "comparisons and constraint-kernel dimension bookkeeping. "
               "`spectral_subspace_exists` is conditional: it takes a good "
               "subspace E₀ as a hypothesis — that construction exists "
               "unconditionally in NonpositiveSubspace.lean, and "
               "StabilityTransport.lean adds the (B.5)–(B.10) "
               "displacement bounds. All audited."),
    dict(id="rows", kind="result", tier=3, order=3,
         label="Row & barrier estimates",
         sub="Komlos.lean",
         decls=["discarded_row_bound", "normalized_entry_abs_le_one",
                "total_mass_le_dimension", "retained_row_count",
                "small_dimension_signing", "deletion_charge",
                "deletion_constant_bound", "final_constant_margin",
                "live_row_count", "completed_row_error_bound",
                "deleted_defect_bound", "total_deleted_coefficient_bound",
                "protected_signs_exclusive", "barrier_pair_sum",
                "barriers_control_abs_value", "protected_barrier_nonincrease",
                "spread_gradient_bound", "curvature_dimension_margin",
                "affine_history_defect", "sqrt63_lt"]),
    dict(id="init", kind="result", tier=3, order=3.5,
         label="Initialization margin (A.2)",
         sub="InitializationMargin.lean",
         decls=["termSeq_partial_sum_lower", "termSeq_partial_sum_lower_real",
                "initialization_margin", "barrier_at_Rmax",
                "weight_at_barrier_Rmax", "row_weight_bound_at_Rmax"],
         notes="Certifies (1+733/727500)^10000 > 23634 via a kernel-checked "
               "rational partial sum, giving the (A.2) row bound "
               "2ν(16−H₀/Rmax)/Rmax² ≤ (1000/1009)·bdep."),
    dict(id="gauss_cond", kind="result", tier=3, order=4,
         label="Gaussian disintegration",
         sub="App. D · conditional law",
         decls=["stdGaussian_eq_prod_map_add",
                "stdGaussian_map_orthogonalProjectionOnto_prod",
                "gaussLift", "gaussLift_lifting", "gaussCondKernel",
                "stdGaussian_map_prodMk_compProd",
                "stdGaussian_eq_prod_map_add_gaussLift"],
         notes="Regular conditional law of a standard Gaussian under a "
               "continuous linear map: Law(LZ,Z) = Law(LZ) ⊗ₘ kernel, with "
               "shifted standard Gaussian on ker L."),
    dict(id="density_d5", kind="gap", tier=3, order=5,
         label="Explicit density (D.5)",
         sub="Gram Jacobian · Wishart",
         notes="The explicit conditional density formula, Gram-map/QR "
               "Jacobian and Wishart-density calculations remain open."),
    dict(id="conc_finite", kind="result", tier=3, order=6,
         label="Finite sign-model concentration",
         sub="TrialConcentration.lean",
         decls=["signAvg_rowValue_sq", "signAvg_sum_rowValue_sq_le",
                "sum_badRowCount_le", "exists_signing_few_bad_rows",
                "row_tail_fraction_le", "exists_in_support_few_bad_rows",
                "terminalAverage_cubeTop",
                "exists_memLeaf_signing_few_bad_rows"],
         notes="Uniform model over Fin n → Bool: second-moment identities, "
               "Markov bad-row counting, and a bridge to SymmetricWalk. "
               "Not the adaptive Gaussian tails the paper needs."),
    dict(id="invblock", kind="result", tier=3, order=7,
         label="Block inverse update",
         sub="Eq. 4.5 · InverseMaintenanceBlock",
         decls=["augmentedMatrix", "augmentedMatrix_inv",
                "augmentedMatrix_inv_mulVec", "frobenius_norm_sq_fromBlocks",
                "augmentedMatrix_inv_norm_sq_le"]),
    dict(id="rankone", kind="result", tier=3, order=8,
         label="Rank-one inverse updates",
         sub="Sherman–Morrison · InverseUpdate",
         decls=["sherman_morrison", "sherman_morrison_col",
                "frobenius_norm_sq_vecMulVec", "det_one_add_vecMulVec",
                "det_add_vecMulVec"]),
    dict(id="cont", kind="result", tier=3, order=9,
         label="Resolvent continuity",
         sub="ResolventContinuity.lean",
         decls=["continuousAt_slack_inv", "isUnit_slackMatrix_of_posDef",
                "continuousAt_slack_inv_quadratic", "posDef_eventually",
                "posDef_slackMatrix_eventually_add_smul",
                "posDef_slackMatrix_eventually_quadratic"]),
    dict(id="prec", kind="result", tier=3, order=10,
         label="Finite-precision transcript",
         sub="FinitePrecision.lean",
         decls=["roundToGrid", "abs_sub_roundToGrid", "roundEntrywise",
                "verifyRounded_sound", "verifySigning_rounded_sound",
                "soundness_precision_suffices", "step_coupling_bound",
                "transcript_drift_bound", "coupled_affine_transcript_drift",
                "coupled_deleted_drift", "energy_drift_bound",
                "barrier_drift_bound", "rounded_transcript_drift"],
         notes="Deterministic rational-grid rounding, verification "
               "soundness, and transcript drift/coupling bounds."),

    # -- tier 4: deeper support -------------------------------------------
    dict(id="resolv", kind="result", tier=4, order=0,
         label="Resolvent machinery",
         sub="Resolvent + MatrixInverse",
         decls=["weight_pos", "weight_mono", "weight_le_119",
                "protected_weight_majorant", "ground_state_identity",
                "ground_state_identity_with_rhs",
                "ground_state_lower_bound", "weighted_rank_one_domination",
                "weighted_gram_slack_domination", "slack_solution_nonneg",
                "slack_inverse_entrywise_nonneg", "resolvent_equation",
                "resolventVector_pos", "resolventVector_entrywise_mono",
                "resolventPotential_entrywise_mono",
                "resolventVector_comparison_with_guard",
                "slackMatrix_principal_posDef",
                "resolventVector_principal_le",
                "resolventPotential_eq_sum_excess",
                "resolventPotential_barrier_antitone",
                "slack_posDef_of_positive_supersolution",
                "anchor_guard_sound", "resolvent_vector_relative_change",
                "resolvent_vector_relative_bounds"]),
    dict(id="nonpos", kind="result", tier=4, order=0.5,
         label="Nonpositive subspace (B.4)",
         sub="NonpositiveSubspace.lean",
         decls=["posSemidef_eq_zero_of_diag_eq_zero",
                "exists_nonpositive_subspace_of_trace"],
         notes="Unconditional spectral-counting lemma: if Qⱼⱼ ≤ θ·Dⱼⱼ then "
               "Q−D is nonpositive on a subspace of dimension ≥ n−θn, built "
               "from eigenvectors of D⁻¹ᐟ²QD⁻¹ᐟ². Supplies the E₀ needed by "
               "spectral_subspace_exists."),
    dict(id="curv", kind="result", tier=4, order=1,
         label="Weight & curvature stability",
         sub="Curvature.lean",
         decls=["hasDerivAt_weight", "weightDeriv_nonneg",
                "weightDeriv2_pos", "weight_relative_change",
                "weight_abs_change", "weightDeriv_abs_change",
                "weightDeriv2_abs_change", "one_sub_inv_pow_le_exp",
                "differentiableAt_inv_entry",
                "hasDerivAt_inv_entry_add_smul",
                "hasDerivAt_resolvent_inv_sum"]),
    dict(id="gauss_mom", kind="result", tier=4, order=2,
         label="Gaussian moments & small-ball",
         sub="GaussianMoments.lean",
         decls=["gaussianReal_integral_pow_two_mul",
                "gaussianReal_integral_sq", "gaussianReal_integral_id",
                "gaussianReal_integral_exp_mul_sq",
                "gaussianReal_integral_exp_mul_sq_rpow",
                "gaussianReal_Icc_le", "gaussianReal_real_Icc_le"]),
    dict(id="gcomplete", kind="result", tier=4, order=3,
         label="QF / Loewner bounds",
         sub="GaussianCompletion.lean",
         decls=["qfLower_posDef", "qfLower_inv_le", "qfLower_inv_ge",
                "qfLower_submatrix", "qfUpper_submatrix",
                "gram_whiten", "gram_whiten_symm"]),

    # -- tier 5: foundations ------------------------------------------------
    dict(id="mathlib", kind="external", tier=5, order=0,
         label="Mathlib4 v4.34.1",
         sub="external library",
         notes="Linear algebra, measure/probability theory, calculus and "
               "matrix analysis imported as-is."),
    dict(id="axioms", kind="external", tier=5, order=1,
         label="Lean axioms",
         sub="propext · choice · Quot.sound",
         notes="The three foundational axioms permitted by the audit. "
               "No sorry, no custom axioms, no native_decide."),
    dict(id="audit", kind="audit", tier=5, order=2,
         label="Axiom audit gate",
         sub="KomlosAudit.lean",
         notes="Traverses every Komlos theorem's dependency closure and "
               "rejects anything beyond propext / Classical.choice / "
               "Quot.sound."),
]

# edge (a, b) means "a supports b" — drawn with the arrowhead at b.
EDGES = [
    ("disc", "thm11"),
    ("runtime", "thm11"),
    ("stmt", "thm11"),

    ("propA1", "disc"),
    ("gauss_inv", "disc"),
    ("conc", "gauss_inv"),

    ("walk", "propA1"),
    ("concave", "propA1"),
    ("rows", "propA1"),
    ("spectral", "propA1"),
    ("resolv", "spectral"),
    ("curv", "spectral"),
    ("nonpos", "spectral"),
    ("init", "propA1"),

    ("gauss_cond", "gauss_inv"),
    ("density_d5", "gauss_inv"),
    ("gcomplete", "gauss_cond"),
    ("gauss_mom", "density_d5"),
    ("gauss_mom", "conc"),
    ("conc_finite", "conc"),

    ("dyninv", "runtime"),
    ("dither", "runtime"),
    ("bitmodel", "runtime"),
    ("invblock", "dyninv"),
    ("rankone", "dyninv"),
    ("cont", "dyninv"),
    ("prec", "dither"),

    ("mathlib", "resolv"),
    ("mathlib", "gauss_cond"),
    ("mathlib", "spectral"),
    ("axioms", "audit"),
]

SEVERITY = {"done": 0, "conditional": 1, "partial": 2, "missing": 3,
            "external": -1}


def scan_sources() -> dict:
    """Return {decl_name: (file, line)} plus per-file diagnostics."""
    decls: dict[str, dict] = {}
    files: dict[str, dict] = {}
    for path in sorted(ROOT.rglob("*.lean")):
        rel = path.relative_to(ROOT).as_posix()
        if rel.startswith(".lake/"):
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        # strip comments for token checks
        stripped = re.sub(r"/-.*?-/", "", text, flags=re.S)
        stripped = re.sub(r"--[^\n]*", "", stripped)
        fdecls = []
        for m in DECL_RE.finditer(stripped):
            name = m.group(1) or m.group(2)
            line = stripped.count("\n", 0, m.start()) + 1
            decls[name] = {"file": rel, "line": line}
            fdecls.append(name)
        files[rel] = {
            "decls": fdecls,
            "sorry": bool(SORRY_RE.search(stripped)),
            "axioms": AXIOM_RE.findall(stripped),
            "imports": IMPORT_RE.findall(text),
        }
    return {"decls": decls, "files": files}


def audited_closure(files: dict) -> set[str]:
    """Modules reachable from KomlosAudit.lean (plus Komlos.lean itself)."""
    roots = {"KomlosAudit.lean", "Komlos.lean"}
    mod_of = {}
    for rel in files:
        if rel == "KomlosAudit.lean":
            mod_of["KomlosAudit"] = rel
        else:
            mod_of[rel[:-5].replace("/", ".")] = rel
    seen = set(roots)
    stack = [files[r]["imports"] for r in roots if r in files]
    stack = [m for imps in stack for m in imps]
    while stack:
        mod = stack.pop()
        rel = mod_of.get(mod)
        if rel and rel not in seen:
            seen.add(rel)
            stack.extend(files[rel]["imports"])
    return seen


def resolve(scanned: dict) -> dict:
    decls = scanned["decls"]
    files = scanned["files"]
    audited = audited_closure(files)
    failed: set[str] = set()
    if BUILD_FILE.exists():
        try:
            failed = set(json.loads(BUILD_FILE.read_text()).get("failed", []))
        except Exception:
            pass

    nodes = {n["id"]: dict(n) for n in NODES}
    for n in nodes.values():
        n.setdefault("decls", [])
        n["resolved"] = [
            {"name": d, **decls[d]} if d in decls else {"name": d, "file": None}
            for d in n["decls"]
        ]

    def own_status(n: dict) -> str:
        kind = n["kind"]
        if kind == "external":
            return "external"
        if kind in ("gap", "milestone"):
            return "missing" if kind == "gap" else ""
        if kind == "audit":
            return "done"
        found = [r for r in n["resolved"] if r["file"]]
        if not n["decls"]:
            return "missing"
        if len(found) < len(n["decls"]):
            return "partial" if found else "missing"
        bad = [r for r in found
               if files[r["file"]]["sorry"] or files[r["file"]]["axioms"]
               or r["file"] not in audited or r["file"] in failed]
        if bad:
            n["unaudited"] = sorted({r["file"] for r in bad})
            if any(r["file"] in failed for r in found):
                n["broken"] = True
            return "partial"
        return "conditional" if n.get("conditional") else "done"

    own = {nid: own_status(n) for nid, n in nodes.items()}

    supporters = {nid: [] for nid in nodes}
    for a, b in EDGES:
        supporters[b].append(a)

    def rollup(nid: str, seen: set) -> str:
        if nodes[nid]["kind"] != "milestone":
            return own[nid]
        if nid in seen:
            return "missing"
        seen = seen | {nid}
        worst = "done"
        for s in supporters[nid]:
            st = rollup(s, seen) if nodes[s]["kind"] == "milestone" else own[s]
            if SEVERITY[st] > SEVERITY[worst]:
                worst = st
        return worst

    for nid, n in nodes.items():
        n["status"] = rollup(nid, set())
        if n["kind"] == "milestone" and n["status"] == "external":
            n["status"] = "done"

    counts = {s: 0 for s in SEVERITY}
    for n in nodes.values():
        counts[n["status"]] += 1

    last_audit = None
    if AUDIT_FILE.exists():
        last_audit = json.loads(AUDIT_FILE.read_text())
    if failed:
        if last_audit is None:
            last_audit = {}
        last_audit["failedFiles"] = sorted(failed)

    return {
        "generated": time.strftime("%Y-%m-%d %H:%M:%S"),
        "nodes": [nodes[n["id"]] for n in NODES],
        "edges": EDGES,
        "stats": {
            "counts": counts,
            "declarations": len(decls),
            "files": {rel: {"decls": len(f["decls"]),
                            "sorry": f["sorry"],
                            "axioms": f["axioms"],
                            "audited": rel in audited}
                      for rel, f in files.items()},
            "auditedFiles": sorted(audited),
            "lastAudit": last_audit,
        },
    }


def lean_mtimes() -> dict[str, float]:
    return {p.as_posix(): p.stat().st_mtime
            for p in ROOT.rglob("*.lean") if ".lake" not in p.parts}


def emit() -> None:
    data = resolve(scan_sources())
    payload = json.dumps(data, indent=2)
    OUT.write_text(payload)
    OUT_JS.write_text("const EMBEDDED_GRAPH = " + payload + ";\n")
    c = data["stats"]["counts"]
    print(f"[{data['generated']}] wrote {OUT.name}: "
          f"{c['done']} done, {c['conditional']} conditional, "
          f"{c['partial']} partial, {c['missing']} missing, "
          f"{c['external']} external", flush=True)


def main() -> None:
    watch = "--watch" in sys.argv
    emit()
    if not watch:
        return
    prev = lean_mtimes()
    while True:
        time.sleep(10)
        cur = lean_mtimes()
        if cur != prev:
            prev = cur
            emit()


if __name__ == "__main__":
    main()
