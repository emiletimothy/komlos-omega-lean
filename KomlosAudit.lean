import Komlos.MatrixInverse
import Komlos.Walk
import Komlos.Curvature
import Komlos.InverseMaintenanceBlock
import Komlos.InverseUpdate
import Komlos.GaussianCompletion
import Komlos.GaussianDisintegration
import Komlos.GaussianMoments
import Komlos.SpectralDimension
import Komlos.TrialConcentration
import Komlos.ConcentrationMarkov
import Komlos.FinitePrecision
import Komlos.Runtime
import Komlos.RuntimeBound
import Komlos.DynamicMaintenance
import Komlos.ResolventContinuity
import Komlos.DiscrepancyReduction
import Komlos.ConcaveStep
import Komlos.InitializationMargin
import Komlos.CompletionSampler
import Komlos.PotentialConcavity
import Komlos.RowBoundA2
import Komlos.NonpositiveSubspace
import Komlos.CurvatureGeneral
import Komlos.SpectralPath
import Komlos.HessianDecomposition
import Komlos.AnchorUpdate
import Komlos.FiniteRounding
import Komlos.GaussianDensity
import Komlos.UniformSphere
import Komlos.StabilityTransport
import Komlos.ResolventStability
import Komlos.AnchorDimension
import Komlos.Theorem11Assembly
import Komlos.RandomizedCoupling
import Komlos.InterfaceDischarge
import Komlos.SphereMeasure
import Komlos.AlgorithmCost
import Komlos.GaussianInvariant
import Komlos.SubGaussianBound
import Komlos.EpochBound
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
elab "audit_komlos_axioms" : command => do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Komlos).isPrefixOf name && info.isTheorem then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on forbidden axiom {ax}"
      count := count + 1
  if count == 0 then
    throwError "No Komlos theorems found"
  logInfo m!"Audited {count} Komlos theorem declarations; only propext, Classical.choice, and Quot.sound are allowed."
  logInfo "This audits proof dependencies, not completeness of Theorem 1.1."

audit_komlos_axioms

#check Komlos.DiscrepancyPartOfTheorem11
