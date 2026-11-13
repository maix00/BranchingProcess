module

import Probability.BranchingRandomWalk.Restart.SelectedPath.Coupling.Population
import Probability.BranchingRandomWalk.Restart.SelectedPath.Completion.Basic
import Probability.BranchingRandomWalk.Restart.SelectedPath.Completion.FreshField
import Probability.BranchingRandomWalk.Restart.SelectedPath.Completion.FixedHorizon
import all Probability.BranchingRandomWalk.Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.RootFamily
import all Probability.BranchingRandomWalk.Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.Geometry
import all Probability.BranchingRandomWalk.Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.FreshField
import Probability.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Causal
import Probability.BranchingRandomWalk.Restart.SelectedPath.Splits
import Probability.Process.Stopping.Selection.Ranked
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily

/-!
# Axiom audit for the causal selected-path BRW population comparison
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Population.family_finiteSlices

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Population.family_card_le

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.root_at_split

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Coupling.selectedToNSelectedBRWInjection_ae

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Coupling.population_card_ge_of_success

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Coupling.population_card_ge_of_successEvent

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Population.growthTrial_subset_at_endpoint

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.successEvent_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.firstSuccessfulCompletion_isStoppingTime

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Coupling.positionWitness_ae

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Coupling.candidatePositionWitness_ae

#print axioms
  Combinatorics.Selection.NSelection.measurable_particleRankVectorAtStoppingTime

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.subtreeStepFieldVector_measurable_of_measurable_roots

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Completion.time_isStoppingTime

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Completion.endpointNodesByRank_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots_depth

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots_injective

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots_eq_nSelectedBRW_ae

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshField_factorization_on_finite

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.nSelectedBRWFreshField_factorization_on_finite

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Completion.positionFreshField_jointLaw_on_finite

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Coupling.population_law
