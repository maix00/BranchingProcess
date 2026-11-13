/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Lineage
import Probability.BranchingRandomWalk.Restart.Failure.Estimate
import Probability.BranchingRandomWalk.Restart.Trial.FirstSplit
import Probability.BranchingRandomWalk.Restart.FirstSplit.BranchingProperty
import Probability.BranchingRandomWalk.Restart.Reserve.Lineage
import Probability.BranchingRandomWalk.Restart.Trial.Basic
import Probability.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Roots
import Probability.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Lineage
import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppingSubtreeVector.Factorization
import Probability.Process.HittingTime.Examples.Lookahead

/-!
# Pre-sampled lineage API checks

Every pre-sampled trajectory is fixed on the same root-indexed field before any
trial outcome is used. Its raw split generation `tau` and observable
completion generation `sigma` satisfy `sigma = tau + 1`; `sigma` is a stopping
time for the generation domain flow. The look-ahead examples distinguish this
one-generation visibility fact from a general successor rule for anticipative
times.
-/

#print axioms Combinatorics.Branching.Step.FiniteSelection.firstSelectedSlot_measurable

#print axioms Combinatorics.Branching.Step.FiniteSelection.firstSelectedSlot_mem

#print axioms ProbabilityTheory.BranchingRandomWalk.splitBy_measurable

#print axioms ProbabilityTheory.BranchingRandomWalk.RootIndexed.fixedSubtree_measurable_at

#print axioms ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.growthTrialRootAt_root

#print axioms ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.growthTrialRootAt_depth

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.PreSampledLineages.sigma_isStoppingTime

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.PreSampledLineages.all_sigma_isStoppingTime

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.PreSampledLineages.first_success_within_isStoppingTime

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.PreSampledLineages.successfulWithin_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.PreSampledLineages.failureWithin_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.PreSampledLineages.integral_selectedSubtree_abs_on_candidateFailure

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.PreSampledLineages.integral_selectedSubtree_abs_on_candidateFailure_le

#print axioms
  ProbabilityTheory.BranchingRandomWalk.growthTrialSuccess_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.successAtSelectedRoot_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.growthTrialRootAt_fiber_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.growthTrialRootAt_selected

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.successTest_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.completion_isStoppingTime

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.completion_eq_tau_add_trialLength

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.candidatesWithin_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.integral_selectedSubtree_abs_on_growthTrialFailure_le

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.PreSampledLineages.sigma_eq_tau_add_one

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.integral_reserveRoot_abs_on_candidateFailure_le

#print axioms
  ProbabilityTheory.Process.HittingTime.Examples.lookahead_time_not_stopping

#print axioms
  ProbabilityTheory.Process.HittingTime.Examples.lookahead_completion_isStoppingTime

#print axioms
  ProbabilityTheory.Process.HittingTime.Examples.delayed_lookahead_completion_not_stopping

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedPopulationSplitCompletion_eq_raw_add_one

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedPopulationSplitCompletion_isStoppingTime

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedPopulationRawSplitTime_not_stopping_of_probability

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedPopulation_firstSplit_parent_card_eq_one

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedPopulation_firstSplit_has_sibling_pair

#print axioms Combinatorics.Branching.Step.FiniteSelection.secondSelectedSlot_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.continuationChildAt_selected

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.continuationChildAt_sigma_selected

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.continuationChildAt_ne_growthTrialRootAt

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.continuationChildAt_sigma_ne_growthTrialRootAt

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.continuationChildAt_sigma_fiber_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.sigma_continuationChildSubtree_splitCompletion_isStoppingTime

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedPopulationFirstSplitRoots_fiber_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedPopulationFirstSplitRoots_depth

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedPopulationFirstSplitRoots_injective_of_finite

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedChildrenAtFirstSplit_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.sigmaGrowthTrialAndContinuationRoots

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.siblingField_factorization_on_finite

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedPopulation_firstSplit_subtree_vector_factorization
