/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Genealogy.Lineage.MultiRoot
import Probability.BranchingRandomWalk.Restart.FailureEstimate
import Probability.BranchingRandomWalk.Restart.FirstSplit
import Probability.BranchingRandomWalk.Restart.FirstSplit.BranchingProperty
import Probability.BranchingRandomWalk.Restart.ReserveLineage
import Probability.BranchingRandomWalk.Restart.Trial
import Probability.BranchingRandomWalk.Restart.RootedTrial.ReserveLineage
import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppingSubtreeVector.Factorization
import Probability.BranchingRandomWalk.Timing.TimingCounterexample

/-!
# Pre-sampled reserve-lineage API checks

Every reserve trajectory is fixed on the same root-indexed field before any
trial outcome is used. Its raw split generation `tau` and observable
completion generation `sigma` satisfy `sigma = tau + 1`; `sigma` is a stopping
time for the generation domain flow. The look-ahead examples distinguish this
one-generation visibility fact from a general successor rule for anticipative
times.
-/

#print axioms ProbabilityTheory.BranchingRandomWalk.firstSelectedSlot_measurable

#print axioms ProbabilityTheory.BranchingRandomWalk.firstSelectedSlot_mem

#print axioms ProbabilityTheory.BranchingRandomWalk.splitBy_measurable

#print axioms ProbabilityTheory.BranchingRandomWalk.RootIndexed.fixedSubtree_measurable_at

#print axioms ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.firstChildRootAt_root

#print axioms ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.firstChildRootAt_depth

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.sigma_isStoppingTime

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.all_sigma_isStoppingTime

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.first_success_within_isStoppingTime

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.successfulWithin_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.failureWithin_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.integral_selectedSubtree_abs_on_candidateFailure

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.integral_selectedSubtree_abs_on_candidateFailure_le

#print axioms
  ProbabilityTheory.BranchingRandomWalk.growthTrialSuccess_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.growthTrialSuccessAt_selectedRoot_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.firstChildRootAt_fiber_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.firstChildRootAt_selected

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.firstGrowthCandidateTest_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.firstGrowthCandidate_observable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.firstGrowthCompletion_isStoppingTime

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.firstGrowthCompletion_eq_tau_add_trialLength

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.firstGrowthCandidatesWithin_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.integral_selectedSubtree_abs_on_firstGrowthFailure_le

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.sigma_eq_tau_add_one

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.integral_reserveRoot_abs_on_candidateFailure_le

#print axioms
  ProbabilityTheory.BranchingRandomWalk.lookahead_time_not_stopping

#print axioms
  ProbabilityTheory.BranchingRandomWalk.lookahead_completion_isStoppingTime

#print axioms
  ProbabilityTheory.BranchingRandomWalk.delayed_lookahead_completion_not_stopping

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

#print axioms ProbabilityTheory.BranchingRandomWalk.secondSelectedSlot_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.secondChildRootAt_selected

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.secondChildRootAt_sigma_selected

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.secondChildRootAt_ne_firstChildRootAt

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.secondChildRootAt_sigma_ne_firstChildRootAt

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.secondChildRootAt_sigma_fiber_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.sigma_secondChildSubtree_splitCompletion_isStoppingTime

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
  ProbabilityTheory.BranchingRandomWalk.selectedPopulation_firstSplit_subtree_vector_factorization
