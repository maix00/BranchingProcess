/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Analytic.DrawdownSlicing

/-!
# Axiom audit for deterministic spatial slicing

This test checks the bounded-drawdown finite-pattern reduction and its exact
IID block factorization.  It does not claim the subsequent Mogulskii parameter
estimate needed for Aïdékon--Hu Lemma 2.3.
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.additivePath_le_threshold_add_delta_of_noLargeDrop

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.neg_delta_le_additivePath_of_noLargeDrop

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.iidSequenceLaw_measure_spatialBinPatternEvent_eq_pow

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.exists_spatialBinPatternEvent_of_noLargeDrop

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.card_monotoneSpatialBinPattern_le

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.measurableSet_monotoneSpatialBinPatternUnionEvent

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.iidSequenceLaw_measure_monotoneSpatialBinPatternUnionEvent_le

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.noLargeDropEndpointBelowEvent_subset_monotoneSpatialBinPatternUnionEvent

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.iidSequenceLaw_measure_monotoneSpatialBinPatternUnionEvent_le_exp

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_exp

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.eventually_integerDiffusiveBlockOscillationProbability_le_exp

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.eventually_finitePatternEntropyCondition_of_rate_gap

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.eventually_iidSequenceLaw_measure_monotoneSpatialBinPatternUnionEvent_le_exp_of_rate_gap

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_exp_of_rate_gap

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.exists_ah_diffusive_parameters

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp
