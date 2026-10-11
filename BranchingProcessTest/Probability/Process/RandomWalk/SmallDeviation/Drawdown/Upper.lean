/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Upper

/-!
# Axiom audit for deterministic spatial slicing

This test checks the bounded-drawdown finite-pattern reduction and its exact
IID block factorization.  It does not claim the subsequent Mogulskii parameter
estimate needed for Aïdékon--Hu Lemma 2.3.
-/

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.additivePath_le_threshold_add_delta_of_noLargeDrop

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.neg_delta_le_additivePath_of_noLargeDrop

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.iidSequenceLaw_measure_spatialBinPatternEvent_eq_pow

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.exists_spatialBinPatternEvent_of_noLargeDrop

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.card_monotoneSpatialBinPattern_le

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.measurableSet_monotoneSpatialBinPatternUnionEvent

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.iidSequenceLaw_measure_monotoneSpatialBinPatternUnionEvent_le

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent_subset_monotoneSpatialBinPatternUnionEvent

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.iidSequenceLaw_measure_monotoneSpatialBinPatternUnionEvent_le_exp

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_exp

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.eventually_integerDiffusiveBlockOscillationProbability_le_exp

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.eventually_finitePatternEntropyCondition_of_rate_gap

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.eventually_iidSequenceLaw_measure_monotoneSpatialBinPatternUnionEvent_le_exp_of_rate_gap

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_exp_of_rate_gap

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.exists_ah_diffusive_parameters

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp
