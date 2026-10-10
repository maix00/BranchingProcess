/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Analytic.DrawdownNormalization

/-!
# Axiom audit for finite-variance drawdown normalization

This test checks measurability of the finite-horizon event, its pathwise
scaling identity, and the transfer of the unit-variance Aïdékon--Hu estimate
to arbitrary positive finite variance.
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.measurableSet_noLargeDropEndpointBelowEvent

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.noLargeDropEndpointBelowEvent_preimage_div

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_eq_map_div

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp_of_centeredSecondMoment

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp_of_centeredSecondMoment
