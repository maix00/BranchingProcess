/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Scaling

/-!
# Axiom audit for drawdown-event scaling

This audit checks measurability of the finite-horizon event and its pathwise
and probability scaling identities under division by a positive constant.
-/

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.measurableSet_noLargeDropEndpointBelowEvent

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent_preimage_div

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_eq_map_div
