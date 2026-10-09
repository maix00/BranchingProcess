/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Analytic.LeftTailAtAOne
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Range.BlockBound

/-!
# Axiom audit for the raw `a = 1` left-tail input

These declarations give the BRW-to-spine reduction and the elementary
many-to-one endpoint estimates. They do not include the sharp Aïdékon--Hu
no-large-drop estimate or the selected-population transfer in (4.16).
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.measure_hasNoLargeDropEndpointBelow_le_exp_mul_spineProbability

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.measure_hasEndpointBelow_le_exp

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Analytic.measure_hasEndpointBelowByHorizon_le_sum_exp

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.eventually_horizontalTubeProbability_le_pow_fixedCover_uniformOffset
