/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper

/-!
# Axiom audit for the pathwise drawdown lemmas

This audit checks the declarations expressing the finite-horizon event
\(S_i-S_j\leq\Delta\) for \(i\leq j\), the resulting path bounds, and the
identification of segment oscillation with the increment-block event.
It also audits the finite-variance exponential estimate corresponding to
Wang Yiyang, *Asymptotic speed of the $N$-branching random walk with infinite
offspring*, Chapter 3, Lemma 3.3.
-/

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.additivePath_le_threshold_add_delta_of_noLargeDrop

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.neg_delta_le_additivePath_of_noLargeDrop

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.blockOscillationEvent_of_additiveSegment

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.tendsto_diffusiveBlockCount_atTop_of_horizonRatio

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.measureReal_noLargeDropEndpointBelowEvent_le_exp_of_finiteVariance
