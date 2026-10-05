/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Genealogy.Lineage.MultiRoot
import Probability.BranchingRandomWalk.Restart.FailureEstimate
import Probability.BranchingRandomWalk.Timing.TimingCounterexample

/-!
# Pre-sampled reserve-lineage API checks

The reserve trajectories and their first declared split times are functions
of the same root-indexed field. The split times satisfy the stopping-time
interface, while the separate look-ahead example prevents treating the trial
time itself as automatically stopping.
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.sigma_isStoppingTime

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.integral_reserveRoot_abs_on_candidateFailure_le

#print axioms
  ProbabilityTheory.BranchingRandomWalk.lookahead_time_not_stopping
