/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Timing.GeometricTrial.FirstMoment

/-!
# Axiom audit for iid geometric-trial moment identities

These checks expose the transitive axioms used by the failure-only first-moment
formula and its ENNReal exponential-transform expansion.
-/

#print axioms ProbabilityTheory.BranchingRandomWalk.iidGeometricFailurePositiveReward_integral
#print axioms ProbabilityTheory.BranchingRandomWalk.iidGeometricSplitCycle_positiveReward_le
#print axioms ProbabilityTheory.BranchingRandomWalk.iidGeometricFailureExponentialTransform
