/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Sequence.IID.GeometricReward.FirstMoment

/-!
# Axiom audit for iid geometric-trial moment identities

These checks expose the transitive axioms used by the failure-only first-moment
formula and its ENNReal exponential-transform expansion.
-/

#print axioms ProbabilityTheory.iidGeometricFailurePositiveReward_integral
#print axioms ProbabilityTheory.iidGeometricSplitCycle_positiveReward_le
#print axioms ProbabilityTheory.iidGeometricFailureExponentialTransform
