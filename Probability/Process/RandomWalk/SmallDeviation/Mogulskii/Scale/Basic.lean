/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Scale.Basic

/-!
# The diffusive scale for Mogulskii's theorem

## Public declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale`:
  $x_n\to\infty$ and $x_n/\sqrt n\to0$.

This predicate specializes the general small-deviation scale relation to the
Gaussian normalization `sqrt n` used in Theorem 3, Section 4, p. 764 of A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- A spatial scale diverges while remaining negligible compared with the
diffusive scale. -/
def IsMogulskiiScale (scale : ℕ → ℝ) : Prop :=
  Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n)

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
