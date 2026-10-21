/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Corridor.Upper

/-!
# The open corridor used for Brownian meander

The public declarations in this file are:

- `BrownianMeander.openCorridor`: the path event
  $\{f:\exists\varepsilon>0,\ \forall t,\
    f(t)\le(5/6-\rho)/\sigma-\varepsilon,\
    f(1)\in((5/12+\rho)/\sigma,(11/24-\rho)/\sigma)\}$.
- `BrownianMeander.isOpen_openCorridor`: this event is open in the Skorokhod
  $J_1$ topology.

This is the corridor event in Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5 and Appendix A.2,
Lemma A.7. Its openness follows from the general Skorokhod corridor theorem
`Skorokhod.isOpen_rangeBelowEndsIn`. The positive-mass statement for the
Brownian meander law follows from the last-zero representation of Donald L.
Iglehart,
*Functional Central Limit Theorems for Random Walks Conditioned to Stay
Positive*, Ann. Probab. 2(4) (1974), 608--619, DOI 10.1214/aop/1176996607, Section 3, theorem (3.4), p. 616.
-/

@[expose] public section

open MeasureTheory
open scoped Topology

namespace BrownianMeander

/-- The strict upper and terminal corridor in the meander argument of Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5 and Appendix A.2, Lemma A.7. -/
def openCorridor (sigma rho : ℝ) : Set (CadlagPath unitInterval ℝ) :=
  Skorokhod.rangeBelowEndsIn
    ((5 / 6 - rho) / sigma)
    ((5 / 12 + rho) / sigma)
    ((11 / 24 - rho) / sigma)

/-- The meander corridor is open in the Skorokhod $J_1$ topology. -/
theorem isOpen_openCorridor (sigma rho : ℝ) :
    IsOpen (openCorridor sigma rho) := by
  simpa [openCorridor] using
    Skorokhod.isOpen_rangeBelowEndsIn
      ((5 / 6 - rho) / sigma)
      ((5 / 12 + rho) / sigma)
      ((11 / 24 - rho) / sigma)

end BrownianMeander

end
