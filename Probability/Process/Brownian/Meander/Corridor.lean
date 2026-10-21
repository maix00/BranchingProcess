/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Corridor.Upper

/-!
# The open corridor used for Brownian meander

The public definition in this file is:

- `BrownianMeander.openCorridor`: the path event
  $\{f:\exists\varepsilon>0,\ \forall t,\
    f(t)\le(5/6-\rho)/\sigma-\varepsilon,\
    f(1)\in((5/12+\rho)/\sigma,(11/24-\rho)/\sigma)\}$.

This is the corridor event in Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5 and Appendix A.2,
Lemma A.7. Its openness and support argument are recorded in
`Probability.Process.Brownian.Meander.Lemmas.CorridorPositivity`. The positive-mass
statement for the Brownian meander law follows from the last-zero representation
of Donald L. Iglehart,
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

end BrownianMeander

end
