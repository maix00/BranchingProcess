/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Tree.Filtration
public import Probability.Process.HittingTime.ObservableCandidates
public import Probability.Process.Adapted.Recursion

/-!
# Adapted state recursions driven by the current frontier

`frontierMarks n` collects the marks at depth `n` of the pre-sampled mark
field. A population state that is updated from its previous value and the
current frontier is adapted, including retained genealogical identities rather
than only their count.
## Public declarations

- `frontier_causal_state_adapted` states that if
  $state_{n+1}(\omega)=step(state_n(\omega),frontierMarks_n(\omega))$, the update `step` is
  measurable, and the initial state is observable at generation zero, then `state n` is
  measurable with respect to the generation domain flow at every $n$. The state may retain
  genealogical identities as well as population counts.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris MeasureTheory



variable {α : Type*} {M : Type*} [MeasurableSpace M]

/-- A population state updated measurably from the current frontier is adapted.
This includes retained genealogical identities, not only their count. -/
theorem frontier_causal_state_adapted {State : Type*}
    [MeasurableSpace State] [Inhabited M]
    (state : ℕ → Mark α M → State)
    (step : State × Mark α M → State)
    (hstep : Measurable step)
    (hzero : Measurable[generationFiltration (M := M) 0] (state 0))
    (hrec : ∀ n ω, state (n + 1) ω =
      step (state n ω, frontierMarks n ω)) :
    ∀ n, Measurable[generationFiltration (M := M) n] (state n) :=
  causal_recursion_adapted (generationFiltration (M := M))
    state (frontierMarks (M := M)) step hstep hzero
    frontierMarks_measurable hrec

end ProbabilityTheory.BranchingRandomWalk
