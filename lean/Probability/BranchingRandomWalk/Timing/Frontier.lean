import Probability.BranchingRandomWalk.Tree.Filtration
import Probability.BranchingRandomWalk.Timing.Measurability

/-!
# Adapted state recursions driven by the current frontier

`frontierMarks n` collects the marks at depth `n` of the pre-sampled mark
field. A population state that is updated from its previous value and the
current frontier is adapted, including retained genealogical identities rather
than only their count.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris MeasureTheory



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
