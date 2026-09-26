import MeasureTheory.UlamHarris.Split
import MeasureTheory.BranchingWalk.Step.Slot
import Probability.BranchingRandomWalk.Timing.Stopping
import Probability.BranchingRandomWalk.Timing.DeclaredSplit

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingWalk MeasureTheory



theorem first_bifurcation_isStoppingTime
    (path : ℕ → Mark ℕ NatRealStep → 𝕍)
    (hpath : ∀ n,
      Measurable[generationFiltration (M := NatRealStep) n] (path n))
    (hdepth : ∀ n ω, (path n ω).length = n) :
    IsStoppingTime (generationFiltration (M := NatRealStep))
      (firstDeclaredSuccess (splitDeclaration path twoChildren)) :=
  first_split_isStoppingTime_of path twoChildren twoChildren_measurable
    hpath hdepth

end ProbabilityTheory.BranchingRandomWalk
