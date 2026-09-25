import Combinatorics.UlamHarris.Split
import Combinatorics.BranchingStep.Slot.Basic
import Probability.BranchingRandomWalk.Timing.Stopping
import Probability.BranchingRandomWalk.Timing.DeclaredSplit

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory



theorem first_bifurcation_isStoppingTime
    (path : ℕ → Mark ℕ NatRealBranchingStep → 𝕍)
    (hpath : ∀ n,
      Measurable[generationFiltration (M := NatRealBranchingStep) n] (path n))
    (hdepth : ∀ n ω, (path n ω).length = n) :
    IsStoppingTime (generationFiltration (M := NatRealBranchingStep))
      (firstDeclaredSuccess (splitDeclaration path twoChildren)) :=
  first_split_isStoppingTime_of path twoChildren twoChildren_measurable
    hpath hdepth

end ProbabilityTheory.BranchingRandomWalk
