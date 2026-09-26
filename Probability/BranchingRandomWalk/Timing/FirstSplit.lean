import Combinatorics.UlamHarris.Split
import Combinatorics.BranchingWalk.Step.Measurability
import Probability.BranchingRandomWalk.Timing.Stopping
import Probability.BranchingRandomWalk.Timing.DeclaredSplit

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



theorem first_bifurcation_isStoppingTime
    (path : ℕ → Mark ℕ NatRealStep → 𝕍)
    (hpath : ∀ n,
      Measurable[generationFiltration (M := NatRealStep) n] (path n))
    (hdepth : ∀ n ω, (path n ω).length = n) :
    IsStoppingTime (generationFiltration (M := NatRealStep))
      (firstDeclaredSuccess (splitDeclaration path nontrivialSupport)) :=
  first_split_isStoppingTime_of path nontrivialSupport nontrivialSupport_measurable
    hpath hdepth

end ProbabilityTheory.BranchingRandomWalk
