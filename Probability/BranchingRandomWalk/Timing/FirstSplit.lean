import Combinatorics.UlamHarris.Split
import Combinatorics.BranchingWalk.Step.Measurability
import Probability.BranchingRandomWalk.Timing.Stopping
import Probability.BranchingRandomWalk.Timing.DeclaredSplit

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



theorem first_bifurcation_isStoppingTime
    (path : ℕ → Mark ℕ (Step ℕ ℝ) → 𝕍)
    (hpath : ∀ n,
      Measurable[generationFiltration (M := Step ℕ ℝ) n] (path n))
    (hdepth : ∀ n ω, (path n ω).length = n) :
    IsStoppingTime (generationFiltration (M := Step ℕ ℝ))
      (firstDeclaredSuccess (splitDeclaration path nontrivialSupport)) :=
  first_split_isStoppingTime_of path nontrivialSupport nontrivialSupport_measurable
    hpath hdepth

end ProbabilityTheory.BranchingRandomWalk
