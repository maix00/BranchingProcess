module

public import Combinatorics.UlamHarris.Split
public import Combinatorics.BranchingWalk.Step.Measurability
public import Probability.BranchingRandomWalk.Timing.Stopping
public import Probability.BranchingRandomWalk.Timing.DeclaredSplit

open MeasureTheory

@[expose] public section

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
