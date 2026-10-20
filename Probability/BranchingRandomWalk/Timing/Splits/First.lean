/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Split
public import Combinatorics.BranchingWalk.Step.Measurability
public import Probability.Process.HittingTime.Declarations
public import Probability.BranchingRandomWalk.Timing.Splits.Declared

/-!
# First declared bifurcation time

`ProbabilityTheory.BranchingRandomWalk.first_bifurcation_isStoppingTime`
states that the first generation at which the selected lineage declares a
bifurcation is a stopping time for the generation domain flow. If `τ` is
that first-declaration time and `\mathcal F_n` is the generation domain
flow, the conclusion is
$\{\omega \mid \tau(\omega) \le n\} \in \mathcal F_n$ for every $n$.
-/

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
