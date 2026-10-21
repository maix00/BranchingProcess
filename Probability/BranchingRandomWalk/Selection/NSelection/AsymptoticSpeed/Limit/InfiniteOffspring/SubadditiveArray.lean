/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.Repair

/-!
# The repaired selection subadditive array

- `repairedInfiniteSelectionSubadditiveArray`: for `0 < N`, the value
  `A ω s n` is the negative position of rank zero after `n` steps from zero,
  using the repaired environment segment `ω (s + t)`.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

noncomputable def repairedInfiniteSelectionSubadditiveArray {N : ℕ}
    (hN : 0 < N) (ω : GenerationEnvironment N)
    (start length : ℕ) : ℝ :=
  - measurableRepairedInfiniteOffspringRun length
      ((fun _ : Fin N => (0 : ℝ)), fun t => ω (start + t)) ⟨0, hN⟩
end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
