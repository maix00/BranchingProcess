/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Walk.Path.Position
public import Probability.Process.RandomWalk.Path.Scaling

/-!
# Singleton branching walk representation of normalized random-walk paths
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Walk

open Combinatorics.Branching
open Combinatorics.Branching.Walk
open ProbabilityTheory.RandomWalk

/-- The normalized path is the rescaled displacement along the corresponding
node of the singleton lineage. -/
theorem normalizedStepPath_eq_displaceWith
    {Mark : Type*} (d : Mark → ℝ) (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → Mark) (t : ℝ) :
    normalizedStepPath scale n (d ∘ increment) t =
      (scale n)⁻¹ *
        displaceWith d (stepFieldOfIncrements increment) []
          (lineNode ⌊(n : ℝ) * t⌋₊) := by
  rw [normalizedStepPath, displaceWith_lineNode_eq_displacement]

/-- With zero initial position, the normalized path is the rescaled position
stored by the generation cloud of the singleton-lineage branching walk. -/
theorem normalizedStepPath_eq_discreteTimeCloud_position
    {Mark : Type*} (d : Mark → ℝ) (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → Mark) (t : ℝ) :
    normalizedStepPath scale n (d ∘ increment) t =
      (scale n)⁻¹ *
        (Cloud.discreteTimeCloud_ofBranchingWalk d
          (ofIncrements 0 increment)).position PUnit.unit
            (lineNode ⌊(n : ℝ) * t⌋₊) := by
  rw [normalizedStepPath, Cloud.discreteTimeCloud_ofBranchingWalk_position]
  simp only [ofIncrements_initial, zero_add]
  change (scale n)⁻¹ * AdditivePath.displacement ⌊(n : ℝ) * t⌋₊ (d ∘ increment) =
    (scale n)⁻¹ * displaceWith d (stepFieldOfIncrements increment) []
      (lineNode ⌊(n : ℝ) * t⌋₊)
  rw [displaceWith_lineNode_eq_displacement]


end ProbabilityTheory.BranchingRandomWalk.Walk

end
