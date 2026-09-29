module

public import Combinatorics.BranchingWalk.Walk.Path.Position

/-!
# Rescaled step paths

The rescaled right-continuous step path divides the first `⌊nt⌋` increments by
a spatial scale. This construction is deterministic; probability laws and
corridor events are developed separately.
-/

open MeasureTheory

@[expose] public section

namespace Combinatorics.Branching.Walk

/-- The normalized step path used in Mogulskii's theorem.  Its intended time
domain is `[0,1]`; defining it on all reals makes endpoint evaluation and
composition easier. -/
noncomputable def normalizedStepPath (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) (t : ℝ) : ℝ :=
  (scale n)⁻¹ * partialSum ⌊(n : ℝ) * t⌋₊ increment

@[simp] theorem normalizedStepPath_zero (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) :
    normalizedStepPath scale n increment 0 = 0 := by
  simp [normalizedStepPath]

/-- Evaluation of the normalized path at a fixed time is measurable as a
function of its increment path. -/
theorem normalizedStepPath_measurable (scale : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    Measurable (fun increment : ℕ → ℝ =>
      normalizedStepPath scale n increment t) := by
  exact measurable_const.mul (partialSum_measurable _)

/-- At time one, the normalized path is the normalized `n`-step sum. -/
@[simp] theorem normalizedStepPath_one (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) :
    normalizedStepPath scale n increment 1 =
      (scale n)⁻¹ * partialSum n increment := by
  simp [normalizedStepPath]

/-- Evaluation on the `n`-step time grid recovers the corresponding partial
sum. -/
theorem normalizedStepPath_grid (scale : ℕ → ℝ) {n k : ℕ}
    (hn : 0 < n) (increment : ℕ → ℝ) :
    normalizedStepPath scale n increment ((k : ℝ) / n) =
      (scale n)⁻¹ * partialSum k increment := by
  rw [normalizedStepPath]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hgrid : (n : ℝ) * ((k : ℝ) / n) = k := by
    field_simp
  rw [hgrid, Nat.floor_natCast]

/-- The normalized path is the rescaled displacement along the corresponding
node of the singleton lineage. -/
theorem normalizedStepPath_eq_displaceWith
    {Mark : Type*} (d : Mark → ℝ) (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → Mark) (t : ℝ) :
    normalizedStepPath scale n (d ∘ increment) t =
      (scale n)⁻¹ *
        displaceWith d (stepFieldOfIncrements increment) []
          (lineNode ⌊(n : ℝ) * t⌋₊) := by
  rw [normalizedStepPath, displaceWith_lineNode_eq_partialSum]

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
  change (scale n)⁻¹ * partialSum ⌊(n : ℝ) * t⌋₊ (d ∘ increment) =
    (scale n)⁻¹ * displaceWith d (stepFieldOfIncrements increment) []
      (lineNode ⌊(n : ℝ) * t⌋₊)
  rw [displaceWith_lineNode_eq_partialSum]

end Combinatorics.Branching.Walk
