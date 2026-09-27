import Probability.BranchingRandomWalk.Population.Processes.StepSelection.Basic

/-!
# Measurable filtering of finite step selections

Filtering is separate from choosing a finite family.  In particular, a
truncated rule may first choose an intrinsic finite initial segment of an
unordered step and then remove every chosen child above a potential barrier.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.StepSelection

open Combinatorics.Branching

/-- Measurability of a filtered finite step rule. -/
theorem filter_measurable
    {α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (keep : Step α X → α → Prop)
    (hkeep : ∀ i, Measurable fun ξ => keep ξ i) :
    Measurable (R.filter keep).select := by
  rw [measurable_finset_iff]
  intro i
  simp_rw [Step.FiniteSelection.mem_filter]
  exact ((measurable_finset_mem i).comp hR).and (hkeep i)

/-- Killing selected children above a real potential threshold is
measurable. -/
theorem belowPotential_measurable
    {α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (φ : Potential X) (a : ℝ) :
    Measurable (R.belowPotential φ a).select := by
  apply filter_measurable R hR
    (fun ξ i => ξ.potentialValue' φ i ≤ a)
  intro i
  exact measurableSet_setOfPred.mp
    ((Step.potentialValue'_measurable φ i) measurableSet_Iic)

end ProbabilityTheory.BranchingRandomWalk.StepSelection
