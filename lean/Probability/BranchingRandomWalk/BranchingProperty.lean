import Probability.BranchingRandomWalk.IID
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily

/-!
# Branching property of the canonical i.i.d. law

The product construction has a branching property for generation-measurably
chosen families of same-generation roots.  When a chosen family is an actual
population, the same theorem gives the joint law of its fresh descendant
fields.  The statement is about the canonical i.i.d. law, not arbitrary
probability laws on the walk space.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching

/-- Under the canonical i.i.d. walk law, a countable-range, generation-
measurably selected injective family of roots at one generation has the
original root-indexed product law below it.  An application to an actual
population supplies its realized roots as `chosen`; existence and population
adaptedness remain properties of that choice. -/
theorem iid_selectedSubtreeStepFieldVector_law
    {κ α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (μ : Measure (Step α Mark)) (initial : Position)
    [IsProbabilityMeasure μ] (n : ℕ)
    (chosen : RootIndexed.StepField PUnit α Mark →
      κ → PUnit × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := PUnit) (α := α) (X := Mark) n]
      {field | chosen field = roots})
    (hdepth : ∀ field i, (chosen field i).2.length = n)
    (hinj : ∀ field, Function.Injective (chosen field)) :
    (((iid μ initial : WalkLaw α Mark Position) :
      Measure (BranchingWalk α Mark Position)).map
        (fun walk => RootIndexed.selectedSubtreeStepFieldVector
          chosen walk.step)) =
      RootIndexed.stepFieldLaw (Root := κ) μ := by
  exact RootIndexed.selectedSubtreeStepFieldVector_law_comp
    (((iid μ initial : WalkLaw α Mark Position) :
      Measure (BranchingWalk α Mark Position))) μ
    (fun walk => walk.step) iid_step_measurable
    (iid_stepFieldLaw μ initial) chosen hcount hfiber hdepth hinj

end ProbabilityTheory.BranchingRandomWalk

end
