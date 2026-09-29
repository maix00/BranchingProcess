module

public import Probability.BranchingRandomWalk.Step.Law

set_option linter.dupNamespace false

/-!
# Branching random walks

`BranchingRandomWalk α Mark Position` is the random version of a branching
walk whose child marks and accumulated-position space are independent types.
The canonical instance `iid μ init` is the independent, identically distributed
walk in which every address carries an independent branching step with law `μ`
and the walk starts from the initial position `init`.
-/

@[expose] public section

namespace ProbabilityTheory

namespace BranchingRandomWalk

open MeasureTheory Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

/-- A branching random walk: a probability measure on walks with separate
child-mark and initial-position types. -/
structure BranchingRandomWalk (α Mark Position : Type*)
    [MeasurableSpace Mark] [MeasurableSpace Position] where
  /-- The law of the walk. -/
  law : Measure (BranchingWalk α Mark Position)
  /-- The law is a probability measure. -/
  prob : IsProbabilityMeasure law

instance (α Mark Position : Type*)
    [MeasurableSpace Mark] [MeasurableSpace Position] :
    CoeFun (BranchingRandomWalk α Mark Position)
      (fun _ => Measure (BranchingWalk α Mark Position)) :=
  ⟨BranchingRandomWalk.law⟩

/-- The i.i.d. branching random walk: every address carries an independent
branching step with law `μ`, and the walk starts from the initial position
`init`. -/
noncomputable def iid {α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (μ : Measure (Step α Mark))
    (init : Position) (hclosed : ∀ ω : StepField α Mark, IsParentClosed ω)
    [IsProbabilityMeasure μ] : BranchingRandomWalk α Mark Position := by
  let f : StepField α Mark → BranchingWalk α Mark Position :=
    fun ω => ⟨fun _ : PUnit => ω, fun _ : PUnit => init, fun _ => hclosed ω⟩
  have hf : Measurable f := by
    intro s hs
    rw [MeasurableSpace.measurableSet_comap] at hs
    rcases hs with ⟨t, ht, rfl⟩
    change MeasurableSet ((fun ω : StepField α Mark => ((f ω).step, (f ω).initial)) ⁻¹' t)
    exact ((measurable_pi_iff.mpr (fun _ : PUnit => measurable_id)).prodMk measurable_const) ht
  exact ⟨(stepFieldLaw μ).map f, by infer_instance⟩

end BranchingRandomWalk

end ProbabilityTheory
