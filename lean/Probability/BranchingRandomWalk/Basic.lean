import Probability.BranchingRandomWalk.Step.Law

/-!
# Branching random walks

`BranchingRandomWalk α X` is the random version of `BranchingWalk α X`: a law
on the branching walks, that is a probability measure on `BranchingWalk α X`.
The canonical instance `iid μ init` is the independent, identically distributed
walk in which every address carries an independent branching step with law `μ`
and the walk starts from the initial population `init`.
-/

namespace ProbabilityTheory

namespace BranchingRandomWalk

open MeasureTheory MeasureTheory.UlamHarris MeasureTheory.BranchingWalk MeasureTheory

/-- A branching random walk: a probability measure on `BranchingWalk α X`. -/
structure BranchingRandomWalk (α X : Type*) [MeasurableSpace X] where
  /-- The law of the walk. -/
  law : Measure (BranchingWalk α X)
  /-- The law is a probability measure. -/
  prob : IsProbabilityMeasure law

instance (α X : Type*) [MeasurableSpace X] :
    CoeFun (BranchingRandomWalk α X) (fun _ => Measure (BranchingWalk α X)) :=
  ⟨BranchingRandomWalk.law⟩

/-- The i.i.d. branching random walk: every address carries an independent
branching step with law `μ`, and the walk starts from `init`. -/
noncomputable def iid {α X : Type*} [MeasurableSpace X] (μ : Measure (Step α X))
    (init : Set X) [IsProbabilityMeasure μ] : BranchingRandomWalk α X := by
  let f : StepField α X → BranchingWalk α X :=
    fun ω => ⟨fun _ : PUnit => ω, fun _ : PUnit => init⟩
  have hf : Measurable f := by
    intro s hs
    rw [MeasurableSpace.measurableSet_comap] at hs
    rcases hs with ⟨t, ht, rfl⟩
    change MeasurableSet ((fun ω : StepField α X => ((f ω).step, (f ω).initial)) ⁻¹' t)
    exact ((measurable_pi_iff.mpr (fun _ : PUnit => measurable_id)).prodMk measurable_const) ht
  exact ⟨(stepFieldLaw μ).map f, by infer_instance⟩

end BranchingRandomWalk

end ProbabilityTheory
