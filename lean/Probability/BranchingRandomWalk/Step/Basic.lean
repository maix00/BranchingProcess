module

public import Combinatorics.BranchingWalk.Step.Basic
public import Mathlib.MeasureTheory.Measure.Map

/-!
# Laws of random optional-step fields

The random offspring object is a measurable map into the semantic optional
field `ι → Option X`.  The definitions in this file accept that map and its
measurability proof directly; coordinate sampling presentations live in
`Step/Presentation.lean`.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory

/-- The law of a random optional-step field. -/
noncomputable def stepLaw {Ω ι X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X]
    (S : Ω → Combinatorics.Branching.Step ι X) (P : Measure Ω) :
    Measure (Combinatorics.Branching.Step ι X) :=
  P.map S

/-- Evaluate the law of a random optional-step field on a measurable set. -/
theorem stepLaw_apply {Ω ι X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X]
    (S : Ω → Combinatorics.Branching.Step ι X) (hS : Measurable S)
    (P : Measure Ω) (s : Set (Combinatorics.Branching.Step ι X))
    (hs : MeasurableSet s) :
    stepLaw S P s = P (S ⁻¹' s) :=
  Measure.map_apply hS hs

end ProbabilityTheory.BranchingRandomWalk
