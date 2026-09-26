import Probability.BranchingRandomWalk.PointProcess.Basic
import MeasureTheory.BranchingWalk.Ordered

/-!
# Measurable monotone slot enumerations

A `MonotoneEnumeration ν rel` is a measurable optional-slot description of a
measure-valued map `ν : Ω → Measure X`: the presence set is parent closed (an
initial segment of `ℕ`), the present slots are ordered by `rel`, and the Dirac
sum of the slots is `ν`.

Both the mark type `X` and the ordering relation `rel` are parameters, so the
structure is not tied to the real line, and increasing and decreasing
enumerations are instances of one definition. The relation-parameterized slot
condition is `parentRel`; its left--right symmetry is
`parentAntitone_iff_orderDual`.

The real-line laws and the canonical construction live in
`Representation/RealLineEnumeration.lean` and `Representation/FromMeasure.lean`,
because they use the real child-slot vocabulary.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.BranchingWalk MeasureTheory

/-- A measurable monotone optional-slot enumeration whose Dirac sum is the
given measure-valued map, pointwise in the sample. The relation `rel` orders
the present slots, and the presence set is required to be parent closed. -/
structure MonotoneEnumeration {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (rel : X → X → Prop) where
  toStep : Ω → Step ℕ X
  measurable_toStep : Measurable toStep
  presence_parent : ∀ ω, presenceParent (toStep ω)
  rel_ordered : ∀ ω, parentRel rel (toStep ω)
  measure_eq : ∀ ω, stepPointMeasure (toStep ω) = ν ω

/-- The concrete child-mark law induced by a representation. -/
noncomputable def MonotoneEnumeration.markLaw
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {ν : Ω → Measure X} {rel : X → X → Prop}
    (r : MonotoneEnumeration ν rel) (P : Measure Ω) :
    Measure (Step ℕ X) :=
  P.map r.toStep

instance {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {ν : Ω → Measure X} {rel : X → X → Prop}
    (r : MonotoneEnumeration ν rel) (P : Measure Ω) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (r.markLaw P) := by
  unfold MonotoneEnumeration.markLaw
  infer_instance

end ProbabilityTheory.BranchingRandomWalk
