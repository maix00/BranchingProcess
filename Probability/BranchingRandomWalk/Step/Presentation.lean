/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Step.Basic
public import Combinatorics.BranchingWalk.Step.Measurability
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Coordinate presentation of a random branching step

`StepPresentation` stores a measurable presence event and a measurable
`X`-valued displacement for every slot. Evaluating it gives the semantic
optional field `ι → Option X`. Displacements on absent slots are ignored by
that field, so equality of assembled fields is weaker than equality of these
presentations. Core law and point-measure interfaces accept the optional field
and its measurability proof directly.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

/-- An `X`-valued coordinate used by a `StepPresentation`. -/
abbrev StepPresentationDisplace (Ω X : Type*) := Ω → X

/-- A coordinate sampling presentation with a measurable presence event and
an `X`-valued measurable displacement for every slot. The displacement on an
absent slot is ignored by the assembled optional field. -/
structure StepPresentation (Ω ι X : Type*) [MeasurableSpace Ω]
    [MeasurableSpace X] where
  present : ι → Ω → Bool
  measurable_present : ∀ i, Measurable (present i)
  displace : ι → StepPresentationDisplace Ω X
  measurable_displace : ∀ i, Measurable (displace i)

/-- Assemble the coordinate random displacements into a deterministic step at one
sample. -/
def StepPresentation.toFun {Ω ι X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (S : StepPresentation Ω ι X) (ω : Ω) :
    Combinatorics.Branching.Step ι X :=
  fun i => if S.present i ω then some (S.displace i ω) else none

instance {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] :
    CoeFun (StepPresentation Ω ι X)
      (fun _ => Ω → Combinatorics.Branching.Step ι X) :=
  ⟨StepPresentation.toFun⟩

@[simp] theorem StepPresentation.apply_eq_some_iff
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : StepPresentation Ω ι X) (ω : Ω) (i : ι) (x : X) :
    S ω i = some x ↔ S.present i ω = true ∧ S.displace i ω = x := by
  change (if S.present i ω then some (S.displace i ω) else none) = some x ↔
    S.present i ω = true ∧ S.displace i ω = x
  simp

@[simp] theorem StepPresentation.apply_eq_none_iff
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : StepPresentation Ω ι X) (ω : Ω) (i : ι) :
    S ω i = none ↔ S.present i ω = false := by
  change (if S.present i ω then some (S.displace i ω) else none) = none ↔
    S.present i ω = false
  simp

/-- The assembled deterministic step is measurable because every random
displacement coordinate is measurable. -/
theorem StepPresentation.measurable_toFun
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : StepPresentation Ω ι X) : Measurable S := by
  rw [measurable_pi_iff]
  intro i
  change Measurable (fun ω =>
    if S.present i ω then some (S.displace i ω) else none)
  have hp : MeasurableSet {ω | S.present i ω = true} :=
    (measurableSet_singleton true).preimage (S.measurable_present i)
  exact (measurable_option_some.comp (S.measurable_displace i)).ite hp measurable_const

/-- The step law is the law of the assembled coordinate family. -/
noncomputable def StepPresentation.indexedLaw
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : StepPresentation Ω ι X) (P : Measure Ω) :
    Measure (Combinatorics.Branching.Step ι X) :=
  stepLaw S.toFun P

instance StepPresentation.indexedLaw.isProbabilityMeasure
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : StepPresentation Ω ι X) (P : Measure Ω)
    [IsProbabilityMeasure P] : IsProbabilityMeasure (S.indexedLaw P) := by
  unfold StepPresentation.indexedLaw stepLaw
  infer_instance

theorem StepPresentation.indexedLaw_apply
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : StepPresentation Ω ι X) (P : Measure Ω)
    (s : Set (Combinatorics.Branching.Step ι X))
    (hs : MeasurableSet s) :
    S.indexedLaw P s = P (S ⁻¹' s) := by
  exact stepLaw_apply S.toFun S.measurable_toFun P s hs

end ProbabilityTheory.BranchingRandomWalk
