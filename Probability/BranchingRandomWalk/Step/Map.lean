/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Map
public import Probability.BranchingRandomWalk.Step.Presentation

/-!
# Mapping random branching-step marks

A measurable map of marks acts on a random `Step` by composing the random
variable with the deterministic `Combinatorics.Branching.Step.map`. Forgetting
marks is the constant-map instance used for the Galton--Watson genealogy.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching MeasureTheory

/-- Map the marks of a random step by a measurable function. -/
def StepPresentation.map {Ω ι X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y]
    (S : StepPresentation Ω ι X) (f : X → Y) (hf : Measurable f) : StepPresentation Ω ι Y where
  present := S.present
  measurable_present := S.measurable_present
  displace i ω := f (S.displace i ω)
  measurable_displace i := hf.comp (S.measurable_displace i)

@[simp] theorem StepPresentation.map_apply {Ω ι X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y]
    (S : StepPresentation Ω ι X) (f : X → Y) (hf : Measurable f) (ω : Ω) :
    S.map f hf ω = (S ω).map f := by
  ext i
  cases h : S.present i ω <;>
    simp [StepPresentation.toFun, StepPresentation.map, Combinatorics.Branching.Step.map, h]

/-- Mapping marks before taking the law agrees with pushing the step law
forward through the deterministic mark map. -/
theorem StepPresentation.map_indexedLaw
    {Ω ι X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y]
    (S : StepPresentation Ω ι X) (P : Measure Ω) (f : X → Y) (hf : Measurable f) :
    (S.map f hf).indexedLaw P = (S.indexedLaw P).map (Combinatorics.Branching.Step.map f) := by
  unfold StepPresentation.indexedLaw stepLaw
  rw [Measure.map_map (Step.map_measurable hf) S.measurable_toFun]
  congr 1
  funext ω
  exact StepPresentation.map_apply S f hf ω

/-- Forget the spatial marks of a random step. This retains exactly its random
child-slot configuration. -/
def StepPresentation.forgetMarks {Ω ι X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (S : StepPresentation Ω ι X) : StepPresentation Ω ι PUnit.{1} :=
  S.map (fun _ => PUnit.unit.{1}) measurable_const

@[simp] theorem StepPresentation.survive_forgetMarks_iff
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : StepPresentation Ω ι X) (ω : Ω) (i : ι) :
    survive (S.forgetMarks ω) i ↔ survive (S ω) i := by
  cases h : S.present i ω <;>
    simp [survive, StepPresentation.toFun, StepPresentation.forgetMarks, StepPresentation.map, h]

/-- The unmarked reproduction law underlying a random marked step. -/
noncomputable def StepPresentation.unmarkedLaw
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : StepPresentation Ω ι X) (P : Measure Ω) :
    Measure (Combinatorics.Branching.Step ι PUnit.{1}) :=
  S.forgetMarks.indexedLaw P

instance StepPresentation.unmarkedLaw.isProbabilityMeasure
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : StepPresentation Ω ι X) (P : Measure Ω) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (S.unmarkedLaw P) := by
  unfold StepPresentation.unmarkedLaw
  infer_instance

/-- The unmarked reproduction law is the deterministic forgetful image of the
marked step law. -/
theorem StepPresentation.unmarkedLaw_eq_map
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : StepPresentation Ω ι X) (P : Measure Ω) :
    S.unmarkedLaw P =
      (S.indexedLaw P).map Combinatorics.Branching.Step.forgetMark := by
  exact S.map_indexedLaw P (fun _ => PUnit.unit.{1}) measurable_const

end ProbabilityTheory.BranchingRandomWalk
