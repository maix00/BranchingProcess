module

public import Probability.BranchingRandomWalk.Law
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law
public import Combinatorics.BranchingWalk.StepField

/-!
# Canonical i.i.d. branching-walk law

The canonical construction samples one independent offspring configuration at
every root and address.  The initial position is deterministic.  Offspring
configurations at different addresses are independent; siblings within one
configuration may be dependent.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching

/-- Encode a root-indexed field and fixed initial positions as a walk. -/
def iidRealization {α Mark Position : Type*}
    (initial : Position)
    (field : RootIndexed.StepField PUnit α Mark) :
    BranchingWalk α Mark Position :=
  RootIndexed.BranchingWalk.ofStepField (fun _ => initial) field

theorem iidRealization_measurable {α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (initial : Position) :
    Measurable (iidRealization (α := α) (Mark := Mark) initial) := by
  intro s hs
  rw [MeasurableSpace.measurableSet_comap] at hs
  rcases hs with ⟨t, ht, rfl⟩
  change MeasurableSet
    ((fun field : RootIndexed.StepField PUnit α Mark =>
      ((iidRealization initial field).step,
        (iidRealization initial field).initial)) ⁻¹' t)
  have hpair : Measurable
      (fun field : RootIndexed.StepField PUnit α Mark =>
        ((iidRealization initial field).step,
          (iidRealization initial field).initial)) := by
    change Measurable (fun field => (field, fun _ : PUnit => initial))
    exact measurable_id.prodMk measurable_const
  exact hpair ht

theorem iid_step_measurable {α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position] :
    Measurable (fun walk : BranchingWalk α Mark Position => walk.step) := by
  have hpair : Measurable
      (fun walk : BranchingWalk α Mark Position => (walk.step, walk.initial)) :=
    Measurable.of_comap_le le_rfl
  exact measurable_fst.comp hpair

/-- The standard i.i.d. branching walk: the complete offspring configuration
at each address has law `μ`, independently across addresses. -/
noncomputable def iid {α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (μ : Measure (Step α Mark)) (initial : Position)
    [IsProbabilityMeasure μ] : WalkLaw α Mark Position := by
  exact ⟨(RootIndexed.stepFieldLaw (Root := PUnit) μ).map
    (iidRealization initial), by infer_instance⟩

@[simp] theorem iid_toMeasure {α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (μ : Measure (Step α Mark)) (initial : Position)
    [IsProbabilityMeasure μ] :
    ((iid μ initial : WalkLaw α Mark Position) :
      Measure (BranchingWalk α Mark Position)) =
        (RootIndexed.stepFieldLaw (Root := PUnit) μ).map
          (iidRealization initial) := rfl

theorem iid_stepFieldLaw {α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (μ : Measure (Step α Mark)) (initial : Position)
    [IsProbabilityMeasure μ] :
    ((iid μ initial : WalkLaw α Mark Position) :
      Measure (BranchingWalk α Mark Position)).map
        (fun walk => walk.step) =
      RootIndexed.stepFieldLaw (Root := PUnit) μ := by
  rw [iid_toMeasure, Measure.map_map]
  · have hcomp : ((fun walk : BranchingWalk α Mark Position => walk.step) ∘
        iidRealization initial) = id := by
      funext field
      rfl
    rw [hcomp, Measure.map_id]
  · exact iid_step_measurable
  · exact iidRealization_measurable initial

/-- Mapping every child's mark commutes with the canonical i.i.d. branching
walk law. -/
theorem iid_mapMarks {α Mark Mark' Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Mark'] [MeasurableSpace Position]
    (μ : Measure (Step α Mark)) (initial : Position)
    [IsProbabilityMeasure μ] (f : Mark → Mark') (hf : Measurable f) :
    iid (μ.map (Step.map f)) initial =
      (iid μ initial).map
        (Combinatorics.Branching.RootIndexed.BranchingWalk.mapMarks f) := by
  have hwalkMap : Measurable
      (Combinatorics.Branching.RootIndexed.BranchingWalk.mapMarks
        (Root := PUnit) (α := α) (Position := Position) f) :=
    Combinatorics.Branching.RootIndexed.BranchingWalk.mapMarks_measurable
      (Root := PUnit) (α := α) (Position := Position) hf
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map, iid_toMeasure, iid_toMeasure]
  calc
    (RootIndexed.stepFieldLaw (Root := PUnit) (μ.map (Step.map f))).map
        (iidRealization initial) =
      ((RootIndexed.stepFieldLaw (Root := PUnit) μ).map
        (fun field r => StepField.map f (field r))).map
          (iidRealization initial) := by
            rw [← RootIndexed.stepFieldLaw_mapMarks μ f hf]
    _ = (RootIndexed.stepFieldLaw (Root := PUnit) μ).map
          (iidRealization initial ∘ fun field r => StepField.map f (field r)) := by
            rw [Measure.map_map (iidRealization_measurable initial)
              (by
                apply Measurable.of_eval
                intro r
                exact (StepField.map_measurable hf).comp
                  (measurable_pi_apply r))]
    _ = (RootIndexed.stepFieldLaw (Root := PUnit) μ).map
          (fun field => (iidRealization initial field).mapMarks f) := by
            congr 1
    _ = ((RootIndexed.stepFieldLaw (Root := PUnit) μ).map
          (iidRealization initial)).map
          (Combinatorics.Branching.RootIndexed.BranchingWalk.mapMarks f) := by
            rw [Measure.map_map hwalkMap (iidRealization_measurable initial)]
            rfl

/-- Changing the deterministic initial position commutes with the canonical
i.i.d. branching walk law. -/
theorem iid_mapInitial {α Mark Position Position' : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [MeasurableSpace Position']
    (μ : Measure (Step α Mark)) (initial : Position)
    [IsProbabilityMeasure μ] (f : Position → Position')
    (hf : Measurable f) :
    iid μ (f initial) =
      (iid μ initial).map
        (Combinatorics.Branching.RootIndexed.BranchingWalk.mapInitial f) := by
  have hwalkMap : Measurable
      (Combinatorics.Branching.RootIndexed.BranchingWalk.mapInitial
        (Root := PUnit) (α := α) (Mark := Mark) f) :=
    Combinatorics.Branching.RootIndexed.BranchingWalk.mapInitial_measurable
      (Root := PUnit) (α := α) (Mark := Mark) hf
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map, iid_toMeasure, iid_toMeasure]
  rw [Measure.map_map hwalkMap (iidRealization_measurable initial)]
  rfl

end ProbabilityTheory.BranchingRandomWalk

end
