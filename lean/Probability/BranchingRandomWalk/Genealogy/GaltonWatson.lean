import Probability.BranchingRandomWalk.Step.Map
import Probability.BranchingRandomWalk.Step.Law

/-!
# Galton--Watson specialization of a random branching step

A Galton--Watson reproduction field is the single-root i.i.d. step field after
all spatial marks have been forgotten. Its sample object remains the existing
unit-marked `StepField`; this module only names its law and records its
coordinate marginal.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching

/-- The single-root i.i.d. Galton--Watson field law underlying `S`. -/
noncomputable def Step.galtonWatsonFieldLaw
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : Step Ω ι X) (P : Measure Ω) :
    Measure (StepField ι PUnit.{1}) :=
  stepFieldLaw (S.unmarkedLaw P)

instance Step.galtonWatsonFieldLaw.isProbabilityMeasure
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : Step Ω ι X) (P : Measure Ω) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (S.galtonWatsonFieldLaw P) := by
  unfold Step.galtonWatsonFieldLaw
  infer_instance

/-- Every address in the Galton--Watson field has the unit-marked reproduction
law obtained from `S`. -/
theorem Step.galtonWatsonFieldLaw_coordinate
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : Step Ω ι X) (P : Measure Ω) [IsProbabilityMeasure P]
    (u : TreeNode ι) :
    (S.galtonWatsonFieldLaw P).map (fun β => β u) =
      S.unmarkedLaw P := by
  exact stepFieldLaw_coordinate (S.unmarkedLaw P) u

/-- The Galton--Watson law is the law of the single-root unmarked branching
process obtained from the i.i.d. unit-marked step field. -/
noncomputable def Step.galtonWatsonLaw
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : Step Ω ι X) (P : Measure Ω) :
    Measure (Combinatorics.Branching.Process ι) :=
  (S.galtonWatsonFieldLaw P).map
    Combinatorics.Branching.branchingOfStepField

instance Step.galtonWatsonLaw.isProbabilityMeasure
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : Step Ω ι X) (P : Measure Ω) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (S.galtonWatsonLaw P) := by
  unfold Step.galtonWatsonLaw
  infer_instance

end ProbabilityTheory.BranchingRandomWalk
