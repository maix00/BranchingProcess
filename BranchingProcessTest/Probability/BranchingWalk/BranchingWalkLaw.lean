import Probability.BranchingRandomWalk.Law
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Arbitrary branching-walk laws need not branch independently

This model uses one shared Boolean to set every offspring coordinate.  Its
pushforward is a valid `WalkLaw`, showing why the general law type makes no
i.i.d. or branching-property claim.
-/

open MeasureTheory
open Combinatorics.UlamHarris Combinatorics.Branching

def sharedBoolWalk (b : Bool) : BranchingWalk PUnit Bool Unit :=
  RootIndexed.BranchingWalk.ofStepField (fun _ => ())
    (fun _ _ _ => some b)

theorem sharedBoolWalk_coordinate (b : Bool) (r : PUnit)
    (u : TreeNode PUnit) (i : PUnit) :
    (sharedBoolWalk b).step r u i = some b := rfl

theorem sharedBoolWalk_coordinates_equal (b : Bool)
    (r s : PUnit) (u v : TreeNode PUnit) (i j : PUnit) :
    (sharedBoolWalk b).step r u i = (sharedBoolWalk b).step s v j := rfl

theorem measurable_sharedBoolWalk : Measurable sharedBoolWalk := by
  intro s hs
  rw [MeasurableSpace.measurableSet_comap] at hs
  rcases hs with ⟨t, ht, rfl⟩
  change MeasurableSet
    ((fun b : Bool => ((sharedBoolWalk b).step,
      (sharedBoolWalk b).initial)) ⁻¹' t)
  have hstep : Measurable (fun b : Bool =>
      fun r : PUnit => fun u : TreeNode PUnit =>
        fun i : PUnit => some b) := by
    apply measurable_pi_iff.mpr
    intro r
    apply measurable_pi_iff.mpr
    intro u
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_option_some.comp measurable_id
  have hpair : Measurable (fun b : Bool =>
      ((sharedBoolWalk b).step, (sharedBoolWalk b).initial)) := by
    change Measurable (fun b : Bool =>
      ((fun r : PUnit => fun u : TreeNode PUnit =>
        fun i : PUnit => some b), fun _ : PUnit => ()))
    exact hstep.prodMk measurable_const
  exact hpair ht

noncomputable def sharedBoolWalkLaw (ν : Measure Bool)
    [IsProbabilityMeasure ν] :
    ProbabilityTheory.BranchingRandomWalk.WalkLaw PUnit Bool Unit :=
  ⟨ν.map sharedBoolWalk, by infer_instance⟩

@[simp] theorem sharedBoolWalkLaw_measure (ν : Measure Bool)
    [IsProbabilityMeasure ν] :
    (sharedBoolWalkLaw ν : Measure (BranchingWalk PUnit Bool Unit)) =
      ν.map sharedBoolWalk := rfl
