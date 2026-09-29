import Probability.BranchingRandomWalk.Basic
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Measurability
import Probability.BranchingRandomWalk.Step.Position.Measurability
import Combinatorics.BranchingWalk.Genealogy.Survival
import Combinatorics.BranchingWalk.Walk.Path.Position
import Mathlib.MeasureTheory.Measure.Map

/-!
# Random walks as one-branch branching random walks

A random walk is exactly the singleton child-slot specialization of a
branching random walk. The unique possible child may be absent, so this basic
notion also permits killing or extinction. Laws obtained from an increment
sequence form the everywhere-present special case used by the spine.
-/

open MeasureTheory

namespace ProbabilityTheory

open Combinatorics.UlamHarris Combinatorics.Branching
open BranchingRandomWalk

/-- A random walk is a branching random walk with one possible child slot. -/
abbrev RandomWalk (Mark Position : Type*)
    [MeasurableSpace Mark] [MeasurableSpace Position] :=
  BranchingRandomWalk PUnit Mark Position

namespace RandomWalk

/-- Almost-sure permanent survival is an additional property of a random
walk. It is not built into `RandomWalk`: a singleton-slot walk may be killed. -/
def SurvivesForever {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (walk : RandomWalk Mark Position) : Prop :=
  ∀ᵐ realization ∂walk.law, realization.SurvivesForever

/-- Almost-sure permanent survival of a random walk can equivalently be
checked generation by generation.  The equivalence uses the singleton-slot
structure of `RandomWalk`, not an additional branching assumption. -/
theorem survivesForever_iff_ae_survivesEveryGeneration
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (walk : RandomWalk Mark Position) :
    walk.SurvivesForever ↔
      ∀ᵐ realization ∂walk.law,
        ∀ n, surviveAlong (realization.step PUnit.unit) []
          (Walk.lineNode n) := by
  rw [SurvivesForever]
  constructor
  · intro h
    filter_upwards [h] with realization hrealization n
    exact (Walk.survivesForever_iff_survivesEveryGeneration realization).mp
      hrealization n
  · intro h
    filter_upwards [h] with realization hrealization
    exact (Walk.survivesForever_iff_survivesEveryGeneration realization).mpr
      hrealization

theorem measurable_step
    {α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position] :
    Measurable (fun walk : BranchingWalk α Mark Position =>
      walk.step PUnit.unit) := by
  have hpair : Measurable
      (fun walk : BranchingWalk α Mark Position =>
        (walk.step, walk.initial)) :=
    Measurable.of_comap_le le_rfl
  exact (measurable_pi_apply PUnit.unit).comp (measurable_fst.comp hpair)

theorem measurableSet_survivesAlong
    {α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (u : TreeNode α) :
    MeasurableSet {walk : BranchingWalk α Mark Position |
      surviveAlong (walk.step PUnit.unit) [] u} := by
  have hs : MeasurableSet {step : StepField α Mark |
      surviveAlong step [] u} :=
    (generationFiltration (M := Step α Mark)).le u.length _
      (surviveAlong_root_measurableSet (X := Mark) u)
  exact hs.preimage measurable_step

theorem measurableSet_survivesForever
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position] :
    MeasurableSet {walk : Walk Mark Position | walk.SurvivesForever} := by
  rw [show {walk : Walk Mark Position | walk.SurvivesForever} =
      ⋂ n : ℕ, {walk | surviveAlong (walk.step PUnit.unit) []
        (Walk.lineNode n)} by
    ext walk
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact Walk.survivesForever_iff_survivesEveryGeneration walk]
  exact MeasurableSet.iInter fun n =>
    measurableSet_survivesAlong (Walk.lineNode n)

/-- Encoding an increment sequence as its everywhere-present singleton-slot
walk is measurable. -/
theorem measurable_ofIncrements
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (initial : Position) :
    Measurable (Walk.ofIncrements initial : (ℕ → Mark) → Walk Mark Position) := by
  intro s hs
  rw [MeasurableSpace.measurableSet_comap] at hs
  rcases hs with ⟨t, ht, rfl⟩
  apply ((measurable_pi_iff.mpr fun _ : PUnit =>
    measurable_pi_iff.mpr fun u =>
      measurable_pi_iff.mpr fun _ : PUnit =>
        measurable_option_some.comp (measurable_pi_apply u.length)).prodMk
      (measurable_pi_iff.mpr fun _ : PUnit => measurable_const)) ht

/-- The everywhere-present random walk induced by a fixed initial position and
a probability law on increment paths. -/
noncomputable def ofIncrementLaw
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (initial : Position) (incrementLaw : Measure (ℕ → Mark))
    [IsProbabilityMeasure incrementLaw] : RandomWalk Mark Position :=
  ⟨incrementLaw.map (Walk.ofIncrements initial), by infer_instance⟩

@[simp] theorem ofIncrementLaw_law
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (initial : Position) (incrementLaw : Measure (ℕ → Mark))
    [IsProbabilityMeasure incrementLaw] :
    (ofIncrementLaw initial incrementLaw : RandomWalk Mark Position).law =
      incrementLaw.map (Walk.ofIncrements initial) := rfl

/-- An arbitrary sample of a possibly killed random walk, viewed as a standard
`Time → Sample → Option State` process. `none` records that the unique lineage
has died before the requested time. -/
noncomputable def process
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] (d : Mark → Position) :
    ℕ → Walk Mark Position → Option Position := by
  classical
  exact fun n walk =>
    if surviveAlong (walk.step PUnit.unit) [] (Walk.lineNode n)
      then some (walk.position d PUnit.unit (Walk.lineNode n)) else none

/-- Every time coordinate of the possibly killed random walk is measurable.
This includes both survival and the accumulated abstract position. -/
theorem process_measurable
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    (d : Mark → Position) (hd : Measurable d) (n : ℕ) :
    Measurable (process d n) := by
  classical
  have hpair : Measurable
      (fun walk : Walk Mark Position => (walk.step, walk.initial)) :=
    Measurable.of_comap_le le_rfl
  have hstep : Measurable (fun walk : Walk Mark Position => walk.step) :=
    measurable_fst.comp hpair
  have hinitial : Measurable
      (fun walk : Walk Mark Position => walk.initial PUnit.unit) :=
    (measurable_pi_apply PUnit.unit).comp (measurable_snd.comp hpair)
  have hdisplaceField : Measurable
      (fun step : RootIndexed.StepField PUnit PUnit Mark =>
        RootIndexed.displace d step PUnit.unit (Walk.lineNode n)) := by
    exact (RootIndexed.displace_measurable d hd PUnit.unit []
      (Walk.lineNode n) n (by simp)).mono
        (RootIndexed.stepFiltration.le n) le_rfl
  have hposition : Measurable
      (fun walk : Walk Mark Position =>
        walk.position d PUnit.unit (Walk.lineNode n)) := by
    change Measurable
      ((fun walk : Walk Mark Position => walk.initial PUnit.unit) +
        fun walk => RootIndexed.displace d walk.step PUnit.unit
          (Walk.lineNode n))
    exact hinitial.add (hdisplaceField.comp hstep)
  unfold process
  exact Measurable.ite (measurableSet_survivesAlong (Walk.lineNode n))
    (measurable_option_some.comp hposition) measurable_const

@[simp] theorem process_ofIncrements
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] (d : Mark → Position)
    (initial : Position) (increment : ℕ → Mark) (n : ℕ) :
    process d n (Walk.ofIncrements initial increment) =
      some (Walk.positionProcess initial n (d ∘ increment)) := by
  classical
  rw [process]
  split
  · exact congrArg some
      (Walk.position_lineNode_eq_positionProcess d initial increment n)
  · rename_i h
    exfalso
    apply h
    change surviveAlong (Walk.stepFieldOfIncrements increment) []
      (Walk.lineNode n)
    exact Walk.surviveAlong_stepFieldOfIncrements increment _ _

/-- The property that a random-walk law is realized by an everywhere-present
increment path. It is additional structure, rather than part of the basic
(possibly killed) random-walk definition. -/
def IsIncrementPathRealization
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (walk : RandomWalk Mark Position) : Prop :=
  ∃ (initial : Position) (incrementLaw : Measure (ℕ → Mark)),
    IsProbabilityMeasure incrementLaw ∧
      walk.law = incrementLaw.map (Walk.ofIncrements initial)

theorem isIncrementPathRealization_ofIncrementLaw
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (initial : Position) (incrementLaw : Measure (ℕ → Mark))
    [IsProbabilityMeasure incrementLaw] :
    IsIncrementPathRealization
      (ofIncrementLaw initial incrementLaw : RandomWalk Mark Position) :=
  ⟨initial, incrementLaw, inferInstance, rfl⟩

/-- A random walk constructed from an increment-path law survives forever
almost surely. -/
theorem survivesForever_ofIncrementLaw
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (initial : Position) (incrementLaw : Measure (ℕ → Mark))
    [IsProbabilityMeasure incrementLaw] :
    SurvivesForever
      (ofIncrementLaw initial incrementLaw : RandomWalk Mark Position) := by
  rw [SurvivesForever, ofIncrementLaw_law,
    MeasureTheory.ae_map_iff (measurable_ofIncrements initial).aemeasurable
      measurableSet_survivesForever]
  exact Filter.Eventually.of_forall fun increment =>
    Walk.ofIncrements_survivesForever initial increment

/-- Every random walk realized by an everywhere-present increment path
survives forever almost surely.  This is a consequence of the realization
property; permanent survival remains independent of the definition of
`RandomWalk` itself. -/
theorem IsIncrementPathRealization.survivesForever
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    {walk : RandomWalk Mark Position}
    (hwalk : IsIncrementPathRealization walk) :
  SurvivesForever walk := by
  obtain ⟨initial, incrementLaw, hprobability, hlaw⟩ := hwalk
  rw [SurvivesForever, hlaw]
  simpa [SurvivesForever, ofIncrementLaw_law] using
    (@survivesForever_ofIncrementLaw Mark Position _ _ initial incrementLaw
      hprobability)

end RandomWalk
end ProbabilityTheory
