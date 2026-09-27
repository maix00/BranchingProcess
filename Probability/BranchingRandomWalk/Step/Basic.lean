import Combinatorics.BranchingWalk.Step.PointMeasure
import Combinatorics.BranchingWalk.Step.Monotone
import Combinatorics.BranchingWalk.Step.Measurability

/-!
# Random branching steps

Randomness begins with `X`-valued slot displacements. Each slot also has a
measurable presence event. Evaluating both at one sample gives the deterministic
optional step `ι → Option X`; absence is introduced only at this assembly
boundary.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

/-- The `X`-valued random displacement in one child slot. -/
abbrev StepDisplace (Ω X : Type*) := Ω → X

/-- A random branching step: a measurable presence event and an `X`-valued
measurable displacement for every slot. The displacement on an absent slot is
ignored. -/
structure Step (Ω ι X : Type*) [MeasurableSpace Ω]
    [MeasurableSpace X] where
  present : ι → Ω → Bool
  measurable_present : ∀ i, Measurable (present i)
  displace : ι → StepDisplace Ω X
  measurable_displace : ∀ i, Measurable (displace i)

/-- Assemble the coordinate random displacements into a deterministic step at one
sample. -/
def Step.toFun {Ω ι X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (S : Step Ω ι X) (ω : Ω) :
    Combinatorics.Branching.Step ι X :=
  fun i => if S.present i ω then some (S.displace i ω) else none

instance {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] :
    CoeFun (Step Ω ι X)
      (fun _ => Ω → Combinatorics.Branching.Step ι X) :=
  ⟨Step.toFun⟩

@[simp] theorem Step.apply_eq_some_iff
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : Step Ω ι X) (ω : Ω) (i : ι) (x : X) :
    S ω i = some x ↔ S.present i ω = true ∧ S.displace i ω = x := by
  change (if S.present i ω then some (S.displace i ω) else none) = some x ↔
    S.present i ω = true ∧ S.displace i ω = x
  simp

@[simp] theorem Step.apply_eq_none_iff
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : Step Ω ι X) (ω : Ω) (i : ι) :
    S ω i = none ↔ S.present i ω = false := by
  change (if S.present i ω then some (S.displace i ω) else none) = none ↔
    S.present i ω = false
  simp

/-- The assembled deterministic step is measurable because every random
displacement coordinate is measurable. -/
theorem Step.measurable_toFun
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : Step Ω ι X) : Measurable S := by
  rw [measurable_pi_iff]
  intro i
  change Measurable (fun ω =>
    if S.present i ω then some (S.displace i ω) else none)
  have hp : MeasurableSet {ω | S.present i ω = true} :=
    (measurableSet_singleton true).preimage (S.measurable_present i)
  exact (measurable_option_some.comp (S.measurable_displace i)).ite hp measurable_const

/-- The step law is the law of the assembled coordinate family. -/
noncomputable def Step.indexedLaw
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : Step Ω ι X) (P : Measure Ω) :
    Measure (Combinatorics.Branching.Step ι X) :=
  P.map S

instance {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : Step Ω ι X) (P : Measure Ω)
    [IsProbabilityMeasure P] : IsProbabilityMeasure (S.indexedLaw P) := by
  unfold Step.indexedLaw
  infer_instance

/-- The random point measure is a deterministic observation of the assembled
step. -/
noncomputable def Step.pointMeasure
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : Step Ω ι X) : Ω → Measure X :=
  fun ω => stepPointMeasure (S ω)

/-- The branching law: the distribution of the random point measure generated
by all present displacement coordinates. -/
noncomputable def Step.branchingLaw
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] [Zero X] (S : Step Ω ι X) (P : Measure Ω) :
    Measure (Measure X) :=
  P.map S.pointMeasure

instance Step.branchingLaw.isProbabilityMeasure
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] [Zero X] (S : Step Ω ι X) (P : Measure Ω)
    [IsProbabilityMeasure P] : IsProbabilityMeasure (S.branchingLaw P) := by
  unfold Step.branchingLaw
  infer_instance

theorem Step.pointMeasure_measurable
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] [Zero X] (S : Step Ω ι X) :
    Measurable S.pointMeasure :=
  stepPointMeasure_measurable.comp S.measurable_toFun

/-- Taking the point-measure observation commutes with taking the step law. -/
theorem Step.indexedLaw_map_pointMeasure
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] [Zero X] (S : Step Ω ι X) (P : Measure Ω) :
    (S.indexedLaw P).map stepPointMeasure = S.branchingLaw P := by
  unfold Step.indexedLaw Step.branchingLaw Step.pointMeasure
  rw [Measure.map_map stepPointMeasure_measurable S.measurable_toFun]
  rfl

theorem Step.indexedLaw_apply
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (S : Step Ω ι X) (P : Measure Ω)
    (s : Set (Combinatorics.Branching.Step ι X))
    (hs : MeasurableSet s) :
    S.indexedLaw P s = P (S ⁻¹' s) := by
  exact Measure.map_apply S.measurable_toFun hs

end ProbabilityTheory.BranchingRandomWalk
