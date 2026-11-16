/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Filtration

/-!
# Measurable particle matching

A coupling may match a random object particle to a random partner particle.
Reading the partner step only requires countability of the labels that can
actually occur.  Neither the ambient root type nor the child-slot type is
assumed countable.

## Public declarations

At a partner coordinate, `valueAtObjectPreimage` reads the matched object value
when the object preimage is present and otherwise reads the fallback value:

\[
\operatorname{valueAtObjectPreimage}(S,F,p)(\omega,q)
=\begin{cases}
S(\omega,r),&p(\omega,q)=\operatorname{some}(r),\\
F(\omega,q),&p(\omega,q)=\operatorname{none}.
\end{cases}
\]

* `valueAtObjectPreimage` reads object data at the optional object preimage of
  a partner label and uses fallback data when the object preimage is absent.
* `RootIndexed.reindexedSteps` transports steps along a sample-dependent
  particle map; `RootIndexed.reindexedSteps_measurable` proves its
  measurability from coordinate measurability and map-fibre assumptions.
* `partnerOfObject_fiber_measurable` and
  `partnerOfObject_range_countable` give fibre-measurability and
  countable-range criteria for the partner assigned to a random object.
* `RootIndexed.partnerStep_measurable` proves measurability of the step read
  at a matched partner particle.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Coupling

open Combinatorics.UlamHarris Combinatorics.Branching

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- Read an object coordinate when a partner label has a matched object
preimage, and otherwise read the fallback coordinate at that partner. -/
def valueAtObjectPreimage {Y : Type*}
    (objectField fallbackField : Ω → ι → Y)
    (objectPreimageAtPartner : Ω → ι → Option ι) (ω : Ω) (partner : ι) : Y :=
  (objectPreimageAtPartner ω partner).elim (fallbackField ω partner)
    (objectField ω)

/-- Read, for every object particle label, the partner step at the particle
assigned by a sample-dependent matching.  This is a family of one-step
marks, rather than a branching field: the matching may change from one
generation to the next. -/
def RootIndexed.reindexedSteps {Root α X : Type*}
    (partnerOfObject : RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α)
    (ω : RootIndexed.StepField Root α X) :
    RootIndexed.TreeNode Root α → Step α X :=
  fun p => ω (partnerOfObject ω p).1 (partnerOfObject ω p).2

/-- Fibres of a particle map remain measurable after evaluating it at a
random particle with countable range.  Countability is localized to the
object selector; the ambient particle type may be uncountable. -/
theorem partnerOfObject_fiber_measurable
    (objectSelector : Ω → ι) (partnerOfObject : Ω → ι → ι)
    (hobjectSelectorCount : (Set.range objectSelector).Countable)
    (hobjectSelectorFiber : ∀ p, MeasurableSet {ω | objectSelector ω = p})
    (hpartnerOfObjectFiber : ∀ p q, MeasurableSet {ω | partnerOfObject ω p = q})
    (q : ι) :
    MeasurableSet {ω | partnerOfObject ω (objectSelector ω) = q} := by
  let S : Set ι := Set.range objectSelector
  let _ : Countable S := Set.countable_coe_iff.mpr hobjectSelectorCount
  have hset : {ω | partnerOfObject ω (objectSelector ω) = q} =
      ⋃ p : S, {ω | objectSelector ω = p.1} ∩
        {ω | partnerOfObject ω p.1 = q} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨⟨objectSelector ω, Set.mem_range_self ω⟩, rfl, h⟩
    · rintro ⟨p, hp, hm⟩
      simpa [hp] using hm
  rw [hset]
  exact MeasurableSet.iUnion fun p =>
    (hobjectSelectorFiber p.1).inter (hpartnerOfObjectFiber p.1 q)

omit [MeasurableSpace Ω] in
/-- The range of a particle map evaluated at a countably valued random
particle is countable when every fixed-particle coordinate is countably
valued. -/
theorem partnerOfObject_range_countable
    (objectSelector : Ω → ι) (partnerOfObject : Ω → ι → ι)
    (hobjectSelectorCount : (Set.range objectSelector).Countable)
    (hpartnerOfObjectCount : ∀ p, (Set.range fun ω => partnerOfObject ω p).Countable) :
    (Set.range fun ω => partnerOfObject ω (objectSelector ω)).Countable := by
  let S : Set ι := Set.range objectSelector
  let _ : Countable S := Set.countable_coe_iff.mpr hobjectSelectorCount
  have hsubset : Set.range (fun ω => partnerOfObject ω (objectSelector ω)) ⊆
      ⋃ p : S, Set.range fun ω => partnerOfObject ω p.1 := by
    rintro q ⟨ω, rfl⟩
    apply Set.mem_iUnion_of_mem
      (⟨objectSelector ω, Set.mem_range_self ω⟩ : S)
    exact Set.mem_range_self ω
  exact (Set.countable_iUnion fun p : S => hpartnerOfObjectCount p.1).mono hsubset

/-- A partner step selected through a random particle matching is observable
from the generation domain flow.  All countability assumptions concern only
actual selector ranges. -/
theorem RootIndexed.partnerStep_measurable
    {Root α X : Type*} [MeasurableSpace X] {n : ℕ}
    (objectSelector : RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α)
    (partnerOfObject : RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α)
    (hobjectSelectorCount : (Set.range objectSelector).Countable)
    (hobjectSelectorFiber : ∀ p, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {ω | objectSelector ω = p})
    (hpartnerOfObjectCount : ∀ p,
      (Set.range fun ω => partnerOfObject ω p).Countable)
    (hpartnerOfObjectFiber : ∀ p q, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
        {ω | partnerOfObject ω p = q})
    (hdepth : ∀ ω,
      (partnerOfObject ω (objectSelector ω)).2.length < n) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (fun ω => ω (partnerOfObject ω (objectSelector ω)).1
        (partnerOfObject ω (objectSelector ω)).2) := by
  let _ : MeasurableSpace (RootIndexed.StepField Root α X) :=
    RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n
  let chosen := fun ω => partnerOfObject ω (objectSelector ω)
  apply RootIndexed.selectedStep_measurable chosen
  · exact fun q => partnerOfObject_fiber_measurable objectSelector partnerOfObject
      hobjectSelectorCount hobjectSelectorFiber hpartnerOfObjectFiber q
  · exact hdepth
  · exact partnerOfObject_range_countable objectSelector partnerOfObject
      hobjectSelectorCount hpartnerOfObjectCount

/-- All fixed object labels may read their matched partner steps
simultaneously.  The object-label type itself need not be countable because
measurability into a function space is checked coordinatewise. -/
theorem RootIndexed.reindexedSteps_measurable
    {Root α X : Type*} [MeasurableSpace X] {n : ℕ}
    (partnerOfObject : RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α)
    (hpartnerOfObjectCount : ∀ p,
      (Set.range fun ω => partnerOfObject ω p).Countable)
    (hpartnerOfObjectFiber : ∀ p q, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
        {ω | partnerOfObject ω p = q})
    (hdepth : ∀ ω p, (partnerOfObject ω p).2.length < n) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (RootIndexed.reindexedSteps partnerOfObject) := by
  let _ : MeasurableSpace (RootIndexed.StepField Root α X) :=
    RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n
  apply measurable_pi_iff.mpr
  intro p
  exact RootIndexed.selectedStep_measurable (fun ω => partnerOfObject ω p)
    (hpartnerOfObjectFiber p) (fun ω => hdepth ω p) (hpartnerOfObjectCount p)

end ProbabilityTheory.BranchingRandomWalk.Coupling
