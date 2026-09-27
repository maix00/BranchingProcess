import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Filtration

/-!
# Measurable particle matching

A coupling may match a random source particle to a random target particle.
Reading the target step only requires countability of the labels that can
actually occur.  Neither the ambient root type nor the child-slot type is
assumed countable.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.Coupling

open Combinatorics.UlamHarris Combinatorics.Branching

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- Read, for every source particle label, the target step at the particle
assigned by a sample-dependent matching.  This is a family of one-step
marks, rather than a branching field: the matching may change from one
generation to the next. -/
def RootIndexed.matchedSteps {Root α X : Type*}
    (matchParticle : RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α)
    (ω : RootIndexed.StepField Root α X) :
    RootIndexed.TreeNode Root α → Step α X :=
  fun p => ω (matchParticle ω p).1 (matchParticle ω p).2

/-- Fibres of a particle map remain measurable after evaluating it at a
random particle with countable range.  Countability is localized to the
source selector; the ambient particle type may be uncountable. -/
theorem selectedParticle_fiber_measurable
    (source : Ω → ι) (matchParticle : Ω → ι → ι)
    (hsourceCount : (Set.range source).Countable)
    (hsourceFiber : ∀ p, MeasurableSet {ω | source ω = p})
    (hmatchFiber : ∀ p q, MeasurableSet {ω | matchParticle ω p = q})
    (q : ι) :
    MeasurableSet {ω | matchParticle ω (source ω) = q} := by
  let S : Set ι := Set.range source
  let _ : Countable S := Set.countable_coe_iff.mpr hsourceCount
  have hset : {ω | matchParticle ω (source ω) = q} =
      ⋃ p : S, {ω | source ω = p.1} ∩
        {ω | matchParticle ω p.1 = q} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨⟨source ω, Set.mem_range_self ω⟩, rfl, h⟩
    · rintro ⟨p, hp, hm⟩
      simpa [hp] using hm
  rw [hset]
  exact MeasurableSet.iUnion fun p =>
    (hsourceFiber p.1).inter (hmatchFiber p.1 q)

omit [MeasurableSpace Ω] in
/-- The range of a particle map evaluated at a countably valued random
particle is countable when every fixed-particle coordinate is countably
valued. -/
theorem selectedParticle_range_countable
    (source : Ω → ι) (matchParticle : Ω → ι → ι)
    (hsourceCount : (Set.range source).Countable)
    (hmatchCount : ∀ p, (Set.range fun ω => matchParticle ω p).Countable) :
    (Set.range fun ω => matchParticle ω (source ω)).Countable := by
  let S : Set ι := Set.range source
  let _ : Countable S := Set.countable_coe_iff.mpr hsourceCount
  have hsubset : Set.range (fun ω => matchParticle ω (source ω)) ⊆
      ⋃ p : S, Set.range fun ω => matchParticle ω p.1 := by
    rintro q ⟨ω, rfl⟩
    apply Set.mem_iUnion_of_mem
      (⟨source ω, Set.mem_range_self ω⟩ : S)
    exact Set.mem_range_self ω
  exact (Set.countable_iUnion fun p : S => hmatchCount p.1).mono hsubset

/-- A target step selected through a random particle matching is observable
from the generation domain flow.  All countability assumptions concern only
actual selector ranges. -/
theorem RootIndexed.matchedStep_measurable
    {Root α X : Type*} [MeasurableSpace X] {n : ℕ}
    (source : RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α)
    (matchParticle : RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α)
    (hsourceCount : (Set.range source).Countable)
    (hsourceFiber : ∀ p, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {ω | source ω = p})
    (hmatchCount : ∀ p,
      (Set.range fun ω => matchParticle ω p).Countable)
    (hmatchFiber : ∀ p q, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
        {ω | matchParticle ω p = q})
    (hdepth : ∀ ω,
      (matchParticle ω (source ω)).2.length < n) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (fun ω => ω (matchParticle ω (source ω)).1
        (matchParticle ω (source ω)).2) := by
  let _ : MeasurableSpace (RootIndexed.StepField Root α X) :=
    RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n
  let chosen := fun ω => matchParticle ω (source ω)
  apply RootIndexed.selectedStep_measurable chosen
  · exact fun q => selectedParticle_fiber_measurable source matchParticle
      hsourceCount hsourceFiber hmatchFiber q
  · exact hdepth
  · exact selectedParticle_range_countable source matchParticle
      hsourceCount hmatchCount

/-- All fixed source labels may read their matched target steps
simultaneously.  The source-label type itself need not be countable because
measurability into a function space is checked coordinatewise. -/
theorem RootIndexed.matchedSteps_measurable
    {Root α X : Type*} [MeasurableSpace X] {n : ℕ}
    (matchParticle : RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α)
    (hmatchCount : ∀ p,
      (Set.range fun ω => matchParticle ω p).Countable)
    (hmatchFiber : ∀ p q, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
        {ω | matchParticle ω p = q})
    (hdepth : ∀ ω p, (matchParticle ω p).2.length < n) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (RootIndexed.matchedSteps matchParticle) := by
  let _ : MeasurableSpace (RootIndexed.StepField Root α X) :=
    RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n
  apply measurable_pi_iff.mpr
  intro p
  exact RootIndexed.selectedStep_measurable (fun ω => matchParticle ω p)
    (hmatchFiber p) (fun ω => hdepth ω p) (hmatchCount p)

end ProbabilityTheory.BranchingRandomWalk.Selection.Coupling
