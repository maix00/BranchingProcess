import Probability.BranchingRandomWalk.Selection.Coupling.SelectedPopulation
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.RootIndexed

/-!
# Coupling a labelled step-selected trial to an `N`-selected population

A single-root trial is embedded into the multi-root particle labels used by
the cloud coupling. The source and target may be built from different step
fields on the same sample. Their relationship is stated only through selected
slot inclusion and equality of the corresponding mapped increments.
-/

namespace ProbabilityTheory.BranchingRandomWalk.Selection.Coupling

open Combinatorics.UlamHarris
open Combinatorics.Branching
open Combinatorics.Branching.Selection.Coupling

variable {Root α Mark Position Value : Type*}

/-- Data-valued canonical coupling of a labelled step-selected trial to the
multi-root first-`N` population.  At generation zero the labelled root is
included by identity; every successor map is the canonical equal-rank map. -/
noncomputable def generationInjection_labelledPopulation
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (φ : Position → Value) (d : Mark → Position) (N : ℕ)
    (R : Step.FiniteSelection α Mark)
    (roots : Finset Root) (r : Root) (hr : r ∈ roots)
    (initial : Root → Position)
    (sourceStep : RootIndexed.StepField Root α Mark →
      RootIndexed.StepField Root α Mark)
    (hadmits : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      Combinatorics.Branching.Selection.NSelection.AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initial d φ (n + 1) ω)
        (RootIndexed.childrenAtGeneration n parents ω))
    (hcard : ∀ n ω,
      (RootIndexed.StepSelection.labelledPopulation
        R n (sourceStep ω) r).card ≤ N)
    (hslots : ∀ n ω p,
      p ∈ RootIndexed.StepSelection.labelledPopulation
        R n (sourceStep ω) r →
      ∀ q, q ∈ RootIndexed.selectedPopulation
        N roots initial d φ hadmits n ω →
      φ ((RootIndexed.BranchingWalk.ofStepField initial ω).position
          d q.1 q.2) ≤
        φ ((RootIndexed.BranchingWalk.ofStepField
          initial (sourceStep ω)).position d p.1 p.2) →
      ↑(R (sourceStep ω p.1 p.2)) ⊆ {i | survive (ω q.1 q.2) i})
    (hsharedIncrement : ∀ n ω p,
      p ∈ RootIndexed.StepSelection.labelledPopulation
        R n (sourceStep ω) r →
      ∀ q, q ∈ RootIndexed.selectedPopulation
        N roots initial d φ hadmits n ω →
      φ ((RootIndexed.BranchingWalk.ofStepField initial ω).position
          d q.1 q.2) ≤
        φ ((RootIndexed.BranchingWalk.ofStepField
          initial (sourceStep ω)).position d p.1 p.2) →
      ∀ i ∈ R (sourceStep ω p.1 p.2),
        value' ((ω q.1 q.2).map d) i =
          value' ((sourceStep ω p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (n : ℕ) (ω : RootIndexed.StepField Root α Mark) :
    Cloud.DominatingInjection φ
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial (sourceStep ω))
        (RootIndexed.StepSelection.labelledPopulation R n (sourceStep ω) r))
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial ω)
        (RootIndexed.selectedPopulation
          N roots initial d φ hadmits n ω)) () :=
  generationInjection_selectedPopulation φ d N roots initial
    (fun sample => RootIndexed.BranchingWalk.ofStepField
      initial (sourceStep sample))
    (fun k sample => RootIndexed.StepSelection.labelledPopulation
      R k (sourceStep sample) r)
    (fun _ sample p => ↑(R (sourceStep sample p.1 p.2))) hadmits
    (fun sample =>
      { toFun := id
        mapsTo := by
          intro p hp
          have hp' : p = (r, []) := by simpa using hp
          subst p
          change (r, []) ∈ RootIndexed.initialPopulation (α := α) roots
          rw [RootIndexed.initialPopulation, Finset.mem_map]
          exact ⟨r, hr, rfl⟩
        injOn := Set.injOn_id _
        dominates := by
          intro p hp
          have hp' : p = (r, []) := by simpa using hp
          subst p
          change φ (RootIndexed.position initial d sample r []) ≤
            φ (RootIndexed.position initial d (sourceStep sample) r [])
          simp })
    (fun k sample =>
      RootIndexed.StepSelection.labelledPopulation_succ_subset
        R k (sourceStep sample) r)
    (fun k sample => hcard (k + 1) sample)
    hslots hsharedIncrement htranslate n ω

/-- A capacity-bounded single-root step-selected population is dominated by
the multi-root first-`N` population whenever matched parents share every
selected slot and its displacement. No law, countability, or address ordering
of offspring is assumed. -/
theorem injectivelyDominatesBy_labelledPopulation
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (φ : Position → Value) (d : Mark → Position) (N : ℕ)
    (R : Step.FiniteSelection α Mark)
    (roots : Finset Root) (r : Root) (hr : r ∈ roots)
    (initial : Root → Position)
    (sourceStep : RootIndexed.StepField Root α Mark →
      RootIndexed.StepField Root α Mark)
    (hadmits : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      Combinatorics.Branching.Selection.NSelection.AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initial d φ (n + 1) ω)
        (RootIndexed.childrenAtGeneration n parents ω))
    (hcard : ∀ n ω,
      (RootIndexed.StepSelection.labelledPopulation
        R n (sourceStep ω) r).card ≤ N)
    (hslots : ∀ n ω p,
      p ∈ RootIndexed.StepSelection.labelledPopulation
        R n (sourceStep ω) r →
      ∀ q, q ∈ RootIndexed.selectedPopulation
        N roots initial d φ hadmits n ω →
      φ ((RootIndexed.BranchingWalk.ofStepField initial ω).position
          d q.1 q.2) ≤
        φ ((RootIndexed.BranchingWalk.ofStepField
          initial (sourceStep ω)).position d p.1 p.2) →
      ↑(R (sourceStep ω p.1 p.2)) ⊆ {i | survive (ω q.1 q.2) i})
    (hsharedIncrement : ∀ n ω p,
      p ∈ RootIndexed.StepSelection.labelledPopulation
        R n (sourceStep ω) r →
      ∀ q, q ∈ RootIndexed.selectedPopulation
        N roots initial d φ hadmits n ω →
      φ ((RootIndexed.BranchingWalk.ofStepField initial ω).position
          d q.1 q.2) ≤
        φ ((RootIndexed.BranchingWalk.ofStepField
          initial (sourceStep ω)).position d p.1 p.2) →
      ∀ i ∈ R (sourceStep ω p.1 p.2),
        value' ((ω q.1 q.2).map d) i =
          value' ((sourceStep ω p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    ∀ n ω,
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial (sourceStep ω))
        (RootIndexed.StepSelection.labelledPopulation
          R n (sourceStep ω) r)).InjectivelyDominatesBy φ
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial ω)
        (RootIndexed.selectedPopulation
          N roots initial d φ hadmits n ω)) () := by
  apply injectivelyDominatesBy_selectedPopulation
    φ d N roots initial
    (fun ω => RootIndexed.BranchingWalk.ofStepField initial (sourceStep ω))
    (fun n ω => RootIndexed.StepSelection.labelledPopulation
      R n (sourceStep ω) r)
    (fun _ ω p => ↑(R (sourceStep ω p.1 p.2))) hadmits
  · intro ω
    refine ⟨id, ?_, Set.injOn_id _, ?_⟩
    · intro p hp
      have hp' : p = (r, []) := by simpa using hp
      subst p
      change (r, []) ∈ RootIndexed.initialPopulation (α := α) roots
      rw [RootIndexed.initialPopulation, Finset.mem_map]
      exact ⟨r, hr, rfl⟩
    · intro p hp
      have hp' : p = (r, []) := by simpa using hp
      subst p
      change φ (RootIndexed.position initial d ω r []) ≤
        φ (RootIndexed.position initial d (sourceStep ω) r [])
      simp
  · exact fun n ω =>
      RootIndexed.StepSelection.labelledPopulation_succ_subset
        R n (sourceStep ω) r
  · exact fun n ω => hcard (n + 1) ω
  · exact hslots
  · exact hsharedIncrement
  · exact htranslate

end ProbabilityTheory.BranchingRandomWalk.Selection.Coupling
