/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Candidates.RootIndexed
import Probability.BranchingRandomWalk.Selection.NSelection.Position

/-!
# Root-indexed selected population process

At every generation this process forms the set of all surviving children of
the retained population, allowing infinitely many children, then retains its
intrinsic first `N` particles by observed position. The construction is
causal on the pre-sampled root-indexed step field.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.RootIndexed

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

noncomputable section

variable {Root α Mark Position Value : Type*}

/-- Label a finite set of initial roots by their empty addresses. -/
def initialPopulation [DecidableEq (RootIndexed.TreeNode Root α)]
    (roots : Finset Root) : Finset (RootIndexed.TreeNode Root α) :=
  roots.map ⟨fun r => (r, []), fun _ _ h => congrArg Prod.fst h⟩

@[simp] theorem mem_initialPopulation_iff
    [DecidableEq (RootIndexed.TreeNode Root α)]
    {roots : Finset Root} {p : RootIndexed.TreeNode Root α} :
    p ∈ initialPopulation (α := α) roots ↔ ∃ r ∈ roots, p = (r, []) := by
  rw [initialPopulation, Finset.mem_map]
  constructor
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, h.symm⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, h.symm⟩

@[simp] theorem initialPopulation_card
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (roots : Finset Root) : (initialPopulation (α := α) roots).card = roots.card := by
  simp [initialPopulation]

/-- The totalized N-selected population.  It is defined on every raw field;
at a generation whose candidate population is not lower-finite, the selected
population is empty.  Under suitable offspring laws this fallback occurs
only on a null set. -/
noncomputable def selectedPopulationTotalized
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value) :
    ℕ → RootIndexed.StepField Root α Mark →
      Finset (RootIndexed.TreeNode Root α)
  | 0, _ => initialPopulation roots
  | n + 1, ω =>
      Selection.NSelection.selectFirstNFromSetTotalized N
        (observedPositionAtGeneration initial d φ (n + 1))
        (fun field => childrenAtGeneration n
          (selectedPopulationTotalized N roots initial d φ n field) field) ω

theorem selectedPopulationTotalized_succ_spec
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
    (hgood : Combinatorics.Branching.Selection.NSelection.IsLowerFiniteBy
      (observedPositionAtGeneration initial d φ (n + 1) ω)
      (childrenAtGeneration n
        (selectedPopulationTotalized N roots initial d φ n ω) ω)) :
    IsFirstNBy N
      (observedPositionAtGeneration initial d φ (n + 1) ω)
      (childrenAtGeneration n
        (selectedPopulationTotalized N roots initial d φ n ω) ω)
      (selectedPopulationTotalized N roots initial d φ (n + 1) ω) := by
  exact Selection.NSelection.selectFirstNFromSetTotalized_spec
    N (observedPositionAtGeneration initial d φ (n + 1))
    (fun field => childrenAtGeneration n
      (selectedPopulationTotalized N roots initial d φ n field) field) ω hgood

theorem selectedPopulationTotalized_succ_subset
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (n : ℕ) (ω : RootIndexed.StepField Root α Mark) :
    ↑(selectedPopulationTotalized N roots initial d φ (n + 1) ω) ⊆
      childrenAtGeneration n
        (selectedPopulationTotalized N roots initial d φ n ω) ω := by
  classical
  by_cases hgood : Combinatorics.Branching.Selection.NSelection.IsLowerFiniteBy
      (observedPositionAtGeneration initial d φ (n + 1) ω)
      (childrenAtGeneration n
        (selectedPopulationTotalized N roots initial d φ n ω) ω)
  · exact (selectedPopulationTotalized_succ_spec N roots initial d φ n ω
      hgood).subset
  · have hEmpty :=
      Selection.NSelection.selectFirstNFromSetTotalized_empty_of_not_lowerFinite N
        (observedPositionAtGeneration initial d φ (n + 1))
        (fun field => childrenAtGeneration n
          (selectedPopulationTotalized N roots initial d φ n field) field)
        ω hgood
    simp [selectedPopulationTotalized, hEmpty]

theorem selectedPopulationTotalized_depth
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
    (p : RootIndexed.TreeNode Root α)
    (hp : p ∈ selectedPopulationTotalized N roots initial d φ n ω) :
    p.2.length = n := by
  cases n with
  | zero =>
      change p ∈ initialPopulation roots at hp
      rw [initialPopulation, Finset.mem_map] at hp
      obtain ⟨r, _, rfl⟩ := hp
      rfl
  | succ n =>
      apply childrenAtGeneration_depth n
        (selectedPopulationTotalized N roots initial d φ n ω) ω p
      exact selectedPopulationTotalized_succ_subset N roots initial d φ n ω hp

/-- Totalized selection never introduces a root outside its finite initial
root set, even on a raw field where admissibility fails. -/
theorem selectedPopulationTotalized_root_mem
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
    (p : RootIndexed.TreeNode Root α)
    (hp : p ∈ selectedPopulationTotalized N roots initial d φ n ω) :
    p.1 ∈ roots := by
  induction n generalizing p with
  | zero =>
      change p ∈ initialPopulation roots at hp
      rw [initialPopulation, Finset.mem_map] at hp
      obtain ⟨r, hr, rfl⟩ := hp
      exact hr
  | succ n ih =>
      have hchild := selectedPopulationTotalized_succ_subset
        N roots initial d φ n ω hp
      obtain ⟨q, hq, hqdepth, i, hi, rfl⟩ :=
        (mem_childrenAtGeneration_iff n
          (selectedPopulationTotalized N roots initial d φ n ω) ω p).mp hchild
      exact ih q hq

theorem selectedPopulationTotalized_adapted
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [SecondCountableTopology Value]
    [OrderClosedTopology Value] [MeasurableEq Value]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ) :
    ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := Mark) n]
      (selectedPopulationTotalized N roots initial d φ n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hcandidates := childrenAtGeneration_measurable n
        (selectedPopulationTotalized N roots initial d φ n) ih
      exact RootIndexed.measurable_selectFirstNFromSetTotalized
        N initial d hd φ hφ (n + 1)
        (fun ω => childrenAtGeneration n
          (selectedPopulationTotalized N roots initial d φ n ω) ω)
        hcandidates

/-- The selected population obtained from all surviving children. Existence
of the first-`N` segment is an explicit pointwise premise; lower local
finiteness is a standard way to supply it. -/
noncomputable def selectedPopulation
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hadmits : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (observedPositionAtGeneration initial d φ (n + 1) ω)
        (childrenAtGeneration n parents ω)) :
    ℕ → RootIndexed.StepField Root α Mark →
      Finset (RootIndexed.TreeNode Root α)
  | 0, _ => initialPopulation roots
  | n + 1, ω =>
      let parents := selectedPopulation N roots initial d φ hadmits n ω
      selectFirstNFromSet N
        (observedPositionAtGeneration initial d φ (n + 1) ω)
        (childrenAtGeneration n parents ω) (hadmits n ω parents)

theorem selectedPopulation_succ_spec
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hadmits : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (observedPositionAtGeneration initial d φ (n + 1) ω)
        (childrenAtGeneration n parents ω))
    (n : ℕ) (ω : RootIndexed.StepField Root α Mark) :
    IsFirstNBy N
      (observedPositionAtGeneration initial d φ (n + 1) ω)
      (childrenAtGeneration n
        (selectedPopulation N roots initial d φ hadmits n ω) ω)
      (selectedPopulation N roots initial d φ hadmits (n + 1) ω) := by
  exact selectFirstNFromSet_spec N
    (observedPositionAtGeneration initial d φ (n + 1) ω)
    (childrenAtGeneration n
      (selectedPopulation N roots initial d φ hadmits n ω) ω)
    (hadmits n ω
      (selectedPopulation N roots initial d φ hadmits n ω))

theorem selectedPopulation_succ_subset
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hadmits : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (observedPositionAtGeneration initial d φ (n + 1) ω)
        (childrenAtGeneration n parents ω))
    (n : ℕ) (ω : RootIndexed.StepField Root α Mark) :
    ↑(selectedPopulation N roots initial d φ hadmits (n + 1) ω) ⊆
      childrenAtGeneration n
        (selectedPopulation N roots initial d φ hadmits n ω) ω :=
  (selectedPopulation_succ_spec N roots initial d φ hadmits n ω).subset

theorem selectedPopulation_adapted
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    [MeasurableSpace Mark] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hadmits : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (observedPositionAtGeneration initial d φ (n + 1) ω)
        (childrenAtGeneration n parents ω))
    (hselect : ∀ (n : ℕ)
        (parents : RootIndexed.StepField Root α Mark →
          Finset (RootIndexed.TreeNode Root α)),
      Measurable[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := Mark) n] parents →
      Measurable[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := Mark) (n + 1)] fun ω =>
        selectFirstNFromSet N
          (observedPositionAtGeneration initial d φ (n + 1) ω)
          (childrenAtGeneration n (parents ω) ω)
          (hadmits n ω (parents ω))) :
    ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := Mark) n]
      (selectedPopulation N roots initial d φ hadmits n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      change Measurable[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := Mark) (n + 1)] (fun ω =>
          selectFirstNFromSet N
            (observedPositionAtGeneration initial d φ (n + 1) ω)
            (childrenAtGeneration n
              (selectedPopulation N roots initial d φ hadmits n ω) ω)
            (hadmits n ω
              (selectedPopulation N roots initial d φ hadmits n ω)))
      exact hselect n (selectedPopulation N roots initial d φ hadmits n) ih

/-- Countable particle labels supply the abstract measurable-selection premise
through measurable lower-set cardinalities. -/
theorem selectedPopulation_adapted_of_countable
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [LinearOrder Value]
    [SecondCountableTopology Value] [OrderClosedTopology Value]
    [MeasurableEq Value]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ)
    (hadmits : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (observedPositionAtGeneration initial d φ (n + 1) ω)
        (childrenAtGeneration n parents ω)) :
    ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := Mark) n]
      (selectedPopulation N roots initial d φ hadmits n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hcandidates := childrenAtGeneration_measurable n
        (selectedPopulation N roots initial d φ hadmits n) ih
      exact RootIndexed.measurable_selectFirstNFromSet
        N initial d hd φ hφ (n + 1)
        (fun ω => childrenAtGeneration n
          (selectedPopulation N roots initial d φ hadmits n ω) ω)
        (fun ω => hadmits n ω
          (selectedPopulation N roots initial d φ hadmits n ω))
        hcandidates

theorem selectedPopulation_depth
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hadmits : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (observedPositionAtGeneration initial d φ (n + 1) ω)
        (childrenAtGeneration n parents ω))
    (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
    (p : RootIndexed.TreeNode Root α)
    (hp : p ∈ selectedPopulation N roots initial d φ hadmits n ω) :
    p.2.length = n := by
  cases n with
  | zero =>
      change p ∈ initialPopulation roots at hp
      rw [initialPopulation, Finset.mem_map] at hp
      obtain ⟨r, _, rfl⟩ := hp
      rfl
  | succ n =>
      apply childrenAtGeneration_depth n
        (selectedPopulation N roots initial d φ hadmits n ω) ω p
      exact (selectFirstNFromSet_spec N
        (observedPositionAtGeneration initial d φ (n + 1) ω)
        (childrenAtGeneration n
          (selectedPopulation N roots initial d φ hadmits n ω) ω)
        (hadmits n ω
          (selectedPopulation N roots initial d φ hadmits n ω))).subset hp

/-- Successor selection stated with the abstract offspring address set used
by the multi-root coupling API. -/
theorem selectedPopulation_succ_spec_offspringAddressSet
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hadmits : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (observedPositionAtGeneration initial d φ (n + 1) ω)
        (childrenAtGeneration n parents ω))
    (n : ℕ) (ω : RootIndexed.StepField Root α Mark) :
    IsFirstNBy N
      (observedPositionAtGeneration initial d φ (n + 1) ω)
      (Combinatorics.Branching.Selection.Coupling.offspringAddressSet
        (↑(selectedPopulation N roots initial d φ hadmits n ω))
        (fun p => {i | survive (ω p.1 p.2) i}))
      (selectedPopulation N roots initial d φ hadmits (n + 1) ω) := by
  rw [← childrenAtGeneration_eq_offspringAddressSet n
    (selectedPopulation N roots initial d φ hadmits n ω) ω]
  · exact selectedPopulation_succ_spec N roots initial d φ hadmits n ω
  · intro p hp
    exact selectedPopulation_depth N roots initial d φ hadmits n ω p hp

/-- Successor selection expressed with the actual position function of the
branching walk bundled from the pre-sampled field. This is the exact target
premise of the pathwise multi-root coupling theorem. -/
theorem selectedPopulation_succ_spec_position
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hadmits : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (observedPositionAtGeneration initial d φ (n + 1) ω)
        (childrenAtGeneration n parents ω))
    (n : ℕ) (ω : RootIndexed.StepField Root α Mark) :
    IsFirstNBy N
      (fun q => φ
        ((Combinatorics.Branching.RootIndexed.BranchingWalk.ofStepField
          initial ω).position d q.1 q.2))
      (Combinatorics.Branching.Selection.Coupling.offspringAddressSet
        (↑(selectedPopulation N roots initial d φ hadmits n ω))
        (fun p => {i | survive (ω p.1 p.2) i}))
      (selectedPopulation N roots initial d φ hadmits (n + 1) ω) := by
  apply (selectedPopulation_succ_spec_offspringAddressSet
    N roots initial d φ hadmits n ω).congr_value
  intro q hq
  apply observedPositionAtGeneration_eq
  rw [← childrenAtGeneration_eq_offspringAddressSet n
    (selectedPopulation N roots initial d φ hadmits n ω) ω] at hq
  · exact childrenAtGeneration_depth n
      (selectedPopulation N roots initial d φ hadmits n ω) ω q hq
  · intro p hp
    exact selectedPopulation_depth N roots initial d φ hadmits n ω p hp

theorem selectedPopulation_card_le
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hadmits : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (observedPositionAtGeneration initial d φ (n + 1) ω)
        (childrenAtGeneration n parents ω))
    (n : ℕ) (ω : RootIndexed.StepField Root α Mark) :
    (selectedPopulation N roots initial d φ hadmits (n + 1) ω).card ≤ N :=
  (selectFirstNFromSet_spec N
    (observedPositionAtGeneration initial d φ (n + 1) ω)
    (childrenAtGeneration n
      (selectedPopulation N roots initial d φ hadmits n ω) ω)
    (hadmits n ω
      (selectedPopulation N roots initial d φ hadmits n ω))).card_le

end

end ProbabilityTheory.BranchingRandomWalk.RootIndexed
