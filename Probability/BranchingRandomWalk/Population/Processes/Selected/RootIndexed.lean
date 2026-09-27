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

@[simp] theorem initialPopulation_card
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (roots : Finset Root) : (initialPopulation (α := α) roots).card = roots.card := by
  simp [initialPopulation]

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
