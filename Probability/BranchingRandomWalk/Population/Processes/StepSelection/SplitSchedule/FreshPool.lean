import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Roots
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily

/-!
# Extending a successful population to a fresh root pool

A successful population supplies the finite active part of the next field.
An injectively labelled reserve family supplies all remaining root labels.
This produces a complete product field whose root type can be reused at the
next restart stage.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed
namespace StepSelection
namespace SplitSchedule

open Combinatorics.UlamHarris Combinatorics.Branching

/-- Labels of the finite active part of an active/reserve root pool. -/
def activeRoots {Reserve : Type*} (N : ℕ) : Finset (Fin N ⊕ Reserve) :=
  Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩

@[simp] theorem mem_activeRoots {Reserve : Type*} (N : ℕ)
    (r : Fin N ⊕ Reserve) :
    r ∈ activeRoots N ↔ ∃ i : Fin N, r = Sum.inl i := by
  simp [activeRoots, eq_comm]

@[simp] theorem card_activeRoots {Reserve : Type*} (N : ℕ) :
    (activeRoots (Reserve := Reserve) N).card = N := by
  simp [activeRoots]

/-- Extend a finite active family by a reserve family rooted at one fixed
address. -/
def extendRoots
    {Root Reserve α : Type*} {N : ℕ}
    (active : Fin N → Root × TreeNode α)
    (reserve : Reserve → Root) (stem : TreeNode α) :
    Fin N ⊕ Reserve → Root × TreeNode α
  | Sum.inl i => active i
  | Sum.inr r => (reserve r, stem)

theorem extendRoots_left_injective
    {Root Reserve α : Type*} {N : ℕ}
    (reserve : Reserve → Root) (stem : TreeNode α) :
    Function.Injective
      (fun active : Fin N → Root × TreeNode α =>
        extendRoots active reserve stem) := by
  intro active₁ active₂ h
  funext i
  exact congrFun h (Sum.inl i)

theorem extendRoots_injective
    {Root Reserve α : Type*} {N : ℕ}
    (active : Fin N → Root × TreeNode α)
    (reserve : Reserve → Root) (stem : TreeNode α)
    (hactive : Function.Injective active)
    (hreserve : Function.Injective reserve)
    (hcross : ∀ i r, (active i).1 ≠ reserve r) :
    Function.Injective (extendRoots active reserve stem) := by
  intro a b hab
  cases a with
  | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (hactive hab)
      | inr r => exact (hcross i r (congrArg Prod.fst hab)).elim
  | inr r =>
      cases b with
      | inl i => exact (hcross i r (congrArg Prod.fst hab).symm).elim
      | inr s => exact congrArg Sum.inr (hreserve (congrArg Prod.fst hab))

/-- The successful active roots together with a deterministic reserve family. -/
noncomputable def poolRoots
    {Root Reserve α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (reserve : Reserve → Root) (stem : TreeNode α)
    (ω : RootIndexed.StepField Root α X) :
    Fin N ⊕ Reserve → Root × TreeNode α :=
  extendRoots (roots N R trial duration target fallback ω) reserve stem

theorem poolRoots_range_countable
    {Root Reserve α X : Type*} [Countable α]
    [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (reserve : Reserve → Root) (stem : TreeNode α) :
    (Set.range (poolRoots N R trial duration target fallback reserve stem)
      ).Countable := by
  apply ((roots_range_countable N R trial duration target fallback).image
    (fun active => extendRoots active reserve stem)).mono
  rintro selected ⟨ω, rfl⟩
  exact ⟨roots N R trial duration target fallback ω,
    ⟨ω, rfl⟩, rfl⟩

theorem poolRoots_fiber_adapted
    {Root Reserve α X : Type*} [Countable α] [MeasurableSpace X]
    [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (trial : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (reserve : Reserve → Root) (stem : TreeNode α)
    (selected : Fin N ⊕ Reserve → Root × TreeNode α) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) duration]
      {ω | poolRoots N R trial duration target fallback reserve stem ω =
        selected} := by
  let _ : MeasurableSpace (RootIndexed.StepField Root α X) :=
    RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) duration
  let extend := fun active : Fin N → Root × TreeNode α =>
    extendRoots active reserve stem
  have hextend : Function.Injective extend :=
    extendRoots_left_injective reserve stem
  by_cases hselected : selected ∈ Set.range extend
  · obtain ⟨active, rfl⟩ := hselected
    have hset :
        {ω : RootIndexed.StepField Root α X |
          poolRoots N R trial duration target fallback reserve stem ω =
            extend active} =
        {ω | roots N R trial duration target fallback ω = active} := by
      ext ω
      exact hextend.eq_iff
    rw [hset]
    exact roots_fiber_adapted N R hR trial duration target fallback active
  · have hset :
        {ω : RootIndexed.StepField Root α X |
          poolRoots N R trial duration target fallback reserve stem ω =
            selected} = ∅ := by
      ext ω
      constructor
      · intro h
        exact (hselected
          ⟨roots N R trial duration target fallback ω, h⟩).elim
      · intro h
        exact h.elim
    rw [hset]
    exact MeasurableSet.empty

theorem poolRoots_depth
    {Root Reserve α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (hfallback : ∀ i, (fallback i).2.length = duration)
    (reserve : Reserve → Root) (stem : TreeNode α)
    (hstem : stem.length = duration)
    (ω : RootIndexed.StepField Root α X)
    (i : Fin N ⊕ Reserve) :
    ((poolRoots N R trial duration target fallback reserve stem ω i).2
      ).length = duration := by
  cases i with
  | inl i => exact roots_depth N R trial duration target fallback hfallback ω i
  | inr _ => exact hstem

theorem roots_root_ne_reserve
    {Root Reserve α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (reserve : Reserve → Root)
    (htrial : ∀ k r, trial k ≠ reserve r)
    (hfallback : ∀ i r, (fallback i).1 ≠ reserve r)
    (ω : RootIndexed.StepField Root α X) (i : Fin N) (r : Reserve) :
    (roots N R trial duration target fallback ω i).1 ≠ reserve r := by
  induction hfirst : firstSuccess R trial duration target ω using WithTop.recTopCoe with
  | top => simpa [roots, hfirst] using hfallback i r
  | coe k =>
      rw [roots, hfirst, WithTop.recTopCoe_coe, rootFamily]
      split_ifs
      · exact htrial k r
      · exact hfallback i r

theorem poolRoots_injective
    {Root Reserve α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (hfallbackInjective : Function.Injective fallback)
    (reserve : Reserve → Root) (hreserve : Function.Injective reserve)
    (htrial : ∀ k r, trial k ≠ reserve r)
    (hfallbackReserve : ∀ i r, (fallback i).1 ≠ reserve r)
    (stem : TreeNode α) (ω : RootIndexed.StepField Root α X) :
    Function.Injective
      (poolRoots N R trial duration target fallback reserve stem ω) := by
  exact extendRoots_injective _ reserve stem
    (roots_injective N R trial duration target fallback
      hfallbackInjective ω)
    hreserve
    (roots_root_ne_reserve N R trial duration target fallback reserve
      htrial hfallbackReserve ω)

/-- The full descendant field below the active and reserve root pool. -/
noncomputable def poolField
    {Root Reserve α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (reserve : Reserve → Root) (stem : TreeNode α)
    (ω : RootIndexed.StepField Root α X) :
    RootIndexed.StepField (Fin N ⊕ Reserve) α X :=
  RootIndexed.selectedSubtreeStepFieldVector
    (poolRoots N R trial duration target fallback reserve stem) ω

theorem poolField_law
    {Root Reserve α X : Type*} [Countable α] [MeasurableSpace X]
    [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (trial : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (hfallbackDepth : ∀ i, (fallback i).2.length = duration)
    (hfallbackInjective : Function.Injective fallback)
    (reserve : Reserve → Root) (hreserve : Function.Injective reserve)
    (htrial : ∀ k r, trial k ≠ reserve r)
    (hfallbackReserve : ∀ i r, (fallback i).1 ≠ reserve r)
    (stem : TreeNode α) (hstem : stem.length = duration)
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] :
    (RootIndexed.stepFieldLaw (Root := Root) μ).map
        (poolField N R trial duration target fallback reserve stem) =
      RootIndexed.stepFieldLaw (Root := Fin N ⊕ Reserve) μ := by
  exact RootIndexed.selectedSubtreeStepFieldVector_law μ
    (poolRoots N R trial duration target fallback reserve stem)
    (poolRoots_range_countable N R trial duration target fallback reserve stem)
    (poolRoots_fiber_adapted N R hR trial duration target fallback reserve stem)
    (poolRoots_depth N R trial duration target fallback hfallbackDepth
      reserve stem hstem)
    (poolRoots_injective N R trial duration target fallback
      hfallbackInjective reserve hreserve htrial hfallbackReserve stem)

end SplitSchedule
end StepSelection
end RootIndexed
end ProbabilityTheory.BranchingRandomWalk
