import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.FreshPool
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Coordinates

/-!
# Iterating the successful split root pool

When the ambient root type is the active/reserve sum, the fresh-pool
construction can be applied repeatedly.  Every finite number of restart
stages preserves the complete root-indexed product law.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed
namespace StepSelection
namespace SplitSchedule

open Combinatorics.UlamHarris Combinatorics.Branching

/-- Repeatedly replace an active/reserve field by the fresh root pool supplied
by its first successful fixed-age split trial. -/
noncomputable def iteratedPoolField
    {Reserve α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ Reserve) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ Reserve) × TreeNode α)
    (reserve : Reserve → Fin N ⊕ Reserve) (stem : TreeNode α) :
    ℕ → RootIndexed.StepField (Fin N ⊕ Reserve) α X →
      RootIndexed.StepField (Fin N ⊕ Reserve) α X :=
  RootIndexed.iteratedSelectedSubtreeStepField fun _ =>
    poolRoots N R trial duration target fallback reserve stem

@[simp] theorem iteratedPoolField_zero
    {Reserve α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ Reserve) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ Reserve) × TreeNode α)
    (reserve : Reserve → Fin N ⊕ Reserve) (stem : TreeNode α) :
    iteratedPoolField N R trial duration target fallback reserve stem 0 = id :=
  rfl

/-- Cumulative original coordinates of the roots in an iterated split pool. -/
noncomputable def iteratedPoolRoots
    {Reserve α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ Reserve) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ Reserve) × TreeNode α)
    (reserve : Reserve → Fin N ⊕ Reserve) (stem : TreeNode α) :
    ℕ → RootIndexed.StepField (Fin N ⊕ Reserve) α X →
      Fin N ⊕ Reserve → (Fin N ⊕ Reserve) × TreeNode α :=
  RootIndexed.iteratedSelectedRoots fun _ =>
    poolRoots N R trial duration target fallback reserve stem

/-- Embed a particle of an iterated pool into the original pre-sampled field. -/
noncomputable def iteratedPoolAddress
    {Reserve α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ Reserve) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ Reserve) × TreeNode α)
    (reserve : Reserve → Fin N ⊕ Reserve) (stem : TreeNode α)
    (j : ℕ) (step : RootIndexed.StepField (Fin N ⊕ Reserve) α X)
    (p : RootIndexed.TreeNode (Fin N ⊕ Reserve) α) :
    RootIndexed.TreeNode (Fin N ⊕ Reserve) α :=
  RootIndexed.iteratedSelectedAddress
    (fun _ => poolRoots N R trial duration target fallback reserve stem)
    j step p

/-- The iterated concrete field reads the original pre-sampled field at its
cumulative root/address coordinates. -/
theorem iteratedPoolField_apply
    {Reserve α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ Reserve) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ Reserve) × TreeNode α)
    (reserve : Reserve → Fin N ⊕ Reserve) (stem : TreeNode α)
    (j : ℕ) (step : RootIndexed.StepField (Fin N ⊕ Reserve) α X)
    (i : Fin N ⊕ Reserve) (v : TreeNode α) :
    iteratedPoolField N R trial duration target fallback reserve stem j
        step i v =
      step (iteratedPoolRoots N R trial duration target fallback reserve stem
        j step i).1
        ((iteratedPoolRoots N R trial duration target fallback reserve stem
          j step i).2 ++ v) :=
  RootIndexed.iteratedSelectedSubtreeStepField_apply
    (fun _ => poolRoots N R trial duration target fallback reserve stem)
    j step i v

theorem iteratedPoolField_eq_at_address
    {Reserve α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ Reserve) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ Reserve) × TreeNode α)
    (reserve : Reserve → Fin N ⊕ Reserve) (stem : TreeNode α)
    (j : ℕ) (step : RootIndexed.StepField (Fin N ⊕ Reserve) α X)
    (p : RootIndexed.TreeNode (Fin N ⊕ Reserve) α) :
    iteratedPoolField N R trial duration target fallback reserve stem j
        step p.1 p.2 =
      step (iteratedPoolAddress N R trial duration target fallback reserve stem
        j step p).1
        (iteratedPoolAddress N R trial duration target fallback reserve stem
          j step p).2 :=
  RootIndexed.iteratedSelectedSubtreeStepField_eq_at_address
    (fun _ => poolRoots N R trial duration target fallback reserve stem)
    j step p

/-- Any step functional, including a finite selection rule, agrees at an
iterated pool particle and its embedded original address. -/
theorem map_iteratedPoolField
    {Reserve α X Y : Type*} [LinearOrder (TreeNode α)]
    (F : Step α X → Y)
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ Reserve) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ Reserve) × TreeNode α)
    (reserve : Reserve → Fin N ⊕ Reserve) (stem : TreeNode α)
    (j : ℕ) (step : RootIndexed.StepField (Fin N ⊕ Reserve) α X)
    (p : RootIndexed.TreeNode (Fin N ⊕ Reserve) α) :
    F (iteratedPoolField N R trial duration target fallback reserve stem j
        step p.1 p.2) =
      F (step (iteratedPoolAddress N R trial duration target fallback reserve
        stem j step p).1
        (iteratedPoolAddress N R trial duration target fallback reserve stem
          j step p).2) :=
  RootIndexed.map_iteratedSelectedSubtreeStepField F
    (fun _ => poolRoots N R trial duration target fallback reserve stem)
    j step p

theorem iteratedPoolAddress_injective
    {Reserve α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ Reserve) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ Reserve) × TreeNode α)
    (hfallbackDepth : ∀ i, (fallback i).2.length = duration)
    (hfallbackInjective : Function.Injective fallback)
    (reserve : Reserve → Fin N ⊕ Reserve)
    (hreserve : Function.Injective reserve)
    (htrial : ∀ k r, trial k ≠ reserve r)
    (hfallbackReserve : ∀ i r, (fallback i).1 ≠ reserve r)
    (stem : TreeNode α) (hstem : stem.length = duration) :
    ∀ j (step : RootIndexed.StepField (Fin N ⊕ Reserve) α X),
      Function.Injective
        (iteratedPoolAddress N R trial duration target fallback reserve stem
          j step) := by
  exact RootIndexed.iteratedSelectedAddress_injective
    (fun _ => poolRoots N R trial duration target fallback reserve stem)
    (fun _ => duration)
    (fun _ => poolRoots_depth N R trial duration target fallback
      hfallbackDepth reserve stem hstem)
    (fun _ => poolRoots_injective N R trial duration target fallback
      hfallbackInjective reserve hreserve htrial hfallbackReserve stem)

/-- Absolute initial positions associated with the cumulative split-pool
coordinates. -/
noncomputable def iteratedPoolInitialPosition
    {Reserve α Mark Position : Type*} [AddCommMonoid Position]
    [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α Mark)
    (initial : Fin N ⊕ Reserve → Position) (d : Mark → Position)
    (trial : ℕ → Fin N ⊕ Reserve) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ Reserve) × TreeNode α)
    (reserve : Reserve → Fin N ⊕ Reserve) (stem : TreeNode α)
    (j : ℕ) (step : RootIndexed.StepField (Fin N ⊕ Reserve) α Mark) :
    Fin N ⊕ Reserve → Position :=
  RootIndexed.iteratedSelectedInitialPosition initial d
    (fun _ => poolRoots N R trial duration target fallback reserve stem)
    j step

/-- The concrete iteration preserves all absolute positions in an arbitrary
additive position space under an arbitrary mark displacement map. -/
theorem position_iteratedPoolField
    {Reserve α Mark Position : Type*} [AddCommMonoid Position]
    [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α Mark)
    (initial : Fin N ⊕ Reserve → Position) (d : Mark → Position)
    (trial : ℕ → Fin N ⊕ Reserve) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ Reserve) × TreeNode α)
    (reserve : Reserve → Fin N ⊕ Reserve) (stem : TreeNode α)
    (j : ℕ) (step : RootIndexed.StepField (Fin N ⊕ Reserve) α Mark)
    (i : Fin N ⊕ Reserve) (v : TreeNode α) :
    RootIndexed.position
        (iteratedPoolInitialPosition N R initial d trial duration target
          fallback reserve stem j step) d
        (iteratedPoolField N R trial duration target fallback reserve stem j
          step) i v =
      RootIndexed.position initial d step
        (iteratedPoolRoots N R trial duration target fallback reserve stem
          j step i).1
        ((iteratedPoolRoots N R trial duration target fallback reserve stem
          j step i).2 ++ v) :=
  RootIndexed.position_iteratedSelectedSubtreeStepField initial d
    (fun _ => poolRoots N R trial duration target fallback reserve stem)
    j step i v

/-- Every finite concrete restart iteration retains the original product
field law. -/
theorem iteratedPoolField_law
    {Reserve α X : Type*} [Countable α] [MeasurableSpace X]
    [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (trial : ℕ → Fin N ⊕ Reserve) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ Reserve) × TreeNode α)
    (hfallbackDepth : ∀ i, (fallback i).2.length = duration)
    (hfallbackInjective : Function.Injective fallback)
    (reserve : Reserve → Fin N ⊕ Reserve)
    (hreserve : Function.Injective reserve)
    (htrial : ∀ k r, trial k ≠ reserve r)
    (hfallbackReserve : ∀ i r, (fallback i).1 ≠ reserve r)
    (stem : TreeNode α) (hstem : stem.length = duration)
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] :
    ∀ j,
      (RootIndexed.stepFieldLaw (Root := Fin N ⊕ Reserve) μ).map
          (iteratedPoolField N R trial duration target fallback reserve stem j) =
        RootIndexed.stepFieldLaw (Root := Fin N ⊕ Reserve) μ := by
  exact RootIndexed.iteratedSelectedSubtreeStepField_law μ
    (fun _ => poolRoots N R trial duration target fallback reserve stem)
    (fun _ => duration)
    (fun _ => poolRoots_range_countable
      N R trial duration target fallback reserve stem)
    (fun _ => poolRoots_fiber_adapted
      N R hR trial duration target fallback reserve stem)
    (fun _ => poolRoots_depth N R trial duration target fallback
      hfallbackDepth reserve stem hstem)
    (fun _ => poolRoots_injective N R trial duration target fallback
      hfallbackInjective reserve hreserve htrial hfallbackReserve stem)

end SplitSchedule
end StepSelection
end RootIndexed
end ProbabilityTheory.BranchingRandomWalk
