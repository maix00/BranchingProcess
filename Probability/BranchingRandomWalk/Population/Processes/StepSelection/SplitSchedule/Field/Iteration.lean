/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Field.FreshPool
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Coordinates

/-!
# Iterating the successful split root pool

When the ambient root type is the active and additional sum, the fresh-pool
construction can be applied repeatedly.  Every finite number of restart
stages preserves the complete root-indexed product law.
## Public declarations

At every finite restart stage \(j\), the iterated root-indexed field keeps
the complete product law, and its positions agree with the corresponding
original-field positions under the cumulative root-address map \(\Phi_j\):

\[\operatorname{Law}(\operatorname{iteratedPoolField}_j)
  =\operatorname{stepFieldLaw}(\mu),\qquad
  \operatorname{position}_j(p)=\operatorname{position}_0(\Phi_j(p)).\]

* `iteratedPoolField` recursively builds the field after each restart;
  `iteratedPoolRoots` and `iteratedPoolAddress` track the new root labels and
  cumulative addresses. `iteratedPoolField_zero`,
  `iteratedPoolField_apply`, `iteratedPoolField_eq_at_address`,
  `map_iteratedPoolField`, and `iteratedPoolAddress_injective` describe these
  recursive and address relations.
* `iteratedPoolInitialPosition` records particle locations through the
  iteration, and `position_iteratedPoolField` identifies them with positions
  in the original field.
* `iteratedPoolField_law` proves that each finite restart stage retains the
  original root-indexed product law.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed
namespace StepSelection
namespace SplitSchedule

open Combinatorics.UlamHarris Combinatorics.Branching

/-- Repeatedly replace an active and additional field by the fresh root pool supplied
by its first successful fixed-age split trial. -/
noncomputable def iteratedPoolField
    {AdditionalRoot α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ AdditionalRoot) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ AdditionalRoot) × TreeNode α)
    (additionalRoots : AdditionalRoot → Fin N ⊕ AdditionalRoot) (stem : TreeNode α) :
    ℕ → RootIndexed.StepField (Fin N ⊕ AdditionalRoot) α X →
      RootIndexed.StepField (Fin N ⊕ AdditionalRoot) α X :=
  RootIndexed.iteratedSelectedSubtreeStepField fun _ =>
    poolRoots N R trial duration target fallback additionalRoots stem

@[simp] theorem iteratedPoolField_zero
    {AdditionalRoot α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ AdditionalRoot) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ AdditionalRoot) × TreeNode α)
    (additionalRoots : AdditionalRoot → Fin N ⊕ AdditionalRoot) (stem : TreeNode α) :
    iteratedPoolField N R trial duration target fallback additionalRoots stem 0 = id :=
  rfl

/-- Cumulative original coordinates of the roots in an iterated split pool. -/
noncomputable def iteratedPoolRoots
    {AdditionalRoot α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ AdditionalRoot) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ AdditionalRoot) × TreeNode α)
    (additionalRoots : AdditionalRoot → Fin N ⊕ AdditionalRoot) (stem : TreeNode α) :
    ℕ → RootIndexed.StepField (Fin N ⊕ AdditionalRoot) α X →
      Fin N ⊕ AdditionalRoot → (Fin N ⊕ AdditionalRoot) × TreeNode α :=
  RootIndexed.iteratedSelectedRoots fun _ =>
    poolRoots N R trial duration target fallback additionalRoots stem

/-- Embed a particle of an iterated pool into the original pre-sampled field. -/
noncomputable def iteratedPoolAddress
    {AdditionalRoot α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ AdditionalRoot) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ AdditionalRoot) × TreeNode α)
    (additionalRoots : AdditionalRoot → Fin N ⊕ AdditionalRoot) (stem : TreeNode α)
    (j : ℕ) (step : RootIndexed.StepField (Fin N ⊕ AdditionalRoot) α X)
    (p : RootIndexed.TreeNode (Fin N ⊕ AdditionalRoot) α) :
    RootIndexed.TreeNode (Fin N ⊕ AdditionalRoot) α :=
  RootIndexed.iteratedSelectedAddress
    (fun _ => poolRoots N R trial duration target fallback additionalRoots stem)
    j step p

/-- The iterated concrete field reads the original pre-sampled field at its
cumulative root/address coordinates. -/
theorem iteratedPoolField_apply
    {AdditionalRoot α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ AdditionalRoot) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ AdditionalRoot) × TreeNode α)
    (additionalRoots : AdditionalRoot → Fin N ⊕ AdditionalRoot) (stem : TreeNode α)
    (j : ℕ) (step : RootIndexed.StepField (Fin N ⊕ AdditionalRoot) α X)
    (i : Fin N ⊕ AdditionalRoot) (v : TreeNode α) :
    iteratedPoolField N R trial duration target fallback additionalRoots stem j
        step i v =
      step (iteratedPoolRoots N R trial duration target fallback additionalRoots stem
        j step i).1
        ((iteratedPoolRoots N R trial duration target fallback additionalRoots stem
          j step i).2 ++ v) :=
  RootIndexed.iteratedSelectedSubtreeStepField_apply
    (fun _ => poolRoots N R trial duration target fallback additionalRoots stem)
    j step i v

theorem iteratedPoolField_eq_at_address
    {AdditionalRoot α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ AdditionalRoot) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ AdditionalRoot) × TreeNode α)
    (additionalRoots : AdditionalRoot → Fin N ⊕ AdditionalRoot) (stem : TreeNode α)
    (j : ℕ) (step : RootIndexed.StepField (Fin N ⊕ AdditionalRoot) α X)
    (p : RootIndexed.TreeNode (Fin N ⊕ AdditionalRoot) α) :
    iteratedPoolField N R trial duration target fallback additionalRoots stem j
        step p.1 p.2 =
      step (iteratedPoolAddress N R trial duration target fallback additionalRoots stem
        j step p).1
        (iteratedPoolAddress N R trial duration target fallback additionalRoots stem
          j step p).2 :=
  RootIndexed.iteratedSelectedSubtreeStepField_eq_at_address
    (fun _ => poolRoots N R trial duration target fallback additionalRoots stem)
    j step p

/-- Any step functional, including a finite selection rule, agrees at an
iterated pool particle and its embedded original address. -/
theorem map_iteratedPoolField
    {AdditionalRoot α X Y : Type*} [LinearOrder (TreeNode α)]
    (F : Step α X → Y)
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ AdditionalRoot) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ AdditionalRoot) × TreeNode α)
    (additionalRoots : AdditionalRoot → Fin N ⊕ AdditionalRoot) (stem : TreeNode α)
    (j : ℕ) (step : RootIndexed.StepField (Fin N ⊕ AdditionalRoot) α X)
    (p : RootIndexed.TreeNode (Fin N ⊕ AdditionalRoot) α) :
    F (iteratedPoolField N R trial duration target fallback additionalRoots stem j
        step p.1 p.2) =
      F (step (iteratedPoolAddress N R trial duration target fallback additionalRoots
        stem j step p).1
        (iteratedPoolAddress N R trial duration target fallback additionalRoots stem
          j step p).2) :=
  RootIndexed.map_iteratedSelectedSubtreeStepField F
    (fun _ => poolRoots N R trial duration target fallback additionalRoots stem)
    j step p

theorem iteratedPoolAddress_injective
    {AdditionalRoot α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ AdditionalRoot) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ AdditionalRoot) × TreeNode α)
    (hfallbackDepth : ∀ i, (fallback i).2.length = duration)
    (hfallbackInjective : Function.Injective fallback)
    (additionalRoots : AdditionalRoot → Fin N ⊕ AdditionalRoot)
    (hadditionalRoots : Function.Injective additionalRoots)
    (htrial : ∀ k r, trial k ≠ additionalRoots r)
    (hfallbackAdditionalRoots : ∀ i r, (fallback i).1 ≠ additionalRoots r)
    (stem : TreeNode α) (hstem : stem.length = duration) :
    ∀ j (step : RootIndexed.StepField (Fin N ⊕ AdditionalRoot) α X),
      Function.Injective
        (iteratedPoolAddress N R trial duration target fallback additionalRoots stem
          j step) := by
  exact RootIndexed.iteratedSelectedAddress_injective
    (fun _ => poolRoots N R trial duration target fallback additionalRoots stem)
    (fun _ => duration)
    (fun _ => poolRoots_depth N R trial duration target fallback
      hfallbackDepth additionalRoots stem hstem)
    (fun _ => poolRoots_injective N R trial duration target fallback
      hfallbackInjective additionalRoots hadditionalRoots htrial hfallbackAdditionalRoots stem)

/-- Absolute initial positions associated with the cumulative split-pool
coordinates. -/
noncomputable def iteratedPoolInitialPosition
    {AdditionalRoot α Mark Position : Type*} [AddCommMonoid Position]
    [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α Mark)
    (initial : Fin N ⊕ AdditionalRoot → Position) (d : Mark → Position)
    (trial : ℕ → Fin N ⊕ AdditionalRoot) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ AdditionalRoot) × TreeNode α)
    (additionalRoots : AdditionalRoot → Fin N ⊕ AdditionalRoot) (stem : TreeNode α)
    (j : ℕ) (step : RootIndexed.StepField (Fin N ⊕ AdditionalRoot) α Mark) :
    Fin N ⊕ AdditionalRoot → Position :=
  RootIndexed.iteratedSelectedInitialPosition initial d
    (fun _ => poolRoots N R trial duration target fallback additionalRoots stem)
    j step

/-- The concrete iteration preserves all absolute positions in an arbitrary
additive position space under an arbitrary mark displacement map. -/
theorem position_iteratedPoolField
    {AdditionalRoot α Mark Position : Type*} [AddCommMonoid Position]
    [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α Mark)
    (initial : Fin N ⊕ AdditionalRoot → Position) (d : Mark → Position)
    (trial : ℕ → Fin N ⊕ AdditionalRoot) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ AdditionalRoot) × TreeNode α)
    (additionalRoots : AdditionalRoot → Fin N ⊕ AdditionalRoot) (stem : TreeNode α)
    (j : ℕ) (step : RootIndexed.StepField (Fin N ⊕ AdditionalRoot) α Mark)
    (i : Fin N ⊕ AdditionalRoot) (v : TreeNode α) :
    RootIndexed.position
        (iteratedPoolInitialPosition N R initial d trial duration target
          fallback additionalRoots stem j step) d
        (iteratedPoolField N R trial duration target fallback additionalRoots stem j
          step) i v =
      RootIndexed.position initial d step
        (iteratedPoolRoots N R trial duration target fallback additionalRoots stem
          j step i).1
        ((iteratedPoolRoots N R trial duration target fallback additionalRoots stem
          j step i).2 ++ v) :=
  RootIndexed.position_iteratedSelectedSubtreeStepField initial d
    (fun _ => poolRoots N R trial duration target fallback additionalRoots stem)
    j step i v

/-- Every finite concrete restart iteration retains the original product
field law. -/
theorem iteratedPoolField_law
    {AdditionalRoot α X : Type*} [Countable α] [MeasurableSpace X]
    [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (trial : ℕ → Fin N ⊕ AdditionalRoot) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ AdditionalRoot) × TreeNode α)
    (hfallbackDepth : ∀ i, (fallback i).2.length = duration)
    (hfallbackInjective : Function.Injective fallback)
    (additionalRoots : AdditionalRoot → Fin N ⊕ AdditionalRoot)
    (hadditionalRoots : Function.Injective additionalRoots)
    (htrial : ∀ k r, trial k ≠ additionalRoots r)
    (hfallbackAdditionalRoots : ∀ i r, (fallback i).1 ≠ additionalRoots r)
    (stem : TreeNode α) (hstem : stem.length = duration)
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] :
    ∀ j,
      (RootIndexed.stepFieldLaw (Root := Fin N ⊕ AdditionalRoot) μ).map
          (iteratedPoolField N R trial duration target fallback additionalRoots stem j) =
        RootIndexed.stepFieldLaw (Root := Fin N ⊕ AdditionalRoot) μ := by
  exact RootIndexed.iteratedSelectedSubtreeStepField_law μ
    (fun _ => poolRoots N R trial duration target fallback additionalRoots stem)
    (fun _ => duration)
    (fun _ => poolRoots_range_countable
      N R trial duration target fallback additionalRoots stem)
    (fun _ => poolRoots_fiber_adapted
      N R hR trial duration target fallback additionalRoots stem)
    (fun _ => poolRoots_depth N R trial duration target fallback
      hfallbackDepth additionalRoots stem hstem)
    (fun _ => poolRoots_injective N R trial duration target fallback
      hfallbackInjective additionalRoots hadditionalRoots htrial hfallbackAdditionalRoots stem)

end SplitSchedule
end StepSelection
end RootIndexed
end ProbabilityTheory.BranchingRandomWalk
