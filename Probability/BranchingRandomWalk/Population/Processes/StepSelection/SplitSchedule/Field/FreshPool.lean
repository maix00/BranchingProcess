/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Definition.Roots
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily

/-!
# Extending a successful population to a fresh root pool

A successful population supplies the finite active part of the next field.
An injectively labelled additional root family supplies all remaining root labels.
This produces a complete product field whose root type can be reused at the
next restart stage.
## Public declarations

Appending an injectively labelled additional root family disjoint from the active
roots gives an injective pool map and a full product field:

\[\operatorname{poolRoots}:\mathrm{Fin}(N)\oplus\mathrm{AdditionalRoot}
  \hookrightarrow\mathrm{Root}\times\mathbb V,\qquad
  \operatorname{Law}(\operatorname{poolField})
  =\operatorname{stepFieldLaw}_{\mathrm{Fin}(N)\oplus\mathrm{AdditionalRoot}}(\mu).\]

* `activeRoots` and `extendRoots` form the active and additional-root root index and its
  injective inclusion; `mem_activeRoots`, `card_activeRoots`,
  `extendRoots_left_injective`, and `extendRoots_injective` describe them.
* `poolRoots` labels the selected active roots together with an injective
  additional root family. Its range, fibers, depths, separation of active and additional roots, and
  injectivity are stated by `poolRoots_range_countable`,
  `poolRoots_fiber_adapted`, `poolRoots_depth`, `roots_root_ne_additionalRoot`, and
  `poolRoots_injective`.
* `poolField` is the complete root-indexed field on this pool, and
  `poolField_law` proves that it has the product law of the original field.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed
namespace StepSelection
namespace SplitSchedule

open Combinatorics.UlamHarris Combinatorics.Branching

/-- Labels of the finite active part of an active and additional root pool. -/
def activeRoots {AdditionalRoot : Type*} (N : ℕ) : Finset (Fin N ⊕ AdditionalRoot) :=
  Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩

@[simp] theorem mem_activeRoots {AdditionalRoot : Type*} (N : ℕ)
    (r : Fin N ⊕ AdditionalRoot) :
    r ∈ activeRoots N ↔ ∃ i : Fin N, r = Sum.inl i := by
  simp [activeRoots, eq_comm]

@[simp] theorem card_activeRoots {AdditionalRoot : Type*} (N : ℕ) :
    (activeRoots (AdditionalRoot := AdditionalRoot) N).card = N := by
  simp [activeRoots]

/-- Extend a finite active family by a additional root family rooted at one fixed
address. -/
def extendRoots
    {Root AdditionalRoot α : Type*} {N : ℕ}
    (active : Fin N → Root × TreeNode α)
    (additionalRoots : AdditionalRoot → Root) (stem : TreeNode α) :
    Fin N ⊕ AdditionalRoot → Root × TreeNode α
  | Sum.inl i => active i
  | Sum.inr r => (additionalRoots r, stem)

theorem extendRoots_left_injective
    {Root AdditionalRoot α : Type*} {N : ℕ}
    (additionalRoots : AdditionalRoot → Root) (stem : TreeNode α) :
    Function.Injective
      (fun active : Fin N → Root × TreeNode α =>
        extendRoots active additionalRoots stem) := by
  intro active₁ active₂ h
  funext i
  exact congrFun h (Sum.inl i)

theorem extendRoots_injective
    {Root AdditionalRoot α : Type*} {N : ℕ}
    (active : Fin N → Root × TreeNode α)
    (additionalRoots : AdditionalRoot → Root) (stem : TreeNode α)
    (hactive : Function.Injective active)
    (hadditionalRoots : Function.Injective additionalRoots)
    (hcross : ∀ i r, (active i).1 ≠ additionalRoots r) :
    Function.Injective (extendRoots active additionalRoots stem) := by
  intro a b hab
  cases a with
  | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (hactive hab)
      | inr r => exact (hcross i r (congrArg Prod.fst hab)).elim
  | inr r =>
      cases b with
      | inl i => exact (hcross i r (congrArg Prod.fst hab).symm).elim
      | inr s => exact congrArg Sum.inr (hadditionalRoots (congrArg Prod.fst hab))

/-- The successful active roots together with a deterministic additional root family. -/
noncomputable def poolRoots
    {Root AdditionalRoot α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (additionalRoots : AdditionalRoot → Root) (stem : TreeNode α)
    (ω : RootIndexed.StepField Root α X) :
    Fin N ⊕ AdditionalRoot → Root × TreeNode α :=
  extendRoots (roots N R trial duration target fallback ω) additionalRoots stem

theorem poolRoots_range_countable
    {Root AdditionalRoot α X : Type*} [Countable α]
    [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (additionalRoots : AdditionalRoot → Root) (stem : TreeNode α) :
    (Set.range (poolRoots N R trial duration target fallback additionalRoots stem)
      ).Countable := by
  apply ((roots_range_countable N R trial duration target fallback).image
    (fun active => extendRoots active additionalRoots stem)).mono
  rintro selected ⟨ω, rfl⟩
  exact ⟨roots N R trial duration target fallback ω,
    ⟨ω, rfl⟩, rfl⟩

theorem poolRoots_fiber_adapted
    {Root AdditionalRoot α X : Type*} [Countable α] [MeasurableSpace X]
    [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (trial : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (additionalRoots : AdditionalRoot → Root) (stem : TreeNode α)
    (selected : Fin N ⊕ AdditionalRoot → Root × TreeNode α) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) duration]
      {ω | poolRoots N R trial duration target fallback additionalRoots stem ω =
        selected} := by
  let _ : MeasurableSpace (RootIndexed.StepField Root α X) :=
    RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) duration
  let extend := fun active : Fin N → Root × TreeNode α =>
    extendRoots active additionalRoots stem
  have hextend : Function.Injective extend :=
    extendRoots_left_injective additionalRoots stem
  by_cases hselected : selected ∈ Set.range extend
  · obtain ⟨active, rfl⟩ := hselected
    have hset :
        {ω : RootIndexed.StepField Root α X |
          poolRoots N R trial duration target fallback additionalRoots stem ω =
            extend active} =
        {ω | roots N R trial duration target fallback ω = active} := by
      ext ω
      exact hextend.eq_iff
    rw [hset]
    exact roots_fiber_adapted N R hR trial duration target fallback active
  · have hset :
        {ω : RootIndexed.StepField Root α X |
          poolRoots N R trial duration target fallback additionalRoots stem ω =
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
    {Root AdditionalRoot α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (hfallback : ∀ i, (fallback i).2.length = duration)
    (additionalRoots : AdditionalRoot → Root) (stem : TreeNode α)
    (hstem : stem.length = duration)
    (ω : RootIndexed.StepField Root α X)
    (i : Fin N ⊕ AdditionalRoot) :
    ((poolRoots N R trial duration target fallback additionalRoots stem ω i).2
      ).length = duration := by
  cases i with
  | inl i => exact roots_depth N R trial duration target fallback hfallback ω i
  | inr _ => exact hstem

theorem roots_root_ne_additionalRoot
    {Root AdditionalRoot α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (additionalRoots : AdditionalRoot → Root)
    (htrial : ∀ k r, trial k ≠ additionalRoots r)
    (hfallback : ∀ i r, (fallback i).1 ≠ additionalRoots r)
    (ω : RootIndexed.StepField Root α X) (i : Fin N) (r : AdditionalRoot) :
    (roots N R trial duration target fallback ω i).1 ≠ additionalRoots r := by
  induction hfirst : firstSuccess R trial duration target ω using WithTop.recTopCoe with
  | top => simpa [roots, hfirst] using hfallback i r
  | coe k =>
      rw [roots, hfirst, WithTop.recTopCoe_coe, rootFamily]
      split_ifs
      · exact htrial k r
      · exact hfallback i r

theorem poolRoots_injective
    {Root AdditionalRoot α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (hfallbackInjective : Function.Injective fallback)
    (additionalRoots : AdditionalRoot → Root) (hadditionalRoots : Function.Injective additionalRoots)
    (htrial : ∀ k r, trial k ≠ additionalRoots r)
    (hfallbackAdditionalRoots : ∀ i r, (fallback i).1 ≠ additionalRoots r)
    (stem : TreeNode α) (ω : RootIndexed.StepField Root α X) :
    Function.Injective
      (poolRoots N R trial duration target fallback additionalRoots stem ω) := by
  exact extendRoots_injective _ additionalRoots stem
    (roots_injective N R trial duration target fallback
      hfallbackInjective ω)
    hadditionalRoots
    (roots_root_ne_additionalRoot N R trial duration target fallback additionalRoots
      htrial hfallbackAdditionalRoots ω)

/-- The full descendant field below the root pool with active and additional roots. -/
noncomputable def poolField
    {Root AdditionalRoot α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (additionalRoots : AdditionalRoot → Root) (stem : TreeNode α)
    (ω : RootIndexed.StepField Root α X) :
    RootIndexed.StepField (Fin N ⊕ AdditionalRoot) α X :=
  RootIndexed.selectedSubtreeStepFieldVector
    (poolRoots N R trial duration target fallback additionalRoots stem) ω

theorem poolField_law
    {Root AdditionalRoot α X : Type*} [Countable α] [MeasurableSpace X]
    [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (trial : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (hfallbackDepth : ∀ i, (fallback i).2.length = duration)
    (hfallbackInjective : Function.Injective fallback)
    (additionalRoots : AdditionalRoot → Root) (hadditionalRoots : Function.Injective additionalRoots)
    (htrial : ∀ k r, trial k ≠ additionalRoots r)
    (hfallbackAdditionalRoots : ∀ i r, (fallback i).1 ≠ additionalRoots r)
    (stem : TreeNode α) (hstem : stem.length = duration)
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] :
    (RootIndexed.stepFieldLaw (Root := Root) μ).map
        (poolField N R trial duration target fallback additionalRoots stem) =
      RootIndexed.stepFieldLaw (Root := Fin N ⊕ AdditionalRoot) μ := by
  exact RootIndexed.selectedSubtreeStepFieldVector_law μ
    (poolRoots N R trial duration target fallback additionalRoots stem)
    (poolRoots_range_countable N R trial duration target fallback additionalRoots stem)
    (poolRoots_fiber_adapted N R hR trial duration target fallback additionalRoots stem)
    (poolRoots_depth N R trial duration target fallback hfallbackDepth
      additionalRoots stem hstem)
    (poolRoots_injective N R trial duration target fallback
      hfallbackInjective additionalRoots hadditionalRoots htrial hfallbackAdditionalRoots stem)

end SplitSchedule
end StepSelection
end RootIndexed
end ProbabilityTheory.BranchingRandomWalk
