import Probability.BranchingRandomWalk.Analytic.ExceptionalEvent
import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.Exploration.SelectedSubtree
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Law
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.RootFamily
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.DomainFlow.RootSubset

/-!
# First-moment estimates from a fresh reserve subtree

This file connects the coordinate-domain exploration interface to the
first-moment exceptional-event estimate.  Once a reserve root is chosen from
the inspected information and its descendant coordinates are fresh, every
measurable real observable of that subtree is independent of the exploration
domain.  Consequently its contribution on any failure event in that domain
gains the probability of the failure event exactly.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

/-- A measurable observable of a fresh, measurably selected reserve subtree is
independent of the information used to select that subtree. -/
theorem BranchingExplorationDomains.selected_fresh_subtree_observable_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (H : BranchingExplorationDomains α X) (j : ℕ)
    (chosen : (TreeNode α → Step α X) → TreeNode α)
    (hchosen : Measurable[H.domain j] chosen)
    (hcount : (Set.range chosen).Countable)
    (hfresh : ∀ ω, Disjoint (H.inspected j)
      (branchingDescendantAddresses (chosen ω)))
    (g : (TreeNode α → Step α X) → ℝ) (hg : Measurable g) :
    Indep (H.domain j)
      (MeasurableSpace.comap
        (fun ω => g (selectedSubtreeStepField chosen ω)) inferInstance)
      (stepFieldLaw μ) := by
  have hind := H.selected_fresh_subtree_independent μ j chosen hchosen
    hcount hfresh
  apply indep_of_indep_of_le_right hind
  have hs : Measurable[
      MeasurableSpace.comap (selectedSubtreeStepField chosen) inferInstance]
      (fun ω => g (selectedSubtreeStepField chosen ω)) :=
    hg.comp (Measurable.of_comap_le le_rfl)
  exact hs.comap_le

/-- Exact `L¹` factorization for a reserve-subtree observable on a failure
event determined by the inspected exploration domain. -/
theorem BranchingExplorationDomains.integral_reserve_abs_on_event
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (H : BranchingExplorationDomains α X) (j : ℕ)
    (chosen : (TreeNode α → Step α X) → TreeNode α)
    (hchosen : Measurable[H.domain j] chosen)
    (hcount : (Set.range chosen).Countable)
    (hfresh : ∀ ω, Disjoint (H.inspected j)
      (branchingDescendantAddresses (chosen ω)))
    (g : (TreeNode α → Step α X) → ℝ) (hg : Measurable g)
    (E : Set (TreeNode α → Step α X))
    (hE : MeasurableSet[H.domain j] E)
    (hint : Integrable
      (fun ω => g (selectedSubtreeStepField chosen ω)) (stepFieldLaw μ)) :
    (∫ ω, |g (selectedSubtreeStepField chosen ω)| *
        E.indicator (fun _ => (1 : ℝ)) ω ∂stepFieldLaw μ) =
      (∫ ω, |g (selectedSubtreeStepField chosen ω)| ∂stepFieldLaw μ) *
        (stepFieldLaw μ).real E := by
  have hEfull : MeasurableSet E :=
    ((H.domain_le j).trans (stepsOnSpace_le _)) E hE
  exact integral_abs_mul_indicator_eq_of_indep
    (stepFieldLaw μ) (H.domain j)
    (fun ω => g (selectedSubtreeStepField chosen ω)) E hint hE hEfull
    (H.selected_fresh_subtree_observable_independent μ j chosen
      hchosen hcount hfresh g hg)

/-- An observable of any measurably selected family of fresh subtrees in an
arbitrary root-indexed field is independent of the generation domain flow.
The selected family itself may have an arbitrary index type. -/
theorem RootIndexed.selectedSubtree_observable_independent
    {Root κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {n : ℕ}
    (chosen : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {ω | chosen ω = roots})
    (hdepth : ∀ ω i, (chosen ω i).2.length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω))
    (g : (κ → TreeNode α → Step α X) → ℝ) (hg : Measurable g) :
    Indep (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n)
      (MeasurableSpace.comap
        (fun ω => g (RootIndexed.selectedSubtreeStepFieldVector chosen ω))
        inferInstance)
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  have hind := RootIndexed.selectedSubtreeStepFieldVector_independent μ
    chosen hcount hfiber hdepth hinj
  apply indep_of_indep_of_le_right hind
  have hs : Measurable[MeasurableSpace.comap
      (RootIndexed.selectedSubtreeStepFieldVector chosen) inferInstance]
      (fun ω => g (RootIndexed.selectedSubtreeStepFieldVector chosen ω)) :=
    hg.comp (Measurable.of_comap_le le_rfl)
  exact hs.comap_le

/-- Exact first-moment factorization for an arbitrary root-indexed reserve
family on an event visible in the generation domain flow. -/
theorem RootIndexed.integral_reserve_abs_on_event
    {Root κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {n : ℕ}
    (chosen : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {ω | chosen ω = roots})
    (hdepth : ∀ ω i, (chosen ω i).2.length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω))
    (g : (κ → TreeNode α → Step α X) → ℝ) (hg : Measurable g)
    (E : Set (RootIndexed.StepField Root α X))
    (hE : MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] E)
    (hint : Integrable
      (fun ω => g (RootIndexed.selectedSubtreeStepFieldVector chosen ω))
      (RootIndexed.stepFieldLaw (Root := Root) μ)) :
    (∫ ω, |g (RootIndexed.selectedSubtreeStepFieldVector chosen ω)| *
        E.indicator (fun _ => (1 : ℝ)) ω
      ∂RootIndexed.stepFieldLaw (Root := Root) μ) =
      (∫ ω, |g (RootIndexed.selectedSubtreeStepFieldVector chosen ω)|
        ∂RootIndexed.stepFieldLaw (Root := Root) μ) *
        (RootIndexed.stepFieldLaw (Root := Root) μ).real E := by
  have hEfull : MeasurableSet E :=
    (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) |>.le n) E hE
  exact integral_abs_mul_indicator_eq_of_indep
    (RootIndexed.stepFieldLaw (Root := Root) μ)
    (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n)
    (fun ω => g (RootIndexed.selectedSubtreeStepFieldVector chosen ω)) E
    hint hE hEfull
    (RootIndexed.selectedSubtree_observable_independent μ chosen hcount
      hfiber hdepth hinj g hg)

/-- Exact first-moment factorization when all trials are confined to one set
of initial roots and the continuation reads a fixed disjoint reserve-root
family.  This is the canonical concurrent pre-sampling interface: trial and
reserve trees coexist in one root-indexed field, but their coordinates are
disjoint. -/
theorem RootIndexed.integral_reserveRoot_abs_on_event
    {Root κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (trials : Set Root) (reserve : κ → Root)
    (hdisjoint : Disjoint trials (Set.range reserve)) (n : ℕ)
    (g : (κ → TreeNode α → Step α X) → ℝ) (hg : Measurable g)
    (E : Set (RootIndexed.StepField Root α X))
    (hE : MeasurableSet[RootIndexed.rootFiltration
      (α := α) (X := X) trials n] E)
    (hint : Integrable
      (fun ω => g (fun i => ω (reserve i)))
      (RootIndexed.stepFieldLaw (Root := Root) μ)) :
    (∫ ω, |g (fun i => ω (reserve i))| *
        E.indicator (fun _ => (1 : ℝ)) ω
      ∂RootIndexed.stepFieldLaw (Root := Root) μ) =
      (∫ ω, |g (fun i => ω (reserve i))|
        ∂RootIndexed.stepFieldLaw (Root := Root) μ) *
        (RootIndexed.stepFieldLaw (Root := Root) μ).real E := by
  have hEfull : MeasurableSet E :=
    (RootIndexed.rootFiltration
      (α := α) (X := X) trials |>.le n) E hE
  have hind := RootIndexed.reserveField_independent μ trials reserve
    hdisjoint n
  apply integral_abs_mul_indicator_eq_of_indep
    (RootIndexed.stepFieldLaw (Root := Root) μ)
    (RootIndexed.rootFiltration (α := α) (X := X) trials n)
    (fun ω => g (fun i => ω (reserve i))) E hint hE hEfull
  apply indep_of_indep_of_le_right hind
  have hm : Measurable[MeasurableSpace.comap
      (fun ω : RootIndexed.StepField Root α X => fun i => ω (reserve i))
      inferInstance]
      (fun ω => g (fun i => ω (reserve i))) :=
    hg.comp (Measurable.of_comap_le le_rfl)
  exact hm.comap_le

/-- A measurable real observable of a generation-measurably selected vector
of distinct reserve subtrees is independent of the multi-root generation
domain.  This is the form used for a walk started from `m` labelled roots. -/
theorem selectedMultiRootSubtree_observable_independent
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ}
    (chosen : FiniteRootStepField m ℕ X → Fin k → Fin m × 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := X) n] chosen)
    (hdepth : ∀ step j, (chosen step j).2.length = n)
    (hinj : ∀ step, Function.Injective (chosen step))
    (g : (Fin k → 𝕍 → Step ℕ X) → ℝ) (hg : Measurable g) :
    Indep (multiRootStepFiltration (m := m) (X := X) n)
      (MeasurableSpace.comap
        (fun ω => g (selectedMultiRootSubtreeStepFieldVector chosen ω))
        inferInstance)
      (finiteRootStepFieldLaw μ m) := by
  have hind := selectedMultiRootSubtreeStepFieldVector_independent μ chosen
    hchosen hdepth hinj
  apply indep_of_indep_of_le_right hind
  have hs : Measurable[MeasurableSpace.comap
      (selectedMultiRootSubtreeStepFieldVector chosen) inferInstance]
      (fun ω => g (selectedMultiRootSubtreeStepFieldVector chosen ω)) :=
    hg.comp (Measurable.of_comap_le le_rfl)
  exact hs.comap_le

/-- Exact first-moment factorization for an observable of a selected reserve
subtree vector on a failure event visible at generation `n`. -/
theorem integral_selectedMultiRoot_reserve_abs_on_event
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ}
    (chosen : FiniteRootStepField m ℕ X → Fin k → Fin m × 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := X) n] chosen)
    (hdepth : ∀ step j, (chosen step j).2.length = n)
    (hinj : ∀ step, Function.Injective (chosen step))
    (g : (Fin k → 𝕍 → Step ℕ X) → ℝ) (hg : Measurable g)
    (E : Set (FiniteRootStepField m ℕ X))
    (hE : MeasurableSet[
      multiRootStepFiltration (m := m) (X := X) n] E)
    (hint : Integrable
      (fun ω => g (selectedMultiRootSubtreeStepFieldVector chosen ω))
      (finiteRootStepFieldLaw μ m)) :
    (∫ ω, |g (selectedMultiRootSubtreeStepFieldVector chosen ω)| *
        E.indicator (fun _ => (1 : ℝ)) ω ∂finiteRootStepFieldLaw μ m) =
      (∫ ω, |g (selectedMultiRootSubtreeStepFieldVector chosen ω)|
        ∂finiteRootStepFieldLaw μ m) *
        (finiteRootStepFieldLaw μ m).real E := by
  have hEfull : MeasurableSet E :=
    (multiRootStepFiltration (m := m) (X := X) |>.le n) E hE
  exact integral_abs_mul_indicator_eq_of_indep
    (finiteRootStepFieldLaw μ m)
    (multiRootStepFiltration (m := m) (X := X) n)
    (fun ω => g (selectedMultiRootSubtreeStepFieldVector chosen ω)) E
    hint hE hEfull
    (selectedMultiRootSubtree_observable_independent μ chosen hchosen
      hdepth hinj g hg)

end ProbabilityTheory.BranchingRandomWalk
