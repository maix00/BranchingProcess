/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Assumptions.Structural
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law
import Probability.BranchingRandomWalk.Population.Candidates.RootIndexed.Real
import Probability.BranchingRandomWalk.Population.Processes.Selected.RootIndexed

/-!
# Almost-sure admissibility for real-valued branching walks

Boundary normalization makes every pre-sampled offspring configuration have
finite negative exponential weight almost surely.  Countability lifts this to
all root/address coordinates, and finite parent populations then have
lower-finite child sets at every generation.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

theorem RootIndexed.stepFieldLaw_ae_real_weight_finite_on_roots
    {Root α : Type*} [Countable α]
    (μ : Measure (Combinatorics.Branching.Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ) (roots : Finset Root) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      ∀ r ∈ roots, ∀ u : TreeNode α,
        totalPotentialWeight realPotential (-1) (field r u) ≠ ∞ := by
  let s : Set (Combinatorics.Branching.Step α ℝ) :=
    {ξ | totalPotentialWeight realPotential (-1) ξ ≠ ∞}
  have hs : MeasurableSet s := by
    change MeasurableSet
      ((fun ξ : Combinatorics.Branching.Step α ℝ =>
        totalPotentialWeight realPotential (-1) ξ) ⁻¹'
        ({∞}ᶜ))
    exact (totalPotentialWeight_measurable realPotential (-1))
      (MeasurableSet.singleton ∞).compl
  have hae : ∀ᵐ ξ ∂μ, ξ ∈ s := by
    exact HasBoundaryNormalization.ae_totalPotentialWeight_ne_top
      realPotential μ hnorm
  have hμ : μ s = 1 := by
    simpa using (ae_mem_iff_measure_eq hs.nullMeasurableSet).mp hae
  classical
  let e : {r : Root // r ∈ roots} ≃ Fin roots.card :=
    Fintype.equivFinOfCardEq (by simp)
  let index : Fin roots.card → Root := fun i => (e.symm i).1
  have hindexInjective : Function.Injective index := by
    intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  let restrict := fun (field : RootIndexed.StepField Root α ℝ) =>
    RootIndexed.StepField.reindex index field
  have hrestrictMeasurable : Measurable restrict := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_pi_apply (index i)
  have hfinite := finiteRootStepFieldLaw_ae_all_of_measure_one
    hs μ hμ roots.card
  have hfinite' := hfinite
  rw [← RootIndexed.stepFieldLaw_fin_restrict μ index hindexInjective] at hfinite'
  have hmap := ae_of_ae_map hrestrictMeasurable.aemeasurable hfinite'
  filter_upwards [hmap] with field hfield
  intro r hr u
  let i := e ⟨r, hr⟩
  have hi : index i = r := by simp [index, i]
  change field r u ∈ s
  simpa only [restrict, RootIndexed.StepField.reindex, hi] using hfield i u

theorem RootIndexed.selectedPopulationTotalized_admissible_ae
    {Root α : Type*} [Countable α]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Combinatorics.Branching.Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (roots : Finset Root) (initial : Root → ℝ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      ∀ n, IsLowerFiniteBy
        (RootIndexed.observedPositionAtGeneration initial id id (n + 1) field)
        (RootIndexed.childrenAtGeneration n
          (RootIndexed.selectedPopulationTotalized N roots initial id id n field)
          field) := by
  filter_upwards
    [RootIndexed.stepFieldLaw_ae_real_weight_finite_on_roots μ hnorm roots]
    with field hfield
  intro n
  exact RootIndexed.childrenAtGeneration_isLowerFiniteBy_real n
    (RootIndexed.selectedPopulationTotalized N roots initial id id n field)
    field initial
    (fun p hp => RootIndexed.selectedPopulationTotalized_depth
      N roots initial id id n field p hp)
    (fun p hp => hfield p.1
      (RootIndexed.selectedPopulationTotalized_root_mem N roots initial id id
        n field p hp) p.2)

theorem RootIndexed.selectedPopulationTotalized_succ_spec_ae
    {Root α : Type*} [Countable α]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Combinatorics.Branching.Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (roots : Finset Root) (initial : Root → ℝ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root) μ, ∀ n,
      IsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initial id id (n + 1) field)
        (RootIndexed.childrenAtGeneration n
          (RootIndexed.selectedPopulationTotalized N roots initial id id n field)
          field)
        (RootIndexed.selectedPopulationTotalized N roots initial id id (n + 1)
          field) := by
  filter_upwards
    [RootIndexed.selectedPopulationTotalized_admissible_ae μ hnorm
      N roots initial] with field hgood
  intro n
  exact RootIndexed.selectedPopulationTotalized_succ_spec
    N roots initial id id n field (hgood n)

end ProbabilityTheory.BranchingRandomWalk
