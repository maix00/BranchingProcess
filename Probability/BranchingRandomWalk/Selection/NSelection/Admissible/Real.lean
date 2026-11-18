/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Assumptions.Structural
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic
public import Probability.BranchingRandomWalk.Population.Candidates.RootIndexed.RealPosition
public import Probability.BranchingRandomWalk.Population.Processes.Selected.RootIndexed

/-!
# Almost-sure admissibility for real-valued branching walks

## Public declarations

- `ae_isLeftLocallyFinite_of_exponentialMoment`: a finite mean
  $\mathbb E[\sum_i e^{-\beta\Xi_i}]$ for $\beta>0$ implies almost-sure
  left local finiteness of the offspring configurations.
- `HasBoundaryNormalization.ae_isLeftLocallyFinite`: specialization to
  $\mathbb E[\sum_i e^{-\Xi_i}]=1$.
- `RootIndexed.selectedPopulationTotalized_admissible_ae_of_leftLocallyFinite`:
  if the offspring configurations are almost surely locally finite on the left,
  then every candidate set of a finite first-$N$ population is lower finite.

- `ProbabilityTheory.BranchingRandomWalk.RootIndexed.stepFieldLaw_ae_real_weight_finite_on_roots`:
  boundary normalization implies that, almost surely, each of finitely many
  roots has finite negative exponential weight at every address.
- `ProbabilityTheory.BranchingRandomWalk.RootIndexed.selectedPopulationTotalized_admissible_ae`:
  almost surely, every generation's selected population has a lower-finite
  child-position set.
- `ProbabilityTheory.BranchingRandomWalk.RootIndexed.selectedPopulationTotalized_succ_spec_ae`:
  almost surely, each next selected population is the first \(N\) children in
  the prescribed order.

- `ProbabilityTheory.BranchingRandomWalk.RootIndexed.selectedPopulationTotalized_nonempty_ae`:
  for nonempty initial roots, positive capacity, boundary normalization and
  almost surely nonempty offspring, $Z_n\ne\varnothing$ for all $n$ almost surely.

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
open _root_.Combinatorics.Selection.NSelection

/-- The positive-exponent moment condition in Zhan Shi, *Branching Random
Walks* (Springer, 2015), Chapter 1, §§1.3 and 1.6,
DOI 10.1007/978-3-319-25372-5, implies left local finiteness. -/
theorem ae_isLeftLocallyFinite_of_exponentialMoment {α : Type*} [Countable α]
    (μ : Measure (Step α ℝ)) {β : ℝ} (hβ : 0 < β)
    (hweight : (∫⁻ ξ, totalPotentialWeight realPotential (-β) ξ ∂μ) ≠ ∞) :
    ∀ᵐ ξ ∂μ, ξ.IsLeftLocallyFinite := by
  filter_upwards [ae_lt_top (totalPotentialWeight_measurable realPotential (-β)) hweight]
    with ξ hξ
  exact ξ.isLeftLocallyFinite_of_totalPotentialWeight_ne_top hβ hξ.ne

theorem HasBoundaryNormalization.ae_isLeftLocallyFinite {α : Type*} [Countable α]
    {μ : Measure (Step α ℝ)} (h : HasBoundaryNormalization realPotential μ) :
    ∀ᵐ ξ ∂μ, ξ.IsLeftLocallyFinite := by
  filter_upwards [HasBoundaryNormalization.ae_totalPotentialWeight_ne_top realPotential μ h] with ξ hξ
  exact ξ.isLeftLocallyFinite_of_totalPotentialWeight_ne_top (β := 1) zero_lt_one hξ

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

theorem RootIndexed.selectedPopulationTotalized_admissible_ae_of_leftLocallyFinite
    {Root α : Type*} [Countable α]
    [Countable (RootIndexed.TreeNode Root α)]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Combinatorics.Branching.Step α ℝ)) [IsProbabilityMeasure μ]
    (hleft : ∀ᵐ ξ ∂μ, ξ.IsLeftLocallyFinite)
    (N : ℕ) (roots : Finset Root) (initial : Root → ℝ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      ∀ n, IsLowerFiniteBy
        (RootIndexed.observedPositionAtGeneration initial id id (n + 1) field)
        (Combinatorics.Branching.Population.childrenAtGeneration n
          (RootIndexed.selectedPopulationTotalized N roots initial id id n field)
          field) := by
  have : Countable Root := (show Function.Injective (fun r : Root => (r, ([] : TreeNode α)))
    from fun _ _ h => congrArg Prod.fst h).countable
  have hμ : μ {ξ | ξ.IsLeftLocallyFinite} = 1 := by
    simpa using (ae_mem_iff_measure_eq
      Step.measurableSet_isLeftLocallyFinite.nullMeasurableSet).mp hleft
  filter_upwards [RootIndexed.stepFieldLaw_ae_all_of_measure_one (Root := Root)
    Step.measurableSet_isLeftLocallyFinite μ hμ] with field hfield
  intro n
  exact RootIndexed.childrenAtGeneration_isLowerFiniteBy_of_leftLocallyFinite n
    (RootIndexed.selectedPopulationTotalized N roots initial id id n field)
    field initial (fun p _ => hfield p.1 p.2)

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
        (Combinatorics.Branching.Population.childrenAtGeneration n
          (RootIndexed.selectedPopulationTotalized N roots initial id id n field)
          field) := by
  filter_upwards
    [RootIndexed.stepFieldLaw_ae_real_weight_finite_on_roots μ hnorm roots]
    with field hfield
  intro n
  exact RootIndexed.childrenAtGeneration_isLowerFiniteBy_real n
    (RootIndexed.selectedPopulationTotalized N roots initial id id n field)
    field initial
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
        (Combinatorics.Branching.Population.childrenAtGeneration n
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

/-- A nonempty initial population stays nonempty under an almost surely
nonempty offspring law and admissible first-`N` selection. -/
theorem RootIndexed.selectedPopulationTotalized_nonempty_ae
    {Root α : Type*} [Countable Root] [Countable α]
    (N : ℕ) (roots : Finset Root) (hroots : roots.Nonempty)
    (initialPosition : Root → ℝ) (hN : 0 < N)
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      ∀ n, (RootIndexed.selectedPopulationTotalized N
        roots initialPosition id id n field).Nonempty := by
  have hspec := RootIndexed.selectedPopulationTotalized_succ_spec_ae
    μ hboundary N roots initialPosition
  have hchildren := RootIndexed.stepFieldLaw_ae_all_of_measure_one (Root := Root)
    nonemptySupport_measurable μ hnonempty
  filter_upwards [hspec, hchildren] with field hspec hchildren
  intro n
  induction n with
  | zero =>
      obtain ⟨r, hr⟩ := hroots
      exact ⟨(r, []), RootIndexed.mem_initialPopulation_iff.mpr ⟨r, hr, rfl⟩⟩
  | succ n ih =>
      let parents := RootIndexed.selectedPopulationTotalized N
        roots initialPosition id id n field
      have hdepth : ∀ p ∈ parents, p.2.length = n := by
        intro p hp
        exact RootIndexed.selectedPopulationTotalized_depth N roots
          initialPosition id id n field p hp
      have hcandidates :
          (Combinatorics.Branching.Population.childrenAtGeneration n parents field).Nonempty := by
        rcases ih with ⟨p, hp⟩
        obtain ⟨i, hi⟩ := hchildren p.1 p.2
        exact ⟨(p.1, p.2 ++ [i]),
          Combinatorics.Branching.Population.childAddress_mem_childrenAtGeneration n parents field
            p hp (hdepth p hp) i hi⟩
      have hselected : IsFirstNBy N
          (RootIndexed.observedPositionAtGeneration initialPosition
            id id (n + 1) field)
          (Combinatorics.Branching.Population.childrenAtGeneration n parents field)
          (RootIndexed.selectedPopulationTotalized N
            roots initialPosition id id
            (n + 1) field) := hspec n
      exact hselected.nonempty_of_nonempty_candidates hN hcandidates

end ProbabilityTheory.BranchingRandomWalk
