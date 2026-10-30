/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.FirstPassage
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic
public import Probability.BranchingRandomWalk.Population.Processes.Selected.RootIndexed

public import Mathlib.Order.Defs.LinearOrder

/-!
# Selected-population transfer for endpoint paths with bounded drawdown

## Public declarations

The declarations are in
`ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation`.

- `firstNSelectedPopulation m N n` defines the generation-`n` first-`N`
  population from `m` zero-started roots.
- `firstNSelectedNoLargeDropEndpointBelow m N n delta threshold` is the event
  that some selected endpoint is at most `threshold` and its ancestral path
  has no downward drawdown greater than `delta`.
- `firstNSelectedPopulation_adapted` states that the selected population is
  measurable from generations below `n`.
- `firstNSelectedPopulation_card_le` proves the selected population has at
  most `N` addresses when the initial root count satisfies `m ≤ N`.
- `firstNSelectedPopulation_measurable` and
  `measurableSet_firstNSelectedNoLargeDropEndpointBelow` prove measurability
  of that population and event, for the countable measurable linearly ordered
  root-indexed address space in their signatures.
- `firstNSelectedPopulation_depth` and
  `firstNSelectedPopulation_surviveAlong` state that
  `p ∈ firstNSelectedPopulation m N n field` implies `p.2.length = n` and
  `surviveAlong (field p.1) [] p.2`.
- `firstNSelectedPopulation_prefix_mem` states that if an address belongs to
  generation `n`, then each prefix of length `j ≤ n` belongs to generation
  `j` of the selected population.
- `firstNSelectedNoLargeDropEndpointBelow_subset_roots` gives the pathwise
  inclusion `E_{m,N,n}(delta,threshold) ⊆ ⋃ r : Fin m, {field | field r ∈ E₁}`,
  where `E₁` is the corresponding one-root event.
- `measure_firstNSelectedNoLargeDropEndpointBelow_le` proves, under boundary
  normalization,
  \[
  \mathbb P_{\mu^{\otimes m}}(E_{m,N,n}(\delta,x))
  \le m e^x\,\mathbb P_{\widetilde\mu}
  (\text{one-root path has drawdown at most }\delta\text{ and endpoint at most }x).
  \]

At a fixed generation, every particle retained by first-`N` selection is an
actual surviving vertex of one of the initial root trees.  Thus the event
that a retained particle has a low endpoint and no large ancestral drawdown
is contained in the union of the corresponding one-root branching events.
The existing many-to-one estimate then gives the selected-population bound.
This is only the no-large-drawdown term in Aïdékon--Hu's estimate (4.16); the
large-drawdown exceptional event is a separate estimate.

The cited bound is equation (4.16) in the proof of Proposition 3.1 of Elie
Aïdékon and Yueyun Hu, *Average-weight percolation on the complete graph*,
arXiv:2512.23266 (2025).
-/

@[expose] public section
attribute [local instance] Classical.propDecidable Classical.decEq

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- The generation-`n` population produced by totalized first-`N`
selection from `m` independent initial roots, all started at zero.  The
totalized selector is empty off the lower-finite domain, so no nonempty
offspring assumption is built into this definition. -/
noncomputable def firstNSelectedPopulation (m N n : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) :
    Finset (RootIndexed.TreeNode (Fin m) ℕ) := by
  classical
  exact RootIndexed.selectedPopulationTotalized N
    (Finset.univ : Finset (Fin m)) (fun _ => 0) id id n field

/-- The selected population has at most `N` addresses whenever the initial
population also fits within the capacity. -/
theorem firstNSelectedPopulation_card_le (m N n : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hmN : m ≤ N) (field : FiniteRootStepField m ℕ ℝ) :
    (firstNSelectedPopulation m N n field).card ≤ N := by
  classical
  cases n with
  | zero =>
      simpa [firstNSelectedPopulation, RootIndexed.selectedPopulationTotalized,
        RootIndexed.initialPopulation_card] using hmN
  | succ n =>
      let value := RootIndexed.observedPositionAtGeneration
        (α := ℕ) (fun _ : Fin m => (0 : ℝ)) (id : ℝ → ℝ) (id : ℝ → ℝ) (n + 1)
      let candidates := fun ω : FiniteRootStepField m ℕ ℝ =>
        Combinatorics.Branching.Population.childrenAtGeneration n
          (RootIndexed.selectedPopulationTotalized N Finset.univ
            (fun _ : Fin m => (0 : ℝ)) id id n ω) ω
      by_cases hgood : Combinatorics.Selection.NSelection.IsLowerFiniteBy
          (value field) (candidates field)
      · change (RootIndexed.selectedPopulationTotalized N Finset.univ
          (fun _ : Fin m => (0 : ℝ)) id id (n + 1) field).card ≤ N
        exact (RootIndexed.selectedPopulationTotalized_succ_spec
          N Finset.univ (fun _ : Fin m => (0 : ℝ)) id id n field hgood).card_le
      · change (Combinatorics.Selection.NSelection.selectFirstNFromSetTotalized
          N value candidates field).card ≤ N
        rw [Combinatorics.Selection.NSelection.selectFirstNFromSetTotalized_empty_of_not_lowerFinite
          N value candidates field hgood]
        simp

/-- A selected generation-`n` particle has endpoint at most `threshold` and
its ancestral path has no downward drawdown larger than `delta`.  The event
is phrased by an actual selected address, so it is false when the selected
population is empty. -/
def firstNSelectedNoLargeDropEndpointBelow (m N n : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (delta threshold : ℝ) : Set (FiniteRootStepField m ℕ ℝ) :=
  {field | ∃ p : RootIndexed.TreeNode (Fin m) ℕ,
    p ∈ firstNSelectedPopulation m N n field ∧
      p.2.length = n ∧
      surviveAlong (field p.1) [] p.2 ∧
      historyNoLargeDropAndEndpointBelow delta threshold
        (Spine.pathHistory realPotential n 0 (field p.1) p.2)}

theorem firstNSelectedPopulation_measurable (m N n : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    Measurable (firstNSelectedPopulation m N n) := by
  classical
  have hflow : Measurable[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) n]
      (firstNSelectedPopulation m N n) := by
    exact RootIndexed.selectedPopulationTotalized_adapted
      N (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) id
      measurable_id id measurable_id n
  exact hflow.mono
    (Filtration.le (RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ)) n)
    le_rfl

/-- The generation-`n` selected population is measurable with respect to the
domain flow that reveals the step field below generation `n`. -/
theorem firstNSelectedPopulation_adapted (m N n : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    Measurable[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) n]
      (firstNSelectedPopulation m N n) := by
  classical
  exact RootIndexed.selectedPopulationTotalized_adapted
    N (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) id measurable_id
    id measurable_id n

theorem measurableSet_firstNSelectedNoLargeDropEndpointBelow
    (m N n : ℕ) [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (delta threshold : ℝ) :
    MeasurableSet
      (firstNSelectedNoLargeDropEndpointBelow m N n delta threshold) := by
  have hpopulation : Measurable (firstNSelectedPopulation m N n) :=
    firstNSelectedPopulation_measurable m N n
  rw [show firstNSelectedNoLargeDropEndpointBelow m N n delta threshold =
      ⋃ p : RootIndexed.TreeNode (Fin m) ℕ,
        {field | p ∈ firstNSelectedPopulation m N n field ∧
          p.2.length = n ∧
          surviveAlong (field p.1) [] p.2 ∧
          historyNoLargeDropAndEndpointBelow delta threshold
            (Spine.pathHistory realPotential n 0 (field p.1) p.2)} by
    ext field
    simp [firstNSelectedNoLargeDropEndpointBelow]]
  apply MeasurableSet.iUnion
  intro p
  have hmem : MeasurableSet
      {field : FiniteRootStepField m ℕ ℝ |
        p ∈ firstNSelectedPopulation m N n field} :=
    hpopulation (measurableSet_mem_finset p)
  have hdepth : MeasurableSet
      {field : FiniteRootStepField m ℕ ℝ | p.2.length = n} := by
    by_cases hp : p.2.length = n <;> simp [hp]
  have hpath : MeasurableSet
      {field : FiniteRootStepField m ℕ ℝ |
        historyNoLargeDropAndEndpointBelow delta threshold
          (Spine.pathHistory realPotential n 0 (field p.1) p.2)} :=
    (measurableSet_historyNoLargeDropAndEndpointBelow delta threshold).preimage
      ((Spine.pathHistory_measurable realPotential n 0 p.2).comp
        (measurable_pi_apply p.1))
  have hsurvive : MeasurableSet
      {field : FiniteRootStepField m ℕ ℝ |
        surviveAlong (field p.1) [] p.2} :=
    (Spine.measurableSet_surviveAlong [] p.2).preimage
      (measurable_pi_apply p.1)
  rw [show {field : FiniteRootStepField m ℕ ℝ |
      p ∈ firstNSelectedPopulation m N n field ∧
        p.2.length = n ∧
        surviveAlong (field p.1) [] p.2 ∧
        historyNoLargeDropAndEndpointBelow delta threshold
          (Spine.pathHistory realPotential n 0 (field p.1) p.2)} =
      {field | p ∈ firstNSelectedPopulation m N n field} ∩
        {field | p.2.length = n} ∩
        {field | surviveAlong (field p.1) [] p.2} ∩
        {field | historyNoLargeDropAndEndpointBelow delta threshold
          (Spine.pathHistory realPotential n 0 (field p.1) p.2)} by
    ext field
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]]
  exact ((hmem.inter hdepth).inter hsurvive).inter hpath

theorem firstNSelectedPopulation_depth (m N n : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (p : RootIndexed.TreeNode (Fin m) ℕ)
    (hp : p ∈ firstNSelectedPopulation m N n field) :
    p.2.length = n :=
  by
    classical
    change p ∈ RootIndexed.selectedPopulationTotalized N
      (Finset.univ : Finset (Fin m)) (fun _ : Fin m => (0 : ℝ)) id id n field
      at hp
    exact RootIndexed.selectedPopulationTotalized_depth N Finset.univ
      (fun _ : Fin m => (0 : ℝ)) id id n field p hp

/-- First-`N` selection never introduces a particle whose ancestral path
contains an absent child. The induction follows the actual parent/child
presentation of `Combinatorics.Branching.Population.childrenAtGeneration`; the empty-offspring case contributes
no selected address. -/
theorem firstNSelectedPopulation_surviveAlong (m N n : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (p : RootIndexed.TreeNode (Fin m) ℕ)
    (hp : p ∈ firstNSelectedPopulation m N n field) :
    surviveAlong (field p.1) [] p.2 := by
  classical
  induction n generalizing p with
  | zero =>
      simp only [firstNSelectedPopulation, RootIndexed.selectedPopulationTotalized]
        at hp
      rw [RootIndexed.initialPopulation, Finset.mem_map] at hp
      obtain ⟨r, _, rfl⟩ := hp
      exact surviveAlong_nil _ []
  | succ n ih =>
      change p ∈ RootIndexed.selectedPopulationTotalized N
        (Finset.univ : Finset (Fin m)) (fun _ : Fin m => (0 : ℝ)) id id
        (n + 1) field at hp
      have hchild := RootIndexed.selectedPopulationTotalized_succ_subset
        N (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) id id n field hp
      obtain ⟨q, hq, hqdepth, i, hi, rfl⟩ :=
        (Combinatorics.Branching.Population.mem_childrenAtGeneration_iff n
          (firstNSelectedPopulation m N n field) field p).mp hchild
      exact (surviveAlong_append_singleton (field q.1) [] q.2 i).2
        ⟨ih q hq, hi⟩

/-- Every prefix of a selected address is selected at its own generation.
This is the ancestor-closure property needed to branch the first-`N`
population at the start of a witnessed drawdown. -/
theorem firstNSelectedPopulation_prefix_mem (m N n : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (p : RootIndexed.TreeNode (Fin m) ℕ)
    (hp : p ∈ firstNSelectedPopulation m N n field)
    (j : ℕ) (hjn : j ≤ n) :
    (p.1, p.2.take j) ∈ firstNSelectedPopulation m N j field := by
  classical
  induction n generalizing p j with
  | zero =>
      have hj : j = 0 := by omega
      subst j
      change p ∈ RootIndexed.initialPopulation (Finset.univ : Finset (Fin m)) at hp
      change (p.1, p.2.take 0) ∈
        RootIndexed.initialPopulation (Finset.univ : Finset (Fin m))
      rw [RootIndexed.mem_initialPopulation_iff] at hp ⊢
      obtain ⟨r, hr, hpEq⟩ := hp
      subst p
      simp
  | succ n ih =>
      by_cases htop : j = n + 1
      · subst j
        have hdepth : p.2.length = n + 1 := by
          change p ∈ RootIndexed.selectedPopulationTotalized N Finset.univ
            (fun _ : Fin m => (0 : ℝ)) id id (n + 1) field at hp
          exact RootIndexed.selectedPopulationTotalized_depth N Finset.univ
            (fun _ : Fin m => (0 : ℝ)) id id (n + 1) field p hp
        have htake : p.2.take (n + 1) = p.2 :=
          (List.take_eq_self_iff p.2).2 (by omega)
        simpa [firstNSelectedPopulation, htake] using hp
      · have hjn' : j ≤ n := by omega
        have hchild :
            p ∈ Combinatorics.Branching.Population.childrenAtGeneration n
              (firstNSelectedPopulation m N n field) field := by
          change p ∈ RootIndexed.selectedPopulationTotalized N Finset.univ
            (fun _ : Fin m => (0 : ℝ)) id id (n + 1) field at hp
          exact RootIndexed.selectedPopulationTotalized_succ_subset
            N Finset.univ (fun _ : Fin m => (0 : ℝ)) id id n field hp
        obtain ⟨q, hq, hqdepth, i, hi, rfl⟩ :=
          (Combinatorics.Branching.Population.mem_childrenAtGeneration_iff n
            (firstNSelectedPopulation m N n field) field p).mp hchild
        have htake : (q.2 ++ [i]).take j = q.2.take j :=
          List.take_append_of_le_length (by simpa [hqdepth] using hjn')
        simpa [htake] using ih q hq j hjn'

/-- The no-large-drawdown event for a retained endpoint is contained in the
union of the corresponding one-root events in the full pre-sampled forest.
This containment is pathwise and does not use a branching-property
assumption or a nonempty-offspring premise. -/
theorem firstNSelectedNoLargeDropEndpointBelow_subset_roots
    (m N n : ℕ) [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (delta threshold : ℝ) :
    firstNSelectedNoLargeDropEndpointBelow m N n delta threshold ⊆
      ⋃ r : Fin m,
        {field : FiniteRootStepField m ℕ ℝ |
          field r ∈ hasNoLargeDropEndpointBelow realPotential n delta threshold} := by
  intro field hfield
  obtain ⟨p, hp, hdepth, hsurvive, hpath⟩ := hfield
  refine Set.mem_iUnion.2 ⟨p.1, ?_⟩
  change field p.1 ∈ hasNoLargeDropEndpointBelow realPotential n delta threshold
  exact ⟨p.2, hdepth, hsurvive, hpath⟩

/-- Fixed-generation selected-population transfer of the endpoint/no-large-
drawdown event.  The proof is full-branching containment followed by a union
bound over the `m` initial roots and the existing one-root many-to-one
estimate.  This closes only the second (no-large-drawdown) term in the proof
of Aïdékon--Hu (4.16); it does not estimate the large-drawdown event. -/
theorem measure_firstNSelectedNoLargeDropEndpointBelow_le
    (m N n : ℕ) [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (delta threshold : ℝ)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ) :
    (finiteRootStepFieldLaw μ m)
        (firstNSelectedNoLargeDropEndpointBelow m N n delta threshold) ≤
      (m : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp threshold) *
          (tiltedIncrementFieldLaw realPotential μ)
            (spineNoLargeDropEndpointBelowEvent n delta threshold)) := by
  let E : Set (FiniteRootStepField m ℕ ℝ) :=
    firstNSelectedNoLargeDropEndpointBelow m N n delta threshold
  let A : Set (StepField ℕ ℝ) :=
    hasNoLargeDropEndpointBelow realPotential n delta threshold
  have hsubset : E ⊆ ⋃ r : Fin m, {field : FiniteRootStepField m ℕ ℝ |
      field r ∈ A} := by
    exact firstNSelectedNoLargeDropEndpointBelow_subset_roots m N n delta threshold
  have hroot (r : Fin m) :
      (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ ℝ | field r ∈ A} =
        (offspringFieldLaw μ) A := by
    change (finiteRootStepFieldLaw μ m)
      ((fun field : FiniteRootStepField m ℕ ℝ => field r) ⁻¹' A) = _
    rw [← Measure.map_apply (measurable_pi_apply r)
      (measurableSet_hasNoLargeDropEndpointBelow realPotential n delta threshold)]
    rw [finiteRootStepFieldLaw_root_marginal μ r]
  have honeRoot :=
    measure_hasNoLargeDropEndpointBelow_le_exp_mul_spineProbability
      realPotential μ hboundary n delta threshold
  calc
    (finiteRootStepFieldLaw μ m) E ≤
        (finiteRootStepFieldLaw μ m)
          (⋃ r : Fin m, {field : FiniteRootStepField m ℕ ℝ | field r ∈ A}) :=
      measure_mono hsubset
    _ ≤ ∑ r : Fin m,
          (finiteRootStepFieldLaw μ m)
            {field : FiniteRootStepField m ℕ ℝ | field r ∈ A} :=
      measure_iUnion_fintype_le (finiteRootStepFieldLaw μ m) _
    _ ≤ ∑ _r : Fin m,
          ENNReal.ofReal (Real.exp threshold) *
            (tiltedIncrementFieldLaw realPotential μ)
              (spineNoLargeDropEndpointBelowEvent n delta threshold) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [hroot r]
      exact honeRoot
    _ = (m : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp threshold) *
            (tiltedIncrementFieldLaw realPotential μ)
              (spineNoLargeDropEndpointBelowEvent n delta threshold)) := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

end
