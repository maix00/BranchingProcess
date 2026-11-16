/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.NestedRoots
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Minimum.CountableRoots
import Combinatorics.UlamHarris.Order
import Probability.BranchingRandomWalk.Selection.NSelection.Admissible.Real
set_option linter.style.haveILetI false

/-!
# Endpoint sublevel probabilities for nested root sets

## Public declarations

The declarations in
`ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation` are:

- `RootIndexed.selectedPopulationEndpointBelow`: the event that some particle
  in the generation-`n` first-`N` selected population from `roots` has position
  at most `threshold`:
  `{field | ∃ p, p ∈ RootIndexed.selectedPopulationTotalized N roots initialPosition id id n field ∧ RootIndexed.position initialPosition id field p.1 p.2 ≤ threshold}`.
- `measurableSet_RootIndexed_selectedPopulationEndpointBelow`: this event is
  measurable.
- `RootIndexed.measure_selectedPopulationEndpointBelow_mono_roots`: if
  `subsetBRWRoots ⊆ supersetBRWRoots` and the boundary normalization holds, then the
  root-indexed step-field law satisfies
  $\nu(\operatorname{EndpointBelow}(\text{subsetBRWRoots},n,x))\le
  \nu(\operatorname{EndpointBelow}(\text{supersetBRWRoots},n,x))$.

- `measure_countableRootEndpointMinimum_le_mono_roots`: for $0<m\le k$,
  the minimum from $m$ roots has sublevel probability at most that from $k$
  roots, on the common countable-root field.

The rank-installed coupling shows that adding initial roots can only increase
the probability of finding a selected endpoint below a fixed threshold.  The
two fields in the coupling have the same product-law marginal, so this
pathwise comparison transfers to their endpoint probabilities.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Coupling
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

/-- There is a generation-`n` particle in first-`N` selection from `roots`
whose position is at most `threshold`. -/
def RootIndexed.selectedPopulationEndpointBelow
    {Root α : Type*} [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (n : ℕ) (threshold : ℝ) :
    Set (RootIndexed.StepField Root α ℝ) :=
  {field | ∃ p : RootIndexed.TreeNode Root α,
    p ∈ RootIndexed.selectedPopulationTotalized N roots initialPosition id id n field ∧
      RootIndexed.position initialPosition id field p.1 p.2 ≤ threshold}

theorem measurableSet_RootIndexed_selectedPopulationEndpointBelow
    {Root α : Type*} [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (n : ℕ) (threshold : ℝ) :
    MeasurableSet
      (RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
        N roots initialPosition n threshold) := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode Root α) :=
    fun a b => LinearOrder.toDecidableEq a b
  rw [show RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
      N roots initialPosition n threshold =
      ⋃ p : RootIndexed.TreeNode Root α,
        {field | p ∈ RootIndexed.selectedPopulationTotalized N roots
          initialPosition id id n field ∧
          RootIndexed.position initialPosition id field p.1 p.2 ≤ threshold} by
    ext field
    simp only [RootIndexed.selectedPopulationEndpointBelow,
      Set.mem_ofPred_eq, Set.mem_iUnion]]
  apply MeasurableSet.iUnion
  intro p
  have hpopulation : Measurable
      (RootIndexed.selectedPopulationTotalized (Root := Root) (α := α)
        (Mark := ℝ) (Position := ℝ) (Value := ℝ)
        N roots initialPosition id id n) := by
    exact (RootIndexed.selectedPopulationTotalized_adapted
      (Root := Root) (α := α) (Mark := ℝ) (Position := ℝ) (Value := ℝ)
      N roots initialPosition id measurable_id id measurable_id n).mono
        (Filtration.le
          (RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ)) n)
        le_rfl
  have hmem : MeasurableSet
      {field : RootIndexed.StepField Root α ℝ |
        p ∈ RootIndexed.selectedPopulationTotalized N roots initialPosition id id n field} :=
    hpopulation (measurableSet_mem_finset p)
  have hposition : Measurable
      (fun field : RootIndexed.StepField Root α ℝ =>
        RootIndexed.position initialPosition id field p.1 p.2) := by
    exact (RootIndexed.position_measurable initialPosition id measurable_id p.1 p.2).mono
      (Filtration.le
        (RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ)) p.2.length)
      le_rfl
  have hbelow : MeasurableSet
      {field : RootIndexed.StepField Root α ℝ |
        RootIndexed.position initialPosition id field p.1 p.2 ≤ threshold} :=
    measurableSet_Iic.preimage hposition
  rw [show {field : RootIndexed.StepField Root α ℝ |
      p ∈ RootIndexed.selectedPopulationTotalized N roots initialPosition id id n field ∧
        RootIndexed.position initialPosition id field p.1 p.2 ≤ threshold} =
      {field | p ∈ RootIndexed.selectedPopulationTotalized N roots
        initialPosition id id n field} ∩
      {field | RootIndexed.position initialPosition id field p.1 p.2 ≤ threshold} by
    ext field
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]]
  exact hmem.inter hbelow

/-- Almost surely under the common two-copy field, every selected endpoint
below a threshold from the smaller root set has a selected endpoint below the
same threshold in the rank-installed process from the containing root set. -/
private lemma RootIndexed.selectedPopulationNestedRoots_endpointBelow_ae
    {Root α : Type*} [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (subsetBRWRoots supersetBRWRoots : Finset Root)
    (hroots : subsetBRWRoots ⊆ supersetBRWRoots)
    (initialPosition : Root → ℝ) (n : ℕ) (x : ℝ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      (∃ p : RootIndexed.TreeNode Root α,
        p ∈ RootIndexed.selectedPopulationTotalized N subsetBRWRoots
          initialPosition id id n (RootIndexed.StepField.left field) ∧
        RootIndexed.position initialPosition id (RootIndexed.StepField.left field)
          p.1 p.2 ≤ x) →
      (∃ q : RootIndexed.TreeNode Root α,
        q ∈ RootIndexed.restartedRealPositionNSelectedBRWPopulation N supersetBRWRoots
          initialPosition id
          (fun k field => RootIndexed.selectedPopulationTotalized N subsetBRWRoots
            initialPosition id id k (RootIndexed.StepField.left field)) n field ∧
        RootIndexed.position initialPosition id
          (RootIndexed.restartedRealPositionNSelectedBRWField N supersetBRWRoots
            initialPosition id
            (fun k field => RootIndexed.selectedPopulationTotalized N subsetBRWRoots
              initialPosition id id k (RootIndexed.StepField.left field)) n field)
          q.1 q.2 ≤ x) := by
  have hcoupled := RootIndexed.selectedPopulationNestedRootsCoupledInjection_ae
    μ hnorm N subsetBRWRoots supersetBRWRoots hroots initialPosition n
  filter_upwards [hcoupled] with field hcoupled
  intro hbelow
  rcases hbelow with ⟨p, hp, hpx⟩
  rcases hcoupled with ⟨hmap⟩
  let q := hmap p
  have hq : q ∈ RootIndexed.restartedRealPositionNSelectedBRWPopulation N supersetBRWRoots
      initialPosition id
      (fun k field => RootIndexed.selectedPopulationTotalized N subsetBRWRoots
        initialPosition id id k (RootIndexed.StepField.left field)) n field := by
    exact hmap.mapsTo (by simpa [Combinatorics.Branching.Selection.Coupling.populationCloud]
      using hp)
  have hposition :
      RootIndexed.position initialPosition id
          (RootIndexed.restartedRealPositionNSelectedBRWField N supersetBRWRoots
            initialPosition id
            (fun k field => RootIndexed.selectedPopulationTotalized N subsetBRWRoots
              initialPosition id id k (RootIndexed.StepField.left field)) n field)
          q.1 q.2 ≤
        RootIndexed.position initialPosition id (RootIndexed.StepField.left field)
          p.1 p.2 := by
    have hp' : p ∈
        (Combinatorics.Branching.Selection.Coupling.populationCloud id
          (RootIndexed.BranchingWalk.ofStepField initialPosition
            (RootIndexed.StepField.left field))
          (RootIndexed.selectedPopulationTotalized N subsetBRWRoots
            initialPosition id id n (RootIndexed.StepField.left field))).particles () := by
      simpa [Combinatorics.Branching.Selection.Coupling.populationCloud] using hp
    have hdom := hmap.dominates p hp'
    simpa [Combinatorics.Branching.RootIndexed.BranchingWalk.ofStepField,
      ProbabilityTheory.BranchingRandomWalk.RootIndexed.position,
      ProbabilityTheory.BranchingRandomWalk.RootIndexed.displace] using hdom
  exact ⟨q, hq, hposition.trans hpx⟩

/-- Under boundary normalization, the endpoint-sublevel probability for a
larger finite root set is at least that for a contained root set.  This is the
law-level form of the nested-root rank-installed coupling. -/
theorem RootIndexed.measure_selectedPopulationEndpointBelow_mono_roots
    {Root α : Type*} [Countable Root] [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (subsetBRWRoots supersetBRWRoots : Finset Root)
    (hroots : subsetBRWRoots ⊆ supersetBRWRoots)
    (initialPosition : Root → ℝ) (n : ℕ) (threshold : ℝ) :
    (RootIndexed.stepFieldLaw (Root := Root) μ)
        (RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α) N subsetBRWRoots
          initialPosition n threshold) ≤
      (RootIndexed.stepFieldLaw (Root := Root) μ)
        (RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α) N supersetBRWRoots
          initialPosition n threshold) := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode Root α) :=
    fun a b => LinearOrder.toDecidableEq a b
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  let μRoot := RootIndexed.stepFieldLaw (Root := Root) μ
  let left : RootIndexed.StepField (Root ⊕ Root) α ℝ →
      RootIndexed.StepField Root α ℝ := RootIndexed.StepField.left
  let subsetNSelectedBRWPopulation := RootIndexed.nSelectedBRWPopulationTotalizedCausalPopulation
    (Root := Root) (α := α) (Mark := ℝ) (Position := ℝ) (Value := ℝ)
    N subsetBRWRoots initialPosition id measurable_id id measurable_id
  let subsetNSelectedBRWPopulationFiniteSlices := RootIndexed.nSelectedBRWPopulationTotalizedCausalPopulation_finiteSlices
    (Root := Root) (α := α) (Mark := ℝ) (Position := ℝ) (Value := ℝ)
    N subsetBRWRoots initialPosition id measurable_id id measurable_id
  have hsubsetNSelectedBRWPopulationEq : subsetNSelectedBRWPopulationFiniteSlices.toFinset =
      (fun k field => RootIndexed.selectedPopulationTotalized N subsetBRWRoots
        initialPosition id id k (RootIndexed.StepField.left field)) := by
    funext k
    funext field
    apply Finset.coe_injective
    rw [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
    change (subsetNSelectedBRWPopulation.toPopulation field).particles k = _
    rfl
  let supersetNSelectedBRWField := RootIndexed.restartedRealPositionNSelectedBRWField N supersetBRWRoots
    initialPosition id subsetNSelectedBRWPopulationFiniteSlices.toFinset n
  have hleftMeasurable : Measurable left := by
    change Measurable (RootIndexed.StepField.reindex Sum.inl)
    rw [measurable_pi_iff]
    intro r
    rw [measurable_pi_iff]
    intro u
    exact (measurable_pi_apply u).comp (measurable_pi_apply (Sum.inl r))
  have hleftLaw : P.map left = μRoot := by
    change (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
        (RootIndexed.StepField.reindex Sum.inl) = _
    exact RootIndexed.stepFieldLaw_reindex μ Sum.inl Sum.inl_injective
  have hleftSet : MeasurableSet
      (RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
        N subsetBRWRoots initialPosition
        n threshold) :=
    measurableSet_RootIndexed_selectedPopulationEndpointBelow
      (Root := Root) (α := α) N subsetBRWRoots initialPosition n threshold
  have hsupersetNSelectedBRWEventSet : MeasurableSet
      (RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
        N supersetBRWRoots initialPosition
        n threshold) :=
    measurableSet_RootIndexed_selectedPopulationEndpointBelow
      (Root := Root) (α := α) N supersetBRWRoots initialPosition n threshold
  have hsupersetNSelectedBRWLaw : Measurable supersetNSelectedBRWField ∧ P.map supersetNSelectedBRWField = μRoot := by
    change Measurable
        (RootIndexed.restartedRealPositionNSelectedBRWField N supersetBRWRoots initialPosition id
          subsetNSelectedBRWPopulationFiniteSlices.toFinset n) ∧
      P.map (RootIndexed.restartedRealPositionNSelectedBRWField N supersetBRWRoots
        initialPosition id subsetNSelectedBRWPopulationFiniteSlices.toFinset n) = μRoot
    have hleft : RootIndexed.StepField.left =
        (RootIndexed.StepField.reindex Sum.inl :
          RootIndexed.StepField (Root ⊕ Root) α ℝ → RootIndexed.StepField Root α ℝ) := rfl
    simpa only [P, μRoot, RootIndexed.restartedRealPositionNSelectedBRWField, hleft] using
      (RootIndexed.rankInstalledField_causalPopulation_measurable_law
        μ N supersetBRWRoots initialPosition id measurable_id id measurable_id
        subsetNSelectedBRWPopulation subsetNSelectedBRWPopulationFiniteSlices n)
  have hsubsetNSelectedBRWMarginal : P (left ⁻¹'
      RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
        N subsetBRWRoots initialPosition
        n threshold) =
      μRoot (RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
        N subsetBRWRoots
        initialPosition n threshold) := by
    rw [← hleftLaw, Measure.map_apply hleftMeasurable hleftSet]
  have hsupersetNSelectedBRWMarginal : P (supersetNSelectedBRWField ⁻¹'
      RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
        N supersetBRWRoots initialPosition
        n threshold) =
      μRoot (RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
        N supersetBRWRoots
        initialPosition n threshold) := by
    rw [← hsupersetNSelectedBRWLaw.2, Measure.map_apply hsupersetNSelectedBRWLaw.1 hsupersetNSelectedBRWEventSet]
  have hcoupled := RootIndexed.selectedPopulationNestedRoots_endpointBelow_ae
    μ hboundary N subsetBRWRoots supersetBRWRoots hroots initialPosition n threshold
  have hsubset : ∀ᵐ field ∂P,
      field ∈ left ⁻¹'
          RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α) N subsetBRWRoots
            initialPosition n threshold →
        field ∈ supersetNSelectedBRWField ⁻¹'
          RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α) N supersetBRWRoots
            initialPosition n threshold := by
    filter_upwards [hcoupled] with field hcoupled
    intro hsubsetNSelectedBRWEvent
    have hsubsetNSelectedBRWWitness : ∃ p : RootIndexed.TreeNode Root α,
        p ∈ RootIndexed.selectedPopulationTotalized N subsetBRWRoots
          initialPosition id id n (RootIndexed.StepField.left field) ∧
        RootIndexed.position initialPosition id (RootIndexed.StepField.left field)
          p.1 p.2 ≤ threshold := by
      simpa [left, RootIndexed.selectedPopulationEndpointBelow] using hsubsetNSelectedBRWEvent
    rcases hcoupled hsubsetNSelectedBRWWitness with ⟨q, hq, hqx⟩
    have hsupersetNSelectedBRWEvent : ∃ q : RootIndexed.TreeNode Root α,
        q ∈ RootIndexed.restartedRealPositionNSelectedBRWPopulation N supersetBRWRoots
          initialPosition id
          (fun k field => RootIndexed.selectedPopulationTotalized N subsetBRWRoots
            initialPosition id id k (RootIndexed.StepField.left field)) n field ∧
        RootIndexed.position initialPosition id
          (RootIndexed.restartedRealPositionNSelectedBRWField N supersetBRWRoots
            initialPosition id
            (fun k field => RootIndexed.selectedPopulationTotalized N subsetBRWRoots
              initialPosition id id k (RootIndexed.StepField.left field)) n field)
          q.1 q.2 ≤ threshold := ⟨q, hq, hqx⟩
    simpa [supersetNSelectedBRWField, RootIndexed.restartedRealPositionNSelectedBRWPopulation,
      RootIndexed.restartedRealPositionNSelectedBRWField,
      RootIndexed.selectedPopulationEndpointBelow, hsubsetNSelectedBRWPopulationEq] using hsupersetNSelectedBRWEvent
  have heventMeasureLe : P (left ⁻¹'
      RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
        N subsetBRWRoots initialPosition
        n threshold) ≤
      P (supersetNSelectedBRWField ⁻¹'
        RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
          N supersetBRWRoots initialPosition
          n threshold) := by
    exact measure_mono_ae hsubset
  rw [hsubsetNSelectedBRWMarginal, hsupersetNSelectedBRWMarginal] at heventMeasureLe
  simpa [μRoot] using heventMeasureLe

open scoped ENNReal
open _root_.Combinatorics.Selection.NSelection

noncomputable local instance natAddressOrder : LinearOrder (RootIndexed.TreeNode ℕ ℕ) :=
  RootIndexed.addressLinearOrder ℕ ℕ

noncomputable local instance natAddressDecidableEq : DecidableEq (RootIndexed.TreeNode ℕ ℕ) :=
  fun a b => LinearOrder.toDecidableEq a b

noncomputable local instance finAddressOrder (m : ℕ) :
    LinearOrder (RootIndexed.TreeNode (Fin m) ℕ) :=
  RootIndexed.addressLinearOrder (Fin m) ℕ

private lemma firstNSelectedPopulation_image_first_ae
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hb : HasBoundaryNormalization realPotential μ) (m N : ℕ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := ℕ) μ, ∀ n,
      (firstNSelectedPopulation m N n (RootIndexed.StepField.first m field)).image
          (fun p => ((p.1 : ℕ), p.2)) =
        RootIndexed.selectedPopulationTotalized N (Finset.range m)
          (fun _ : ℕ => (0 : ℝ)) id id n field := by
  classical
  let f : RootIndexed.TreeNode (Fin m) ℕ → RootIndexed.TreeNode ℕ ℕ :=
    fun p => ((p.1 : ℕ), p.2)
  have hf : Function.Injective f := by
    intro p q h
    have hroot := congrArg (fun v : RootIndexed.TreeNode ℕ ℕ => v.1) h
    have hword := congrArg (fun v : RootIndexed.TreeNode ℕ ℕ => v.2) h
    exact Prod.ext (Fin.ext hroot) hword
  have hlt (p q : RootIndexed.TreeNode (Fin m) ℕ) :
      @LT.lt _ (finAddressOrder m).toLT p q ↔ @LT.lt _ natAddressOrder.toLT (f p) (f q) := by
    rw [RootIndexed.addressLinearOrder_lt_iff (Fin m) ℕ,
      RootIndexed.addressLinearOrder_lt_iff ℕ ℕ]
    simp only [f, Fin.val_fin_lt, Fin.val_inj]
  have hfin := RootIndexed.selectedPopulationTotalized_succ_spec_ae μ hb
    N (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ))
  have hfinPull := (RootIndexed.StepField.measurePreserving_first μ m).quasiMeasurePreserving.ae hfin
  have hnat := RootIndexed.selectedPopulationTotalized_succ_spec_ae μ hb
    N (Finset.range m) (fun _ => (0 : ℝ))
  filter_upwards [hfinPull, hnat] with field hfin hnat n
  let small (k : ℕ) := firstNSelectedPopulation m N k (RootIndexed.StepField.first m field)
  let large (k : ℕ) := RootIndexed.selectedPopulationTotalized N (Finset.range m)
    (fun _ : ℕ => (0 : ℝ)) id id k field
  change (small n).image f = large n
  induction n with
  | zero =>
    ext p
    simp only [small, large, firstNSelectedPopulation, RootIndexed.selectedPopulationTotalized,
      Finset.mem_image, RootIndexed.mem_initialPopulation_iff, Finset.mem_range, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨↑r, r.isLt, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨(⟨r, hr⟩, []), ⟨⟨r, hr⟩, rfl⟩, rfl⟩
  | succ n ih =>
    let smallCandidates := Population.childrenAtGeneration n (small n)
      (RootIndexed.StepField.first m field)
    let largeCandidates := Population.childrenAtGeneration n (large n) field
    let smallValue := RootIndexed.observedPositionAtGeneration
      (fun _ : Fin m => (0 : ℝ)) id id (n + 1) (RootIndexed.StepField.first m field)
    let largeValue := RootIndexed.observedPositionAtGeneration
      (fun _ : ℕ => (0 : ℝ)) id id (n + 1) field
    have hcandidates : f '' smallCandidates = largeCandidates := by
      ext q
      change (∃ p ∈ smallCandidates, f p = q) ↔ q ∈ largeCandidates
      simp only [smallCandidates, largeCandidates, Population.mem_childrenAtGeneration_iff, ← ih]
      constructor
      · rintro ⟨_, ⟨p, hp, hd, i, hi, rfl⟩, rfl⟩
        exact ⟨f p, Finset.mem_image_of_mem f hp, hd, i, hi, rfl⟩
      · rintro ⟨parent, hp, hd, i, hi, rfl⟩
        obtain ⟨p, hsmall, heq⟩ := Finset.mem_image.mp hp
        subst parent
        exact ⟨RootIndexed.childAddress p i, ⟨p, hsmall, hd, i, hi, rfl⟩, rfl⟩
    letI : LT (RootIndexed.TreeNode (Fin m) ℕ) := (finAddressOrder m).toLT
    letI : LT (RootIndexed.TreeNode ℕ ℕ) := natAddressOrder.toLT
    have hkey (p q : RootIndexed.TreeNode (Fin m) ℕ) :
        valueKey smallValue p < valueKey smallValue q ↔
          valueKey largeValue (f p) < valueKey largeValue (f q) := by
      have hvalue (p : RootIndexed.TreeNode (Fin m) ℕ) : smallValue p = largeValue (f p) := rfl
      simp only [valueKey, Prod.Lex.toLex_lt_toLex, hvalue, hlt]
    have hs : IsFirstNBy N smallValue smallCandidates (small (n + 1)) := hfin n
    have hl : IsFirstNBy N largeValue largeCandidates (large (n + 1)) := hnat n
    have himage := hs.image N f hf smallValue largeValue hkey smallCandidates (small (n + 1))
    rw [hcandidates] at himage
    exact himage.unique hl

private lemma measure_firstNSelectedEndpointBelow_eq_range
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hb : HasBoundaryNormalization realPotential μ) (m N H : ℕ) (x : ℝ) :
    finiteRootStepFieldLaw μ m (firstNSelectedEndpointBelow m N H x) =
      RootIndexed.stepFieldLaw (Root := ℕ) μ
        (RootIndexed.selectedPopulationEndpointBelow (α := ℕ) N (Finset.range m) (fun _ => 0) H x) := by
  classical
  let P := RootIndexed.stepFieldLaw (Root := ℕ) μ
  let A := firstNSelectedEndpointBelow m N H x
  let B := RootIndexed.selectedPopulationEndpointBelow (α := ℕ) N (Finset.range m) (fun _ => 0) H x
  have hpres := RootIndexed.StepField.measurePreserving_first μ m
  calc
    _ = P (RootIndexed.StepField.first m ⁻¹' A) := by
      rw [← hpres.map_eq, Measure.map_apply hpres.measurable
        (measurableSet_firstNSelectedEndpointBelow m N H x)]
    _ = P B := by
      apply measure_congr
      filter_upwards [firstNSelectedPopulation_image_first_ae μ hb m N] with field himage
      simp only [A, B, Set.mem_preimage, firstNSelectedEndpointBelow,
        RootIndexed.selectedPopulationEndpointBelow, Set.mem_ofPred_eq]
      rw [← himage H]
      constructor
      · rintro ⟨p, hp, hx⟩
        exact ⟨_, Finset.mem_image_of_mem _ hp, hx⟩
      · rintro ⟨p, hp, hx⟩
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
        exact ⟨q, hq, hx⟩

/-- For lexicographically ordered root addresses, increasing the number of
zero-position roots increases the endpoint sublevel probability. This is the
initial-population comparison used in the $a=1$ case of Wang Yiyang's
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 4, Theorem 1.1. -/
theorem measure_countableRootEndpointMinimum_le_mono_roots
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hb : HasBoundaryNormalization realPotential μ) (hne : μ nonemptySupport = 1)
    {m k N : ℕ} (hm : 0 < m) (hmk : m ≤ k) (hN : 0 < N) (H : ℕ) (x : ℝ) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ) μ
    P {field | countableRootEndpointMinimum m N H field ≤ x} ≤
      P {field | countableRootEndpointMinimum k N H field ≤ x} := by
  classical
  let P := RootIndexed.stepFieldLaw (Root := ℕ) μ
  have hlaw (j : ℕ) (hj : 0 < j) :
      P {field | countableRootEndpointMinimum j N H field ≤ x} =
        P (RootIndexed.selectedPopulationEndpointBelow (α := ℕ) N (Finset.range j) (fun _ => 0) H x) := by
    have hmap := congrArg (fun law : Measure ℝ => law (Set.Iic x))
      (countableRootEndpointMinimum_map_eq μ j N H)
    rw [Measure.map_apply (measurable_countableRootEndpointMinimum j N H) measurableSet_Iic,
      Measure.map_apply (measurable_firstNSelectedEndpointMinimum j N H) measurableSet_Iic]
      at hmap
    have hmin := firstNSelectedEndpointMinimum_le_iff_endpointBelow_ae j N H hj hN μ hb hne x
    calc
      _ = finiteRootStepFieldLaw μ j {field | firstNSelectedEndpointMinimum j N H field ≤ x} :=
        hmap
      _ = finiteRootStepFieldLaw μ j (firstNSelectedEndpointBelow j N H x) :=
        measure_congr (hmin.mono fun _ h => h.symm)
      _ = _ := measure_firstNSelectedEndpointBelow_eq_range μ hb j N H x
  change P _ ≤ P _
  rw [hlaw m hm, hlaw k (hm.trans_le hmk)]
  exact RootIndexed.measure_selectedPopulationEndpointBelow_mono_roots
    (α := ℕ) μ hb N _ _ (Finset.range_mono hmk) (fun _ => 0) H x

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
