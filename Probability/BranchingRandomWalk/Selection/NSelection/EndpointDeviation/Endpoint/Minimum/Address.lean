/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Minimum.Basic
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Population
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic

/-!
# A measurable address attaining the selected endpoint minimum

At each generation the selected population is finite. We choose the least
address, in the fixed address order, among those attaining its minimum
endpoint. The selector is measurable from the marks revealed by that
generation. Its slot-zero child gives the one-step endpoint comparison.

The public declarations in
`ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail` are:

- `firstNSelectedEndpointMinimizers m N k field`: the finite set
  $\{p\in\operatorname{Pop}_{N,k}: \forall q\in\operatorname{Pop}_{N,k},
  \operatorname{pos}_k(p)\le\operatorname{pos}_k(q)\}$.
- `firstNSelectedEndpointMinimizers_nonempty_of_population_nonempty`:
  a nonempty selected population has at least one minimizing address.
- `firstNSelectedEndpointMinAddress m N k hm field`: the least minimizing
  address, with a fixed root/address value on the empty-population branch.
- `firstNSelectedEndpointMinAddress_mem_and_min`: when the population is
  nonempty, the chosen address belongs to it and minimizes its endpoint.
- `firstNSelectedEndpointMinimizers_mem_measurable`: membership of any fixed
  address in the minimizing set is measurable at generation `k`.
- `measurable_firstNSelectedEndpointMinAddress`: the canonical address is
  measurable at generation `k`.

Here `Pop_{N,k}` is the generation-`k` first-`N` selected population and
`pos_k` is its endpoint position.
-/

open MeasureTheory

section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open Combinatorics.UlamHarris

private abbrev endpointAtGeneration (m k : ℕ)
    (field : FiniteRootStepField m ℕ ℝ)
    (p : RootIndexed.TreeNode (Fin m) ℕ) : ℝ :=
  RootIndexed.positionAtGeneration (fun _ : Fin m => (0 : ℝ)) id k
    p.1 p.2 field

/-- Addresses in the generation-`k` selected population that attain its
minimum endpoint. -/
noncomputable def firstNSelectedEndpointMinimizers (m N k : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) :
    Finset (RootIndexed.TreeNode (Fin m) ℕ) := by
  classical
  let population := firstNSelectedPopulation m N k field
  exact population.filter fun p =>
    ∀ q ∈ population, endpointAtGeneration m k field p ≤
      endpointAtGeneration m k field q

theorem firstNSelectedEndpointMinimizers_nonempty_of_population_nonempty
    (m N k : ℕ) [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (hpopulation : (firstNSelectedPopulation m N k field).Nonempty) :
    (firstNSelectedEndpointMinimizers m N k field).Nonempty := by
  classical
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image
    (firstNSelectedPopulation m N k field)
    (endpointAtGeneration m k field) hpopulation
  refine ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩⟩
  intro q hq
  exact hmin q hq

/-- Canonical endpoint-minimizing address, with a fixed root/address fallback
only on the totalized empty-population branch. -/
noncomputable def firstNSelectedEndpointMinAddress (m N k : ℕ)
    (hm : 0 < m) [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) : RootIndexed.TreeNode (Fin m) ℕ := by
  classical
  exact if hpopulation : (firstNSelectedPopulation m N k field).Nonempty then
      (firstNSelectedEndpointMinimizers m N k field).min'
        (firstNSelectedEndpointMinimizers_nonempty_of_population_nonempty
          m N k field hpopulation)
    else
      ((⟨0, hm⟩ : Fin m), [])

theorem firstNSelectedEndpointMinAddress_mem_and_min
    (m N k : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (hpopulation : (firstNSelectedPopulation m N k field).Nonempty) :
    let p := firstNSelectedEndpointMinAddress m N k hm field
    p ∈ firstNSelectedPopulation m N k field ∧
      ∀ q ∈ firstNSelectedPopulation m N k field,
        endpointAtGeneration m k field p ≤ endpointAtGeneration m k field q := by
  classical
  let minimizers := firstNSelectedEndpointMinimizers m N k field
  have hminimizers : minimizers.Nonempty :=
    firstNSelectedEndpointMinimizers_nonempty_of_population_nonempty
      m N k field hpopulation
  have hpmin : firstNSelectedEndpointMinAddress m N k hm field =
      minimizers.min' hminimizers := by
    simp [firstNSelectedEndpointMinAddress, hpopulation, minimizers]
  rw [hpmin]
  have hp := Finset.min'_mem minimizers hminimizers
  rcases Finset.mem_filter.mp hp with ⟨hp, hleast⟩
  exact ⟨hp, hleast⟩

theorem firstNSelectedEndpointMinimizers_mem_measurable
    (m N k : ℕ) [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (p : RootIndexed.TreeNode (Fin m) ℕ) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) k]
      {field : FiniteRootStepField m ℕ ℝ |
        p ∈ firstNSelectedEndpointMinimizers m N k field} := by
  classical
  have hpopulation : Measurable[
      RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) k]
      (firstNSelectedPopulation m N k) := by
    change Measurable[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) k]
      (fun field => RootIndexed.selectedPopulationTotalized N
        (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) id id k field)
    exact RootIndexed.selectedPopulationTotalized_adapted N
      (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) id
      measurable_id id measurable_id k
  have hpopulationMem (q : RootIndexed.TreeNode (Fin m) ℕ) :
      MeasurableSet[RootIndexed.stepFiltration
        (Root := Fin m) (α := ℕ) (X := ℝ) k]
        {field : FiniteRootStepField m ℕ ℝ |
          q ∈ firstNSelectedPopulation m N k field} :=
    hpopulation (measurableSet_mem_finset q)
  have hposition (q : RootIndexed.TreeNode (Fin m) ℕ) :
      Measurable[RootIndexed.stepFiltration
        (Root := Fin m) (α := ℕ) (X := ℝ) k]
        (fun field : FiniteRootStepField m ℕ ℝ =>
          endpointAtGeneration m k field q) := by
    exact RootIndexed.positionAtGeneration_measurable
      (fun _ : Fin m => (0 : ℝ)) id measurable_id k q.1 q.2
  have hminimal (q : RootIndexed.TreeNode (Fin m) ℕ) :
      MeasurableSet[RootIndexed.stepFiltration
        (Root := Fin m) (α := ℕ) (X := ℝ) k]
        {field : FiniteRootStepField m ℕ ℝ |
          ∀ r ∈ firstNSelectedPopulation m N k field,
            endpointAtGeneration m k field q ≤
              endpointAtGeneration m k field r} := by
    rw [show {field : FiniteRootStepField m ℕ ℝ |
        ∀ r ∈ firstNSelectedPopulation m N k field,
          endpointAtGeneration m k field q ≤
            endpointAtGeneration m k field r} =
        ⋂ r : RootIndexed.TreeNode (Fin m) ℕ,
          ({field | r ∉ firstNSelectedPopulation m N k field} ∪
            {field | endpointAtGeneration m k field q ≤
              endpointAtGeneration m k field r}) by
      ext field
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union]
      constructor
      · intro h r
        by_cases hr : r ∈ firstNSelectedPopulation m N k field
        · exact Or.inr (h r hr)
        · exact Or.inl hr
      · intro h r hr
        rcases h r with hnot | hle
        · exact (hnot hr).elim
        · exact hle]
    apply MeasurableSet.iInter
    intro r
    exact (hpopulationMem r).compl.union
      (measurableSet_le (hposition q) (hposition r))
  rw [show {field : FiniteRootStepField m ℕ ℝ |
      p ∈ firstNSelectedEndpointMinimizers m N k field} =
      {field | p ∈ firstNSelectedPopulation m N k field} ∩
        {field | ∀ q ∈ firstNSelectedPopulation m N k field,
          endpointAtGeneration m k field p ≤ endpointAtGeneration m k field q} by
    ext field
    simp [firstNSelectedEndpointMinimizers, Finset.mem_filter]]
  exact (hpopulationMem p).inter (hminimal p)

theorem measurable_firstNSelectedEndpointMinAddress
    (m N k : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    Measurable[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) k]
      (firstNSelectedEndpointMinAddress m N k hm) := by
  classical
  have hpopulation : Measurable[
      RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) k]
      (firstNSelectedPopulation m N k) := by
    change Measurable[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) k]
      (fun field => RootIndexed.selectedPopulationTotalized N
        (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) id id k field)
    exact RootIndexed.selectedPopulationTotalized_adapted N
      (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) id
      measurable_id id measurable_id k
  have hpopulationEmpty : MeasurableSet[
      RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) k]
      {field : FiniteRootStepField m ℕ ℝ |
        (firstNSelectedPopulation m N k field).Nonempty} := by
    rw [show {field : FiniteRootStepField m ℕ ℝ |
        (firstNSelectedPopulation m N k field).Nonempty} =
        {field | firstNSelectedPopulation m N k field ≠ ∅} by
      ext field
      simp [Finset.nonempty_iff_ne_empty]]
    exact (hpopulation (measurableSet_singleton
      (∅ : Finset (RootIndexed.TreeNode (Fin m) ℕ)))).compl
  have hminMem (p : RootIndexed.TreeNode (Fin m) ℕ) :
      MeasurableSet[RootIndexed.stepFiltration
        (Root := Fin m) (α := ℕ) (X := ℝ) k]
        {field : FiniteRootStepField m ℕ ℝ |
          p ∈ firstNSelectedEndpointMinimizers m N k field} :=
    firstNSelectedEndpointMinimizers_mem_measurable m N k p
  let addressLE : LE (RootIndexed.TreeNode (Fin m) ℕ) :=
    (inferInstance : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)).toPartialOrder.toPreorder.toLE
  have hleast (p : RootIndexed.TreeNode (Fin m) ℕ) :
      MeasurableSet[RootIndexed.stepFiltration
        (Root := Fin m) (α := ℕ) (X := ℝ) k]
        {field : FiniteRootStepField m ℕ ℝ |
          ∀ q ∈ firstNSelectedEndpointMinimizers m N k field,
            @LE.le _ addressLE p q} := by
    rw [show {field : FiniteRootStepField m ℕ ℝ |
        ∀ q ∈ firstNSelectedEndpointMinimizers m N k field,
          @LE.le _ addressLE p q} =
        ⋂ q : RootIndexed.TreeNode (Fin m) ℕ,
          ({field | q ∉ firstNSelectedEndpointMinimizers m N k field} ∪
            {field | @LE.le _ addressLE p q}) by
      ext field
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union]
      constructor
      · intro h q
        by_cases hq : q ∈ firstNSelectedEndpointMinimizers m N k field
        · exact Or.inr (h q hq)
        · exact Or.inl hq
      · intro h q hq
        rcases h q with hnot | hle
        · exact (hnot hq).elim
        · exact hle]
    apply MeasurableSet.iInter
    intro q
    have hconstant : MeasurableSet[
        RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) k]
        {field : FiniteRootStepField m ℕ ℝ | @LE.le _ addressLE p q} := by
      by_cases hpq : @LE.le _ addressLE p q <;> simp [hpq]
    exact (hminMem q).compl.union hconstant
  have hfiber (p : RootIndexed.TreeNode (Fin m) ℕ) :
      MeasurableSet[RootIndexed.stepFiltration
        (Root := Fin m) (α := ℕ) (X := ℝ) k]
        {field : FiniteRootStepField m ℕ ℝ |
          firstNSelectedEndpointMinAddress m N k hm field = p} := by
    rw [show {field : FiniteRootStepField m ℕ ℝ |
        firstNSelectedEndpointMinAddress m N k hm field = p} =
        ({field | (firstNSelectedPopulation m N k field).Nonempty} ∩
          {field | p ∈ firstNSelectedEndpointMinimizers m N k field} ∩
          {field | ∀ q ∈ firstNSelectedEndpointMinimizers m N k field,
            @LE.le _ addressLE p q}) ∪
        (if p = ((⟨0, hm⟩ : Fin m), []) then
          {field | ¬ (firstNSelectedPopulation m N k field).Nonempty}
        else ∅) by
      ext field
      by_cases hpop : (firstNSelectedPopulation m N k field).Nonempty
      · have hpopNe : firstNSelectedPopulation m N k field ≠ ∅ :=
          Finset.nonempty_iff_ne_empty.mp hpop
        simp [firstNSelectedEndpointMinAddress, hpop, hpopNe,
          Finset.min'_eq_iff] <;> (intro _; rfl)
      · have hempty : firstNSelectedPopulation m N k field = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hpop
        by_cases hp : p = ((⟨0, hm⟩ : Fin m), [])
        · simp [firstNSelectedEndpointMinAddress, hpop, hp, hempty]
        · have hdefaultNe : ((⟨0, hm⟩ : Fin m), []) ≠ p :=
            fun h => hp h.symm
          simp [firstNSelectedEndpointMinAddress, hpop, hp, hempty,
            hdefaultNe]]
    apply MeasurableSet.union
    · exact (hpopulationEmpty.inter (hminMem p)).inter (hleast p)
    · by_cases hp : p = ((⟨0, hm⟩ : Fin m), [])
      · simp only [hp, ↓reduceIte]
        exact hpopulationEmpty.compl
      · simp only [hp, ↓reduceIte]
        exact @MeasurableSet.empty (FiniteRootStepField m ℕ ℝ)
          (RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) k)
  exact @measurable_to_countable'
    (RootIndexed.TreeNode (Fin m) ℕ) (FiniteRootStepField m ℕ ℝ)
    ‹MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)›
    ‹Countable (RootIndexed.TreeNode (Fin m) ℕ)›
    (RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) k)
    (firstNSelectedEndpointMinAddress m N k hm) hfiber

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

end
