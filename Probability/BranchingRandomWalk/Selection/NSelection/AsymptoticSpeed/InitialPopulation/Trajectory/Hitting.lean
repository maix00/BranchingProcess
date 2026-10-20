/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingProcess.Offspring.Count
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Minimum.Address
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Roots.Nonempty
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.InitialPopulation.Trajectory.Population
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.InitialPopulation.Trajectory.Lemmas.CapacityHit.Growth
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic
import Combinatorics.BranchingWalk.Step.Basic

/-!
# Hitting the capacity from a smaller initial population

The actual selected population grows through recurrent split opportunities.
Once it reaches size $N$, the trajectory and fresh-field statements are
proved in the sibling modules under `Field/`.

The public declaration is:

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed.finiteRootStepFieldLaw_ae_smallInitialPopulation_hits_capacity`:
  under supercriticality, almost-surely nonempty offspring, and boundary
  normalization, $0<m\le N$ implies the selected population reaches size $N$
  in finite time almost surely.

-/

open MeasureTheory ProbabilityTheory
open Filter
open scoped ENNReal

section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open Combinatorics.UlamHarris
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingProcess.Offspring

attribute [local instance] Classical.propDecidable Classical.decEq

private lemma exists_eq_capacity_of_frequently_growing
    {N : ℕ} (populationSize : ℕ → ℕ) (split : ℕ → Prop)
    (hinitial : 0 < populationSize 0)
    (hcapacity : ∀ n, populationSize n ≤ N)
    (hmonotone : ∀ n, populationSize n ≤ populationSize (n + 1))
    (hgrowth : ∀ n, 0 < populationSize n → populationSize n < N →
      split n → populationSize n < populationSize (n + 1))
    (hfrequently : ∃ᶠ n in atTop, split n) :
    ∃ n, populationSize n = N := by
  have hmono : ∀ {m n}, m ≤ n → populationSize m ≤ populationSize n := by
    intro m n hmn
    induction hmn with
    | refl => exact le_rfl
    | @step n hmn ih =>
        exact le_trans ih (hmonotone n)
  have hpositive : ∀ n, 0 < populationSize n := by
    intro n
    exact lt_of_lt_of_le hinitial (hmono (Nat.zero_le n))
  have hreach : ∀ q, q ≤ N → ∃ n, q ≤ populationSize n := by
    intro q
    induction q with
    | zero =>
        intro _
        exact ⟨0, Nat.zero_le _⟩
    | succ q ih =>
        intro hq
        have hqN : q ≤ N := Nat.le_trans (Nat.le_succ q) hq
        obtain ⟨n, hn⟩ := ih hqN
        by_cases htarget : q + 1 ≤ populationSize n
        · exact ⟨n, htarget⟩
        · have hcurrent : populationSize n = q := by omega
          obtain ⟨m, hsplit, hnm⟩ :=
            (hfrequently.and_eventually (eventually_ge_atTop n)).exists
          have hge : q ≤ populationSize m := by
            exact hn.trans (hmono hnm)
          by_cases htargetAtM : q + 1 ≤ populationSize m
          · exact ⟨m, htargetAtM⟩
          · have hcurrentAtM : populationSize m = q := by omega
            have hqLtN : q < N := by omega
            have hnext := hgrowth m (hpositive m) (by omega) hsplit
            refine ⟨m + 1, ?_⟩
            omega
  obtain ⟨n, hn⟩ := hreach N le_rfl
  exact ⟨n, le_antisymm (hcapacity n) hn⟩

/-- Starting from any nonempty population of size at most N, the actual
root-indexed N-selection population reaches size N in finite time almost
surely. The only offspring assumptions are supercriticality and almost-sure
nonemptiness; boundary normalization is the existing admissibility hypothesis
for the selected process. -/
theorem finiteRootStepFieldLaw_ae_smallInitialPopulation_hits_capacity
    (m N : ℕ) (hm : 0 < m) (hmN : m ≤ N)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (Fin m × TreeNode ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (hsupercritical : (1 : ℝ≥0∞) <
      ∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂μ) :
    ∀ᵐ field ∂finiteRootStepFieldLaw μ m,
      ∃ n, (smallInitialPopulation m N n field).card = N := by
  have hN : 0 < N := lt_of_lt_of_le hm hmN
  have hgoodAE := RootIndexed.selectedPopulationTotalized_succ_spec_ae
    μ hboundary N Finset.univ (fun _ : Fin m => (0 : ℝ))
  have hpopulationAE := Tail.finiteRootStepFieldLaw_firstNSelectedPopulation_nonempty_ae
    m N hm hN μ hboundary hnonempty
  have hmarksAE := finiteRootStepFieldLaw_ae_all_of_measure_one
    nonemptySupport_measurable μ hnonempty m
  have hsplitAE := ae_frequently_smallInitialActiveSplitEvent
    m N hm μ hsupercritical
  filter_upwards [hgoodAE, hpopulationAE, hmarksAE, hsplitAE]
    with field hgood hpopulation hmarks hsplit
  let populationSize : ℕ → ℕ := fun n =>
    (smallInitialPopulation m N n field).card
  let split : ℕ → Prop := fun n =>
    field ∈ smallInitialActiveSplitEvent m N n hm
  have hinitial : 0 < populationSize 0 := by
    simp [populationSize, smallInitialPopulation,
      RootIndexed.selectedPopulationTotalized,
      RootIndexed.initialPopulation_card]
    exact hm
  have hcapacity : ∀ n, populationSize n ≤ N := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [populationSize, smallInitialPopulation,
        RootIndexed.selectedPopulationTotalized,
        RootIndexed.initialPopulation_card]
      exact hmN
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hfirst := hgood k
      change IsFirstNBy N
        (RootIndexed.observedPositionAtGeneration
          (fun _ : Fin m => (0 : ℝ)) id id (k + 1) field)
        (RootIndexed.childrenAtGeneration k
          (smallInitialPopulation m N k field) field)
        (smallInitialPopulation m N (k + 1) field) at hfirst
      simpa [populationSize, smallInitialPopulation] using hfirst.card_le
  have hmonotone : ∀ n, populationSize n ≤ populationSize (n + 1) := by
    intro n
    let parents := smallInitialPopulation m N n field
    let selected := smallInitialPopulation m N (n + 1) field
    let value := RootIndexed.observedPositionAtGeneration
      (fun _ : Fin m => (0 : ℝ)) id id (n + 1) field
    have hfirst : IsFirstNBy N value
        (RootIndexed.childrenAtGeneration n parents field) selected := by
      simpa [parents, selected, value, smallInitialPopulation] using hgood n
    have hdepth : ∀ p ∈ parents, p.2.length = n := by
      intro p hp
      exact Tail.firstNSelectedPopulation_depth m N n field p
        (by simpa [parents, smallInitialPopulation,
          Tail.firstNSelectedPopulation] using hp)
    have hchildren : ∀ p ∈ parents,
        ∃ i : ℕ, survive (field p.1 p.2) i := by
      intro p hp
      exact hmarks p.1 p.2
    have hparentsCapacity : parents.card ≤ N := by
      simpa [parents, populationSize] using hcapacity n
    have hle := smallInitialFirstN_card_ge N n parents field value selected
      hfirst hdepth hchildren hparentsCapacity
    simpa [parents, selected, populationSize] using hle
  have hgrowth : ∀ n, 0 < populationSize n → populationSize n < N →
      split n → populationSize n < populationSize (n + 1) := by
    intro n hpositive hsmall hsplitn
    let parents := smallInitialPopulation m N n field
    let selected := smallInitialPopulation m N (n + 1) field
    let value := RootIndexed.observedPositionAtGeneration
      (fun _ : Fin m => (0 : ℝ)) id id (n + 1) field
    have hfirst : IsFirstNBy N value
        (RootIndexed.childrenAtGeneration n parents field) selected := by
      simpa [parents, selected, value, smallInitialPopulation] using hgood n
    have hdepth : ∀ p ∈ parents, p.2.length = n := by
      intro p hp
      exact Tail.firstNSelectedPopulation_depth m N n field p
        (by simpa [parents, smallInitialPopulation,
          Tail.firstNSelectedPopulation] using hp)
    have hchildren : ∀ p ∈ parents,
        ∃ i : ℕ, survive (field p.1 p.2) i := by
      intro p hp
      exact hmarks p.1 p.2
    have hchosen : smallInitialActiveAddress m N n hm field ∈ parents := by
      have hnonempty := hpopulation n
      have hnonempty' : (Tail.firstNSelectedPopulation m N n field).Nonempty := by
        simpa [Tail.firstNSelectedPopulation] using hnonempty
      have hmem : smallInitialActiveAddress m N n hm field ∈
          Tail.firstNSelectedPopulation m N n field := by
        dsimp [smallInitialActiveAddress]
        rw [ite_eq_left hnonempty']
        exact (Tail.firstNSelectedEndpointMinAddress_mem_and_min m N n hm field
          hnonempty').1
      simpa [parents, smallInitialPopulation,
        Tail.firstNSelectedPopulation] using hmem
    have hsplit' : 2 ≤ Step.childCount
        (field (smallInitialActiveAddress m N n hm field).1
          (smallInitialActiveAddress m N n hm field).2) := by
      change field ∈ smallInitialActiveSplitEvent m N n hm at hsplitn
      simpa [smallInitialActiveSplitEvent, smallInitialActiveMark,
        offspringSplitSet] using hsplitn
    have hparentsSmall : parents.card < N := by
      simpa [parents, populationSize] using hsmall
    have hlt := smallInitialFirstN_card_gt_of_split N n hm parents field
      value selected hfirst hdepth hchildren hchosen hsplit' hparentsSmall
    simpa [parents, selected, populationSize] using hlt
  have hfrequently : ∃ᶠ n in atTop, split n := by
    simpa [split] using hsplit
  obtain ⟨n, hn⟩ := exists_eq_capacity_of_frequently_growing
    populationSize split hinitial hcapacity hmonotone hgrowth hfrequently
  exact ⟨n, hn⟩


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
