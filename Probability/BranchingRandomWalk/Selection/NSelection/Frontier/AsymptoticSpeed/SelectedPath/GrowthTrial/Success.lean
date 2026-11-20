/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.FiniteSlot.Growth
public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.FiniteSlot.GaltonWatson
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.FiniteSlot.NormalizedGrowth
public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Causal
public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Basic
public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Roots
public import Probability.BranchingProcess.Offspring.Count
public import Probability.BranchingProcess.Offspring.FieldLaw
/-!
# Successful growth trials

This module combines the finite-slot population bound with the observable
growth-trial candidate construction. The first theorem gives a uniform positive
probability for a selected growth-trial population to complete a logarithmic growth
trial. The second transfers almost-sure nonemptiness of selected marks to the
observable success event for each enabled growth-trial candidate.

## Public declarations

* `exists_success_probability_lower_bound`: for a sufficiently large cutoff
  $M$, the binary growth selector has mean $\rho>1$ and the path selector has
  positive split probability. At durations $d_n\to\infty$ with
  $\rho x_n\le\rho^{d_n}$ eventually and
  $K_n^{-1}\sum_{j=0}^{d_n}\rho^j\to0$, a trial with target
  $\lceil x_n\rceil$ and capacity $K_n$ has probability at least $p_1>0$
  eventually.
* `growthTrialSuccess_eq_of_binary_horizon_le`: if $q>0$ and $2^d\le K$,
  the trials at capacities $K$ and $2^d$ have the same success event.
* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.successEvent_of_binary_horizon_ae` states that
  an enabled split candidate satisfies the full trial event almost surely when
  its horizon obeys `2 ^ duration ≤ upper` and every selected mark is almost
  surely nonempty.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial

open ProbabilityTheory.BranchingRandomWalk.Step.Selection
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial
open ProbabilityTheory.BranchingRandomWalk.Selection.Stepwise.SplitTime
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.FiniteSlot

open Combinatorics.Branching Combinatorics.UlamHarris
open Combinatorics.Branching.Step.FiniteSelection
open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)
open ProbabilityTheory.BranchingProcess.GaltonWatson

/-- The growth trial of Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (Fudan University, 2026), Chapter 4,
Theorem 1.1 for $a=0$. A finite cutoff on both selected displacements
gives a supercritical binary selector and a uniform success probability. -/
theorem exists_success_probability_lower_bound
    {ι α X : Type*} [MeasurableSpace X] [Countable ι]
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw]
    (hnonempty : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.HasAtLeastOneChild
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ :
        ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι X))
    (hsupercritical : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ :
        ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι X)) :
    let μ := L.sortedPotentialImage
    ∃ M : ℕ,
      let B := Step.FiniteSelection.firstNBySlotOrder (α := α) (X := ℝ) 2
      let S := B.belowPotential realPotential (M : ℝ)
      let hS := B.belowPotential_measurable firstTwoBySlotOrder_measurable realPotential (M : ℝ)
      let law := Selection.Stepwise.binaryOffspringLaw ⟨μ, inferInstance⟩ S hS
      let ρ := finiteSlotOffspringMeanReal law
      1 < ρ ∧ 0 < μ (splitBy (firstOrBelowPotential B realPotential (M : ℝ))) ∧
        ∃ p₁ : ℝ, 0 < p₁ ∧ ∀ (duration capacity : ℕ → ℕ) (target : ℕ → ℝ),
          Tendsto duration atTop atTop →
          (∀ᶠ n in atTop, 0 < capacity n ∧ 0 < target n ∧ ρ * target n ≤ ρ ^ duration n) →
          Tendsto (fun n => (∑ j ∈ Finset.range (duration n + 1), ρ ^ j) / (capacity n : ℝ))
            atTop (𝓝 0) →
          ∀ᶠ n in atTop, p₁ ≤ (offspringFieldLaw μ).real
            {ω | growthTrialSuccess S ⌈target n⌉₊ (capacity n) (duration n) ω} := by
  intro μ
  let B := Step.FiniteSelection.firstNBySlotOrder (α := α) (X := ℝ) 2
  let rawB := Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2
  let ν : ProbabilityMeasure (Step α ℝ) := ⟨μ, inferInstance⟩
  have hB : Measurable B.select := firstTwoBySlotOrder_measurable
  have hBcap : B.IsBoundedBy 2 := firstNBySlotOrder_isBoundedBy 2
  obtain ⟨M₀, hsplit, _⟩ := exists_nat_cutoff_positive_firstOrBelowPotentialSplit L hsupercritical
  have hrawSplit : 0 < L.sorted {ξ | 2 ≤ (rawB ξ).card} := by
    apply hsplit.trans_le
    exact measure_mono fun ξ hξ => hξ.trans
      (Finset.card_le_card (firstOrBelowPotential_subset rawB L.potential (M₀ : ℝ) ξ))
  have hbeq (ξ : Step α X) : B (ξ.map L.potential) = rawB ξ := by
    have hb := firstNBySlotOrder_spec 2 (ξ.map L.potential)
    rw [Step.support_map] at hb
    exact hb.unique (firstNBySlotOrder_spec 2 ξ)
  have hBsplit : 0 < (ν : Measure _) {ξ | 2 ≤ (B ξ).card} := by
    change 0 < L.sortedPotentialImage (splitBy B)
    rw [StepLaw.sortedPotentialImage, Measure.map_apply
      (Step.map_measurable L.potential.measurable_toFun) (splitBy_measurable B hB)]
    simpa only [splitBy, Set.preimage_ofPred_eq, hbeq] using hrawSplit
  let ν₀ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw α ℝ :=
    ⟨μ, inferInstance⟩
  have hμ : ν₀.HasAtLeastOneChild := by
    change L.sortedPotentialImage nonemptySupport = 1
    rw [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport]
    exact hnonempty
  have hBne : ∀ᵐ ξ ∂(ν : Measure _), (B ξ).Nonempty := by
    filter_upwards [ν₀.hasAtLeastOneChild_ae hμ] with ξ hξ
    exact firstNBySlotOrder_nonempty_of_support_nonempty (N := 2) (by norm_num) ξ hξ
  have hmean := finiteSlotOffspringMeanReal_gt_one_of_nonempty_and_split
    ν B hB hBcap hBne hBsplit
  obtain ⟨M, hM⟩ := exists_nat_cutoff_binaryOffspringMean_gt_one ν B hB hBcap realPotential hmean
  let S := B.belowPotential realPotential (M : ℝ)
  have hS : Measurable S.select := B.belowPotential_measurable hB realPotential (M : ℝ)
  have hScap : S.IsBoundedBy 2 := by
    intro ξ
    apply (Finset.card_le_card ?_).trans (hBcap ξ)
    intro i hi
    exact ((Step.FiniteSelection.mem_filter B _ ξ i).mp hi).1
  have hsplitS := measure_selects_two_pos_of_binaryOffspringMean_gt_one ν S hS hScap hM
  have hsplitR : 0 < μ (splitBy (firstOrBelowPotential B realPotential (M : ℝ))) := by
    apply hsplitS.trans_le
    apply measure_mono
    intro ξ hξ
    change 2 ≤ (S ξ).card at hξ
    change 2 ≤ (firstOrBelowPotential B realPotential (M : ℝ) ξ).card
    exact hξ.trans (Finset.card_le_card fun i hi =>
      @Finset.mem_union_right α (Classical.decEq α) _ i _ hi)
  obtain ⟨p, hp, hsuccess⟩ :=
    exists_eventually_measure_growthTrialSuccess_ge μ S hS hScap hM
  exact ⟨M, hM, hsplitR, p / 2, by positivity, hsuccess⟩

/-- The binary cap used for parallel trials has the same success event as
any larger single-trial cap at this duration. -/
theorem growthTrialSuccess_eq_of_binary_horizon_le
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (hcap : S.IsBoundedBy 2)
    (q d K : ℕ) (hq : 0 < q) (hK : 2 ^ d ≤ K) :
    {ω | growthTrialSuccess S q (2 ^ d) d ω} =
      {ω | growthTrialSuccess S q K d ω} := by
  ext ω
  exact ⟨fun h => growthTrialSuccess_of_positive_terminal_population S hcap ω q d K
      hq hK h.1,
    fun h => growthTrialSuccess_of_positive_terminal_population S hcap ω q d (2 ^ d)
      hq le_rfl h.1⟩

/-- A growth-trial candidate's growth trial is successful whenever its observable
split is enabled, almost surely, if its binary horizon fits under the cap.
All coordinates belong to the same pre-sampled field; the proof does not
resample a trial after inspecting another trial's outcome. -/
theorem successEvent_of_binary_horizon_ae
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α] [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select)
    (hnonempty : ∀ᵐ ξ ∂μ, (growth ξ).Nonempty)
    (hcapacity : ∀ ξ, (growth ξ).card ≤ 2)
    (upper duration : ℕ) (hupper : 2 ^ duration ≤ upper)
    (r : Root) (k : ℕ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.isAlive R r k field ∧
        ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.splitEvent R r k field) →
      field ∈ ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.successEvent R growth hR
        1 upper duration r k := by
  classical
  let split : Set (Step α X) := {ξ | (growth ξ).Nonempty}
  have hsplit : MeasurableSet split := by
    change MeasurableSet {ξ | (growth ξ).Nonempty}
    have hcard : Measurable (fun ξ : Step α X => (growth ξ).card) :=
      (measurable_of_countable fun s : Finset α => s.card).comp hgrowth
    have heq : {ξ | (growth ξ).Nonempty} =
        {ξ | 0 < (growth ξ).card} := by
      ext ξ
      simp
    rw [heq]
    exact hcard measurableSet_Ioi
  have hsplitOne : μ split = 1 := by
    have hset : split =ᵐ[μ] Set.univ := by
      filter_upwards [hnonempty] with ξ hξ
      simp [split, hξ]
    exact (measure_congr hset).trans (measure_univ)
  have hall : ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      ∀ u : TreeNode α, (growth (field r u)).Nonempty := by
    apply ae_all_iff.2
    intro u
    have heval : Measurable
        (fun field : RootIndexed.StepField Root α X => field r u) :=
      (measurable_pi_apply u).comp (measurable_pi_apply r)
    apply (ae_mem_iff_measure_eq (heval hsplit).nullMeasurableSet).2
    rw [← Measure.map_apply heval hsplit,
      RootIndexed.stepFieldLaw_coordinate_marginal μ r u, hsplitOne]
    simp
  filter_upwards [hall] with field hmarks
  intro hsplitCandidate
  rcases hsplitCandidate with ⟨halive, hsplitCandidate⟩
  change ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.isAlive R r k field ∧
    ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.splitEvent R r k field ∧
    growthTrialSuccess growth 1 upper duration
      (fun v => field r
        ((ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.growthTrialRootAt (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.lineages R hR)
          R r PUnit.unit (k + 1) field).2 ++ v))
  refine ⟨halive, hsplitCandidate, ?_⟩
  refine growthTrialSuccess_of_population_ge_lower
    growth hcapacity
    (fun v => field r
      ((ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.growthTrialRootAt (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.lineages R hR)
        R r PUnit.unit (k + 1) field).2 ++ v))
    (fun v => hmarks ((ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.growthTrialRootAt (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.lineages R hR)
      R r PUnit.unit (k + 1) field).2 ++ v))
    1 duration upper hupper ?_
  let trial : Mark α (Step α X) := fun v => field r
    ((ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.growthTrialRootAt (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.lineages R hR)
      R r PUnit.unit (k + 1) field).2 ++ v)
  have hpop : (Selection.Stepwise.population growth duration trial).Nonempty :=
    Selection.Stepwise.population_nonempty_of_all_selected_marks_nonempty growth trial
      (fun v => hmarks ((ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.growthTrialRootAt (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.lineages R hR)
        R r PUnit.unit (k + 1) field).2 ++ v)) duration
  exact Finset.card_pos.mpr hpop
end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial

end
