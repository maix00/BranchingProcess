/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Restart.FirstSplit.BranchingProperty
import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.SelectedSubtree
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Finite first-split completion: proof lemmas

These declarations support the geometric no-split estimate used by the public
completion theorem. The prefix event, its measurable representative, and the
population nonemptiness argument are specific to that proof.

## Internal proof declarations

* `selectedPopulationNoSplitPrefix` defines the event that the selected
  population has fewer than two particles through the first `n` generations.
* `selectedPopulationDepthRepresentative` chooses a depth-`n` address from the
  generation, with a deterministic fallback when the generation is empty.
* `selectedPopulationDepthRepresentative_mem`,
  `selectedPopulationDepthRepresentative_length`, and
  `selectedPopulationDepthRepresentative_measurable` state its membership,
  depth, and generation-filtration measurability properties.
* `selectedPopulationNoSplitPrefix_measurable` proves measurability of the
  no-split prefix event.

Writing $Z_j$ for the selected population at generation $j$, the event and
its representative satisfy
\[
 E_n=\{\omega:\ |Z_j(\omega)|<2\text{ for }1\le j\le n\},
 \qquad |p_n(\omega)|=n\quad\text{for every }\omega,
\]
and $p_n$ is measurable in the generation-$n$ domain flow.

-/

open MeasureTheory ProbabilityTheory
open Filter Topology
open scoped ENNReal

section

namespace ProbabilityTheory.BranchingRandomWalk

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory

variable {α X : Type*}

/-- No selected split is visible among the first `n` generated populations. -/
def selectedPopulationNoSplitPrefix (R : Step.FiniteSelection α X) (n : ℕ) :
    Set (Mark α (Step α X)) :=
  {ω | ∀ k < n, (StepSelection.population R (k + 1) ω).card < 2}

/-- A total depth-`n` representative of the selected population.  The dummy
address is used only when that population is empty; it still has depth `n`,
which makes the selected-subtree factorization applicable on the whole sample
space. -/
noncomputable def selectedPopulationDepthRepresentative
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (n : ℕ) :
    Mark α (Step α X) → TreeNode α := fun ω => by
  classical
  let p := StepSelection.population R n ω
  exact if h : p.Nonempty then p.toList.head h.toList_ne_nil
    else List.replicate n ⊥

lemma selectedPopulationDepthRepresentative_mem
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (n : ℕ) (ω : Mark α (Step α X))
    (hne : (StepSelection.population R n ω).Nonempty) :
    selectedPopulationDepthRepresentative R n ω ∈
      StepSelection.population R n ω := by
  classical
  simp only [selectedPopulationDepthRepresentative, dite_eq_left hne]
  exact Finset.mem_toList.mp (List.head_mem hne.toList_ne_nil)

lemma selectedPopulationDepthRepresentative_length
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (n : ℕ) (ω : Mark α (Step α X)) :
    (selectedPopulationDepthRepresentative R n ω).length = n := by
  classical
  by_cases hne : (StepSelection.population R n ω).Nonempty
  · have hmem := selectedPopulationDepthRepresentative_mem R n ω hne
    exact StepSelection.population_depth R ω n _ hmem
  · simp [selectedPopulationDepthRepresentative, hne]

lemma selectedPopulationDepthRepresentative_measurable
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace X] [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select) (n : ℕ) :
    Measurable[generationFiltration (M := Step α X) n]
      (selectedPopulationDepthRepresentative R n) := by
  classical
  let f : Finset (TreeNode α) → TreeNode α := fun p =>
    if h : p.Nonempty then p.toList.head h.toList_ne_nil else List.replicate n ⊥
  have hf : Measurable f := measurable_of_countable f
  have hEq : selectedPopulationDepthRepresentative R n =
      f ∘ StepSelection.population R n := by
    funext ω
    rfl
  rw [hEq]
  exact hf.comp (StepSelection.population_adapted R hR n)

lemma selectedPopulationNoSplitPrefix_measurable
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select) (n : ℕ) :
    MeasurableSet[generationFiltration (M := Step α X) n]
      (selectedPopulationNoSplitPrefix R n) := by
  classical
  rw [show selectedPopulationNoSplitPrefix R n =
      ⋂ k : ℕ, if k < n then
        {ω | (StepSelection.population R (k + 1) ω).card < 2}
      else Set.univ by
        ext ω
        simp [selectedPopulationNoSplitPrefix, Set.mem_iInter]]
  apply MeasurableSet.iInter
  intro k
  by_cases hk : k < n
  · have hcard : Measurable[generationFiltration (M := Step α X) (k + 1)]
        (fun ω => (StepSelection.population R (k + 1) ω).card) :=
      (measurable_of_countable fun s : Finset (TreeNode α) => s.card).comp
        (StepSelection.population_adapted R hR (k + 1))
    have hset : MeasurableSet[generationFiltration (M := Step α X) (k + 1)]
        {ω | (StepSelection.population R (k + 1) ω).card < 2} :=
      hcard measurableSet_Iio
    have hle : k + 1 ≤ n := Nat.succ_le_iff.mpr hk
    simpa [hk] using (generationFiltration (M := Step α X)).mono hle _ hset
  · simp [hk]

set_option linter.style.haveILetI false in
private lemma selectedChildren_card_eq
    [LinearOrder α]
    (R : Step.FiniteSelection α X) (ω : Mark α (Step α X)) (p : TreeNode α) :
    (StepSelection.children R ω p).card = (R (ω p)).card := by
  classical
  letI : DecidableEq α := Classical.decEq α
  rw [StepSelection.children]
  exact Finset.card_image_of_injective (R (ω p)) (fun i j hij => by
    have hsingleton : [i] = [j] := List.append_cancel_left hij
    simpa using hsingleton)

private lemma selectedPopulationNoSplitPrefix_succ_iff
    [DecidableEq α] [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (n : ℕ) (ω : Mark α (Step α X))
    (hnonempty : ∀ k, (StepSelection.population R k ω).Nonempty) :
    ω ∈ selectedPopulationNoSplitPrefix R (n + 1) ↔
    ω ∈ selectedPopulationNoSplitPrefix R n ∧
      selectedSubtreeStepField (selectedPopulationDepthRepresentative R n) ω ∈
          {η : Mark α (Step α X) |
            (R (η [])).card < 2} := by
  constructor
  · intro h
    have hprev : ω ∈ selectedPopulationNoSplitPrefix R n := by
      intro k hk
      exact h k (by omega)
    refine ⟨hprev, ?_⟩
    have hnext := h n (Nat.lt_succ_self n)
    change (StepSelection.population R (n + 1) ω).card < 2 at hnext
    have hpCard : (StepSelection.population R n ω).card = 1 := by
      by_cases hn : n = 0
      · subst n
        simp
      · have hlt := hprev (n - 1) (by omega)
        have hlt' : (StepSelection.population R n ω).card < 2 := by
          simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] using hlt
        have hpos : 0 < (StepSelection.population R n ω).card :=
          Finset.card_pos.mpr (hnonempty n)
        omega
    let p := selectedPopulationDepthRepresentative R n ω
    have hpMem : p ∈ StepSelection.population R n ω :=
      selectedPopulationDepthRepresentative_mem R n ω (hnonempty n)
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp (by simpa [p] using hpCard)
    have hpq : p = q := by
      have hmem : p ∈ ({q} : Finset (TreeNode α)) := by
        rw [← hq]
        exact hpMem
      simpa using hmem
    subst q
    have hpEq : StepSelection.population R n ω = {p} := hq
    have hpDepth : p.length = n :=
      selectedPopulationDepthRepresentative_length R n ω
    have hnextCard : (StepSelection.population R (n + 1) ω).card =
        (R (ω p)).card := by
      rw [StepSelection.population_succ, hpEq]
      simp only [StepSelection.grow, Finset.singleton_biUnion]
      rw [selectedChildren_card_eq]
      simp [frontierMarks, hpDepth]
    have hnext' := hnext
    rw [hnextCard] at hnext'
    simpa [p, selectedSubtreeStepField, subtreeStepField] using hnext'
  · rintro ⟨hprev, hroot⟩ k hk
    by_cases hkn : k = n
    · subst k
      have hpCard : (StepSelection.population R n ω).card = 1 := by
        by_cases hn : n = 0
        · subst n
          simp
        · have hlt := hprev (n - 1) (by omega)
          have hlt' : (StepSelection.population R n ω).card < 2 := by
            simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] using hlt
          have hpos : 0 < (StepSelection.population R n ω).card :=
            Finset.card_pos.mpr (hnonempty n)
          omega
      let p := selectedPopulationDepthRepresentative R n ω
      have hpMem : p ∈ StepSelection.population R n ω :=
        selectedPopulationDepthRepresentative_mem R n ω (hnonempty n)
      obtain ⟨q, hq⟩ := Finset.card_eq_one.mp (by simpa [p] using hpCard)
      have hpq : p = q := by
        have hmem : p ∈ ({q} : Finset (TreeNode α)) := by
          rw [← hq]
          exact hpMem
        simpa using hmem
      subst q
      have hpEq : StepSelection.population R n ω = {p} := hq
      have hpDepth : p.length = n :=
        selectedPopulationDepthRepresentative_length R n ω
      have hnextCard : (StepSelection.population R (n + 1) ω).card =
          (R (ω p)).card := by
        rw [StepSelection.population_succ, hpEq]
        simp only [StepSelection.grow, Finset.singleton_biUnion]
        rw [selectedChildren_card_eq]
        simp [frontierMarks, hpDepth]
      have hroot' : (R (ω p)).card < 2 := by
        simpa [p, selectedSubtreeStepField, subtreeStepField] using hroot
      rw [hnextCard]
      exact hroot'
    · exact hprev k (by omega)

private lemma selectedPopulation_all_nonempty_ae
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X)
    (hnonempty : μ {ξ | (R ξ).Nonempty} = 1)
    (hmeas : MeasurableSet {ξ : Step α X | (R ξ).Nonempty}) :
    ∀ᵐ ω ∂offspringFieldLaw μ, ∀ n, (StepSelection.population R n ω).Nonempty := by
  have hcoordinate (u : TreeNode α) :
      ∀ᵐ ω ∂offspringFieldLaw μ, (R (ω u)).Nonempty := by
    let eval : Mark α (Step α X) → Step α X := fun ω => ω u
    have hpre : (offspringFieldLaw μ) (eval ⁻¹' {ξ | (R ξ).Nonempty}) =
        μ {ξ | (R ξ).Nonempty} := by
      change (offspringFieldLaw μ) ((fun ω : Mark α (Step α X) => ω u) ⁻¹'
        {ξ | (R ξ).Nonempty}) = μ {ξ | (R ξ).Nonempty}
      rw [← Measure.map_apply (measurable_pi_apply u) hmeas,
        offspringFieldLaw_coordinate]
    have hae : ∀ᵐ ω ∂offspringFieldLaw μ,
        ω ∈ eval ⁻¹' {ξ | (R ξ).Nonempty} :=
      (ae_mem_iff_measure_eq
        ((measurable_pi_apply u) hmeas).nullMeasurableSet).2 (by
          change (offspringFieldLaw μ) (eval ⁻¹' {ξ | (R ξ).Nonempty}) =
            (offspringFieldLaw μ) Set.univ
          rw [hpre, hnonempty]
          simp)
    simpa [eval] using hae
  have hall : ∀ᵐ ω ∂offspringFieldLaw μ, ∀ u : TreeNode α,
      (R (ω u)).Nonempty := ae_all_iff.2 hcoordinate
  filter_upwards [hall] with ω hω
  intro n
  induction n with
  | zero => simp [StepSelection.population]
  | succ n ih =>
      obtain ⟨p, hp⟩ := ih
      have hdepth := StepSelection.population_depth R ω n p hp
      obtain ⟨i, hi⟩ := hω p
      refine ⟨p ++ [i], ?_⟩
      rw [StepSelection.population_succ]
      apply (StepSelection.mem_grow_iff R
        (StepSelection.population R n ω) (frontierMarks n ω) (p ++ [i])).2
      refine ⟨p, hp, i, ?_, rfl⟩
      simpa [frontierMarks, hdepth] using hi


end ProbabilityTheory.BranchingRandomWalk

end
