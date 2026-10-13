/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.FirstSplit.BranchingProperty
import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.AbstractSubtree
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Almost-sure finite completion of the first selected split

If a finite selection is nonempty almost surely and has positive one-step
split probability, its selected population reaches a split almost surely.
Before the split, the current population is a singleton.  The stopped-domain
branching factorization at its measurable representative gives a geometric
bound on the probability of no split through generation `n`.
-/

open MeasureTheory ProbabilityTheory
open Filter Topology
open scoped ENNReal

section

namespace ProbabilityTheory.BranchingRandomWalk

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

theorem selectedPopulationDepthRepresentative_mem
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (n : ℕ) (ω : Mark α (Step α X))
    (hne : (StepSelection.population R n ω).Nonempty) :
    selectedPopulationDepthRepresentative R n ω ∈
      StepSelection.population R n ω := by
  classical
  simp only [selectedPopulationDepthRepresentative, dite_eq_left hne]
  exact Finset.mem_toList.mp (List.head_mem hne.toList_ne_nil)

theorem selectedPopulationDepthRepresentative_length
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (n : ℕ) (ω : Mark α (Step α X)) :
    (selectedPopulationDepthRepresentative R n ω).length = n := by
  classical
  by_cases hne : (StepSelection.population R n ω).Nonempty
  · have hmem := selectedPopulationDepthRepresentative_mem R n ω hne
    exact StepSelection.population_depth R ω n _ hmem
  · simp [selectedPopulationDepthRepresentative, hne]

theorem selectedPopulationDepthRepresentative_measurable
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

theorem selectedPopulationNoSplitPrefix_measurable
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

private theorem selectedChildren_card_eq
    [LinearOrder α]
    (R : Step.FiniteSelection α X) (ω : Mark α (Step α X)) (p : TreeNode α) :
    (StepSelection.children R ω p).card = (R (ω p)).card := by
  classical
  letI : DecidableEq α := Classical.decEq α
  rw [StepSelection.children]
  exact Finset.card_image_of_injective (R (ω p)) (fun i j hij => by
    have hsingleton : [i] = [j] := List.append_cancel_left hij
    simpa using hsingleton)

private theorem selectedPopulationNoSplitPrefix_succ_iff
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

private theorem selectedPopulation_all_nonempty_ae
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X)
    (hnonempty : μ {ξ | (R ξ).Nonempty} = 1)
    (hmeas : MeasurableSet {ξ : Step α X | (R ξ).Nonempty}) :
    ∀ᵐ ω ∂stepFieldLaw μ, ∀ n, (StepSelection.population R n ω).Nonempty := by
  have hcoordinate (u : TreeNode α) :
      ∀ᵐ ω ∂stepFieldLaw μ, (R (ω u)).Nonempty := by
    let eval : Mark α (Step α X) → Step α X := fun ω => ω u
    have hpre : (stepFieldLaw μ) (eval ⁻¹' {ξ | (R ξ).Nonempty}) =
        μ {ξ | (R ξ).Nonempty} := by
      change (stepFieldLaw μ) ((fun ω : Mark α (Step α X) => ω u) ⁻¹'
        {ξ | (R ξ).Nonempty}) = μ {ξ | (R ξ).Nonempty}
      rw [← Measure.map_apply (measurable_pi_apply u) hmeas,
        stepFieldLaw_coordinate]
    have hae : ∀ᵐ ω ∂stepFieldLaw μ,
        ω ∈ eval ⁻¹' {ξ | (R ξ).Nonempty} :=
      (ae_mem_iff_measure_eq
        ((measurable_pi_apply u) hmeas).nullMeasurableSet).2 (by
          change (stepFieldLaw μ) (eval ⁻¹' {ξ | (R ξ).Nonempty}) =
            (stepFieldLaw μ) Set.univ
          rw [hpre, hnonempty]
          simp)
    simpa [eval] using hae
  have hall : ∀ᵐ ω ∂stepFieldLaw μ, ∀ u : TreeNode α,
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

/-- With positive one-step split probability and an almost surely nonempty
selected family, the selected population's first split has finite observable
completion almost surely.  Empty offspring remain allowed in the generic
step model; the nonemptiness premise is isolated here because extinction can
otherwise prevent every split. -/
theorem selectedPopulationSplitCompletion_ae_finite_of_nonempty_and_split_pos
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hnonempty : μ {ξ | (R ξ).Nonempty} = 1)
    (hsplit : MeasurableSet {ξ : Step α X | 2 ≤ (R ξ).card})
    (hpositive : 0 < μ {ξ : Step α X | 2 ≤ (R ξ).card}) :
    ∀ᵐ ω ∂stepFieldLaw μ,
      selectedPopulationSplitCompletion R ω ≠ ⊤ := by
  classical
  let noSplit : Set (Step α X) := {ξ | (R ξ).card < 2}
  let split : Set (Step α X) := {ξ | 2 ≤ (R ξ).card}
  let rootNoSplit : Set (Mark α (Step α X)) :=
    {η | (R (η [])).card < 2}
  let ν := stepFieldLaw μ
  have hnoMeas : MeasurableSet noSplit := by
    dsimp [noSplit]
    exact (measurable_of_countable fun s : Finset α => s.card).comp hR
      measurableSet_Iio
  have hrootMeas : MeasurableSet rootNoSplit := by
    change MeasurableSet ((fun η : Mark α (Step α X) => η []) ⁻¹' noSplit)
    exact hnoMeas.preimage (measurable_pi_apply [])
  have hsplitMeas : MeasurableSet split := by
    simpa [split] using hsplit
  have hcomp : splitᶜ = noSplit := by
    ext ξ
    simp [split, noSplit]
  have hpartition : μ split + μ noSplit = 1 := by
    calc
      μ split + μ noSplit = μ split + μ splitᶜ := by rw [← hcomp]
      _ = μ Set.univ := measure_add_measure_compl hsplitMeas
      _ = 1 := measure_univ
  have hq : μ noSplit < 1 := by
    by_contra hnot
    have hle : 1 ≤ μ noSplit := le_of_not_gt hnot
    have hlt : μ noSplit < μ split + μ noSplit := by
      have hlt0 : 0 + μ noSplit < μ split + μ noSplit :=
        (ENNReal.add_lt_add_iff_right (measure_ne_top μ noSplit)).2
          (by simpa [split] using hpositive)
      simpa using hlt0
    rw [hpartition] at hlt
    exact (not_lt_of_ge hle hlt)
  have hrootLaw : ν rootNoSplit = μ noSplit := by
    change ν ((fun η : Mark α (Step α X) => η []) ⁻¹' noSplit) = μ noSplit
    rw [← Measure.map_apply (measurable_pi_apply []) hnoMeas,
      stepFieldLaw_coordinate]
  have hnonemptyMeas : MeasurableSet
      {ξ : Step α X | (R ξ).Nonempty} := by
    have hcard : Measurable (fun ξ : Step α X => (R ξ).card) :=
      (measurable_of_countable fun s : Finset α => s.card).comp hR
    have hcardPos : MeasurableSet {ξ : Step α X | 0 < (R ξ).card} :=
      hcard measurableSet_Ioi
    convert hcardPos using 1
    ext ξ
    simp [Finset.card_pos]
  have hpopNonempty := selectedPopulation_all_nonempty_ae μ R hnonempty
    hnonemptyMeas
  have hprefixMeas (n : ℕ) :
      MeasurableSet[generationFiltration (M := Step α X) n]
        (selectedPopulationNoSplitPrefix R n) :=
    selectedPopulationNoSplitPrefix_measurable R hR n
  have hrepresentative (n : ℕ) :
      Measurable[generationFiltration (M := Step α X) n]
        (selectedPopulationDepthRepresentative R n) :=
    selectedPopulationDepthRepresentative_measurable R hR n
  have hprefixRecurrence (n : ℕ) :
      ν (selectedPopulationNoSplitPrefix R (n + 1)) =
        ν (selectedPopulationNoSplitPrefix R n) * μ noSplit := by
    let chosen := selectedPopulationDepthRepresentative R n
    have hfactor := selectedSubtreeStepField_event_factorization μ n chosen
      (hrepresentative n) (Set.to_countable _)
      (selectedPopulationDepthRepresentative_length R n)
      (selectedPopulationNoSplitPrefix R n) rootNoSplit
      (hprefixMeas n) hrootMeas
    have heq : selectedPopulationNoSplitPrefix R (n + 1) =ᵐ[ν]
        selectedPopulationNoSplitPrefix R n ∩
          selectedSubtreeStepField chosen ⁻¹' rootNoSplit := by
      filter_upwards [hpopNonempty] with ω hpop
      exact propext (selectedPopulationNoSplitPrefix_succ_iff R n ω hpop)
    calc
      ν (selectedPopulationNoSplitPrefix R (n + 1)) =
          ν (selectedPopulationNoSplitPrefix R n ∩
            selectedSubtreeStepField chosen ⁻¹' rootNoSplit) := measure_congr heq
      _ = ν (selectedPopulationNoSplitPrefix R n) * ν rootNoSplit := hfactor
      _ = ν (selectedPopulationNoSplitPrefix R n) * μ noSplit := by rw [hrootLaw]
  have hprefixPower (n : ℕ) :
      ν (selectedPopulationNoSplitPrefix R n) = (μ noSplit) ^ n := by
    induction n with
    | zero => simp [selectedPopulationNoSplitPrefix]
    | succ n ih =>
        rw [hprefixRecurrence n, ih, pow_succ]
  have hpow : Filter.Tendsto (fun n : ℕ => (μ noSplit) ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := μ noSplit) hq
  let forever : Set (Mark α (Step α X)) :=
    ⋂ n : ℕ, selectedPopulationNoSplitPrefix R n
  have hforever_eq : forever =
      {ω | selectedPopulationSplitCompletion R ω = ⊤} := by
    ext ω
    rw [Set.mem_iInter]
    constructor
    · intro hprefix
      have hraw : selectedPopulationRawSplitTime R ω = ⊤ := by
        cases hτ : selectedPopulationRawSplitTime R ω with
        | top => rfl
        | coe k =>
          have hdecl := (firstDeclaredSuccess_eq_iff
            (selectedPopulationSplitDeclaration R) ω k).mp hτ
          have hno := hprefix (k + 1) k (Nat.lt_succ_self k)
          have hsplit : 2 ≤ (StepSelection.population R (k + 1) ω).card := by
            simpa [selectedPopulationSplitDeclaration] using hdecl.1
          have hnot : (StepSelection.population R (k + 1) ω).card < 2 := by
            simpa [selectedPopulationNoSplitPrefix] using hno
          omega
      change selectedPopulationSplitCompletion R ω = ⊤
      rw [selectedPopulationSplitCompletion_eq_raw_add_one, hraw]
      simp
    · intro htop n k hk
      have hraw := selectedPopulationRawSplitTime_eq_top_of_completion_eq_top
        R ω htop
      have hnot : ω ∉ selectedPopulationSplitDeclaration R k := by
        intro hdecl
        have hle := (firstDeclaredSuccess_le_iff
          (selectedPopulationSplitDeclaration R) ω k).mpr ⟨k, le_rfl, hdecl⟩
        change selectedPopulationRawSplitTime R ω ≤ k at hle
        rw [hraw] at hle
        simp at hle
      have hcard : (StepSelection.population R (k + 1) ω).card < 2 := by
        simpa [selectedPopulationSplitDeclaration] using hnot
      exact hcard
  have hmeasureForever : ν forever = 0 := by
    apply le_antisymm ?_ bot_le
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hpow
    filter_upwards with n
    rw [← hprefixPower n]
    apply measure_mono
    intro ω hω
    exact (Set.mem_iInter.mp hω) n
  rw [hforever_eq] at hmeasureForever
  have hae := (measure_eq_zero_iff_ae_notMem
    (μ := ν) (s := {ω | selectedPopulationSplitCompletion R ω = ⊤})).mp
      hmeasureForever
  simpa using hae

end ProbabilityTheory.BranchingRandomWalk

end
