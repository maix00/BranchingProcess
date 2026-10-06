/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Processes.StepSelection.Basic
public import Probability.BranchingRandomWalk.Restart.Trial
public import Probability.Process.HittingTime.Declarations

/-!
# First split of a selected branching population

The raw split index reads the next generation and need not be a stopping time.
Its completion generation is observable.  At a finite first split, the
previous generation contains exactly one parent, even when the selected
offspring family is empty on other samples or has arbitrary finite size.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory

variable {α X : Type*}

/-- The raw declaration at index `n` says that the selected population in
generation `n + 1` has at least two particles. -/
def selectedPopulationSplitDeclaration (R : Step.FiniteSelection α X) :
    ℕ → Set (Mark α (Step α X)) :=
  fun n => {ω | 2 ≤ (StepSelection.population R (n + 1) ω).card}

/-- The raw first split index.  It inspects the next generation, so it is not
the observable stopping time used by the branching property. -/
noncomputable def selectedPopulationRawSplitTime
    (R : Step.FiniteSelection α X) : Mark α (Step α X) → WithTop ℕ :=
  firstDeclaredSuccess (selectedPopulationSplitDeclaration R)

/-- The first generation at which the split population is observable. -/
noncomputable def selectedPopulationSplitCompletion
    (R : Step.FiniteSelection α X) : Mark α (Step α X) → WithTop ℕ :=
  firstDeclaredSuccess
    (shiftDeclarationByOne (selectedPopulationSplitDeclaration R))

theorem selectedPopulationSplitCompletion_eq_raw_add_one
    (R : Step.FiniteSelection α X) (ω : Mark α (Step α X)) :
    selectedPopulationSplitCompletion R ω =
      selectedPopulationRawSplitTime R ω + 1 :=
  firstDeclaredSuccess_shiftDeclarationByOne
    (selectedPopulationSplitDeclaration R) ω

theorem selectedPopulationSplitCompletion_ne_zero
    (R : Step.FiniteSelection α X) (ω : Mark α (Step α X)) :
    selectedPopulationSplitCompletion R ω ≠ (0 : WithTop ℕ) := by
  rw [selectedPopulationSplitCompletion_eq_raw_add_one]
  cases selectedPopulationRawSplitTime R ω <;> simp

theorem selectedPopulationRawSplitTime_eq_of_completion_eq
    (R : Step.FiniteSelection α X) (ω : Mark α (Step α X)) (n : ℕ)
    (h : selectedPopulationSplitCompletion R ω = (n + 1 : ℕ)) :
    selectedPopulationRawSplitTime R ω = n := by
  have hadd := selectedPopulationSplitCompletion_eq_raw_add_one R ω
  rw [h] at hadd
  cases hraw : selectedPopulationRawSplitTime R ω with
  | top => simp [hraw] at hadd
  | coe k =>
      have hn : n + 1 = k + 1 :=
        WithTop.coe_injective (by simpa [hraw] using hadd)
      have hn' : n = k := Nat.add_right_cancel hn
      subst k
      rfl

theorem selectedPopulationRawSplitTime_eq_top_of_completion_eq_top
    (R : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (h : selectedPopulationSplitCompletion R ω = ⊤) :
    selectedPopulationRawSplitTime R ω = ⊤ := by
  have hadd := selectedPopulationSplitCompletion_eq_raw_add_one R ω
  rw [h] at hadd
  cases hraw : selectedPopulationRawSplitTime R ω with
  | top => rfl
  | coe n =>
      rw [hraw] at hadd
      have hne : ((n : WithTop ℕ) + 1) ≠ ⊤ :=
        WithTop.add_ne_top.mpr ⟨WithTop.coe_ne_top, WithTop.coe_ne_top⟩
      exact False.elim (hne hadd.symm)

theorem selectedPopulationSplitCompletion_isStoppingTime
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select) :
    IsStoppingTime (generationFiltration (M := Step α X))
      (selectedPopulationSplitCompletion R) := by
  apply firstDeclaredSuccess_isStoppingTime
  intro n
  cases n with
  | zero =>
      change MeasurableSet[generationFiltration (M := Step α X) 0]
        (∅ : Set (Mark α (Step α X)))
      exact (generationSpace (M := Step α X) 0).measurableSet_empty
  | succ n =>
      change MeasurableSet[generationFiltration (M := Step α X) (n + 1)]
        {ω | 2 ≤ (StepSelection.population R (n + 1) ω).card}
      have hcard : Measurable[generationFiltration (M := Step α X) (n + 1)]
          (fun ω => (StepSelection.population R (n + 1) ω).card) :=
        (measurable_of_countable fun s : Finset (TreeNode α) => s.card).comp
          (StepSelection.population_adapted R hR (n + 1))
      exact hcard measurableSet_Ici

/-- If the first-generation split event has probability strictly between zero
and one, its raw look-ahead index is not a stopping time for the generation
filtration. -/
theorem selectedPopulationRawSplitTime_not_stopping_of_probability
    [MeasurableSpace α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (ν : Measure (Mark α (Step α X)))
    [IsProbabilityMeasure ν]
    (hprob : 0 < ν (selectedPopulationSplitDeclaration R 0) ∧
      ν (selectedPopulationSplitDeclaration R 0) < 1) :
    ¬ IsStoppingTime (generationFiltration (M := Step α X))
      (selectedPopulationRawSplitTime R) := by
  intro hτ
  have hevent :
      {ω | selectedPopulationRawSplitTime R ω ≤ (0 : ℕ)} =
        selectedPopulationSplitDeclaration R 0 := by
    ext ω
    change firstDeclaredSuccess (selectedPopulationSplitDeclaration R) ω ≤
      (0 : ℕ) ↔ ω ∈ selectedPopulationSplitDeclaration R 0
    rw [firstDeclaredSuccess_le_iff]
    constructor
    · rintro ⟨j, hj, hjE⟩
      have hj0 : j = 0 := by omega
      simpa [selectedPopulationSplitDeclaration, hj0] using hjE
    · intro hE
      exact ⟨0, le_rfl, hE⟩
  have hmeas : MeasurableSet[generationFiltration (M := Step α X) 0]
      (selectedPopulationSplitDeclaration R 0) := by
    rw [← hevent]
    exact hτ 0
  rw [show generationFiltration (M := Step α X) 0 = ⊥ by
    exact generationSpace_zero]
      at hmeas
  rw [MeasurableSpace.measurableSet_bot_iff] at hmeas
  rcases hmeas with hempty | huniv
  · rw [hempty] at hprob
    simp at hprob
  · rw [huniv] at hprob
    simp at hprob

theorem selectedPopulation_nonempty_of_succ_nonempty
    (R : Step.FiniteSelection α X) (ω : Mark α (Step α X)) (n : ℕ)
    (hnext : (StepSelection.population R (n + 1) ω).Nonempty) :
    (StepSelection.population R n ω).Nonempty := by
  obtain ⟨q, hq⟩ := hnext
  obtain ⟨p, hp, _, _⟩ :=
    StepSelection.population_succ_selectedParent R ω n q hq
  exact ⟨p, hp⟩

/-- On a finite first split, the preceding generation has exactly one
particle.  Extinction remains allowed on samples with no later split. -/
theorem selectedPopulation_firstSplit_parent_card_eq_one
    (R : Step.FiniteSelection α X) (ω : Mark α (Step α X)) (n : ℕ)
    (hfirst : selectedPopulationRawSplitTime R ω = n) :
    (StepSelection.population R n ω).card = 1 := by
  have hdeclaration := (firstDeclaredSuccess_eq_iff
    (selectedPopulationSplitDeclaration R) ω n).mp hfirst
  have hnextCard : 2 ≤ (StepSelection.population R (n + 1) ω).card := by
    simpa [selectedPopulationSplitDeclaration] using hdeclaration.1
  have hnext : (StepSelection.population R (n + 1) ω).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hparent : (StepSelection.population R n ω).Nonempty :=
    selectedPopulation_nonempty_of_succ_nonempty R ω n hnext
  have hcardLE : (StepSelection.population R n ω).card ≤ 1 := by
    by_cases hn : n = 0
    · subst n
      simp
    · have hnot := hdeclaration.2 (n - 1) (by omega)
      have hsmall : ¬ 2 ≤ (StepSelection.population R n ω).card := by
        simpa [selectedPopulationSplitDeclaration, Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr hn)] using hnot
      omega
  exact Nat.le_antisymm hcardLE (Nat.succ_le_of_lt (Finset.card_pos.mpr hparent))

/-- The first finite split consists of two selected children of the unique
particle in the preceding generation.  No child is required to exist away
from this event, and no upper bound on the selected family is imposed. -/
theorem selectedPopulation_firstSplit_has_sibling_pair
    (R : Step.FiniteSelection α X) (ω : Mark α (Step α X)) (n : ℕ)
    (hfirst : selectedPopulationRawSplitTime R ω = n) :
    ∃ p q₁ q₂ i₁ i₂,
      (StepSelection.population R n ω) = {p} ∧
      q₁ ∈ StepSelection.population R (n + 1) ω ∧
      q₂ ∈ StepSelection.population R (n + 1) ω ∧
      q₁ ≠ q₂ ∧
      i₁ ∈ R (ω p) ∧ i₂ ∈ R (ω p) ∧
      q₁ = p ++ [i₁] ∧ q₂ = p ++ [i₂] ∧ i₁ ≠ i₂ := by
  have hfirstDecl := (firstDeclaredSuccess_eq_iff
    (selectedPopulationSplitDeclaration R) ω n).mp hfirst
  have hcard : 2 ≤ (StepSelection.population R (n + 1) ω).card := by
    simpa [selectedPopulationSplitDeclaration] using hfirstDecl.1
  have hsingleton : (StepSelection.population R n ω).card = 1 :=
    selectedPopulation_firstSplit_parent_card_eq_one R ω n hfirst
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hsingleton
  have htwo := Finset.one_lt_card_iff.mp (by omega :
    1 < (StepSelection.population R (n + 1) ω).card)
  obtain ⟨q₁, q₂, hq₁, hq₂, hneq⟩ := htwo
  obtain ⟨p₁, hp₁, i₁, hi₁, hq₁eq⟩ :=
    StepSelection.population_succ_selectedParent R ω n q₁ hq₁
  obtain ⟨p₂, hp₂, i₂, hi₂, hq₂eq⟩ :=
    StepSelection.population_succ_selectedParent R ω n q₂ hq₂
  have hp₁eq : p₁ = p := by
    have : p₁ ∈ ({p} : Finset (TreeNode α)) := by simpa [← hp] using hp₁
    simpa using this
  have hp₂eq : p₂ = p := by
    have : p₂ ∈ ({p} : Finset (TreeNode α)) := by simpa [← hp] using hp₂
    simpa using this
  have hi_ne : i₁ ≠ i₂ := by
    intro heq
    apply hneq
    rw [hq₁eq, hq₂eq, hp₁eq, hp₂eq, heq]
  refine ⟨p, q₁, q₂, i₁, i₂, ?_, hq₁, hq₂, hneq, ?_, ?_, ?_, ?_, hi_ne⟩
  · simp [hp]
  · simpa [hp₁eq] using hi₁
  · simpa [hp₂eq] using hi₂
  · simpa [hp₁eq] using hq₁eq
  · simpa [hp₂eq] using hq₂eq

/-- The second slot in the finite selected family, after its first slot in
the given slot order.  The bottom slot is used only when fewer than two
selected slots exist. -/
noncomputable def secondSelectedSlot {α X : Type*} [LinearOrder α]
    [OrderBot α] (R : Step.FiniteSelection α X) (ξ : Step α X) : α :=
  let first := firstSelectedSlot R ξ
  if h : (R ξ).erase first |>.Nonempty then
    (R ξ).erase first |>.min' h
  else ⊥

theorem secondSelectedSlot_mem_of_card
    {α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hcard : 2 ≤ (R ξ).card) :
    secondSelectedSlot R ξ ∈ R ξ ∧
      firstSelectedSlot R ξ ≠ secondSelectedSlot R ξ := by
  classical
  have hfirst : firstSelectedSlot R ξ ∈ R ξ :=
    firstSelectedSlot_mem R ξ (Finset.card_pos.mp (by omega))
  have herase : ((R ξ).erase (firstSelectedSlot R ξ)).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hfirst]
    omega
  have hsecond : secondSelectedSlot R ξ ∈ (R ξ).erase (firstSelectedSlot R ξ) := by
    have hvalue : secondSelectedSlot R ξ =
        ((R ξ).erase (firstSelectedSlot R ξ)).min' herase := by
      simp [secondSelectedSlot, herase]
    rw [hvalue]
    exact Finset.min'_mem _ _
  exact ⟨(Finset.mem_erase.mp hsecond).2,
    (Finset.mem_erase.mp hsecond).1.symm⟩

theorem secondSelectedSlot_measurable {α X : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select) :
    Measurable (secondSelectedSlot R) := by
  classical
  let f : Finset α → α := fun s =>
    let first := if h : s.Nonempty then s.min' h else ⊥
    if h : s.erase first |>.Nonempty then s.erase first |>.min' h else ⊥
  have hf : Measurable f := measurable_of_countable f
  have heq : secondSelectedSlot R = f ∘ R.select := by
    funext ξ
    rfl
  rw [heq]
  exact hf.comp hR

/-- Choose an arbitrary address from a finite population; it is a total
selector, with the root address used on the empty population. -/
noncomputable def finitePopulationRepresentative
    {α : Type*} (population : Finset (TreeNode α)) : TreeNode α := by
  classical
  exact if h : population.Nonempty then
    population.toList.head h.toList_ne_nil else []

theorem finitePopulationRepresentative_mem
    {α : Type*} (population : Finset (TreeNode α))
    (hne : population.Nonempty) :
  finitePopulationRepresentative population ∈ population := by
  classical
  simp only [finitePopulationRepresentative, dite_eq_left hne]
  exact Finset.mem_toList.mp (List.head_mem hne.toList_ne_nil)

/-- The first two selected child addresses exposed from the representative
parent of generation `n`.  On the first finite split that generation is a
singleton, so this total selector gives its sibling pair. -/
noncomputable def selectedChildrenAtFirstSplit
    {α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (n : ℕ)
    (ω : Mark α (Step α X)) : Fin 2 → TreeNode α := by
  classical
  let parent := finitePopulationRepresentative (StepSelection.population R n ω)
  let ξ := ω parent
  exact fun i => if i.val = 0 then parent ++ [firstSelectedSlot R ξ]
    else parent ++ [secondSelectedSlot R ξ]

theorem selectedChildrenAtFirstSplit_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select) (n : ℕ) :
    Measurable[generationFiltration (M := Step α X) (n + 1)]
      (selectedChildrenAtFirstSplit R n) := by
  classical
  let parent : Mark α (Step α X) → TreeNode α := fun ω =>
    finitePopulationRepresentative (StepSelection.population R n ω)
  have hparent : Measurable[generationFiltration (M := Step α X) n] parent :=
    (measurable_of_countable fun s : Finset (TreeNode α) =>
      finitePopulationRepresentative s).comp
        (StepSelection.population_adapted R hR n)
  have hparentDepth (ω : Mark α (Step α X)) : (parent ω).length ≤ n := by
    by_cases hpop : (StepSelection.population R n ω).Nonempty
    · have hmem := finitePopulationRepresentative_mem _ hpop
      rw [StepSelection.population_depth R ω n (parent ω) hmem]
    · simp [parent, finitePopulationRepresentative, hpop]
  have hparent' : Measurable[generationFiltration (M := Step α X) (n + 1)] parent :=
    hparent.mono (generationFiltration (M := Step α X) |>.mono (Nat.le_succ n)) le_rfl
  have hmark : Measurable[generationFiltration (M := Step α X) (n + 1)]
      (fun ω => ω (parent ω)) :=
    selected_mark_measurable (n + 1) parent hparent'
      (fun ω => by have h := hparentDepth ω; omega)
  have hfirst : Measurable[generationFiltration (M := Step α X) (n + 1)]
      (fun ω => firstSelectedSlot R (ω (parent ω))) :=
    (firstSelectedSlot_measurable R hR).comp hmark
  have hsecond : Measurable[generationFiltration (M := Step α X) (n + 1)]
      (fun ω => secondSelectedSlot R (ω (parent ω))) :=
    (secondSelectedSlot_measurable R hR).comp hmark
  have hpair₁ : Measurable[generationFiltration (M := Step α X) (n + 1)]
      (fun ω => (parent ω, firstSelectedSlot R (ω (parent ω)))) :=
    hparent'.prodMk hfirst
  have hpair₂ : Measurable[generationFiltration (M := Step α X) (n + 1)]
      (fun ω => (parent ω, secondSelectedSlot R (ω (parent ω)))) :=
    hparent'.prodMk hsecond
  have happend : Measurable (fun p : TreeNode α × α => p.1 ++ [p.2]) :=
    measurable_of_countable _
  have hcoord (i : Fin 2) : Measurable[generationFiltration (M := Step α X) (n + 1)]
      (fun ω => selectedChildrenAtFirstSplit R n ω i) := by
    fin_cases i
    · exact happend.comp hpair₁
    · exact happend.comp hpair₂
  exact (@measurable_pi_iff (Mark α (Step α X)) (Fin 2)
    (fun _ => TreeNode α)
    (generationFiltration (M := Step α X) (n + 1))
    (fun _ => inferInstance) (selectedChildrenAtFirstSplit R n)).2 hcoord

theorem selectedChildrenAtFirstSplit_valid_at_first_split
    {α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ω : Mark α (Step α X)) (n : ℕ)
    (hfirst : selectedPopulationRawSplitTime R ω = n) :
    let roots := selectedChildrenAtFirstSplit R n ω
    roots 0 ∈ StepSelection.population R (n + 1) ω ∧
      roots 1 ∈ StepSelection.population R (n + 1) ω ∧
      roots 0 ≠ roots 1 ∧
      (roots 0).length = n + 1 ∧ (roots 1).length = n + 1 := by
  classical
  obtain ⟨p, q₁, q₂, i₁, i₂, hpop, hq₁, hq₂, hqneq,
      hi₁, hi₂, hq₁eq, hq₂eq, hi12⟩ :=
    selectedPopulation_firstSplit_has_sibling_pair R ω n hfirst
  have hp : p ∈ StepSelection.population R n ω := by
    rw [hpop]
    simp
  have hdepth : p.length = n := StepSelection.population_depth R ω n p hp
  have hparent : finitePopulationRepresentative
      (StepSelection.population R n ω) = p := by
    have hrep := finitePopulationRepresentative_mem
      (StepSelection.population R n ω)
      (by rw [hpop]; simp : (StepSelection.population R n ω).Nonempty)
    simpa [hpop] using hrep
  have hslots : 2 ≤ (R (ω p)).card := by
    have h := Finset.one_lt_card_iff.mpr ⟨i₁, i₂, hi₁, hi₂, hi12⟩
    omega
  obtain ⟨hsecondMem, hslotsNe⟩ :=
    secondSelectedSlot_mem_of_card R (ω p) hslots
  have hfirstMem : firstSelectedSlot R (ω p) ∈ R (ω p) :=
    firstSelectedSlot_mem R (ω p) (Finset.card_pos.mp (by omega))
  have hroot0 : selectedChildrenAtFirstSplit R n ω 0 =
      p ++ [firstSelectedSlot R (ω p)] := by
    simp [selectedChildrenAtFirstSplit, hparent]
  have hroot1 : selectedChildrenAtFirstSplit R n ω 1 =
      p ++ [secondSelectedSlot R (ω p)] := by
    norm_num [selectedChildrenAtFirstSplit, hparent]
  have hfrontier : frontierMarks n ω p = ω p := by
    simp [frontierMarks, hdepth]
  have hchild (i : α) (hi : i ∈ R (ω p)) :
      p ++ [i] ∈ StepSelection.population R (n + 1) ω := by
    rw [StepSelection.population_succ, StepSelection.mem_grow_iff]
    exact ⟨p, hp, i, hfrontier ▸ hi, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hroot0]
    exact hchild _ hfirstMem
  · rw [hroot1]
    exact hchild _ hsecondMem
  · intro heq
    have heq' : p ++ [firstSelectedSlot R (ω p)] =
        p ++ [secondSelectedSlot R (ω p)] := by
      rw [← hroot0, ← hroot1]
      exact heq
    have hslotEq : [firstSelectedSlot R (ω p)] =
        [secondSelectedSlot R (ω p)] := List.append_cancel_left heq'
    have : firstSelectedSlot R (ω p) = secondSelectedSlot R (ω p) := by
      simpa using hslotEq
    exact hslotsNe this
  · rw [hroot0, List.length_append]
    simp [hdepth]
  · rw [hroot1, List.length_append]
    simp [hdepth]

/-- The root vector at the observable first-split generation, totalized by
the empty address vector when no split occurs. -/
noncomputable def selectedPopulationFirstSplitRoots
    {α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) :
    Mark α (Step α X) → Fin 2 → TreeNode α := fun ω =>
  match selectedPopulationRawSplitTime R ω with
  | ⊤ => fun _ => []
  | (n : ℕ) => selectedChildrenAtFirstSplit R n ω

theorem selectedPopulationFirstSplitRoots_fiber_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Fin 2 → TreeNode α) :
    MeasurableSet[(selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace]
      {ω | selectedPopulationFirstSplitRoots R ω = r} := by
  classical
  let F := generationFiltration (α := α) (M := Step α X)
  let σ := selectedPopulationSplitCompletion R
  have hσ : IsStoppingTime F σ := selectedPopulationSplitCompletion_isStoppingTime R hR
  have htimeCell (n : ℕ) (E : Set (Mark α (Step α X)))
      (hE : MeasurableSet[F n] E) :
      MeasurableSet[hσ.measurableSpace] (E ∩ {ω | σ ω = (n : WithTop ℕ)}) := by
    have htimeStop : MeasurableSet[hσ.measurableSpace]
        {ω | σ ω = (n : WithTop ℕ)} := by
      exact hσ.measurableSet_eq_of_countable' n
    have htime : MeasurableSet[F n] {ω | σ ω = (n : WithTop ℕ)} := by
      simpa using (hσ.measurableSet_inter_eq_iff
        {ω | σ ω = (n : WithTop ℕ)} n).1 (htimeStop.inter htimeStop)
    have hcell : MeasurableSet[F n]
        (E ∩ {ω | σ ω = (n : WithTop ℕ)}) := hE.inter htime
    have hleF : F n ≤ ⨆ k, F k := le_iSup (fun k => F k) n
    refine ⟨hleF _ hcell, fun k => ?_⟩
    have hcut :
        (E ∩ {ω | σ ω = (n : WithTop ℕ)}) ∩ {ω | σ ω ≤ k} =
          if n ≤ k then E ∩ {ω | σ ω = (n : WithTop ℕ)} else ∅ := by
      ext ω
      by_cases hnk : n ≤ k
      · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ite_eq_left hnk]
        constructor
        · rintro ⟨⟨hEω, htimeω⟩, hleω⟩
          exact ⟨hEω, htimeω⟩
        · rintro ⟨hEω, htimeω⟩
          exact ⟨⟨hEω, htimeω⟩, by rw [htimeω]; exact WithTop.coe_le_coe.mpr hnk⟩
      · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ite_eq_right hnk,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, htimeω⟩, hleω⟩
        apply hnk
        rw [htimeω] at hleω
        exact WithTop.coe_le_coe.mp hleω
    by_cases hnk : n ≤ k
    · have heq :
          (E ∩ {ω | σ ω = (n : WithTop ℕ)}) ∩ {ω | σ ω ≤ k} =
            E ∩ {ω | σ ω = (n : WithTop ℕ)} := by
        simpa [hnk] using hcut
      exact heq.symm ▸ (F.mono hnk) _ hcell
    · have heq :
          (E ∩ {ω | σ ω = (n : WithTop ℕ)}) ∩ {ω | σ ω ≤ k} = ∅ := by
        simpa [hnk] using hcut
      exact heq.symm ▸ (F k).measurableSet_empty
  have htop : MeasurableSet[hσ.measurableSpace] {ω | σ ω = ⊤} := by
    have hfinite : MeasurableSet[hσ.measurableSpace]
        (⋃ n : ℕ, {ω | σ ω = (n : WithTop ℕ)}) :=
      MeasurableSet.iUnion fun n : ℕ => hσ.measurableSet_eq_of_countable' n
    have heq : {ω | σ ω = ⊤} = (⋃ n : ℕ, {ω | σ ω = (n : WithTop ℕ)})ᶜ := by
      ext ω
      cases htime : σ ω with
      | top => simp [htime]
      | coe n => simp [htime]
    rw [heq]
    exact hfinite.compl
  have hdefault : MeasurableSet[hσ.measurableSpace]
      {ω | selectedPopulationFirstSplitRoots R ω = (fun _ => [])} := by
    have hdecomp :
        {ω | selectedPopulationFirstSplitRoots R ω = (fun _ => [])} =
          {ω | σ ω = ⊤} ∪
          ⋃ n : ℕ, {ω | σ ω = (n + 1 : ℕ)} ∩
                {ω | selectedChildrenAtFirstSplit R n ω = (fun _ => [])} := by
      ext ω
      cases htime : σ ω with
      | top =>
          have hraw := selectedPopulationRawSplitTime_eq_top_of_completion_eq_top
            R ω (by simpa [σ] using htime)
          simp [selectedPopulationFirstSplitRoots, hraw, σ, htime]
      | coe k =>
          cases k with
          | zero =>
              have hzero : selectedPopulationSplitCompletion R ω = 0 := by
                simpa [σ] using htime
              exact False.elim ((selectedPopulationSplitCompletion_ne_zero R ω) hzero)
          | succ n =>
              have hraw := selectedPopulationRawSplitTime_eq_of_completion_eq
                R ω n (by simpa [σ] using htime)
              simp [selectedPopulationFirstSplitRoots, hraw, σ, htime]
    rw [hdecomp]
    have hfamily : MeasurableSet[hσ.measurableSpace]
        (⋃ n : ℕ, {ω | σ ω = (n + 1 : ℕ)} ∩
          {ω | selectedChildrenAtFirstSplit R n ω = (fun _ => [])}) := by
      apply MeasurableSet.iUnion
      intro n
      have hroots : MeasurableSet[F (n + 1)]
          {ω | selectedChildrenAtFirstSplit R n ω = (fun _ => [])} :=
        (selectedChildrenAtFirstSplit_measurable R hR n)
          (measurableSet_singleton (fun _ => []))
      simpa [Set.inter_comm] using htimeCell (n + 1) _ hroots
    exact htop.union hfamily
  by_cases hr : r = (fun _ => [])
  · simpa [hr] using hdefault
  · have hdecomp :
        {ω | selectedPopulationFirstSplitRoots R ω = r} =
          ⋃ n : ℕ, {ω | σ ω = (n + 1 : ℕ)} ∩
            {ω | selectedChildrenAtFirstSplit R n ω = r} := by
      ext ω
      cases htime : σ ω with
      | top =>
          have hraw := selectedPopulationRawSplitTime_eq_top_of_completion_eq_top
            R ω (by simpa [σ] using htime)
          have hr' : (fun _ : Fin 2 => []) ≠ r := fun heq => hr heq.symm
          simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
            selectedPopulationFirstSplitRoots, hraw, σ, htime]
          constructor
          · intro heq
            exact False.elim (hr' heq)
          · rintro ⟨i, hi, _⟩
            have hne : ((i : WithTop ℕ) + 1) ≠ ⊤ :=
              WithTop.add_ne_top.mpr ⟨WithTop.coe_ne_top, WithTop.coe_ne_top⟩
            exact False.elim (hne hi.symm)
      | coe k =>
          cases k with
          | zero =>
              have hzero : selectedPopulationSplitCompletion R ω = 0 := by
                simpa [σ] using htime
              exact False.elim ((selectedPopulationSplitCompletion_ne_zero R ω) hzero)
          | succ n =>
              have hraw := selectedPopulationRawSplitTime_eq_of_completion_eq
                R ω n (by simpa [σ] using htime)
              simp [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
                selectedPopulationFirstSplitRoots, hraw, σ, htime]
    rw [hdecomp]
    have hfamily : MeasurableSet[hσ.measurableSpace]
        (⋃ n : ℕ, {ω | σ ω = (n + 1 : ℕ)} ∩
          {ω | selectedChildrenAtFirstSplit R n ω = r}) := by
      apply MeasurableSet.iUnion
      intro n
      have hroots : MeasurableSet[F (n + 1)]
          {ω | selectedChildrenAtFirstSplit R n ω = r} :=
        (selectedChildrenAtFirstSplit_measurable R hR n)
          (measurableSet_singleton r)
      simpa [Set.inter_comm] using htimeCell (n + 1) _ hroots
    exact hfamily

theorem selectedPopulationFirstSplitRoots_depth
    {α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ω : Mark α (Step α X)) (n : ℕ)
    (htime : selectedPopulationSplitCompletion R ω = (n : WithTop ℕ)) :
    ∀ i : Fin 2, (selectedPopulationFirstSplitRoots R ω i).length = n := by
  cases n with
  | zero =>
      exact False.elim ((selectedPopulationSplitCompletion_ne_zero R ω) htime)
  | succ n =>
      have hraw := selectedPopulationRawSplitTime_eq_of_completion_eq
        R ω n (by simpa using htime)
      obtain ⟨_, _, _, hroot₀, hroot₁⟩ :=
        selectedChildrenAtFirstSplit_valid_at_first_split R ω n hraw
      intro i
      fin_cases i
      · simpa [selectedPopulationFirstSplitRoots, hraw] using hroot₀
      · simpa [selectedPopulationFirstSplitRoots, hraw] using hroot₁

theorem selectedPopulationFirstSplitRoots_injective_of_finite
    {α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (hfinite : selectedPopulationSplitCompletion R ω ≠ ⊤) :
    Function.Injective (selectedPopulationFirstSplitRoots R ω) := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfinite
  cases k with
  | zero =>
      exact False.elim
        ((selectedPopulationSplitCompletion_ne_zero R ω) hk.symm)
  | succ n =>
      have hraw := selectedPopulationRawSplitTime_eq_of_completion_eq
        R ω n (by simpa using hk.symm)
      obtain ⟨_, _, hrootsNe, _, _⟩ :=
        selectedChildrenAtFirstSplit_valid_at_first_split R ω n hraw
      have hne : selectedPopulationFirstSplitRoots R ω 0 ≠
          selectedPopulationFirstSplitRoots R ω 1 := by
        simpa [selectedPopulationFirstSplitRoots, hraw] using hrootsNe
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact (hne hij).elim
      · exact (hne hij.symm).elim
      · rfl

end ProbabilityTheory.BranchingRandomWalk

end
