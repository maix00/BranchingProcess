/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.GenerationBatch
import Probability.BranchingRandomWalk.Selection.NSelection.AtRank
import Probability.BranchingRandomWalk.Population.Processes.Selected.RootIndexed

/-!
# Offspring batches at the selected population

The spatially ranked particles of a totalized first-`N` population form an
adapted injective family of roots at their generation.  Reading the root
steps of their fresh descendant fields therefore gives the independent
generation batches used by the finite-selection speed construction.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.UlamHarris
open Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed

/-- The particle of dynamic rank `i` in the totalized first-`N` population.
When the population has fewer than `N` particles, use distinct addresses at
the current depth so this totalization remains injective. -/
noncomputable def selectedPopulationRankRoot
    (N n : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ) (i : Fin N) :
    RootIndexed.TreeNode (Fin N) ℕ := by
  classical
  let population := RootIndexed.selectedPopulationTotalized N
    (Finset.univ : Finset (Fin N)) initial id id n field
  let value := RootIndexed.observedPositionAtGeneration initial id id n field
  by_cases hcard : population.card = N
  · exact (Combinatorics.Branching.Selection.NSelection.particleAtRankBy
      value population i.val).getD (i, List.replicate n 0)
  · exact (i, List.replicate n 0)

/-- Enumerate the selected population in spatial rank order, breaking ties by
the genealogical address order used by first-`N` selection. -/
noncomputable def selectedPopulationRankRoots
    (N : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)] :
    ℕ → RootIndexed.StepField (Fin N) ℕ ℝ →
      Fin N → Fin N × TreeNode ℕ :=
  fun n field i => selectedPopulationRankRoot N n initial field i

private lemma selectedPopulationRankRoot_eq_ranked_of_card
    (N n : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ) (i : Fin N)
    (hcard : (RootIndexed.selectedPopulationTotalized N
      (Finset.univ : Finset (Fin N)) initial id id n field).card = N) :
    selectedPopulationRankRoot N n initial field i =
      (Combinatorics.Branching.Selection.NSelection.particleAtRankBy
        (RootIndexed.observedPositionAtGeneration initial id id n field)
        (RootIndexed.selectedPopulationTotalized N
          (Finset.univ : Finset (Fin N)) initial id id n field) i.val).getD
        (i, List.replicate n 0) := by
  simp [selectedPopulationRankRoot, hcard]

theorem selectedPopulationRankRoot_depth
    (N n : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ) (i : Fin N) :
    (selectedPopulationRankRoot N n initial field i).2.length = n := by
  classical
  let population := RootIndexed.selectedPopulationTotalized N
    (Finset.univ : Finset (Fin N)) initial id id n field
  let value := RootIndexed.observedPositionAtGeneration initial id id n field
  by_cases hcard : population.card = N
  · rw [selectedPopulationRankRoot_eq_ranked_of_card N n initial field i hcard]
    by_cases hnone : Combinatorics.Branching.Selection.NSelection.particleAtRankBy
        value population i.val = none
    · have hle :=
        Combinatorics.Branching.Selection.NSelection.particleAtRankBy_eq_none_iff.mp hnone
      rw [hcard] at hle
      exfalso
      exact (not_le_of_gt i.isLt) hle
    · obtain ⟨p, hp⟩ := Option.ne_none_iff_exists.mp hnone
      rw [show (Combinatorics.Branching.Selection.NSelection.particleAtRankBy
          value population i.val).getD (i, List.replicate n 0) = p by
        rw [← hp]
        rfl]
      exact RootIndexed.selectedPopulationTotalized_depth
        N Finset.univ initial id id n field p
        ((Combinatorics.Branching.Selection.NSelection.particleAtRankBy_eq_some_iff.mp hp.symm).1)
  · simp [selectedPopulationRankRoot, population, hcard]

theorem selectedPopulationRankRoots_injective
    (N n : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ) :
    Function.Injective (selectedPopulationRankRoots N initial n field) := by
  classical
  intro i j hij
  let population := RootIndexed.selectedPopulationTotalized N
    (Finset.univ : Finset (Fin N)) initial id id n field
  let value := RootIndexed.observedPositionAtGeneration initial id id n field
  by_cases hcard : population.card = N
  · have hrooti := selectedPopulationRankRoot_eq_ranked_of_card
      N n initial field i hcard
    have hrootj := selectedPopulationRankRoot_eq_ranked_of_card
      N n initial field j hcard
    change selectedPopulationRankRoot N n initial field i =
      selectedPopulationRankRoot N n initial field j at hij
    rw [hrooti, hrootj] at hij
    have hnonei : Combinatorics.Branching.Selection.NSelection.particleAtRankBy
        value population i.val ≠ none := by
      intro hn
      have hle :=
        Combinatorics.Branching.Selection.NSelection.particleAtRankBy_eq_none_iff.mp hn
      rw [hcard] at hle
      exact (not_le_of_gt i.isLt) hle
    have hnonej : Combinatorics.Branching.Selection.NSelection.particleAtRankBy
        value population j.val ≠ none := by
      intro hn
      have hle :=
        Combinatorics.Branching.Selection.NSelection.particleAtRankBy_eq_none_iff.mp hn
      rw [hcard] at hle
      exact (not_le_of_gt j.isLt) hle
    obtain ⟨p, hp⟩ := Option.ne_none_iff_exists.mp hnonei
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists.mp hnonej
    rw [← hp, ← hq] at hij
    have hpq : p = q := hij
    have hranki :=
      (Combinatorics.Branching.Selection.NSelection.particleAtRankBy_eq_some_iff.mp hp.symm).2
    have hrankj :=
      (Combinatorics.Branching.Selection.NSelection.particleAtRankBy_eq_some_iff.mp hq.symm).2
    apply Fin.ext
    calc
      i.val = Combinatorics.Branching.Selection.NSelection.rankBy value population p := hranki.symm
      _ = Combinatorics.Branching.Selection.NSelection.rankBy value population q := by rw [hpq]
      _ = j.val := hrankj
  · have hsimple : (i, List.replicate n 0) = (j, List.replicate n 0) := by
      simpa [selectedPopulationRankRoots, selectedPopulationRankRoot, population, hcard] using hij
    exact congrArg Prod.fst hsimple

/-- Whenever the totalized population has full size, its rank root is the
actual particle at that rank. -/
theorem selectedPopulationRankRoot_mem_and_rank_of_card
    (N n : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ) (i : Fin N)
    (hcard : (RootIndexed.selectedPopulationTotalized N
      (Finset.univ : Finset (Fin N)) initial id id n field).card = N) :
    selectedPopulationRankRoot N n initial field i ∈
        RootIndexed.selectedPopulationTotalized N Finset.univ initial id id n field ∧
      Combinatorics.Branching.Selection.NSelection.rankBy
        (RootIndexed.observedPositionAtGeneration initial id id n field)
        (RootIndexed.selectedPopulationTotalized N Finset.univ initial id id n field)
        (selectedPopulationRankRoot N n initial field i) = i.val := by
  classical
  let population := RootIndexed.selectedPopulationTotalized N
    (Finset.univ : Finset (Fin N)) initial id id n field
  let value := RootIndexed.observedPositionAtGeneration initial id id n field
  have hnone : Combinatorics.Branching.Selection.NSelection.particleAtRankBy
      value population i.val ≠ none := by
    intro hn
    have hle :=
      Combinatorics.Branching.Selection.NSelection.particleAtRankBy_eq_none_iff.mp hn
    rw [hcard] at hle
    exact (not_le_of_gt i.isLt) hle
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists.mp hnone
  have hget :
      (Combinatorics.Branching.Selection.NSelection.particleAtRankBy
        value population i.val).getD (i, List.replicate n 0) = p := by
    rw [← hp]
    rfl
  have hroot : selectedPopulationRankRoot N n initial field i = p := by
    rw [selectedPopulationRankRoot_eq_ranked_of_card N n initial field i
      (by simpa [population] using hcard)]
    simpa [population, value] using hget
  rw [hroot]
  exact Combinatorics.Branching.Selection.NSelection.particleAtRankBy_eq_some_iff.mp
    hp.symm

/-- The rank-root family contains exactly `N` distinct roots. -/
theorem selectedPopulationRankRoots_range_card
    (N n : ℕ) (initial : Fin N → ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ) :
    Fintype.card (Set.range (selectedPopulationRankRoots N initial n field)) = N := by
  classical
  let e : Fin N ≃ Set.range (selectedPopulationRankRoots N initial n field) :=
    Equiv.ofInjective (selectedPopulationRankRoots N initial n field)
      (selectedPopulationRankRoots_injective N n initial field)
  calc
    Fintype.card (Set.range (selectedPopulationRankRoots N initial n field)) =
        Fintype.card (Fin N) := Fintype.card_congr e.symm
    _ = N := Fintype.card_fin N

private lemma measurableSet_selectedPopulationRankRoot_eq
    (N n : ℕ) (initial : Fin N → ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin N) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin N) ℕ)]
    [treeOrder : LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (i : Fin N) (p : RootIndexed.TreeNode (Fin N) ℕ) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Fin N) (α := ℕ) (X := ℝ) n]
      {field | selectedPopulationRankRoot N n initial field i = p} := by
  classical
  let F := RootIndexed.stepFiltration (Root := Fin N) (α := ℕ) (X := ℝ)
  let population : RootIndexed.StepField (Fin N) ℕ ℝ →
      Finset (RootIndexed.TreeNode (Fin N) ℕ) := fun field =>
    RootIndexed.selectedPopulationTotalized N Finset.univ initial id id n field
  let value : RootIndexed.StepField (Fin N) ℕ ℝ →
      RootIndexed.TreeNode (Fin N) ℕ → ℝ := fun field p =>
    RootIndexed.observedPositionAtGeneration initial id id n field p
  letI : MeasurableSpace (RootIndexed.StepField (Fin N) ℕ ℝ) := F n
  have hpopulation : Measurable[F n] population := by
    dsimp [population]
    exact RootIndexed.selectedPopulationTotalized_adapted N Finset.univ
      initial id measurable_id id measurable_id n
  have hpopulationFiber (s : Finset (RootIndexed.TreeNode (Fin N) ℕ)) :
      MeasurableSet[F n] {field | population field = s} :=
    hpopulation (measurableSet_singleton s)
  have hpopulationRange : (Set.range population).Countable := Set.to_countable _
  have hcard : Measurable[F n] (fun field => (population field).card) :=
    (measurable_of_countable
      (fun s : Finset (RootIndexed.TreeNode (Fin N) ℕ) => s.card)).comp hpopulation
  have hcardFiber : MeasurableSet[F n] {field | (population field).card = N} :=
    hcard (measurableSet_singleton N)
  have hvalue (t : RootIndexed.TreeNode (Fin N) ℕ) :
      Measurable fun field : RootIndexed.StepField (Fin N) ℕ ℝ => value field t := by
    exact RootIndexed.positionAtGeneration_measurable initial id measurable_id n t.1 t.2
  let hkey := fun (p q : RootIndexed.TreeNode (Fin N) ℕ) =>
    @ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.measurable_valueKey_lt
      (RootIndexed.StepField (Fin N) ℕ ℝ) (RootIndexed.TreeNode (Fin N) ℕ) ℝ
      (F n) inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance treeOrder value hvalue p q
  have hrankFiber : MeasurableSet[F n]
      {field | Combinatorics.Branching.Selection.NSelection.particleAtRankBy
        (value field) (population field) i.val = some p} := by
    exact @ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.measurableSet_particleAtRankBy_eq_some
      (RootIndexed.StepField (Fin N) ℕ ℝ) (RootIndexed.TreeNode (Fin N) ℕ) ℝ
      (F n) treeOrder inferInstance value population hpopulationFiber
      hpopulationRange hkey i.val p
  let fallback : RootIndexed.TreeNode (Fin N) ℕ := (i, List.replicate n 0)
  have hset : {field | selectedPopulationRankRoot N n initial field i = p} =
      {field | (population field).card = N} ∩
          {field | Combinatorics.Branching.Selection.NSelection.particleAtRankBy
            (value field) (population field) i.val = some p} ∪
        {field | (population field).card ≠ N} ∩ {field | fallback = p} := by
    ext field
    by_cases hfull : (population field).card = N
    · have hnone : Combinatorics.Branching.Selection.NSelection.particleAtRankBy
        (value field) (population field) i.val ≠ none := by
          intro hn
          have hle :=
            Combinatorics.Branching.Selection.NSelection.particleAtRankBy_eq_none_iff.mp hn
          rw [hfull] at hle
          exact (not_le_of_gt i.isLt) hle
      have hranked := selectedPopulationRankRoot_eq_ranked_of_card N n initial field i
        (by simpa [population] using hfull)
      have hranked' : selectedPopulationRankRoot N n initial field i =
          (Combinatorics.Branching.Selection.NSelection.particleAtRankBy
            (value field) (population field) i.val).getD fallback := by
        simpa [population, value, fallback] using hranked
      have hget :
          (Combinatorics.Branching.Selection.NSelection.particleAtRankBy
            (value field) (population field) i.val).getD fallback = p ↔
            Combinatorics.Branching.Selection.NSelection.particleAtRankBy
              (value field) (population field) i.val = some p := by
        cases hopt : Combinatorics.Branching.Selection.NSelection.particleAtRankBy
            (value field) (population field) i.val with
        | none => simp [hopt] at hnone
        | some q => simp [hopt]
      change selectedPopulationRankRoot N n initial field i = p ↔ _
      rw [hranked', hget]
      simp [hfull]
    · simp [selectedPopulationRankRoot, population, value, fallback, hfull]
  rw [hset]
  exact (hcardFiber.inter hrankFiber).union
    (hcardFiber.compl.inter (by
      by_cases hp : fallback = p
      · simp [hp]
      · simp [hp]))

theorem measurable_selectedPopulationRankRoots_at
    (N n : ℕ) (initial : Fin N → ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin N) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin N) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)] :
    Measurable[RootIndexed.stepFiltration
      (Root := Fin N) (α := ℕ) (X := ℝ) n]
      (selectedPopulationRankRoots N initial n) := by
  classical
  letI : MeasurableSpace (RootIndexed.StepField (Fin N) ℕ ℝ) :=
    RootIndexed.stepFiltration (Root := Fin N) (α := ℕ) (X := ℝ) n
  apply Measurable.of_eval
  intro i
  apply measurable_to_countable'
  intro p
  exact measurableSet_selectedPopulationRankRoot_eq N n initial i p

theorem selectedPopulationRankRoots_countable
    (N n : ℕ) (initial : Fin N → ℝ)
    [treeOrder : LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)] :
    (Set.range (selectedPopulationRankRoots N initial n)).Countable :=
  Set.to_countable _

theorem selectedPopulationRankRoots_fiber_measurable
    (N n : ℕ) (initial : Fin N → ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin N) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (Fin N × TreeNode ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (roots : Fin N → Fin N × TreeNode ℕ) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Fin N) (α := ℕ) (X := ℝ) n]
      {field | selectedPopulationRankRoots N initial n field = roots} := by
  have hmeas := measurable_selectedPopulationRankRoots_at N n initial
  exact hmeas (measurableSet_singleton roots)

theorem selectedPopulationRankBatch_iIndepFun
    (N : ℕ) (initial : Fin N → ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin N) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (Fin N × TreeNode ℕ)]
    [MeasurableSingletonClass (Fin N → Fin N × TreeNode ℕ)]
    [Countable (Fin N × TreeNode ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (μ : Measure (Combinatorics.Branching.Step ℕ ℝ)) [IsProbabilityMeasure μ] :
    iIndepFun
      (selectedRootBatch (selectedPopulationRankRoots N initial) ·)
      (RootIndexed.stepFieldLaw (Root := Fin N) μ) := by
  apply selectedRootBatch_iIndepFun μ (selectedPopulationRankRoots N initial)
  · intro n
    exact selectedPopulationRankRoots_countable N n initial
  · intro n roots
    exact selectedPopulationRankRoots_fiber_measurable N n initial roots
  · intro n field i
    exact selectedPopulationRankRoot_depth N n initial field i
  · intro n field
    exact selectedPopulationRankRoots_injective N n initial field

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
