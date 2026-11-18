/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import MeasureTheory.Measure.LowerTail
public import Probability.Process.HittingTime.PopulationOverflow
public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Trajectory
import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Coupling
import all Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Lemmas.Coupling
import all Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Lemmas.FirstNSpec

/-!
# First-N comparison through population overflow

## Public declarations

- `RootIndexed.restartedRealPositionComparison_throughOverflow_ae`:
  $\tau=\inf\{n:|P_n|>N\}$ is a stopping time, and the installed and left
  fields have the product offspring law. Almost surely, $P_n$ embeds into
  the first-$N$ slice with positions ordered downwards for $n<\tau$.
  The leftmost first-$N$ position is at most the leftmost retained position
  for $n\le\tau$, with the empty minimum taken to be $+\infty$.
- `RootIndexed.restartedRealPositionMinimum_lowerTailDominates`: under the
  same initial order, the original endpoint laws satisfy
  $\mathbb P(M_n^{\mathrm s,\tau}\le x)\le\mathbb P(M_n^N\le x)$, with
  $M_n^{\mathrm s,\tau}=+\infty$ after the selected population overflows.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling

/-- The stopped comparison of Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 3, Lemma 3.15, on the rank-installed stages. Before overflow the
whole slice embeds into the first-N slice. At overflow, each retained
child can still be compared to a first-N child by matching a singleton. -/
private theorem stageComparison_throughOverflow_ae
    {Root α : Type*} [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (hN : 0 < N) (roots : Finset Root) (initialPosition : Root → ℝ)
    (selectedBRWPopulation : RootIndexed.CausalPopulation
      (RootIndexed.StepField (Root ⊕ Root) α ℝ) Root α ℝ
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := ℝ))
      RootIndexed.StepField.left)
    (hselectedBRWPopulationFiniteSlices : selectedBRWPopulation.FiniteSlices)
    (initialInjection : ∀ field, Cloud.SliceDominatingMap id
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field))
        (hselectedBRWPopulationFiniteSlices.toFinset 0 field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.right field))
        (RootIndexed.restartedRealPositionNSelectedBRWPopulation N roots
          initialPosition id (hselectedBRWPopulationFiniteSlices.toFinset) 0 field)) ())
    :
    let population := hselectedBRWPopulationFiniteSlices.toFinset
    let τ := finsetPopulationOverflowTime population N
    let installedField := RootIndexed.restartedRealPositionNSelectedBRWField
      N roots initialPosition id population
    let installedPopulation := RootIndexed.restartedRealPositionNSelectedBRWPopulation
      N roots initialPosition id population
    IsStoppingTime (RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := ℝ)) τ ∧
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ, ∀ n : ℕ,
      let selectedWalk := RootIndexed.BranchingWalk.ofStepField initialPosition
        (RootIndexed.StepField.left field)
      let installedWalk := RootIndexed.BranchingWalk.ofStepField initialPosition
        (installedField n field)
      ((n : WithTop ℕ) < τ field →
        Nonempty (Cloud.SliceDominatingMap id
          (Combinatorics.Branching.Selection.Coupling.populationCloud id
            selectedWalk (population n field))
          (Combinatorics.Branching.Selection.Coupling.populationCloud id
            installedWalk (installedPopulation n field)) ())) ∧
      ((n : WithTop ℕ) ≤ τ field → ∀ p ∈ population n field,
        ∃ q ∈ installedPopulation n field,
          installedWalk.position id q.1 q.2 ≤ selectedWalk.position id p.1 p.2) := by
  dsimp only
  let population := hselectedBRWPopulationFiniteSlices.toFinset
  let τ := finsetPopulationOverflowTime population N
  refine ⟨?_, ?_⟩
  · apply populationOverflowTime_isStoppingTime_of_countable
    intro n
    have hm := hselectedBRWPopulationFiniteSlices.measurable_toFinset n
    exact (measurable_of_countable
      (fun s : Finset (RootIndexed.TreeNode Root α) => (↑s : Set (RootIndexed.TreeNode Root α)))).comp hm
  have hall := ae_all_iff.2 (fun n => RootIndexed.restartedRealPositionCoupledInjection_ae
    μ hnorm N roots initialPosition selectedBRWPopulation
    hselectedBRWPopulationFiniteSlices initialInjection n)
  have hspec := installedFirstN_spec_ae μ hnorm N roots initialPosition
    selectedBRWPopulation hselectedBRWPopulationFiniteSlices
  filter_upwards [hall, hspec] with field hmatch hspec
  have hbefore (n : ℕ) (hn : (n : WithTop ℕ) < τ field) :
      ∀ k < n, (population (k + 1) field).card ≤ N := by
    intro k hk
    apply card_le_of_lt_finsetPopulationOverflowTime population N (k + 1) field
    exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr (Nat.succ_le_of_lt hk)) hn
  intro n
  refine ⟨fun hn => hmatch n (hbefore n hn), ?_⟩
  intro hn p hp
  cases n with
  | zero =>
    obtain ⟨f⟩ := hmatch 0 (by simp)
    exact ⟨f p, f.mapsTo hp, f.dominates p hp⟩
  | succ k =>
    have hk : (k : WithTop ℕ) < τ field :=
      lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self k)) hn
    obtain ⟨parents⟩ := hmatch k (hbefore k hk)
    have hsingleton : ({p} : Finset (RootIndexed.TreeNode Root α)) ⊆
        population (k + 1) field := Finset.singleton_subset_iff.mpr hp
    let f := RootIndexed.restartedRealPositionCoupledSuccessorInjection
      N roots initialPosition id selectedBRWPopulation hselectedBRWPopulationFiniteSlices
      k field {p} hsingleton (by simpa using (Nat.succ_le_of_lt hN)) (by
        rw [RootIndexed.restartedRealPositionNSelectedBRWPopulation_stage_stable
          N roots initialPosition id hselectedBRWPopulationFiniteSlices.toFinset k field]
        exact hspec k) parents
    have hmem : p ∈ ({p} : Finset (RootIndexed.TreeNode Root α)) := Finset.mem_singleton_self p
    exact ⟨f p, f.mapsTo hmem, f.dominates p hmem⟩

/-- The stopped comparison of Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 3, Lemma 3.15, on a single coupled pair of product-law fields.
Population order holds before overflow and each retained position dominates
some first-N position through the overflow generation. -/
theorem RootIndexed.restartedRealPositionComparison_throughOverflow_ae
    {Root α : Type*} [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (hN : 0 < N) (roots : Finset Root) (initialPosition : Root → ℝ)
    (selectedBRWPopulation : RootIndexed.CausalPopulation
      (RootIndexed.StepField (Root ⊕ Root) α ℝ) Root α ℝ
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := ℝ))
      RootIndexed.StepField.left)
    (hselectedBRWPopulationFiniteSlices : selectedBRWPopulation.FiniteSlices)
    (initialInjection : ∀ field, Cloud.SliceDominatingMap id
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field))
        (hselectedBRWPopulationFiniteSlices.toFinset 0 field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.right field))
        (RootIndexed.restartedRealPositionNSelectedBRWPopulation N roots
          initialPosition id (hselectedBRWPopulationFiniteSlices.toFinset) 0 field)) ())
    :
    let population := hselectedBRWPopulationFiniteSlices.toFinset
    let τ := finsetPopulationOverflowTime population N
    let V := RootIndexed.restartedRealPositionTrajectoryField N roots initialPosition id population
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    let Q := RootIndexed.stepFieldLaw (Root := Root) μ
    Measurable V ∧ P.map V = Q ∧ P.map RootIndexed.StepField.left = Q ∧
    IsStoppingTime (RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := ℝ)) τ ∧
    ∀ᵐ field ∂P, ∀ n : ℕ,
      let selectedWalk := RootIndexed.BranchingWalk.ofStepField initialPosition
        (RootIndexed.StepField.left field)
      let installedWalk := RootIndexed.BranchingWalk.ofStepField initialPosition (V field)
      let installedPopulation := RootIndexed.selectedPopulationTotalized
        N roots initialPosition id id n (V field)
      ((n : WithTop ℕ) < τ field →
        Nonempty (Cloud.SliceDominatingMap id
          (Combinatorics.Branching.Selection.Coupling.populationCloud id
            selectedWalk (population n field))
          (Combinatorics.Branching.Selection.Coupling.populationCloud id
            installedWalk installedPopulation) ())) ∧
      ((n : WithTop ℕ) ≤ τ field →
        installedPopulation.inf (fun q => ((installedWalk.position id q.1 q.2 : ℝ) : WithTop ℝ)) ≤
          (population n field).inf
            (fun p => ((selectedWalk.position id p.1 p.2 : ℝ) : WithTop ℝ))) := by
  dsimp only
  obtain ⟨hm, hlaw⟩ := RootIndexed.restartedRealPositionTrajectoryField_measurable_law
    μ N roots initialPosition selectedBRWPopulation hselectedBRWPopulationFiniteSlices
  obtain ⟨hstop, hcompare⟩ := stageComparison_throughOverflow_ae μ hnorm N hN roots
    initialPosition selectedBRWPopulation hselectedBRWPopulationFiniteSlices initialInjection
  refine ⟨hm, hlaw, RootIndexed.stepFieldLaw_reindex μ Sum.inl Sum.inl_injective, hstop, ?_⟩
  filter_upwards [hcompare] with field hcompare
  intro n
  let population := hselectedBRWPopulationFiniteSlices.toFinset
  let V := RootIndexed.restartedRealPositionTrajectoryField N roots initialPosition id population field
  let S := RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id population n field
  let parents := RootIndexed.restartedRealPositionNSelectedBRWPopulation
    N roots initialPosition id population n field
  let selected := RootIndexed.selectedPopulationTotalized N roots initialPosition id id n V
  have hagree := RootIndexed.restartedRealPositionTrajectoryField_eq_stage N roots initialPosition id population field n
  have hpop : selected = parents :=
    RootIndexed.adapted_eq_of_agree_before n _ (RootIndexed.selectedPopulationTotalized_adapted
      N roots initialPosition id measurable_id id measurable_id n) V S hagree
  have hposition (q : RootIndexed.TreeNode Root α) (hq : q ∈ parents) :
      RootIndexed.position initialPosition id V q.1 q.2 =
        RootIndexed.position initialPosition id S q.1 q.2 := by
    have hdepth : q.2.length = n :=
      RootIndexed.selectedPopulationTotalized_depth N roots initialPosition id id n S q hq
    have heq := RootIndexed.adapted_eq_of_agree_before n _ (RootIndexed.positionAtGeneration_measurable
      initialPosition id measurable_id n q.1 q.2) V S hagree
    simpa [RootIndexed.positionAtGeneration, hdepth] using heq
  refine ⟨?_, ?_⟩
  · intro hn
    obtain ⟨f⟩ := (hcompare n).1 hn
    refine ⟨⟨f, ?_, ?_, ?_⟩⟩
    · intro p hp
      change f p ∈ selected
      rw [hpop]
      exact f.mapsTo hp
    · exact f.injOn
    · intro p hp
      have hq : f p ∈ parents := f.mapsTo hp
      change RootIndexed.position initialPosition id V (f p).1 (f p).2 ≤ _
      rw [hposition (f p) hq]
      exact f.dominates p hp
  · intro hn
    apply Finset.le_inf
    intro p hp
    obtain ⟨q, hq, hle⟩ := (hcompare n).2 hn p hp
    have hq' : q ∈ selected := hpop.symm ▸ hq
    apply (Finset.inf_le hq').trans
    apply WithTop.coe_le_coe.mpr
    change RootIndexed.position initialPosition id V q.1 q.2 ≤ _
    exact (hposition q hq).le.trans hle


private theorem measurable_finsetMinimum
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {population : Ω → Finset ι} {position : ι → Ω → ℝ}
    (hpopulation : Measurable population) (hposition : ∀ p, Measurable (position p)) :
    Measurable (fun ω => (population ω).inf fun p => (position p ω : WithTop ℝ)) := by
  apply measurable_of_Iio
  intro x
  rw [show (fun ω => (population ω).inf fun p => (position p ω : WithTop ℝ)) ⁻¹'
      Set.Iio x = ⋃ p, {ω | p ∈ population ω} ∩ {ω | (position p ω : WithTop ℝ) < x} by
    ext ω
    simp [Finset.inf_lt_iff]]
  exact MeasurableSet.iUnion fun p =>
    (measurable_finset_iff.mp hpopulation p).setOf.inter
      (measurableSet_lt (hposition p).withTop_coe measurable_const)

/-- The marginal endpoint comparison of Wang Yiyang, *Asymptotic Speed of
the N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 3, Lemma 3.15. The selected endpoint is set to $+\infty$ after overflow. -/
theorem RootIndexed.restartedRealPositionMinimum_lowerTailDominates
    {Root α : Type*} [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (hN : 0 < N) (roots : Finset Root) (initialPosition : Root → ℝ)
    (selectedPopulation : RootIndexed.CausalPopulation
      (RootIndexed.StepField Root α ℝ) Root α ℝ
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ)) id)
    (finiteSlices : selectedPopulation.FiniteSlices)
    (initialInjection : ∀ field, Order.DominatingMap
      (↑(finiteSlices.toFinset 0 field) : Set (RootIndexed.TreeNode Root α))
      (↑(RootIndexed.initialPopulation (α := α) roots) : Set (RootIndexed.TreeNode Root α))
      (fun p => initialPosition p.1) (fun q => initialPosition q.1))
    (n : ℕ) :
    let Q := RootIndexed.stepFieldLaw (Root := Root) μ
    let τ := finsetPopulationOverflowTime finiteSlices.toFinset N
    let selectedMinimum := fun field =>
      if (n : WithTop ℕ) ≤ τ field then
        (finiteSlices.toFinset n field).inf fun p =>
          ((RootIndexed.position initialPosition id field p.1 p.2 : ℝ) : WithTop ℝ)
      else ⊤
    let nSelectedMinimum := fun field =>
      (RootIndexed.selectedPopulationTotalized N roots initialPosition id id n field).inf fun q =>
        ((RootIndexed.position initialPosition id field q.1 q.2 : ℝ) : WithTop ℝ)
    (Q.map selectedMinimum).LowerTailDominates (Q.map nSelectedMinimum) := by
  intro Q τ F G
  let ℱ := RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ)
  let 𝒢 := RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)
  let left : RootIndexed.StepField (Root ⊕ Root) α ℝ → RootIndexed.StepField Root α ℝ :=
    RootIndexed.StepField.left
  have hleftFiltration (k : ℕ) : Measurable[𝒢 k, ℱ k] left :=
    RootIndexed.StepField.reindex_filtration_measurable (X := ℝ) Sum.inl k
  have hleft : Measurable left := by
    apply measurable_pi_iff.mpr
    intro r
    exact measurable_pi_apply (Sum.inl r)
  let lifted := selectedPopulation.pullback left hleftFiltration rfl
  let liftedFinite := finiteSlices.pullback left hleftFiltration rfl
  have hslice (k : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) :
      liftedFinite.toFinset k field = finiteSlices.toFinset k (left field) := by
    apply Finset.coe_injective
    simp
  have hinit : ∀ field, Cloud.SliceDominatingMap id
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition (left field))
        (liftedFinite.toFinset 0 field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.right field))
        (RootIndexed.restartedRealPositionNSelectedBRWPopulation N roots initialPosition
          id liftedFinite.toFinset 0 field)) () := by
    intro field
    rw [hslice]
    let f := initialInjection (left field)
    refine ⟨f.toFun, f.mapsTo, f.injOn, ?_⟩
    intro p hp
    have hp' : p.2 = [] := List.length_eq_zero_iff.mp
      (selectedPopulation.depth 0 (left field) p
        ((finiteSlices.mem_toFinset 0 (left field) p).mp hp))
    obtain ⟨r, _, hr⟩ := RootIndexed.mem_initialPopulation_iff.mp (f.mapsTo hp)
    change RootIndexed.position initialPosition id (RootIndexed.StepField.right field)
      (f.toFun p).1 (f.toFun p).2 ≤ RootIndexed.position initialPosition id (left field) p.1 p.2
    rw [hr, hp']
    simpa [RootIndexed.position, hr] using f.dominates p hp
  obtain ⟨hV, hVlaw, hleftLaw, _, hcompare⟩ :=
    RootIndexed.restartedRealPositionComparison_throughOverflow_ae
      μ hnorm N hN roots initialPosition lifted liftedFinite hinit
  let V := RootIndexed.restartedRealPositionTrajectoryField N roots initialPosition id
    liftedFinite.toFinset
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  have hpos (p : RootIndexed.TreeNode Root α) :
      Measurable (fun field : RootIndexed.StepField Root α ℝ =>
        RootIndexed.position initialPosition id field p.1 p.2) :=
    (RootIndexed.position_measurable initialPosition id measurable_id p.1 p.2).mono
      (ℱ.le p.2.length) le_rfl
  have hstop : IsStoppingTime ℱ τ := by
    apply populationOverflowTime_isStoppingTime_of_countable
    intro k
    exact (measurable_of_countable
      (fun s : Finset (RootIndexed.TreeNode Root α) => (↑s : Set (RootIndexed.TreeNode Root α)))).comp
      (finiteSlices.measurable_toFinset k)
  have hF : Measurable F := (measurable_finsetMinimum
      ((finiteSlices.measurable_toFinset n).mono (ℱ.le n) le_rfl) hpos).piecewise
    (ℱ.le n _ (hstop.measurableSet_ge_of_countable n)) measurable_const
  have hG : Measurable G := measurable_finsetMinimum
    ((RootIndexed.selectedPopulationTotalized_adapted N roots initialPosition
      id measurable_id id measurable_id n).mono (ℱ.le n) le_rfl) hpos
  have hle : ∀ᵐ field ∂P, G (V field) ≤ F (left field) := by
    filter_upwards [hcompare] with field hfield
    by_cases hn : (n : WithTop ℕ) ≤ τ (left field)
    · have hτ : finsetPopulationOverflowTime liftedFinite.toFinset N field = τ (left field) := by
        apply WithTop.eq_of_forall_le_coe_iff
        intro k
        calc
          _ ↔ ∃ j ≤ k, N < (liftedFinite.toFinset j field).card :=
            finsetPopulationOverflowTime_le_iff liftedFinite.toFinset N k field
          _ ↔ ∃ j ≤ k, N < (finiteSlices.toFinset j (left field)).card := by
            simp only [hslice]
          _ ↔ _ :=
            (finsetPopulationOverflowTime_le_iff finiteSlices.toFinset N k (left field)).symm
      rw [show F (left field) = (finiteSlices.toFinset n (left field)).inf (fun p =>
          ((RootIndexed.position initialPosition id (left field) p.1 p.2 : ℝ) : WithTop ℝ)) by
        simp [F, hn], ← hslice]
      exact (hfield n).2 (hτ.symm ▸ hn)
    · simp [F, hn]
  have hFmap : P.map (F ∘ left) = Q.map F := by
    rw [← Measure.map_map hF hleft, hleftLaw]
  have hGmap : P.map (G ∘ V) = Q.map G := by
    rw [← Measure.map_map hG hV, hVlaw]
  intro x
  rw [← hFmap, ← hGmap, Measure.map_apply (hF.comp hleft) measurableSet_Iic,
    Measure.map_apply (hG.comp hV) measurableSet_Iic]
  apply measure_mono_ae
  filter_upwards [hle] with field hfield hmem
  exact hfield.trans hmem

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

end
