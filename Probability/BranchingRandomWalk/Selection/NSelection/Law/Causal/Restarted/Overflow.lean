/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import Mathlib.MeasureTheory.Measure.Prod
import Probability.BranchingRandomWalk.Population.Processes.Causal.Restriction
import Mathlib.MeasureTheory.Measure.Continuity
public import MeasureTheory.Measure.LowerTail
public import Probability.Process.HittingTime.PopulationOverflow
public import Probability.BranchingRandomWalk.Population.Processes.Causal.Capacity.Basic
public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Trajectory
import Probability.BranchingRandomWalk.Population.Processes.Selected.ParameterizedRootIndexed
import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Coupling
import all Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Lemmas.Coupling
import all Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Lemmas.FirstNSpec

/-!
# First-N comparison through population overflow

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.measure_endpointMinimum_gt_le_terminalAvoidance_add_capacityFailure`:
  under almost-sure left local finiteness and `N>0`, for any causal
  population `P` with an initial dominating injection,
  `P(min NSelected_n>x) ≤ P(∀p∈P_n, position(p)>x)+P(Cap(N,n)ᶜ)`.
  Empty minima are `+∞`; no normalization or moment hypothesis is imposed.

- `RootIndexed.restartedRealPositionComparison_throughOverflow_ae`:
  $\tau=\inf\{n:|P_n|>N\}$ is a stopping time, and the installed and left
  fields have the product offspring law. Almost surely, $P_n$ embeds into
  the first-$N$ slice with positions ordered downwards for $n<\tau$.
  The leftmost first-$N$ position is at most the leftmost retained position
  for $n\le\tau$, with the empty minimum taken to be $+\infty$.
- `RootIndexed.measure_selectedPopulation_lowerTail_le_firstN`: for any causal
  population, including infinite slices, the event that a particle is at most
  $x$ at generation $n\le\tau$ has probability at most
  $P(M_n^N\le x)$. Only initial domination and one-sided local finiteness
  of the offspring law are required.
- `RootIndexed.measure_selectedPopulation_lowerTail_le_firstN_of_randomInitial`:
  the same inequality for a coupled random initial pair independent of the
  offspring field. No finite-slice or moment assumption is added.

The finite product-field construction is internal to this proof. The general
result follows by increasing finite ancestral restrictions and Mathlib's
continuity of measure from below.
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
    (N : ℕ) (hN : 0 < N) (roots : Finset Root) (initialPosition : Root → ℝ)
    (admissible : ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root) μ, ∀ k,
      IsLowerFiniteBy
        (RootIndexed.observedPositionAtGeneration initialPosition id id (k + 1) field)
        (Combinatorics.Branching.Population.childrenAtGeneration k
          (RootIndexed.selectedPopulationTotalized N roots initialPosition id id k field) field))
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
    μ N roots initialPosition admissible selectedBRWPopulation
    hselectedBRWPopulationFiniteSlices initialInjection n)
  have hspec := installedFirstN_spec_ae μ N roots initialPosition admissible
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
    (N : ℕ) (hN : 0 < N) (roots : Finset Root) (initialPosition : Root → ℝ)
    (admissible : ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root) μ, ∀ k,
      IsLowerFiniteBy
        (RootIndexed.observedPositionAtGeneration initialPosition id id (k + 1) field)
        (Combinatorics.Branching.Population.childrenAtGeneration k
          (RootIndexed.selectedPopulationTotalized N roots initialPosition id id k field) field))
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
  obtain ⟨hstop, hcompare⟩ := stageComparison_throughOverflow_ae μ N hN roots
    initialPosition admissible selectedBRWPopulation hselectedBRWPopulationFiniteSlices initialInjection
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

/-- Lemma 3.15 of Wang Yiyang, *Asymptotic Speed of the N-Branching Random
Walk with Infinite Offspring* (Fudan University, 2026), Chapter 3, for coupled
random initial positions. The product measure samples the initial pair
independently of the offspring field. Each section at a fixed initial pair
uses the same offspring-sharing construction. -/
private theorem RootIndexed.restartedRealPositionCoupling_of_randomInitial
    {Initial Root α : Type*} [MeasurableSpace Initial] [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (initialLaw : Measure Initial) [IsProbabilityMeasure initialLaw]
    (N : ℕ) (hN : 0 < N) (roots : Finset Root)
    (initialPosition : Initial → Root → ℝ) (hposition : Measurable initialPosition)
    (selectedPopulation : Initial → RootIndexed.CausalPopulation
      (RootIndexed.StepField Root α ℝ) Root α ℝ
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ)) id)
    (finiteSlices : ∀ x, (selectedPopulation x).FiniteSlices)
    (hpopulation : ∀ n, Measurable
      (fun sample : Initial × RootIndexed.StepField Root α ℝ =>
        (finiteSlices sample.1).toFinset n sample.2))
    (hleftFinite : ∀ᵐ ξ ∂μ, ξ.IsLeftLocallyFinite)
    (initialOrder : ∀ᵐ x ∂initialLaw, ∀ field, Nonempty (Order.DominatingMap
      (↑((finiteSlices x).toFinset 0 field) : Set (RootIndexed.TreeNode Root α))
      (↑(RootIndexed.initialPopulation (α := α) roots) : Set (RootIndexed.TreeNode Root α))
      (fun p => initialPosition x p.1) (fun q => initialPosition x q.1)))
    :
    let Q := RootIndexed.stepFieldLaw (Root := Root) μ
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    let originalLaw := initialLaw.prod Q
    let couplingLaw := initialLaw.prod P
    let slices := fun k (sample : Initial × RootIndexed.StepField Root α ℝ) =>
      (finiteSlices sample.1).toFinset k sample.2
    let τ := finsetPopulationOverflowTime slices N
    let selectedMinimum := fun (n : ℕ) sample =>
      if (n : WithTop ℕ) ≤ τ sample then
        (slices n sample).inf fun p =>
          ((RootIndexed.position (initialPosition sample.1) id sample.2 p.1 p.2 : ℝ) : WithTop ℝ)
      else ⊤
    let nSelectedMinimum := fun (n : ℕ) (sample : Initial × RootIndexed.StepField Root α ℝ) =>
      (RootIndexed.selectedPopulationTotalized N roots (initialPosition sample.1)
        id id n sample.2).inf fun q =>
        ((RootIndexed.position (initialPosition sample.1) id sample.2 q.1 q.2 : ℝ) : WithTop ℝ)
    ∃ V : Initial × RootIndexed.StepField (Root ⊕ Root) α ℝ → RootIndexed.StepField Root α ℝ,
      Measurable V ∧ couplingLaw.map (fun sample => (sample.1, V sample)) = originalLaw ∧
      couplingLaw.map (Prod.map id RootIndexed.StepField.left) = originalLaw ∧
      (∀ᵐ sample ∂couplingLaw, ∀ n,
        nSelectedMinimum n (sample.1, V sample) ≤
          selectedMinimum n (sample.1, RootIndexed.StepField.left sample.2)) ∧
      ∀ n, (originalLaw.map (selectedMinimum n)).LowerTailDominates
        (originalLaw.map (nSelectedMinimum n)) := by
  intro Q P originalLaw couplingLaw slices τ F G
  let input := fun sample : Initial × RootIndexed.StepField Root α ℝ =>
    (initialPosition sample.1, sample.2)
  have hinput : Measurable input :=
    (hposition.comp measurable_fst).prodMk measurable_snd
  have hpos (p : RootIndexed.TreeNode Root α) :
      Measurable (fun sample : Initial × RootIndexed.StepField Root α ℝ =>
        RootIndexed.position (initialPosition sample.1) id sample.2 p.1 p.2) := by
    simpa [input, Function.comp_def, RootIndexed.observedPositionAtGeneration,
      RootIndexed.positionAtGeneration]
      using (RootIndexed.measurable_observedPositionAtGeneration_withInitialPosition p.2.length p
        |>.comp hinput)
  have hstop : IsStoppingTime (⊤ : Filtration ℕ inferInstance) τ := by
    apply populationOverflowTime_isStoppingTime_of_countable
    intro k
    change Measurable (fun sample => (↑(slices k sample) : Set (RootIndexed.TreeNode Root α)))
    exact (measurable_of_countable
      (fun s : Finset (RootIndexed.TreeNode Root α) => (↑s : Set (RootIndexed.TreeNode Root α)))).comp
      (hpopulation k)
  have hF (n : ℕ) : Measurable (F n) :=
    (measurable_finsetMinimum (hpopulation n) hpos).piecewise
      ((⊤ : Filtration ℕ _).le n _ (hstop.measurableSet_ge_of_countable n)) measurable_const
  have hG (n : ℕ) : Measurable (G n) := measurable_finsetMinimum
    ((RootIndexed.measurable_selectedPopulationTotalized_withInitialPosition N roots n).comp
      hinput) hpos
  let left : RootIndexed.StepField (Root ⊕ Root) α ℝ → RootIndexed.StepField Root α ℝ :=
    RootIndexed.StepField.left
  let right : RootIndexed.StepField (Root ⊕ Root) α ℝ → RootIndexed.StepField Root α ℝ :=
    RootIndexed.StepField.right
  have hleft : Measurable left := measurable_pi_iff.mpr
    fun r => measurable_pi_apply (Sum.inl r)
  have hright : Measurable right := measurable_pi_iff.mpr
    fun r => measurable_pi_apply (Sum.inr r)
  let leftPair : Initial × RootIndexed.StepField (Root ⊕ Root) α ℝ →
      Initial × RootIndexed.StepField Root α ℝ := Prod.map id left
  have hleftPair : Measurable leftPair :=
    measurable_fst.prodMk (hleft.comp measurable_snd)
  have hleftLaw : P.map left = Q :=
    RootIndexed.stepFieldLaw_reindex μ Sum.inl Sum.inl_injective
  have hleftPairLaw : couplingLaw.map leftPair = originalLaw := by
    rw [show couplingLaw = initialLaw.prod P from rfl,
      show leftPair = Prod.map id left from rfl,
      ← Measure.map_prod_map initialLaw P measurable_id hleft, Measure.map_id, hleftLaw]
  let leftPosition := fun n (sample : Initial × RootIndexed.StepField (Root ⊕ Root) α ℝ) p =>
    RootIndexed.observedPositionAtGeneration (initialPosition sample.1) id id n
      (left sample.2) p
  let rightPosition := fun n (sample : Initial × RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (field : RootIndexed.StepField Root α ℝ) p =>
    RootIndexed.observedPositionAtGeneration (initialPosition sample.1) id id n field p
  let rightPopulation := fun n (sample : Initial × RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (field : RootIndexed.StepField Root α ℝ) =>
    RootIndexed.selectedPopulationTotalized N roots (initialPosition sample.1) id id n field
  let stage := RootIndexed.rankInstalledField leftPosition rightPosition
    (fun n sample => slices n (leftPair sample)) rightPopulation (left ∘ Prod.snd) (right ∘ Prod.snd)
  let V : Initial × RootIndexed.StepField (Root ⊕ Root) α ℝ → RootIndexed.StepField Root α ℝ :=
    fun sample r u => stage (u.length + 1) sample r u
  have hstage (k : ℕ) : Measurable (stage k) := by
    apply RootIndexed.rankInstalledField_measurable
    · intro n s
      exact ((hpopulation n).comp hleftPair) (measurableSet_singleton s)
    · intro n
      exact Set.to_countable _
    · intro n prior hprior s
      exact ((RootIndexed.measurable_selectedPopulationTotalized_withInitialPosition N roots n).comp
        ((hposition.comp measurable_fst).prodMk hprior)) (measurableSet_singleton s)
    · intro n prior hprior
      exact Set.to_countable _
    · intro n p q
      apply measurable_valueKey_lt
      intro r
      exact (RootIndexed.measurable_observedPositionAtGeneration_withInitialPosition n r).comp
        (hinput.comp hleftPair)
    · intro n prior hprior p q
      apply measurable_valueKey_lt
      intro r
      exact (RootIndexed.measurable_observedPositionAtGeneration_withInitialPosition n r).comp
        ((hposition.comp measurable_fst).prodMk hprior)
    · exact hleft.comp measurable_snd
    · exact hright.comp measurable_snd
  have hV : Measurable V := by
    apply measurable_pi_iff.mpr
    intro r
    apply measurable_pi_iff.mpr
    intro u
    exact ((measurable_pi_apply u).comp (measurable_pi_apply r)).comp (hstage (u.length + 1))
  let rightPair := fun (sample : Initial × RootIndexed.StepField (Root ⊕ Root) α ℝ) => (sample.1, V sample)
  have hrightPair : Measurable rightPair := measurable_fst.prodMk hV
  let lift (x : Initial) := (selectedPopulation x).pullback left
    (fun k => RootIndexed.StepField.reindex_filtration_measurable (X := ℝ) Sum.inl k) rfl
  let liftedFinite (x : Initial) := (finiteSlices x).pullback left
    (fun k => RootIndexed.StepField.reindex_filtration_measurable (X := ℝ) Sum.inl k) rfl
  have hslice (x : Initial) (k : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) :
      (liftedFinite x).toFinset k field = slices k (x, left field) := by
    apply Finset.coe_injective
    simp only [slices, RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
    rfl
  have hfixedV (x : Initial) :
      (fun field => V (x, field)) = RootIndexed.restartedRealPositionTrajectoryField
        N roots (initialPosition x) id (liftedFinite x).toFinset := by
    have hstageEq (k : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) :
        stage k (x, field) = RootIndexed.restartedRealPositionNSelectedBRWField N roots
          (initialPosition x) id (liftedFinite x).toFinset k field := by
      induction k generalizing field with
      | zero => rfl
      | succ k ih =>
        simp only [stage, RootIndexed.restartedRealPositionNSelectedBRWField,
          RootIndexed.rankInstalledField_succ]
        congr 1
        · have hprior := ih field
          unfold stage RootIndexed.restartedRealPositionNSelectedBRWField at hprior
          simp only [leftPosition, rightPosition, rightPopulation, leftPair, Prod.map, id_eq,
            ← hslice, left, right] at hprior
          funext r u
          simp only [RootIndexed.rankInstalledStepField, valueAtMatchedRank,
            ProbabilityTheory.BranchingRandomWalk.Coupling.valueAtObjectPreimage,
            Function.comp_apply, leftPair, Prod.map, id_eq, leftPosition, rightPosition,
            rightPopulation, ← hslice, left, right, hprior]
        · exact ih field
    funext field r u
    exact congrFun (congrFun (hstageEq (u.length + 1) field) r) u
  have hrightPairLaw : couplingLaw.map rightPair = originalLaw := by
    ext S hS
    rw [Measure.map_apply hrightPair hS, Measure.prod_apply (hS.preimage hrightPair),
      Measure.prod_apply hS]
    apply lintegral_congr
    intro x
    obtain ⟨hm, hlaw⟩ := RootIndexed.restartedRealPositionTrajectoryField_measurable_law
      μ N roots (initialPosition x) (lift x) (liftedFinite x)
    let Sx := (fun f : RootIndexed.StepField Root α ℝ => (x, f)) ⁻¹' S
    have hSx : MeasurableSet Sx := hS.preimage (measurable_const.prodMk measurable_id)
    change P ((fun field => V (x, field)) ⁻¹' Sx) = Q Sx
    rw [hfixedV x, ← Measure.map_apply hm hSx, hlaw]
  have hcompare : ∀ᵐ sample ∂couplingLaw, ∀ n, G n (rightPair sample) ≤ F n (leftPair sample) := by
    have hmeas : MeasurableSet {sample | ∀ n, G n (rightPair sample) ≤ F n (leftPair sample)} := by
      rw [show {sample | ∀ n, G n (rightPair sample) ≤ F n (leftPair sample)} =
          ⋂ n, {sample | G n (rightPair sample) ≤ F n (leftPair sample)} by ext; simp]
      exact MeasurableSet.iInter fun n =>
        measurableSet_le ((hG n).comp hrightPair) ((hF n).comp hleftPair)
    apply (Measure.ae_prod_iff_ae_ae (μ := initialLaw) (ν := P) hmeas).2
    filter_upwards [initialOrder] with x hinit
    have hbase : ∀ field, Cloud.SliceDominatingMap id
        (Combinatorics.Branching.Selection.Coupling.populationCloud id
          (RootIndexed.BranchingWalk.ofStepField (initialPosition x) (left field))
          ((liftedFinite x).toFinset 0 field))
        (Combinatorics.Branching.Selection.Coupling.populationCloud id
          (RootIndexed.BranchingWalk.ofStepField (initialPosition x) (right field))
          (RootIndexed.restartedRealPositionNSelectedBRWPopulation N roots (initialPosition x)
            id (liftedFinite x).toFinset 0 field)) () := by
      intro field
      rw [hslice]
      let f := (hinit (left field)).some
      refine ⟨f.toFun, f.mapsTo, f.injOn, ?_⟩
      intro p hp
      have hp' : p.2 = [] := List.length_eq_zero_iff.mp
        ((selectedPopulation x).depth 0 (left field) p
          (((finiteSlices x).mem_toFinset 0 (left field) p).mp hp))
      obtain ⟨r, _, hr⟩ := RootIndexed.mem_initialPopulation_iff.mp (f.mapsTo hp)
      change RootIndexed.position (initialPosition x) id (right field) (f.toFun p).1 (f.toFun p).2 ≤
        RootIndexed.position (initialPosition x) id (left field) p.1 p.2
      rw [hr, hp']
      simpa [RootIndexed.position, hr] using f.dominates p hp
    obtain ⟨_, _, _, _, hbound⟩ := RootIndexed.restartedRealPositionComparison_throughOverflow_ae
      μ N hN roots (initialPosition x)
      (RootIndexed.selectedPopulationTotalized_admissible_ae_of_leftLocallyFinite
        μ hleftFinite N roots (initialPosition x)) (lift x) (liftedFinite x) hbase
    filter_upwards [hbound] with field hfield n
    change G n (x, V (x, field)) ≤ F n (x, left field)
    by_cases hn : (n : WithTop ℕ) ≤ τ (x, left field)
    · have hτ : finsetPopulationOverflowTime (liftedFinite x).toFinset N field =
          τ (x, left field) := by
        apply WithTop.eq_of_forall_le_coe_iff
        intro k
        calc
          _ ↔ ∃ j ≤ k, N < ((liftedFinite x).toFinset j field).card :=
            finsetPopulationOverflowTime_le_iff (liftedFinite x).toFinset N k field
          _ ↔ ∃ j ≤ k, N < (slices j (x, left field)).card := by simp only [hslice]
          _ ↔ _ := (finsetPopulationOverflowTime_le_iff slices N k (x, left field)).symm
      rw [show F n (x, left field) = (slices n (x, left field)).inf (fun p =>
          ((RootIndexed.position (initialPosition x) id (left field) p.1 p.2 : ℝ) :
            WithTop ℝ)) by simp [F, hn], ← hslice, congrFun (hfixedV x) field]
      exact (hfield n).2 (hτ.symm ▸ hn)
    · simp [F, hn]
  refine ⟨V, hV, hrightPairLaw, hleftPairLaw, hcompare, ?_⟩
  intro n a
  have hFmap : couplingLaw.map (F n ∘ leftPair) = originalLaw.map (F n) := by
    rw [← Measure.map_map (hF n) hleftPair, hleftPairLaw]
  have hGmap : couplingLaw.map (G n ∘ rightPair) = originalLaw.map (G n) := by
    rw [← Measure.map_map (hG n) hrightPair, hrightPairLaw]
  rw [← hFmap, ← hGmap, Measure.map_apply ((hF n).comp hleftPair) measurableSet_Iic,
    Measure.map_apply ((hG n).comp hrightPair) measurableSet_Iic]
  apply measure_mono_ae
  filter_upwards [hcompare] with sample hsample hmem
  exact (hsample n).trans hmem

/-- The marginal endpoint comparison of Wang Yiyang, *Asymptotic Speed of
the N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 3, Lemma 3.15, with the initial law specialized to a Dirac measure. -/
private theorem RootIndexed.restartedRealPositionMinimum_lowerTailDominates
    {Root α : Type*} [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 0 < N) (roots : Finset Root) (initialPosition : Root → ℝ)
    (hleftFinite : ∀ᵐ ξ ∂μ, ξ.IsLeftLocallyFinite)
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
  let hpopulation (k : ℕ) :
      Measurable (fun sample : Unit × RootIndexed.StepField Root α ℝ =>
        finiteSlices.toFinset k sample.2) :=
    ((finiteSlices.measurable_toFinset k).mono (ℱ.le k) le_rfl).comp measurable_snd
  obtain ⟨_, _, _, _, _, horder⟩ :=
    RootIndexed.restartedRealPositionCoupling_of_randomInitial μ (Measure.dirac ()) N hN roots
      (fun _ : Unit => initialPosition) measurable_const (fun _ => selectedPopulation)
      (fun _ => finiteSlices) hpopulation hleftFinite
      (Filter.Eventually.of_forall fun _ field => ⟨initialInjection field⟩)
  have hτ (sample : Unit × RootIndexed.StepField Root α ℝ) :
      finsetPopulationOverflowTime (fun k (s : Unit × RootIndexed.StepField Root α ℝ) =>
        finiteSlices.toFinset k s.2) N sample = τ sample.2 := by
    apply WithTop.eq_of_forall_le_coe_iff
    intro k
    exact (finsetPopulationOverflowTime_le_iff
      (fun j (s : Unit × RootIndexed.StepField Root α ℝ) => finiteSlices.toFinset j s.2)
      N k sample).trans
      (finsetPopulationOverflowTime_le_iff finiteSlices.toFinset N k sample.2).symm
  have hmarginal : ((Measure.dirac ()).prod Q).map Prod.snd = Q := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hFmap : ((Measure.dirac ()).prod Q).map (F ∘ Prod.snd) = Q.map F := by
    rw [← Measure.map_map hF measurable_snd, hmarginal]
  have hGmap : ((Measure.dirac ()).prod Q).map (G ∘ Prod.snd) = Q.map G := by
    rw [← Measure.map_map hG measurable_snd, hmarginal]
  have hspecialized : (((Measure.dirac ()).prod Q).map (F ∘ Prod.snd)).LowerTailDominates
      (((Measure.dirac ()).prod Q).map (G ∘ Prod.snd)) := by
    simpa only [F, G, Function.comp_def, hτ, Q] using horder n
  rwa [hFmap, hGmap] at hspecialized

set_option backward.isDefEq.respectTransparency false

/-- The lower-tail conclusion of Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 3, Lemma 3.15. Finite ancestral restrictions remove the finite-slice
condition: the original population may be infinite at and after overflow. -/
theorem RootIndexed.measure_selectedPopulation_lowerTail_le_firstN
    {Root α : Type*} [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 0 < N) (roots : Finset Root) (initial : Root → ℝ)
    (hleftFinite : ∀ᵐ ξ ∂μ, ξ.IsLeftLocallyFinite)
    (P : RootIndexed.CausalPopulation (RootIndexed.StepField Root α ℝ) Root α ℝ
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ)) id)
    (initialOrder : ∀ field, Order.DominatingMap (P 0 field)
      (↑(RootIndexed.initialPopulation (α := α) roots) : Set (RootIndexed.TreeNode Root α))
      (fun p => initial p.1) (fun q => initial q.1))
    (n : ℕ) (x : ℝ) :
    let Q := RootIndexed.stepFieldLaw (Root := Root) μ
    Q {field | (n : WithTop ℕ) ≤ populationOverflowTime P N field ∧
      ∃ p ∈ P n field, RootIndexed.position initial id field p.1 p.2 ≤ x} ≤
    Q {field | (RootIndexed.selectedPopulationTotalized N roots initial id id n field).inf
      (fun q => ((RootIndexed.position initial id field q.1 q.2 : ℝ) : WithTop ℝ)) ≤ x} := by
  intro Q
  let ℱ := RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ)
  let G (field : RootIndexed.StepField Root α ℝ) :=
    (RootIndexed.selectedPopulationTotalized N roots initial id id n field).inf
      (fun q => ((RootIndexed.position initial id field q.1 q.2 : ℝ) : WithTop ℝ))
  let A (s : Finset (RootIndexed.TreeNode Root α)) :=
    {field | (n : WithTop ℕ) ≤ populationOverflowTime P N field ∧
      ∃ p ∈ P.restrictAncestors s n field,
        RootIndexed.position initial id field p.1 p.2 ≤ x}
  have hunion : {field | (n : WithTop ℕ) ≤ populationOverflowTime P N field ∧
      ∃ p ∈ P n field, RootIndexed.position initial id field p.1 p.2 ≤ x} = ⋃ s, A s := by
    ext field
    constructor
    · rintro ⟨hn, p, hp, hx⟩
      obtain ⟨s, hs⟩ := P.exists_mem_restrictAncestors hp
      exact Set.mem_iUnion.mpr ⟨s, hn, p, hs, hx⟩
    · intro h
      obtain ⟨s, hn, p, hp, hx⟩ := Set.mem_iUnion.mp h
      exact ⟨hn, p, hp.1, hx⟩
  have hdir : Directed (· ⊆ ·) A := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · rintro field ⟨hn, p, hp, hx⟩
      exact ⟨hn, p, P.restrictAncestors_mono Finset.subset_union_left n field hp, hx⟩
    · rintro field ⟨hn, p, hp, hx⟩
      exact ⟨hn, p, P.restrictAncestors_mono Finset.subset_union_right n field hp, hx⟩
  rw [hunion, hdir.measure_iUnion]
  apply iSup_le
  intro s
  let Ps := P.restrictAncestors s
  let hs := P.restrictAncestors_finiteSlices s
  let τs := finsetPopulationOverflowTime hs.toFinset N
  let F (field : RootIndexed.StepField Root α ℝ) :=
    if (n : WithTop ℕ) ≤ τs field then
      (hs.toFinset n field).inf fun p =>
        ((RootIndexed.position initial id field p.1 p.2 : ℝ) : WithTop ℝ)
    else ⊤
  have hi (field) : Order.DominatingMap
      (↑(hs.toFinset 0 field) : Set (RootIndexed.TreeNode Root α))
      (↑(RootIndexed.initialPopulation (α := α) roots) : Set (RootIndexed.TreeNode Root α))
      (fun p => initial p.1) (fun q => initial q.1) :=
    { toFun := initialOrder field
      mapsTo := fun p hp => (initialOrder field).mapsTo
        (P.restrictAncestors_subset s 0 field ((hs.mem_toFinset 0 field p).mp hp))
      injOn := fun p hp q hq he => (initialOrder field).injOn
        (P.restrictAncestors_subset s 0 field ((hs.mem_toFinset 0 field p).mp hp))
        (P.restrictAncestors_subset s 0 field ((hs.mem_toFinset 0 field q).mp hq)) he
      dominates := fun p hp => (initialOrder field).dominates p
        (P.restrictAncestors_subset s 0 field ((hs.mem_toFinset 0 field p).mp hp)) }
  have horder := RootIndexed.restartedRealPositionMinimum_lowerTailDominates
    μ N hN roots initial hleftFinite Ps hs hi n
  have hpos (p : RootIndexed.TreeNode Root α) : Measurable fun field =>
      RootIndexed.position initial id field p.1 p.2 :=
    (RootIndexed.position_measurable initial id measurable_id p.1 p.2).mono
      (ℱ.le p.2.length) le_rfl
  have hstop : IsStoppingTime ℱ τs := by
    apply populationOverflowTime_isStoppingTime_of_countable
    intro k
    exact (measurable_of_countable
      (fun f : Finset (RootIndexed.TreeNode Root α) => (↑f : Set (RootIndexed.TreeNode Root α)))).comp
      (hs.measurable_toFinset k)
  have hF : Measurable F := (measurable_finsetMinimum
    ((hs.measurable_toFinset n).mono (ℱ.le n) le_rfl) hpos).piecewise
      (ℱ.le n _ (hstop.measurableSet_ge_of_countable n)) measurable_const
  have hG : Measurable G := measurable_finsetMinimum
    ((RootIndexed.selectedPopulationTotalized_adapted N roots initial id measurable_id
      id measurable_id n).mono (ℱ.le n) le_rfl) hpos
  have hlow : Q {field | F field ≤ (x : WithTop ℝ)} ≤ Q {field | G field ≤ x} := by
    have h := horder (x : WithTop ℝ)
    simp only [F, G, Q, τs] at hF hG ⊢
    rw [Measure.map_apply hF measurableSet_Iic, Measure.map_apply hG measurableSet_Iic] at h
    exact h
  dsimp only [G] at hlow
  apply (measure_mono (t := {field | F field ≤ (x : WithTop ℝ)}) ?_).trans hlow
  rintro field ⟨hn, p, hp, hx⟩
  have hτ : (n : WithTop ℕ) ≤ τs field := by
    by_contra h
    have hlt := lt_of_not_ge h
    obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp
      (ne_top_of_lt hlt)
    have hjlt : (j : WithTop ℕ) < (n : WithTop ℕ) := by rwa [← hj] at hlt
    have hover := card_gt_of_finsetPopulationOverflowTime_eq hs.toFinset N j field hj.symm
    have hjP : (j : WithTop ℕ) < populationOverflowTime P N field := hjlt.trans_le hn
    have hb := encard_le_of_lt_populationOverflowTime P N j field hjP
    have hsub : (↑(hs.toFinset j field) : Set (RootIndexed.TreeNode Root α)) ⊆ P j field :=
      fun q hq => (P.restrictAncestors_subset s j field) ((hs.mem_toFinset j field q).mp hq)
    have hc := (Set.encard_mono hsub).trans hb
    rw [encard_coe_finset, ENat.natCast_le_natCast] at hc
    omega
  change F field ≤ (x : WithTop ℝ)
  simp only [F, ite_eq_left hτ]
  exact (Finset.inf_le ((hs.mem_toFinset n field p).mpr hp)).trans (WithTop.coe_le_coe.mpr hx)


set_option backward.isDefEq.respectTransparency false in
/-- The stopped minimum comparison bounds the original first-`N` endpoint
law by terminal avoidance in any causal comparison population and capacity
failure. See Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk
with Infinite Offspring* (Fudan University, 2026), Chapter 3, Lemma 3.15. -/
theorem RootIndexed.measure_endpointMinimum_gt_le_terminalAvoidance_add_capacityFailure
    {Root α : Type*} [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)] [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 0 < N) (roots : Finset Root) (initialPosition : Root → ℝ)
    (hleftFinite : ∀ᵐ ξ ∂μ, ξ.IsLeftLocallyFinite)
    (P : RootIndexed.CausalPopulation (RootIndexed.StepField Root α ℝ) Root α ℝ
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ)) id)
    (initialInjection : ∀ field, Order.DominatingMap
      (P 0 field)
      (↑(RootIndexed.initialPopulation (α := α) roots) : Set (RootIndexed.TreeNode Root α))
      (fun p => initialPosition p.1) (fun q => initialPosition q.1))
    (n : ℕ) (x : ℝ) :
    let Q := RootIndexed.stepFieldLaw (Root := Root) μ
    Q {field | (x : WithTop ℝ) <
      (RootIndexed.selectedPopulationTotalized N roots initialPosition id id n field).inf
        (fun p => ((RootIndexed.position initialPosition id field p.1 p.2 : ℝ) : WithTop ℝ))} ≤
      Q {field | ¬ ∃ p ∈ P n field, RootIndexed.position initialPosition id field p.1 p.2 ≤ x} +
        Q (P.capacityEvent N n)ᶜ := by
  intro Q
  let ℱ := RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ)
  let τ := populationOverflowTime P N
  let A := {field | (n : WithTop ℕ) ≤ τ field ∧
    ∃ p ∈ P n field, RootIndexed.position initialPosition id field p.1 p.2 ≤ x}
  let G (field : RootIndexed.StepField Root α ℝ) :=
    (RootIndexed.selectedPopulationTotalized N roots initialPosition id id n field).inf
      fun p => ((RootIndexed.position initialPosition id field p.1 p.2 : ℝ) : WithTop ℝ)
  have hpos (p : RootIndexed.TreeNode Root α) : Measurable fun field =>
      RootIndexed.position initialPosition id field p.1 p.2 :=
    (RootIndexed.position_measurable initialPosition id measurable_id p.1 p.2).mono
      (ℱ.le p.2.length) le_rfl
  have hstop : IsStoppingTime ℱ τ :=
    populationOverflowTime_isStoppingTime_of_countable ℱ P (fun k => by
      have hm := fun p => P.measurable_mem k p
      let : MeasurableSpace (RootIndexed.StepField Root α ℝ) := ℱ k
      exact measurable_set_iff.mpr hm) N
  have hA : MeasurableSet A := by
    change MeasurableSet ({field | (n : WithTop ℕ) ≤ τ field} ∩
      {field | ∃ p ∈ P n field, RootIndexed.position initialPosition id field p.1 p.2 ≤ x})
    apply (ℱ.le n _ (hstop.measurableSet_ge_of_countable n)).inter
    have heq : {field | ∃ p ∈ P n field,
        RootIndexed.position initialPosition id field p.1 p.2 ≤ x} =
        ⋃ p, {field | p ∈ P n field} ∩
          {field | RootIndexed.position initialPosition id field p.1 p.2 ≤ x} := by ext field; simp
    rw [heq]
    exact MeasurableSet.iUnion fun p =>
      (measurableSet_setOfPred.2 ((P.measurable_mem n p).mono (ℱ.le n) le_rfl)).inter
        (measurableSet_le (hpos p) measurable_const)
  have hG : Measurable G := measurable_finsetMinimum
    ((RootIndexed.selectedPopulationTotalized_adapted N roots initialPosition
      id measurable_id id measurable_id n).mono (ℱ.le n) le_rfl) hpos
  have hlow := RootIndexed.measure_selectedPopulation_lowerTail_le_firstN
    μ N hN roots initialPosition hleftFinite P initialInjection n x
  have hstrict : Q {field | (x : WithTop ℝ) < G field} ≤ Q Aᶜ := by
    have heq : {field | (x : WithTop ℝ) < G field} = {field | G field ≤ x}ᶜ := by
      ext field; simp
    rw [heq, prob_compl_eq_one_sub (measurableSet_le hG measurable_const),
      prob_compl_eq_one_sub hA]
    exact tsub_le_tsub_left hlow 1
  refine hstrict.trans ((measure_mono ?_).trans (measure_union_le _ _))
  intro field hh
  by_cases hcap : field ∈ P.capacityEvent N n
  · left
    rintro ⟨p, hp, hx⟩
    apply hh
    refine ⟨?_, p, hp, hx⟩
    apply le_of_lt
    apply lt_of_not_ge
    intro hover
    obtain ⟨j, hj, hjover⟩ := (populationOverflowTime_le_iff P N n field).mp hover
    exact (not_lt_of_ge ((P.mem_capacityEvent_iff N n field).mp hcap j hj)) hjover
  · exact Or.inr hcap

/-- Random-initial version of the stopped comparison in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 3, Lemma 3.15. The coupled initial pair
is independent of the offspring field. No finite-slice or moment hypothesis
is imposed on the selected population. -/
theorem RootIndexed.measure_selectedPopulation_lowerTail_le_firstN_of_randomInitial
    {Initial Root α : Type*} [MeasurableSpace Initial] [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (initialLaw : Measure Initial) [IsProbabilityMeasure initialLaw]
    (N : ℕ) (hN : 0 < N) (roots : Finset Root)
    (initial : Initial → Root → ℝ) (hinitial : Measurable initial)
    (P : Initial → RootIndexed.CausalPopulation (RootIndexed.StepField Root α ℝ) Root α ℝ
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ)) id)
    (hpopulation : ∀ k, Measurable
      (fun sample : Initial × RootIndexed.StepField Root α ℝ => P sample.1 k sample.2))
    (hleftFinite : ∀ᵐ ξ ∂μ, ξ.IsLeftLocallyFinite)
    (initialOrder : ∀ᵐ a ∂initialLaw, ∀ field, Nonempty (Order.DominatingMap
      (P a 0 field)
      (↑(RootIndexed.initialPopulation (α := α) roots) : Set (RootIndexed.TreeNode Root α))
      (fun p => initial a p.1) (fun q => initial a q.1)))
    (n : ℕ) (x : ℝ) :
    let Q := RootIndexed.stepFieldLaw (Root := Root) μ
    let population := fun k (sample : Initial × RootIndexed.StepField Root α ℝ) =>
      P sample.1 k sample.2
    (initialLaw.prod Q) {sample |
      (n : WithTop ℕ) ≤ populationOverflowTime population N sample ∧
      ∃ p ∈ population n sample,
        RootIndexed.position (initial sample.1) id sample.2 p.1 p.2 ≤ x} ≤
    (initialLaw.prod Q) {sample |
      (RootIndexed.selectedPopulationTotalized N roots (initial sample.1) id id n sample.2).inf
        (fun q => ((RootIndexed.position (initial sample.1) id sample.2 q.1 q.2 : ℝ) : WithTop ℝ)) ≤ x} := by
  intro Q population
  let τ := populationOverflowTime population N
  let A := {sample : Initial × RootIndexed.StepField Root α ℝ |
    (n : WithTop ℕ) ≤ τ sample ∧ ∃ p ∈ population n sample,
      RootIndexed.position (initial sample.1) id sample.2 p.1 p.2 ≤ x}
  let G (sample : Initial × RootIndexed.StepField Root α ℝ) :=
    (RootIndexed.selectedPopulationTotalized N roots (initial sample.1) id id n sample.2).inf
      (fun q => ((RootIndexed.position (initial sample.1) id sample.2 q.1 q.2 : ℝ) : WithTop ℝ))
  have hinput : Measurable (fun sample : Initial × RootIndexed.StepField Root α ℝ =>
      (initial sample.1, sample.2)) := (hinitial.comp measurable_fst).prodMk measurable_snd
  have hpos (p : RootIndexed.TreeNode Root α) : Measurable fun sample :
      Initial × RootIndexed.StepField Root α ℝ =>
      RootIndexed.position (initial sample.1) id sample.2 p.1 p.2 := by
    simpa [Function.comp_def, RootIndexed.observedPositionAtGeneration,
      RootIndexed.positionAtGeneration] using
      (RootIndexed.measurable_observedPositionAtGeneration_withInitialPosition p.2.length p).comp hinput
  have hstop : IsStoppingTime (⊤ : Filtration ℕ inferInstance) τ :=
    populationOverflowTime_isStoppingTime_of_countable ⊤ population hpopulation N
  have hA : MeasurableSet A := by
    have hex : MeasurableSet {sample : Initial × RootIndexed.StepField Root α ℝ |
        ∃ p ∈ population n sample,
          RootIndexed.position (initial sample.1) id sample.2 p.1 p.2 ≤ x} := by
      simp only [show {sample : Initial × RootIndexed.StepField Root α ℝ |
          ∃ p ∈ population n sample,
            RootIndexed.position (initial sample.1) id sample.2 p.1 p.2 ≤ x} =
          ⋃ p, {sample | p ∈ population n sample} ∩
            {sample | RootIndexed.position (initial sample.1) id sample.2 p.1 p.2 ≤ x} by
          ext sample; simp]
      exact MeasurableSet.iUnion fun p =>
        (measurableSet_setOfPred.2 (measurable_set_iff.mp (hpopulation n) p)).inter
          (measurableSet_le (hpos p) measurable_const)
    exact ((⊤ : Filtration ℕ _).le n _ (hstop.measurableSet_ge_of_countable n)).inter hex
  have hG : Measurable G := measurable_finsetMinimum
    ((RootIndexed.measurable_selectedPopulationTotalized_withInitialPosition N roots n).comp hinput) hpos
  dsimp only [G] at hG
  change (initialLaw.prod Q) A ≤ (initialLaw.prod Q) {sample | _ ≤ (x : WithTop ℝ)}
  rw [Measure.prod_apply hA, Measure.prod_apply (measurableSet_le hG measurable_const)]
  apply lintegral_mono_ae
  filter_upwards [initialOrder] with a ha
  have hτ (field : RootIndexed.StepField Root α ℝ) :
      τ (a, field) = populationOverflowTime (P a) N field := by
    apply WithTop.eq_of_forall_le_coe_iff
    intro k
    exact (populationOverflowTime_le_iff population N k (a, field)).trans
      (populationOverflowTime_le_iff (P a) N k field).symm
  simpa only [A, G, Set.preimage_ofPred_eq, hτ, population] using
    RootIndexed.measure_selectedPopulation_lowerTail_le_firstN μ N hN roots (initial a)
      hleftFinite (P a) (fun field => (ha field).some) n x

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

end
