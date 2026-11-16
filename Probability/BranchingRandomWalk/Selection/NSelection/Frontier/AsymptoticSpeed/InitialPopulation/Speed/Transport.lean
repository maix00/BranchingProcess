/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Processes.Selected.ParameterizedRootIndexed
public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Selection.PopulationBatch
public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.InitialPopulation.Trajectory.RunBridge
public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.InfiniteOffspring.Repair
public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.InfiniteOffspring.Speed
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.InfiniteOffspring.Kingman.Lemmas.ArrayStructure
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.InfiniteOffspring.Kingman.Limit
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
/-!
# Speed transport for a random initial population

## Public declarations

- `selectedPopulationEndpointWithParameter_eq_rankZero`: when the selected
  population has cardinality $N$, its minimum endpoint equals the position
  of its rank-zero particle.
- `selectedPopulationEndpointTrajectoryWithParameter`:
  $n\mapsto$ the minimum endpoint at generation $n$ for a parameterized
  initial-position vector and a pre-sampled root field.
- `measurable_selectedPopulationEndpointTrajectoryWithParameter`: each fixed
  generation endpoint is measurable in the initial vector and root field.
- `ae_selectedPopulationEndpointTrajectoryWithParameter_prod_of_stepLaw`:
  under boundary normalization, nonempty offspring, and the leftmost first
  moment condition, there is a speed shared almost surely under the product
  of any initial-position law and the canonical root-field law.

- `selectedPopulationEndpointTrajectory_ae_hasAsymptoticSpeed_and_L1_of_stepLaw`:
  under the same assumptions, each deterministic full-capacity start has
  $M_n/n\to v_N$ almost surely and in $L^1$ on the root-field law.

- `integral_fullCapacityEndpoint_div_le_speed`: from $N$ zero-position
  particles, $mathbb E[M_H]/Hle v_N$ at every positive horizon $H$.

Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026), Chapter 3, Corollary 3.13, gives the
comparison with constant initial positions.

This file connects the measurable endpoint of a selected population with the
rank-zero trajectory used by the exact-capacity speed theorem.
-/

open Asymptotics MeasureTheory Filter
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

open Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed

attribute [local instance] Classical.propDecidable Classical.decEq

/-- When the selected population has full size, its minimum endpoint is the
position of its rank-zero particle. -/
theorem selectedPopulationEndpointWithParameter_eq_rankZero
    (N n : ℕ) (hN : 0 < N) (initial : Fin N → ℝ)
    [treeOrder : LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (field : RootIndexed.StepField (Fin N) ℕ ℝ)
    (hcard : (RootIndexed.selectedPopulationTotalized N Finset.univ
      initial id id n field).card = N) :
    selectedPopulationEndpointWithParameter N N n (initial, field) =
      selectedPopulationRankPosition N n initial field ⟨0, hN⟩ := by
  letI : Preorder (RootIndexed.TreeNode (Fin N) ℕ) := treeOrder.toPreorder
  let population := RootIndexed.selectedPopulationTotalized N Finset.univ
    initial id id n field
  let value := RootIndexed.observedPositionAtGeneration initial id id n field
  let root := selectedPopulationRankRoot N n initial field ⟨0, hN⟩
  have hroot := selectedPopulationRankRoot_mem_and_rank_of_card
    N n initial field ⟨0, hN⟩ (by simpa [population] using hcard)
  have hfilter := hroot.2
  rw [Combinatorics.Selection.NSelection.rankBy_eq_card_filter] at hfilter
  have hminimum : ∀ q ∈ population, value root ≤ value q := by
    intro q hq
    by_contra hnot
    have hlt : value q < value root := lt_of_not_ge hnot
    have hmem : q ∈ (RootIndexed.selectedPopulationTotalized N Finset.univ
        initial id id n field).filter (fun r =>
        Combinatorics.Selection.NSelection.valueKey
            (RootIndexed.observedPositionAtGeneration initial id id n field) r <
          Combinatorics.Selection.NSelection.valueKey
            (RootIndexed.observedPositionAtGeneration initial id id n field)
            (selectedPopulationRankRoot N n initial field ⟨0, hN⟩)) :=
      Finset.mem_filter.mpr
        ⟨by simpa [population] using hq,
          Combinatorics.Selection.NSelection.valueKey_lt_of_value_lt
            (RootIndexed.observedPositionAtGeneration initial id id n field) hlt⟩
    have hpos : 0 < {r ∈ RootIndexed.selectedPopulationTotalized N Finset.univ
        initial id id n field |
        Combinatorics.Selection.NSelection.valueKey
            (RootIndexed.observedPositionAtGeneration initial id id n field) r <
          Combinatorics.Selection.NSelection.valueKey
            (RootIndexed.observedPositionAtGeneration initial id id n field)
            (selectedPopulationRankRoot N n initial field ⟨0, hN⟩)}.card := by
      exact Finset.card_pos.mpr ⟨q, hmem⟩
    have hfilterZero : ({r ∈ RootIndexed.selectedPopulationTotalized N Finset.univ
        initial id id n field |
        Combinatorics.Selection.NSelection.valueKey
            (RootIndexed.observedPositionAtGeneration initial id id n field) r <
          Combinatorics.Selection.NSelection.valueKey
            (RootIndexed.observedPositionAtGeneration initial id id n field)
            (selectedPopulationRankRoot N n initial field ⟨0, hN⟩)}).card = 0 := by
      simpa [Fin.val_mk] using hfilter
    omega
  have hrootMem : root ∈ population := by
    simpa [population, root] using hroot.1
  have hpop : population.Nonempty := ⟨root, hrootMem⟩
  have hinf : population.inf' hpop value = value root := by
    apply le_antisymm
    · exact Finset.inf'_le value hrootMem
    · apply Finset.le_inf'
      intro q hq
      exact hminimum q hq
  have hendpoint : selectedPopulationEndpointWithParameter N N n (initial, field) =
      population.inf' hpop value := by
    change (if h : population.Nonempty then population.inf' h value else 0) = _
    rw [dite_eq_left hpop]
  rw [hendpoint]
  rw [hinf]
  rfl

/-- The local endpoint trajectory starting from a parameterized position
vector and driven by a pre-sampled root field. -/
noncomputable def selectedPopulationEndpointTrajectoryWithParameter
    (N : ℕ) [DecidableEq (RootIndexed.TreeNode (Fin N) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (p : (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ) :
    ℕ → ℝ := fun n => selectedPopulationEndpointWithParameter N N n p

theorem measurable_selectedPopulationEndpointTrajectoryWithParameter
    (N n : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin N) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin N) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin N) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)] :
    Measurable (fun p : (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ =>
      selectedPopulationEndpointTrajectoryWithParameter N p n) := by
  simpa [selectedPopulationEndpointTrajectoryWithParameter] using
    measurable_selectedPopulationEndpointWithParameter N N n

private lemma ae_selectedPopulationEndpointTrajectoryWithParameter_sections
    {N : ℕ} (hN : 0 < N)
    (envLaw : Measure (GenerationEnvironment N))
    (fieldLaw : Measure (RootIndexed.StepField (Fin N) ℕ ℝ))
    [IsProbabilityMeasure envLaw] [IsProbabilityMeasure fieldLaw]
    (originPosition : ℕ → GenerationEnvironment N → ℝ) (speed : ℝ)
    (horiginPosition : ∀ n ω,
      originPosition n ω =
        (measurableRepairedInfiniteOffspringRun n
          ((fun _ : Fin N => (0 : ℝ)), ω)) ⟨0, hN⟩)
    (hspeedMeasurable : MeasurableSet
      {ω : GenerationEnvironment N |
        HasAsymptoticSpeed (𝕜 := ℝ) (originPosition · ω) speed})
    (hspeedRepaired : ∀ᵐ ω ∂envLaw,
      HasAsymptoticSpeed (𝕜 := ℝ) (originPosition · ω) speed)
    (hgoodEnv : ∀ᵐ ω ∂envLaw, ∀ n,
      IsGoodInfiniteOffspringBatch (ω n))
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSpace (RootIndexed.TreeNode (Fin N) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (Fin N × RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (Fin N → Fin N × RootIndexed.TreeNode (Fin N) ℕ)]
    (hbatchLaw : ∀ initial : Fin N → ℝ, HasLaw
      (fun field n => selectedRootBatch
        (selectedPopulationRankRoots N initial) n field) envLaw fieldLaw) :
    ∀ initial : Fin N → ℝ, ∀ᵐ field ∂fieldLaw,
      HasAsymptoticSpeed (𝕜 := ℝ)
        (selectedPopulationEndpointTrajectoryWithParameter N
          (initial, field)) speed := by
  classical
  have hgoodMeas : MeasurableSet
      {ω : GenerationEnvironment N | ∀ n,
        IsGoodInfiniteOffspringBatch (ω n)} := by
    have hEq : {ω : GenerationEnvironment N | ∀ n,
        IsGoodInfiniteOffspringBatch (ω n)} =
        ⋂ n : ℕ, {ω : GenerationEnvironment N |
          IsGoodInfiniteOffspringBatch (ω n)} := by
      ext ω
      simp
    rw [hEq]
    apply MeasurableSet.iInter
    intro n
    have hbatch : MeasurableSet
        {batch : GenerationBatch N | IsGoodInfiniteOffspringBatch batch} := by
      simpa [IsRepairableBatch] using isRepairableBatch_measurable
    change MeasurableSet ((fun ω : GenerationEnvironment N => ω n) ⁻¹'
      {batch : GenerationBatch N | IsGoodInfiniteOffspringBatch batch})
    exact hbatch.preimage (measurable_pi_apply n)
  intro initial
  let rowMap : RootIndexed.StepField (Fin N) ℕ ℝ →
      GenerationEnvironment N := fun field n =>
        selectedRootBatch (selectedPopulationRankRoots N initial) n field
  have hrowLaw := hbatchLaw initial
  have hrepRaw : ∀ᵐ field ∂fieldLaw,
      HasAsymptoticSpeed (𝕜 := ℝ)
        (fun n => originPosition n (rowMap field)) speed := by
    have h := (hrowLaw.ae_iff (p := fun ω : GenerationEnvironment N =>
        HasAsymptoticSpeed (𝕜 := ℝ) (originPosition · ω) speed)
        (measurableSet_setOfPred.mp hspeedMeasurable)).mpr hspeedRepaired
    simpa [rowMap] using h
  have hgoodRaw : ∀ᵐ field ∂fieldLaw, ∀ n,
      IsGoodInfiniteOffspringBatch (rowMap field n) := by
    have h := (hrowLaw.ae_iff (p := fun ω : GenerationEnvironment N =>
        ∀ n, IsGoodInfiniteOffspringBatch (ω n))
        (measurableSet_setOfPred.mp hgoodMeas)).mpr hgoodEnv
    simpa [rowMap] using h
  filter_upwards [hrepRaw, hgoodRaw] with field hrep hgood
  have hmarks : (fun n => repairGenerationBatch (rowMap field n)) =
      rowMap field := by
    funext n
    exact repairGenerationBatch_eq_of_repairable
      (rowMap field n) (hgood n)
  have horigin : HasAsymptoticSpeed (𝕜 := ℝ)
      (fun n => infiniteOffspringRun (rowMap field) hgood
        (fun _ => 0) n ⟨0, hN⟩) speed := by
    change Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ *
        infiniteOffspringRun (rowMap field) hgood (fun _ => 0) n ⟨0, hN⟩)
      atTop (𝓝 speed)
    apply hrep.congr'
    filter_upwards [] with n
    have hrun : originPosition n (rowMap field) =
        infiniteOffspringRun (rowMap field) hgood (fun _ => 0) n ⟨0, hN⟩ := by
      rw [horiginPosition]
      rw [measurableRepairedInfiniteOffspringRun_eq_infiniteOffspringRun]
      exact congrFun (infiniteOffspringRun_congr
        (fun n => repairGenerationBatch (rowMap field n)) (rowMap field)
        hmarks (fun n => repairGenerationBatch_repairable (rowMap field n))
        hgood (fun _ => 0) n) ⟨0, hN⟩
    rw [hrun]
    simp [smul_eq_mul]
  have hrankSpeed := selectedPopulationRankPosition_hasAsymptoticSpeed_of_originRun
    hN initial field hgood speed horigin
  have hcards := selectedPopulationTotalized_card_eq_of_rankedBatches_good
    N initial field hgood
  have hendpoint (n : ℕ) :
      selectedPopulationEndpointWithParameter N N n (initial, field) =
        selectedPopulationRankPosition N n initial field ⟨0, hN⟩ := by
    apply selectedPopulationEndpointWithParameter_eq_rankZero N n hN initial field
    have hcardN :
        (RootIndexed.selectedPopulationTotalized N Finset.univ
          initial id id n field).card = N := by
      exact hcards n
    simpa [selectedPopulationWithParameter] using hcardN
  change Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
    selectedPopulationEndpointTrajectoryWithParameter N (initial, field) n)
    atTop (𝓝 speed)
  apply hrankSpeed.congr'
  filter_upwards [] with n
  simp [selectedPopulationEndpointTrajectoryWithParameter, hendpoint n]

set_option maxHeartbeats 3000000
theorem selectedPopulationEndpointTrajectory_ae_hasAsymptoticSpeed_and_L1_of_stepLaw
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    {N : ℕ} (hN : 0 < N) (L : StepLaw ι ℕ X)
    [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hfirst : HasLeftmostFirstMoment L)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSpace (RootIndexed.TreeNode (Fin N) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (Fin N × RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (Fin N → Fin N × RootIndexed.TreeNode (Fin N) ℕ)] :
    ∃ speed : ℝ, ∀ initial : Fin N → ℝ,
      let P := RootIndexed.stepFieldLaw (Root := Fin N) L.sortedPotentialImage
      let endpoint := fun field =>
        selectedPopulationEndpointTrajectoryWithParameter N (initial, field)
      (∀ᵐ field ∂P, HasAsymptoticSpeed (𝕜 := ℝ) (endpoint field) speed) ∧
      Tendsto (fun n : ℕ => eLpNorm (fun field =>
        (n : ℝ)⁻¹ * endpoint field n - speed) 1 P) atTop (𝓝 0) := by
  classical
  let μ := L.sortedPotentialImage
  let envLaw := generationEnvironmentLaw μ N
  let fieldLaw := RootIndexed.stepFieldLaw (Root := Fin N) μ
  let _ : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  let _ : IsProbabilityMeasure envLaw := by
    exact generationEnvironmentLaw_isProbability μ N
  let _ : IsProbabilityMeasure fieldLaw := by
    dsimp [fieldLaw]
    infer_instance
  have hboundaryμ : HasBoundaryNormalization realPotential μ := by
    dsimp [μ]
    exact L.sortedPotentialImage_hasBoundaryNormalization hboundary
  have hnonemptyμ : μ nonemptySupport = 1 := by
    dsimp [μ]
    rw [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport]
    exact hnonempty
  obtain ⟨c, horiginSpeed, hL1⟩ :=
    infiniteOffspringRun_leftmost_ae_hasAsymptoticSpeed_and_L1_of_stepLaw
      hN L hboundary hnonempty hfirst
  let speed := -c
  let originPosition : ℕ → GenerationEnvironment N → ℝ := fun n ω =>
    (measurableRepairedInfiniteOffspringRun n
      ((fun _ : Fin N => (0 : ℝ)), ω)) ⟨0, hN⟩
  have horiginMeasurable (n : ℕ) : Measurable (originPosition n) := by
    dsimp [originPosition]
    exact (measurable_pi_apply (⟨0, hN⟩ : Fin N)).comp
      ((measurable_measurableRepairedInfiniteOffspringRun n).comp
        (measurable_const.prodMk measurable_id))
  have hscaledMeasurable (n : ℕ) : Measurable (fun ω =>
      (n : ℝ)⁻¹ * originPosition n ω) :=
    measurable_const.mul (horiginMeasurable n)
  have hspeedMeasurable : MeasurableSet
      {ω : GenerationEnvironment N |
        HasAsymptoticSpeed (𝕜 := ℝ) (fun n => originPosition n ω) speed} := by
    change MeasurableSet {ω : GenerationEnvironment N |
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * originPosition n ω)
        atTop (𝓝 speed)}
    exact measurableSet_tendsto (𝓝 speed) hscaledMeasurable
  have hgoodEnv : ∀ᵐ ω ∂envLaw, ∀ n,
      IsGoodInfiniteOffspringBatch (ω n) := by
    dsimp [envLaw, μ]
    exact generationEnvironmentLaw_ae_allGood L.sortedPotentialImage
      hboundaryμ hnonemptyμ N
  have hspeedRepaired : ∀ᵐ ω ∂envLaw,
      HasAsymptoticSpeed (𝕜 := ℝ) (originPosition · ω) speed := by
    filter_upwards [hgoodEnv, horiginSpeed] with ω hgood hspeed
    rcases hspeed with ⟨hgood', hlimit⟩
    have hrepairMarks :
        (fun n => repairGenerationBatch (ω n)) = ω := by
      funext n
      exact repairGenerationBatch_eq_of_repairable (ω n) (hgood n)
    have hrun (n : ℕ) : originPosition n ω =
        infiniteOffspringRun ω hgood' (fun _ => 0) n ⟨0, hN⟩ := by
      dsimp [originPosition]
      rw [measurableRepairedInfiniteOffspringRun_eq_infiniteOffspringRun]
      exact congrFun (infiniteOffspringRun_congr
        (fun n => repairGenerationBatch (ω n)) ω hrepairMarks
        (fun n => repairGenerationBatch_repairable (ω n)) hgood'
        (fun _ => 0) n) ⟨0, hN⟩
    change Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * originPosition n ω) atTop (𝓝 speed)
    apply hlimit.congr'
    filter_upwards [] with n
    rw [hrun n]
    rfl
  have hbatchLaw (initial : Fin N → ℝ) : HasLaw
      (fun field n => selectedRootBatch
        (selectedPopulationRankRoots N initial) n field)
      envLaw fieldLaw := by
    dsimp [envLaw, fieldLaw, μ]
    exact selectedPopulationRankBatch_hasLaw_generationEnvironment
      N initial L.sortedPotentialImage
  have hsections :=
    ae_selectedPopulationEndpointTrajectoryWithParameter_sections
      hN envLaw fieldLaw originPosition speed
      (by intro n ω; rfl) hspeedMeasurable hspeedRepaired hgoodEnv hbatchLaw
  refine ⟨speed, fun initial => ⟨hsections initial, ?_⟩⟩
  let rows (field : RootIndexed.StepField (Fin N) ℕ ℝ) : GenerationEnvironment N :=
    fun n => selectedRootBatch (selectedPopulationRankRoots N initial) n field
  have hrowLaw : HasLaw rows envLaw fieldLaw := hbatchLaw initial
  let K := ∑ i, |initial i|
  have hK (i : Fin N) : |initial i| ≤ K :=
    Finset.single_le_sum (fun j _ => abs_nonneg (initial j)) (Finset.mem_univ i)
  let error (n : ℕ) (field : RootIndexed.StepField (Fin N) ℕ ℝ) :=
    (n : ℝ)⁻¹ * selectedPopulationEndpointTrajectoryWithParameter N (initial, field) n - speed
  let originError (n : ℕ) (ω : GenerationEnvironment N) :=
    (n : ℝ)⁻¹ * originPosition n ω - speed
  have hmeasOrigin (n : ℕ) : Measurable (originError n) :=
    (hscaledMeasurable n).sub_const _
  have hmeasError (n : ℕ) : Measurable (error n) :=
    (measurable_const.mul
      ((measurable_selectedPopulationEndpointTrajectoryWithParameter N n).comp
        (measurable_const.prodMk measurable_id))).sub_const _
  have hgoodRaw : ∀ᵐ field ∂fieldLaw, ∀ t, IsGoodInfiniteOffspringBatch (rows field t) :=
    ae_of_ae_map hrowLaw.aemeasurable (hrowLaw.map_eq.symm ▸ hgoodEnv)
  have hbound (n : ℕ) : ∀ᵐ field ∂fieldLaw,
      |error n field| ≤ |originError n (rows field)| + (n : ℝ)⁻¹ * K := by
    filter_upwards [hgoodRaw] with field hgood
    let initialRank := selectedPopulationRankPosition N 0 initial field
    let i₀ : Fin N := ⟨0, hN⟩
    have hmin := selectedPopulationEndpointWithParameter_eq_rankZero N n hN initial field
      (selectedPopulationTotalized_card_eq_of_rankedBatches_good N initial field hgood n)
    have htraj := congrFun
      (selectedPopulationRankPosition_eq_infiniteOffspringRun N initial field hgood n) i₀
    have hmarks : (fun t => repairGenerationBatch (rows field t)) = rows field := by
      funext t
      exact repairGenerationBatch_eq_of_repairable _ (hgood t)
    have hzero : originPosition n (rows field) =
        infiniteOffspringRun (rows field) hgood (fun _ => 0) n i₀ := by
      dsimp [originPosition, i₀]
      rw [measurableRepairedInfiniteOffspringRun_eq_infiniteOffspringRun]
      exact congrFun (infiniteOffspringRun_congr _ _ hmarks _ hgood _ _) _
    have hinit (i : Fin N) : |initialRank i| ≤ K := by
      unfold initialRank selectedPopulationRankPosition RootIndexed.observedPositionAtGeneration
        RootIndexed.positionAtGeneration
      split
      · rename_i hlength
        have hnil := List.length_eq_zero_iff.mp hlength
        simp only [hnil, id_eq, RootIndexed.position, RootIndexed.displace,
          Combinatorics.Branching.displaceWith]
        simpa using hK _
      · simpa using (le_trans (abs_nonneg _) (hK i))
    have hlo := infiniteOffspringRun_mono_initial (rows field) hgood
      (fun _ => -K) initialRank (fun i => (abs_le.mp (hinit i)).1) n i₀
    have hhi := infiniteOffspringRun_mono_initial (rows field) hgood
      initialRank (fun _ => K) (fun i => (abs_le.mp (hinit i)).2) n i₀
    have hshift (a : ℝ) := congrFun
      (infiniteOffspringRun_shift (rows field) hgood (fun _ => 0) a n) i₀
    simp only [zero_add] at hshift
    rw [hshift] at hlo hhi
    have hdiff : |infiniteOffspringRun (rows field) hgood initialRank n i₀ -
        infiniteOffspringRun (rows field) hgood (fun _ => 0) n i₀| ≤ K := by
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    change |(n : ℝ)⁻¹ * selectedPopulationEndpointWithParameter N N n (initial, field) -
        speed| ≤ |(n : ℝ)⁻¹ * originPosition n (rows field) - speed| + (n : ℝ)⁻¹ * K
    rw [hmin, htraj, hzero]
    let scale : ℝ := (n : ℝ)⁻¹
    have hs : 0 ≤ scale := inv_nonneg.mpr (Nat.cast_nonneg _)
    calc
      _ ≤ |scale * infiniteOffspringRun (rows field) hgood (fun _ => 0) n i₀ - speed| +
          |scale * (infiniteOffspringRun (rows field) hgood initialRank n i₀ -
            infiniteOffspringRun (rows field) hgood (fun _ => 0) n i₀)| := by
        convert abs_add_le
          (scale * infiniteOffspringRun (rows field) hgood (fun _ => 0) n i₀ - speed)
          (scale * (infiniteOffspringRun (rows field) hgood initialRank n i₀ -
            infiniteOffspringRun (rows field) hgood (fun _ => 0) n i₀)) using 2 <;> ring
      _ ≤ _ := by rw [abs_mul, abs_of_nonneg hs]; gcongr
  have hL1rows (n : ℕ) :
      eLpNorm (originError n ∘ rows) 1 fieldLaw = eLpNorm (originError n) 1 envLaw := by
    rw [← eLpNorm_map_measure (hmeasOrigin n).aestronglyMeasurable hrowLaw.aemeasurable,
      hrowLaw.map_eq]
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * K) atTop (𝓝 0) := by
    simpa using ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const K)
  have hupper : Tendsto (fun n =>
      eLpNorm (originError n) 1 envLaw + ENNReal.ofReal ((n : ℝ)⁻¹ * K))
      atTop (𝓝 0) := by
    have hbase : Tendsto (fun n => eLpNorm (originError n) 1 envLaw) atTop (𝓝 0) := hL1
    have hcorrection : Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ)⁻¹ * K)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp hinv
    simpa only [add_zero] using hbase.add hcorrection
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper (fun _ => zero_le)
  intro n
  calc
    eLpNorm (error n) 1 fieldLaw ≤
        eLpNorm (fun field => |originError n (rows field)| + (n : ℝ)⁻¹ * K) 1 fieldLaw :=
      eLpNorm_mono_ae_real (hmeasError n).aestronglyMeasurable
        ((hbound n).mono fun _ h => by simpa only [Real.norm_eq_abs] using h)
    _ ≤ eLpNorm (originError n) 1 envLaw + ENNReal.ofReal ((n : ℝ)⁻¹ * K) := by
      have hm := (hmeasOrigin n).aemeasurable.comp_aemeasurable hrowLaw.aemeasurable
      have hc : 0 ≤ (n : ℝ)⁻¹ * K :=
        mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
          (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      have habs : eLpNorm (fun field => |originError n (rows field)|) 1 fieldLaw =
          eLpNorm (originError n) 1 envLaw := by
        rw [← hL1rows n]
        simpa only [Real.norm_eq_abs, Function.comp_def] using
          eLpNorm_norm (originError n ∘ rows) hm.aestronglyMeasurable
      have hconst : eLpNorm (fun _ : RootIndexed.StepField (Fin N) ℕ ℝ => (n : ℝ)⁻¹ * K)
          1 fieldLaw = ENNReal.ofReal ((n : ℝ)⁻¹ * K) := by
        rw [eLpNorm_const _ one_ne_zero (IsProbabilityMeasure.ne_zero _)]
        simp only [Real.eNorm_eq_ofReal_abs, abs_of_nonneg hc, measure_univ, ENNReal.one_rpow, mul_one]
      rw [← habs, ← hconst]
      exact eLpNorm_add_le le_rfl


set_option maxHeartbeats 3000000
/-- Under the boundary, nonempty-offspring, and leftmost first
moment assumptions, the exact-capacity endpoint has its almost-sure speed
uniformly over deterministic initial position vectors. Hence an independent
random initial vector has the same speed under the product law. -/
theorem ae_selectedPopulationEndpointTrajectoryWithParameter_prod_of_stepLaw
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    {N : ℕ} (hN : 0 < N) (L : StepLaw ι ℕ X)
    [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hfirst : HasLeftmostFirstMoment L)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSpace (RootIndexed.TreeNode (Fin N) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (Fin N × RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (Fin N → Fin N × RootIndexed.TreeNode (Fin N) ℕ)]
    (ρ : Measure (Fin N → ℝ)) :
    ∃ speed : ℝ,
      ∀ᵐ p ∂ρ.prod
        (RootIndexed.stepFieldLaw (Root := Fin N) L.sortedPotentialImage),
        HasAsymptoticSpeed (𝕜 := ℝ)
          (selectedPopulationEndpointTrajectoryWithParameter N p) speed := by
  classical
  let μ := L.sortedPotentialImage
  let fieldLaw := RootIndexed.stepFieldLaw (Root := Fin N) μ
  let _ : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  let _ : IsProbabilityMeasure fieldLaw := by
    dsimp [fieldLaw]
    infer_instance
  obtain ⟨speed, hsections⟩ :=
    selectedPopulationEndpointTrajectory_ae_hasAsymptoticSpeed_and_L1_of_stepLaw
      hN L hboundary hnonempty hfirst
  have hsectionsAE : ∀ᵐ initial ∂ρ, ∀ᵐ field ∂fieldLaw,
      HasAsymptoticSpeed (𝕜 := ℝ)
        (selectedPopulationEndpointTrajectoryWithParameter N
          (initial, field)) speed := by
    filter_upwards [] with initial
    exact (hsections initial).1
  have hjoint : ∀ᵐ p ∂ρ.prod fieldLaw,
      HasAsymptoticSpeed (𝕜 := ℝ)
        (selectedPopulationEndpointTrajectoryWithParameter N p) speed := by
    have hscaled (n : ℕ) : Measurable (fun p :
        (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ =>
        (n : ℝ)⁻¹ * selectedPopulationEndpointTrajectoryWithParameter N p n) :=
      measurable_const.mul
        (measurable_selectedPopulationEndpointTrajectoryWithParameter N n)
    have hevent : MeasurableSet {p :
        (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ |
        HasAsymptoticSpeed (𝕜 := ℝ)
          (selectedPopulationEndpointTrajectoryWithParameter N p) speed} := by
      change MeasurableSet {p : (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ |
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
          selectedPopulationEndpointTrajectoryWithParameter N p n)
          atTop (𝓝 speed)}
      exact measurableSet_tendsto (𝓝 speed) hscaled
    rw [Measure.ae_prod_iff_ae_ae hevent]
    exact hsectionsAE
  refine ⟨speed, ?_⟩
  change ∀ᵐ p ∂ρ.prod
    (RootIndexed.stepFieldLaw (Root := Fin N) L.sortedPotentialImage),
      HasAsymptoticSpeed (fun n =>
        selectedPopulationEndpointTrajectoryWithParameter N p n) speed
  simpa [fieldLaw, μ] using hjoint

/-- The full-capacity block bound in Wang Yiyang, Theorem 1.2, transported
from the independent generation batches to the selected population law. -/
theorem integral_fullCapacityEndpoint_div_le_speed
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    {N : ℕ} (hN : 0 < N) (L : StepLaw ι ℕ X)
    [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hfirst : HasLeftmostFirstMoment L)
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSpace (RootIndexed.TreeNode (Fin N) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (Fin N × RootIndexed.TreeNode (Fin N) ℕ)]
    [MeasurableSingletonClass (Fin N → Fin N × RootIndexed.TreeNode (Fin N) ℕ)]
    {speed : ℝ}
    (hL1 : Tendsto (fun n : ℕ => eLpNorm (fun field =>
      (n : ℝ)⁻¹ * selectedPopulationEndpointTrajectoryWithParameter N
        ((fun _ => 0), field) n - speed) 1
      (finiteRootStepFieldLaw L.sortedPotentialImage N)) atTop (𝓝 0))
    {H : ℕ} (hH : 0 < H) :
    (∫ field, selectedPopulationEndpointTrajectoryWithParameter N ((fun _ => 0), field) H
      ∂finiteRootStepFieldLaw L.sortedPotentialImage N) / H ≤ speed := by
  classical
  let μ := L.sortedPotentialImage
  let P := finiteRootStepFieldLaw μ N
  let Q := generationEnvironmentLaw μ N
  let x : Fin N → ℝ := fun _ => 0
  let A (n : ℕ) (ω : GenerationEnvironment N) :=
    repairedInfiniteSelectionSubadditiveArray hN ω 0 n
  let rows (field : RootIndexed.StepField (Fin N) ℕ ℝ) : GenerationEnvironment N :=
    fun n => selectedRootBatch (selectedPopulationRankRoots N x) n field
  have hrow : HasLaw rows Q P := selectedPopulationRankBatch_hasLaw_generationEnvironment N x μ
  have hb := L.sortedPotentialImage_hasBoundaryNormalization hboundary
  have hn : μ nonemptySupport = 1 := by
    dsimp [μ]
    rw [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport, hnonempty]
  have ho : μ (orderedBySteps realPotential) = 1 := by
    simp [μ, L.sortedPotentialImage_orderedBy]
  have hs := L.integrable_sortedPotentialImage_firstSlot_abs hboundary hfirst
  have hgoodEnv : ∀ᵐ ω ∂Q, ∀ n, IsGoodInfiniteOffspringBatch (ω n) :=
    generationEnvironmentLaw_ae_allGood μ hb hn N
  have heq (n : ℕ) : ∀ᵐ field ∂P, A n (rows field) =
      -selectedPopulationEndpointTrajectoryWithParameter N (x, field) n := by
    have hgoodRaw : ∀ᵐ field ∂P, ∀ t, IsGoodInfiniteOffspringBatch (rows field t) :=
      ae_of_ae_map hrow.aemeasurable (hrow.map_eq.symm ▸ hgoodEnv)
    filter_upwards [hgoodRaw] with field hgood
    have hmin := selectedPopulationEndpointWithParameter_eq_rankZero N n hN x field
      (selectedPopulationTotalized_card_eq_of_rankedBatches_good N x field hgood n)
    have htraj := congrFun
      (selectedPopulationRankPosition_eq_infiniteOffspringRun N x field hgood n) ⟨0, hN⟩
    have hinit : selectedPopulationRankPosition N 0 x field = x := by
      funext i
      unfold selectedPopulationRankPosition RootIndexed.observedPositionAtGeneration
        RootIndexed.positionAtGeneration
      split
      · rename_i hlength
        have hnil := List.length_eq_zero_iff.mp hlength
        simp [hnil, x, RootIndexed.position, RootIndexed.displace,
          Combinatorics.Branching.displaceWith]
      · rfl
    change A n (rows field) = -RootIndexed.selectedPopulationEndpointWithParameter N N n (x, field)
    rw [hmin, htraj, hinit]
    rw [show A n (rows field) = repairedInfiniteSelectionSubadditiveArray hN
      (rows field) 0 n from rfl, repairedInfiniteSelectionSubadditiveArray_eq_of_allGood
      hN (rows field) hgood 0 n]
    simp only [infiniteSelectionSubadditiveArray, infiniteSelectionBlockMinimum, zero_add, neg_inj]
    rfl
  have hmeas (n : ℕ) : Measurable (A n) :=
    measurable_repairedInfiniteSelectionSubadditiveArray hN 0 n
  have harray : Tendsto (fun n : ℕ => eLpNorm
      (fun ω => (n : ℝ)⁻¹ * A n ω - (-speed)) 1 Q) atTop (𝓝 0) := by
    refine hL1.congr fun n => ?_
    have hg : Measurable (fun ω => (n : ℝ)⁻¹ * A n ω - (-speed)) :=
      (measurable_const.mul (hmeas n)).sub_const _
    rw [← hrow.map_eq, eLpNorm_map_measure hg.aestronglyMeasurable hrow.aemeasurable]
    rw [← eLpNorm_neg]
    apply eLpNorm_congr_ae
    filter_upwards [heq n] with field hf
    change -((n : ℝ)⁻¹ * selectedPopulationEndpointTrajectoryWithParameter N (x, field) n -
      speed) = (n : ℝ)⁻¹ * A n (rows field) - (-speed)
    rw [hf]
    ring
  have hbound := le_normalizedIntegral_repairedInfiniteSelectionSubadditiveArray
    hN μ hb hn ho hs harray hH
  have hmean : (∫ ω, A H ω ∂Q) =
      -(∫ field, selectedPopulationEndpointTrajectoryWithParameter N (x, field) H ∂P) := by
    rw [← hrow.map_eq, integral_map hrow.aemeasurable (hmeas H).aestronglyMeasurable]
    rw [integral_congr_ae (heq H), integral_neg]
  change -speed ≤ (∫ ω, A H ω ∂Q) / H at hbound
  rw [hmean, neg_div] at hbound
  exact neg_le_neg_iff.mp hbound

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

end
