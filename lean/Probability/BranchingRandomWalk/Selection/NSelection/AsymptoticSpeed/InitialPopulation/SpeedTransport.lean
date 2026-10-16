/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.InitialPopulation.JointMeasurability
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.InitialPopulation.RunBridge
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.ProductAlmostSure
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.KingmanInterface
/-!
# Speed transport for a random initial population

This file connects the measurable endpoint of a selected population with the
rank-zero trajectory used by the exact-capacity speed theorem.
-/

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
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
    selectedPopulationEndpointWithParameter N n (initial, field) =
      selectedPopulationRankPosition N n initial field ⟨0, hN⟩ := by
  letI : Preorder (RootIndexed.TreeNode (Fin N) ℕ) := treeOrder.toPreorder
  let population := RootIndexed.selectedPopulationTotalized N Finset.univ
    initial id id n field
  let value := RootIndexed.observedPositionAtGeneration initial id id n field
  let root := selectedPopulationRankRoot N n initial field ⟨0, hN⟩
  have hroot := selectedPopulationRankRoot_mem_and_rank_of_card
    N n initial field ⟨0, hN⟩ (by simpa [population] using hcard)
  have hfilter := hroot.2
  rw [Combinatorics.Branching.Selection.NSelection.rankBy_eq_card_filter] at hfilter
  have hminimum : ∀ q ∈ population, value root ≤ value q := by
    intro q hq
    by_contra hnot
    have hlt : value q < value root := lt_of_not_ge hnot
    have hmem : q ∈ (RootIndexed.selectedPopulationTotalized N Finset.univ
        initial id id n field).filter (fun r =>
        Combinatorics.Branching.Selection.NSelection.valueKey
            (RootIndexed.observedPositionAtGeneration initial id id n field) r <
          Combinatorics.Branching.Selection.NSelection.valueKey
            (RootIndexed.observedPositionAtGeneration initial id id n field)
            (selectedPopulationRankRoot N n initial field ⟨0, hN⟩)) :=
      Finset.mem_filter.mpr
        ⟨by simpa [population] using hq,
          Combinatorics.Branching.Selection.NSelection.valueKey_lt_of_value_lt
            (RootIndexed.observedPositionAtGeneration initial id id n field) hlt⟩
    have hpos : 0 < {r ∈ RootIndexed.selectedPopulationTotalized N Finset.univ
        initial id id n field |
        Combinatorics.Branching.Selection.NSelection.valueKey
            (RootIndexed.observedPositionAtGeneration initial id id n field) r <
          Combinatorics.Branching.Selection.NSelection.valueKey
            (RootIndexed.observedPositionAtGeneration initial id id n field)
            (selectedPopulationRankRoot N n initial field ⟨0, hN⟩)}.card := by
      exact Finset.card_pos.mpr ⟨q, hmem⟩
    have hfilterZero : ({r ∈ RootIndexed.selectedPopulationTotalized N Finset.univ
        initial id id n field |
        Combinatorics.Branching.Selection.NSelection.valueKey
            (RootIndexed.observedPositionAtGeneration initial id id n field) r <
          Combinatorics.Branching.Selection.NSelection.valueKey
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
  have hendpoint : selectedPopulationEndpointWithParameter N n (initial, field) =
      population.inf' hpop value := by
    change (if h : population.Nonempty then population.inf' h value else 0) = _
    rw [dif_pos hpop]
  rw [hendpoint]
  rw [hinf]
  rfl

/-- The local endpoint trajectory starting from a parameterized position
vector and driven by a pre-sampled root field. -/
noncomputable def selectedPopulationEndpointTrajectoryWithParameter
    (N : ℕ) [DecidableEq (RootIndexed.TreeNode (Fin N) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (p : (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ) :
    ℕ → ℝ := fun n => selectedPopulationEndpointWithParameter N n p

theorem measurable_selectedPopulationEndpointTrajectoryWithParameter
    (N n : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin N) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin N) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin N) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)] :
    Measurable (fun p : (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ =>
      selectedPopulationEndpointTrajectoryWithParameter N p n) := by
  simpa [selectedPopulationEndpointTrajectoryWithParameter] using
    measurable_selectedPopulationEndpointWithParameter N n

private theorem ae_selectedPopulationEndpointTrajectoryWithParameter_sections
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
      selectedPopulationEndpointWithParameter N n (initial, field) =
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
private theorem ae_selectedPopulationEndpointTrajectoryWithParameter_sections_of_stepLaw
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
      ∀ᵐ field ∂RootIndexed.stepFieldLaw
        (Root := Fin N) L.sortedPotentialImage,
        HasAsymptoticSpeed (𝕜 := ℝ)
          (selectedPopulationEndpointTrajectoryWithParameter N
            (initial, field)) speed := by
  classical
  let μ := L.sortedPotentialImage
  let envLaw := generationEnvironmentLaw μ N
  let fieldLaw := RootIndexed.stepFieldLaw (Root := Fin N) μ
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  letI : IsProbabilityMeasure envLaw := by
    exact generationEnvironmentLaw_isProbability μ N
  letI : IsProbabilityMeasure fieldLaw := by
    dsimp [fieldLaw]
    infer_instance
  have hboundaryμ : HasBoundaryNormalization realPotential μ := by
    dsimp [μ]
    exact L.sortedPotentialImage_hasBoundaryNormalization hboundary
  have hnonemptyμ : μ nonemptySupport = 1 := by
    dsimp [μ]
    rw [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport]
    exact hnonempty
  obtain ⟨c, horiginSpeed⟩ :=
    infiniteOffspringRun_leftmost_ae_hasAsymptoticSpeed_of_stepLaw
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
  let batchMap : RootIndexed.StepField (Fin N) ℕ ℝ →
      GenerationEnvironment N := fun field n =>
        selectedRootBatch (selectedPopulationRankRoots N (fun _ => 0)) n field
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
  refine ⟨speed, ?_⟩
  simpa [fieldLaw] using hsections

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
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  letI : IsProbabilityMeasure fieldLaw := by
    dsimp [fieldLaw]
    infer_instance
  obtain ⟨speed, hsections⟩ :=
    ae_selectedPopulationEndpointTrajectoryWithParameter_sections_of_stepLaw
      hN L hboundary hnonempty hfirst
  have hsectionsAE : ∀ᵐ initial ∂ρ, ∀ᵐ field ∂fieldLaw,
      HasAsymptoticSpeed (𝕜 := ℝ)
        (selectedPopulationEndpointTrajectoryWithParameter N
          (initial, field)) speed := by
    filter_upwards [] with initial
    exact hsections initial
  have hjoint := ae_hasAsymptoticSpeed_prod_of_ae_sections
    ρ fieldLaw
    (fun initial field n =>
      selectedPopulationEndpointTrajectoryWithParameter N (initial, field) n)
    (fun n => measurable_selectedPopulationEndpointTrajectoryWithParameter
      N n) speed hsectionsAE
  refine ⟨speed, ?_⟩
  change ∀ᵐ p ∂ρ.prod
    (RootIndexed.stepFieldLaw (Root := Fin N) L.sortedPotentialImage),
      HasAsymptoticSpeed (fun n =>
        selectedPopulationEndpointTrajectoryWithParameter N p n) speed
  simpa [fieldLaw, μ] using hjoint

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed
