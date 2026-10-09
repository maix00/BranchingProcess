/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.CadlagPath.FiniteDimensional
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathFiniteDimensionalSource
public import Probability.Process.RandomWalk.Path.Skorokhod

/-!
# Stable path-law subsequences from a scalar domain of attraction

Prokhorov compactness produces a path-valued subsequential limit directly
from tightness of the normalized random walks. This file records the finite
dimensional laws that can be identified without assuming a preconstructed
stable-process witness: on a countable dense set of almost-sure continuity
times for the cluster law, the limit has the expected stable increment-grid
law.

The dense continuity set is chosen after taking the subsequence, as required
for the Skorokhod `J₁` evaluation maps. A second theorem in this file extends
the identification to all strictly increasing finite grids by right-
continuous time approximation.
-/

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.CadlagPath
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

/-- From tightness and scalar domain-of-attraction convergence, one can
extract a weakly convergent subsequence of normalized random-walk path laws.
The limiting law has the stable finite-dimensional position laws on a
countable dense set of times at which evaluation is almost surely continuous
under that limit. No stable-process path-law witness is an input. -/
theorem exists_subseq_normalizedStepPathLaw_with_stable_dense_grid_laws
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization center : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization center)
    (hStable : IsStrictlyAlphaStable α μ)
    (htight : IsTightMeasureSet (Set.range
      (fun n => RandomWalk.normalizedStepPathLaw ν normalization n)))
    (hcenter : ∀ (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval),
      StrictMono grid → grid 0 = ⊥ → ∀ j : Fin blocks,
        Tendsto (fun n : ℕ => center
          (unitIntervalGridFloorTime grid n j.succ -
            unitIntervalGridFloorTime grid n j.castSucc) / normalization n)
          atTop (𝓝 0)) :
    ∃ (sub : ℕ → ℕ) (P : ProbabilityMeasure (CadlagPath unitInterval ℝ)),
      StrictMono sub ∧
      Tendsto (fun n =>
        (⟨RandomWalk.normalizedStepPathLaw ν normalization (sub n), inferInstance⟩ :
          ProbabilityMeasure (CadlagPath unitInterval ℝ))) atTop
        (@nhds (ProbabilityMeasure (CadlagPath unitInterval ℝ)) inferInstance P) ∧
      ∃ T : Set unitInterval,
        T.Countable ∧ Dense T ∧
        (∀ t ∈ T,
          (∀ᵐ path ∂(P : Measure (CadlagPath unitInterval ℝ)),
            ContinuousAt (fun s : unitInterval => path s) t) ∨
            t = ⊥ ∨ t = ⊤) ∧
        (∀ x, IsBot x → x ∈ T) ∧ (∀ x, IsTop x → x ∈ T) ∧
        ∀ (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval),
          StrictMono grid → grid 0 = ⊥ → (∀ j, grid j ∈ T) →
          P.map (denseEvaluation grid) =
            (stableTimeLawProductProbability (μ := μ) α grid).map
              (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ) := by
  let pathLaw : ℕ → ProbabilityMeasure (CadlagPath unitInterval ℝ) := fun n =>
    ⟨RandomWalk.normalizedStepPathLaw ν normalization n, inferInstance⟩
  have htight' : IsTightMeasureSet
      {((pathLaw n : ProbabilityMeasure (CadlagPath unitInterval ℝ)) :
        Measure (CadlagPath unitInterval ℝ)) | n} := by
    convert htight using 1
    ext q
    simp [pathLaw]
  obtain ⟨sub, P, hsub, hconv⟩ :=
    ProbabilityTheory.CadlagPath.ProbabilityMeasure.exists_tendsto_subseq_of_tight
      pathLaw htight'

  let good : Set unitInterval := {t | ∀ᵐ path ∂(P : Measure (CadlagPath unitInterval ℝ)),
    ContinuousAt (fun s : unitInterval => path s) t}
  let candidate : Set unitInterval := good ∪ ({⊥, ⊤} : Set unitInterval)
  have hgoodDense : Dense good :=
    MeasureTheory.CadlagPath.dense_ae_continuityTimes_of_cadlag
      (P : Measure (CadlagPath unitInterval ℝ))
  have hcandidateDense : Dense candidate := hgoodDense.mono (by
    intro t ht
    exact Or.inl ht)
  obtain ⟨T, hTsub, hTcount, hTdense, hTbot, hTtop⟩ :=
    hcandidateDense.exists_countable_dense_subset_bot_top

  have hgridLaw (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval)
      (hgrid : StrictMono grid) (hstart : grid 0 = ⊥)
      (hgridT : ∀ j, grid j ∈ T) :
      P.map (denseEvaluation grid) =
        (stableTimeLawProductProbability (μ := μ) α grid).map
          (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ) := by
    let pathEvaluation : CadlagPath unitInterval ℝ → Fin (blocks + 1) → ℝ :=
      denseEvaluation grid
    have hcontinuousCoordinate (j : Fin (blocks + 1)) :
        ∀ᵐ path ∂(P : Measure (CadlagPath unitInterval ℝ)),
          ContinuousAt (fun f : CadlagPath unitInterval ℝ => f (grid j)) path := by
      rcases hTsub (hgridT j) with hjGood | hjEnd
      · filter_upwards [hjGood] with path hpath
        exact Skorokhod.continuousAt_apply_of_continuousAt path (grid j) hpath
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hjEnd
        rcases hjEnd with hjBot | hjTop
        · filter_upwards [] with path
          simpa [hjBot] using
            (Skorokhod.continuous_apply_bot.continuousAt :
              ContinuousAt (fun f : CadlagPath unitInterval ℝ => f ⊥) path)
        · filter_upwards [] with path
          simpa [hjTop] using
            (Skorokhod.continuous_apply_top.continuousAt :
              ContinuousAt (fun f : CadlagPath unitInterval ℝ => f ⊤) path)
    have hall : ∀ᵐ path ∂(P : Measure (CadlagPath unitInterval ℝ)),
        ∀ j : Fin (blocks + 1),
          ContinuousAt (fun f : CadlagPath unitInterval ℝ => f (grid j)) path :=
      ae_all_iff.mpr hcontinuousCoordinate
    have hcontinuous :
        ∀ᵐ path ∂(P : Measure (CadlagPath unitInterval ℝ)),
          ContinuousAt pathEvaluation path := by
      filter_upwards [hall] with path hpath
      change ContinuousAt (fun f : CadlagPath unitInterval ℝ =>
        fun j : Fin (blocks + 1) => f (grid j)) path
      exact continuousAt_pi.2 hpath

    let target : ProbabilityMeasure (Fin (blocks + 1) → ℝ) :=
      (stableTimeLawProductProbability (μ := μ) α grid).map
        (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ)
    have hfd := tendstoInDistribution_normalizedStepPath_finiteGrid_of_stableDomain
      hDOA hStable blocks grid hgrid hstart (hcenter blocks grid hgrid hstart)
    have hsource (n : ℕ) :
        (pathLaw n).map pathEvaluation =
          (⟨(iidSequenceLaw ν).map
            (fun increments j => RandomWalk.normalizedStepPath normalization n
              increments (grid j : ℝ)), inferInstance⟩ :
            ProbabilityMeasure (Fin (blocks + 1) → ℝ)) := by
      apply Subtype.ext
      change (RandomWalk.normalizedStepPathLaw ν normalization n).map
        (denseEvaluation grid) = _
      rw [RandomWalk.normalizedStepPathLaw,
        Measure.map_map (measurable_denseEvaluation grid)
          (RandomWalk.measurable_normalizedStepCadlagPathIcc normalization n)]
      rfl
    have hsourceLimit : Tendsto (fun n => (pathLaw n).map pathEvaluation) atTop
        (@nhds (ProbabilityMeasure (Fin (blocks + 1) → ℝ)) inferInstance target) := by
      have hraw := hfd.tendsto
      have hseq : (fun n => (pathLaw n).map pathEvaluation) =
          (fun n => (⟨(iidSequenceLaw ν).map
            (fun increments j => RandomWalk.normalizedStepPath normalization n
              increments (grid j : ℝ)), inferInstance⟩ :
            ProbabilityMeasure (Fin (blocks + 1) → ℝ))) := by
        funext n
        exact hsource n
      rw [hseq]
      have htargetEq : target =
          (⟨Measure.map id (target : Measure (Fin (blocks + 1) → ℝ)), inferInstance⟩ :
            ProbabilityMeasure (Fin (blocks + 1) → ℝ)) := by
        apply Subtype.ext
        simp [target, Measure.map_id]
      rw [htargetEq]
      exact hraw
    have hsubLimit : Tendsto (fun n => (pathLaw (sub n)).map pathEvaluation) atTop
        (@nhds (ProbabilityMeasure (Fin (blocks + 1) → ℝ)) inferInstance
          (P.map pathEvaluation)) :=
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuousAt_ae
        (by simpa [pathLaw] using hconv)
        (measurable_denseEvaluation grid) hcontinuous
    have hsubSource : Tendsto (fun n => (pathLaw (sub n)).map pathEvaluation)
        atTop (@nhds (ProbabilityMeasure (Fin (blocks + 1) → ℝ)) inferInstance target) :=
      hsourceLimit.comp hsub.tendsto_atTop
    have heq : P.map pathEvaluation = target := tendsto_nhds_unique hsubLimit hsubSource
    simpa [target, pathEvaluation] using heq

  refine ⟨sub, P, hsub, ?_, T, hTcount, hTdense, ?_, ?_, ?_, ?_⟩
  · exact hconv
  · intro t ht
    rcases hTsub ht with htGood | htEnd
    · exact Or.inl htGood
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at htEnd
      rcases htEnd with htBot | htTop
      · exact Or.inr (Or.inl htBot)
      · exact Or.inr (Or.inr htTop)
  · intro x hx
    apply hTbot x hx
    exact Or.inr (Or.inl hx.eq_bot)
  · intro x hx
    apply hTtop x hx
    exact Or.inr (Or.inr hx.eq_top)
  · intro blocks grid hgrid hstart hgridT
    exact hgridLaw blocks grid hgrid hstart hgridT

/-- The uncentered version of dense-grid stable path-law extraction. When the
domain-of-attraction centering is identically zero, the block-centering input
is automatic. -/
theorem exists_subseq_normalizedStepPathLaw_with_stable_dense_grid_laws_of_zeroCenter
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hStable : IsStrictlyAlphaStable α μ)
    (htight : IsTightMeasureSet (Set.range
      (fun n => RandomWalk.normalizedStepPathLaw ν normalization n))) :
    ∃ (sub : ℕ → ℕ) (P : ProbabilityMeasure (CadlagPath unitInterval ℝ)),
      StrictMono sub ∧
      Tendsto (fun n =>
        (⟨RandomWalk.normalizedStepPathLaw ν normalization (sub n), inferInstance⟩ :
          ProbabilityMeasure (CadlagPath unitInterval ℝ))) atTop
        (@nhds (ProbabilityMeasure (CadlagPath unitInterval ℝ)) inferInstance P) ∧
      ∃ T : Set unitInterval,
        T.Countable ∧ Dense T ∧
        (∀ t ∈ T,
          (∀ᵐ path ∂(P : Measure (CadlagPath unitInterval ℝ)),
            ContinuousAt (fun s : unitInterval => path s) t) ∨
            t = ⊥ ∨ t = ⊤) ∧
        (∀ x, IsBot x → x ∈ T) ∧ (∀ x, IsTop x → x ∈ T) ∧
        ∀ (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval),
          StrictMono grid → grid 0 = ⊥ → (∀ j, grid j ∈ T) →
          P.map (denseEvaluation grid) =
            (stableTimeLawProductProbability (μ := μ) α grid).map
              (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ) := by
  apply exists_subseq_normalizedStepPathLaw_with_stable_dense_grid_laws
    hDOA hStable htight
  intro blocks grid hgrid hstart j
  simp

private theorem tendsto_stableGridPositionLaw_of_tendsto
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}
    (hStable : IsStrictlyAlphaStable α μ) {blocks : ℕ}
    (grid : Fin (blocks + 1) → unitInterval)
    (gridSeq : ℕ → Fin (blocks + 1) → unitInterval)
    (hgridTime : ∀ j, Tendsto (fun n => gridSeq n j) atTop (𝓝 (grid j))) :
    Tendsto (fun n =>
      (stableTimeLawProductProbability (μ := μ) α (gridSeq n)).map
        (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ))
      atTop
      (@nhds (ProbabilityMeasure (Fin (blocks + 1) → ℝ)) inferInstance
        ((stableTimeLawProductProbability (μ := μ) α grid).map
          (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ))) := by
  let base : Measure (Fin blocks → ℝ) := Measure.pi fun _ : Fin blocks => μ
  let scaleVector : ℕ → (Fin blocks → ℝ) → Fin blocks → ℝ := fun n z j =>
    (((gridSeq n j.succ : ℝ) - (gridSeq n j.castSucc : ℝ)) ^ (1 / α)) * z j
  let limitScaleVector : (Fin blocks → ℝ) → Fin blocks → ℝ := fun z j =>
    (((grid j.succ : ℝ) - (grid j.castSucc : ℝ)) ^ (1 / α)) * z j
  have hprob : IsProbabilityMeasure base := by
    dsimp [base]
    infer_instance
  have hscaledPi (n : ℕ) :
      base.map (scaleVector n) = stableTimeLawProductProbability (μ := μ) α (gridSeq n) := by
    have hpi := Measure.pi_map_pi
      (fun j : Fin blocks =>
        (by fun_prop : AEMeasurable
          (fun x : ℝ =>
            (((gridSeq n j.succ : ℝ) - (gridSeq n j.castSucc : ℝ)) ^ (1 / α)) * x) μ))
    simpa [base, scaleVector, stableTimeLawProductProbability, stableTimeLaw] using hpi
  have hscaledPiLimit :
      base.map limitScaleVector = stableTimeLawProductProbability (μ := μ) α grid := by
    have hpi := Measure.pi_map_pi
      (fun j : Fin blocks =>
        (by fun_prop : AEMeasurable
          (fun x : ℝ =>
            (((grid j.succ : ℝ) - (grid j.castSucc : ℝ)) ^ (1 / α)) * x) μ))
    simpa [base, limitScaleVector, stableTimeLawProductProbability, stableTimeLaw] using hpi
  have hduration (j : Fin blocks) :
      Tendsto (fun n =>
        ((gridSeq n j.succ : ℝ) - (gridSeq n j.castSucc : ℝ))) atTop
        (𝓝 ((grid j.succ : ℝ) - (grid j.castSucc : ℝ))) := by
    have hsucc : Tendsto (fun n => (gridSeq n j.succ : ℝ)) atTop
        (𝓝 (grid j.succ : ℝ)) :=
      (continuous_subtype_val.tendsto (grid j.succ)).comp (hgridTime j.succ)
    have hpred : Tendsto (fun n => (gridSeq n j.castSucc : ℝ)) atTop
        (𝓝 (grid j.castSucc : ℝ)) :=
      (continuous_subtype_val.tendsto (grid j.castSucc)).comp (hgridTime j.castSucc)
    exact hsucc.sub hpred
  have hcoefficient (j : Fin blocks) :
      Tendsto (fun n =>
        (((gridSeq n j.succ : ℝ) - (gridSeq n j.castSucc : ℝ)) ^ (1 / α))) atTop
        (𝓝 (((grid j.succ : ℝ) - (grid j.castSucc : ℝ)) ^ (1 / α))) := by
    have hq : 0 ≤ (1 / α : ℝ) := le_of_lt (one_div_pos.mpr hStable.1)
    have hcont : ContinuousAt (fun x : ℝ => x ^ (1 / α))
        ((grid j.succ : ℝ) - (grid j.castSucc : ℝ)) :=
      (Real.continuous_rpow_const (q := 1 / α) hq).continuousAt
    exact hcont.tendsto.comp (hduration j)
  have hpointwise (z : Fin blocks → ℝ) :
      Tendsto (fun n => scaleVector n z) atTop (𝓝 (limitScaleVector z)) := by
    apply tendsto_pi_nhds.2
    intro j
    dsimp [scaleVector, limitScaleVector]
    exact (hcoefficient j).mul_const (z j)
  have hTID : TendstoInDistribution scaleVector atTop limitScaleVector
      (fun _ => base) base :=
    MeasureTheory.tendstoInDistribution_of_ae_tendsto
      (fun n => by fun_prop)
      (by fun_prop)
      (ae_of_all (base) hpointwise)
  let scalePosition : ℕ → (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ :=
    fun n z => Fin.partialSum (scaleVector n z)
  let limitScalePosition : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ :=
    fun z => Fin.partialSum (limitScaleVector z)
  have hpositionTID := hTID.continuous_comp (Fin.continuous_partialSum blocks)
  have hpositionPi (n : ℕ) :
      (stableTimeLawProductProbability (μ := μ) α (gridSeq n)).map
          (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ) =
        ⟨base.map (scalePosition n), by
          dsimp [base, scalePosition]
          infer_instance⟩ := by
    apply Subtype.ext
    change Measure.map
        (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ)
          (stableTimeLawProductProbability (μ := μ) α (gridSeq n) :
            Measure (Fin blocks → ℝ)) =
      base.map (scalePosition n)
    rw [← hscaledPi n]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hpositionPiLimit :
      (stableTimeLawProductProbability (μ := μ) α grid).map
          (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ) =
        ⟨base.map limitScalePosition, by
          dsimp [base, limitScalePosition]
          infer_instance⟩ := by
    apply Subtype.ext
    change Measure.map
        (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ)
          (stableTimeLawProductProbability (μ := μ) α grid :
            Measure (Fin blocks → ℝ)) =
      base.map limitScalePosition
    rw [← hscaledPiLimit]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hseq : (fun n =>
      (stableTimeLawProductProbability (μ := μ) α (gridSeq n)).map
        (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ)) =
      fun n => ⟨base.map (scalePosition n), by
        dsimp [base, scalePosition]
        infer_instance⟩ := by
    funext n
    exact hpositionPi n
  rw [hseq, hpositionPiLimit]
  exact hpositionTID.tendsto

private theorem exists_dense_strictGrid_approximation
    {T : Set unitInterval} (hTdense : Dense T)
    (hTbot : (⊥ : unitInterval) ∈ T) (hTtop : (⊤ : unitInterval) ∈ T)
    {blocks : ℕ} (grid : Fin (blocks + 1) → unitInterval)
    (hgrid : StrictMono grid) (hstart : grid 0 = ⊥) :
    ∃ gridSeq : ℕ → Fin (blocks + 1) → unitInterval,
      (∀ n, StrictMono (gridSeq n)) ∧
      (∀ n j, gridSeq n j ∈ T) ∧
      (∀ j, Tendsto (fun n => gridSeq n j) atTop (𝓝 (grid j))) ∧
      (∀ n j, grid j ≤ gridSeq n j) ∧
      (∀ j, grid j = ⊥ → ∀ n, gridSeq n j = ⊥) ∧
      (∀ j, grid j = ⊤ → ∀ n, gridSeq n j = ⊤) ∧
      (∀ j, grid j ≠ ⊥ → grid j ≠ ⊤ → ∀ n, grid j < gridSeq n j) := by
  have hcoordinate (j : Fin (blocks + 1)) :
      ∃ u : ℕ → unitInterval,
        (∀ n, u n ∈ T) ∧
        Tendsto u atTop (𝓝 (grid j)) ∧
        (grid j = ⊥ → ∀ n, u n = ⊥) ∧
        (grid j = ⊤ → ∀ n, u n = ⊤) ∧
        (grid j ≠ ⊥ → grid j ≠ ⊤ → ∀ n, grid j < u n) ∧
        (∀ n (hj : j.val < blocks),
          u n < grid ⟨j.val + 1, by omega⟩) := by
    by_cases hj0 : j.val = 0
    · have hj : j = 0 := Fin.ext hj0
      refine ⟨fun _ => ⊥, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro n
        exact hTbot
      · simp [hj, hstart]
      · intro hjbot n
        rfl
      · intro hjtop n
        rw [hj, hstart] at hjtop
        exact (bot_ne_top hjtop).elim
      · intro hjbot hjtop n
        exact (hjbot (by simp [hj, hstart])).elim
      · intro n hjlt
        have hidx : (0 : Fin (blocks + 1)) < ⟨0 + 1, by omega⟩ := by
          apply Fin.mk_lt_mk.mpr
          simp
        have := hgrid hidx
        simpa [hj, hstart] using this
    · by_cases hjtop : grid j = ⊤
      · refine ⟨fun _ => ⊤, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro n
          exact hTtop
        · simp [hjtop]
        · intro hjbot n
          rw [hjtop] at hjbot
          exact (top_ne_bot hjbot).elim
        · intro hjtop' n
          rfl
        · intro hjbot hjtop' n
          rw [hjtop] at hjtop'
          exact (hjtop' rfl).elim
        · intro n hjlt
          have hidx : j < ⟨j.val + 1, by omega⟩ := by
            apply Fin.mk_lt_mk.mpr
            simp
          have hstrict := hgrid hidx
          simp [hjtop] at hstrict
      · have hjbot : grid j ≠ ⊥ := by
          intro heq
          have hjpos : (0 : Fin (blocks + 1)) < j := by
            exact Fin.pos_iff_ne_zero.mpr (fun heq' => hj0 (congrArg Fin.val heq'))
          have hstrict := hgrid hjpos
          rw [hstart, heq] at hstrict
          exact (lt_irrefl _ hstrict).elim
        let upper : unitInterval :=
          if hlast : j.val = blocks then ⊤ else grid ⟨j.val + 1, by omega⟩
        have hupper : grid j < upper := by
          by_cases hlast : j.val = blocks
          · simp [upper, hlast]
            exact lt_of_le_of_ne le_top hjtop
          · simp [upper, hlast]
            have hidx : j < ⟨j.val + 1, by omega⟩ := by
              apply Fin.mk_lt_mk.mpr
              simp
            exact hgrid hidx
        obtain ⟨u, huanti, humem, hlim⟩ :=
          hTdense.exists_seq_strictAnti_tendsto_of_lt hupper
        refine ⟨u, ?_, hlim, ?_, ?_, ?_, ?_⟩
        · intro n
          exact (humem n).2
        · intro heq n
          exact (hjbot heq).elim
        · intro heq n
          exact (hjtop heq).elim
        · intro _ _ n
          exact (humem n).1.1
        · intro n hjlt
          have hlast : j.val ≠ blocks := by omega
          have hmemUpper := (humem n).1.2
          simpa [upper, hlast] using hmemUpper
  let coordinate : Fin (blocks + 1) → ℕ → unitInterval := fun j =>
    (hcoordinate j).choose
  have hcoordinateProp (j : Fin (blocks + 1)) := (hcoordinate j).choose_spec
  let gridSeq : ℕ → Fin (blocks + 1) → unitInterval := fun n j => coordinate j n
  have hgridTime (j : Fin (blocks + 1)) :
      Tendsto (fun n => gridSeq n j) atTop (𝓝 (grid j)) :=
    (hcoordinateProp j).2.1
  have hgridMem (n : ℕ) (j : Fin (blocks + 1)) : gridSeq n j ∈ T :=
    (hcoordinateProp j).1 n
  have hgridGe (n : ℕ) (j : Fin (blocks + 1)) : grid j ≤ gridSeq n j := by
    change grid j ≤ (hcoordinate j).choose n
    by_cases hjbot : grid j = ⊥
    · rw [(hcoordinateProp j).2.2.1 hjbot n, hjbot]
    · by_cases hjtop : grid j = ⊤
      · rw [(hcoordinateProp j).2.2.2.1 hjtop n, hjtop]
      · exact ((hcoordinateProp j).2.2.2.2.1 hjbot hjtop n).le
  have hleftLt (n : ℕ) (j : Fin blocks) :
      gridSeq n j.castSucc < gridSeq n j.succ := by
    change (hcoordinate j.castSucc).choose n < (hcoordinate j.succ).choose n
    by_cases hjbot : grid j.castSucc = ⊥
    · rw [(hcoordinateProp j.castSucc).2.2.1 hjbot n]
      have hidx : j.castSucc < j.succ := by
        apply Fin.mk_lt_mk.mpr
        simp
      have hstrict := hgrid hidx
      rw [hjbot] at hstrict
      exact hstrict.trans_le (hgridGe n j.succ)
    · by_cases hjtop : grid j.castSucc = ⊤
      · have hidx : j.castSucc < j.succ := by
          apply Fin.mk_lt_mk.mpr
          simp
        have hstrict := hgrid hidx
        rw [hjtop] at hstrict
        exact (not_lt_of_ge le_top hstrict).elim
      · have hnext :
          (⟨j.castSucc.val + 1, by simp⟩ : Fin (blocks + 1)) = j.succ := by
            apply Fin.ext
            simp
        have hupper :=
          (hcoordinateProp j.castSucc).2.2.2.2.2 n (by simp)
        rw [hnext] at hupper
        exact hupper.trans_le (hgridGe n j.succ)
  have hgridSeqStrict (n : ℕ) : StrictMono (gridSeq n) := by
    rw [Fin.strictMono_iff_lt_succ]
    exact hleftLt n
  have hgridBot (j : Fin (blocks + 1)) (hj : grid j = ⊥) (n : ℕ) :
      gridSeq n j = ⊥ := by
    change (hcoordinate j).choose n = ⊥
    exact (hcoordinateProp j).2.2.1 hj n
  have hgridTop (j : Fin (blocks + 1)) (hj : grid j = ⊤) (n : ℕ) :
      gridSeq n j = ⊤ := by
    change (hcoordinate j).choose n = ⊤
    exact (hcoordinateProp j).2.2.2.1 hj n
  have hgridAbove (j : Fin (blocks + 1)) (hjbot : grid j ≠ ⊥)
      (hjtop : grid j ≠ ⊤) (n : ℕ) : grid j < gridSeq n j := by
    change grid j < (hcoordinate j).choose n
    exact (hcoordinateProp j).2.2.2.2.1 hjbot hjtop n
  exact ⟨gridSeq, fun n => hgridSeqStrict n, hgridMem, hgridTime,
    hgridGe, hgridBot, hgridTop, hgridAbove⟩

private theorem stable_grid_law_of_dense_grid_laws
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}
    (hStable : IsStrictlyAlphaStable α μ)
    {P : ProbabilityMeasure (CadlagPath unitInterval ℝ)}
    {T : Set unitInterval} (hTdense : Dense T)
    (hTbot : (⊥ : unitInterval) ∈ T) (hTtop : (⊤ : unitInterval) ∈ T)
    (hDenseLaw : ∀ (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval),
      StrictMono grid → grid 0 = ⊥ → (∀ j, grid j ∈ T) →
        P.map (denseEvaluation grid) =
          (stableTimeLawProductProbability (μ := μ) α grid).map
            (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ))
    {blocks : ℕ} (grid : Fin (blocks + 1) → unitInterval)
    (hgrid : StrictMono grid) (hstart : grid 0 = ⊥) :
    P.map (denseEvaluation grid) =
      (stableTimeLawProductProbability (μ := μ) α grid).map
        (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ) := by
  obtain ⟨gridSeq, hgridSeqStrict, hgridSeqMem, hgridTime, hgridGe,
      hgridSeqBot, hgridSeqTop, hgridSeqAbove⟩ :=
    exists_dense_strictGrid_approximation hTdense hTbot hTtop grid hgrid hstart
  have hgridSeqStart (n : ℕ) : gridSeq n 0 = ⊥ := by
    exact hgridSeqBot 0 hstart n
  have hcoordinateTendsto (path : CadlagPath unitInterval ℝ)
      (j : Fin (blocks + 1)) :
      Tendsto (fun n => path (gridSeq n j)) atTop (𝓝 (path (grid j))) := by
    by_cases hjbot : grid j = ⊥
    · have hseq : ∀ n, gridSeq n j = grid j := by
        intro n
        rw [hgridSeqBot j hjbot n, hjbot]
      simpa only [hseq] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => path (grid j)) atTop
          (𝓝 (path (grid j))))
    · by_cases hjtop : grid j = ⊤
      · have hseq : ∀ n, gridSeq n j = grid j := by
          intro n
          rw [hgridSeqTop j hjtop n, hjtop]
        simpa only [hseq] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => path (grid j)) atTop
            (𝓝 (path (grid j))))
      · have hstrict : ∀ n, grid j < gridSeq n j := by
          intro n
          exact hgridSeqAbove j hjbot hjtop n
        have htimeWithin :
            Tendsto (fun n => gridSeq n j) atTop (𝓝[Set.Ioi (grid j)] (grid j)) :=
          tendsto_nhdsWithin_iff.mpr ⟨hgridTime j,
            Filter.Eventually.of_forall hstrict⟩
        exact (path.isCadlag_toFun.isRightContinuous (grid j)).tendsto.comp
          htimeWithin
  have hpointwise (path : CadlagPath unitInterval ℝ) :
      Tendsto (fun n => denseEvaluation (gridSeq n) path) atTop
        (𝓝 (denseEvaluation grid path)) := by
    apply tendsto_pi_nhds.2
    intro j
    exact hcoordinateTendsto path j
  have hTID : TendstoInDistribution (fun n => denseEvaluation (gridSeq n)) atTop
      (denseEvaluation grid) (fun _ => (P : Measure (CadlagPath unitInterval ℝ)))
      (P : Measure (CadlagPath unitInterval ℝ)) :=
    MeasureTheory.tendstoInDistribution_of_ae_tendsto
      (fun n => (measurable_denseEvaluation (gridSeq n)).aemeasurable)
      (measurable_denseEvaluation grid).aemeasurable
      (ae_of_all (P : Measure (CadlagPath unitInterval ℝ)) hpointwise)
  have hpathLimit :
      Tendsto (fun n => P.map (denseEvaluation (gridSeq n))) atTop
        (@nhds (ProbabilityMeasure (Fin (blocks + 1) → ℝ)) inferInstance
          (P.map (denseEvaluation grid))) := hTID.tendsto
  have hdenseIdentify (n : ℕ) :
      P.map (denseEvaluation (gridSeq n)) =
        (stableTimeLawProductProbability (μ := μ) α (gridSeq n)).map
          (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ) :=
    hDenseLaw blocks (gridSeq n) (hgridSeqStrict n) (hgridSeqStart n)
      (hgridSeqMem n)
  have hpathLimitStable :
      Tendsto (fun n => P.map (denseEvaluation (gridSeq n))) atTop
        (@nhds (ProbabilityMeasure (Fin (blocks + 1) → ℝ)) inferInstance
          ((stableTimeLawProductProbability (μ := μ) α grid).map
            (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ))) := by
    have hseq : (fun n => P.map (denseEvaluation (gridSeq n))) =
        fun n => (stableTimeLawProductProbability (μ := μ) α (gridSeq n)).map
          (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ) := by
      funext n
      exact hdenseIdentify n
    rw [hseq]
    exact tendsto_stableGridPositionLaw_of_tendsto hStable grid gridSeq hgridTime
  exact tendsto_nhds_unique hpathLimit hpathLimitStable

/-- Tightness, scalar domain of attraction, and the block-centering condition
produce a subsequential càdlàg path law with the stable finite-dimensional
position distributions on every strictly increasing deterministic time grid.
The weak limit is not assumed in advance: it is obtained from Prokhorov
compactness, first identified on a dense set of continuity times, then
extended to arbitrary grids by right continuity of the paths. -/
theorem exists_subseq_normalizedStepPathLaw_with_stable_grid_laws
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization center : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization center)
    (hStable : IsStrictlyAlphaStable α μ)
    (htight : IsTightMeasureSet (Set.range
      (fun n => RandomWalk.normalizedStepPathLaw ν normalization n)))
    (hcenter : ∀ (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval),
      StrictMono grid → grid 0 = ⊥ → ∀ j : Fin blocks,
        Tendsto (fun n : ℕ => center
          (unitIntervalGridFloorTime grid n j.succ -
            unitIntervalGridFloorTime grid n j.castSucc) / normalization n)
          atTop (𝓝 0)) :
    ∃ (sub : ℕ → ℕ) (P : ProbabilityMeasure (CadlagPath unitInterval ℝ)),
      StrictMono sub ∧
      Tendsto (fun n =>
        (⟨RandomWalk.normalizedStepPathLaw ν normalization (sub n), inferInstance⟩ :
          ProbabilityMeasure (CadlagPath unitInterval ℝ))) atTop
        (@nhds (ProbabilityMeasure (CadlagPath unitInterval ℝ)) inferInstance P) ∧
      ∀ (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval),
        StrictMono grid → grid 0 = ⊥ →
        P.map (denseEvaluation grid) =
          (stableTimeLawProductProbability (μ := μ) α grid).map
            (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ) := by
  obtain ⟨sub, P, hsub, hconv, T, hTcount, hTdense, hTgood, hTbot, hTtop,
      hDenseLaw⟩ :=
    exists_subseq_normalizedStepPathLaw_with_stable_dense_grid_laws
      hDOA hStable htight hcenter
  refine ⟨sub, P, hsub, hconv, ?_⟩
  intro blocks grid hgrid hstart
  exact stable_grid_law_of_dense_grid_laws hStable hTdense
    (hTbot ⊥ isBot_bot) (hTtop ⊤ isTop_top) hDenseLaw grid hgrid hstart

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end
