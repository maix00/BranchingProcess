/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.CadlagPath.FiniteDimensional.Dense
public import Probability.ConvergenceInDistribution.Mapping
public import Topology.Cadlag.Skorokhod.Evaluation
public import Topology.Cadlag.Skorokhod.Endpoint

/-!
# Weak convergence of càdlàg path laws from finite grids

Tightness and convergence of finite-dimensional laws identify weak limits in
Skorokhod path space. The underlying dense-coordinate measure-uniqueness
results are in `MeasureTheory.Measure.CadlagPath.FiniteDimensional.Dense`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.CadlagPath
open Skorokhod
open scoped Topology

namespace ProbabilityTheory.CadlagPath

set_option maxHeartbeats 1000000 in
/-- Tightness and convergence of every finite real-time grid imply weak
convergence of càdlàg path laws. For each weak cluster law, Fubini supplies a
dense family of almost-sure continuity times; finite-grid convergence
identifies the coordinate laws there, and dense-coordinate uniqueness
identifies the path law. -/
theorem ProbabilityMeasure.tendsto_of_tight_of_finiteGridEvaluation
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    [FirstCountableTopology (ProbabilityMeasure (CadlagPath unitInterval ℝ))]
    (μ : ι → ProbabilityMeasure (CadlagPath unitInterval ℝ))
    (μ₀ : ProbabilityMeasure (CadlagPath unitInterval ℝ))
    (htight : IsTightMeasureSet
      {((μ i : ProbabilityMeasure (CadlagPath unitInterval ℝ)) :
        Measure (CadlagPath unitInterval ℝ)) | i})
    (hfinite : ∀ (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval),
      StrictMono grid → grid 0 = ⊥ →
        Tendsto (fun i => (μ i).map (denseEvaluation grid)) l
          (nhds (μ₀.map (denseEvaluation grid)))) :
    Tendsto μ l (nhds μ₀) := by
  have hcompact : IsCompact (closure (Set.range μ)) :=
    isCompact_closure_of_isTightMeasureSet (by simpa using htight)
  refine Filter.tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨μ', hμ'mem, sub, hsubStrict, hμsub⟩ :=
    hcompact.isSeqCompact fun k => subset_closure (Set.mem_range_self (ns k))
  have hsubAtTop : Tendsto sub atTop atTop := hsubStrict.tendsto_atTop

  let good : Set unitInterval := {t | ∀ᵐ path ∂(μ' : Measure (CadlagPath unitInterval ℝ)),
    ContinuousAt (fun s : unitInterval => path s) t}
  let candidate : Set unitInterval := good ∪ ({⊥, ⊤} : Set unitInterval)
  have hgoodDense : Dense good := dense_ae_continuityTimes_of_cadlag
    (μ' : Measure (CadlagPath unitInterval ℝ))
  have hcandidateDense : Dense candidate := hgoodDense.mono (by
    intro t ht
    exact Or.inl ht)
  obtain ⟨T, hTsub, hTcount, hTdense, hbot, htop⟩ :=
    hcandidateDense.exists_countable_dense_subset_bot_top
  let Index := T
  let time : Index → unitInterval := Subtype.val
  let : Countable Index := hTcount
  have htimeStrict : StrictMono time := by
    intro i j hij
    exact hij
  have htimeMono : Monotone time := htimeStrict.monotone
  have htimeDense : DenseRange time := hTdense.denseRange_val
  have htopRange : (⊤ : unitInterval) ∈ Set.range time :=
    ⟨⟨⊤, htop ⊤ isTop_top (by simp [candidate])⟩, rfl⟩
  have htimeEvaluationContinuous (i : Index) :
      ∀ᵐ path ∂(μ' : Measure (CadlagPath unitInterval ℝ)),
        ContinuousAt (fun p : CadlagPath unitInterval ℝ => p (time i)) path := by
    have hi := hTsub i.property
    rcases hi with hiGood | hiEnd
    · filter_upwards [hiGood] with path hpath
      exact continuousAt_apply_of_continuousAt path (time i) hpath
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hiEnd
      rcases hiEnd with hiBot | hiTop
      · filter_upwards [] with path
        simpa [time, hiBot] using
          (continuous_apply_bot.continuousAt :
            ContinuousAt (fun p : CadlagPath unitInterval ℝ => p ⊥) path)
      · filter_upwards [] with path
        simpa [time, hiTop] using
          (continuous_apply_top.continuousAt :
            ContinuousAt (fun p : CadlagPath unitInterval ℝ => p ⊤) path)

  have hgridMapEq (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval)
      (hgrid : StrictMono grid) (hstart : grid 0 = ⊥)
      (hvalues : ∀ j, grid j = ⊥ ∨ grid j ∈ Set.range time) :
      (μ' : Measure (CadlagPath unitInterval ℝ)).map (denseEvaluation grid) =
        (μ₀ : Measure (CadlagPath unitInterval ℝ)).map (denseEvaluation grid) := by
    have hcoordinate (j : Fin (blocks + 1)) :
        ∀ᵐ path ∂(μ' : Measure (CadlagPath unitInterval ℝ)),
          ContinuousAt (fun p : CadlagPath unitInterval ℝ => p (grid j)) path := by
      rcases hvalues j with hbot | ⟨i, hi⟩
      · rw [hbot]
        exact Filter.Eventually.of_forall fun path => continuous_apply_bot.continuousAt
      · filter_upwards [htimeEvaluationContinuous i] with path hcontinuous
        simpa only [hi] using hcontinuous
    have hall : ∀ᵐ path ∂(μ' : Measure (CadlagPath unitInterval ℝ)),
        ∀ j : Fin (blocks + 1),
          ContinuousAt (fun p : CadlagPath unitInterval ℝ => p (grid j)) path :=
      ae_all_iff.mpr hcoordinate
    have hcontinuous : ∀ᵐ path ∂(μ' : Measure (CadlagPath unitInterval ℝ)),
        ContinuousAt (denseEvaluation grid) path := by
      filter_upwards [hall] with path hpath
      change ContinuousAt (fun p : CadlagPath unitInterval ℝ =>
        fun j : Fin (blocks + 1) => p (grid j)) path
      exact continuousAt_pi.2 hpath
    have hfromCluster := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuousAt_ae
      hμsub (measurable_denseEvaluation grid) hcontinuous
    have hfromFinite := (hfinite blocks grid hgrid hstart).comp
      (hns.comp hsubAtTop)
    exact congrArg ProbabilityMeasure.toMeasure
      (tendsto_nhds_unique hfromCluster hfromFinite)

  have hfiniteDense (I : Finset Index) :
      (μ' : Measure (CadlagPath unitInterval ℝ)).map
          (denseEvaluation (fun i : I => time i.1)) =
        (μ₀ : Measure (CadlagPath unitInterval ℝ)).map
          (denseEvaluation (fun i : I => time i.1)) :=
    measure_map_finiteEvaluation_eq_of_gridEvaluation_eq time
      (μ' : Measure (CadlagPath unitInterval ℝ)) (μ₀ : Measure _)
      htimeStrict hgridMapEq I
  have hμ'eq : μ' = μ₀ := by
    apply Subtype.ext
    apply measure_eq_of_map_finiteDenseEvaluation_eq time htimeDense
      htimeMono htopRange (μ' : Measure (CadlagPath unitInterval ℝ))
      (μ₀ : Measure (CadlagPath unitInterval ℝ)) hfiniteDense
  exact ⟨sub, by simpa [hμ'eq, Function.comp_def] using hμsub⟩


end ProbabilityTheory.CadlagPath

end
