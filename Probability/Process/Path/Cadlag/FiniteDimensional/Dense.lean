/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Probability.Process.Path.Cadlag.ContinuityTimes
public import Probability.Process.Path.Cadlag.FiniteDimensional

/-!
# Dense-coordinate identification for càdlàg path laws

For càdlàg paths, evaluations on any dense, ordered family containing the
right endpoint determine the path and its finite measure. This is the
path-space uniqueness interface used when the useful continuity times depend
on a weak cluster law.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace Skorokhod

/-- Evaluate a càdlàg path on a chosen family of times. -/
def denseEvaluation {Index : Type*} (time : Index → unitInterval) :
    CadlagPath unitInterval ℝ → Index → ℝ :=
  fun path i => path (time i)

theorem measurable_denseEvaluation {Index : Type*} [MeasurableSpace Index]
    (time : Index → unitInterval) :
    Measurable (denseEvaluation time : CadlagPath unitInterval ℝ → Index → ℝ) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_apply (time i)

private theorem denseEvaluation_injective {Index : Type*} [LinearOrder Index]
    (time : Index → unitInterval) (htime : DenseRange time)
    (htimeMono : Monotone time) (htop : (⊤ : unitInterval) ∈ Set.range time) :
    Function.Injective (denseEvaluation time :
      CadlagPath unitInterval ℝ → Index → ℝ) := by
  intro f g hfg
  apply CadlagPath.ext (T := unitInterval) (E := ℝ)
  intro t
  by_cases ht : t = ⊤
  · subst t
    obtain ⟨i, hi⟩ := htop
    have heq := congrFun hfg i
    simpa [denseEvaluation, hi] using heq
  · have httop : t < ⊤ := (lt_top_iff_ne_top).2 ht
    obtain ⟨u, huanti, humem, hutend⟩ :=
      htime.exists_seq_strictAnti_tendsto_of_lt htimeMono httop
    have htimeTendsto : Tendsto (fun n => time (u n)) atTop (𝓝 t) := by
      simpa only [Function.comp_def] using hutend
    have htimeWithin : Tendsto (fun n => time (u n)) atTop (𝓝[Set.Ioi t] t) :=
      tendsto_nhdsWithin_iff.2 ⟨htimeTendsto,
        Filter.Eventually.of_forall fun n => (humem n).1⟩
    have hseq : ∀ n, f (time (u n)) = g (time (u n)) := by
      intro n
      exact congrFun hfg (u n)
    have hlimF : Tendsto (fun n => f (time (u n))) atTop (𝓝 (f t)) :=
      (f.isCadlag_toFun.isRightContinuous t).tendsto.comp htimeWithin
    have hlimG : Tendsto (fun n => g (time (u n))) atTop (𝓝 (g t)) :=
      (g.isCadlag_toFun.isRightContinuous t).tendsto.comp htimeWithin
    have hlimG' : Tendsto (fun n => f (time (u n))) atTop (𝓝 (g t)) := by
      simpa only [hseq] using hlimG
    exact tendsto_nhds_unique hlimF hlimG'

/-- Evaluations on a dense ordered time family containing the right endpoint
form a measurable embedding of real càdlàg path space. -/
theorem measurableEmbedding_denseEvaluation {Index : Type*} [Countable Index]
    [LinearOrder Index] [MeasurableSpace Index] (time : Index → unitInterval)
    (htime : DenseRange time) (htimeMono : Monotone time)
    (htop : (⊤ : unitInterval) ∈ Set.range time) :
    MeasurableEmbedding (denseEvaluation time :
      CadlagPath unitInterval ℝ → Index → ℝ) := by
  apply (measurable_denseEvaluation time).measurableEmbedding
  exact denseEvaluation_injective time htime htimeMono htop

/-- A finite family of times is read off from its strictly increasing grid
after prepending time zero. -/
theorem measure_map_finiteEvaluation_eq_of_gridEvaluation_eq
    {Index : Type*} [LinearOrder Index] [MeasurableSpace Index]
    (time : Index → unitInterval) (μ ν : Measure (CadlagPath unitInterval ℝ))
    (htime : StrictMono time)
    (hgrid : ∀ (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval),
      StrictMono grid → grid 0 = ⊥ →
        (∀ j, grid j = ⊥ ∨ grid j ∈ Set.range time) →
        μ.map (denseEvaluation grid) = ν.map (denseEvaluation grid))
    (I : Finset Index) :
    μ.map (denseEvaluation (fun i : I => time i.1)) =
      ν.map (denseEvaluation (fun i : I => time i.1)) := by
  let J : Finset Index := I.filter fun i => time i ≠ ⊥
  let grid : Fin (J.card + 1) → unitInterval :=
    Fin.cons ⊥ (fun j => time (J.orderEmbOfFin rfl j))
  have hgridStrict : StrictMono grid := by
    rw [Fin.strictMono_cons]
    constructor
    · intro j
      have hj := Finset.orderEmbOfFin_mem J rfl j
      have hj' := (Finset.mem_filter.mp hj).2
      exact lt_of_le_of_ne bot_le (Ne.symm hj')
    · exact htime.comp (J.orderEmbOfFin rfl).strictMono
  have hgridStart : grid 0 = ⊥ := by simp [grid]
  let coordinate : I → Fin (J.card + 1) := fun i =>
    if hbot : time i.1 = ⊥ then 0 else
      Fin.succ ((J.orderIsoOfFin rfl).symm
        ⟨i.1, Finset.mem_filter.mpr ⟨i.2, hbot⟩⟩)
  let project : (Fin (J.card + 1) → ℝ) → I → ℝ :=
    fun z i => z (coordinate i)
  have hprojectMeasurable : Measurable project := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply (coordinate i)
  have hprojectEval : project ∘ denseEvaluation grid =
      denseEvaluation (fun i : I => time i.1) := by
    funext path
    funext i
    by_cases hbot : time i.1 = ⊥
    · simp [project, coordinate, hbot, denseEvaluation, grid]
    · have hiJ : i.1 ∈ J := Finset.mem_filter.mpr ⟨i.2, hbot⟩
      let rank : Fin J.card := (J.orderIsoOfFin rfl).symm ⟨i.1, hiJ⟩
      have hrank : J.orderEmbOfFin rfl rank = i.1 := by
        change ((J.orderIsoOfFin rfl)
          ((J.orderIsoOfFin rfl).symm ⟨i.1, hiJ⟩)).val = i.1
        simp
      change (denseEvaluation grid path) (coordinate i) = path (time i.1)
      simp [denseEvaluation, coordinate, hbot, rank, grid, hrank]
  have hgridValues (j : Fin (J.card + 1)) : grid j = ⊥ ∨ grid j ∈ Set.range time := by
    refine Fin.cases ?_ ?_ j
    · exact Or.inl rfl
    · intro k
      exact Or.inr ⟨J.orderEmbOfFin rfl k, rfl⟩
  have hgridEq := hgrid J.card grid hgridStrict hgridStart hgridValues
  have hmapμ : (μ.map (denseEvaluation grid)).map project =
      μ.map (project ∘ denseEvaluation grid) :=
    Measure.map_map hprojectMeasurable (measurable_denseEvaluation grid)
  have hmapν : (ν.map (denseEvaluation grid)).map project =
      ν.map (project ∘ denseEvaluation grid) :=
    Measure.map_map hprojectMeasurable (measurable_denseEvaluation grid)
  have hprojected := congrArg (fun m => m.map project) hgridEq
  rw [hmapμ, hmapν, hprojectEval] at hprojected
  exact hprojected

/-- Two finite measures on càdlàg path space coincide when all finite
coordinate laws on a dense ordered time family containing the right endpoint
coincide. -/
theorem measure_eq_of_map_finiteDenseEvaluation_eq {Index : Type*}
    [Countable Index] [LinearOrder Index] [MeasurableSpace Index]
    (time : Index → unitInterval) (htime : DenseRange time)
    (htimeMono : Monotone time) (htop : (⊤ : unitInterval) ∈ Set.range time)
    (μ ν : Measure (CadlagPath unitInterval ℝ)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (hfinite : ∀ I : Finset Index,
      μ.map (denseEvaluation (fun i : I => time i)) =
        ν.map (denseEvaluation (fun i : I => time i))) :
    μ = ν := by
  let P : ∀ I : Finset Index, Measure (I → ℝ) := fun I =>
    μ.map (denseEvaluation (fun i : I => time i))
  have hμ : IsProjectiveLimit (μ.map (denseEvaluation time)) P := by
    intro I
    rw [Measure.map_map]
    · rfl
    · exact Measurable.of_eval fun _ => measurable_pi_apply _
    · exact measurable_denseEvaluation time
  have hν : IsProjectiveLimit (ν.map (denseEvaluation time)) P := by
    intro I
    rw [Measure.map_map]
    · exact hfinite I |>.symm
    · exact Measurable.of_eval fun _ => measurable_pi_apply _
    · exact measurable_denseEvaluation time
  exact (measurableEmbedding_denseEvaluation time htime htimeMono htop).map_injective
    (hμ.unique hν)

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
  have hgoodDense : Dense good := Skorokhod.dense_ae_continuityTimes_of_cadlag
    (μ' : Measure (CadlagPath unitInterval ℝ))
  have hcandidateDense : Dense candidate := hgoodDense.mono (by
    intro t ht
    exact Or.inl ht)
  obtain ⟨T, hTsub, hTcount, hTdense, hbot, htop⟩ :=
    hcandidateDense.exists_countable_dense_subset_bot_top
  let Index := T
  let time : Index → unitInterval := Subtype.val
  letI : Countable Index := hTcount
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

end Skorokhod

end
