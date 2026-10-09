/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import MeasureTheory.Measure.CadlagPath.ContinuityTimes

/-!
# Dense-coordinate identification for càdlàg path laws

For càdlàg paths, evaluations on any dense, ordered family containing the
right endpoint determine the path and its finite measure. This is the
path-space uniqueness interface used when the useful continuity times depend
on a weak cluster law.
-/

@[expose] public section

open Filter MeasureTheory
open Skorokhod
open scoped Topology

namespace MeasureTheory.CadlagPath

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


end MeasureTheory.CadlagPath

end
