/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Topology.Instances.Real.Lemmas
public import Order.Interval.RationalCoordinate.UnitInterval
public import Topology.Cadlag.Skorokhod.Evaluation.Measurable
public import Topology.Cadlag.Skorokhod.Path.Separable
public import Topology.Order.UnitInterval.Rational

/-!
# Measurable coordinates on càdlàg Skorokhod path space

For real-valued paths over the compact unit interval, evaluation on a dense
ordered family containing the terminal time is a measurable embedding. The
canonical rational family generates the Borel structure of the Skorokhod
`J₁` topology.

## Public declarations

Evaluations on a countable dense ordered family containing the terminal time
form a measurable embedding; the rational coordinates generate the Borel
structure of the Skorokhod path space:

\[
f\longmapsto(f(t_i))_{i\in I},
\qquad
\mathcal B(D([0,1],\mathbb R))
=\operatorname{comap}\!\left(f\mapsto(f(q))_{q\in\mathbb Q\cap[0,1]},
\mathcal B(\mathbb R^{\mathbb Q\cap[0,1]})\right).
\]

- `MeasureTheory.CadlagPath.denseEvaluation time` maps `f` to
  `i ↦ f (time i)`; when `time` is countable, monotone, dense, and contains
  `1`, this map is a measurable embedding.
- `Skorokhod.measurableEmbedding_rationalEvaluation` specializes the embedding
  to `RationalCoordinate.UnitInterval`; the Borel sigma algebra is the comap
  of the product Borel structure along these coordinates.
-/

@[expose] public section

open Filter MeasureTheory Set
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
  exact Skorokhod.measurable_apply (time i)

private lemma denseEvaluation_injective {Index : Type*} [LinearOrder Index]
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

end MeasureTheory.CadlagPath

namespace Skorokhod

/-- Evaluation on the canonical rational coordinates is a measurable
embedding of real càdlàg path space. -/
theorem measurableEmbedding_rationalEvaluation :
    MeasurableEmbedding (MeasureTheory.CadlagPath.denseEvaluation
      RationalCoordinate.toUnitInterval :
        CadlagPath unitInterval ℝ → RationalCoordinate.UnitInterval → ℝ) := by
  let time := RationalCoordinate.toUnitInterval
  have hstrict : StrictMono time := by
    intro q r hqr
    change ((q : ℚ) : ℝ) < ((r : ℚ) : ℝ)
    exact_mod_cast hqr
  have htop : (⊤ : unitInterval) ∈ Set.range time := by
    refine ⟨⟨1, by norm_num⟩, ?_⟩
    apply Subtype.ext
    norm_num [time, RationalCoordinate.toUnitInterval]
  exact MeasureTheory.CadlagPath.measurableEmbedding_denseEvaluation time
    RationalCoordinate.denseRange_toUnitInterval hstrict.monotone htop

/-- The Borel sigma algebra of real càdlàg `J₁` paths is the sigma algebra
generated by rational-time evaluations. -/
theorem borel_eq_comap_rationalEvaluation :
    borel (CadlagPath unitInterval ℝ) =
      MeasurableSpace.comap (MeasureTheory.CadlagPath.denseEvaluation
        RationalCoordinate.toUnitInterval)
        (inferInstance :
          MeasurableSpace (RationalCoordinate.UnitInterval → ℝ)) := by
  exact measurableEmbedding_rationalEvaluation.comap_eq.symm

end Skorokhod

end
