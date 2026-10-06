/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Probability.ConvergenceInDistribution.Mapping
public import Probability.Process.Path.FiniteDimensional
public import MeasureTheory.MeasurableSpace.CadlagPath
public import Topology.Cadlag.Skorokhod.Endpoint
public import Topology.Cadlag.Skorokhod.Evaluation

/-!
# Finite-dimensional identification for càdlàg path laws

Finite rational-time coordinates generate the Borel structure of real-valued
Skorokhod path space. This file combines that uniqueness result with tightness
and the almost-everywhere continuous mapping theorem. The continuity premise
is required for every possible weak cluster law; continuity only under the
target law does not by itself identify those cluster laws.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped Topology

namespace Skorokhod

/-- Restrict a càdlàg path to a finite family of rational times. -/
def finiteRationalEvaluation
    (I : Finset RationalUnitIntervalTime) :
    CadlagPath unitInterval ℝ → (I → ℝ) :=
  fun path q => path (rationalTimeToUnitInterval q.1)

theorem measurable_finiteRationalEvaluation
    (I : Finset RationalUnitIntervalTime) :
    Measurable (finiteRationalEvaluation I) := by
  rw [measurable_pi_iff]
  intro q
  exact measurable_apply (rationalTimeToUnitInterval q.1)

/-- Finite-dimensional laws on rational times determine a finite measure on
real-valued càdlàg Skorokhod path space. -/
theorem measure_eq_of_map_finiteRationalEvaluation_eq
    (μ ν : Measure (CadlagPath unitInterval ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfinite : ∀ I : Finset RationalUnitIntervalTime,
      μ.map (finiteRationalEvaluation I) =
        ν.map (finiteRationalEvaluation I)) :
    μ = ν := by
  let P : ∀ I : Finset RationalUnitIntervalTime, Measure (I → ℝ) := fun I =>
    μ.map (finiteRationalEvaluation I)
  have hμ : IsProjectiveLimit (μ.map rationalEvaluation) P := by
    intro I
    rw [Measure.map_map]
    · rfl
    · exact Measurable.of_eval fun _ => measurable_pi_apply _
    · exact measurable_rationalEvaluation
  have hν : IsProjectiveLimit (ν.map rationalEvaluation) P := by
    intro I
    rw [Measure.map_map]
    · exact hfinite I |>.symm
    · exact Measurable.of_eval fun _ => measurable_pi_apply _
    · exact measurable_rationalEvaluation
  exact measurableEmbedding_rationalEvaluation.map_injective (hμ.unique hν)

set_option maxHeartbeats 1000000 in
/-- Tightness and convergence of all finite rational-coordinate laws imply
weak convergence, provided each weak cluster law gives full mass to paths
continuous at every selected interior rational time. Endpoint evaluations are
already continuous in the `J₁` topology. -/
theorem ProbabilityMeasure.tendsto_of_tight_of_finiteRationalEvaluation
    {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated]
    [FirstCountableTopology (ProbabilityMeasure (CadlagPath unitInterval ℝ))]
    (μ : ι → ProbabilityMeasure (CadlagPath unitInterval ℝ))
    (μ₀ : ProbabilityMeasure (CadlagPath unitInterval ℝ))
    (htight : IsTightMeasureSet
      {((μ i : ProbabilityMeasure (CadlagPath unitInterval ℝ)) :
        Measure (CadlagPath unitInterval ℝ)) | i})
    (hfinite : ∀ I : Finset RationalUnitIntervalTime,
      Tendsto (fun i => (μ i).map (finiteRationalEvaluation I)) l
        (nhds (μ₀.map (finiteRationalEvaluation I))))
    (hclusterContinuous : ∀ μ' ∈ closure (Set.range μ),
      ∀ q : RationalUnitIntervalTime,
        rationalTimeToUnitInterval q ≠ ⊥ →
        rationalTimeToUnitInterval q ≠ ⊤ →
        ∀ᵐ path ∂(μ' : Measure (CadlagPath unitInterval ℝ)),
          ContinuousAt (fun t : unitInterval => path t)
            (rationalTimeToUnitInterval q)) :
    Tendsto μ l (nhds μ₀) := by
  have hcompact : IsCompact (closure (Set.range μ)) :=
    isCompact_closure_of_isTightMeasureSet (by simpa using htight)
  refine Filter.tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨μ', hμ'mem, sub, hsubStrict, hμsub⟩ :=
    hcompact.isSeqCompact fun k =>
      subset_closure (Set.mem_range_self (ns k))
  have hsubAtTop : Tendsto sub atTop atTop := hsubStrict.tendsto_atTop
  have hμ'eq : μ' = μ₀ := by
    apply Subtype.ext
    apply measure_eq_of_map_finiteRationalEvaluation_eq
      (μ'.toFiniteMeasure : Measure (CadlagPath unitInterval ℝ))
      (μ₀.toFiniteMeasure : Measure (CadlagPath unitInterval ℝ))
    intro I
    have hclusterEval : ∀ᵐ path ∂(μ' : Measure (CadlagPath unitInterval ℝ)),
        ContinuousAt (finiteRationalEvaluation I) path := by
      have hcoordinates : ∀ q : I, ∀ᵐ path : CadlagPath unitInterval ℝ ∂
          (μ' : Measure (CadlagPath unitInterval ℝ)),
            ContinuousAt (fun p : CadlagPath unitInterval ℝ =>
              p (rationalTimeToUnitInterval q.1)) path := by
        intro q
        let t := rationalTimeToUnitInterval q.1
        by_cases ht0 : t = ⊥
        · have ht0' : rationalTimeToUnitInterval q.1 = ⊥ := by
            simpa [t] using ht0
          rw [ht0']
          exact Filter.Eventually.of_forall fun path =>
            continuous_apply_bot.continuousAt
        · by_cases ht1 : t = ⊤
          · have ht1' : rationalTimeToUnitInterval q.1 = ⊤ := by
              simpa [t] using ht1
            rw [ht1']
            exact Filter.Eventually.of_forall fun path =>
              continuous_apply_top.continuousAt
          · have ht0' : rationalTimeToUnitInterval q.1 ≠ ⊥ := by
              simpa [t] using ht0
            have ht1' : rationalTimeToUnitInterval q.1 ≠ ⊤ := by
              simpa [t] using ht1
            filter_upwards
                [hclusterContinuous μ' hμ'mem q.1 ht0' ht1'] with path hpath
            exact continuousAt_apply_of_continuousAt path
              (rationalTimeToUnitInterval q.1) hpath
      have hall : ∀ᵐ path : CadlagPath unitInterval ℝ ∂
          (μ' : Measure (CadlagPath unitInterval ℝ)),
            ∀ q : I, ContinuousAt (fun p : CadlagPath unitInterval ℝ =>
              p (rationalTimeToUnitInterval q.1)) path :=
        ae_all_iff.mpr hcoordinates
      filter_upwards [hall] with path hpath
      change ContinuousAt (fun p : CadlagPath unitInterval ℝ =>
        fun q : I => p (rationalTimeToUnitInterval q.1)) path
      exact continuousAt_pi.2 hpath
    have hlimitFromCluster : Tendsto
        (fun k => (μ (ns (sub k))).map (finiteRationalEvaluation I)) atTop
        (nhds (μ'.map (finiteRationalEvaluation I))) :=
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuousAt_ae
        hμsub (measurable_finiteRationalEvaluation I) hclusterEval
    have hlimitTarget := (hfinite I).comp (hns.comp hsubAtTop)
    exact congrArg ProbabilityMeasure.toMeasure
      (tendsto_nhds_unique hlimitFromCluster hlimitTarget)
  exact ⟨sub, by simpa [hμ'eq, Function.comp_def] using hμsub⟩

end Skorokhod

end
