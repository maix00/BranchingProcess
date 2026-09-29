import Mathlib.Topology.UnitInterval
import Probability.BranchingRandomWalk.Walk.Path.Skorokhod
import Probability.BranchingRandomWalk.Walk.Path.Skorokhod.Corridor.Endpoint
import Probability.ConvergenceInDistribution.Portmanteau
import Topology.Cadlag.Skorokhod.Corridor.Weight

/-!
# Weighted functional-limit bounds for walk corridors

Portmanteau applies to continuous nonnegative path weights as well as open
events. The corridor cutoff below turns that fact into a weighted lower bound
for the discrete killed-walk block, retaining endpoint information needed by
core-to-core estimates.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- A functional limit theorem transfers a continuous nonnegative path
weight to a `liminf` of its expectations under the normalized random-walk
path laws. -/
theorem lintegral_map_le_liminf_normalizedStepPathLaw_of_functionalLimit
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ)
    (limit : Ω → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc scale n)
      atTop limit (fun _ => independentIncrementLaw ν) P)
    {f : CadlagPath unitInterval ℝ → ℝ}
    (hf : Continuous f) (hfnn : ∀ path, 0 ≤ f path) :
    ∫⁻ path, ENNReal.ofReal (f path) ∂P.map limit ≤
      atTop.liminf (fun n =>
        ∫⁻ path, ENNReal.ofReal (f path) ∂normalizedStepPathLaw ν scale n) := by
  simpa [normalizedStepPathLaw] using
    (MeasureTheory.TendstoInDistribution.lintegral_map_le_liminf_of_continuous_nonneg
      hlimit hf hfnn)

/-- The continuous corridor/endpoint cutoff is bounded by the probability of
the corresponding path event. -/
theorem lintegral_corridorEndsInWeight_le_measure
    (μ : Measure (CadlagPath unitInterval ℝ))
    (lower upper endpointLower endpointUpper : ℝ) :
    ∫⁻ path, ENNReal.ofReal
        (Skorokhod.corridorEndsInWeight lower upper endpointLower endpointUpper path) ∂μ ≤
      μ (Skorokhod.rangeInOpenIntervalEndsIn
        lower upper endpointLower endpointUpper) := by
  let pathConstant : (CadlagPath unitInterval ℝ) → ℝ≥0∞ :=
    fun _ => 1
  let event := Skorokhod.rangeInOpenIntervalEndsIn
    lower upper endpointLower endpointUpper
  calc
    ∫⁻ path, ENNReal.ofReal
        (Skorokhod.corridorEndsInWeight lower upper endpointLower endpointUpper path) ∂μ ≤
        ∫⁻ path, (Set.indicator event pathConstant path) ∂μ := by
      apply lintegral_mono
      intro path
      by_cases hevent : path ∈ event
      · rw [Set.indicator_of_mem hevent]
        change ENNReal.ofReal
          (Skorokhod.corridorEndsInWeight lower upper endpointLower endpointUpper path) ≤ 1
        exact ENNReal.ofReal_le_one.mpr
          (Skorokhod.corridorEndsInWeight_le_one
            lower upper endpointLower endpointUpper path)
      · have hnotpos : ¬ 0 <
            Skorokhod.corridorEndsInWeight lower upper endpointLower endpointUpper path := by
          intro hpos
          apply hevent
          rw [Skorokhod.mem_rangeInOpenIntervalEndsIn_iff]
          exact (Skorokhod.corridorEndsInWeight_pos_iff
            lower upper endpointLower endpointUpper path).mp hpos
        have hzero :
            Skorokhod.corridorEndsInWeight lower upper endpointLower endpointUpper path = 0 :=
          le_antisymm (le_of_not_gt hnotpos)
            (Skorokhod.corridorEndsInWeight_nonneg
              lower upper endpointLower endpointUpper path)
        rw [Set.indicator_of_notMem hevent]
        change ENNReal.ofReal
          (Skorokhod.corridorEndsInWeight lower upper endpointLower endpointUpper path) ≤ 0
        simp [hzero]
    _ ≤ μ event := by
      dsimp [pathConstant]
      exact lintegral_indicator_one_le event

/-- Under the canonical i.i.d. increment law, the cutoff integral for a
normalized step path is bounded by the strict tube event with its prescribed
normalized endpoint interval. -/
theorem lintegral_centeredCorridorEndsInWeight_le_strictTubeEndsIn
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (hscale : 0 < scale n)
    {width endpointLower endpointUpper : ℝ} (hwidth : 0 < width) :
    ∫⁻ path, ENNReal.ofReal
        (Skorokhod.corridorEndsInWeight
          (-(width / 2)) (width / 2) endpointLower endpointUpper path) ∂
          normalizedStepPathLaw ν scale n ≤
      independentIncrementLaw ν {increment |
        InOpenHorizontalTube (1 / 2) (width * scale n) n increment ∧
          partialSum n increment / scale n ∈
            Set.Ioo endpointLower endpointUpper} := by
  calc
    _ ≤ normalizedStepPathLaw ν scale n
        (Skorokhod.rangeInOpenIntervalEndsIn
          (-(width / 2)) (width / 2) endpointLower endpointUpper) :=
      lintegral_corridorEndsInWeight_le_measure
        (normalizedStepPathLaw ν scale n)
        (-(width / 2)) (width / 2) endpointLower endpointUpper
    _ = _ := normalizedStepPathLaw_apply_centeredOpenIntervalEndsIn
      ν scale hn hscale hwidth

/-- For a Donsker limit, the limiting weighted corridor integral is bounded
by the `liminf` of the discrete weighted path integrals. Unlike the event
version, the weight preserves the endpoint mode needed for later kernel
iteration. -/
theorem lintegral_map_corridorEndsInWeight_le_liminf_normalizedStepPathLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ)
    (limit : Ω → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc scale n)
      atTop limit (fun _ => independentIncrementLaw ν) P)
    {width endpointLower endpointUpper : ℝ} (_hwidth : 0 < width) :
    ∫⁻ path, ENNReal.ofReal
        (Skorokhod.corridorEndsInWeight
          (-(width / 2)) (width / 2) endpointLower endpointUpper path) ∂
          P.map limit ≤
      atTop.liminf (fun n =>
        ∫⁻ path, ENNReal.ofReal
          (Skorokhod.corridorEndsInWeight
            (-(width / 2)) (width / 2) endpointLower endpointUpper path) ∂
            normalizedStepPathLaw ν scale n) :=
  lintegral_map_le_liminf_normalizedStepPathLaw_of_functionalLimit
    P ν scale limit hlimit
    (Skorokhod.continuous_corridorEndsInWeight _ _ _ _)
    (fun path => Skorokhod.corridorEndsInWeight_nonneg _ _ _ _ path)

/-- The Donsker limit also transfers a corridor weight carrying an arbitrary
continuous nonnegative endpoint potential. This is the test-function form
needed for a positive eigenfunction of the killed transition operator. -/
theorem lintegral_map_corridorPotentialWeight_le_liminf_normalizedStepPathLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ)
    (limit : Ω → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc scale n)
      atTop limit (fun _ => independentIncrementLaw ν) P)
    {lower upper : ℝ} {potential : ℝ → ℝ}
    (hpotential : Continuous potential)
    (hpotentialNonneg : ∀ x, 0 ≤ potential x) :
    ∫⁻ path, ENNReal.ofReal
        (Skorokhod.corridorPotentialWeight lower upper potential path) ∂
          P.map limit ≤
      atTop.liminf (fun n =>
        ∫⁻ path, ENNReal.ofReal
          (Skorokhod.corridorPotentialWeight lower upper potential path) ∂
            normalizedStepPathLaw ν scale n) :=
  lintegral_map_le_liminf_normalizedStepPathLaw_of_functionalLimit
    P ν scale limit hlimit
    (Skorokhod.continuous_corridorPotentialWeight lower upper hpotential)
    (Skorokhod.corridorPotentialWeight_nonneg lower upper potential
      hpotentialNonneg)

end ProbabilityTheory.RandomWalk
