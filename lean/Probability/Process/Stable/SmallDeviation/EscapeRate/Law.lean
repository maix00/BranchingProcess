import Probability.Process.Stable.SmallDeviation.EscapeRate

/-!
# Law invariance of stable-process escape rates

The range tube is defined by rational-time coordinates. Equal stable
increment specifications therefore give equal range-tube probabilities and,
consequently, the same escape-rate constant.
-/

@[expose] public section

namespace ProbabilityTheory

open Filter MeasureTheory
open scoped NNReal Topology

/-- Stable Lévy processes with the same index and one-step law have the same
rational range-tube probabilities at every width. -/
theorem IsStableLevyProcess.rationalRangeProbability_eq_of_same_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω' → ℝ}
    {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X P)
    (hY : IsStableLevyProcess α μ Y Q) (a : ℝ) :
    rationalRangeProbability P X a = rationalRangeProbability Q Y a := by
  let clock : RationalGrid.RationalUnitInterval → ℝ :=
    fun q => (rationalUnitTime q : ℝ)
  have hXclock : HasStableClockIncrements α μ clock
      (fun q ω => X (rationalUnitTime q) ω) P := by
    exact hX.increments.comp_time rationalUnitTime monotone_rationalUnitTime
      rationalUnitTime_bot
  have hYclock : HasStableClockIncrements α μ clock
      (fun q ω => Y (rationalUnitTime q) ω) Q := by
    exact hY.increments.comp_time rationalUnitTime monotone_rationalUnitTime
      rationalUnitTime_bot
  have hlaw := hXclock.process_identDistrib_of_aemeasurable hYclock
    (AEMeasurable.of_eval fun q => hXclock.aemeasurable_eval q)
    (AEMeasurable.of_eval fun q => hYclock.aemeasurable_eval q)
  have hprob := hlaw.measure_mem_eq
    (Skorokhod.measurableSet_rationalCoordinateOscillationTube (2 * a))
  have hprob' : P (rationalHorizonTubeEvent X 1 (2 * a)) =
      Q (rationalHorizonTubeEvent Y 1 (2 * a)) := by
    change P ((fun ω q => X (1 * rationalUnitTime q) ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube (2 * a)) =
      Q ((fun ω q => Y (1 * rationalUnitTime q) ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube (2 * a))
    simpa only [one_mul] using hprob
  simpa [rationalRangeProbability] using hprob'

/-- Whenever the normalized rational range log probabilities for two stable
processes have limits, the limits agree if their stable increment laws agree.
In particular, the escape-rate constant depends only on the stable law. -/
theorem IsStableLevyProcess.escapeRate_constant_eq_of_same_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {α C D : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω' → ℝ}
    {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X P)
    (hY : IsStableLevyProcess α μ Y Q)
    (hC : Tendsto (stableRangeLogRate P X α)
      (𝓝[>] (0 : ℝ)) (𝓝 C))
    (hD : Tendsto (stableRangeLogRate Q Y α)
      (𝓝[>] (0 : ℝ)) (𝓝 D)) :
    C = D := by
  have hrate : stableRangeLogRate P X α = stableRangeLogRate Q Y α := by
    funext a
    simp only [stableRangeLogRate]
    rw [hX.rationalRangeProbability_eq_of_same_law hY a]
  rw [hrate] at hC
  exact tendsto_nhds_unique hC hD

end ProbabilityTheory

end
