/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.EscapeRate
public import Probability.Process.Stable.Levy
public import Probability.Process.Corridor.Range
public import Mathlib.Probability.CDF

import Probability.Process.Stable.FiniteDimensional
import Probability.Process.Stable.SmallDeviation.EscapeRate
import Probability.Process.Path.Skorokhod.RationalTime

/-!
# Stable escape rates on càdlàg path laws

The rational-coordinate description of a range tube lets a unit-interval
stable path law inherit the process-level escape rate whenever it has the same
stable increment specification as a stable Lévy process.
-/

open Filter MeasureTheory
open scoped NNReal Topology

@[expose] public section

namespace ProbabilityTheory

/-- A càdlàg path law with stable clock increments has the same unit-time
tube probability as any stable Lévy process with that increment law. This is
the exact path-law transfer used by the escape-rate corollary below. -/
theorem IsStableClockProcessLaw.measure_stableProcessTube_eq_rationalRangeProbability
    {α : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hX : IsStableLevyProcess α μ X Q) (a : ℝ) :
    P (stableProcessTube a) = rationalRangeProbability Q X a := by
  let pathCoordinates : CadlagPath unitInterval ℝ →
      RationalGrid.RationalUnitInterval → ℝ :=
    fun f q => f (RationalGrid.unitCoe q)
  have hunitCoeMonotone : Monotone RationalGrid.unitCoe := by
    intro q r hqr
    change ((q : ℚ) : ℝ) ≤ ((r : ℚ) : ℝ)
    exact_mod_cast hqr
  have hunitCoeBot : RationalGrid.unitCoe ⊥ = ⊥ := by
    apply Subtype.ext
    norm_num [RationalGrid.unitCoe]
  have hPbase : HasStableClockIncrements α μ unitIntervalClock
      cadlagPathProcess P := hP
  have hPgrid0 := hPbase.comp_time RationalGrid.unitCoe
    hunitCoeMonotone hunitCoeBot
  change HasStableClockIncrements α μ
    (fun q => unitIntervalClock (RationalGrid.unitCoe q))
    (fun q f => f (RationalGrid.unitCoe q)) P at hPgrid0
  have hPgrid : HasStableClockIncrements α μ
      (fun q => (rationalUnitTime q : ℝ))
      (fun q f => pathCoordinates f q) P := by
    convert hPgrid0 using 1
    · funext q
      exact (rationalUnitTime_coe q).symm
  have hXgrid0 := hX.increments.comp_time rationalUnitTime
    monotone_rationalUnitTime rationalUnitTime_bot
  have hXgrid : HasStableClockIncrements α μ
      (fun q => (rationalUnitTime q : ℝ))
      (fun q ω => X (rationalUnitTime q) ω) Q := by
    convert hXgrid0 using 1
  have hlaw := hPgrid.process_identDistrib_of_aemeasurable hXgrid
    (AEMeasurable.of_eval fun q => hPgrid.aemeasurable_eval q)
    (AEMeasurable.of_eval fun q => hXgrid.aemeasurable_eval q)
  have hcoord :
      P (stableProcessRangeTube a) =
        Q (rationalHorizonTubeEvent X 1 (2 * a)) := by
    have hmeas := hlaw.measure_mem_eq
      (Skorokhod.measurableSet_rationalCoordinateOscillationTube (2 * a))
    have hmeas' :
        P (pathCoordinates ⁻¹'
          Skorokhod.rationalCoordinateOscillationTube (2 * a)) =
        Q ((fun ω q => X (rationalUnitTime q) ω) ⁻¹'
          Skorokhod.rationalCoordinateOscillationTube (2 * a)) := by
      simpa [pathCoordinates] using hmeas
    have hset : stableProcessRangeTube a =
        pathCoordinates ⁻¹' Skorokhod.rationalCoordinateOscillationTube (2 * a) := by
      ext f
      rw [stableProcessRangeTube,
        ← Skorokhod.rationalOscillationInOpenTube_eq]
      rfl
    rw [hset]
    change P (pathCoordinates ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube (2 * a)) =
      Q ((fun ω q => X (1 * rationalUnitTime q) ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube (2 * a))
    simpa only [one_mul] using hmeas'
  calc
    P (stableProcessTube a) = P (stableProcessRangeTube a) :=
      measure_stableProcessTube_eq_rangeTube hP a
    _ = rationalRangeProbability Q X a := by
      simpa [rationalRangeProbability] using hcoord

/-- A stable path law on the unit interval has the same tube probabilities,
and hence the same escape rate, as any stable Lévy process with the same
increment specification. The reference process supplies the process-level
long-horizon escape-rate theorem; no path-space extension theorem is assumed.
-/
theorem IsStableClockProcessLaw.hasStableProcessEscapeRate_of_isStableLevyProcess
    {α : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    ∃ C, HasStableProcessEscapeRate α μ P C := by
  have hprob (a : ℝ) :=
    hP.measure_stableProcessTube_eq_rationalRangeProbability hX a
  obtain ⟨C, hC, hlim⟩ := hX.exists_rationalRange_escape_rate hcdf
  have hpos : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ),
      0 < (P (stableProcessTube a)).toReal := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have hRa : 0 < rationalRangeProbability Q X a :=
      hX.rationalRangeProbability_pos_of_cdf hcdf ha
    rw [hprob]
    exact ENNReal.toReal_pos_iff.mpr
      ⟨hRa, measure_lt_top Q (rationalHorizonTubeEvent X 1 (2 * a))⟩
  refine ⟨C, hP, hC, hpos, ?_⟩
  have hrate :
      (fun a => a ^ α * Real.log ((P (stableProcessTube a)).toReal)) =
        stableRangeLogRate Q X α := by
    funext a
    simp [stableRangeLogRate, hprob]
  rw [hrate]
  exact hlim

end ProbabilityTheory

end
