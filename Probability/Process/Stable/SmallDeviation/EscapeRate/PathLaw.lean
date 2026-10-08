/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalCoordinate.UnitInterval
public import Probability.Process.Stable.EscapeRate
public import Probability.Process.Stable.Levy
public import Probability.Process.Corridor.Range
public import Probability.Process.Path.Skorokhod.Corridor.Segment
public import Mathlib.Probability.CDF

import Probability.Process.Stable.FiniteDimensional
public import Probability.Process.Stable.SmallDeviation.EscapeRate
import Probability.Process.Path.Skorokhod.RationalTime
import Topology.Order.UnitInterval.Rational

/-!
# Stable escape rates on càdlàg path laws

The rational-coordinate description of a range tube lets a unit-interval
stable path law inherit the process-level escape rate whenever it has the same
stable increment specification as a stable Lévy process.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

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
      RationalCoordinate.UnitInterval → ℝ :=
    fun f q => f (RationalCoordinate.toUnitInterval q)
  have htoUnitIntervalMonotone : Monotone RationalCoordinate.toUnitInterval := by
    intro q r hqr
    change ((q : ℚ) : ℝ) ≤ ((r : ℚ) : ℝ)
    exact_mod_cast hqr
  have htoUnitIntervalBot : RationalCoordinate.toUnitInterval ⊥ = ⊥ := by
    apply Subtype.ext
    norm_num [RationalCoordinate.toUnitInterval]
  have hPbase : HasStableClockIncrements α μ unitIntervalClock
      cadlagPathProcess P := hP
  have hPgrid0 := hPbase.comp_time RationalCoordinate.toUnitInterval
    htoUnitIntervalMonotone htoUnitIntervalBot
  change HasStableClockIncrements α μ
    (fun q => unitIntervalClock (RationalCoordinate.toUnitInterval q))
    (fun q f => f (RationalCoordinate.toUnitInterval q)) P at hPgrid0
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

/-- A path-law escape rate transfers to the matching stable Lévy process's
rational range probability with the same constant. -/
theorem HasStableProcessEscapeRate.tendsto_stableRangeLogRate_of_isStableLevyProcess
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    (hX : IsStableLevyProcess α μ X Q) :
    Tendsto (stableRangeLogRate Q X α)
      (𝓝[>] (0 : ℝ)) (𝓝 C) := by
  have hP := hEscape.isStableClockProcessLaw
  have heq : (fun a : ℝ => a ^ α * Real.log
      ((P (stableProcessTube a)).toReal)) = stableRangeLogRate Q X α := by
    funext a
    simp [stableRangeLogRate,
      hP.measure_stableProcessTube_eq_rationalRangeProbability hX a]
  exact hEscape.tendsto.congr'
    (Filter.Eventually.of_forall fun a => congrFun heq a)

/-- A finite sum of stable tube logarithms inherits the single-tube escape
rate term by term. This is the analytic step used after the independent-cell
upper product for a finite step corridor. -/
theorem HasStableProcessEscapeRate.tendsto_invRpow_mul_sum_log_stableProcessTube
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {ι : Type*} (s : Finset ι) (radius : ι → ℝ)
    (hradius : ∀ i ∈ s, 0 < radius i) :
    Tendsto
      (fun c : ℝ => c⁻¹ ^ α *
        ∑ i ∈ s, Real.log ((P (stableProcessTube (radius i / c))).toReal))
      atTop
      (𝓝 (∑ i ∈ s, C / radius i ^ α)) := by
  have hterm : ∀ i ∈ s,
      Tendsto
        (fun c : ℝ => c⁻¹ ^ α *
          Real.log ((P (stableProcessTube (radius i / c))).toReal))
        atTop (𝓝 (C / radius i ^ α)) := by
    intro i hi
    exact hEscape.tendsto_inv_rpow_mul_log_stableProcessTube (hradius i hi)
  have hsum := tendsto_finsetSum s hterm
  have hsumEq :
      (fun c : ℝ => c⁻¹ ^ α *
        ∑ i ∈ s, Real.log ((P (stableProcessTube (radius i / c))).toReal)) =
      (fun c : ℝ => ∑ i ∈ s, c⁻¹ ^ α *
        Real.log ((P (stableProcessTube (radius i / c))).toReal)) := by
    funext c
    rw [Finset.mul_sum]
  rw [hsumEq]
  exact hsum

/-- A stable càdlàg path law and a stable Lévy process with the same
increment specification assign the same probability to a complete open
corridor with an open terminal window. The bridge is finite-dimensional law
equality on rational coordinates, followed by the càdlàg corridor
characterization. -/
theorem IsStableClockProcessLaw.measure_corridorReturnEvent_eq
    {α : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hX : IsStableLevyProcess α μ X Q)
    (lower upper coreLower coreUpper : ℝ) :
    P (Skorokhod.rangeInOpenIntervalEndsIn lower upper coreLower coreUpper) =
      Q (fullSegmentCorridorReturnEvent X 0 1 lower upper coreLower coreUpper) := by
  let pathCoordinates : CadlagPath unitInterval ℝ →
      RationalCoordinate.UnitInterval → ℝ :=
    fun f q => f (RationalCoordinate.toUnitInterval q)
  have htoUnitIntervalMonotone : Monotone RationalCoordinate.toUnitInterval := by
    intro q r hqr
    change ((q : ℚ) : ℝ) ≤ ((r : ℚ) : ℝ)
    exact_mod_cast hqr
  have htoUnitIntervalBot : RationalCoordinate.toUnitInterval ⊥ = ⊥ := by
    apply Subtype.ext
    norm_num [RationalCoordinate.toUnitInterval]
  have hPbase : HasStableClockIncrements α μ unitIntervalClock
      cadlagPathProcess P := hP
  have hPgrid0 := hPbase.comp_time RationalCoordinate.toUnitInterval
    htoUnitIntervalMonotone htoUnitIntervalBot
  change HasStableClockIncrements α μ
    (fun q => unitIntervalClock (RationalCoordinate.toUnitInterval q))
    (fun q f => f (RationalCoordinate.toUnitInterval q)) P at hPgrid0
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
  let rationalCorridor := Skorokhod.rationalCoordinateCorridorReturnWithMargin
    lower upper coreLower coreUpper
  have hcoord := hlaw.measure_mem_eq
    (Skorokhod.measurableSet_rationalCoordinateCorridorReturnWithMargin
      lower upper coreLower coreUpper)
  have hpathSet :
      Skorokhod.rangeInOpenIntervalEndsIn lower upper coreLower coreUpper =
        pathCoordinates ⁻¹' rationalCorridor := by
    ext f
    change (f ∈ Skorokhod.rangeInOpenInterval lower upper ∧
      f ⊤ ∈ Set.Ioo coreLower coreUpper) ↔
      pathCoordinates f ∈ Skorokhod.rationalCoordinateCorridorReturnWithMargin
        lower upper coreLower coreUpper
    rw [Skorokhod.rationalCoordinateCorridorReturnWithMargin]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    have htop : RationalCoordinate.toUnitInterval ⊤ = (⊤ : unitInterval) := by
      apply Subtype.ext
      norm_num [RationalCoordinate.toUnitInterval]
    change (f ∈ Skorokhod.rangeInOpenInterval lower upper ∧
      f ⊤ ∈ Set.Ioo coreLower coreUpper) ↔
      ((fun q => f (RationalCoordinate.toUnitInterval q)) ∈
          Skorokhod.rationalCoordinateCorridorWithMargin lower upper ∧
        f (RationalCoordinate.toUnitInterval ⊤) ∈
          Set.Ioo coreLower coreUpper)
    constructor
    · rintro ⟨hpath, hend⟩
      exact ⟨(Skorokhod.mem_rationalCoordinateCorridorWithMargin_iff
        f lower upper).mpr hpath, by simpa [htop] using hend⟩
    · rintro ⟨hpath, hend⟩
      exact ⟨(Skorokhod.mem_rationalCoordinateCorridorWithMargin_iff
        f lower upper).mp hpath, by simpa [htop] using hend⟩
  have hpathMeasure :
      P (Skorokhod.rangeInOpenIntervalEndsIn lower upper coreLower coreUpper) =
        P (pathCoordinates ⁻¹' rationalCorridor) := by
    rw [hpathSet]
  have hstart : ∀ᵐ ω ∂Q, X 0 ω = 0 := hX.increments.ae_start_eq_zero
  have hcoordinateEq :
      Q ((fun ω q => X (rationalUnitTime q) ω) ⁻¹' rationalCorridor) =
        Q ((fun ω q => X (rationalUnitTime q) ω - X 0 ω) ⁻¹'
          rationalCorridor) := by
    apply measure_congr
    filter_upwards [hstart] with ω hω
    have hfun : (fun q => X (rationalUnitTime q) ω) =
        fun q => X (rationalUnitTime q) ω - X 0 ω := by
      funext q
      simp [hω]
    change ((fun q => X (rationalUnitTime q) ω) ∈ rationalCorridor) =
      ((fun q => X (rationalUnitTime q) ω - X 0 ω) ∈ rationalCorridor)
    rw [hfun]
  have hprocess := measure_fullSegmentCorridorReturnEvent_eq_rational
    Q X 0 1 lower upper coreLower coreUpper hX.ae_cadlag
  calc
    P (Skorokhod.rangeInOpenIntervalEndsIn lower upper coreLower coreUpper) =
        P (pathCoordinates ⁻¹' rationalCorridor) := hpathMeasure
    _ = Q ((fun ω q => X (rationalUnitTime q) ω) ⁻¹' rationalCorridor) := by
      simpa [pathCoordinates, rationalCorridor] using hcoord
    _ = Q ((fun ω q => X (rationalUnitTime q) ω - X 0 ω) ⁻¹'
        rationalCorridor) := hcoordinateEq
    _ = Q (fullSegmentCorridorReturnEvent X 0 1 lower upper coreLower coreUpper) := by
      simpa only [rationalCorridor, zero_add, one_mul] using hprocess

/-- Transfer a common positive lower bound on finitely many strict-stable
endpoint windows to the corresponding open endpoint events under a càdlàg
stable path law. The stable-process estimate is applied to smaller `Ioc`
windows; their strict containment in the requested `Ioo` windows makes the
Portmanteau input genuinely open. -/
theorem IsStableClockProcessLaw.exists_finite_openEndpointCorridor_lowerBound
    {α : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (innerLower innerUpper outerLower outerUpper : ι → ℝ)
    (hstableLower : ∀ i, -1 ≤ (1 + 1 / 16 : ℝ) * innerLower i)
    (hinner : ∀ i, innerLower i < innerUpper i)
    (hstableUpper : ∀ i, (1 + 1 / 16 : ℝ) * innerUpper i ≤ 1)
    (houterLower : ∀ i, outerLower i < innerLower i)
    (houterUpper : ∀ i, innerUpper i < outerUpper i) :
    ∃ β : ℝ, ∃ q : ℝ≥0∞, 0 < β ∧ β < 1 / 2 ∧ 0 < q ∧
      ∀ i, q ≤ P (Skorokhod.rangeInOpenIntervalEndsIn (-β) β
        (β * outerLower i) (β * outerUpper i)) := by
  obtain ⟨β, q, hβ, hβsmall, hq, hqle⟩ :=
    hX.exists_finite_endpointCorridorIoc_lowerBound hcdf
      innerLower innerUpper hstableLower hinner hstableUpper
  refine ⟨β, q, hβ, hβsmall, hq, ?_⟩
  intro i
  have hwindow :
      Set.Ioc (β * innerLower i) (β * innerUpper i) ⊆
        Set.Ioo (β * outerLower i) (β * outerUpper i) := by
    intro x hx
    simp only [Set.mem_Ioc, Set.mem_Ioo] at hx ⊢
    exact ⟨by nlinarith [hβ, houterLower i],
      by nlinarith [hβ, houterUpper i]⟩
  have hsubset :
      fullSegmentCorridorIocReturnEvent X 0 1 (-β) β
          (β * innerLower i) (β * innerUpper i) ⊆
        fullSegmentCorridorReturnEvent X 0 1 (-β) β
          (β * outerLower i) (β * outerUpper i) := by
    change segmentCorridorEndpointEvent X 0 1 (-β) β
        (Set.Ioc (β * innerLower i) (β * innerUpper i)) ⊆
      segmentCorridorEndpointEvent X 0 1 (-β) β
        (Set.Ioo (β * outerLower i) (β * outerUpper i))
    exact segmentCorridorEndpointEvent_mono X 0 1 le_rfl le_rfl hwindow
  have hprocess :
      q ≤ Q (fullSegmentCorridorReturnEvent X 0 1 (-β) β
        (β * outerLower i) (β * outerUpper i)) :=
    (hqle i).trans (measure_mono hsubset)
  rw [← hP.measure_corridorReturnEvent_eq hX (-β) β
    (β * outerLower i) (β * outerUpper i)] at hprocess
  exact hprocess

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
