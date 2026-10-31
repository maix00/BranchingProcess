/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalCoordinate.UnitInterval
public import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Basic
public import Probability.Process.Stable.Levy
public import Probability.Process.Corridor.Range
public import Probability.Process.Path.Skorokhod.Corridor.Segment
public import Topology.Cadlag.Skorokhod.Corridor.Endpoint
public import Mathlib.Probability.CDF

import Probability.Process.Stable.FiniteDimensional
public import Probability.Process.Stable.SmallDeviation.EscapeRate.Basic
public import Probability.Process.Stable.SmallDeviation.EscapeRate.Corridor
import Probability.Process.Levy.PathLaw.Corridor
import Probability.Process.Stable.PathLaw.SelfSimilarity
import Probability.Process.Path.Skorokhod.RationalTime
import Topology.Order.UnitInterval.Rational

/-!
# Stable escape rates on càdlàg path laws

## Public declarations

- `ProbabilityTheory.IsStableClockProcessLaw.measure_stableProcessTube_eq_rationalRangeProbability`:
  \(P(\operatorname{stableProcessTube}(a))=
  \operatorname{rationalRangeProbability}(Q,X,a)\), for path and process
  laws with the same stable increment specification.
- `ProbabilityTheory.HasStableProcessEscapeRate.tendsto_stableRangeLogRate_of_isStableLevyProcess`:
  the path-law rate transfers to the process range rate,
  \[
    a^\alpha\log((\operatorname{rationalRangeProbability}(Q,X,a)).toReal)
      \longrightarrow C\qquad(a\downarrow0).
  \]
- `ProbabilityTheory.HasStableProcessEscapeRate.tendsto_invRpow_mul_sum_log_stableProcessTube`:
  for a finite set \(F\) and positive radii \(r_i\),
  \[
    c^{-\alpha}\sum_{i\in F}\log\!\left(
      (P(\operatorname{stableProcessTube}(r_i/c))).toReal\right)
    \longrightarrow \sum_{i\in F}\frac{C}{r_i^\alpha}
    \qquad(c\to\infty).
  \]
- `ProbabilityTheory.IsStableClockProcessLaw.measure_corridorReturnEvent_eq`:
  stable path-law uniqueness and the Lévy path-law corridor bridge give
  \[
    P(\operatorname{rangeInOpenIntervalEndsIn}(l,u,c,d))
      =Q(\operatorname{fullSegmentCorridorReturnEvent}(X,0,1,l,u,c,d)).
  \]
- `ProbabilityTheory.IsStableClockProcessLaw.measure_stableProcessCenteredCorridor_eq`:
  the zero-start centered path corridor has the same probability as the
  centered process corridor,
  \(P(I^a_{-a})=\mathbb P_Q\{\exists\eta>0,\forall t\in[0,1],
  -a+\eta\le X_t-X_0\le a-\eta\}\), with rate parameter
  \(a\downarrow0\).
- `ProbabilityTheory.IsStableClockProcessLaw.exists_centeredCorridorEscapeRate_of_isStableLevyProcess`:
  when \(0<F_\alpha(0)<1\), the centered rate transfers with a negative
  constant, \(C<0\) and
  \(a^\alpha\log((P(I^a_{-a})).toReal)\to C\).
- `ProbabilityTheory.IsStableClockProcessLaw.exists_finite_openEndpointCorridor_lowerBound`:
  for the finite family of strictly nested endpoint intervals in its
  hypotheses, there are \(0<\beta<1/2\) and \(q>0\) such that
  \[
    q\le P(\operatorname{rangeInOpenIntervalEndsIn}
      (-\beta,\beta,\beta l_i,\beta u_i))\quad(i:\iota).
  \]
- `ProbabilityTheory.IsStableClockProcessLaw.hasStableProcessEscapeRate_of_isStableLevyProcess`:
  when \(0<F_\alpha(0)<1\), the process escape-rate theorem supplies
  \(C\in\mathbb R\) with
  \(\operatorname{HasStableProcessEscapeRate}(\alpha,\mu,P,C)\).

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
    (hP : IsStableClockProcessLaw α μ unitInterval.clock P)
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
  have hPbase : HasStableClockIncrements α μ unitInterval.clock
      cadlagPathProcess P := hP
  have hPgrid0 := hPbase.comp_time RationalCoordinate.toUnitInterval
    htoUnitIntervalMonotone htoUnitIntervalBot
  change HasStableClockIncrements α μ
    (fun q => unitInterval.clock (RationalCoordinate.toUnitInterval q))
    (fun q f => f (RationalCoordinate.toUnitInterval q)) P at hPgrid0
  have hPgrid : HasStableClockIncrements α μ
      (fun q => (RationalCoordinate.toNNReal q : ℝ))
      (fun q f => pathCoordinates f q) P := by
    convert hPgrid0 using 1
    · funext q
      exact (RationalCoordinate.toNNReal_coe q).symm
  have hXgrid0 := hX.increments.comp_time RationalCoordinate.toNNReal
    RationalCoordinate.monotone_toNNReal RationalCoordinate.toNNReal_bot
  have hXgrid : HasStableClockIncrements α μ
      (fun q => (RationalCoordinate.toNNReal q : ℝ))
      (fun q ω => X (RationalCoordinate.toNNReal q) ω) Q := by
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
        Q ((fun ω q => X (RationalCoordinate.toNNReal q) ω) ⁻¹'
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
      Q ((fun ω q => X (1 * RationalCoordinate.toNNReal q) ω) ⁻¹'
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
corridor with an open terminal window. Stable path-law uniqueness identifies
the path measure with the process's canonical unit-interval path law; the
generic Lévy corridor bridge then transfers the event probability. -/
theorem IsStableClockProcessLaw.measure_corridorReturnEvent_eq
    {α : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ unitInterval.clock P)
    (hX : IsStableLevyProcess α μ X Q)
    (lower upper coreLower coreUpper : ℝ) :
    P (Skorokhod.rangeInOpenIntervalEndsIn lower upper coreLower coreUpper) =
      Q (fullSegmentCorridorReturnEvent X 0 1 lower upper coreLower coreUpper) := by
  let pathEvent : Set (CadlagPath unitInterval ℝ) :=
    Skorokhod.corridorStartingAtZero lower upper ∩
      {f : CadlagPath unitInterval ℝ | f ⊤ ∈ Set.Ioo coreLower coreUpper}
  have hpathEvent :
      Skorokhod.rangeInOpenIntervalEndsIn lower upper coreLower coreUpper =ᵐ[P]
        pathEvent := by
    filter_upwards [hP.ae_start_eq_zero] with f hf
    simp [pathEvent, Skorokhod.rangeInOpenIntervalEndsIn,
      Skorokhod.corridorStartingAtZero, hf]
  have hP_eq : P =
      (hX.toIsLevyProcess.unitIntervalPathLaw 1 :
        Measure (CadlagPath unitInterval ℝ)) :=
    hP.unitInterval_measure_eq
      hX.isStableClockProcessLaw_unitIntervalPathLaw
  calc
    P (Skorokhod.rangeInOpenIntervalEndsIn lower upper coreLower coreUpper) =
        P pathEvent := measure_congr hpathEvent
    _ = (hX.toIsLevyProcess.unitIntervalPathLaw 1 :
        Measure (CadlagPath unitInterval ℝ)) pathEvent := by rw [hP_eq]
    _ = Q (fullSegmentCorridorReturnEvent X 0 1 lower upper coreLower coreUpper) :=
      hX.toIsLevyProcess.unitIntervalPathLaw_measure_corridorReturnEvent
        1 lower upper coreLower coreUpper

/-- The centered path-space corridor has the same probability as the
corresponding complete-segment corridor of a stable Lévy process with the
same increment law. The path law starts at zero almost surely, and the
terminal condition in the transfer theorem follows from the uniform corridor
margin. -/
theorem IsStableClockProcessLaw.measure_stableProcessCenteredCorridor_eq
    {α : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ unitInterval.clock P)
    (hX : IsStableLevyProcess α μ X Q) (a : ℝ) :
    P (stableProcessCenteredCorridor a) =
      centeredCorridorProbability Q X a := by
  have hstart := hP.ae_start_eq_zero
  have hpathSet :
      stableProcessCenteredCorridor a =ᵐ[P]
        Skorokhod.rangeInOpenInterval (-a) a := by
    filter_upwards [hstart] with f hf
    simp [stableProcessCenteredCorridor, Skorokhod.corridorStartingAtZero, hf]
  have hpathMeasure :
      P (stableProcessCenteredCorridor a) =
        P (Skorokhod.rangeInOpenInterval (-a) a) :=
    measure_congr hpathSet
  have hterminal :
      Skorokhod.rangeInOpenInterval (-a) a =
        Skorokhod.rangeInOpenIntervalEndsIn (-a) a (-a) a := by
    ext f
    rw [Skorokhod.mem_rangeInOpenIntervalEndsIn_iff]
    constructor
    · intro hf
      refine ⟨hf, ?_⟩
      obtain ⟨margin, hmargin, hpath⟩ := hf
      have htop := hpath ⊤
      constructor <;> linarith
    · exact fun hf => hf.1
  have hprocessEvent :
      fullSegmentCorridorReturnEvent X 0 1 (-a) a (-a) a =
        fullSegmentCorridorEvent X 0 1 (-a) a := by
    ext ω
    simp only [fullSegmentCorridorReturnEvent, segmentCorridorEndpointEvent,
      Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo]
    constructor
    · exact fun h => h.1
    · intro h
      rcases h with ⟨margin, hmargin, hpath⟩
      refine ⟨⟨margin, hmargin, hpath⟩, ?_⟩
      have htop := hpath ⊤
      constructor <;> linarith
  calc
    P (stableProcessCenteredCorridor a) =
        P (Skorokhod.rangeInOpenInterval (-a) a) := hpathMeasure
    _ = P (Skorokhod.rangeInOpenIntervalEndsIn (-a) a (-a) a) := by
      rw [hterminal]
    _ = Q (fullSegmentCorridorReturnEvent X 0 1 (-a) a (-a) a) :=
      hP.measure_corridorReturnEvent_eq hX (-a) a (-a) a
    _ = Q (fullSegmentCorridorEvent X 0 1 (-a) a) := by
      rw [hprocessEvent]

/-- Lemma 1(II) of A. A. Mogul'skii, “Small Deviations in a Space of
Trajectories,” as a path-law consequence of the centered and range-tube
comparison. A stable-clock path law and a stable Lévy-process realization
with the same increment law have the same centered-corridor escape constant. -/
theorem IsStableClockProcessLaw.exists_centeredCorridorEscapeRate_of_isStableLevyProcess
    {α : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ unitInterval.clock P)
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    ∃ C : ℝ, C < 0 ∧ HasStableCenteredCorridorEscapeRate α μ P C := by
  obtain ⟨C, hC, _, hcenter⟩ := hX.exists_centeredCorridor_escape_rate hcdf
  have hpositive : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ),
      0 < (P (stableProcessCenteredCorridor a)).toReal := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    rw [hP.measure_stableProcessCenteredCorridor_eq hX a]
    have ⟨hnegative, hpositive⟩ :=
      hX.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
    have hcorridor : 0 < centeredCorridorProbability Q X a := by
      dsimp [centeredCorridorProbability]
      have ha' : 0 < a := by simpa using ha
      exact hX.measure_fullSegmentCorridor_pos (-a) a (neg_neg_of_pos ha') ha'
        hpositive hnegative
    exact ENNReal.toReal_pos_iff.mpr
      ⟨hcorridor, measure_lt_top Q _⟩
  have hrate : Tendsto
      (fun a : ℝ => a ^ α *
        Real.log ((P (stableProcessCenteredCorridor a)).toReal))
      (𝓝[>] (0 : ℝ)) (𝓝 C) := by
    have heq : (fun a : ℝ => a ^ α *
        Real.log ((P (stableProcessCenteredCorridor a)).toReal)) =
        fun a => stableCenteredLogRate Q X α a := by
      funext a
      simp [stableCenteredLogRate,
        hP.measure_stableProcessCenteredCorridor_eq hX a]
    rw [heq]
    exact hcenter
  refine ⟨C, hC, hP, ?_⟩
  exact ⟨hP.strictlyStable.1, hC, hpositive, hrate⟩

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
    (hP : IsStableClockProcessLaw α μ unitInterval.clock P)
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
    (hP : IsStableClockProcessLaw α μ unitInterval.clock P)
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    ∃ C, HasStableProcessEscapeRate α μ P C := by
  have hprob (a : ℝ) :=
    hP.measure_stableProcessTube_eq_rationalRangeProbability hX a
  obtain ⟨C, hC, hlim⟩ := hX.exists_rationalRange_escape_rate hcdf
  have hα : 0 < α := hP.strictlyStable.1
  have hpos : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ),
      0 < (P (stableProcessTube a)).toReal := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have hRa : 0 < rationalRangeProbability Q X a :=
      hX.rationalRangeProbability_pos_of_cdf hcdf ha
    rw [hprob]
    exact ENNReal.toReal_pos_iff.mpr
      ⟨hRa, measure_lt_top Q (rationalHorizonTubeEvent X 1 (2 * a))⟩
  refine ⟨C, hP, hα, hC, hpos, ?_⟩
  have hrate :
      (fun a => a ^ α * Real.log ((P (stableProcessTube a)).toReal)) =
        stableRangeLogRate Q X α := by
    funext a
    simp [stableRangeLogRate, hprob]
  rw [hrate]
  exact hlim

end ProbabilityTheory

end
