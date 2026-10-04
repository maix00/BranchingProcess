/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.FiniteDimensional
public import Probability.Process.Path.Skorokhod.RationalTime
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Stable-process range tubes on rational times

The range tube of a càdlàg path is determined by its rational-time
coordinates; the pathwise identification is proved in
`Topology.Cadlag.Skorokhod.Oscillation.Dense`. This file uses the resulting
measurable coordinate tube together with the generic finite-dimensional-law
theorem to obtain the exact time-space scaling identity for stable-process
coordinate-tube probabilities.
-/

open Filter MeasureTheory
open scoped NNReal Topology

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The normalized logarithmic probability for a width-`2a` tube over unit
time. -/
noncomputable def stableRationalTubeSmallLogRate {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) (α a : ℝ) : ℝ :=
  a ^ α * Real.log ((P (rationalHorizonTubeEvent X 1 (2 * a))).toReal)

/-- The logarithmic probability per unit time for the width-two tube up to a
given horizon. -/
noncomputable def stableRationalTubeLongLogRate {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) (horizon : ℝ≥0) : ℝ :=
  Real.log ((P (rationalHorizonTubeEvent X horizon 2)).toReal) /
    (horizon : ℝ)

/-- The long horizon corresponding to a tube half-width under stable scaling.
Using `toNNReal` makes this a total function of the real parameter; on the
positive-width filter it agrees with the positive real power. -/
noncomputable def stableTubeHorizon (α a : ℝ) : ℝ≥0 :=
  Real.toNNReal (a ^ (-α))

/-- Stable scaling sends widths decreasing to zero to horizons tending to
infinity. -/
theorem tendsto_stableTubeHorizon_atTop {α : ℝ} (hα : 0 < α) :
    Tendsto (stableTubeHorizon α) (𝓝[>] (0 : ℝ)) atTop := by
  have hpow : Tendsto (fun a : ℝ => a ^ (-α)) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr hα)
  apply tendsto_atTop.2
  intro b
  have hpowb := (tendsto_atTop.1 hpow) (b : ℝ)
  filter_upwards [hpowb, self_mem_nhdsWithin] with a hab ha
  apply NNReal.coe_le_coe.mp
  unfold stableTubeHorizon
  rw [Real.coe_toNNReal _ (le_of_lt (Real.rpow_pos_of_pos ha _))]
  exact hab

/-- The law of a stable process on rational times is invariant under the
canonical stable time-space scaling. -/
theorem IsStableLevyProcess.rationalRestriction_identDistrib
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (horizon : ℝ≥0)
    (hhorizon : 0 < horizon) :
    IdentDistrib
      (rationalHorizonProcess X 1)
      (rationalHorizonProcess
        (fun t ω => (horizon : ℝ) ^ (-(1 / α)) * X (horizon * t) ω) 1)
      P P := by
  let clock : RationalGrid.RationalUnitInterval → ℝ :=
    fun q => (rationalUnitTime q : ℝ)
  have hbase : HasStableClockIncrements α μ clock
      (fun q ω => X (rationalUnitTime q) ω) P := by
    exact h.increments.comp_time rationalUnitTime monotone_rationalUnitTime
      rationalUnitTime_bot
  have hscaled := h.timeSpaceScale horizon hhorizon
  have hscaled' : HasStableClockIncrements α μ clock
      (fun q ω => (horizon : ℝ) ^ (-(1 / α)) *
        X (horizon * rationalUnitTime q) ω) P := by
    exact hscaled.increments.comp_time rationalUnitTime monotone_rationalUnitTime
      rationalUnitTime_bot
  have hprocess := hbase.process_identDistrib hscaled'
  convert hprocess using 1
  · funext ω q
    simp [rationalHorizonProcess]
  · funext ω q
    simp [rationalHorizonProcess]

/-- Stable-process coordinate-tube probabilities obey the exact time-space
scaling identity. The target tube is represented by rational coordinates and
finite-dimensional law uniqueness compares its probabilities. The separate
path-law bridge to `stableProcessRangeTube` remains an application-level step.
-/
theorem IsStableLevyProcess.rationalTube_timeSpaceScale
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (horizon : ℝ≥0)
    (hhorizon : 0 < horizon) (width : ℝ) :
    P (rationalHorizonTubeEvent X 1 width) =
      P (rationalHorizonTubeEvent X horizon
        (width / ((horizon : ℝ) ^ (-(1 / α))))) := by
  let scale : ℝ := (horizon : ℝ) ^ (-(1 / α))
  have hscale : 0 < scale := by
    dsimp [scale]
    exact Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hhorizon) _
  have hprocess := h.rationalRestriction_identDistrib horizon hhorizon
  have hprob := hprocess.measure_mem_eq
    (Skorokhod.measurableSet_rationalCoordinateOscillationTube width)
  have hevent :
      rationalHorizonTubeEvent
          (fun t ω => scale * X (horizon * t) ω) 1 width =
        rationalHorizonTubeEvent X horizon (width / scale) := by
    ext ω
    change rationalHorizonProcess
        (fun t ω => scale * X (horizon * t) ω) 1 ω ∈
          Skorokhod.rationalCoordinateOscillationTube width ↔
      rationalHorizonProcess X horizon ω ∈
        Skorokhod.rationalCoordinateOscillationTube (width / scale)
    rw [Skorokhod.rationalCoordinateOscillationTube_eq_real,
      Skorokhod.rationalCoordinateOscillationTube_eq_real]
    change (fun q => scale * X (horizon * (1 * rationalUnitTime q)) ω) ∈
        Skorokhod.rationalCoordinateOscillationTubeReal width ↔
      (fun q => X (horizon * rationalUnitTime q) ω) ∈
        Skorokhod.rationalCoordinateOscillationTubeReal (width / scale)
    simp only [one_mul]
    exact Skorokhod.mem_rationalCoordinateOscillationTubeReal_smul_iff
      hscale (fun q => X (horizon * rationalUnitTime q) ω)
  have hprob' :
      P (rationalHorizonTubeEvent X 1 width) =
        P (rationalHorizonTubeEvent
          (fun t ω => scale * X (horizon * t) ω) 1 width) := by
    exact hprob
  rw [hevent] at hprob'
  simpa [scale] using hprob'

/-- The inverse form of stable scaling evaluates a tube at a positive
horizon as a unit-time tube with the width multiplied by the stable spatial
scale. -/
theorem IsStableLevyProcess.rationalTube_timeSpaceScale_inv
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (horizon : ℝ≥0)
    (hhorizon : 0 < horizon) (width : ℝ) :
    P (rationalHorizonTubeEvent X horizon width) =
      P (rationalHorizonTubeEvent X 1
        (width * ((horizon : ℝ) ^ (-(1 / α))))) := by
  let scale : ℝ := (horizon : ℝ) ^ (-(1 / α))
  have hs : scale ≠ 0 := ne_of_gt
    (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hhorizon) _)
  have hscale := h.rationalTube_timeSpaceScale horizon hhorizon (width * scale)
  dsimp only [scale] at hscale hs
  simp only [mul_div_cancel_right₀ _ hs] at hscale
  exact hscale.symm

/-- The source's stable scaling identity, specialized to a small tube of
half-width `a`: its probability on unit time equals that of the unit tube on
the long horizon `a ^ (-α)`. This is the exact scaling step used before the
escape-rate limit in Mogul'skii's stable-process argument. -/
theorem IsStableLevyProcess.rationalTube_smallWidth_eq_longHorizon
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (hα : 0 < α)
    (a : ℝ) (ha : 0 < a) :
    P (rationalHorizonTubeEvent X 1 (2 * a)) =
      P (rationalHorizonTubeEvent X
        ⟨a ^ (-α), (Real.rpow_pos_of_pos ha _).le⟩ 2) := by
  let horizon : ℝ≥0 := ⟨a ^ (-α), (Real.rpow_pos_of_pos ha _).le⟩
  have hhorizon : 0 < horizon := by
    apply NNReal.coe_pos.mp
    dsimp [horizon]
    exact Real.rpow_pos_of_pos ha _
  have hscale : (horizon : ℝ) ^ (-(1 / α)) = a := by
    change (a ^ (-α)) ^ (-(1 / α)) = a
    rw [← Real.rpow_mul (le_of_lt ha)]
    have hexp : (-α) * (-(1 / α)) = 1 := by
      field_simp [ne_of_gt hα]
    rw [hexp, Real.rpow_one]
  have hprob := h.rationalTube_timeSpaceScale horizon hhorizon (2 * a)
  rw [hscale] at hprob
  have hwidth : 2 * a / a = 2 := by
    field_simp
  rw [hwidth] at hprob
  simpa [horizon] using hprob

/-- In the original stable-process argument, the small-width rate is exactly
the long-horizon rate after the substitution `T = a ^ (-α)`. This isolates
the remaining task in Lemma 1(I): prove existence and finiteness of the
long-time escape rate using the paper's finite-shift inequalities. -/
theorem IsStableLevyProcess.rationalTube_smallLogRate_eq_longLogRate
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (hα : 0 < α)
    (a : ℝ) (ha : 0 < a) :
    stableRationalTubeSmallLogRate X P α a =
      stableRationalTubeLongLogRate X P
        ⟨a ^ (-α), (Real.rpow_pos_of_pos ha _).le⟩ := by
  let horizon : ℝ≥0 := ⟨a ^ (-α), (Real.rpow_pos_of_pos ha _).le⟩
  have hprob := h.rationalTube_smallWidth_eq_longHorizon hα a ha
  have hcoeff : a ^ α = ((horizon : ℝ)⁻¹) := by
    change a ^ α = (a ^ (-α))⁻¹
    rw [Real.rpow_neg (le_of_lt ha) α]
    simp
  unfold stableRationalTubeSmallLogRate stableRationalTubeLongLogRate
  rw [show P (rationalHorizonTubeEvent X 1 (2 * a)) =
      P (rationalHorizonTubeEvent X horizon 2) by exact hprob]
  rw [hcoeff]
  simp only [div_eq_mul_inv]
  ring

/-- Once the long-time escape rate has been established, the source's stable
scaling change of variables transfers it to the small-width limit in Lemma
1(I). The hard estimate is existence of the long-time limit, proved from the
paper's finite-shift inequalities; this theorem only performs the exact
reparameterization. -/
theorem IsStableLevyProcess.tendsto_smallLogRate_of_tendsto_longLogRate
    {α C : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (hα : 0 < α)
    (hlong : Tendsto (stableRationalTubeLongLogRate X P) atTop (𝓝 C)) :
    Tendsto (stableRationalTubeSmallLogRate X P α)
      (𝓝[>] (0 : ℝ)) (𝓝 C) := by
  have hcomp := hlong.comp (tendsto_stableTubeHorizon_atTop hα)
  apply hcomp.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  have hpoint := h.rationalTube_smallLogRate_eq_longLogRate hα a ha
  have hhor : stableTubeHorizon α a =
      ⟨a ^ (-α), (Real.rpow_pos_of_pos ha _).le⟩ := by
    apply Subtype.ext
    change (Real.toNNReal (a ^ (-α)) : ℝ) = a ^ (-α)
    exact Real.coe_toNNReal _ (Real.rpow_nonneg (le_of_lt ha) _)
  rw [← hhor] at hpoint
  exact hpoint.symm

end ProbabilityTheory

end
