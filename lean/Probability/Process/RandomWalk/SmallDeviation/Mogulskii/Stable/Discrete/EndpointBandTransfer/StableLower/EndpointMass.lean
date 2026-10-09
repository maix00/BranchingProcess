/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLimit.Block
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.EndpointBandTransfer.StableRate
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Rate
import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Transfer

/-!
# Stable lower bounds for shifted endpoint-return blocks

This combines the stable escape rate, the variable-block path limit, and
open-set Portmanteau for an arbitrary shifted interval. It supplies the
finite endpoint-band probabilities needed by the discrete return kernel.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- A stable escape rate gives an eventual sharp exponential lower mass for a
fixed open endpoint window strictly inside a corridor containing the origin.
The endpoint location changes the positive prefactor, while the exponent
depends only on the corridor's half-width. -/
theorem eventually_scaledStableEndpointCorridorProbability_ge_exp
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {α C : ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {lower upper endpointLower endpointUpper delta : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper)
    (hendLower : lower < endpointLower)
    (hendOrder : endpointLower < endpointUpper)
    (hendUpper : endpointUpper < upper) (hdelta : 0 < delta) :
    ∀ᶠ amplitude : ℝ in atTop,
      ENNReal.ofReal (Real.exp
        ((C / (((upper - lower) / 2) ^ α) - delta) * amplitude ^ α)) <
        P.map (Skorokhod.scalePath amplitude)
          (Skorokhod.rangeInOpenIntervalEndsIn
            lower upper endpointLower endpointUpper) := by
  let radius : ℝ := (upper - lower) / 2
  let centerRatio : ℝ := (upper + lower) / (upper - lower)
  let c : ℝ := endpointLower / radius - centerRatio
  let b : ℝ := endpointUpper / radius - centerRatio
  have hwidth : 0 < upper - lower := sub_pos.mpr (lt_trans hlower hupper)
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hlowerRatio : lower / radius = centerRatio - 1 := by
    dsimp [radius, centerRatio]
    field_simp [ne_of_gt hwidth]
    ring
  have hupperRatio : upper / radius = centerRatio + 1 := by
    dsimp [radius, centerRatio]
    field_simp [ne_of_gt hwidth]
    ring
  have hd : -1 < centerRatio ∧ centerRatio < 1 := by
    constructor
    · have hpos : 0 < upper / radius := div_pos hupper hradius
      rw [hupperRatio] at hpos
      linarith
    · have hneg : lower / radius < 0 := div_neg_of_neg_of_pos hlower hradius
      rw [hlowerRatio] at hneg
      linarith
  have hc : -1 < c := by
    dsimp [c]
    have hdiv := div_lt_div_of_pos_right hendLower hradius
    rw [hlowerRatio] at hdiv
    linarith
  have hb : b < 1 := by
    dsimp [b]
    have hdiv := div_lt_div_of_pos_right hendUpper hradius
    rw [hupperRatio] at hdiv
    linarith
  have hcb : c < b := by
    dsimp [c, b]
    have hdiv := div_lt_div_of_pos_right hendOrder hradius
    linarith
  have hscaled := eventually_scaledStableShiftedEndpointCorridorProbability_ge_exp
    hEscape hX hcdf hradius hdelta hd hc hcb hb
  have hendpointLower : radius * (centerRatio + c) = endpointLower := by
    dsimp [c]
    field_simp [hradius.ne']
    ring
  have hendpointUpper : radius * (centerRatio + b) = endpointUpper := by
    dsimp [b]
    field_simp [hradius.ne']
    ring
  have hleft : radius * (centerRatio - 1) = lower := by
    rw [← hlowerRatio]
    field_simp [hradius.ne']
  have hright : radius * (centerRatio + 1) = upper := by
    rw [← hupperRatio]
    field_simp [hradius.ne']
  have hparams :
      Skorokhod.rangeInOpenIntervalEndsIn
          (radius * (centerRatio - 1)) (radius * (centerRatio + 1))
          (radius * (centerRatio + c)) (radius * (centerRatio + b)) =
        Skorokhod.rangeInOpenIntervalEndsIn lower upper
          endpointLower endpointUpper := by
    rw [hleft, hright, hendpointLower, hendpointUpper]
  filter_upwards [hscaled] with amplitude hmass
  rw [← hparams]
  simpa [radius] using hmass

/-- A finite family of open endpoint windows inside one fixed corridor has a
common eventual stable escape lower bound. The finite intersection is what
allows all entrance and exit bands to use one spatial amplitude. -/
theorem eventually_scaledStableEndpointWindowFamilyProbability_ge_exp
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {α C : ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (endpointLower endpointUpper : ι → ℝ)
    {lower upper delta : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper)
    (hwindows : ∀ i ∈ indices,
      lower < endpointLower i ∧ endpointLower i < endpointUpper i ∧
        endpointUpper i < upper)
    (hdelta : 0 < delta) :
    ∀ᶠ amplitude : ℝ in atTop,
      ∀ i ∈ indices,
        ENNReal.ofReal (Real.exp
          ((C / (((upper - lower) / 2) ^ α) - delta) * amplitude ^ α)) <
          P.map (Skorokhod.scalePath amplitude)
            (Skorokhod.rangeInOpenIntervalEndsIn
              lower upper (endpointLower i) (endpointUpper i)) := by
  apply indices.eventually_all.2
  intro i hi
  exact eventually_scaledStableEndpointCorridorProbability_ge_exp
    hEscape hX hcdf hlower hupper (hwindows i hi).1 (hwindows i hi).2.1
    (hwindows i hi).2.2 hdelta

/-- A stable escape rate gives the sharp exponential lower mass for any one
fixed open endpoint window strictly inside a corridor containing the origin.
This supplies the finite-cost entrance and exit blocks in the partition
lower bound. -/
theorem exists_stableEndpointCorridorMassLowerBound_of_escapeRate
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {α C : ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {lower upper endpointLower endpointUpper delta : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper)
    (hendLower : lower < endpointLower)
    (hendOrder : endpointLower < endpointUpper)
    (hendUpper : endpointUpper < upper) (hdelta : 0 < delta) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      ENNReal.ofReal (Real.exp
        ((C / (((upper - lower) / 2) ^ α) - delta) * amplitude ^ α)) <
        P.map (Skorokhod.scalePath amplitude)
          (Skorokhod.rangeInOpenIntervalEndsIn
            lower upper endpointLower endpointUpper) := by
  let radius : ℝ := (upper - lower) / 2
  let centerRatio : ℝ := (upper + lower) / (upper - lower)
  let c : ℝ := endpointLower / radius - centerRatio
  let b : ℝ := endpointUpper / radius - centerRatio
  have hwidth : 0 < upper - lower := sub_pos.mpr (lt_trans hlower hupper)
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hlowerRatio : lower / radius = centerRatio - 1 := by
    dsimp [radius, centerRatio]
    field_simp [ne_of_gt hwidth]
    ring
  have hupperRatio : upper / radius = centerRatio + 1 := by
    dsimp [radius, centerRatio]
    field_simp [ne_of_gt hwidth]
    ring
  have hd : -1 < centerRatio ∧ centerRatio < 1 := by
    constructor
    · have hpos : 0 < upper / radius := div_pos hupper hradius
      rw [hupperRatio] at hpos
      linarith
    · have hneg : lower / radius < 0 := div_neg_of_neg_of_pos hlower hradius
      rw [hlowerRatio] at hneg
      linarith
  have hendpointLower : radius * (centerRatio + c) = endpointLower := by
    dsimp [c]
    field_simp [hradius.ne']
    ring
  have hendpointUpper : radius * (centerRatio + b) = endpointUpper := by
    dsimp [b]
    field_simp [hradius.ne']
    ring
  have hc : -1 < c := by
    dsimp [c]
    have hdiv := div_lt_div_of_pos_right hendLower hradius
    rw [hlowerRatio] at hdiv
    linarith
  have hb : b < 1 := by
    dsimp [b]
    have hdiv := div_lt_div_of_pos_right hendUpper hradius
    rw [hupperRatio] at hdiv
    linarith
  have hcb : c < b := by
    dsimp [c, b]
    have hdiv := div_lt_div_of_pos_right hendOrder hradius
    linarith
  have hscaled := eventually_scaledStableShiftedEndpointCorridorProbability_ge_exp
    hEscape hX hcdf hradius (by linarith : 0 < delta / 2) hd hc hcb hb
  obtain ⟨amplitude₀, hmass₀⟩ := Filter.eventually_atTop.1
    (hscaled.and (eventually_gt_atTop (0 : ℝ)))
  let amplitude : ℝ := max amplitude₀ 1
  have hamplitude : 0 < amplitude := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hmass := (hmass₀ amplitude (le_max_left _ _)).1
  have hrate : C / radius ^ α < 0 :=
    div_neg_of_neg_of_pos hEscape.negative (Real.rpow_pos_of_pos hradius α)
  have hlowExponent : (C / radius ^ α - delta) * amplitude ^ α <
      (C / radius ^ α - delta / 2) * amplitude ^ α := by
    have hpower : 0 < amplitude ^ α := Real.rpow_pos_of_pos hamplitude α
    nlinarith
  have hlowENN : ENNReal.ofReal
      (Real.exp ((C / radius ^ α - delta) * amplitude ^ α)) <
      ENNReal.ofReal
        (Real.exp ((C / radius ^ α - delta / 2) * amplitude ^ α)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).2
    exact Real.exp_lt_exp.mpr hlowExponent
  have hleft : radius * (centerRatio - 1) = lower := by
    rw [← hlowerRatio]
    field_simp [hradius.ne']
  have hright : radius * (centerRatio + 1) = upper := by
    rw [← hupperRatio]
    field_simp [hradius.ne']
  have hparams :
      Skorokhod.rangeInOpenIntervalEndsIn
          (radius * (centerRatio - 1)) (radius * (centerRatio + 1))
          (radius * (centerRatio + c)) (radius * (centerRatio + b)) =
        Skorokhod.rangeInOpenIntervalEndsIn lower upper
          endpointLower endpointUpper := by
    rw [hleft, hright, hendpointLower, hendpointUpper]
  refine ⟨amplitude, hamplitude, ?_⟩
  rw [← hparams]
  exact hlowENN.trans hmass

/-- A stable escape rate supplies one common exponential lower mass for the
finite family of open endpoint bands. The amplitude is chosen after the
stable-process estimate and before any discrete block length is selected, so
the same mass can be transferred to several asymptotically equivalent block
sequences. -/
theorem exists_stableEndpointBandReturnMassLowerBound_of_escapeRate
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {α C : ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {lower upper epsilon delta : ℝ}
    (hlower : lower + 4 * epsilon < 0)
    (hupper : 0 < upper - 4 * epsilon)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta)
    (hbands : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lower + 4 * epsilon < (((i : ℝ) - 1) * epsilon) ∧
        ((i : ℝ) + 1) * epsilon < upper - 4 * epsilon) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
        ENNReal.ofReal (Real.exp
          ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
            amplitude ^ α)) <
          P.map (Skorokhod.scalePath amplitude)
            (Skorokhod.rangeInOpenIntervalEndsIn
              (lower + 4 * epsilon) (upper - 4 * epsilon)
              (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon)) := by
  let corridorLower : ℝ := lower + 4 * epsilon
  let corridorUpper : ℝ := upper - 4 * epsilon
  let radius : ℝ := (corridorUpper - corridorLower) / 2
  have hradiusEq : radius = (upper - lower - 8 * epsilon) / 2 := by
    dsimp [radius, corridorLower, corridorUpper]
    ring
  have hradius : 0 < radius := by
    dsimp [radius, corridorLower, corridorUpper]
    linarith [hlower, hupper]
  have hlower' : corridorLower < 0 := by
    simpa [corridorLower] using hlower
  have hupper' : 0 < corridorUpper := by
    simpa [corridorUpper] using hupper
  have hscaledMass := eventually_scaledStableIntervalEndpointBandsProbability_ge_exp
    (lower := corridorLower) (upper := corridorUpper) (epsilon := epsilon)
    (delta := delta / 2) hEscape hX hcdf hlower' hupper' hepsilon
    (by positivity) (by
      intro i hi
      simpa [corridorLower, corridorUpper] using hbands i hi)
  obtain ⟨amplitude₀, hmass₀⟩ := Filter.eventually_atTop.1
    (hscaledMass.and (eventually_gt_atTop (0 : ℝ)))
  let amplitude : ℝ := max amplitude₀ 1
  have hamplitude : 0 < amplitude := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hstableMass := (hmass₀ amplitude (le_max_left _ _)).1
  have hrate : C / radius ^ α < 0 :=
    div_neg_of_neg_of_pos hEscape.negative (Real.rpow_pos_of_pos hradius α)
  have hlowExponent : (C / radius ^ α - delta) * amplitude ^ α <
      (C / radius ^ α - delta / 2) * amplitude ^ α := by
    have hpower : 0 < amplitude ^ α := Real.rpow_pos_of_pos hamplitude α
    nlinarith
  have hlowENN : ENNReal.ofReal
      (Real.exp ((C / radius ^ α - delta) * amplitude ^ α)) <
      ENNReal.ofReal
        (Real.exp ((C / radius ^ α - delta / 2) * amplitude ^ α)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).2
    exact Real.exp_lt_exp.mpr hlowExponent
  refine ⟨amplitude, hamplitude, ?_⟩
  intro i hi
  have hstableMassI := hstableMass i hi
  have hstableMassI' : ENNReal.ofReal
      (Real.exp ((C / radius ^ α - delta / 2) * amplitude ^ α)) <
      P.map (Skorokhod.scalePath amplitude)
        (Skorokhod.rangeInOpenIntervalEndsIn corridorLower corridorUpper
          (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon)) := by
    simpa [corridorLower, corridorUpper, radius] using hstableMassI
  have hrateEq : radius = (upper - lower - 8 * epsilon) / 2 := hradiusEq
  rw [← hrateEq]
  simpa [corridorLower, corridorUpper] using hlowENN.trans hstableMassI'

/-- Choose one amplitude that works both for all seven repeated-return bands
and for a finite family of arbitrary entrance/exit windows. This is the
common stable-process input needed before assigning discrete block lengths. -/
theorem exists_commonStableEndpointBandAndBridgeMassLowerBound_of_escapeRate
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {α C : ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {lower upper epsilon delta : ℝ}
    (hlower : lower + 4 * epsilon < 0)
    (hupper : 0 < upper - 4 * epsilon)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta)
    (hbands : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lower + 4 * epsilon < (((i : ℝ) - 1) * epsilon) ∧
        ((i : ℝ) + 1) * epsilon < upper - 4 * epsilon)
    {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (endpointLower endpointUpper : ι → ℝ)
    (hwindows : ∀ i ∈ indices,
      lower + 4 * epsilon < endpointLower i ∧
        endpointLower i < endpointUpper i ∧
        endpointUpper i < upper - 4 * epsilon) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      (∀ i ∈ Finset.Icc (-3 : ℤ) 3,
        ENNReal.ofReal (Real.exp
          ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
            amplitude ^ α)) <
          P.map (Skorokhod.scalePath amplitude)
            (Skorokhod.rangeInOpenIntervalEndsIn
              (lower + 4 * epsilon) (upper - 4 * epsilon)
              (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon))) ∧
      (∀ i ∈ indices,
        ENNReal.ofReal (Real.exp
          ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
            amplitude ^ α)) <
          P.map (Skorokhod.scalePath amplitude)
            (Skorokhod.rangeInOpenIntervalEndsIn
              (lower + 4 * epsilon) (upper - 4 * epsilon)
              (endpointLower i) (endpointUpper i))) := by
  let corridorLower : ℝ := lower + 4 * epsilon
  let corridorUpper : ℝ := upper - 4 * epsilon
  let radius : ℝ := (corridorUpper - corridorLower) / 2
  have hradiusEq : radius = (upper - lower - 8 * epsilon) / 2 := by
    dsimp [radius, corridorLower, corridorUpper]
    ring
  have hradius : 0 < radius := by
    dsimp [radius, corridorLower, corridorUpper]
    linarith [hlower, hupper]
  have hleft : corridorLower < 0 := by simpa [corridorLower] using hlower
  have hright : 0 < corridorUpper := by simpa [corridorUpper] using hupper
  have hbandEventually := eventually_scaledStableIntervalEndpointBandsProbability_ge_exp
    (lower := corridorLower) (upper := corridorUpper) (epsilon := epsilon)
    (delta := delta / 2) hEscape hX hcdf hleft hright hepsilon
    (by positivity) (by
      intro i hi
      simpa [corridorLower, corridorUpper] using hbands i hi)
  have hbridgeEventually :=
    eventually_scaledStableEndpointWindowFamilyProbability_ge_exp
      hEscape hX hcdf indices endpointLower endpointUpper
      (lower := corridorLower) (upper := corridorUpper) (delta := delta / 2)
      hleft hright (by
        intro i hi
        simpa [corridorLower, corridorUpper] using hwindows i hi)
      (by positivity)
  obtain ⟨amplitude₀, hmass₀⟩ := Filter.eventually_atTop.1
    ((hbandEventually.and hbridgeEventually).and
      (eventually_gt_atTop (0 : ℝ)))
  let amplitude : ℝ := max amplitude₀ 1
  have hamplitude : 0 < amplitude := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hmass := hmass₀ amplitude (le_max_left _ _)
  have hbandMass := hmass.1.1
  have hbridgeMass := hmass.1.2
  have hpower : 0 < amplitude ^ α := Real.rpow_pos_of_pos hamplitude α
  have hlowExponent : (C / radius ^ α - delta) * amplitude ^ α <
      (C / radius ^ α - delta / 2) * amplitude ^ α := by nlinarith
  have hlowENN : ENNReal.ofReal
      (Real.exp ((C / radius ^ α - delta) * amplitude ^ α)) <
      ENNReal.ofReal
        (Real.exp ((C / radius ^ α - delta / 2) * amplitude ^ α)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).2
    exact Real.exp_lt_exp.mpr hlowExponent
  have hlowENN' : ENNReal.ofReal
      (Real.exp
        ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
          amplitude ^ α)) <
      ENNReal.ofReal
        (Real.exp ((C / radius ^ α - delta / 2) * amplitude ^ α)) := by
    rw [← hradiusEq]
    exact hlowENN
  refine ⟨amplitude, hamplitude, ?_, ?_⟩
  · intro i hi
    exact hlowENN'.trans (by simpa [corridorLower, corridorUpper, radius] using hbandMass i hi)
  · intro i hi
    exact hlowENN'.trans (by simpa [corridorLower, corridorUpper, radius] using hbridgeMass i hi)

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
