/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.DonskerEndpointWindows
public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Skorokhod

/-!
# Endpoint-window Donsker transfer along block lengths

This file handles a cofinal sequence of block horizons, rather than requiring
the block length to equal the sequence index. It is the interface used by the
fixed-diffusive-parameter argument, where the block horizon is chosen by
rounding a multiple of the squared spatial scale.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- Brownian Donsker convergence remains valid along any cofinal sequence of
block horizons. The path normalization is the square root of that horizon. -/
theorem tendstoInDistribution_normalizedStepCadlagPathIcc_brownian_along
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (length : ℕ → ℕ) (hlength : Tendsto length atTop atTop) :
    TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc
        (fun _ => Real.sqrt (length n)) (length n))
      atTop
      (Skorokhod.ofContinuousMap ∘ continuousunitIntervalPath B hcontinuous)
      (fun _ => iidSequenceLaw ν) P := by
  change (∫ x : ℝ, x ∂ν) = 0 ∧ (∫ x : ℝ, x ^ 2 ∂ν) = 1 at hν
  obtain ⟨hcentered, hsecondMoment⟩ := hν
  have hbase := RandomWalk.tendstoInDistribution_normalizedStepCadlagPath_brownian
    ν hcentered hsecondMoment hB hcontinuous hmeasurable
  have hsubsequence := hbase.comp_tendsto hlength
  convert hsubsequence using 1
  funext n increment
  ext t
  rw [normalizedStepCadlagPathIcc_apply, normalizedStepCadlagPathIcc_apply]
  simp [normalizedStepPath]

/-- Endpoint-window probability along a possibly reindexed sequence of block
lengths and path scales. -/
noncomputable def normalizedEndpointWindowProbabilityAlong
    (ν : Measure ℝ) (radius spacing windowRadius : ℕ → ℝ)
    (i : ℤ) (scale : ℕ → ℝ) (length : ℕ → ℕ) (n : ℕ) : ENNReal :=
  iidSequenceLaw ν (normalizedEndpointWindowEvent (radius n) (spacing n)
    (windowRadius n) i (scale n) (length n))

/-- In original coordinates, an endpoint-window probability along a block
sequence is the usual discrete block-event probability. -/
theorem normalizedEndpointWindowProbabilityAlong_eq_endpointWindowBlockEvent_of_scale
    (ν : Measure ℝ) (radius spacing windowRadius : ℝ) (i : ℤ)
    (scale : ℕ → ℝ) (length : ℕ → ℕ) (n : ℕ)
    (hscale : 0 < scale n) :
    normalizedEndpointWindowProbabilityAlong ν
        (fun _ => radius / scale n) (fun _ => spacing / scale n)
        (fun _ => windowRadius / scale n) i scale length n =
      iidSequenceLaw ν
        (endpointWindowBlockEvent radius spacing windowRadius i (length n)) := by
  have hevent := normalizedEndpointWindowEvent_eq_endpointWindowBlockEvent_scale
    (radius := radius / scale n) (spacing := spacing / scale n)
    (windowRadius := windowRadius / scale n) hscale i (length n)
  have hradius : radius / scale n * scale n = radius := div_mul_cancel₀ _ hscale.ne'
  have hspacing : spacing / scale n * scale n = spacing := div_mul_cancel₀ _ hscale.ne'
  have hwindow : windowRadius / scale n * scale n = windowRadius :=
    div_mul_cancel₀ _ hscale.ne'
  unfold normalizedEndpointWindowProbabilityAlong
  rw [hevent]
  simp [hradius, hspacing, hwindow]

/-- The normalized endpoint-window probability is the raw block event under
the correspondingly scaled increment law. -/
theorem iidSequenceLaw_map_div_endpointWindowBlockEvent_eq_normalizedAlong
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (radius spacing windowRadius : ℕ → ℝ) (i : ℤ)
    (scale : ℕ → ℝ) (length : ℕ → ℕ) (n : ℕ)
    (hscale : 0 < scale n) :
    iidSequenceLaw (ν.map fun x : ℝ => x / scale n)
        (endpointWindowBlockEvent (radius n) (spacing n) (windowRadius n) i
          (length n)) =
      normalizedEndpointWindowProbabilityAlong ν
        radius spacing windowRadius i scale length n := by
  rw [← iidSequenceLaw_map_coordinatewise ν
    (fun x : ℝ => x / scale n) (measurable_id.div_const (scale n))]
  rw [Measure.map_apply]
  · congr 1
    ext increment
    simp only [Set.mem_preimage]
    have hpath := inOpenHorizontalTube_div_iff
      (1 / 2) (2 * radius n * scale n) (length n) increment hscale
    have hwidth : (2 * radius n * scale n) / scale n = 2 * radius n := by
      field_simp [hscale.ne']
    have hsum :
        AdditivePath.displacement (length n)
            (fun k => increment k / scale n) =
          AdditivePath.displacement (length n) increment / scale n := by
      simp [AdditivePath.displacement, div_eq_mul_inv, Finset.sum_mul]
    change InOpenHorizontalTube (1 / 2) (2 * radius n) (length n)
        (fun k => increment k / scale n) ∧
      AdditivePath.displacement (length n)
          (fun k => increment k / scale n) ∈
        Set.Ioo ((i : ℝ) * spacing n - windowRadius n)
          ((i : ℝ) * spacing n + windowRadius n) ↔ _
    rw [hwidth] at hpath
    rw [hpath, hsum]
    rfl
  · exact Measurable.of_eval fun k =>
      (measurable_id.div_const (scale n)).comp
        (measurable_pi_apply k)
  · exact measurableSet_endpointWindowBlockEvent (radius n) (spacing n)
      (windowRadius n) i (length n)

/-- Open endpoint windows transfer from a functional limit along a sequence
of possibly varying block lengths. -/
theorem measure_centeredSkorokhodCorridorEndsIn_le_liminf_normalizedEndpointWindowProbabilityAlong_of_functionalLimit
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (length : ℕ → ℕ)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hlength : ∀ᶠ n in atTop, 0 < length n)
    (limit : Ω → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc (fun _ => scale n) (length n))
      atTop limit (fun _ => iidSequenceLaw ν) P)
    {radius spacing windowRadius : ℝ} (hradius : 0 < radius)
    (i : ℤ) :
    P.map limit
        (Skorokhod.rangeInOpenIntervalEndsIn (-radius) radius
          ((i : ℝ) * spacing - windowRadius)
          ((i : ℝ) * spacing + windowRadius)) ≤
      atTop.liminf (fun n =>
        normalizedEndpointWindowProbabilityAlong ν
          (fun _ => radius) (fun _ => spacing) (fun _ => windowRadius)
          i scale length n) := by
  have hevent := hlimit.measure_skorokhodCorridorEndsIn_le_liminf
    (-radius) radius ((i : ℝ) * spacing - windowRadius)
    ((i : ℝ) * spacing + windowRadius)
  refine hevent.trans_eq ?_
  apply liminf_congr
  filter_upwards [hscale, hlength] with n hscaleN hlengthN
  have hpath := normalizedStepPathLaw_apply_centeredOpenIntervalEndsIn
    (ν := ν) (scale := fun _ => scale n) (n := length n)
    hlengthN hscaleN (width := 2 * radius)
    (endpointLower := (i : ℝ) * spacing - windowRadius)
    (endpointUpper := (i : ℝ) * spacing + windowRadius) (by linarith)
  simpa [normalizedEndpointWindowProbabilityAlong,
    normalizedEndpointWindowEvent, normalizedStepPathLaw, mul_assoc] using hpath

/-- Moving endpoint windows contained in a fixed weak corridor are bounded
above by its closed limiting path event along a block-length sequence. -/
theorem limsup_normalizedEndpointWindowProbabilityAlong_le_closedCorridor_of_eventually_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (length : ℕ → ℕ)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hlength : ∀ᶠ n in atTop, 0 < length n)
    (limit : Ω → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc (fun _ => scale n) (length n))
      atTop limit (fun _ => iidSequenceLaw ν) P)
    (radius spacing windowRadius : ℕ → ℝ) (i : ℤ)
    {outerRadius endpointLower endpointUpper : ℝ}
    (houter : 0 ≤ outerRadius)
    (hparameters : ∀ᶠ n in atTop,
      radius n ≤ outerRadius ∧
        endpointLower ≤ (i : ℝ) * spacing n - windowRadius n ∧
        (i : ℝ) * spacing n + windowRadius n ≤ endpointUpper) :
    atTop.limsup (fun n => normalizedEndpointWindowProbabilityAlong ν
      radius spacing windowRadius i scale length n) ≤
      P.map limit
        (Skorokhod.rangeInClosedIntervalEndsIn (-outerRadius) outerRadius
          endpointLower endpointUpper) := by
  let weakEvent (n : ℕ) : Set (ℕ → ℝ) :=
    {increment | InHorizontalTube (1 / 2) (2 * outerRadius * scale n)
        (length n) increment ∧
      AdditivePath.displacement (length n) increment / scale n ∈
        Set.Icc endpointLower endpointUpper}
  have hsubset : ∀ᶠ n in atTop,
      normalizedEndpointWindowProbabilityAlong ν radius spacing windowRadius
          i scale length n ≤ iidSequenceLaw ν (weakEvent n) := by
    filter_upwards [hparameters, hscale] with n hn hscaleN
    apply measure_mono
    intro increment hevent
    rcases hevent with ⟨htube, hend⟩
    refine ⟨?_, ?_⟩
    · intro k
      have hk := htube k
      change -(1 / 2 : ℝ) * (2 * radius n * scale n) <
          AdditivePath.displacement (k + 1) increment ∧
        AdditivePath.displacement (k + 1) increment <
          (1 - (1 / 2 : ℝ)) * (2 * radius n * scale n) at hk
      change -(1 / 2 : ℝ) * (2 * outerRadius * scale n) ≤
          AdditivePath.displacement (k + 1) increment ∧
        AdditivePath.displacement (k + 1) increment ≤
          (1 - (1 / 2 : ℝ)) * (2 * outerRadius * scale n)
      have hwidth : radius n * scale n ≤ outerRadius * scale n :=
        mul_le_mul_of_nonneg_right hn.1 hscaleN.le
      constructor
      · apply le_of_lt
        have hk' : -radius n * scale n <
            AdditivePath.displacement (k + 1) increment := by
          nlinarith [hk.1]
        nlinarith
      · apply le_of_lt
        have hk' : AdditivePath.displacement (k + 1) increment <
            radius n * scale n := by
          nlinarith [hk.2]
        nlinarith
    · exact ⟨le_trans hn.2.1 hend.1.le, le_trans hend.2.le hn.2.2⟩
  have hweakBounded : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun n => iidSequenceLaw ν (weakEvent n)) := by
    apply Filter.isBoundedUnder_of_eventually_le (a := 1)
    exact Eventually.of_forall fun n => by
      calc
        iidSequenceLaw ν (weakEvent n) ≤ iidSequenceLaw ν Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
  have hlimsup := Filter.limsup_le_limsup hsubset
    (Filter.isCoboundedUnder_le_of_le atTop (fun _ => bot_le)) hweakBounded
  have hport := hlimit.limsup_measure_skorokhodCorridorEndsIn_le
    (-outerRadius) outerRadius endpointLower endpointUpper
  have hport' : atTop.limsup (fun n => iidSequenceLaw ν (weakEvent n)) ≤
      P.map limit
        (Skorokhod.rangeInClosedIntervalEndsIn (-outerRadius) outerRadius
          endpointLower endpointUpper) := by
    have heq : ∀ᶠ n in atTop,
        iidSequenceLaw ν (weakEvent n) =
          (iidSequenceLaw ν).map
            (normalizedStepCadlagPathIcc (fun _ => scale n) (length n))
            (Skorokhod.rangeInClosedIntervalEndsIn
              (-outerRadius) outerRadius endpointLower endpointUpper) := by
      filter_upwards [hscale, hlength] with n hscaleN hlengthN
      have hpath := normalizedStepPathLaw_apply_centeredClosedIntervalEndsIn
        (ν := ν) (scale := fun _ => scale n) (n := length n)
        hlengthN hscaleN (width := 2 * outerRadius)
        (endpointLower := endpointLower) (endpointUpper := endpointUpper) (by positivity)
      simpa [weakEvent, normalizedStepPathLaw, mul_assoc] using hpath.symm
    calc
      _ = atTop.limsup (fun n =>
          (iidSequenceLaw ν).map
            (normalizedStepCadlagPathIcc (fun _ => scale n) (length n))
            (Skorokhod.rangeInClosedIntervalEndsIn
              (-outerRadius) outerRadius endpointLower endpointUpper)) :=
        limsup_congr heq
      _ ≤ P.map limit
          (Skorokhod.rangeInClosedIntervalEndsIn
            (-outerRadius) outerRadius endpointLower endpointUpper) := hport
  exact hlimsup.trans hport'

/-- Transfer a strict spectral lower bound for narrower Rademacher windows
to a wider endpoint-window event for a centered unit-variance law, along a
possibly reindexed block-length sequence. -/
theorem eventually_ofReal_le_normalizedEndpointWindowProbabilityAlong_of_spectralLower
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (length : ℕ → ℕ)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hlength : ∀ᶠ n in atTop, 0 < length n)
    (limit : Ω → CadlagPath unitInterval ℝ)
    (hRademacher : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc (fun _ => scale n) (length n))
      atTop limit (fun _ => iidSequenceLaw rademacherMeasure) P)
    (hν : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc (fun _ => scale n) (length n))
      atTop limit (fun _ => iidSequenceLaw ν) P)
    (spectralRadius mesh spectralWindow applicationRadius applicationWindow :
      ℕ → ℝ)
    (i : ℤ) {spectralLower applicationLower : ℝ}
    {closedRadius closedWindow openRadius openWindow meshLimit : ℝ}
    (happlicationLower : 0 ≤ applicationLower)
    (hlower : applicationLower < spectralLower)
    (hclosedRadius : 0 ≤ closedRadius)
    (hclosedOpenRadius : closedRadius < openRadius)
    (hclosedOpenWindow : closedWindow < openWindow)
    (hwindowLimit : ∀ᶠ n in atTop,
      spectralRadius n ≤ closedRadius ∧
        (i : ℝ) * mesh n - spectralWindow n ≥
          (i : ℝ) * meshLimit - closedWindow ∧
        (i : ℝ) * mesh n + spectralWindow n ≤
          (i : ℝ) * meshLimit + closedWindow)
    (happlicationContainsOpen : ∀ᶠ n in atTop,
      openRadius ≤ applicationRadius n ∧
        (i : ℝ) * mesh n - applicationWindow n ≤
          (i : ℝ) * meshLimit - openWindow ∧
        (i : ℝ) * meshLimit + openWindow ≤
          (i : ℝ) * mesh n + applicationWindow n)
    (hlowerRademacher : ∀ᶠ n in atTop,
      ENNReal.ofReal spectralLower ≤
        normalizedEndpointWindowProbabilityAlong rademacherMeasure
          spectralRadius mesh spectralWindow i scale length n) :
    ∀ᶠ n in atTop,
      ENNReal.ofReal applicationLower ≤
        normalizedEndpointWindowProbabilityAlong ν applicationRadius mesh
          applicationWindow i scale length n := by
  let spectralProbability : ℕ → ENNReal := fun n =>
    normalizedEndpointWindowProbabilityAlong rademacherMeasure
      spectralRadius mesh spectralWindow i scale length n
  let innerProbability : ℕ → ENNReal := fun n =>
    normalizedEndpointWindowProbabilityAlong ν (fun _ => openRadius)
      (fun _ => meshLimit) (fun _ => openWindow) i scale length n
  have hspectralBounded : Filter.IsBoundedUnder (· ≤ ·) atTop
      spectralProbability := by
    apply Filter.isBoundedUnder_of_eventually_le (a := 1)
    exact Eventually.of_forall fun n => by
      calc
        spectralProbability n ≤ iidSequenceLaw rademacherMeasure Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
  have hspectralFrequently : ∃ᶠ n in atTop,
      ENNReal.ofReal spectralLower ≤ spectralProbability n :=
    Eventually.frequently hlowerRademacher
  have hspectralLimsup : ENNReal.ofReal spectralLower ≤
      atTop.limsup spectralProbability :=
    Filter.le_limsup_of_frequently_le hspectralFrequently hspectralBounded
  have hclosed := limsup_normalizedEndpointWindowProbabilityAlong_le_closedCorridor_of_eventually_bounds
    P rademacherMeasure scale length hscale hlength limit hRademacher
      spectralRadius mesh spectralWindow i (outerRadius := closedRadius)
      (endpointLower := (i : ℝ) * meshLimit - closedWindow)
      (endpointUpper := (i : ℝ) * meshLimit + closedWindow) hclosedRadius (by
        filter_upwards [hwindowLimit] with n hn
        exact ⟨hn.1, hn.2.1, hn.2.2⟩)
  have hclosedMass : ENNReal.ofReal spectralLower ≤
      P.map limit
        (Skorokhod.rangeInClosedIntervalEndsIn (-closedRadius) closedRadius
          ((i : ℝ) * meshLimit - closedWindow)
          ((i : ℝ) * meshLimit + closedWindow)) :=
    hspectralLimsup.trans hclosed
  have hclosedSubsetOpen :
      Skorokhod.rangeInClosedIntervalEndsIn (-closedRadius) closedRadius
          ((i : ℝ) * meshLimit - closedWindow)
          ((i : ℝ) * meshLimit + closedWindow) ⊆
        Skorokhod.rangeInOpenIntervalEndsIn (-openRadius) openRadius
          ((i : ℝ) * meshLimit - openWindow)
          ((i : ℝ) * meshLimit + openWindow) := by
    intro path hpath
    rw [Skorokhod.mem_rangeInClosedIntervalEndsIn_iff] at hpath
    rw [Skorokhod.mem_rangeInOpenIntervalEndsIn_iff]
    refine ⟨?_, ?_⟩
    · rw [Skorokhod.mem_rangeInOpenInterval_iff]
      refine ⟨(openRadius - closedRadius) / 2, by linarith, ?_⟩
      intro t
      have ht := (Skorokhod.mem_rangeInClosedInterval_iff.mp hpath.1) t
      constructor <;> linarith
    · rcases hpath.2 with ⟨hl, hu⟩
      constructor <;> linarith
  have hopenMass : ENNReal.ofReal spectralLower ≤
      P.map limit
        (Skorokhod.rangeInOpenIntervalEndsIn (-openRadius) openRadius
          ((i : ℝ) * meshLimit - openWindow)
          ((i : ℝ) * meshLimit + openWindow)) :=
    hclosedMass.trans (measure_mono hclosedSubsetOpen)
  have hopenDonsker :=
    measure_centeredSkorokhodCorridorEndsIn_le_liminf_normalizedEndpointWindowProbabilityAlong_of_functionalLimit
      P ν scale length hscale hlength limit hν (radius := openRadius)
      (spacing := meshLimit) (windowRadius := openWindow) (by linarith) i
  have hinnerLiminf : ENNReal.ofReal spectralLower ≤
      atTop.liminf innerProbability := by
    exact hopenMass.trans (by simpa [innerProbability] using hopenDonsker)
  have hstrict : ENNReal.ofReal applicationLower <
      atTop.liminf innerProbability := by
    exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg happlicationLower).2 hlower).trans_le
      hinnerLiminf
  have hinnerBounded : Filter.IsBoundedUnder (· ≥ ·) atTop innerProbability := by
    apply Filter.isBoundedUnder_of_eventually_ge (a := 0)
    exact Eventually.of_forall fun _ => bot_le
  have heventuallyInner : ∀ᶠ n in atTop,
      ENNReal.ofReal applicationLower < innerProbability n :=
    eventually_lt_of_lt_liminf hstrict hinnerBounded
  filter_upwards [heventuallyInner, happlicationContainsOpen, hscale]
    with n hinner happ hscaleN
  have hsubset :
      normalizedEndpointWindowEvent openRadius meshLimit openWindow i
          (scale n) (length n) ⊆
        normalizedEndpointWindowEvent (applicationRadius n) (mesh n)
          (applicationWindow n) i (scale n) (length n) := by
    intro increment hevent
    rcases hevent with ⟨htube, hend⟩
    refine ⟨?_, ?_⟩
    · intro k
      have hk := htube k
      change -(1 / 2 : ℝ) * (2 * openRadius * scale n) <
          AdditivePath.displacement (k + 1) increment ∧
        AdditivePath.displacement (k + 1) increment <
          (1 - (1 / 2 : ℝ)) * (2 * openRadius * scale n) at hk
      change -(1 / 2 : ℝ) * (2 * applicationRadius n * scale n) <
          AdditivePath.displacement (k + 1) increment ∧
        AdditivePath.displacement (k + 1) increment <
          (1 - (1 / 2 : ℝ)) * (2 * applicationRadius n * scale n)
      have hwidth : openRadius * scale n ≤ applicationRadius n * scale n :=
        mul_le_mul_of_nonneg_right happ.1 hscaleN.le
      constructor <;> nlinarith [hk.1, hk.2]
    · exact ⟨lt_of_le_of_lt happ.2.1 hend.1,
        lt_of_lt_of_le hend.2 happ.2.2⟩
  exact le_trans (le_of_lt hinner) (measure_mono hsubset)

/-- Transfer the seven narrow spectral bands together.  The hypotheses retain
the two strict corridor enlargements required by the closed-set upper and
open-set lower Portmanteau bounds; the result is exactly the uniform endpoint
family consumed by the return-kernel iteration. -/
theorem eventually_forall_seven_ofReal_le_normalizedEndpointWindowProbabilityAlong_of_spectralLower
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (length : ℕ → ℕ)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hlength : ∀ᶠ n in atTop, 0 < length n)
    (limit : Ω → CadlagPath unitInterval ℝ)
    (hRademacher : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc (fun _ => scale n) (length n))
      atTop limit (fun _ => iidSequenceLaw rademacherMeasure) P)
    (hν : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc (fun _ => scale n) (length n))
      atTop limit (fun _ => iidSequenceLaw ν) P)
    (spectralRadius mesh spectralWindow applicationRadius applicationWindow :
      ℕ → ℝ)
    {spectralLower applicationLower : ℝ}
    {closedRadius closedWindow openRadius openWindow meshLimit : ℝ}
    (happlicationLower : 0 ≤ applicationLower)
    (hlower : applicationLower < spectralLower)
    (hclosedRadius : 0 ≤ closedRadius)
    (hclosedOpenRadius : closedRadius < openRadius)
    (hclosedOpenWindow : closedWindow < openWindow)
    (hwindowLimit : ∀ i ∈ Finset.Icc (-3 : ℤ) 3, ∀ᶠ n in atTop,
      spectralRadius n ≤ closedRadius ∧
        (i : ℝ) * mesh n - spectralWindow n ≥
          (i : ℝ) * meshLimit - closedWindow ∧
        (i : ℝ) * mesh n + spectralWindow n ≤
          (i : ℝ) * meshLimit + closedWindow)
    (happlicationContainsOpen : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      ∀ᶠ n in atTop,
        openRadius ≤ applicationRadius n ∧
          (i : ℝ) * mesh n - applicationWindow n ≤
            (i : ℝ) * meshLimit - openWindow ∧
          (i : ℝ) * meshLimit + openWindow ≤
            (i : ℝ) * mesh n + applicationWindow n)
    (hlowerRademacher : ∀ᶠ n in atTop, ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      ENNReal.ofReal spectralLower ≤
        normalizedEndpointWindowProbabilityAlong rademacherMeasure
          spectralRadius mesh spectralWindow i scale length n) :
    ∀ᶠ n in atTop, ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      ENNReal.ofReal applicationLower ≤
        normalizedEndpointWindowProbabilityAlong ν applicationRadius mesh
          applicationWindow i scale length n := by
  apply (Finset.Icc (-3 : ℤ) 3).eventually_all.2
  intro i hi
  have hsingle := eventually_ofReal_le_normalizedEndpointWindowProbabilityAlong_of_spectralLower
    P ν scale length hscale hlength limit hRademacher hν
    spectralRadius mesh spectralWindow applicationRadius applicationWindow i
    happlicationLower hlower hclosedRadius hclosedOpenRadius hclosedOpenWindow
    (hwindowLimit i hi) (happlicationContainsOpen i hi)
    (hlowerRademacher.mono fun n h => h i hi)
  exact hsingle

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
