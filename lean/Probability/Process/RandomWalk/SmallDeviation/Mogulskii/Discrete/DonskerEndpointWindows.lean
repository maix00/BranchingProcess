/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Endpoint
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.EndpointWindows
public import Probability.Distributions.Rademacher

/-!
# Donsker transfer for endpoint windows

These adapters keep the endpoint-window mesh, window half-width, and path
normalization independent. This permits a narrow spectral event to be compared
with a slightly wider fixed Brownian event before transferring it to another
centered unit-variance increment law.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- The raw-increment event corresponding to a normalized tube and endpoint
window at the given path scale. -/
def normalizedEndpointWindowEvent (radius spacing windowRadius : ℝ)
    (i : ℤ) (scale : ℝ) (length : ℕ) : Set (ℕ → ℝ) :=
  {increment | InOpenHorizontalTube (1 / 2) (2 * radius * scale) length increment ∧
    AdditivePath.displacement length increment / scale ∈
      Set.Ioo ((i : ℝ) * spacing - windowRadius)
        ((i : ℝ) * spacing + windowRadius)}

/-- Probability of the normalized tube and endpoint window under an IID
increment law. -/
noncomputable def normalizedEndpointWindowProbability
    (ν : Measure ℝ) (radius spacing windowRadius : ℝ)
    (i : ℤ) (scale : ℕ → ℝ) (n : ℕ) : ENNReal :=
  iidSequenceLaw ν
    (normalizedEndpointWindowEvent radius spacing windowRadius i (scale n) n)

/-- Scaling the normalized tube and endpoint coordinates back by `scale`
recovers the endpoint-window block event. -/
theorem normalizedEndpointWindowEvent_eq_endpointWindowBlockEvent_scale
    {radius spacing windowRadius scale : ℝ} (hscale : 0 < scale)
    (i : ℤ) (length : ℕ) :
    normalizedEndpointWindowEvent radius spacing windowRadius i scale length =
      endpointWindowBlockEvent (radius * scale) (spacing * scale)
        (windowRadius * scale) i length := by
  ext increment
  simp only [normalizedEndpointWindowEvent, endpointWindowBlockEvent,
    Set.mem_ofPred_eq]
  have hsum :
      AdditivePath.displacement length increment / scale ∈
          Set.Ioo ((i : ℝ) * spacing - windowRadius)
            ((i : ℝ) * spacing + windowRadius) ↔
        AdditivePath.displacement length increment ∈
          Set.Ioo ((i : ℝ) * (spacing * scale) - windowRadius * scale)
            ((i : ℝ) * (spacing * scale) + windowRadius * scale) := by
    constructor <;> intro h
    · rcases h with ⟨hlo, hhi⟩
      constructor
      · have hlo' := (lt_div_iff₀ hscale).mp hlo
        nlinarith
      · have hhi' := (div_lt_iff₀ hscale).mp hhi
        nlinarith
    · rcases h with ⟨hlo, hhi⟩
      constructor
      · have hlo' : ((i : ℝ) * spacing - windowRadius) * scale <
          AdditivePath.displacement length increment := by nlinarith
        exact (lt_div_iff₀ hscale).mpr hlo'
      · have hhi' : AdditivePath.displacement length increment <
          ((i : ℝ) * spacing + windowRadius) * scale := by nlinarith
        exact (div_lt_iff₀ hscale).mpr hhi'
  constructor
  · rintro ⟨htube, hend⟩
    refine ⟨by simpa [mul_assoc] using htube, hsum.mp hend⟩
  · rintro ⟨htube, hend⟩
    refine ⟨by simpa [mul_assoc] using htube, hsum.mpr hend⟩

/-- A block event in original coordinates equals its normalized-window
probability when all three spatial parameters use the same positive scale. -/
theorem normalizedEndpointWindowProbability_eq_endpointWindowBlockEvent_of_div
    (ν : Measure ℝ) (radius spacing windowRadius : ℝ) (i : ℤ)
    (n : ℕ) (hn : 0 < n) :
    normalizedEndpointWindowProbability ν (radius / Real.sqrt n)
        (spacing / Real.sqrt n) (windowRadius / Real.sqrt n) i
        (fun _ => Real.sqrt n) n =
      iidSequenceLaw ν (endpointWindowBlockEvent radius spacing windowRadius i n) := by
  have hsqrt : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hevent := normalizedEndpointWindowEvent_eq_endpointWindowBlockEvent_scale
    (radius := radius / Real.sqrt n)
    (spacing := spacing / Real.sqrt n)
    (windowRadius := windowRadius / Real.sqrt n) hsqrt i n
  have hrad : radius / Real.sqrt n * Real.sqrt n = radius :=
    div_mul_cancel₀ _ hsqrt.ne'
  have hspacing : spacing / Real.sqrt n * Real.sqrt n = spacing :=
    div_mul_cancel₀ _ hsqrt.ne'
  have hwindow : windowRadius / Real.sqrt n * Real.sqrt n = windowRadius :=
    div_mul_cancel₀ _ hsqrt.ne'
  unfold normalizedEndpointWindowProbability
  rw [show Real.sqrt (n : ℝ) = (fun _ : ℕ => Real.sqrt n) n by rfl]
  rw [hevent]
  simp [hrad, hspacing, hwindow]

/-- Open endpoint windows transfer from a functional limit by the open-set
Portmanteau inequality. -/
theorem measure_centeredSkorokhodCorridorEndsIn_le_liminf_normalizedEndpointWindowProbability_of_functionalLimit
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (limit : Ω → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc scale n)
      atTop limit (fun _ => iidSequenceLaw ν) P)
    {radius spacing windowRadius : ℝ} (hradius : 0 < radius)
    (i : ℤ) :
    P.map limit
        (Skorokhod.rangeInOpenIntervalEndsIn (-radius) radius
          ((i : ℝ) * spacing - windowRadius)
          ((i : ℝ) * spacing + windowRadius)) ≤
      atTop.liminf (fun n =>
        normalizedEndpointWindowProbability ν radius spacing windowRadius
          i scale n) := by
  have hevent := hlimit.measure_skorokhodCorridorEndsIn_le_liminf
    (-radius) radius ((i : ℝ) * spacing - windowRadius)
    ((i : ℝ) * spacing + windowRadius)
  refine hevent.trans_eq ?_
  apply liminf_congr
  filter_upwards [eventually_gt_atTop 0, hscale] with n hn hscalePos
  change normalizedStepPathLaw ν scale n
      (Skorokhod.rangeInOpenIntervalEndsIn (-radius) radius
        ((i : ℝ) * spacing - windowRadius)
        ((i : ℝ) * spacing + windowRadius)) = _
  have hidentity := normalizedStepPathLaw_apply_centeredOpenIntervalEndsIn
    (ν := ν) (scale := scale) (n := n) hn hscalePos
    (width := 2 * radius)
    (endpointLower := (i : ℝ) * spacing - windowRadius)
    (endpointUpper := (i : ℝ) * spacing + windowRadius) (by linarith)
  simpa [normalizedEndpointWindowProbability, normalizedEndpointWindowEvent,
    mul_assoc] using hidentity

/-- Moving endpoint windows whose parameters are eventually contained in a
fixed weak corridor are bounded above by the closed limiting corridor. -/
theorem limsup_normalizedEndpointWindowProbability_le_closedCorridor_of_eventually_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (limit : Ω → CadlagPath unitInterval ℝ)
    (hlimit : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc scale n)
      atTop limit (fun _ => iidSequenceLaw ν) P)
    (radius spacing windowRadius : ℕ → ℝ) (i : ℤ)
    {outerRadius endpointLower endpointUpper : ℝ}
    (houter : 0 ≤ outerRadius)
    (hparameters : ∀ᶠ n in atTop,
      radius n ≤ outerRadius ∧
        endpointLower ≤ (i : ℝ) * spacing n - windowRadius n ∧
        (i : ℝ) * spacing n + windowRadius n ≤ endpointUpper) :
    atTop.limsup (fun n =>
      normalizedEndpointWindowProbability ν (radius n) (spacing n)
        (windowRadius n) i scale n) ≤
      P.map limit
        (Skorokhod.rangeInClosedIntervalEndsIn (-outerRadius) outerRadius
          endpointLower endpointUpper) := by
  let weakEvent (n : ℕ) : Set (ℕ → ℝ) :=
    {increment | InHorizontalTube (1 / 2) (2 * outerRadius * scale n)
        n increment ∧
      AdditivePath.displacement n increment / scale n ∈
        Set.Icc endpointLower endpointUpper}
  have hsubset : ∀ᶠ n in atTop,
      normalizedEndpointWindowProbability ν (radius n) (spacing n)
          (windowRadius n) i scale n ≤
        iidSequenceLaw ν (weakEvent n) := by
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
  have hport := RandomWalk.limsup_weakTubeEndsIn_le_measure_centeredSkorokhodCorridorEndsIn_of_functionalLimit
    P ν scale hscale limit hlimit
    (width := 2 * outerRadius) (endpointLower := endpointLower)
    (endpointUpper := endpointUpper) (by positivity)
  have hbounded : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun n => iidSequenceLaw ν (weakEvent n)) := by
    apply Filter.isBoundedUnder_of_eventually_le (a := 1)
    exact Eventually.of_forall fun n => by
      calc
        iidSequenceLaw ν (weakEvent n) ≤ iidSequenceLaw ν Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
  have hlimsup := Filter.limsup_le_limsup hsubset
    (Filter.isCoboundedUnder_le_of_le atTop (fun _ => bot_le)) hbounded
  have hport' : Filter.limsup (fun n => iidSequenceLaw ν (weakEvent n)) atTop ≤
      P.map limit
        (Skorokhod.rangeInClosedIntervalEndsIn (-outerRadius) outerRadius
          endpointLower endpointUpper) := by
    simpa only [show 2 * outerRadius / 2 = outerRadius by ring] using hport
  exact hlimsup.trans hport'

/-- A strict spectral lower bound for narrower Rademacher windows transfers to
a wider endpoint-window event under any centered unit-variance increment law.
The intermediate closed Brownian corridor is placed strictly inside the
open corridor used for the second Portmanteau transfer. -/
theorem eventually_ofReal_le_normalizedEndpointWindowProbability_of_spectralLower
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (limit : Ω → CadlagPath unitInterval ℝ)
    (hRademacher : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc scale n)
      atTop limit (fun _ => iidSequenceLaw rademacherMeasure) P)
    (hν : TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc scale n)
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
        normalizedEndpointWindowProbability rademacherMeasure
          (spectralRadius n) (mesh n) (spectralWindow n) i scale n) :
    ∀ᶠ n in atTop,
      ENNReal.ofReal applicationLower ≤
        normalizedEndpointWindowProbability ν (applicationRadius n)
          (mesh n) (applicationWindow n) i scale n := by
  let spectralProbability : ℕ → ENNReal := fun n =>
    normalizedEndpointWindowProbability rademacherMeasure
      (spectralRadius n) (mesh n) (spectralWindow n) i scale n
  let innerProbability : ℕ → ENNReal := fun n =>
    normalizedEndpointWindowProbability ν openRadius meshLimit openWindow i
      scale n
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
  have hclosed := limsup_normalizedEndpointWindowProbability_le_closedCorridor_of_eventually_bounds
    P rademacherMeasure scale hscale limit hRademacher spectralRadius mesh
      spectralWindow i (outerRadius := closedRadius)
      (endpointLower := (i : ℝ) * meshLimit - closedWindow)
      (endpointUpper := (i : ℝ) * meshLimit + closedWindow) hclosedRadius (by
        filter_upwards [hwindowLimit] with n hn
        exact ⟨hn.1, hn.2.1, hn.2.2⟩)
  have hclosedMass : ENNReal.ofReal spectralLower ≤
      P.map limit
        (Skorokhod.rangeInClosedIntervalEndsIn (-closedRadius) closedRadius
          ((i : ℝ) * meshLimit - closedWindow)
          ((i : ℝ) * meshLimit + closedWindow)) := by
    exact hspectralLimsup.trans hclosed
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
    measure_centeredSkorokhodCorridorEndsIn_le_liminf_normalizedEndpointWindowProbability_of_functionalLimit
      P ν scale hscale limit hν (radius := openRadius)
      (spacing := meshLimit) (windowRadius := openWindow) (by linarith) i
  have hinnerLiminf : ENNReal.ofReal spectralLower ≤
      atTop.liminf innerProbability := by
    exact hopenMass.trans (by simpa [innerProbability] using hopenDonsker)
  have hstrict : ENNReal.ofReal applicationLower <
      atTop.liminf innerProbability := by
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg happlicationLower).2 hlower |>.trans_le
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
          (scale n) n ⊆
        normalizedEndpointWindowEvent (applicationRadius n) (mesh n)
          (applicationWindow n) i (scale n) n := by
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

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
