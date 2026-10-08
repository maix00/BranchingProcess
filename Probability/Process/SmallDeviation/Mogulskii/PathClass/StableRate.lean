/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.SmallDeviation.Mogulskii.PathClass.NullMeasurable
import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw
import Probability.Process.Stable.SmallDeviation.EscapeRate.Corridor

/-!
# Stable small-deviation rate for constant `M₂` corridors

The source's pointwise-strict corridor need not be open in `J₁`: a càdlàg
path can approach a boundary through a left limit without attaining it.  For
constant finite boundaries, its stable small-width rate can nevertheless be
obtained by squeezing the exact event between narrower and wider uniformly
interior corridors.  This avoids a boundary-null hypothesis and preserves
the pointwise event.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.Process.SmallDeviation.Mogulskii

/-- The exact pointwise-strict corridor between finite constant boundaries,
with the source's pinned-zero starting condition. -/
def constantCorridorEvent (lower upper : ℝ) : Set (CadlagPath unitInterval ℝ) :=
  {f | f ⊥ = 0 ∧ ∀ t, lower < f t ∧ f t < upper}

theorem corridorSet_constant_eq (lower upper : ℝ) :
    corridorSet (StepBoundary.constant (upper : EReal))
      (StepBoundary.constant (lower : EReal)) = constantCorridorEvent lower upper := by
  ext f
  simp [corridorSet, constantCorridorEvent, StepBoundary.eval_constant]

/-- The constant corridor is an `M₂` corridor whenever it contains the
origin.  The constant zero path witnesses continuous admissibility. -/
def M2Corridor.constantBounds {lower upper : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper) : M2Corridor where
  upper := StepBoundary.constant (upper : EReal)
  lower := StepBoundary.constant (lower : EReal)
  hasContinuousAdmissiblePath := by
    let f : C(unitInterval, ℝ) := ContinuousMap.const unitInterval 0
    refine ⟨f, rfl, ?_⟩
    rw [corridorSet_constant_eq]
    constructor
    · rfl
    · intro t
      simp only [f, ContinuousMap.const_apply, Skorokhod.ofContinuousMap_apply]
      exact ⟨hlower, hupper⟩

@[simp]
theorem M2Corridor.constantBounds_toSet {lower upper : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper) :
    (M2Corridor.constantBounds hlower hupper).toSet =
      constantCorridorEvent lower upper := by
  simp [M2Corridor.toSet, M1Corridor.toSet, M2Corridor.constantBounds,
    corridorSet_constant_eq]

/-- The exact event obtained by shrinking a fixed constant corridor by the
positive factor `a`. -/
def scaledConstantCorridorEvent (a lower upper : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  constantCorridorEvent (a * lower) (a * upper)

theorem scaledConstantCorridorEvent_eq_toSet
    {a lower upper : ℝ} (ha : 0 < a) (hlower : lower < 0) (hupper : 0 < upper) :
    scaledConstantCorridorEvent a lower upper =
      (M2Corridor.constantBounds (mul_neg_of_pos_of_neg ha hlower)
        (mul_pos ha hupper)).toSet := by
  simp [scaledConstantCorridorEvent, M2Corridor.constantBounds_toSet]

/-- At each positive scale, the exact constant corridor is the path-class
`M₂` event and inherits its null-measurability under finite path laws. -/
theorem nullMeasurableSet_scaledConstantCorridorEvent
    {a lower upper : ℝ} (ha : 0 < a) (hlower : lower < 0) (hupper : 0 < upper)
    (P : Measure (CadlagPath unitInterval ℝ)) [IsFiniteMeasure P] :
    NullMeasurableSet (scaledConstantCorridorEvent a lower upper) P := by
  rw [scaledConstantCorridorEvent_eq_toSet ha hlower hupper]
  exact M2Corridor.nullMeasurableSet_toSet _ P

/-- Uniformly interior path corridors transfer to the corresponding process
complete-segment event under matching stable increment laws. -/
private theorem measure_rangeInOpenInterval_eq_fullSegmentCorridorEvent
    {α : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hX : IsStableLevyProcess α μ X Q) (lower upper : ℝ) :
    P (Skorokhod.rangeInOpenInterval lower upper) =
      Q (fullSegmentCorridorEvent X 0 1 lower upper) := by
  have hpath : Skorokhod.rangeInOpenIntervalEndsIn lower upper
      (lower - 1) (upper + 1) = Skorokhod.rangeInOpenInterval lower upper := by
    ext f
    simp only [Skorokhod.rangeInOpenIntervalEndsIn, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨margin, hmargin, hvalues⟩, hend⟩
      exact ⟨margin, hmargin, hvalues⟩
    · rintro ⟨margin, hmargin, hvalues⟩
      refine ⟨⟨margin, hmargin, hvalues⟩, ?_⟩
      have ht := hvalues ⊤
      constructor <;> linarith
  have hproc : fullSegmentCorridorReturnEvent X 0 1 lower upper
      (lower - 1) (upper + 1) = fullSegmentCorridorEvent X 0 1 lower upper := by
    ext ω
    simp only [fullSegmentCorridorReturnEvent, segmentCorridorEndpointEvent,
      Set.mem_inter_iff, Set.mem_ofPred_eq, fullSegmentCorridorEvent]
    constructor
    · rintro ⟨hpath, _⟩
      exact hpath
    · intro hpath
      refine ⟨hpath, ?_⟩
      obtain ⟨margin, hmargin, hvalues⟩ := hpath
      have ht := hvalues ⊤
      change segmentIncrement X 0 1 ω ⊤ ∈ Set.Ioo (lower - 1) (upper + 1)
      simp only [Set.mem_Ioo]
      exact ⟨by linarith, by linarith⟩
  calc
    P (Skorokhod.rangeInOpenInterval lower upper) =
        P (Skorokhod.rangeInOpenIntervalEndsIn lower upper
          (lower - 1) (upper + 1)) := by rw [hpath]
    _ = Q (fullSegmentCorridorReturnEvent X 0 1 lower upper
          (lower - 1) (upper + 1)) :=
        hP.measure_corridorReturnEvent_eq hX lower upper (lower - 1) (upper + 1)
    _ = Q (fullSegmentCorridorEvent X 0 1 lower upper) := by rw [hproc]

/-! The exact event is between a smaller open corridor and a slightly
expanded open corridor. -/

private theorem rangeInOpenInterval_subset_pointwiseCorridor
    {lo hi lower upper : ℝ}
    (hlo : lo < lower) (hhi : upper < hi) :
    Skorokhod.rangeInOpenInterval lower upper ⊆
      {f : CadlagPath unitInterval ℝ | ∀ t, lo < f t ∧ f t < hi} := by
  intro f hf
  obtain ⟨margin, hmargin, hpath⟩ := hf
  intro t
  refine ⟨?_, ?_⟩
  · obtain ⟨hlo', _⟩ := hpath t
    linarith
  · obtain ⟨_, hhi'⟩ := hpath t
    linarith

private theorem constantCorridorEvent_subset_rangeInOpenInterval
    {lower upper lo hi : ℝ}
    (hlo : lo < lower) (hhi : upper < hi) :
    constantCorridorEvent lower upper ⊆
      Skorokhod.rangeInOpenInterval lo hi := by
  intro f hf
  rcases hf with ⟨_, hpath⟩
  let margin : ℝ := min (lower - lo) (hi - upper) / 2
  have hmargin : 0 < margin := by
    dsimp [margin]
    exact half_pos (lt_min (sub_pos.mpr hlo) (sub_pos.mpr hhi))
  refine ⟨margin, hmargin, fun t => ?_⟩
  obtain ⟨hl, hu⟩ := hpath t
  constructor <;> dsimp [margin] <;> have hm := min_le_left (lower - lo) (hi - upper) <;>
    have hm' := min_le_right (lower - lo) (hi - upper) <;> linarith

private theorem measure_rangeInOpenInterval_le_constantCorridorEvent
    {α : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    {lo hi lower upper : ℝ} (hlo : lower < lo) (hhi : hi < upper) :
    P (Skorokhod.rangeInOpenInterval lo hi) ≤
      P (constantCorridorEvent lower upper) := by
  let startZero : Set (CadlagPath unitInterval ℝ) := {f | f ⊥ = 0}
  have heq : Skorokhod.rangeInOpenInterval lo hi =ᵐ[P]
      Skorokhod.rangeInOpenInterval lo hi ∩ startZero := by
    filter_upwards [hP.ae_start_eq_zero] with f hf
    simp [startZero, hf]
  have hsub : Skorokhod.rangeInOpenInterval lo hi ∩ startZero ⊆
      constantCorridorEvent lower upper := by
    intro f hf
    refine ⟨hf.2, ?_⟩
    exact rangeInOpenInterval_subset_pointwiseCorridor hlo hhi hf.1
  calc
    P (Skorokhod.rangeInOpenInterval lo hi) =
        P (Skorokhod.rangeInOpenInterval lo hi ∩ startZero) := measure_congr heq
    _ ≤ P (constantCorridorEvent lower upper) := measure_mono hsub

private theorem measure_constantCorridorEvent_le_rangeInOpenInterval
    {P : Measure (CadlagPath unitInterval ℝ)}
    {lower upper lo hi : ℝ} (hlo : lo < lower) (hhi : upper < hi) :
    P (constantCorridorEvent lower upper) ≤
      P (Skorokhod.rangeInOpenInterval lo hi) :=
  measure_mono (constantCorridorEvent_subset_rangeInOpenInterval hlo hhi)

private theorem rpow_log_rescale {α e s q : ℝ}
    (he : 0 < e) (hs : 0 < s) :
    e ^ α * Real.log q = (e / s) ^ α * (s ^ α * Real.log q) := by
  have hpow : (e / s) ^ α * s ^ α = e ^ α := by
    rw [Real.div_rpow he.le hs.le]
    exact div_mul_cancel₀ (e ^ α) (ne_of_gt (Real.rpow_pos_of_pos hs α))
  calc
    e ^ α * Real.log q = ((e / s) ^ α * s ^ α) * Real.log q := by rw [hpow]
    _ = (e / s) ^ α * (s ^ α * Real.log q) := by ring

/-- A constant finite `M₂` corridor has the stable-process small-width rate.
The limiting coefficient is the common stable escape constant multiplied by
the reciprocal `α`-power of the corridor half-width.  No frontier-null
assumption is needed: exact pointwise strict membership is squeezed between
inner and outer `J₁`-open corridors whose relative widths tend to one. -/
theorem exists_tendsto_log_scaledConstantCorridorEvent
    {α : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper) :
    ∃ C : ℝ, C < 0 ∧
      Tendsto (fun a : ℝ => a ^ α *
        Real.log ((P (scaledConstantCorridorEvent a lower upper)).toReal))
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 / ((upper - lower) / 2)) ^ α * C)) := by
  let radius : ℝ := (upper - lower) / 2
  let center : ℝ := (upper + lower) / (upper - lower)
  have hradius : 0 < radius := by
    dsimp [radius]
    linarith
  have hcenter : -1 < center ∧ center < 1 := by
    dsimp [center]
    constructor
    · rw [lt_div_iff₀ (by linarith : 0 < upper - lower)]
      linarith
    · rw [div_lt_iff₀ (by linarith : 0 < upper - lower)]
      linarith
  have hlowerScale : radius * (center - 1) = lower := by
    dsimp [radius, center]
    field_simp [ne_of_gt (show 0 < upper - lower by linarith)]
    ring
  have hupperScale : radius * (center + 1) = upper := by
    dsimp [radius, center]
    field_simp [ne_of_gt (show 0 < upper - lower by linarith)]
    ring
  obtain ⟨C, hC, _, _, hshift⟩ :=
    hX.exists_shiftedCorridor_escape_rate hcdf hcenter
  let l : Filter ℝ := 𝓝[>] (0 : ℝ)
  let baseRate : ℝ → ℝ := stableShiftedCorridorLogRate Q X α center
  have hbase : Tendsto baseRate l (𝓝 C) := by
    simpa [baseRate, l] using hshift
  have hid : Tendsto id l (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have honeMinus : Tendsto (fun a : ℝ => 1 - a) l (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub hid
  have honePlus : Tendsto (fun a : ℝ => 1 + a) l (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.add hid
  let narrowScale : ℝ → ℝ := fun a => a * radius * (1 - a)
  let wideScale : ℝ → ℝ := fun a => a * radius * (1 + a)
  have hnarrowZero : Tendsto narrowScale l (𝓝 (0 : ℝ)) := by
    have hfirst : Tendsto (fun a : ℝ => a * radius) l (𝓝 0) := by
      simpa using hid.mul_const radius
    simpa [narrowScale, mul_assoc] using hfirst.mul honeMinus
  have hwideZero : Tendsto wideScale l (𝓝 (0 : ℝ)) := by
    have hfirst : Tendsto (fun a : ℝ => a * radius) l (𝓝 0) := by
      simpa using hid.mul_const radius
    simpa [wideScale, mul_assoc] using hfirst.mul honePlus
  have hnarrowPos : ∀ᶠ a : ℝ in l, 0 < narrowScale a := by
    filter_upwards [self_mem_nhdsWithin,
      honeMinus.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with a ha hminus
    exact mul_pos (mul_pos ha hradius) hminus
  have hwidePos : ∀ᶠ a : ℝ in l, 0 < wideScale a := by
    filter_upwards [self_mem_nhdsWithin,
      honePlus.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with a ha hplus
    exact mul_pos (mul_pos ha hradius) hplus
  have hnarrow : Tendsto narrowScale l (𝓝[>] (0 : ℝ)) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨hnarrowZero, hnarrowPos⟩
  have hwide : Tendsto wideScale l (𝓝[>] (0 : ℝ)) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨hwideZero, hwidePos⟩
  have hdenN : Tendsto (fun a : ℝ => radius * (1 - a)) l (𝓝 radius) := by
    simpa using tendsto_const_nhds.mul honeMinus
  have hdenW : Tendsto (fun a : ℝ => radius * (1 + a)) l (𝓝 radius) := by
    simpa using tendsto_const_nhds.mul honePlus
  have hinvN : Tendsto (fun a : ℝ => (radius * (1 - a))⁻¹) l
      (𝓝 radius⁻¹) := hdenN.inv₀ hradius.ne'
  have hinvW : Tendsto (fun a : ℝ => (radius * (1 + a))⁻¹) l
      (𝓝 radius⁻¹) := hdenW.inv₀ hradius.ne'
  have hrInvPos : 0 < radius⁻¹ := inv_pos.mpr hradius
  have hfactorN : Tendsto (fun a : ℝ => (radius * (1 - a))⁻¹ ^ α) l
      (𝓝 (radius⁻¹ ^ α)) :=
    (Real.continuousAt_rpow_const radius⁻¹ α (Or.inl hrInvPos.ne')).tendsto.comp hinvN
  have hfactorW : Tendsto (fun a : ℝ => (radius * (1 + a))⁻¹ ^ α) l
      (𝓝 (radius⁻¹ ^ α)) :=
    (Real.continuousAt_rpow_const radius⁻¹ α (Or.inl hrInvPos.ne')).tendsto.comp hinvW
  have hlowerLimit : Tendsto
      (fun a : ℝ => (radius * (1 - a))⁻¹ ^ α * baseRate (narrowScale a)) l
      (𝓝 (radius⁻¹ ^ α * C)) := hfactorN.mul (hbase.comp hnarrow)
  have hupperLimit : Tendsto
      (fun a : ℝ => (radius * (1 + a))⁻¹ ^ α * baseRate (wideScale a)) l
      (𝓝 (radius⁻¹ ^ α * C)) := hfactorW.mul (hbase.comp hwide)
  let exactRate : ℝ → ℝ := fun a => a ^ α *
    Real.log ((P (scaledConstantCorridorEvent a lower upper)).toReal)
  let narrowRate : ℝ → ℝ := fun a =>
    (radius * (1 - a))⁻¹ ^ α * baseRate (narrowScale a)
  let wideRate : ℝ → ℝ := fun a =>
    (radius * (1 + a))⁻¹ ^ α * baseRate (wideScale a)
  have hrateEq (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
      a ^ α * Real.log ((shiftedCorridorProbability Q X center
          (narrowScale a)).toReal) = narrowRate a ∧
      a ^ α * Real.log ((shiftedCorridorProbability Q X center
          (wideScale a)).toReal) = wideRate a := by
    have hsN : 0 < narrowScale a := by
      dsimp [narrowScale]
      exact mul_pos (mul_pos ha hradius) (by linarith)
    have hsW : 0 < wideScale a := by
      dsimp [wideScale]
      exact mul_pos (mul_pos ha hradius) (by linarith)
    have hratioN : a / narrowScale a = (radius * (1 - a))⁻¹ := by
      dsimp [narrowScale]
      field_simp [ha.ne', hradius.ne', ne_of_gt (by linarith : 0 < 1 - a)]
    have hratioW : a / wideScale a = (radius * (1 + a))⁻¹ := by
      dsimp [wideScale]
      field_simp [ha.ne', hradius.ne']
    constructor
    · calc
        a ^ α * Real.log ((shiftedCorridorProbability Q X center
            (narrowScale a)).toReal) =
              (a / narrowScale a) ^ α *
                (narrowScale a ^ α * Real.log
                  ((shiftedCorridorProbability Q X center
                    (narrowScale a)).toReal)) :=
          rpow_log_rescale ha hsN
        _ = narrowRate a := by
          rw [hratioN]
          rfl
    · calc
        a ^ α * Real.log ((shiftedCorridorProbability Q X center
            (wideScale a)).toReal) =
              (a / wideScale a) ^ α *
                (wideScale a ^ α * Real.log
                  ((shiftedCorridorProbability Q X center
                    (wideScale a)).toReal)) :=
          rpow_log_rescale ha hsW
        _ = wideRate a := by
          rw [hratioW]
          rfl
  have hqpos (s : ℝ) (hs : 0 < s) :
      0 < shiftedCorridorProbability Q X center s := by
    have hlo : s * (center - 1) < 0 :=
      mul_neg_of_pos_of_neg hs (by linarith [hcenter.2])
    have hhi : 0 < s * (center + 1) :=
      mul_pos hs (by linarith [hcenter.1])
    unfold shiftedCorridorProbability
    exact hX.measure_fullSegmentCorridor_pos_of_cdfAtZero _ _ hlo hhi hcdf
  have hsmall : ∀ᶠ a : ℝ in l, a < 1 :=
    hid.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hbound : ∀ᶠ a : ℝ in l,
      narrowRate a ≤ exactRate a ∧ exactRate a ≤ wideRate a := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with a ha ha1
    have hinnerLower : a * lower < a * (1 - a) * lower := by
      have hgap : 0 < a * a * (-lower) :=
        mul_pos (mul_pos ha ha) (neg_pos.mpr hlower)
      nlinarith [hgap]
    have hinnerUpper : a * (1 - a) * upper < a * upper := by
      have hgap : 0 < a * a * upper := mul_pos (mul_pos ha ha) hupper
      nlinarith [hgap]
    have houterLower : a * (1 + a) * lower < a * lower := by
      have hgap : 0 < a * a * (-lower) :=
        mul_pos (mul_pos ha ha) (neg_pos.mpr hlower)
      nlinarith [hgap]
    have houterUpper : a * upper < a * (1 + a) * upper := by
      have hgap : 0 < a * a * upper := mul_pos (mul_pos ha ha) hupper
      nlinarith [hgap]
    let lowLower := a * (1 - a) * lower
    let lowUpper := a * (1 - a) * upper
    let highLower := a * (1 + a) * lower
    let highUpper := a * (1 + a) * upper
    have hprobLower :
        shiftedCorridorProbability Q X center (narrowScale a) ≤
          P (scaledConstantCorridorEvent a lower upper) := by
      have hleft : narrowScale a * (center - 1) = lowLower := by
        dsimp [narrowScale, lowLower]
        calc
          a * radius * (1 - a) * (center - 1) =
              a * (1 - a) * (radius * (center - 1)) := by ring
          _ = _ := by rw [hlowerScale]
      have hright : narrowScale a * (center + 1) = lowUpper := by
        dsimp [narrowScale, lowUpper]
        calc
          a * radius * (1 - a) * (center + 1) =
              a * (1 - a) * (radius * (center + 1)) := by ring
          _ = _ := by rw [hupperScale]
      have hpathLaw := measure_rangeInOpenInterval_eq_fullSegmentCorridorEvent
        hP hX lowLower lowUpper
      calc
        shiftedCorridorProbability Q X center (narrowScale a) =
            Q (fullSegmentCorridorEvent X 0 1 lowLower lowUpper) := by
          unfold shiftedCorridorProbability
          rw [hleft, hright]
        _ = P (Skorokhod.rangeInOpenInterval lowLower lowUpper) := hpathLaw.symm
        _ ≤ P (scaledConstantCorridorEvent a lower upper) := by
          apply measure_rangeInOpenInterval_le_constantCorridorEvent hP
          · exact hinnerLower
          · exact hinnerUpper
    have hprobUpper :
        P (scaledConstantCorridorEvent a lower upper) ≤
          shiftedCorridorProbability Q X center (wideScale a) := by
      have hleft : wideScale a * (center - 1) = highLower := by
        dsimp [wideScale, highLower]
        calc
          a * radius * (1 + a) * (center - 1) =
              a * (1 + a) * (radius * (center - 1)) := by ring
          _ = _ := by rw [hlowerScale]
      have hright : wideScale a * (center + 1) = highUpper := by
        dsimp [wideScale, highUpper]
        calc
          a * radius * (1 + a) * (center + 1) =
              a * (1 + a) * (radius * (center + 1)) := by ring
          _ = _ := by rw [hupperScale]
      have hpathLaw := measure_rangeInOpenInterval_eq_fullSegmentCorridorEvent
        hP hX highLower highUpper
      calc
        P (scaledConstantCorridorEvent a lower upper) ≤
            P (Skorokhod.rangeInOpenInterval highLower highUpper) := by
          apply measure_constantCorridorEvent_le_rangeInOpenInterval
          · exact houterLower
          · exact houterUpper
        _ = Q (fullSegmentCorridorEvent X 0 1 highLower highUpper) := hpathLaw
        _ = shiftedCorridorProbability Q X center (wideScale a) := by
          unfold shiftedCorridorProbability
          rw [← hleft, ← hright]
    have hqLower := hqpos (narrowScale a) (by
      dsimp [narrowScale]
      exact mul_pos (mul_pos ha hradius) (by linarith))
    have hqUpper := hqpos (wideScale a) (by
      dsimp [wideScale]
      have ha' : 0 < a := by simpa using ha
      exact mul_pos (mul_pos ha' hradius) (by linarith))
    have hprobLowerReal :
        (shiftedCorridorProbability Q X center (narrowScale a)).toReal ≤
          (P (scaledConstantCorridorEvent a lower upper)).toReal :=
      (ENNReal.toReal_le_toReal (measure_lt_top Q _).ne
        (measure_lt_top P _).ne).mpr hprobLower
    have hpReal : 0 < (P (scaledConstantCorridorEvent a lower upper)).toReal :=
      lt_of_lt_of_le
        (ENNReal.toReal_pos_iff.mpr ⟨hqLower, measure_lt_top Q _⟩)
        hprobLowerReal
    have hprobUpperReal :
        (P (scaledConstantCorridorEvent a lower upper)).toReal ≤
          (shiftedCorridorProbability Q X center (wideScale a)).toReal :=
      (ENNReal.toReal_le_toReal (measure_lt_top P _).ne
        (measure_lt_top Q _).ne).mpr hprobUpper
    have hlogLower := Real.log_le_log
      (ENNReal.toReal_pos_iff.mpr ⟨hqLower, measure_lt_top Q _⟩)
      hprobLowerReal
    have hlogUpper := Real.log_le_log hpReal hprobUpperReal
    obtain ⟨heqLower, heqUpper⟩ := hrateEq a ha ha1
    constructor
    · calc
        narrowRate a = a ^ α * Real.log
            ((shiftedCorridorProbability Q X center (narrowScale a)).toReal) :=
          heqLower.symm
        _ ≤ exactRate a := by
          dsimp [exactRate]
          exact mul_le_mul_of_nonneg_left hlogLower (Real.rpow_nonneg ha.le α)
    · calc
        exactRate a = a ^ α * Real.log
            ((P (scaledConstantCorridorEvent a lower upper)).toReal) := rfl
        _ ≤ a ^ α * Real.log
            ((shiftedCorridorProbability Q X center (wideScale a)).toReal) :=
          mul_le_mul_of_nonneg_left hlogUpper (Real.rpow_nonneg ha.le α)
        _ = wideRate a := heqUpper
  have hlowerLimit' : Tendsto narrowRate l (𝓝 (radius⁻¹ ^ α * C)) := by
    simpa [narrowRate] using hlowerLimit
  have hupperLimit' : Tendsto wideRate l (𝓝 (radius⁻¹ ^ α * C)) := by
    simpa [wideRate] using hupperLimit
  have hboundLower : ∀ᶠ a : ℝ in l, narrowRate a ≤ exactRate a :=
    hbound.mono fun _ h => h.1
  have hboundUpper : ∀ᶠ a : ℝ in l, exactRate a ≤ wideRate a :=
    hbound.mono fun _ h => h.2
  have hexactLimit : Tendsto exactRate l (𝓝 (radius⁻¹ ^ α * C)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hlowerLimit' hupperLimit' hboundLower hboundUpper
  refine ⟨C, hC, ?_⟩
  simpa [exactRate, l, radius, one_div] using hexactLimit

end ProbabilityTheory.Process.SmallDeviation.Mogulskii

end
