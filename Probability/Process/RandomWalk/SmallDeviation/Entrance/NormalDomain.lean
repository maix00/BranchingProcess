/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.CyclicPath
public import Probability.Process.RandomWalk.SmallDeviation.Entrance.FunctionalLimit
public import Probability.Process.RandomWalk.FunctionalLimit.Normal.Tightness
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.ProcessExistence

/-!
# Normal-domain entrance lower bound

This file transfers the normal-domain functional limit to the first
diffusive-time entrance event. The source path is normalized by
`sigma * sqrt n`, while the moving corridor is normalized by `Delta`; a
spatial-scaling estimate in the J₁ topology accounts for their ratio.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The finite-step entrance event in the original moving corridor. Time is
normalized to `[0,1]`; `drift` is the boundary displacement per step in these
spatial units, and the endpoint window is the central third of the corridor. -/
def finiteMovingEntranceEvent {n : ℕ} (scale drift u : ℝ) :
    Set (Fin n → ℝ) :=
  {x | (∀ j : Fin (n + 1),
      finiteNormalizedStepKnots scale x j ∈
        Set.Icc (-u + drift * (j.val : ℝ))
          (1 - u + drift * (j.val : ℝ))) ∧
    finiteNormalizedStepKnots scale x (Fin.last n) ∈
      Set.Icc (1 / 3 - u + drift * (n : ℝ))
        (2 / 3 - u + drift * (n : ℝ))}

/-- Subtracting the linear boundary drift identifies the static rotated
corridor event with the original moving entrance event, including its
time-`n` central endpoint window. -/
theorem finiteDriftRemovedOffsetCorridorEvent_iff_finiteMovingEntranceEvent
    {n : ℕ} (scale drift u : ℝ) (x : Fin n → ℝ) :
    x ∈ finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u ↔
      x ∈ finiteMovingEntranceEvent (n := n) scale drift u := by
  change offsetCorridorPath u
      (removeLinearDrift drift (finiteNormalizedStepKnots scale x)) ↔ _
  unfold offsetCorridorPath removeLinearDrift finiteMovingEntranceEvent
  have hlastVal : ((Fin.last n).val : ℝ) = (n : ℝ) := by simp
  constructor
  · rintro ⟨hpath, hend⟩
    refine ⟨fun j => ?_, ?_⟩
    · rcases Set.mem_Icc.mp (hpath j) with ⟨hlo, hhi⟩
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    · rcases Set.mem_Icc.mp hend with ⟨hlo, hhi⟩
      rw [hlastVal] at hlo hhi
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  · rintro ⟨hpath, hend⟩
    refine ⟨fun j => ?_, ?_⟩
    · rcases Set.mem_Icc.mp (hpath j) with ⟨hlo, hhi⟩
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    · rcases Set.mem_Icc.mp hend with ⟨hlo, hhi⟩
      rw [hlastVal]
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩

/-- A uniform linear-ball lower bound on all slopes needed by the offset
rotation yields the factor-`n` lower bound for every offset in the corridor. -/
theorem measure_pi_finiteMovingEntranceEvent_ge_div_of_uniformLinearBall
    {n : ℕ} (hn : 0 < n) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (targetScale sourceScale ratio drift radius bound : ℝ)
    (htargetScale : targetScale ≠ 0) (hsourceScale : sourceScale ≠ 0)
    (hratio : ratio = sourceScale / targetScale)
    (hratioPos : 0 < ratio) (hradius : 0 < radius)
    (hsmall : 2 * (max 1 |ratio| * radius) +
      |drift| * (n : ℝ) < 1 / 16)
    (hboundRatio : 1 / 2 ≤ bound * ratio)
    (rotate : Fin n → Fin n ≃ Fin n)
    (hrotate : IsCyclicPartialSumReindex rotate)
    {q : ℝ≥0∞}
    (hq : ∀ slope ∈ Set.Icc (-bound) bound,
      q ≤ iidSequenceLaw ν
        {x | RandomWalk.normalizedStepCadlagPathIcc
          (fun _ => sourceScale) n x ∈
            Metric.ball (Skorokhod.linearPath slope) radius}) :
    ∀ u ∈ Set.Icc 0 1,
      q / n ≤ Measure.pi (fun _ : Fin n => ν)
        (finiteMovingEntranceEvent (n := n) targetScale drift u) := by
  intro u hu
  have hm : |1 / 2 - u| ≤ 1 / 2 := by
    rw [abs_le]
    have hucopy := hu
    rcases hucopy with ⟨hu0, hu1⟩
    constructor <;> linarith
  have hsourceSlope : |(1 / 2 - u) / ratio| ≤ bound := by
    rw [abs_div, abs_of_pos hratioPos]
    apply (div_le_iff₀ hratioPos).2
    calc
      |1 / 2 - u| ≤ 1 / 2 := hm
      _ ≤ bound * ratio := hboundRatio
  have hsourceMem : (1 / 2 - u) / ratio ∈ Set.Icc (-bound) bound := by
    change -bound ≤ (1 / 2 - u) / ratio ∧
      (1 / 2 - u) / ratio ≤ bound
    exact abs_le.mp hsourceSlope
  have hsafe : MeasurableSet
      (finiteDriftRemovedOffsetCorridorEvent (n := n) targetScale drift u) :=
    measurableSet_finiteDriftRemovedOffsetCorridorEvent targetScale drift u
  have hqsource := hq ((1 / 2 - u) / ratio) hsourceMem
  have hcenter : ratio * ((1 / 2 - u) / ratio) = 1 / 2 - u := by
    field_simp [hratioPos.ne']
  have hremoved :=
    measure_pi_offsetCorridor_ge_div_of_linearTube_allOffsets_of_normalizationRatio
      hn ν targetScale sourceScale ratio drift ((1 / 2 - u) / ratio)
      radius u htargetScale hsourceScale hratio hcenter hradius hsmall hu
      rotate hrotate hsafe hqsource
  have hevent : finiteDriftRemovedOffsetCorridorEvent
      (n := n) targetScale drift u =
        finiteMovingEntranceEvent (n := n) targetScale drift u := by
    ext x
    exact finiteDriftRemovedOffsetCorridorEvent_iff_finiteMovingEntranceEvent
      targetScale drift u x
  rw [← hevent]
  exact hremoved

/-- The normal-domain entrance estimate with `n = floor (Delta²)` and the
source normalization `sigma * sqrt n`. The constant `q` is independent of
the initial point `r₀`; the raw corridor offset is `u = -r₀ / Delta`. The
standard Gaussian clock-process law is constructed internally from the
normalized source by the normal-domain tightness and functional-limit theorem. -/
theorem exists_eventually_measure_pi_finiteMovingEntranceEvent_ge_div_of_centeredSecondMoment
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∃ Delta₀ : ℝ, ∀ Delta ≥ Delta₀,
      ∀ r₀ ∈ Set.Icc (-Delta) 0,
        q / (⌊Delta ^ 2⌋₊ : ℕ) ≤
          Measure.pi (fun _ : Fin (⌊Delta ^ 2⌋₊ : ℕ) => ν)
            (finiteMovingEntranceEvent (n := ⌊Delta ^ 2⌋₊)
              Delta (c / Delta ^ 3) (-r₀ / Delta)) := by
  let bound : ℝ := sigma⁻¹
  let radius : ℝ := 1 / (128 * max 1 sigma)
  let νunit := ν.map (fun x => x / sigma)
  have hνunit : IsCenteredUnitSecondMoment νunit := hν.map_div hsigma
  have hsquare : Integrable (fun x : ℝ => x ^ 2) νunit := by
    apply (memLp_two_iff_integrable_sq
      stronglyMeasurable_id.aestronglyMeasurable).1
    exact IsCenteredUnitSecondMoment.memLp_two hνunit
  have hunitDOA' :=
    isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_integrable_sq
      νunit hνunit.1 hsquare (by rw [hνunit.2]; norm_num)
  have hunitDOA : IsInDomainOfAttractionAlong νunit (gaussianReal 0 1)
      (fun n => Real.sqrt n) (fun _ => 0) := by
    simpa [hνunit.2] using hunitDOA'
  have hnormalization : ∀ n : ℕ, 0 < n → 0 < Real.sqrt (n : ℝ) := by
    intro n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  have htight :=
    RandomWalk.FunctionalLimit.Normal.isTightMeasureSet_range_normalizedStepPathLaw_of_gaussian
      hunitDOA hnormalization
  have hstable : IsStrictlyAlphaStable 2 (gaussianReal 0 1) :=
    isStrictlyAlphaStable_gaussianReal_zero (v := 1) (by norm_num)
  obtain ⟨P, hP, _sub, _strict, _limit⟩ :=
    RandomWalk.FunctionalLimit.Stable.exists_stableClockProcessLaw_of_tightSource
      hunitDOA hstable htight
  have hbound : 0 < bound := by dsimp [bound]; positivity
  have hradius : 0 < radius := by dsimp [radius]; positivity
  obtain ⟨q, hqpos, hqevent⟩ :=
    eventually_measure_normalizedStep_linearBall_pos_on_Icc_of_centeredSecondMoment
      hν hsigma hP bound radius hbound hradius
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hqevent
  refine ⟨q, hqpos, max (max 2 (Real.sqrt (N : ℝ) + 1)) (64 * c + 1), ?_⟩
  intro Delta hDelta r₀ hr₀
  let n : ℕ := ⌊Delta ^ 2⌋₊
  have hDeltaAtLeastTwo : 2 ≤ Delta :=
    (le_max_left 2 (Real.sqrt (N : ℝ) + 1)).trans <|
      (le_max_left (max 2 (Real.sqrt (N : ℝ) + 1)) (64 * c + 1)).trans hDelta
  have hDelta2 : 0 < Delta := by
    linarith
  have hnpos : 0 < n := by
    have hn1 : 1 ≤ n := by
      dsimp [n]
      rw [Nat.one_le_floor_iff]
      nlinarith [hDeltaAtLeastTwo]
    omega
  have hnFloorLower : (N : ℝ) ≤ Delta ^ 2 := by
    have hlarge : Real.sqrt (N : ℝ) + 1 ≤ Delta :=
      (le_max_right 2 (Real.sqrt (N : ℝ) + 1)).trans <|
        (le_max_left (max 2 (Real.sqrt (N : ℝ) + 1))
          (64 * c + 1)).trans hDelta
    have hsqrtN : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    have hsquare : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := by
      rw [Real.sq_sqrt (Nat.cast_nonneg N)]
    nlinarith
  have hnLarge : N ≤ n := by
    dsimp [n]
    rw [Nat.le_floor_iff (show 0 ≤ Delta ^ 2 by positivity)]
    exact hnFloorLower
  have hncastUpper : (n : ℝ) ≤ Delta ^ 2 := by
    dsimp [n]
    exact Nat.floor_le (by positivity)
  have hncastLower : Delta ^ 2 / 4 ≤ (n : ℝ) := by
    dsimp [n]
    have hfloor : Delta ^ 2 < (⌊Delta ^ 2⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hDeltaSq : 2 ≤ Delta ^ 2 := by nlinarith [hDelta2]
    nlinarith
  have hrootLower : Delta / 2 ≤ Real.sqrt (n : ℝ) := by
    apply (sq_le_sq₀ (by positivity : 0 ≤ Delta / 2)
      (Real.sqrt_nonneg _)).1
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    nlinarith [hncastLower]
  have hrootUpper : Real.sqrt (n : ℝ) ≤ Delta := by
    calc
      Real.sqrt (n : ℝ) ≤ Real.sqrt (Delta ^ 2) :=
        Real.sqrt_le_sqrt hncastUpper
      _ = Delta := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hDelta2]
  let sourceScale : ℝ := sigma * Real.sqrt (n : ℝ)
  let ratio : ℝ := sourceScale / Delta
  have hsourceScale : 0 < sourceScale := by
    dsimp [sourceScale]
    exact mul_pos hsigma (Real.sqrt_pos.2 (by exact_mod_cast hnpos))
  have hratioPos : 0 < ratio := div_pos hsourceScale hDelta2
  have hratioLower : sigma / 2 ≤ ratio := by
    dsimp [ratio, sourceScale]
    apply (le_div_iff₀ hDelta2).2
    nlinarith [mul_le_mul_of_nonneg_left hrootLower hsigma.le]
  have hratioUpper : ratio ≤ sigma := by
    dsimp [ratio, sourceScale]
    apply (div_le_iff₀ hDelta2).2
    nlinarith [mul_le_mul_of_nonneg_left hrootUpper hsigma.le]
  have hu : -r₀ / Delta ∈ Set.Icc 0 1 := by
    rcases hr₀ with ⟨hr₀lower, hr₀upper⟩
    constructor
    · exact div_nonneg (by linarith) hDelta2.le
    · exact (div_le_iff₀ hDelta2).2 (by linarith)
  have htargetRadius :
      max 1 |ratio| * radius ≤ 1 / 128 := by
    have hmax : max 1 |ratio| ≤ max 1 sigma := by
      apply max_le_max le_rfl
      simpa [abs_of_pos hratioPos] using hratioUpper
    dsimp [radius]
    calc
      max 1 |ratio| * (1 / (128 * max 1 sigma)) ≤
          max 1 sigma * (1 / (128 * max 1 sigma)) :=
        mul_le_mul_of_nonneg_right hmax (by positivity)
      _ = 1 / 128 := by
        field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
  have hdriftBound : |c / Delta ^ 3| * (n : ℝ) ≤ c / Delta := by
    have hdrift : |c / Delta ^ 3| = c / Delta ^ 3 :=
      abs_of_nonneg (div_nonneg hc (by positivity))
    rw [hdrift]
    calc
      c / Delta ^ 3 * (n : ℝ) ≤ c / Delta ^ 3 * Delta ^ 2 :=
        mul_le_mul_of_nonneg_left hncastUpper (by positivity)
      _ = c / Delta := by
        field_simp [ne_of_gt hDelta2]
  have hcDelta : c / Delta < 1 / 64 := by
    have hDeltaLarge : 64 * c + 1 ≤ Delta := by
      have hmax := le_trans (le_max_right (max 2 (Real.sqrt (N : ℝ) + 1))
        (64 * c + 1)) hDelta
      exact hmax
    apply (div_lt_iff₀ hDelta2).2
    nlinarith
  have hsmall : 2 * (max 1 |ratio| * radius) +
      |c / Delta ^ 3| * (n : ℝ) < 1 / 16 := by
    calc
      2 * (max 1 |ratio| * radius) +
          |c / Delta ^ 3| * (n : ℝ) ≤ 2 * (1 / 128) + c / Delta :=
        add_le_add (mul_le_mul_of_nonneg_left htargetRadius (by norm_num))
          hdriftBound
      _ < 1 / 64 + 1 / 64 := by nlinarith [hcDelta]
      _ < 1 / 16 := by norm_num
  let sourceSlope : ℝ := (1 / 2 - (-r₀ / Delta)) / ratio
  have hsourceSlopeBound : |sourceSlope| ≤ bound := by
    change |(1 / 2 - (-r₀ / Delta)) / ratio| ≤ sigma⁻¹
    rw [abs_div, abs_of_pos hratioPos]
    apply (div_le_iff₀ hratioPos).2
    have htarget : |1 / 2 - (-r₀ / Delta)| ≤ 1 / 2 := by
      have hucopy := hu
      rcases hucopy with ⟨hu0, hu1⟩
      rw [abs_le]
      constructor <;> linarith
    calc
      |1 / 2 - (-r₀ / Delta)| ≤ 1 / 2 := htarget
      _ ≤ sigma⁻¹ * ratio := by
        calc
          (1 : ℝ) / 2 = sigma⁻¹ * (sigma / 2) := by
            field_simp [hsigma.ne']
          _ ≤ sigma⁻¹ * ratio :=
            mul_le_mul_of_nonneg_left hratioLower (by positivity)
  have hboundRatio : 1 / 2 ≤ bound * ratio := by
    dsimp [bound]
    calc
      (1 : ℝ) / 2 = sigma⁻¹ * (sigma / 2) := by
        field_simp [hsigma.ne']
      _ ≤ sigma⁻¹ * ratio :=
        mul_le_mul_of_nonneg_left hratioLower (by positivity)
  have hsourceSlopeMem : sourceSlope ∈ Set.Icc (-bound) bound := by
    change -bound ≤ sourceSlope ∧ sourceSlope ≤ bound
    exact abs_le.mp hsourceSlopeBound
  have hqsource : q ≤ iidSequenceLaw ν
      {x | RandomWalk.normalizedStepCadlagPathIcc
        (fun _ => sourceScale) n x ∈
          Metric.ball (Skorokhod.linearPath sourceSlope) radius} := by
    have hqstrict := hN n hnLarge
    have hq := hqstrict sourceSlope hsourceSlopeMem
    simpa [sourceScale, n] using hq.le
  have hratio : ratio = sourceScale / Delta := rfl
  have hcenter : ratio * sourceSlope = 1 / 2 - (-r₀ / Delta) := by
    change ratio * ((1 / 2 - (-r₀ / Delta)) / ratio) = _
    field_simp [hratioPos.ne']
  have hsafe : MeasurableSet
      (finiteDriftRemovedOffsetCorridorEvent (n := n)
        Delta (c / Delta ^ 3) (-r₀ / Delta)) :=
    measurableSet_finiteDriftRemovedOffsetCorridorEvent _ _ _
  have hmeasure :=
    measure_pi_offsetCorridor_ge_div_of_linearTube_allOffsets_of_normalizationRatio
      hnpos ν Delta sourceScale ratio (c / Delta ^ 3) sourceSlope radius
      (-r₀ / Delta) (by positivity) (ne_of_gt hsourceScale) hratio hcenter
      hradius hsmall hu (fun k => cyclicCoordinateReindex hnpos k)
      (cyclicCoordinateReindex_isCyclicPartialSumReindex hnpos) hsafe hqsource
  have hevent : finiteDriftRemovedOffsetCorridorEvent
      (n := n) Delta (c / Delta ^ 3) (-r₀ / Delta) =
        finiteMovingEntranceEvent (n := n) Delta (c / Delta ^ 3)
          (-r₀ / Delta) := by
    ext x
    exact finiteDriftRemovedOffsetCorridorEvent_iff_finiteMovingEntranceEvent
      Delta (c / Delta ^ 3) (-r₀ / Delta) x
  rw [hevent] at hmeasure
  simpa [n] using hmeasure

/-- The same first-block lower bound under the canonical infinite IID sequence
law. The event depends only on the first `floor (Delta²)` coordinates, so its
probability is the finite-product probability proved above. -/
theorem exists_eventually_iidSequenceLaw_finiteMovingEntranceEvent_ge_div_of_centeredSecondMoment
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∃ Delta₀ : ℝ, ∀ Delta ≥ Delta₀,
      ∀ r₀ ∈ Set.Icc (-Delta) 0,
        q / (⌊Delta ^ 2⌋₊ : ℕ) ≤
          iidSequenceLaw ν
            {increment | finitePrefixVector
              (n := ⌊Delta ^ 2⌋₊) increment ∈
                finiteMovingEntranceEvent (n := ⌊Delta ^ 2⌋₊)
                  Delta (c / Delta ^ 3) (-r₀ / Delta)} := by
  obtain ⟨q, hq, Delta₀, hbound⟩ :=
    exists_eventually_measure_pi_finiteMovingEntranceEvent_ge_div_of_centeredSecondMoment
      hν hsigma c hc
  refine ⟨q, hq, Delta₀, ?_⟩
  intro Delta hDelta r₀ hr₀
  let n : ℕ := ⌊Delta ^ 2⌋₊
  have hsafe : MeasurableSet
      (finiteDriftRemovedOffsetCorridorEvent (n := n)
        Delta (c / Delta ^ 3) (-r₀ / Delta)) :=
    measurableSet_finiteDriftRemovedOffsetCorridorEvent _ _ _
  have hevent : finiteDriftRemovedOffsetCorridorEvent
      (n := n) Delta (c / Delta ^ 3) (-r₀ / Delta) =
        finiteMovingEntranceEvent (n := n) Delta (c / Delta ^ 3)
          (-r₀ / Delta) := by
    ext x
    exact finiteDriftRemovedOffsetCorridorEvent_iff_finiteMovingEntranceEvent
      Delta (c / Delta ^ 3) (-r₀ / Delta) x
  have hmeasurable : MeasurableSet
      (finiteMovingEntranceEvent (n := n) Delta (c / Delta ^ 3)
        (-r₀ / Delta)) := by
    rw [← hevent]
    exact hsafe
  have hprefix := iidSequenceLaw_measure_finitePrefix_preimage_eq_pi ν
    (finiteMovingEntranceEvent (n := n) Delta (c / Delta ^ 3)
      (-r₀ / Delta)) hmeasurable
  have hpi := hbound Delta hDelta r₀ hr₀
  change q / (n : ℝ≥0∞) ≤ iidSequenceLaw ν
    (finitePrefixVector (n := n) ⁻¹'
      finiteMovingEntranceEvent (n := n) Delta (c / Delta ^ 3)
        (-r₀ / Delta))
  rw [hprefix]
  simpa [n] using hpi

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
