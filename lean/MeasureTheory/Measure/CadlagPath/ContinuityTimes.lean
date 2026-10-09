/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import MeasureTheory.MeasurableSpace.CadlagPath
public import Topology.Cadlag.Jump
public import Topology.Cadlag.Skorokhod.Evaluation

/-!
# Deterministic continuity times for càdlàg path laws

This file is intended to show that a probability law on real-valued càdlàg
paths gives full mass to paths continuous at almost every deterministic time.
The proof uses Fubini on the graph of the pathwise discontinuity relation.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open Skorokhod
open scoped Topology

namespace MeasureTheory.CadlagPath

/-- A rational witness that a path has a nonzero jump at an interior time:
arbitrarily close rational times on opposite sides still have separated
values. The relation uses only fixed-time path evaluations, so it is Borel. -/
def rationalSideSeparation :
    Set (CadlagPath unitInterval ℝ × unitInterval) :=
  {z | ∃ n : ℕ, ∀ k : ℕ, ∃ q r : RationalUnitIntervalTime,
    (rationalTimeToUnitInterval q : unitInterval) < z.2 ∧
    z.2 < rationalTimeToUnitInterval r ∧
    dist (rationalTimeToUnitInterval q) z.2 < 1 / ((k + 1 : ℕ) : ℝ) ∧
    dist z.2 (rationalTimeToUnitInterval r) < 1 / ((k + 1 : ℕ) : ℝ) ∧
    1 / ((n + 1 : ℕ) : ℝ) <
      dist (z.1 (rationalTimeToUnitInterval q))
        (z.1 (rationalTimeToUnitInterval r))}

theorem measurableSet_rationalSideSeparation :
    MeasurableSet rationalSideSeparation := by
  unfold rationalSideSeparation
  simp only [Set.ofPred_exists, Set.ofPred_forall]
  refine MeasurableSet.iUnion fun n : ℕ =>
    MeasurableSet.iInter fun k : ℕ =>
      MeasurableSet.iUnion fun q : RationalUnitIntervalTime =>
        MeasurableSet.iUnion fun r : RationalUnitIntervalTime => ?_
  have hq : Measurable fun z : CadlagPath unitInterval ℝ × unitInterval =>
      z.1 (rationalTimeToUnitInterval q) :=
    (measurable_apply _).comp measurable_fst
  have hr : Measurable fun z : CadlagPath unitInterval ℝ × unitInterval =>
      z.1 (rationalTimeToUnitInterval r) :=
    (measurable_apply _).comp measurable_fst
  have hdist : Measurable fun z : CadlagPath unitInterval ℝ × unitInterval =>
      dist (z.1 (rationalTimeToUnitInterval q))
        (z.1 (rationalTimeToUnitInterval r)) := hq.dist hr
  have ht : Measurable fun z : CadlagPath unitInterval ℝ × unitInterval =>
      (z.2 : ℝ) := measurable_subtype_coe.comp measurable_snd
  have hqt : MeasurableSet {z : CadlagPath unitInterval ℝ × unitInterval |
      rationalTimeToUnitInterval q < z.2} := by
    exact (isOpen_Ioi.measurableSet.preimage ht)
  have htr : MeasurableSet {z : CadlagPath unitInterval ℝ × unitInterval |
      z.2 < rationalTimeToUnitInterval r} := by
    exact (isOpen_Iio.measurableSet.preimage ht)
  have hqnear : MeasurableSet {z : CadlagPath unitInterval ℝ × unitInterval |
      dist (rationalTimeToUnitInterval q) z.2 <
        1 / ((k + 1 : ℕ) : ℝ)} := by
    exact (isOpen_Iio.measurableSet.preimage
      ((measurable_const.dist ht)))
  have hrnear : MeasurableSet {z : CadlagPath unitInterval ℝ × unitInterval |
      dist z.2 (rationalTimeToUnitInterval r) <
        1 / ((k + 1 : ℕ) : ℝ)} := by
    exact (isOpen_Iio.measurableSet.preimage
      (ht.dist measurable_const))
  have hsep : MeasurableSet {z : CadlagPath unitInterval ℝ × unitInterval |
      1 / ((n + 1 : ℕ) : ℝ) <
        dist (z.1 (rationalTimeToUnitInterval q))
          (z.1 (rationalTimeToUnitInterval r))} := by
    exact (isOpen_Ioi.measurableSet.preimage hdist)
  simpa only [Set.ofPred_and] using hqt.inter (htr.inter (hqnear.inter (hrnear.inter hsep)))

private theorem rationalSideSeparation_not_continuous
    {path : CadlagPath unitInterval ℝ} {t : unitInterval}
    (hsep : (path, t) ∈ rationalSideSeparation)
    (hcont : ContinuousAt (fun s : unitInterval => path s) t) : False := by
  rcases hsep with ⟨n, hn⟩
  let ε : ℝ := 1 / ((n + 1 : ℕ) : ℝ)
  have hε : 0 < ε := by positivity
  obtain ⟨δ, hδ, hcontrol⟩ :=
    Metric.continuousAt_iff.mp hcont (ε / 3) (by positivity)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  obtain ⟨q, r, hqt, htr, hqclose, hrclose, hfar⟩ := hn k
  have hqδ : dist (rationalTimeToUnitInterval q) t < δ := by
    exact lt_trans hqclose (by simpa [ε] using hk)
  have hrδ : dist (rationalTimeToUnitInterval r) t < δ := by
    have hrclose' : dist (rationalTimeToUnitInterval r) t <
        1 / ((k + 1 : ℕ) : ℝ) := by
      simpa [dist_comm] using hrclose
    exact lt_trans hrclose' (by simpa [ε] using hk)
  have hqval := hcontrol hqδ
  have hrval := hcontrol hrδ
  have hbound : dist
      (path (rationalTimeToUnitInterval q))
      (path (rationalTimeToUnitInterval r)) < ε := by
    calc
      dist (path (rationalTimeToUnitInterval q))
          (path (rationalTimeToUnitInterval r)) ≤
        dist (path (rationalTimeToUnitInterval q)) (path t) +
          dist (path t) (path (rationalTimeToUnitInterval r)) := dist_triangle _ _ _
      _ < ε / 3 + ε / 3 := add_lt_add hqval (by simpa [dist_comm] using hrval)
      _ < ε := by linarith
  exact (lt_irrefl ε) (lt_trans (by simpa [ε] using hfar) hbound)

private theorem leftLim_ne_of_not_continuousAt
    {path : CadlagPath unitInterval ℝ} {t : unitInterval}
    (hbad : ¬ ContinuousAt (fun s : unitInterval => path s) t) :
    Function.leftLim (fun s : unitInterval => path s) t ≠ path t := by
  intro hEq
  have hleft : ContinuousWithinAt (fun s : unitInterval => path s) (Iio t) t := by
    change Tendsto (fun s : unitInterval => path s) (𝓝[<] t) (𝓝 (path t))
    have hlim : Tendsto (fun s : unitInterval => path s) (𝓝[<] t)
        (𝓝 (Function.leftLim (fun s : unitInterval => path s) t)) :=
      tendsto_leftLim_of_tendsto (path.isCadlag_toFun.tendsto_nhdsLT t)
    rw [← hEq]
    exact hlim
  exact hbad (continuousAt_iff_continuous_left'_right'.2
    ⟨hleft, path.isCadlag_toFun.isRightContinuous t⟩)

private theorem exists_rationalSideSequences {t : unitInterval}
    (ht0 : (⊥ : unitInterval) < t) (ht1 : t < ⊤) :
    ∃ q r : ℕ → RationalUnitIntervalTime,
      (∀ n, rationalTimeToUnitInterval (q n) < t) ∧
      (∀ n, t < rationalTimeToUnitInterval (r n)) ∧
      Tendsto (fun n => rationalTimeToUnitInterval (q n)) atTop (𝓝[<] t) ∧
      Tendsto (fun n => rationalTimeToUnitInterval (r n)) atTop (𝓝[>] t) := by
  have ht0' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
  have ht1' : (t : ℝ) < 1 := by exact_mod_cast ht1
  obtain ⟨u, huMono, huLt, huTendsto⟩ :=
    Real.exists_seq_rat_strictMono_tendsto (t : ℝ)
  have huPositive : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (u n : ℝ) :=
    huTendsto.eventually (Ioi_mem_nhds ht0')
  obtain ⟨Nu, hNu⟩ := eventually_atTop.1 huPositive
  let q : ℕ → RationalUnitIntervalTime := fun n =>
    ⟨u (Nu + n), ⟨by
        exact le_of_lt (hNu (Nu + n) (by omega)), by
        exact_mod_cast (huLt (Nu + n)).le.trans ht1'.le⟩⟩
  have huShift : Tendsto (fun n : ℕ => Nu + n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_left n Nu) tendsto_id
  have hqReal : Tendsto (fun n : ℕ => (u (Nu + n) : ℝ)) atTop (𝓝 (t : ℝ)) :=
    huTendsto.comp huShift
  have hqTime : Tendsto (fun n => rationalTimeToUnitInterval (q n)) atTop (𝓝 t) := by
    apply tendsto_subtype_rng.2
    simpa [q, rationalTimeToUnitInterval] using hqReal
  have hqStrict (n : ℕ) : rationalTimeToUnitInterval (q n) < t := by
    change (u (Nu + n) : ℝ) < (t : ℝ)
    exact huLt (Nu + n)
  have hqWithin : Tendsto (fun n => rationalTimeToUnitInterval (q n)) atTop (𝓝[<] t) :=
    tendsto_nhdsWithin_iff.2 ⟨hqTime, Eventually.of_forall hqStrict⟩

  obtain ⟨v, hvAnti, htLt, hvTendsto⟩ :=
    Real.exists_seq_rat_strictAnti_tendsto (t : ℝ)
  have hvBelowOne : ∀ᶠ n : ℕ in atTop, (v n : ℝ) < 1 :=
    hvTendsto.eventually (Iio_mem_nhds ht1')
  obtain ⟨Nv, hNv⟩ := eventually_atTop.1 hvBelowOne
  let r : ℕ → RationalUnitIntervalTime := fun n =>
    ⟨v (Nv + n), ⟨by
        exact_mod_cast ht0'.le.trans (htLt (Nv + n)).le, by
        exact_mod_cast (hNv (Nv + n) (by omega)).le⟩⟩
  have hvShift : Tendsto (fun n : ℕ => Nv + n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_left n Nv) tendsto_id
  have hrReal : Tendsto (fun n : ℕ => (v (Nv + n) : ℝ)) atTop (𝓝 (t : ℝ)) :=
    hvTendsto.comp hvShift
  have hrTime : Tendsto (fun n => rationalTimeToUnitInterval (r n)) atTop (𝓝 t) := by
    apply tendsto_subtype_rng.2
    simpa [r, rationalTimeToUnitInterval] using hrReal
  have hrStrict (n : ℕ) : t < rationalTimeToUnitInterval (r n) := by
    change (t : ℝ) < (v (Nv + n) : ℝ)
    exact htLt (Nv + n)
  have hrWithin : Tendsto (fun n => rationalTimeToUnitInterval (r n)) atTop (𝓝[>] t) :=
    tendsto_nhdsWithin_iff.2 ⟨hrTime, Eventually.of_forall hrStrict⟩
  exact ⟨q, r, hqStrict, hrStrict, hqWithin, hrWithin⟩

private theorem rationalSideSeparation_of_not_continuous
    {path : CadlagPath unitInterval ℝ} {t : unitInterval}
    (ht0 : (⊥ : unitInterval) < t) (ht1 : t < ⊤)
    (hbad : ¬ ContinuousAt (fun s : unitInterval => path s) t) :
    (path, t) ∈ rationalSideSeparation := by
  obtain ⟨q, r, hqside, hrside, hqWithin, hrWithin⟩ :=
    exists_rationalSideSequences ht0 ht1
  let leftValue := Function.leftLim (fun s : unitInterval => path s) t
  have hleftT : Tendsto (fun s : unitInterval => path s) (𝓝[<] t)
      (𝓝 leftValue) := by
    exact tendsto_leftLim_of_tendsto (path.isCadlag_toFun.tendsto_nhdsLT t)
  have hleftSeq : Tendsto (fun n : ℕ =>
      path (rationalTimeToUnitInterval (q n))) atTop (𝓝 leftValue) :=
    hleftT.comp hqWithin
  have hrightT : Tendsto (fun s : unitInterval => path s) (𝓝[>] t)
      (𝓝 (path t)) := path.isCadlag_toFun.isRightContinuous t |>.tendsto
  have hrightSeq : Tendsto (fun n : ℕ =>
      path (rationalTimeToUnitInterval (r n))) atTop (𝓝 (path t)) :=
    hrightT.comp hrWithin
  have hjump : 0 < dist leftValue (path t) :=
    dist_pos.mpr (leftLim_ne_of_not_continuousAt hbad)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hjump)
  let ε : ℝ := 1 / ((n + 1 : ℕ) : ℝ)
  have hε : ε < dist leftValue (path t) / 2 := by
    simpa [ε] using hn
  let η : ℝ := dist leftValue (path t) / 4
  have hη : 0 < η := by positivity
  have hqTime : Tendsto (fun m => rationalTimeToUnitInterval (q m)) atTop (𝓝 t) :=
    (tendsto_nhdsWithin_iff.mp hqWithin).1
  have hrTime : Tendsto (fun m => rationalTimeToUnitInterval (r m)) atTop (𝓝 t) :=
    (tendsto_nhdsWithin_iff.mp hrWithin).1
  refine ⟨n, fun k => ?_⟩
  have hwidth : 0 < (1 / ((k + 1 : ℕ) : ℝ)) := by positivity
  have hqEvent : ∀ᶠ m : ℕ in atTop,
      dist (rationalTimeToUnitInterval (q m)) t <
          1 / ((k + 1 : ℕ) : ℝ) ∧
        dist (path (rationalTimeToUnitInterval (q m))) leftValue < η := by
    filter_upwards
      [hqTime.eventually (Metric.ball_mem_nhds t hwidth),
        hleftSeq.eventually (Metric.ball_mem_nhds leftValue hη)] with m htime hvalue
    exact ⟨Metric.mem_ball.mp htime, Metric.mem_ball.mp hvalue⟩
  have hrEvent : ∀ᶠ m : ℕ in atTop,
      dist (rationalTimeToUnitInterval (r m)) t <
          1 / ((k + 1 : ℕ) : ℝ) ∧
        dist (path (rationalTimeToUnitInterval (r m))) (path t) < η := by
    filter_upwards
      [hrTime.eventually (Metric.ball_mem_nhds t hwidth),
        hrightSeq.eventually (Metric.ball_mem_nhds (path t) hη)] with m htime hvalue
    exact ⟨Metric.mem_ball.mp htime, Metric.mem_ball.mp hvalue⟩
  obtain ⟨mq, hmq⟩ := eventually_atTop.1 hqEvent
  obtain ⟨mr, hmr⟩ := eventually_atTop.1 hrEvent
  have hq := hmq mq le_rfl
  have hr := hmr mr le_rfl
  have hfar : ε < dist
      (path (rationalTimeToUnitInterval (q mq)))
      (path (rationalTimeToUnitInterval (r mr))) := by
    have htri : dist leftValue (path t) ≤
        dist leftValue (path (rationalTimeToUnitInterval (q mq))) +
          dist (path (rationalTimeToUnitInterval (q mq)))
              (path (rationalTimeToUnitInterval (r mr))) +
            dist (path (rationalTimeToUnitInterval (r mr))) (path t) := by
      calc
        dist leftValue (path t) ≤
            dist leftValue (path (rationalTimeToUnitInterval (q mq))) +
              dist (path (rationalTimeToUnitInterval (q mq))) (path t) :=
          dist_triangle _ _ _
        _ ≤ dist leftValue (path (rationalTimeToUnitInterval (q mq))) +
              (dist (path (rationalTimeToUnitInterval (q mq)))
                  (path (rationalTimeToUnitInterval (r mr))) +
                dist (path (rationalTimeToUnitInterval (r mr))) (path t)) := by
          exact add_le_add_right
            (dist_triangle (path (rationalTimeToUnitInterval (q mq)))
              (path (rationalTimeToUnitInterval (r mr))) (path t))
            (dist leftValue (path (rationalTimeToUnitInterval (q mq))))
        _ = dist leftValue (path (rationalTimeToUnitInterval (q mq))) +
              dist (path (rationalTimeToUnitInterval (q mq)))
                (path (rationalTimeToUnitInterval (r mr))) +
              dist (path (rationalTimeToUnitInterval (r mr))) (path t) := by ring
    have hqη : dist leftValue
        (path (rationalTimeToUnitInterval (q mq))) < η := by
      simpa [dist_comm] using hq.2
    dsimp [η] at hqη hr
    linarith [htri, hqη, hr.2, hε]
  exact ⟨q mq, r mr, hqside mq, hrside mr, hq.1,
    by simpa [dist_comm] using hr.1, hfar⟩

/-- At every interior time, rational-side separation is exactly a jump of a
càdlàg path. -/
theorem rationalSideSeparation_iff_not_continuousAt
    {path : CadlagPath unitInterval ℝ} {t : unitInterval}
    (ht0 : (⊥ : unitInterval) < t) (ht1 : t < ⊤) :
    (path, t) ∈ rationalSideSeparation ↔
      ¬ ContinuousAt (fun s : unitInterval => path s) t := by
  constructor
  · intro hsep hcont
    exact rationalSideSeparation_not_continuous hsep hcont
  · exact rationalSideSeparation_of_not_continuous ht0 ht1

private theorem rationalSideSeparation_section_countable
    (path : CadlagPath unitInterval ℝ) :
    {t : unitInterval | (path, t) ∈ rationalSideSeparation}.Countable := by
  apply (path.isCadlag_toFun.countable_discontinuitySet).mono
  intro t ht
  exact rationalSideSeparation_not_continuous ht

private theorem rationalSideSeparation_section_volume_zero
    (path : CadlagPath unitInterval ℝ) :
    volume {t : unitInterval | (path, t) ∈ rationalSideSeparation} = 0 :=
  (rationalSideSeparation_section_countable path).measure_zero volume

/-- For any finite Borel measure on real càdlàg path space, at almost every
deterministic time almost every path is continuous. The proof uses Fubini on
the Borel graph of rational-side separation and the pathwise countability of
càdlàg discontinuities. -/
theorem ae_ae_continuousAt_of_cadlag
    (μ : Measure (CadlagPath unitInterval ℝ)) [IsFiniteMeasure μ] :
    ∀ᵐ t : unitInterval ∂(volume : Measure unitInterval),
      ∀ᵐ path ∂μ, ContinuousAt (fun s : unitInterval => path s) t := by
  let R := rationalSideSeparation
  have hR : MeasurableSet R := measurableSet_rationalSideSeparation
  have hsections : (fun path : CadlagPath unitInterval ℝ =>
      volume (Prod.mk path ⁻¹' R)) =ᵐ[μ] 0 := by
    filter_upwards [] with path
    exact rationalSideSeparation_section_volume_zero path
  have hprod : μ.prod (volume : Measure unitInterval) R = 0 :=
    Measure.measure_prod_null_of_ae_null hR hsections
  let R' : Set (unitInterval × CadlagPath unitInterval ℝ) := Prod.swap ⁻¹' R
  have hR' : MeasurableSet R' := hR.preimage measurable_swap
  have hprod' : (volume : Measure unitInterval).prod μ R' = 0 := by
    rw [← Measure.prod_swap, Measure.map_apply measurable_swap hR']
    simpa [R', Set.preimage_preimage, Function.comp_def] using hprod
  have hfiber : (fun t : unitInterval => μ (Prod.mk t ⁻¹' R')) =ᵐ[
      (volume : Measure unitInterval)] 0 :=
    Measure.measure_ae_null_of_prod_null hprod'
  have hinterior : ∀ᵐ t : unitInterval ∂(volume : Measure unitInterval),
      t ≠ ⊥ ∧ t ≠ ⊤ := by
    rw [ae_iff]
    have hEnds : ({⊥, ⊤} : Set unitInterval).Countable := by
      exact Set.countable_insert.mpr (Set.countable_singleton _)
    have hzero : (volume : Measure unitInterval) ({⊥, ⊤} : Set unitInterval) = 0 :=
      hEnds.measure_zero _
    rw [show {t : unitInterval | ¬ (t ≠ ⊥ ∧ t ≠ ⊤)} =
      ({⊥, ⊤} : Set unitInterval) by
        ext t
        by_cases hbot : t = ⊥ <;> simp [hbot]]
    exact hzero
  have hbad : ∀ᵐ t : unitInterval ∂(volume : Measure unitInterval),
      μ {path : CadlagPath unitInterval ℝ |
        ¬ ContinuousAt (fun s : unitInterval => path s) t} = 0 := by
    filter_upwards [hfiber, hinterior] with t hfiber ht
    have hsection : μ {path : CadlagPath unitInterval ℝ |
        (path, t) ∈ R} = 0 := by
      dsimp only [R'] at hfiber
      change μ {path : CadlagPath unitInterval ℝ | Prod.swap (t, path) ∈ R} = 0 at hfiber
      simpa [Prod.swap] using hfiber
    have ht0 : (⊥ : unitInterval) < t := lt_of_le_of_ne bot_le (Ne.symm ht.1)
    have ht1 : t < ⊤ := lt_of_le_of_ne le_top ht.2
    have hsubset : {path : CadlagPath unitInterval ℝ |
        ¬ ContinuousAt (fun s : unitInterval => path s) t} ⊆
          {path : CadlagPath unitInterval ℝ | (path, t) ∈ R} := by
      intro path hpath
      exact rationalSideSeparation_of_not_continuous ht0 ht1 hpath
    exact le_antisymm (measure_mono hsubset |>.trans_eq hsection)
      bot_le
  filter_upwards [hbad] with t hbad
  rw [ae_iff]
  exact hbad

/-- The deterministic times at which a.e. càdlàg paths are continuous form a
dense subset of the unit interval. -/
theorem dense_ae_continuityTimes_of_cadlag
    (μ : Measure (CadlagPath unitInterval ℝ)) [IsFiniteMeasure μ] :
    Dense {t : unitInterval |
      ∀ᵐ path ∂μ, ContinuousAt (fun s : unitInterval => path s) t} := by
  have hOpenPos : Measure.IsOpenPosMeasure (volume : Measure unitInterval) := by
    refine { open_pos := ?_ }
    intro U hU hne
    obtain ⟨a, b, hab, habU⟩ := hU.exists_Ioo_subset hne
    have hIoo : 0 < (volume : Measure unitInterval) (Ioo a b) := by
      rw [unitInterval.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr (show (a : ℝ) < b from hab))
    exact ne_of_gt (hIoo.trans_le (measure_mono habU))
  exact @Measure.dense_of_ae unitInterval _ _ (volume : Measure unitInterval)
    hOpenPos _ (ae_ae_continuousAt_of_cadlag μ)

end MeasureTheory.CadlagPath

end
