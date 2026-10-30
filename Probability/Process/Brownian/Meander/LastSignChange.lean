/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Meander.LastZeroLaw
public import Probability.Process.Brownian.PathLaw.ContinuousModification
public import Probability.Process.Path.Scaling.FiniteHorizon
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Topology.UnitInterval
public import Topology.ContinuousMap.LastZero
import Probability.Process.Brownian.Meander.LastZero
import Probability.Process.Brownian.Reflection.Path.IntervalMinimum
import Topology.Order.NNReal.Rational
public import Topology.ContinuousMap.LastSignChange

/-!
# The last sign change of a Brownian path

## Public declarations

- `ProbabilityTheory.IsBrownianReal.ae_lastSignChange_eq_lastZero`:
  for a Brownian path on $[0,1]$, Bolthausen's last-sign-change time
  $\tau'$ equals Iglehart's last zero $g$ almost surely.
- `ProbabilityTheory.IsBrownianReal.ae_lastSignChangeMeanderTransform_eq_lastZeroMeanderTransform`:
  Bolthausen's path transform $\Psi(B)$ equals Iglehart's normalized
  terminal Brownian path almost surely.
- `ProbabilityTheory.IsBrownianReal.lastSignChangeMeanderPathLaw_eq_lastZeroMeanderPathLaw`:
  the two resulting probability laws on $C([0,1])$ agree.
- `ProbabilityTheory.IsBrownianReal.ae_continuousAt_lastSignChangeMeanderTransform`:
  $\Psi$ is continuous at almost every Brownian path.
- `ProbabilityTheory.IsBrownianReal.ae_continuousAt_signStableMeanderTransform`:
  Bolthausen's original sign-stable $\Psi$ is continuous at almost
  every Brownian path.
- `ProbabilityTheory.IsBrownianReal.signStableMeanderPathLaw_eq_lastZeroMeanderPathLaw`:
  the original sign-stable transform has Iglehart's terminal-excursion law.

The proof uses atomlessness of interval minima at countably many
rational starts. This identifies the two path transforms appearing on
page 484 and Theorem 3.2 of Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab.
4(3) (1976), 480--485, DOI 10.1214/aop/1176996098, and Section 3, theorem
(3.4), p. 616, of Donald L. Iglehart, *Functional Central Limit Theorems for
Random Walks Conditioned to Stay Positive*, Ann. Probab. 2(4) (1974),
608--619, DOI 10.1214/aop/1176996607.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

private lemma lastSignChange_eq_lastZero_of_intervalMinima
    (f : C(ℝ≥0, ℝ)) (hf0 : f 0 = 0) (hf1 : f 1 ≠ 0)
    (hmin : ∀ q : ℚ≥0, (q : ℝ≥0) < 1 →
      intervalMinimum f ((q : ℝ≥0)) 1 ≠ 0 ∧
      intervalMinimum (-f) ((q : ℝ≥0)) 1 ≠ 0) :
    ContinuousMap.firstNoSignChangeStart (restrictPathToUnitInterval f) =
      ContinuousMap.lastZero (restrictPathToUnitInterval f) := by
  let u := restrictPathToUnitInterval f
  have hu0 : u 0 = 0 := by
    have htime : unitInterval.toNNReal (0 : unitInterval) = 0 := by
      apply NNReal.coe_injective
      rfl
    change f (unitInterval.toNNReal 0) = 0
    rw [htime]
    exact hf0
  have hgzero : u (ContinuousMap.lastZero u) = 0 :=
    ContinuousMap.lastZero_apply_eq_zero u hu0
  have hle : ContinuousMap.firstNoSignChangeStart u ≤
      ContinuousMap.lastZero u := by
    rw [ContinuousMap.firstNoSignChangeStart_eq_lastOppositeSign]
    exact ContinuousMap.lastOppositeSign_le_lastZero u
  apply le_antisymm hle
  by_contra hnot
  have hlt : ContinuousMap.firstNoSignChangeStart u <
      ContinuousMap.lastZero u := lt_of_not_ge hnot
  have hltNN : unitInterval.toNNReal
      (ContinuousMap.firstNoSignChangeStart u) <
        unitInterval.toNNReal (ContinuousMap.lastZero u) := by
    exact_mod_cast hlt
  obtain ⟨q, hτq, hqg⟩ := NNRat.exists_between_nnreal hltNN
  let r := (q : ℝ≥0)
  have hlastBound : unitInterval.toNNReal (ContinuousMap.lastZero u) ≤ 1 := by
    exact_mod_cast (ContinuousMap.lastZero u).property.2
  have hr1 : r < 1 := hqg.trans_le hlastBound
  have hminq := hmin q hr1
  have hzero : f (unitInterval.toNNReal (ContinuousMap.lastZero u)) = 0 :=
    hgzero
  have hminle : intervalMinimum f r 1 ≤ 0 := by
    rw [← hzero]
    exact intervalMinimum_le f hqg.le hlastBound
  have hnegminle : intervalMinimum (-f) r 1 ≤ 0 := by
    rw [← neg_zero, ← hzero]
    exact intervalMinimum_le (-f) hqg.le hlastBound
  have hsign {t : ℝ≥0} (hrt : r ≤ t) (ht1 : t ≤ 1) :
      0 ≤ f t * f 1 := by
    let s : unitInterval := ⟨(t : ℝ), ⟨t.property, by exact_mod_cast ht1⟩⟩
    have hsTime : unitInterval.toNNReal s = t := by
      apply NNReal.coe_injective
      rfl
    have hτs : ContinuousMap.firstNoSignChangeStart u < s := by
      change (ContinuousMap.firstNoSignChangeStart u : ℝ) < (t : ℝ)
      exact_mod_cast hτq.trans_le hrt
    have hnotOpp : ¬ u s * u ⊤ < 0 := by
      intro hneg
      have hsle : s ≤ ContinuousMap.firstNoSignChangeStart u := by
        rw [ContinuousMap.firstNoSignChangeStart_eq_lastOppositeSign]
        exact le_sSup hneg
      exact (not_le_of_gt hτs) hsle
    have hnonneg : 0 ≤ u s * u ⊤ := le_of_not_gt hnotOpp
    have htop : unitInterval.toNNReal ⊤ = 1 := unitInterval.toNNReal_one
    simpa [u, restrictPathToUnitInterval, hsTime, htop] using hnonneg
  rcases lt_or_gt_of_ne hf1 with hf1neg | hf1pos
  · obtain ⟨t, hrt, ht1, hvalue⟩ :=
      exists_intervalMinimum_eq (-f) hr1.le
    have hprod := hsign hrt ht1
    have hnonneg : 0 ≤ -f t := by nlinarith
    have hminnonneg : 0 ≤ intervalMinimum (-f) r 1 := by
      rw [← hvalue]
      exact hnonneg
    exact hminq.2 (le_antisymm hnegminle hminnonneg)
  · obtain ⟨t, hrt, ht1, hvalue⟩ :=
      exists_intervalMinimum_eq f hr1.le
    have hprod := hsign hrt ht1
    have hnonneg : 0 ≤ f t := by nlinarith
    have hminnonneg : 0 ≤ intervalMinimum f r 1 := by
      rw [← hvalue]
      exact hnonneg
    exact hminq.1 (le_antisymm hminle hminnonneg)

/-- The first tail of fixed sign starts at the last zero before one,
almost surely for Brownian motion. -/
theorem IsBrownianReal.ae_lastSignChange_eq_lastZero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t)) :
    ∀ᵐ ω ∂P,
      ContinuousMap.firstNoSignChangeStart
          (restrictPathToUnitInterval
            (hB.continuousPathMap hmeasurable ω)) =
        ContinuousMap.lastZero
          (restrictPathToUnitInterval
            (hB.continuousPathMap hmeasurable ω)) := by
  let pathB := hB.continuousPathMap hmeasurable
  have hpath : Measurable pathB :=
    hB.measurable_continuousPathMap hmeasurable
  have hfixed (q : ℚ≥0) :
      ∀ᵐ ω ∂P, (q : ℝ≥0) < 1 →
        intervalMinimum (pathB ω) ((q : ℝ≥0)) 1 ≠ 0 ∧
        intervalMinimum (-(pathB ω)) ((q : ℝ≥0)) 1 ≠ 0 := by
    let r := (q : ℝ≥0)
    by_cases hr1 : r < 1
    · have hset : MeasurableSet
          {f : C(ℝ≥0, ℝ) | intervalMinimum f r 1 = 0} :=
        (measurable_intervalMinimum r 1) (measurableSet_singleton 0)
      have hsetNeg : MeasurableSet
          {f : C(ℝ≥0, ℝ) | intervalMinimum (-f) r 1 = 0} :=
        (measurable_intervalMinimum r 1).comp continuous_neg.measurable
          (measurableSet_singleton 0)
      have hnull := hB.measure_intervalMinimum_eq hmeasurable hr1 0
      change (P.map pathB)
        {f : C(ℝ≥0, ℝ) | intervalMinimum f r 1 = 0} = 0 at hnull
      rw [Measure.map_apply hpath hset] at hnull
      have hnullNeg := hB.measure_negIntervalMinimum_eq hmeasurable hr1 0
      change (P.map pathB)
        {f : C(ℝ≥0, ℝ) | intervalMinimum (-f) r 1 = 0} = 0 at hnullNeg
      rw [Measure.map_apply hpath hsetNeg] at hnullNeg
      have hae : ∀ᵐ ω ∂P, intervalMinimum (pathB ω) r 1 ≠ 0 := by
        apply (ae_iff).mpr
        simpa using hnull
      have haeNeg : ∀ᵐ ω ∂P, intervalMinimum (-(pathB ω)) r 1 ≠ 0 := by
        apply (ae_iff).mpr
        simpa using hnullNeg
      filter_upwards [hae, haeNeg] with ω hω hωNeg
      exact fun _ => ⟨hω, hωNeg⟩
    · exact Filter.Eventually.of_forall fun _ h => (hr1 h).elim
  have hall : ∀ᵐ ω ∂P, ∀ q : ℚ≥0,
      (q : ℝ≥0) < 1 →
        intervalMinimum (pathB ω) ((q : ℝ≥0)) 1 ≠ 0 ∧
        intervalMinimum (-(pathB ω)) ((q : ℝ≥0)) 1 ≠ 0 :=
    ae_all_iff.mpr hfixed
  have hend : ∀ᵐ ω ∂P, B 1 ω ≠ 0 := by
    exact (hB.hasLaw_eval 1).ae_iff
      (measurableSet_setOfPred.1 (by
        convert (measurableSet_singleton (0 : ℝ)).compl using 1
        ext x
        simp)) |>.2
      (@Measure.ae_ne ℝ _ (gaussianReal 0 1)
        (nullSingletonClass_gaussianReal (by norm_num)) 0)
  filter_upwards [hall, hB.continuousPathMap_ae_eq hmeasurable,
    hB.eval_zero_ae_eq_zero, hend] with ω hω hpathω hzero hendω
  apply lastSignChange_eq_lastZero_of_intervalMinima (pathB ω)
  · rw [hpathω]
    exact hzero
  · rw [hpathω]
    exact hendω
  · exact hω

/-- Bolthausen's last-sign-change transform and Iglehart's last-zero
transform agree almost surely for Brownian paths. -/
theorem IsBrownianReal.ae_lastSignChangeMeanderTransform_eq_lastZeroMeanderTransform
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t)) :
    (fun ω => ContinuousMap.lastSignChangeMeanderTransform
      (restrictPathToUnitInterval
        (hB.continuousPathMap hmeasurable ω))) =ᵐ[P]
      hB.lastZeroMeanderPath hmeasurable := by
  filter_upwards [hB.ae_lastSignChange_eq_lastZero hmeasurable]
    with ω hω
  simp only [ContinuousMap.lastSignChangeMeanderTransform,
    IsBrownianReal.lastZeroMeanderPath,
    ContinuousMap.lastZeroMeanderTransform, hω]

/-- The path laws obtained from Bolthausen's and Iglehart's terminal
path transforms agree. -/
theorem IsBrownianReal.lastSignChangeMeanderPathLaw_eq_lastZeroMeanderPathLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t)) :
    P.map (fun ω => ContinuousMap.lastSignChangeMeanderTransform
      (restrictPathToUnitInterval
        (hB.continuousPathMap hmeasurable ω))) =
      hB.lastZeroMeanderPathLaw hmeasurable := by
  rw [IsBrownianReal.lastZeroMeanderPathLaw]
  exact Measure.map_congr
    (hB.ae_lastSignChangeMeanderTransform_eq_lastZeroMeanderTransform
      hmeasurable)

/-- Bolthausen's last-sign-change meander transform is continuous at
almost every Brownian path, since its last sign change and last zero
agree almost surely and the Brownian endpoint is nonzero almost surely. -/
theorem IsBrownianReal.ae_continuousAt_lastSignChangeMeanderTransform
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t)) :
    ∀ᵐ ω ∂P, ContinuousAt ContinuousMap.lastSignChangeMeanderTransform
      (restrictPathToUnitInterval
        (hB.continuousPathMap hmeasurable ω)) := by
  filter_upwards [hB.ae_lastSignChange_eq_lastZero hmeasurable,
    hB.ae_lastZero_restrictPathToUnitInterval_lt_top hmeasurable]
    with ω heq hlt
  exact ContinuousMap.continuousAt_lastSignChangeMeanderTransform_of_eq_lastZero
    _ heq hlt

/-- Bolthausen's original sign-stable transform agrees locally with the
endpoint-sign transform at every Brownian path whose endpoint is nonzero.
It is therefore continuous almost surely, as asserted on page 484 of Erwin
Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Theorem 3.2, Ann. Probab. 4(3) (1976),
480--485, DOI 10.1214/aop/1176996098. -/
theorem IsBrownianReal.ae_continuousAt_signStableMeanderTransform
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t)) :
    ∀ᵐ ω ∂P, ContinuousAt ContinuousMap.signStableMeanderTransform
      (restrictPathToUnitInterval
        (hB.continuousPathMap hmeasurable ω)) := by
  filter_upwards [hB.ae_continuousAt_lastSignChangeMeanderTransform hmeasurable,
    hB.ae_lastZero_restrictPathToUnitInterval_lt_top hmeasurable]
    with ω hcont hlt
  let f := restrictPathToUnitInterval
    (hB.continuousPathMap hmeasurable ω)
  have hend : f ⊤ ≠ 0 := by
    intro hzero
    exact (not_le_of_gt hlt)
      (ContinuousMap.le_lastZero_of_apply_eq_zero f hzero)
  have hevent : ∀ᶠ g in nhds f, g ⊤ ≠ 0 := by
    have hopen : IsOpen {g : C(unitInterval, ℝ) | g ⊤ ≠ 0} :=
      (isClosed_singleton.isOpen_compl).preimage
        (continuous_eval_const ⊤)
    exact hopen.mem_nhds hend
  apply hcont.congr
  filter_upwards [hevent] with g hg
  exact (ContinuousMap.signStableMeanderTransform_eq_lastSignChangeMeanderTransform
    g hg).symm

/-- Bolthausen's original sign-stable transform and Iglehart's
last-zero transform induce the same Brownian path law. -/
theorem IsBrownianReal.signStableMeanderPathLaw_eq_lastZeroMeanderPathLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t)) :
    P.map (fun ω => ContinuousMap.signStableMeanderTransform
      (restrictPathToUnitInterval
        (hB.continuousPathMap hmeasurable ω))) =
      hB.lastZeroMeanderPathLaw hmeasurable := by
  calc
    P.map (fun ω => ContinuousMap.signStableMeanderTransform
        (restrictPathToUnitInterval
          (hB.continuousPathMap hmeasurable ω))) =
      P.map (fun ω => ContinuousMap.lastSignChangeMeanderTransform
        (restrictPathToUnitInterval
          (hB.continuousPathMap hmeasurable ω))) := by
        apply Measure.map_congr
        filter_upwards [hB.ae_lastZero_restrictPathToUnitInterval_lt_top
          hmeasurable] with ω hlt
        let f := restrictPathToUnitInterval
          (hB.continuousPathMap hmeasurable ω)
        have hend : f ⊤ ≠ 0 := by
          intro hzero
          exact (not_le_of_gt hlt)
            (ContinuousMap.le_lastZero_of_apply_eq_zero f hzero)
        exact ContinuousMap.signStableMeanderTransform_eq_lastSignChangeMeanderTransform
          f hend
    _ = hB.lastZeroMeanderPathLaw hmeasurable :=
      hB.lastSignChangeMeanderPathLaw_eq_lastZeroMeanderPathLaw hmeasurable

end ProbabilityTheory

end
