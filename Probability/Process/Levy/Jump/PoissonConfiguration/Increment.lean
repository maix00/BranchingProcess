/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.Levy.Jump.PoissonConfiguration.Endpoint
import Probability.Process.Levy.Jump.Intensity.Cutoff
import Probability.Process.Levy.Jump.Campbell.FiniteActivity

/-!
# Increments of an uncompensated jump path

For a fixed realized point measure, subtracting two cumulative jump
integrals is exactly the integral over the half-open time window between
them. The integrability hypothesis is pathwise and does not assert a global
first moment for the underlying Lévy law.
-/

namespace ProbabilityTheory

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem integral_jumpPath_sub_eq_timeWindow
    (m : Measure (unitInterval × ℝ))
    (hm : Integrable (fun z : unitInterval × ℝ => z.2) m)
    (s t : unitInterval) (hst : s ≤ t) :
    (∫ z, (if z.1 ≤ t then z.2 else 0 : ℝ) ∂m) -
      (∫ z, (if z.1 ≤ s then z.2 else 0 : ℝ) ∂m) =
    ∫ z, (if s < z.1 ∧ z.1 ≤ t then z.2 else 0 : ℝ) ∂m := by
  have ht : Integrable (fun z : unitInterval × ℝ =>
      if z.1 ≤ t then z.2 else 0) m :=
    hm.indicator (measurableSet_le
      (by fun_prop : Measurable fun z : unitInterval × ℝ => (z.1 : ℝ)) measurable_const)
  have hs : Integrable (fun z : unitInterval × ℝ =>
      if z.1 ≤ s then z.2 else 0) m :=
    hm.indicator (measurableSet_le
      (by fun_prop : Measurable fun z : unitInterval × ℝ => (z.1 : ℝ)) measurable_const)
  rw [← integral_sub ht hs]
  congr 1
  funext z
  by_cases hzs : z.1 ≤ s
  · have hzt : z.1 ≤ t := hzs.trans hst
    simp [hzs, hzt, not_lt.mpr hzs]
  · by_cases hzt : z.1 ≤ t
    · simp [hzs, hzt, lt_of_not_ge hzs]
    · simp [hzs, hzt]

/-- On supported realizations, the selected path equals the cumulative
integral of all realized jumps at every observation time. -/
theorem poissonEntrancePath_eq_fullJumpPath
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    (Ks : ℕ → Ωs → ℕ) (Xs : ℕ → ℕ → Ωs → unitInterval × ℝ)
    (Kb : ℕ → Ωb → ℕ) (Xb : ℕ → ℕ → Ωb → unitInterval × ℝ)
    (A H : Set (unitInterval × ℝ)) (ω : Ωs × Ωb)
    (hs : (poissonRandomMeasure Ks Xs ω.1).restrict A =
      poissonRandomMeasure Ks Xs ω.1)
    (hb : (poissonRandomMeasure Kb Xb ω.2).restrict H =
      poissonRandomMeasure Kb Xb ω.2)
    (t : unitInterval) :
    poissonEntrancePath Ks Xs Kb Xb A H t ω =
      (∫ z, (if z.1 ≤ t then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Ks Xs ω.1)) +
      (∫ z, (if z.1 ≤ t then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Kb Xb ω.2)) := by
  let B : Set (unitInterval × ℝ) := {z | z.1 ≤ t}
  have hB : MeasurableSet B :=
    measurableSet_Iic.preimage
      (by fun_prop : Measurable fun z : unitInterval × ℝ => (z.1 : ℝ))
  have hsmall : (∫ z in {z | z ∈ A ∧ z.1 ≤ t}, z.2
      ∂(poissonRandomMeasure Ks Xs ω.1)) =
      ∫ z, (if z.1 ≤ t then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Ks Xs ω.1) := by
    change (∫ z, z.2 ∂((poissonRandomMeasure Ks Xs ω.1).restrict (A ∩ B))) = _
    rw [Set.inter_comm A B, ← Measure.restrict_restrict hB, hs]
    exact (integral_indicator hB).symm
  have hbig : poissonJumpPath Kb Xb H ω.2 t =
      ∫ z, (if z.1 ≤ t then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Kb Xb ω.2) := by
    unfold poissonJumpPath
    rw [hb]
  exact congrArg₂ (· + ·) hsmall hbig

/-- Each increment of a supported jump-sum path is exactly the sum of
Poisson integrals over the corresponding half-open time window. -/
theorem poissonEntrancePath_sub_eq_timeWindow
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    (Ks : ℕ → Ωs → ℕ) (Xs : ℕ → ℕ → Ωs → unitInterval × ℝ)
    (Kb : ℕ → Ωb → ℕ) (Xb : ℕ → ℕ → Ωb → unitInterval × ℝ)
    (A H : Set (unitInterval × ℝ)) (ω : Ωs × Ωb)
    (hs : (poissonRandomMeasure Ks Xs ω.1).restrict A =
      poissonRandomMeasure Ks Xs ω.1)
    (hb : (poissonRandomMeasure Kb Xb ω.2).restrict H =
      poissonRandomMeasure Kb Xb ω.2)
    (hsi : Integrable (fun z : unitInterval × ℝ => z.2)
      (poissonRandomMeasure Ks Xs ω.1))
    (hbi : Integrable (fun z : unitInterval × ℝ => z.2)
      (poissonRandomMeasure Kb Xb ω.2))
    (s t : unitInterval) (hst : s ≤ t) :
    poissonEntrancePath Ks Xs Kb Xb A H t ω -
      poissonEntrancePath Ks Xs Kb Xb A H s ω =
    (∫ z, (if s < z.1 ∧ z.1 ≤ t then z.2 else 0 : ℝ)
      ∂(poissonRandomMeasure Ks Xs ω.1)) +
    (∫ z, (if s < z.1 ∧ z.1 ≤ t then z.2 else 0 : ℝ)
      ∂(poissonRandomMeasure Kb Xb ω.2)) := by
  rw [poissonEntrancePath_eq_fullJumpPath Ks Xs Kb Xb A H ω hs hb t,
    poissonEntrancePath_eq_fullJumpPath Ks Xs Kb Xb A H ω hs hb s]
  calc
    (∫ z, (if z.1 ≤ t then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Ks Xs ω.1)) +
      (∫ z, (if z.1 ≤ t then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Kb Xb ω.2)) -
      ((∫ z, (if z.1 ≤ s then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Ks Xs ω.1)) +
       (∫ z, (if z.1 ≤ s then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Kb Xb ω.2))) =
        ((∫ z, (if z.1 ≤ t then z.2 else 0 : ℝ)
          ∂(poissonRandomMeasure Ks Xs ω.1)) -
         (∫ z, (if z.1 ≤ s then z.2 else 0 : ℝ)
          ∂(poissonRandomMeasure Ks Xs ω.1))) +
        ((∫ z, (if z.1 ≤ t then z.2 else 0 : ℝ)
          ∂(poissonRandomMeasure Kb Xb ω.2)) -
         (∫ z, (if z.1 ≤ s then z.2 else 0 : ℝ)
          ∂(poissonRandomMeasure Kb Xb ω.2))) := by ring
    _ = _ := by
      rw [integral_jumpPath_sub_eq_timeWindow _ hsi s t hst,
        integral_jumpPath_sub_eq_timeWindow _ hbi s t hst]

/-- The time-window identity for the actual small/large cutoff model holds
almost surely. Each source is treated on its own probability space before
lifting to the product space. -/
theorem ae_poissonEntrancePath_cutoff_sub_eq_timeWindow
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {ν : Measure ℝ} [SigmaFinite ν]
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (n : ℕ)
    (hds : IsPoissonPointFamily Ks Xs
      ((volume : Measure unitInterval).prod (ν.restrict (smallJumpBand n))) Ps)
    (hdb : IsPoissonPointFamily Kb Xb
      ((volume : Measure unitInterval).prod (ν.restrict (largeJumpBand n))) Pb)
    (hsfirst : Integrable (fun z : unitInterval × ℝ => z.2)
      ((volume : Measure unitInterval).prod (ν.restrict (smallJumpBand n))))
    (hbigfinite : ν (largeJumpBand n) < ⊤)
    (s t : unitInterval) (hst : s ≤ t) :
    ∀ᵐ ω ∂(Ps.prod Pb),
      poissonEntrancePath Ks Xs Kb Xb
        (Set.univ ×ˢ smallJumpBand n) (Set.univ ×ˢ largeJumpBand n) t ω -
      poissonEntrancePath Ks Xs Kb Xb
        (Set.univ ×ˢ smallJumpBand n) (Set.univ ×ˢ largeJumpBand n) s ω =
      (∫ z, (if s < z.1 ∧ z.1 ≤ t then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Ks Xs ω.1)) +
      (∫ z, (if s < z.1 ∧ z.1 ≤ t then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Kb Xb ω.2)) := by
  have hss := hds.ae_restrict_poissonRandomMeasure_eq_self
    (MeasurableSet.prod MeasurableSet.univ (measurableSet_smallJumpBand n))
    (unitTime_prod_restrict_carrier ν (smallJumpBand n) (measurableSet_smallJumpBand n))
  have hbs := hdb.ae_restrict_poissonRandomMeasure_eq_self
    (MeasurableSet.prod MeasurableSet.univ (measurableSet_largeJumpBand n))
    (unitTime_prod_restrict_carrier ν (largeJumpBand n) (measurableSet_largeJumpBand n))
  have hsi := hds.ae_integrable_poissonRandomMeasure
    (by fun_prop : Measurable (fun z : unitInterval × ℝ => z.2))
    (by
      have hn : (∫⁻ z, ‖z.2‖ₑ
          ∂((volume : Measure unitInterval).prod (ν.restrict (smallJumpBand n)))) < ⊤ :=
        hasFiniteIntegral_iff_enorm.mp hsfirst.hasFiniteIntegral
      simpa only [Real.enorm_eq_ofReal_abs] using hn)
  have hbigmass : ((volume : Measure unitInterval).prod
      (ν.restrict (largeJumpBand n))) Set.univ < ⊤ := by
    have hmass := unitTime_prod_markWindow
      (ν.restrict (largeJumpBand n)) Set.univ
    simp only [Set.univ_prod_univ, Measure.restrict_apply_univ] at hmass
    rwa [hmass]
  have hbi := hdb.ae_integrable_of_finite_intensity
    (by fun_prop : Measurable (fun z : unitInterval × ℝ => z.2)) hbigmass
  have hss' : ∀ᵐ ω ∂(Ps.prod Pb),
      (poissonRandomMeasure Ks Xs ω.1).restrict
          (Set.univ ×ˢ smallJumpBand n) = poissonRandomMeasure Ks Xs ω.1 := by
    exact ae_of_ae_map (μ := Ps.prod Pb) measurable_fst.aemeasurable
      (by simpa using hss)
  have hsi' : ∀ᵐ ω ∂(Ps.prod Pb),
      Integrable (fun z : unitInterval × ℝ => z.2)
        (poissonRandomMeasure Ks Xs ω.1) := by
    exact ae_of_ae_map (μ := Ps.prod Pb) measurable_fst.aemeasurable
      (by simpa using hsi)
  have hbs' : ∀ᵐ ω ∂(Ps.prod Pb),
      (poissonRandomMeasure Kb Xb ω.2).restrict
          (Set.univ ×ˢ largeJumpBand n) = poissonRandomMeasure Kb Xb ω.2 := by
    exact ae_of_ae_map (μ := Ps.prod Pb) measurable_snd.aemeasurable
      (by simpa using hbs)
  have hbi' : ∀ᵐ ω ∂(Ps.prod Pb),
      Integrable (fun z : unitInterval × ℝ => z.2)
        (poissonRandomMeasure Kb Xb ω.2) := by
    exact ae_of_ae_map (μ := Ps.prod Pb) measurable_snd.aemeasurable
      (by simpa using hbi)
  filter_upwards [hss', hsi', hbs', hbi'] with ω hs hi hb hj
  exact poissonEntrancePath_sub_eq_timeWindow Ks Xs Kb Xb
    _ _ ω hs hb hi hj s t hst

end ProbabilityTheory
