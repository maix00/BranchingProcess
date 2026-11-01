/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.Levy.Cutoff
public import Probability.RandomMeasure.Poisson.Integration.Integrability
public import Probability.RandomMeasure.Poisson.JumpPath.Entrance.Increment
import Probability.RandomMeasure.Poisson.Intensity.Support
import Probability.RandomMeasure.Poisson.Intensity.TimeMark

/-!
# Increments of a Lévy cutoff path

For the small- and large-jump cutoff sources, pathwise integrability gives an
almost-sure representation of every path increment by Poisson integrals over
the intervening half-open time window.

For fixed sources and cutoff `n`, write `X_n(t,ω)` for
`poissonEntrancePath Ks Xs Kb Xb (Set.univ ×ˢ smallJumpBand n)
(Set.univ ×ˢ largeJumpBand n) t ω`, and write
`N_s(ω_s) = poissonRandomMeasure Ks Xs ω_s` and
`N_b(ω_b) = poissonRandomMeasure Kb Xb ω_b`. A point `(r,x)` records its
time and jump size. For `s≤t`, the increment is the sum of the two window
integrals:

\[
X_n(t,\omega)-X_n(s,\omega)
=\int \mathbf 1_{\{s<r\le t\}}x\,N_s(\omega_1)(d(r,x))
+\int \mathbf 1_{\{s<r\le t\}}x\,N_b(\omega_2)(d(r,x))
\quad (P_s\otimes P_b)\text{-almost surely}.
\]

## Public declarations

- `ProbabilityTheory.ae_poissonEntrancePath_cutoff_sub_eq_timeWindow` states
  the increment identity almost surely for the fixed-cutoff construction.
  Its generic supported-path identity is owned by
  `Probability.RandomMeasure.Poisson.JumpPath.Entrance.Increment`.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

attribute [local instance] Classical.propDecidable

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
