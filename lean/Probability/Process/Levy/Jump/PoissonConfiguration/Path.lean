/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.Levy.Jump.PoissonConfiguration.Increment
import Probability.Process.Levy.Jump.Campbell.Support

/-!
# Almost-sure path identities for cutoff Poisson configurations

For a Poisson source whose intensity is carried by a mark band, restricting
the realized random measure to that band changes nothing almost surely. This
identifies the canonical whole-mark path with its explicit cutoff version.
-/

namespace ProbabilityTheory

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Almost surely, the canonical small-plus-large path agrees with the path
that explicitly restricts both sources to their cutoff bands. -/
theorem ae_poissonEntrancePath_canonical_eq_cutoff
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
    (t : unitInterval) :
    ∀ᵐ ω : Ωs × Ωb ∂(Ps.prod Pb),
      poissonEntrancePath Ks Xs Kb Xb Set.univ
        (Set.univ ×ˢ largeJumpBand n) t ω =
      poissonEntrancePath Ks Xs Kb Xb
        (Set.univ ×ˢ smallJumpBand n) (Set.univ ×ˢ largeJumpBand n) t ω := by
  have hs := hds.ae_restrict_poissonRandomMeasure_eq_self
    (MeasurableSet.prod MeasurableSet.univ (measurableSet_smallJumpBand n))
    (unitTime_prod_restrict_carrier ν (smallJumpBand n)
      (measurableSet_smallJumpBand n))
  have hb := hdb.ae_restrict_poissonRandomMeasure_eq_self
    (MeasurableSet.prod MeasurableSet.univ (measurableSet_largeJumpBand n))
    (unitTime_prod_restrict_carrier ν (largeJumpBand n)
      (measurableSet_largeJumpBand n))
  have hs' : ∀ᵐ ω ∂(Ps.prod Pb),
      (poissonRandomMeasure Ks Xs ω.1).restrict
        (Set.univ ×ˢ smallJumpBand n) = poissonRandomMeasure Ks Xs ω.1 := by
    exact ae_of_ae_map (μ := Ps.prod Pb) measurable_fst.aemeasurable (by simpa using hs)
  have hb' : ∀ᵐ ω ∂(Ps.prod Pb),
      (poissonRandomMeasure Kb Xb ω.2).restrict
        (Set.univ ×ˢ largeJumpBand n) = poissonRandomMeasure Kb Xb ω.2 := by
    exact ae_of_ae_map (μ := Ps.prod Pb) measurable_snd.aemeasurable (by simpa using hb)
  filter_upwards [hs', hb'] with ω hsω hbω
  rw [poissonEntrancePath_eq_fullJumpPath Ks Xs Kb Xb Set.univ
      (Set.univ ×ˢ largeJumpBand n) ω (by simp) hbω t,
    poissonEntrancePath_eq_fullJumpPath Ks Xs Kb Xb
      (Set.univ ×ˢ smallJumpBand n) (Set.univ ×ˢ largeJumpBand n)
      ω hsω hbω t]

/-- Almost surely, the canonical Poisson entrance path starts at zero. -/
theorem IsPoissonPointFamily.ae_poissonEntrancePath_canonical_start_eq_zero
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {ν : Measure ℝ} [SigmaFinite ν]
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (n : ℕ)
    (hds : IsPoissonPointFamily Ks Xs
      ((volume : Measure unitInterval).prod
        (ν.restrict (smallJumpBand n))) Ps)
    (hdb : IsPoissonPointFamily Kb Xb
      ((volume : Measure unitInterval).prod
        (ν.restrict (largeJumpBand n))) Pb) :
    ∀ᵐ ω ∂(Ps.prod Pb),
      poissonEntrancePath Ks Xs Kb Xb Set.univ
        (Set.univ ×ˢ largeJumpBand n) ⊥ ω = 0 := by
  have hs0 := hds.ae_no_jump_at_time ⊥
  have hb0 := hdb.ae_no_jump_at_time ⊥
  have hs0' : ∀ᵐ ω ∂(Ps.prod Pb),
      poissonRandomMeasure Ks Xs ω.1 ({⊥} ×ˢ Set.univ) = 0 := by
    exact ae_of_ae_map (μ := Ps.prod Pb) measurable_fst.aemeasurable (by simpa using hs0)
  have hb0' : ∀ᵐ ω ∂(Ps.prod Pb),
      poissonRandomMeasure Kb Xb ω.2 ({⊥} ×ˢ Set.univ) = 0 := by
    exact ae_of_ae_map (μ := Ps.prod Pb) measurable_snd.aemeasurable (by simpa using hb0)
  have hbSupport := hdb.ae_restrict_poissonRandomMeasure_eq_self
    (MeasurableSet.prod MeasurableSet.univ (measurableSet_largeJumpBand n))
    (unitTime_prod_restrict_carrier ν (largeJumpBand n)
      (measurableSet_largeJumpBand n))
  have hbSupport' : ∀ᵐ ω ∂(Ps.prod Pb),
      (poissonRandomMeasure Kb Xb ω.2).restrict
        (Set.univ ×ˢ largeJumpBand n) = poissonRandomMeasure Kb Xb ω.2 := by
    exact ae_of_ae_map (μ := Ps.prod Pb) measurable_snd.aemeasurable
      (by simpa using hbSupport)
  filter_upwards [hs0', hb0', hbSupport'] with ω hsω hbω hsupp
  let awayFromBottom : Set (unitInterval × ℝ) :=
    {z | z.1 ≠ (⊥ : unitInterval)}
  have hsmallAE :
      (fun z : unitInterval × ℝ => if z.1 ≤ (⊥ : unitInterval) then z.2 else 0) =ᵐ[
        poissonRandomMeasure Ks Xs ω.1] 0 := by
    have hset : awayFromBottom ∈
        ae (poissonRandomMeasure Ks Xs ω.1) := by
      apply mem_ae_iff.mpr
      have hcompl :
          awayFromBottomᶜ =
            ({⊥} : Set unitInterval) ×ˢ Set.univ := by
        ext z
        simp [awayFromBottom]
      rw [hcompl]
      exact hsω
    filter_upwards [hset] with z hz
    have hnle : ¬ z.1 ≤ ⊥ := by simpa [le_bot_iff, awayFromBottom] using hz
    simp [hnle]
  have hbigAE :
      (fun z : unitInterval × ℝ => if z.1 ≤ (⊥ : unitInterval) then z.2 else 0) =ᵐ[
        poissonRandomMeasure Kb Xb ω.2] 0 := by
    have hset : awayFromBottom ∈
        ae (poissonRandomMeasure Kb Xb ω.2) := by
      apply mem_ae_iff.mpr
      have hcompl :
          awayFromBottomᶜ =
            ({⊥} : Set unitInterval) ×ˢ Set.univ := by
        ext z
        simp [awayFromBottom]
      rw [hcompl]
      exact hbω
    filter_upwards [hset] with z hz
    have hnle : ¬ z.1 ≤ ⊥ := by simpa [le_bot_iff, awayFromBottom] using hz
    simp [hnle]
  have hsmallInt :
      (∫ z, (if z.1 ≤ (⊥ : unitInterval) then z.2 else 0 : ℝ)
        ∂poissonRandomMeasure Ks Xs ω.1) = 0 := by
    rw [integral_congr_ae hsmallAE]
    simp
  have hbigInt :
      (∫ z, (if z.1 ≤ (⊥ : unitInterval) then z.2 else 0 : ℝ)
        ∂poissonRandomMeasure Kb Xb ω.2) = 0 := by
    rw [integral_congr_ae hbigAE]
    simp
  have hsmallEq :
      (∫ z, (if z.1 = (⊥ : unitInterval) then z.2 else 0 : ℝ)
        ∂poissonRandomMeasure Ks Xs ω.1) = 0 := by
    simpa only [le_bot_iff] using hsmallInt
  have hbigEq :
      (∫ z, (if z.1 = (⊥ : unitInterval) then z.2 else 0 : ℝ)
        ∂poissonRandomMeasure Kb Xb ω.2) = 0 := by
    simpa only [le_bot_iff] using hbigInt
  rw [poissonEntrancePath_eq_fullJumpPath Ks Xs Kb Xb Set.univ
    (Set.univ ×ˢ largeJumpBand n) ω (by simp) hsupp ⊥]
  simp [hsmallEq, hbigEq]

end ProbabilityTheory
