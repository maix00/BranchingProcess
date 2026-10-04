/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.Levy.Jump.IndependentConfiguration

/-!
# Superposition of independent Poisson jump counts

The two canonical Poisson sources used for the small/large jump split have
the correct combined count law on every finite-intensity measurable region.
-/

namespace ProbabilityTheory

open MeasureTheory

theorem poissonRandomMeasure_product_count_law
    {Ωs Ωb E : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    [MeasurableSpace E]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → E}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → E}
    {ms mb : Measure E} [SigmaFinite ms] [SigmaFinite mb] [Nonempty E]
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (hds : IsPoissonPointFamily Ks Xs ms Ps)
    (hdb : IsPoissonPointFamily Kb Xb mb Pb)
    (A : Set E) (hA : MeasurableSet A)
    (hfinS : ms A < ⊤) (hfinB : mb A < ⊤) :
    HasLaw (fun ω : Ωs × Ωb =>
      (poissonRandomMeasure Ks Xs ω.1 + poissonRandomMeasure Kb Xb ω.2) A)
      ((poissonMeasure ((ms A).toNNReal + (mb A).toNNReal)).map
        (Nat.cast : ℕ → ENNReal)) (Ps.prod Pb) := by
  let fs : Ωs → ENNReal := fun ω => poissonRandomMeasure Ks Xs ω A
  let fb : Ωb → ENNReal := fun ω => poissonRandomMeasure Kb Xb ω A
  have hms : Measurable fs :=
    measurable_poissonRandomMeasure_apply hds.measurable_count hds.measurable_point hA
  have hmb : Measurable fb :=
    measurable_poissonRandomMeasure_apply hdb.measurable_count hdb.measurable_point hA
  have hls : HasLaw fs
      ((poissonMeasure (ms A).toNNReal).map (Nat.cast : ℕ → ENNReal)) Ps :=
    ⟨hms.aemeasurable, map_poissonRandomMeasure_apply hds hA hfinS⟩
  have hlb : HasLaw fb
      ((poissonMeasure (mb A).toNNReal).map (Nat.cast : ℕ → ENNReal)) Pb :=
    ⟨hmb.aemeasurable, map_poissonRandomMeasure_apply hdb hA hfinB⟩
  have hlsProd : HasLaw (fun ω : Ωs × Ωb => fs ω.1)
      ((poissonMeasure (ms A).toNNReal).map (Nat.cast : ℕ → ENNReal))
      (Ps.prod Pb) := by
    refine ⟨(hms.comp measurable_fst).aemeasurable, ?_⟩
    rw [← Function.comp_def, ← Measure.map_map hms measurable_fst,
      Measure.map_fst_prod, measure_univ, one_smul, hls.map_eq]
  have hlbProd : HasLaw (fun ω : Ωs × Ωb => fb ω.2)
      ((poissonMeasure (mb A).toNNReal).map (Nat.cast : ℕ → ENNReal))
      (Ps.prod Pb) := by
    refine ⟨(hmb.comp measurable_snd).aemeasurable, ?_⟩
    rw [← Function.comp_def, ← Measure.map_map hmb measurable_snd,
      Measure.map_snd_prod, measure_univ, one_smul, hlb.map_eq]
  have hindep : (fun ω : Ωs × Ωb => fs ω.1) ⟂ᵢ[Ps.prod Pb]
      (fun ω => fb ω.2) := indepFun_prod hms hmb
  convert hindep.hasLaw_add_map_cast_poissonMeasure hlsProd hlbProd using 1

/-- The count law of the superposed random measure uses the sum of the two
intensity measures, without an independently postulated Poisson law. -/
theorem poissonRandomMeasure_product_count_law_add_intensity
    {Ωs Ωb E : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    [MeasurableSpace E]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → E}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → E}
    {ms mb : Measure E} [SigmaFinite ms] [SigmaFinite mb] [Nonempty E]
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (hds : IsPoissonPointFamily Ks Xs ms Ps)
    (hdb : IsPoissonPointFamily Kb Xb mb Pb)
    (A : Set E) (hA : MeasurableSet A)
    (hfinS : ms A < ⊤) (hfinB : mb A < ⊤) :
    HasLaw (fun ω : Ωs × Ωb =>
      (poissonRandomMeasure Ks Xs ω.1 + poissonRandomMeasure Kb Xb ω.2) A)
      ((poissonMeasure ((ms + mb) A).toNNReal).map
        (Nat.cast : ℕ → ENNReal)) (Ps.prod Pb) := by
  simpa only [Measure.add_apply, ENNReal.toNNReal_add hfinS.ne hfinB.ne] using
    poissonRandomMeasure_product_count_law hds hdb A hA hfinS hfinB

/-- Splitting an intensity measure across a measurable small-jump region and
its complement, then superposing independent Poisson sources, recovers the
original finite-region count law. -/
theorem poissonRandomMeasure_partition_count_law
    {Ωs Ωb E : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (S : Set E) (hS : MeasurableSet S)
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → E}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → E}
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (hds : IsPoissonPointFamily Ks Xs (m.restrict S) Ps)
    (hdb : IsPoissonPointFamily Kb Xb (m.restrict Sᶜ) Pb)
    (A : Set E) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    HasLaw (fun ω : Ωs × Ωb =>
      (poissonRandomMeasure Ks Xs ω.1 + poissonRandomMeasure Kb Xb ω.2) A)
      ((poissonMeasure (m A).toNNReal).map
        (Nat.cast : ℕ → ENNReal)) (Ps.prod Pb) := by
  have hfinS : m.restrict S A < ⊤ :=
    (Measure.restrict_le_self A).trans_lt hfin
  have hfinB : m.restrict Sᶜ A < ⊤ :=
    (Measure.restrict_le_self A).trans_lt hfin
  simpa only [Measure.restrict_add_restrict_compl hS] using
    poissonRandomMeasure_product_count_law_add_intensity
      hds hdb A hA hfinS hfinB

end ProbabilityTheory
