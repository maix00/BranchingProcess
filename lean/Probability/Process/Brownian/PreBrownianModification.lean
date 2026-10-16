/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.KolmogorovMoment
public import BrownianMotion.Continuity.KolmogorovChentsov
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Continuous modification of a pre-Brownian process

The public theorems in this file are:

- `IsPreBrownianReal.exists_continuous_modification_fourthMoment`: a pre-Brownian
  process has a measurable continuous modification.
- `IsPreBrownianReal.exists_brownianReal_modification`: this modification is a
  Brownian process in Mathlib's sense.

The proof applies the Kolmogorov–Chentsov theorem
`ProbabilityTheory.exists_modification_holder'` of Rémy Degenne et al.,
*Formalization of Brownian motion in Lean*, arXiv:2511.20118, to the
fourth-moment increment bound. It provides the continuous Brownian motion
used in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

/-- The fourth-moment Kolmogorov condition gives a measurable Brownian
modification with continuous sample paths. -/
theorem IsPreBrownianReal.exists_continuous_modification_fourthMoment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] B t) ∧
      (∀ ω, Continuous (Y · ω)) := by
  letI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨Y, hYmeas, hYmod, hYholder⟩ :=
    exists_modification_holder'
      isCoverWithBoundedCoveringNumber_Ico_nnreal
      hB.isAEKolmogorovProcess_four
      (by intro n; finiteness)
      (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 2)
  refine ⟨Y, hYmeas, hYmod, fun ω => continuous_iff_continuousAt.mpr (fun t => ?_)⟩
  obtain ⟨U, hU, hUH⟩ := hYholder ω t
  have hβpos : (0 : ℝ≥0) < 1 / 8 := by norm_num
  have hβlt : (1 / 8 : ℝ≥0) < ((2 : ℝ) - 1) / 4 := by norm_num
  obtain ⟨C, hC⟩ := hUH (1 / 8) hβpos hβlt
  exact (hC.continuousOn hβpos).continuousAt hU

/-- A continuous modification inherits the pre-Brownian finite-dimensional
laws, hence is a Brownian process. -/
theorem IsPreBrownianReal.exists_brownianReal_modification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      IsBrownianReal Y P ∧ (∀ t, Measurable (Y t)) ∧
      (∀ t, Y t =ᵐ[P] B t) := by
  obtain ⟨Y, hYmeas, hYmod, hYcont⟩ :=
    hB.exists_continuous_modification_fourthMoment
  refine ⟨Y, ⟨hB.congr (fun t => (hYmod t).symm), ?_⟩, hYmeas, hYmod⟩
  exact Filter.Eventually.of_forall hYcont

end ProbabilityTheory

end
