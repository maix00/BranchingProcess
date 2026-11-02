/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.Process.Brownian.Construction.Lemmas.KolmogorovMoment
import BrownianMotion.Continuity.KolmogorovChentsov
public import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Continuous modification of a pre-Brownian process

For every pre-Brownian process `B` with law `P`, the construction selects a
process `Y` whose coordinates are measurable, which agrees with `B` almost
surely at each fixed time, and whose every sample path is continuous:

\[
\forall t\geq0,\quad Y_t=B_t\quad P\text{-almost surely},
\qquad
\forall\omega,\quad t\mapsto Y_t(\omega)\text{ is continuous}.
\]

The selected version preserves the finite-dimensional Brownian laws, so it
is a Brownian process in Mathlib's sense.

## Public declarations

- `IsPreBrownianReal.exists_continuous_modification_fourthMoment`: a pre-Brownian
  process has a measurable continuous modification.
- `IsPreBrownianReal.exists_brownianReal_modification`: this modification is a
  Brownian process in Mathlib's sense.
- `IsPreBrownianReal.continuousModification`: a selected measurable,
  everywhere-continuous version of a pre-Brownian process.
- `IsPreBrownianReal.measurable_continuousModification`:
  each time coordinate of the selected version is measurable.
- `IsPreBrownianReal.continuousModification_ae_eq`: at each fixed time, the
  selected version agrees almost surely with the original process.
- `IsPreBrownianReal.continuous_continuousModification`: every sample path of
  the selected version is continuous.
- `IsPreBrownianReal.isBrownianReal_continuousModification`: the selected
  version is Brownian in Mathlib's sense.

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

/-- Select the measurable, everywhere-continuous modification supplied by the
fourth-moment Kolmogorov argument. -/
noncomputable def IsPreBrownianReal.continuousModification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    ℝ≥0 → Ω → ℝ :=
  Classical.choose hB.exists_continuous_modification_fourthMoment

/-- Each time coordinate of the selected continuous modification is
measurable. -/
theorem IsPreBrownianReal.measurable_continuousModification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    Measurable (hB.continuousModification t) :=
  (Classical.choose_spec hB.exists_continuous_modification_fourthMoment).1 t

/-- At each fixed time, the selected process agrees almost surely with the
original pre-Brownian process. -/
theorem IsPreBrownianReal.continuousModification_ae_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    hB.continuousModification t =ᵐ[P] B t :=
  (Classical.choose_spec hB.exists_continuous_modification_fourthMoment).2.1 t

/-- Every sample path of the selected modification is continuous. -/
theorem IsPreBrownianReal.continuous_continuousModification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (ω : Ω) :
    Continuous (hB.continuousModification · ω) :=
  (Classical.choose_spec hB.exists_continuous_modification_fourthMoment).2.2 ω

/-- The selected modification preserves the finite-dimensional Brownian
laws and has continuous paths, so it is Brownian in Mathlib's sense. -/
theorem IsPreBrownianReal.isBrownianReal_continuousModification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    IsBrownianReal hB.continuousModification P := by
  refine ⟨hB.congr (fun t =>
    (hB.continuousModification_ae_eq t).symm), ?_⟩
  exact ae_of_all P (hB.continuous_continuousModification)

end ProbabilityTheory

end
