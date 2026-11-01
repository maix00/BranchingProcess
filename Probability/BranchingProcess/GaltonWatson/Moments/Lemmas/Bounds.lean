/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingProcess.GaltonWatson.Moments.Definitions
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Finite-generation bounds for Galton--Watson moments

## Internal proof declarations

- `childCount_le_slotCard` bounds one generation's offspring count by the
  finite slot cardinality; `generationSize_le_slotCard_pow` and
  `generationSizeENNReal_le_slotCard_pow` iterate that bound.
- `generationSizeENNReal_lt_top`, `generationFirstMoment_lt_top`, and
  `generationSecondMoment_lt_top` establish finiteness of the generation size
  and its first two moments.
- `generationSizeReal_measurable`, `generationSizeReal_nonneg`, and
  `generationSizeReal_le_slotCard_pow` give measurability, nonnegativity, and
  a pointwise bound for the real-valued generation size.
- `generationSizeReal_memLp_two` and `generationSizeReal_integrable` provide
  integrability inputs to the public moment identities.
- `generationFirstMoment_zero` evaluates the initial generation's first
  moment.

These internal estimates establish deterministic population bounds, moment
finiteness, measurability, and integrability for the finite-slot model. They
are specific to the proofs of the public moment identities.

For a finite slot type $\iota$, every generation and its first two moments
are finite, with the pointwise population bound
\[
  Z_n\le |\iota|^n,
  \qquad \mathbb E[Z_n]<\infty,
  \qquad \mathbb E[Z_n^2]<\infty.
\]
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingProcess.GaltonWatson

lemma childCount_le_slotCard {ι : Type*} [Fintype ι]
    (ξ : Combinatorics.Branching.Step ι PUnit.{1}) :
    ξ.childCount ≤ (Fintype.card ι : ℕ∞) := by
  unfold Combinatorics.Branching.Step.childCount
  calc
    (Combinatorics.Branching.support ξ).encard ≤ ENat.card ι := Set.encard_le_card
    _ = (Fintype.card ι : ℕ∞) := by simp

lemma generationSize_le_slotCard_pow {ι : Type*} [Fintype ι]
    (β : Combinatorics.Branching.Process ι) (n : ℕ) :
    β.generationSize n ≤ (Fintype.card ι : ℕ∞) ^ n := by
  induction n with
  | zero => simp [Combinatorics.Branching.BranchingWalk.generationSize_zero]
  | succ n ih =>
      classical
      letI : Fintype {p // p ∈ Combinatorics.Branching.survivingParticlesAt β n} :=
        (Combinatorics.Branching.RootIndexed.BranchingWalk.generationSlice_finite
          β n).fintype
      rw [Combinatorics.Branching.BranchingWalk.generationSize_succ_eq_sum_childCount
        β n]
      calc
        _ ≤ ∑ p : {p // p ∈ Combinatorics.Branching.survivingParticlesAt β n},
            (Fintype.card ι : ℕ∞) := by
          apply Finset.sum_le_sum
          intro p hp
          exact childCount_le_slotCard (β.step PUnit.unit p.1.2)
        _ = (Fintype.card {p // p ∈
              Combinatorics.Branching.survivingParticlesAt β n} : ℕ∞) *
              (Fintype.card ι : ℕ∞) := by simp
        _ = β.generationSize n * (Fintype.card ι : ℕ∞) := by
          change (Fintype.card {p // p ∈
              Combinatorics.Branching.survivingParticlesAt β n} : ℕ∞) * _ =
            (Combinatorics.Branching.survivingParticlesAt β n).encard * _
          rw [← Set.coe_fintypeCard]
        _ ≤ (Fintype.card ι : ℕ∞) ^ n * (Fintype.card ι : ℕ∞) :=
          mul_le_mul_of_nonneg_right ih (by simp)
        _ = (Fintype.card ι : ℕ∞) ^ (n + 1) := by rw [pow_succ]

lemma generationSizeENNReal_le_slotCard_pow {ι : Type*} [Fintype ι]
    (β : Combinatorics.Branching.Process ι) (n : ℕ) :
    ENat.toENNReal (β.generationSize n) ≤ (Fintype.card ι : ℝ≥0∞) ^ n := by
  calc
    ENat.toENNReal (β.generationSize n) ≤
        ENat.toENNReal ((Fintype.card ι : ℕ∞) ^ n) :=
      ENat.toENNReal_mono (generationSize_le_slotCard_pow β n)
    _ = (Fintype.card ι : ℝ≥0∞) ^ n := by simp [ENat.toENNReal_coe]

lemma generationSizeENNReal_lt_top {ι : Type*} [Fintype ι]
    (β : Combinatorics.Branching.Process ι) (n : ℕ) :
    ENat.toENNReal (β.generationSize n) < ∞ := by
  exact lt_of_le_of_lt (generationSizeENNReal_le_slotCard_pow β n) (by simp)

lemma generationFirstMoment_lt_top {ι : Type*} [Fintype ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) : generationFirstMoment μ n < ∞ := by
  rw [generationFirstMoment]
  have hbound : ∀ β : Combinatorics.Branching.Process ι,
      ENat.toENNReal (β.generationSize n) ≤ (Fintype.card ι : ℝ≥0∞) ^ n :=
    fun β => generationSizeENNReal_le_slotCard_pow β n
  have hlin : (∫⁻ β : Combinatorics.Branching.Process ι,
      ENat.toENNReal (β.generationSize n) ∂(law μ : Measure _)) ≤
      (Fintype.card ι : ℝ≥0∞) ^ n := by
    calc
      _ ≤ ∫⁻ _ : Combinatorics.Branching.Process ι,
          (Fintype.card ι : ℝ≥0∞) ^ n ∂(law μ : Measure _) := by
        apply lintegral_mono_ae
        exact ae_of_all _ hbound
      _ = (Fintype.card ι : ℝ≥0∞) ^ n := by simp
  exact lt_of_le_of_lt hlin (by simp)

lemma generationSecondMoment_lt_top {ι : Type*} [Fintype ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) : generationSecondMoment μ n < ∞ := by
  rw [generationSecondMoment]
  have hbound (β : Combinatorics.Branching.Process ι) :
      ENat.toENNReal (β.generationSize n) ^ 2 ≤
        ((Fintype.card ι : ℝ≥0∞) ^ n) ^ 2 := by
    exact pow_le_pow_left₀ (by simp) (generationSizeENNReal_le_slotCard_pow β n) 2
  have hlin : (∫⁻ β : Combinatorics.Branching.Process ι,
      ENat.toENNReal (β.generationSize n) ^ 2 ∂(law μ : Measure _)) ≤
      ((Fintype.card ι : ℝ≥0∞) ^ n) ^ 2 := by
    calc
      _ ≤ ∫⁻ _ : Combinatorics.Branching.Process ι,
          ((Fintype.card ι : ℝ≥0∞) ^ n) ^ 2 ∂(law μ : Measure _) := by
        apply lintegral_mono_ae
        exact ae_of_all _ hbound
      _ = ((Fintype.card ι : ℝ≥0∞) ^ n) ^ 2 := by simp
  exact lt_of_le_of_lt hlin (by simp)

lemma generationSizeReal_measurable {ι : Type*} [Countable ι]
    (n : ℕ) : Measurable (generationSizeReal (ι := ι) n) := by
  exact ENNReal.measurable_toReal.comp
    ((measurable_of_countable _).comp (generationSize_measurable n))

lemma generationSizeReal_nonneg {ι : Type*} [Fintype ι]
    (n : ℕ) (β : Combinatorics.Branching.Process ι) :
    0 ≤ generationSizeReal n β := ENNReal.toReal_nonneg

lemma generationSizeReal_le_slotCard_pow {ι : Type*} [Fintype ι]
    (n : ℕ) (β : Combinatorics.Branching.Process ι) :
    generationSizeReal n β ≤ (Fintype.card ι : ℝ) ^ n := by
  have htop : (Fintype.card ι : ℝ≥0∞) ^ n ≠ ∞ := by simp
  have h := ENNReal.toReal_mono htop (generationSizeENNReal_le_slotCard_pow β n)
  simpa [generationSizeReal, ENNReal.toReal_pow] using h

/-- At a fixed generation, finite offspring slots give a deterministic real
bound, hence an `L²` generation-size observation under the actual process law.
This requires no positivity assumption on the offspring count. -/
lemma generationSizeReal_memLp_two {ι : Type*} [Fintype ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) :
    MemLp (generationSizeReal (ι := ι) n) 2 (law μ : Measure _) := by
  apply MemLp.of_bound (generationSizeReal_measurable n).aestronglyMeasurable _
  filter_upwards [] with β
  rw [Real.norm_eq_abs, abs_of_nonneg (generationSizeReal_nonneg n β)]
  exact generationSizeReal_le_slotCard_pow n β

/-- Integrability follows from the fixed-generation `L²` bound. -/
lemma generationSizeReal_integrable {ι : Type*} [Fintype ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) :
    Integrable (generationSizeReal (ι := ι) n) (law μ : Measure _) :=
  (generationSizeReal_memLp_two μ n).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
/-- The initial generation consists of the single root. -/
lemma generationFirstMoment_zero {ι : Type*} [Countable ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) : generationFirstMoment μ 0 = 1 := by
  rw [generationFirstMoment]
  simp [Combinatorics.Branching.BranchingWalk.generationSize_zero]

end ProbabilityTheory.BranchingProcess.GaltonWatson
