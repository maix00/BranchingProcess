/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.GaltonWatson.Moments.Definitions
import all Probability.BranchingProcess.GaltonWatson.Moments.Lemmas.Bounds
import Probability.MeasureTheory.Moments.PaleyZygmund
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Paley--Zygmund bounds for Galton--Watson generation sizes

## Public declarations

- `integral_generationSizeReal_eq_toReal_firstMoment` and
  `integral_generationSizeReal_sq_eq_toReal_secondMoment` identify the real
  integrals of $Z_n$ and $Z_n^2$ with the corresponding `ENNReal` moments.
- `measure_generationSizeReal_ge_threshold_of_moments` gives the
  finite-slot Paley--Zygmund lower bound from the first two moments.
- `measure_generationSizeReal_ge_half_mean_of_secondMoment_le` gives the
  lower bound $1/(4C)$ when $M_n\le C m_n^2$.

The general Paley--Zygmund inequalities are in
`Probability.MeasureTheory.Moments.PaleyZygmund`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingProcess.GaltonWatson

theorem integral_generationSizeReal_eq_toReal_firstMoment {ι : Type*}
    [Fintype ι] (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) :
    ∫ β : Combinatorics.Branching.Process ι,
      generationSizeReal n β ∂(law μ : Measure _) =
        (generationFirstMoment μ n).toReal := by
  change ∫ β : Combinatorics.Branching.Process ι,
      (ENat.toENNReal (β.generationSize n)).toReal ∂(law μ : Measure _) = _
  have hmeas : AEMeasurable
      (fun β : Combinatorics.Branching.Process ι =>
        ENat.toENNReal (β.generationSize n)) (law μ : Measure _) :=
    (((measurable_of_countable _).comp (generationSize_measurable n)).aemeasurable)
  rw [integral_toReal hmeas (ae_of_all _ fun β => generationSizeENNReal_lt_top β n)]
  rfl

/-- Convert the actual extended second moment to the real-valued integral used
by Paley--Zygmund. -/
theorem integral_generationSizeReal_sq_eq_toReal_secondMoment {ι : Type*}
    [Fintype ι] (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) :
    ∫ β : Combinatorics.Branching.Process ι,
      generationSizeReal n β ^ 2 ∂(law μ : Measure _) =
        (generationSecondMoment μ n).toReal := by
  let f : Combinatorics.Branching.Process ι → ℝ≥0∞ := fun β =>
    ENat.toENNReal (β.generationSize n) ^ 2
  have hfmeas : Measurable f := by
    exact ((measurable_of_countable _).comp (generationSize_measurable n)).pow_const 2
  have hfinite : ∀ᵐ β ∂(law μ : Measure _), f β < ∞ := by
    filter_upwards [] with β
    exact ENNReal.pow_lt_top (generationSizeENNReal_lt_top β n)
  have htoReal := integral_toReal hfmeas.aemeasurable hfinite
  calc
    _ = ∫ β : Combinatorics.Branching.Process ι, (f β).toReal ∂(law μ : Measure _) := by
      apply integral_congr_ae
      filter_upwards [] with β
      simp [generationSizeReal, f, ENNReal.toReal_pow]
    _ = (∫⁻ β : Combinatorics.Branching.Process ι,
        f β ∂(law μ : Measure _)).toReal := htoReal
    _ = (generationSecondMoment μ n).toReal := by
      simp [f, generationSecondMoment]

theorem measure_generationSizeReal_ge_threshold_of_moments {ι : Type*}
    [Fintype ι] (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) (threshold : ℝ)
    (hthreshold : 0 ≤ threshold)
    (hmean_threshold : threshold < (generationFirstMoment μ n).toReal)
    (hsecond_pos : 0 < (generationSecondMoment μ n).toReal) :
    ((law μ : ProbabilityMeasure (Combinatorics.Branching.Process ι)).toMeasure.real
      {β | threshold ≤ generationSizeReal n β}) ≥
      ((generationFirstMoment μ n).toReal - threshold) ^ 2 /
        (generationSecondMoment μ n).toReal := by
  exact measure_ge_threshold_of_moments (law μ : Measure
      (Combinatorics.Branching.Process ι)) (generationSizeReal n)
    (generationSizeReal_measurable n)
    (ae_of_all _ fun β => generationSizeReal_nonneg n β)
    (generationSizeReal_integrable μ n) (generationSizeReal_memLp_two μ n)
    (generationFirstMoment μ n).toReal (generationSecondMoment μ n).toReal
    threshold (integral_generationSizeReal_eq_toReal_firstMoment μ n)
    (integral_generationSizeReal_sq_eq_toReal_secondMoment μ n)
    hthreshold hmean_threshold hsecond_pos

/-- The finite-slot generation reaches half its mean with the usual
second-moment lower bound. This is the real-valued endpoint used by the
population-growth argument. -/
theorem measure_generationSizeReal_ge_half_mean_of_secondMoment_le
    {ι : Type*} [Fintype ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) (C : ℝ)
    (hmean_pos : 0 < (generationFirstMoment μ n).toReal)
    (hsecond_pos : 0 < (generationSecondMoment μ n).toReal)
    (hC_pos : 0 < C)
    (hsecond_le : (generationSecondMoment μ n).toReal ≤
      C * (generationFirstMoment μ n).toReal ^ 2) :
    ((law μ : ProbabilityMeasure (Combinatorics.Branching.Process ι)).toMeasure.real
      {β | (generationFirstMoment μ n).toReal / 2 ≤ generationSizeReal n β}) ≥
      1 / (4 * C) := by
  exact measure_ge_threshold_of_secondMoment_le
    (law μ : Measure (Combinatorics.Branching.Process ι)) (generationSizeReal n)
    (generationSizeReal_measurable n)
    (ae_of_all _ fun β => generationSizeReal_nonneg n β)
    (generationSizeReal_integrable μ n) (generationSizeReal_memLp_two μ n)
    (generationFirstMoment μ n).toReal (generationSecondMoment μ n).toReal
    ((generationFirstMoment μ n).toReal / 2) C
    (integral_generationSizeReal_eq_toReal_firstMoment μ n)
    (integral_generationSizeReal_sq_eq_toReal_secondMoment μ n)
    (by positivity) hmean_pos (by nlinarith) hsecond_pos hC_pos hsecond_le
end ProbabilityTheory.BranchingProcess.GaltonWatson

end
