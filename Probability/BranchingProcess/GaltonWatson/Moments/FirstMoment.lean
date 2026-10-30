/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.GaltonWatson.Moments.Definitions
import all Probability.BranchingProcess.GaltonWatson.Moments.Lemmas.FieldExpansion
import all Probability.BranchingProcess.GaltonWatson.Moments.Lemmas.Bounds

/-!
# First generation moments for finite-slot Galton--Watson processes

## Public declarations

- `generationFirstMoment_succ_eq_slotSum` gives
  $m_{n+1}=\sum_i p_i m_n$.
- `generationFirstMoment_succ_eq_offspringMean` and
  `generationFirstMoment_eq_offspringMean_pow` give
  $m_{n+1}=\rho m_n$ and $m_n=\rho^n$.
- `offspringMean_eq_expectedChildCount` identifies the slot-sum mean with the
offspring law's expected child count.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingProcess.GaltonWatson

theorem generationFirstMoment_succ_eq_slotSum {ι : Type*} [Fintype ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) :
    generationFirstMoment μ (n + 1) =
      ∑ i, offspringSlotWeight μ i * generationFirstMoment μ n := by
  classical
  rw [generationFirstMoment_eq_fieldLaw μ (n + 1)]
  calc
    _ = ∫⁻ field : Combinatorics.Branching.StepField ι PUnit.{1},
        ∑ i, generationSingleTerm n i field
        ∂(μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})) := by
      apply lintegral_congr_ae
      filter_upwards [] with field
      rw [generationFieldValue_succ_eq_sum field n]
      rfl
    _ = ∑ i, ∫⁻ field : Combinatorics.Branching.StepField ι PUnit.{1},
        generationSingleTerm n i field
        ∂(μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})) := by
      exact lintegral_fintype_sum (μ.fieldLaw : Measure
        (Combinatorics.Branching.StepField ι PUnit.{1}))
        (fun i field => generationSingleTerm n i field)
        (fun i => generationSingleTerm_measurable n i)
    _ = ∑ i, offspringSlotWeight μ i * generationFirstMoment μ n := by
      apply Finset.sum_congr rfl
      intro i hi
      exact lintegral_generationSingleTerm μ n i

/-- The generation mean multiplies by the actual mean offspring number. -/
theorem generationFirstMoment_succ_eq_offspringMean {ι : Type*} [Fintype ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) :
    generationFirstMoment μ (n + 1) = offspringMean μ * generationFirstMoment μ n := by
  rw [generationFirstMoment_succ_eq_slotSum, offspringMean, Finset.sum_mul]

/-- The actual expected generation size is the offspring mean to the power
of the generation. -/
theorem generationFirstMoment_eq_offspringMean_pow {ι : Type*} [Fintype ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) :
    generationFirstMoment μ n = offspringMean μ ^ n := by
  induction n with
  | zero => simp [generationFirstMoment_zero]
  | succ n ih =>
      rw [generationFirstMoment_succ_eq_offspringMean, ih, pow_succ]
      ac_rfl

/-- The generation mean agrees with the offspring-law mean. -/
theorem offspringMean_eq_expectedChildCount {ι : Type*} [Fintype ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) : offspringMean μ = μ.expectedChildCount := by
  calc
    offspringMean μ = generationFirstMoment μ 1 := by
      rw [generationFirstMoment_succ_eq_offspringMean μ 0,
        generationFirstMoment_zero, mul_one]
    _ = μ.expectedChildCount := by
      simpa [generationFirstMoment] using
        lintegral_generationSize_one_eq_expectedChildCount μ

end ProbabilityTheory.BranchingProcess.GaltonWatson

end
