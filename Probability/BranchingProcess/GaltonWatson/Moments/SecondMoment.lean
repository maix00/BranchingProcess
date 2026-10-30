/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.GaltonWatson.Moments.FirstMoment
import all Probability.BranchingProcess.GaltonWatson.Moments.Lemmas.Bounds
import all Probability.BranchingProcess.GaltonWatson.Moments.Lemmas.FieldExpansion
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Second generation moments for finite-slot Galton--Watson processes

## Public declarations

- `generationSecondMoment_succ_eq_slotPairSum` gives the recurrence as a sum
over ordered root-slot pairs.
- `generationSecondMoment_succ_eq_offspringMoments` groups it as
  $M_{n+1}=\rho M_n+\kappa m_n^2$.
- `generationSecondMomentReal_succ_eq_offspringMoments` gives the same
  recurrence after conversion to real-valued moments.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingProcess.GaltonWatson

theorem generationSecondMoment_succ_eq_slotPairSum {ι : Type*} [Fintype ι]
    [DecidableEq ι] (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) :
    generationSecondMoment μ (n + 1) =
      ∑ i, ∑ j, offspringSlotPairWeight μ i j *
        (if i = j then generationSecondMoment μ n else
          generationFirstMoment μ n * generationFirstMoment μ n) := by
  classical
  have hsum_meas (i : ι) : Measurable
      (fun field : Combinatorics.Branching.StepField ι PUnit.{1} =>
        ∑ j, generationPairTerm n i j field) := by
    exact Finset.measurable_sum Finset.univ
      (fun j _ => generationPairTerm_measurable n i j)
  rw [generationSecondMoment_eq_fieldLaw μ (n + 1)]
  calc
    _ = ∫⁻ field : Combinatorics.Branching.StepField ι PUnit.{1},
        ∑ i, ∑ j, generationPairTerm n i j field
        ∂(μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})) := by
      apply lintegral_congr_ae
      filter_upwards [] with field
      rw [generationFieldValue_succ_eq_sum field n, pow_two,
        Finset.sum_mul_sum]
      rfl
    _ = ∑ i, ∫⁻ field : Combinatorics.Branching.StepField ι PUnit.{1},
        ∑ j, generationPairTerm n i j field
        ∂(μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})) := by
      exact lintegral_fintype_sum (μ.fieldLaw : Measure
        (Combinatorics.Branching.StepField ι PUnit.{1}))
        (fun i field => ∑ j, generationPairTerm n i j field) hsum_meas
    _ = ∑ i, ∑ j, ∫⁻ field : Combinatorics.Branching.StepField ι PUnit.{1},
        generationPairTerm n i j field
        ∂(μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact lintegral_fintype_sum (μ.fieldLaw : Measure
        (Combinatorics.Branching.StepField ι PUnit.{1}))
        (fun j field => generationPairTerm n i j field)
        (fun j => generationPairTerm_measurable n i j)
    _ = ∑ i, ∑ j, offspringSlotPairWeight μ i j *
        (if i = j then generationSecondMoment μ n else
          generationFirstMoment μ n * generationFirstMoment μ n) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact lintegral_generationPairTerm μ n i j

/-- The slot-pair formula grouped by the first and second factorial moments of
the offspring count. In conventional notation this is
`E[Z_(n+1)^2] = E[K] E[Z_n^2] + E[K(K-1)] E[Z_n]^2`. -/
theorem generationSecondMoment_succ_eq_offspringMoments {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) :
    generationSecondMoment μ (n + 1) =
      offspringMean μ * generationSecondMoment μ n +
        offspringSecondFactorialMoment μ *
          (generationFirstMoment μ n * generationFirstMoment μ n) := by
  classical
  rw [generationSecondMoment_succ_eq_slotPairSum]
  have hrow (i : ι) :
      (∑ j, offspringSlotPairWeight μ i j *
        (if i = j then generationSecondMoment μ n else
          generationFirstMoment μ n * generationFirstMoment μ n)) =
      offspringSlotWeight μ i * generationSecondMoment μ n +
        (∑ j, if i = j then 0 else offspringSlotPairWeight μ i j) *
          (generationFirstMoment μ n * generationFirstMoment μ n) := by
    calc
      _ = ∑ j,
          ((if i = j then offspringSlotPairWeight μ i j *
              generationSecondMoment μ n else 0) +
            (if i = j then 0 else offspringSlotPairWeight μ i j) *
              (generationFirstMoment μ n * generationFirstMoment μ n)) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : i = j <;> simp [hij]
      _ = (∑ j, if i = j then offspringSlotPairWeight μ i j *
              generationSecondMoment μ n else 0) +
          (∑ j, if i = j then 0 else offspringSlotPairWeight μ i j) *
            (generationFirstMoment μ n * generationFirstMoment μ n) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      _ = offspringSlotWeight μ i * generationSecondMoment μ n +
          (∑ j, if i = j then 0 else offspringSlotPairWeight μ i j) *
            (generationFirstMoment μ n * generationFirstMoment μ n) := by
        simp [offspringSlotPairWeight_self]
  calc
    _ = ∑ i, (offspringSlotWeight μ i * generationSecondMoment μ n +
          (∑ j, if i = j then 0 else offspringSlotPairWeight μ i j) *
            (generationFirstMoment μ n * generationFirstMoment μ n)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hrow i
    _ = offspringMean μ * generationSecondMoment μ n +
        offspringSecondFactorialMoment μ *
          (generationFirstMoment μ n * generationFirstMoment μ n) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        offspringMean, offspringSecondFactorialMoment]

/-- The finite-slot second-moment recursion after conversion to real-valued
moments. The finiteness needed by `ENNReal.toReal` follows from the fixed
finite-generation population bound and the finite number of offspring slots.
This is the actual-law interface for real-valued growth estimates. -/
theorem generationSecondMomentReal_succ_eq_offspringMoments {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) :
    (generationSecondMoment μ (n + 1)).toReal =
      (offspringMean μ).toReal * (generationSecondMoment μ n).toReal +
        (offspringSecondFactorialMoment μ).toReal *
          (generationFirstMoment μ n).toReal ^ 2 := by
  have hmean : offspringMean μ < ∞ := by
    have hmean_eq : generationFirstMoment μ 1 = offspringMean μ := by
      rw [generationFirstMoment_succ_eq_offspringMean,
        generationFirstMoment_zero, mul_one]
    rw [← hmean_eq]
    exact generationFirstMoment_lt_top μ 1
  have hfactorial : offspringSecondFactorialMoment μ < ∞ := by
    rw [offspringSecondFactorialMoment]
    refine ENNReal.sum_lt_top.mpr fun i hi => ?_
    refine ENNReal.sum_lt_top.mpr fun j hj => ?_
    by_cases hij : i = j
    · simp [hij]
    · simpa [hij] using
        (lt_of_le_of_lt (offspringSlotPairWeight_le_one μ i j) (by simp))
  have hsecond : generationSecondMoment μ n < ∞ :=
    generationSecondMoment_lt_top μ n
  have hfirst : generationFirstMoment μ n < ∞ :=
    generationFirstMoment_lt_top μ n
  have hterm₁ : offspringMean μ * generationSecondMoment μ n < ∞ :=
    ENNReal.mul_lt_top hmean hsecond
  have hterm₂ : offspringSecondFactorialMoment μ *
      (generationFirstMoment μ n * generationFirstMoment μ n) < ∞ := by
    apply ENNReal.mul_lt_top hfactorial
    exact ENNReal.mul_lt_top hfirst hfirst
  rw [generationSecondMoment_succ_eq_offspringMoments]
  rw [ENNReal.toReal_add hterm₁.ne hterm₂.ne,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul]
  ring
end ProbabilityTheory.BranchingProcess.GaltonWatson

end
