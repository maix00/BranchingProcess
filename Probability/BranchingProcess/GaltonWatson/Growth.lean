/-
Copyright (c) 2026 WANG Yiyang.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Probability.BranchingProcess.GaltonWatson.Generation
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Probability.MeasureTheory.Moments.PaleyZygmund

/-!
# Finite second-moment growth estimates for Galton--Watson generations

This module isolates the finite-horizon second-moment argument used for a
bounded offspring truncation. It does not assume a second moment for the
untruncated offspring law. The actual finite-slot Galton--Watson generation
moments are computed from the presampled offspring-field product law below;
the general real-valued Paley--Zygmund inequality is in
`Probability/MeasureTheory/Moments/PaleyZygmund.lean`.

* `generationFirstMoment_succ_eq_offspringMean` and
  `generationFirstMoment_eq_offspringMean_pow` give
  `𝔼[Z_(n+1)] = ρ * 𝔼[Z_n]` and `𝔼[Z_n] = ρ^n`.
* `generationSecondMoment_succ_eq_offspringMoments` gives
  `𝔼[Z_(n+1)^2] = 𝔼[K] * 𝔼[Z_n^2] + 𝔼[K(K-1)] * 𝔼[Z_n]^2`.
* `normalizedSecondMoment_le_of_recursion` bounds
  `m₂(n) / ρ^(2*n) ≤ 1 + variance / (ρ * (ρ - 1))` under the displayed
  second-moment recursion.
* `measure_generationSizeReal_ge_threshold_of_moments` transfers the general
  Paley--Zygmund estimate to the actual finite-slot generation law.
* `measure_generation_ge_half_mean_of_moment_recursion` and
  `measure_generation_ge_floor_rpow_of_moment_recursion` give lower bounds on
  reaching half the mean and a floor power threshold, respectively.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingProcess.GaltonWatson

/-- The extended-real value of one generation count, viewed on the sampled
offspring field. -/
noncomputable def generationFieldValue {ι : Type*}
    (n : ℕ) (field : Combinatorics.Branching.StepField ι PUnit.{1}) : ℝ≥0∞ :=
  ENat.toENNReal
    ((Combinatorics.Branching.branchingOfStepField field).generationSize n)

private noncomputable def offspringActiveSlot {ι : Type*}
    (step : Combinatorics.Branching.Step ι PUnit.{1}) (i : ι) : ℝ≥0∞ := by
  classical
  exact if Combinatorics.Branching.survive step i then 1 else 0

/-- The probability weight of a fixed root child slot. -/
noncomputable def offspringSlotWeight {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (i : ι) : ℝ≥0∞ :=
  by
    classical
    exact ∫⁻ ξ : Combinatorics.Branching.Step ι PUnit.{1},
      (if Combinatorics.Branching.survive ξ i then 1 else 0) ∂(μ : Measure _)

private noncomputable def generationSingleTerm {ι : Type*}
    (n : ℕ) (i : ι)
    (field : Combinatorics.Branching.StepField ι PUnit.{1}) : ℝ≥0∞ :=
  offspringActiveSlot (field []) i *
    generationFieldValue n (childSubtreeField field i)

private noncomputable def generationPairTerm {ι : Type*}
    (n : ℕ) (i j : ι)
    (field : Combinatorics.Branching.StepField ι PUnit.{1}) : ℝ≥0∞ :=
  (offspringActiveSlot (field []) i *
    generationFieldValue n (childSubtreeField field i)) *
  (offspringActiveSlot (field []) j *
    generationFieldValue n (childSubtreeField field j))

private lemma childCount_le_slotCard {ι : Type*} [Fintype ι]
    (ξ : Combinatorics.Branching.Step ι PUnit.{1}) :
    ξ.childCount ≤ (Fintype.card ι : ℕ∞) := by
  unfold Combinatorics.Branching.Step.childCount
  calc
    (Combinatorics.Branching.support ξ).encard ≤ ENat.card ι := Set.encard_le_card
    _ = (Fintype.card ι : ℕ∞) := by simp

private lemma generationSize_le_slotCard_pow {ι : Type*} [Fintype ι]
    (β : Combinatorics.Branching.Process ι) (n : ℕ) :
    β.generationSize n ≤ (Fintype.card ι : ℕ∞) ^ n := by
  induction n with
  | zero => simp [Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize_zero]
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

/-- The first moment of a generation under the actual presampled
Galton--Watson law. -/
noncomputable def generationFirstMoment {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ β : Combinatorics.Branching.Process ι,
    ENat.toENNReal (β.generationSize n) ∂(law μ : Measure _)

/-- The second moment of a generation under the actual presampled
Galton--Watson law. -/
noncomputable def generationSecondMoment {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ β : Combinatorics.Branching.Process ι,
    ENat.toENNReal (β.generationSize n) ^ 2 ∂(law μ : Measure _)

/-- The real-valued generation-size observation. For a finite slot type every
generation is finite, so the `toReal` conversion agrees with its usual natural
number value. -/
noncomputable def generationSizeReal {ι : Type*}
    (n : ℕ) (β : Combinatorics.Branching.Process ι) : ℝ :=
  (ENat.toENNReal (β.generationSize n)).toReal

private lemma generationSizeENNReal_le_slotCard_pow {ι : Type*} [Fintype ι]
    (β : Combinatorics.Branching.Process ι) (n : ℕ) :
    ENat.toENNReal (β.generationSize n) ≤ (Fintype.card ι : ℝ≥0∞) ^ n := by
  calc
    ENat.toENNReal (β.generationSize n) ≤
        ENat.toENNReal ((Fintype.card ι : ℕ∞) ^ n) :=
      ENat.toENNReal_mono (generationSize_le_slotCard_pow β n)
    _ = (Fintype.card ι : ℝ≥0∞) ^ n := by simp [ENat.toENNReal_coe]

private lemma generationSizeENNReal_lt_top {ι : Type*} [Fintype ι]
    (β : Combinatorics.Branching.Process ι) (n : ℕ) :
    ENat.toENNReal (β.generationSize n) < ∞ := by
  exact lt_of_le_of_lt (generationSizeENNReal_le_slotCard_pow β n) (by simp)

private lemma generationFirstMoment_lt_top {ι : Type*} [Fintype ι]
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

private lemma generationSecondMoment_lt_top {ι : Type*} [Fintype ι]
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

theorem generationSizeReal_measurable {ι : Type*} [Countable ι]
    (n : ℕ) : Measurable (generationSizeReal (ι := ι) n) := by
  exact ENNReal.measurable_toReal.comp
    ((measurable_of_countable _).comp (generationSize_measurable n))

private lemma generationSizeReal_nonneg {ι : Type*} [Fintype ι]
    (n : ℕ) (β : Combinatorics.Branching.Process ι) :
    0 ≤ generationSizeReal n β := ENNReal.toReal_nonneg

private lemma generationSizeReal_le_slotCard_pow {ι : Type*} [Fintype ι]
    (n : ℕ) (β : Combinatorics.Branching.Process ι) :
    generationSizeReal n β ≤ (Fintype.card ι : ℝ) ^ n := by
  have htop : (Fintype.card ι : ℝ≥0∞) ^ n ≠ ∞ := by simp
  have h := ENNReal.toReal_mono htop (generationSizeENNReal_le_slotCard_pow β n)
  simpa [generationSizeReal, ENNReal.toReal_pow] using h

/-- At a fixed generation, finite offspring slots give a deterministic real
bound, hence an `L²` generation-size observation under the actual process law.
This requires no positivity assumption on the offspring count. -/
theorem generationSizeReal_memLp_two {ι : Type*} [Fintype ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) :
    MemLp (generationSizeReal (ι := ι) n) 2 (law μ : Measure _) := by
  apply MemLp.of_bound (generationSizeReal_measurable n).aestronglyMeasurable _
  filter_upwards [] with β
  rw [Real.norm_eq_abs, abs_of_nonneg (generationSizeReal_nonneg n β)]
  exact generationSizeReal_le_slotCard_pow n β

/-- Integrability follows from the fixed-generation `L²` bound. -/
theorem generationSizeReal_integrable {ι : Type*} [Fintype ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) :
    Integrable (generationSizeReal (ι := ι) n) (law μ : Measure _) :=
  (generationSizeReal_memLp_two μ n).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)

/-- Convert the actual extended first moment to the real-valued integral used
by Paley--Zygmund. -/
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

/-- A root-slot pair has this weight in the second-moment expansion. On the
diagonal this is the probability the slot is present; off the diagonal it is
the probability both slots are present. -/
noncomputable def offspringSlotPairWeight {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (i j : ι) : ℝ≥0∞ :=
  by
    classical
    exact ∫⁻ ξ : Combinatorics.Branching.Step ι PUnit.{1},
      (if Combinatorics.Branching.survive ξ i then 1 else 0) *
        (if Combinatorics.Branching.survive ξ j then 1 else 0) ∂(μ : Measure _)

/-- Mean offspring number in a finite-slot configuration law, expressed as
the sum of its child-slot presence probabilities. -/
noncomputable def offspringMean {ι : Type*} [Fintype ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) : ℝ≥0∞ :=
  ∑ i, offspringSlotWeight μ i

/-- Second factorial moment of the number of present offspring slots. -/
noncomputable def offspringSecondFactorialMoment {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) : ℝ≥0∞ :=
  ∑ i, ∑ j, if i = j then 0 else offspringSlotPairWeight μ i j

private lemma offspringSlotPairWeight_le_one {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (i j : ι) : offspringSlotPairWeight μ i j ≤ 1 := by
  classical
  unfold offspringSlotPairWeight
  calc
    _ ≤ ∫⁻ _ : Combinatorics.Branching.Step ι PUnit.{1}, (1 : ℝ≥0∞)
        ∂(μ : Measure _) := by
      apply lintegral_mono_ae
      filter_upwards [] with ξ
      by_cases hi : Combinatorics.Branching.survive ξ i <;>
        by_cases hj : Combinatorics.Branching.survive ξ j <;>
        simp [hi, hj]
    _ = 1 := by simp

private lemma offspringSlotPairWeight_ne_top {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (i j : ι) : offspringSlotPairWeight μ i j ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (offspringSlotPairWeight_le_one μ i j) (by simp))

private lemma offspringSlotPairWeight_self {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (i : ι) :
    offspringSlotPairWeight μ i i = offspringSlotWeight μ i := by
  classical
  unfold offspringSlotPairWeight offspringSlotWeight
  apply lintegral_congr_ae
  filter_upwards [] with ξ
  by_cases hs : Combinatorics.Branching.survive ξ i <;> simp [hs]

private lemma generationFieldValue_measurable {ι : Type*} [Countable ι]
    (n : ℕ) :
    Measurable (generationFieldValue (ι := ι) n) := by
  have hcast : Measurable (fun x : ℕ∞ => ENat.toENNReal x) :=
    measurable_of_countable _
  exact hcast.comp ((generationSize_measurable n).comp
    Combinatorics.Branching.measurable_branchingOfStepField)

private lemma offspringActiveSlot_measurable {ι : Type*} (i : ι) :
    Measurable (offspringActiveSlot (ι := ι) · i) := by
  classical
  unfold offspringActiveSlot
  exact Measurable.ite (Combinatorics.Branching.survive_measurableSet i)
    measurable_const measurable_const

private lemma generationSingleTerm_measurable {ι : Type*} [Countable ι]
    (n : ℕ) (i : ι) : Measurable (generationSingleTerm (ι := ι) n i) := by
  unfold generationSingleTerm
  have hroot : Measurable
      (fun field : Combinatorics.Branching.StepField ι PUnit.{1} =>
        offspringActiveSlot (field []) i) :=
    (offspringActiveSlot_measurable (ι := ι) i).comp (measurable_pi_apply [])
  have hchild : Measurable
      (fun field : Combinatorics.Branching.StepField ι PUnit.{1} =>
        generationFieldValue n (childSubtreeField field i)) :=
    (generationFieldValue_measurable (ι := ι) n).comp
      (ProbabilityTheory.BranchingRandomWalk.subtreeStepField_measurable [i])
  exact hroot.mul hchild

private lemma generationPairTerm_measurable {ι : Type*} [Countable ι]
    (n : ℕ) (i j : ι) :
    Measurable (generationPairTerm (ι := ι) n i j) := by
  unfold generationPairTerm
  have hroot (i : ι) : Measurable
      (fun field : Combinatorics.Branching.StepField ι PUnit.{1} =>
        offspringActiveSlot (field []) i) :=
    (offspringActiveSlot_measurable (ι := ι) i).comp (measurable_pi_apply [])
  have hchild : ∀ i, Measurable
      (fun field : Combinatorics.Branching.StepField ι PUnit.{1} =>
        generationFieldValue n (childSubtreeField field i)) := by
    intro i
    exact (generationFieldValue_measurable (ι := ι) n).comp
      (ProbabilityTheory.BranchingRandomWalk.subtreeStepField_measurable [i])
  exact (hroot i).mul (hchild i) |>.mul ((hroot j).mul (hchild j))

/-- A generation moment on the presampled configuration law can be computed
on its underlying independent offspring field. -/
theorem generationFirstMoment_eq_fieldLaw {ι : Type*} [Countable ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) :
    generationFirstMoment μ n =
      ∫⁻ field : Combinatorics.Branching.StepField ι PUnit.{1},
        generationFieldValue n field ∂(μ.fieldLaw : Measure _) := by
  have hgen : Measurable (fun β : Combinatorics.Branching.Process ι =>
      ENat.toENNReal (β.generationSize n)) :=
    (measurable_of_countable _).comp (generationSize_measurable n)
  rw [generationFirstMoment, law, ProbabilityMeasure.toMeasure_map]
  exact lintegral_map hgen Combinatorics.Branching.measurable_branchingOfStepField

/-- The same change of variables for the second generation moment. -/
theorem generationSecondMoment_eq_fieldLaw {ι : Type*} [Countable ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) :
    generationSecondMoment μ n =
      ∫⁻ field : Combinatorics.Branching.StepField ι PUnit.{1},
        generationFieldValue n field ^ 2 ∂(μ.fieldLaw : Measure _) := by
  have hgen : Measurable (fun β : Combinatorics.Branching.Process ι =>
      ENat.toENNReal (β.generationSize n) ^ 2) :=
    ((measurable_of_countable _).comp (generationSize_measurable n)).pow_const 2
  rw [generationSecondMoment, law, ProbabilityMeasure.toMeasure_map]
  exact lintegral_map hgen Combinatorics.Branching.measurable_branchingOfStepField

private lemma lintegral_generationSingleTerm {ι : Type*} [Countable ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) (i : ι) :
    ∫⁻ field : Combinatorics.Branching.StepField ι PUnit.{1},
      generationSingleTerm n i field
      ∂(μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})) =
      offspringSlotWeight μ i * generationFirstMoment μ n := by
  classical
  let J : Combinatorics.Branching.StepField ι PUnit.{1} →
      Combinatorics.Branching.Step ι PUnit.{1} ×
        (ι → Combinatorics.Branching.StepField ι PUnit.{1}) :=
    fun field => (field [], childSubtreeVector field)
  have hJ : Measurable J := by
    apply Measurable.prodMk
    · exact measurable_pi_apply []
    · exact childSubtreeVector_measurable
  let g : Combinatorics.Branching.Step ι PUnit.{1} ×
      (ι → Combinatorics.Branching.StepField ι PUnit.{1}) → ℝ≥0∞ :=
    fun p => offspringActiveSlot p.1 i * generationFieldValue n (p.2 i)
  have hg : Measurable g := by
    have hroot : Measurable
        (fun s : Combinatorics.Branching.Step ι PUnit.{1} =>
          offspringActiveSlot s i) := offspringActiveSlot_measurable i
    have hchild : Measurable
        (fun v : ι → Combinatorics.Branching.StepField ι PUnit.{1} =>
          generationFieldValue n (v i)) :=
      (generationFieldValue_measurable (ι := ι) n).comp (measurable_pi_apply i)
    exact hroot.comp measurable_fst |>.mul (hchild.comp measurable_snd)
  have hterm :
      (fun field : Combinatorics.Branching.StepField ι PUnit.{1} =>
        generationSingleTerm n i field) = g ∘ J := by
    funext field
    simp [generationSingleTerm, g, J, childSubtreeVector]
  calc
    _ = ∫⁻ p, g p ∂Measure.map J
        (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})) := by
      rw [hterm]
      symm
      exact lintegral_map hg hJ
    _ = ∫⁻ p, g p ∂(μ : Measure (Combinatorics.Branching.Step ι PUnit.{1})).prod
        (Measure.infinitePi fun _ : ι =>
          (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1}))) := by
      rw [fieldLaw_root_childSubtrees_jointLaw]
    _ = offspringSlotWeight μ i *
        (∫⁻ v : ι → Combinatorics.Branching.StepField ι PUnit.{1},
          generationFieldValue n (v i)
          ∂Measure.infinitePi (fun _ : ι =>
            (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})))) := by
      unfold g
      have hroot : Measurable
          (fun s : Combinatorics.Branching.Step ι PUnit.{1} =>
            offspringActiveSlot s i) := offspringActiveSlot_measurable i
      have hchild : Measurable
          (fun v : ι → Combinatorics.Branching.StepField ι PUnit.{1} =>
            generationFieldValue n (v i)) :=
        (generationFieldValue_measurable (ι := ι) n).comp (measurable_pi_apply i)
      simpa [offspringSlotWeight, offspringActiveSlot] using lintegral_prod_mul
        (μ := (μ : Measure (Combinatorics.Branching.Step ι PUnit.{1})))
        (ν := Measure.infinitePi fun _ : ι =>
          (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})))
        hroot.aemeasurable hchild.aemeasurable
    _ = offspringSlotWeight μ i * generationFirstMoment μ n := by
      congr 1
      have heval := Measure.infinitePi_map_eval
        (fun _ : ι => (μ.fieldLaw : Measure
          (Combinatorics.Branching.StepField ι PUnit.{1}))) i
      have hmap := lintegral_map
        (μ := Measure.infinitePi (fun _ : ι =>
          (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1}))))
        (f := fun f => generationFieldValue n f)
        (g := fun v : ι → Combinatorics.Branching.StepField ι PUnit.{1} => v i)
        (generationFieldValue_measurable (ι := ι) n) (measurable_pi_apply i)
      rw [← hmap, heval, ← generationFirstMoment_eq_fieldLaw μ n]

/-- Under the independent child-subtree field, a single generation value has
the actual Galton--Watson generation moment. -/
private lemma lintegral_childSubtree_pair {ι : Type*} [Countable ι]
    [DecidableEq ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) (i j : ι) :
    ∫⁻ v : ι → Combinatorics.Branching.StepField ι PUnit.{1},
      generationFieldValue n (v i) * generationFieldValue n (v j)
      ∂Measure.infinitePi (fun _ : ι =>
        (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1}))) =
      if i = j then generationSecondMoment μ n else
        generationFirstMoment μ n * generationFirstMoment μ n := by
  classical
  by_cases hij : i = j
  · subst j
    have heval := Measure.infinitePi_map_eval
      (fun _ : ι => (μ.fieldLaw : Measure
        (Combinatorics.Branching.StepField ι PUnit.{1}))) i
    have hm := (generationFieldValue_measurable (ι := ι) n).pow_const 2
    calc
      _ = ∫⁻ f, generationFieldValue n f ^ 2 ∂Measure.map
          (fun v : ι → Combinatorics.Branching.StepField ι PUnit.{1} => v i)
          (Measure.infinitePi (fun _ : ι =>
            (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})))) := by
        have hmapInt := lintegral_map
          (μ := Measure.infinitePi (fun _ : ι =>
            (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1}))))
          (f := fun f => generationFieldValue n f ^ 2)
          (g := fun v : ι → Combinatorics.Branching.StepField ι PUnit.{1} => v i)
          hm (measurable_pi_apply i)
        simpa [pow_two] using hmapInt.symm
      _ = ∫⁻ f, generationFieldValue n f ^ 2
          ∂(μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})) := by
        rw [heval]
      _ = if i = i then generationSecondMoment μ n else _ := by
        simp [generationSecondMoment_eq_fieldLaw]
  · have hmap := Measure.infinitePi_map_eval_prod
      (P := fun _ : ι => (μ.fieldLaw : Measure
        (Combinatorics.Branching.StepField ι PUnit.{1}))) hij
    have hm : Measurable (fun p :
        Combinatorics.Branching.StepField ι PUnit.{1} ×
          Combinatorics.Branching.StepField ι PUnit.{1} =>
        generationFieldValue n p.1 * generationFieldValue n p.2) :=
      (generationFieldValue_measurable (ι := ι) n).comp measurable_fst |>.mul
        ((generationFieldValue_measurable (ι := ι) n).comp measurable_snd)
    have hmp : Measurable
        (fun v : ι → Combinatorics.Branching.StepField ι PUnit.{1} => (v i, v j)) := by
      fun_prop
    calc
      _ = ∫⁻ p, generationFieldValue n p.1 * generationFieldValue n p.2
          ∂Measure.map (fun v : ι → Combinatorics.Branching.StepField ι PUnit.{1} =>
            (v i, v j)) (Measure.infinitePi (fun _ : ι =>
              (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})))) := by
        exact (lintegral_map
          (μ := Measure.infinitePi (fun _ : ι =>
            (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1}))))
          (f := fun p : Combinatorics.Branching.StepField ι PUnit.{1} ×
            Combinatorics.Branching.StepField ι PUnit.{1} =>
            generationFieldValue n p.1 * generationFieldValue n p.2)
          (g := fun v : ι → Combinatorics.Branching.StepField ι PUnit.{1} =>
            (v i, v j)) hm hmp).symm
      _ = ∫⁻ p, generationFieldValue n p.1 * generationFieldValue n p.2
          ∂(μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})).prod
            (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})) := by
        rw [hmap]
      _ = generationFirstMoment μ n * generationFirstMoment μ n := by
        calc
          _ = (∫⁻ f, generationFieldValue n f
                ∂(μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1}))) *
              ∫⁻ f, generationFieldValue n f
                ∂(μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})) :=
            lintegral_prod_mul
              (generationFieldValue_measurable (ι := ι) n).aemeasurable
              (generationFieldValue_measurable (ι := ι) n).aemeasurable
          _ = generationFirstMoment μ n * generationFirstMoment μ n := by
            rw [← generationFirstMoment_eq_fieldLaw μ n]
      _ = if i = j then _ else _ := by simp [hij]

private lemma lintegral_generationPairTerm {ι : Type*} [Countable ι]
    [DecidableEq ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) (i j : ι) :
    ∫⁻ field : Combinatorics.Branching.StepField ι PUnit.{1},
      (offspringActiveSlot (field []) i *
        generationFieldValue n (childSubtreeField field i)) *
      (offspringActiveSlot (field []) j *
        generationFieldValue n (childSubtreeField field j))
      ∂(μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})) =
      offspringSlotPairWeight μ i j *
        (if i = j then generationSecondMoment μ n else
          generationFirstMoment μ n * generationFirstMoment μ n) := by
  classical
  let J : Combinatorics.Branching.StepField ι PUnit.{1} →
      Combinatorics.Branching.Step ι PUnit.{1} ×
        (ι → Combinatorics.Branching.StepField ι PUnit.{1}) :=
    fun field => (field [], childSubtreeVector field)
  have hJ : Measurable J := by
    apply Measurable.prodMk
    · exact measurable_pi_apply []
    · exact childSubtreeVector_measurable
  let g : Combinatorics.Branching.Step ι PUnit.{1} ×
      (ι → Combinatorics.Branching.StepField ι PUnit.{1}) → ℝ≥0∞ :=
    fun p =>
      (offspringActiveSlot p.1 i * offspringActiveSlot p.1 j) *
        (generationFieldValue n (p.2 i) * generationFieldValue n (p.2 j))
  have hg : Measurable g := by
    have hroot : Measurable (fun s : Combinatorics.Branching.Step ι PUnit.{1} =>
        offspringActiveSlot s i * offspringActiveSlot s j) :=
      (offspringActiveSlot_measurable i).mul (offspringActiveSlot_measurable j)
    have hchild : Measurable
        (fun v : ι → Combinatorics.Branching.StepField ι PUnit.{1} =>
          generationFieldValue n (v i) * generationFieldValue n (v j)) := by
      exact (generationFieldValue_measurable (ι := ι) n).comp
          (measurable_pi_apply i) |>.mul
        ((generationFieldValue_measurable (ι := ι) n).comp
          (measurable_pi_apply j))
    exact (hroot.comp measurable_fst).mul (hchild.comp measurable_snd)
  have hterm :
      (fun field : Combinatorics.Branching.StepField ι PUnit.{1} =>
        (offspringActiveSlot (field []) i *
          generationFieldValue n (childSubtreeField field i)) *
        (offspringActiveSlot (field []) j *
          generationFieldValue n (childSubtreeField field j))) = g ∘ J := by
    funext field
    simp [g, J, childSubtreeVector]
    ac_rfl
  calc
    _ = ∫⁻ p, g p ∂Measure.map J
        (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})) := by
      rw [hterm]
      symm
      exact lintegral_map hg hJ
    _ = ∫⁻ p, g p ∂(μ : Measure (Combinatorics.Branching.Step ι PUnit.{1})).prod
        (Measure.infinitePi fun _ : ι =>
          (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1}))) := by
      rw [fieldLaw_root_childSubtrees_jointLaw]
    _ = offspringSlotPairWeight μ i j *
        (∫⁻ v : ι → Combinatorics.Branching.StepField ι PUnit.{1},
          generationFieldValue n (v i) * generationFieldValue n (v j)
          ∂Measure.infinitePi (fun _ : ι =>
            (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})))) := by
      unfold g
      have hroot : Measurable (fun s : Combinatorics.Branching.Step ι PUnit.{1} =>
          offspringActiveSlot s i * offspringActiveSlot s j) :=
        (offspringActiveSlot_measurable i).mul (offspringActiveSlot_measurable j)
      have hchild : Measurable
          (fun v : ι → Combinatorics.Branching.StepField ι PUnit.{1} =>
            generationFieldValue n (v i) * generationFieldValue n (v j)) := by
        exact (generationFieldValue_measurable (ι := ι) n).comp
            (measurable_pi_apply i) |>.mul
          ((generationFieldValue_measurable (ι := ι) n).comp
            (measurable_pi_apply j))
      exact lintegral_prod_mul hroot.aemeasurable hchild.aemeasurable
    _ = offspringSlotPairWeight μ i j *
        (if i = j then generationSecondMoment μ n else
          generationFirstMoment μ n * generationFirstMoment μ n) := by
      rw [lintegral_childSubtree_pair]

private lemma enat_toENNReal_fintype_sum {ι : Type*} [Fintype ι]
    (f : ι → ℕ∞) :
    ENat.toENNReal (∑ i, f i) = ∑ i, ENat.toENNReal (f i) := by
  classical
  change ENat.toENNReal (Finset.univ.sum f) =
    Finset.univ.sum (fun i => ENat.toENNReal (f i))
  have hsum (s : Finset ι) :
      ENat.toENNReal (s.sum f) = s.sum (fun i => ENat.toENNReal (f i)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simp [Finset.sum_insert, hi, ENat.toENNReal_add, ih]
  exact hsum Finset.univ

private lemma generationFieldValue_succ_eq_sum {ι : Type*} [Fintype ι]
    (field : Combinatorics.Branching.StepField ι PUnit.{1}) (n : ℕ) :
    generationFieldValue (n + 1) field =
      ∑ i, offspringActiveSlot (field []) i *
        generationFieldValue n (childSubtreeField field i) := by
  classical
  change ENat.toENNReal
      ((Combinatorics.Branching.branchingOfStepField field).generationSize (n + 1)) = _
  rw [generationSize_succ_eq_sum_childSubtreeSlots field n]
  rw [enat_toENNReal_fintype_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hs : Combinatorics.Branching.survive (field []) i
  · simp [offspringActiveSlot, hs, generationFieldValue]
  · simp [offspringActiveSlot, hs]

private lemma lintegral_fintype_sum {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (ν : Measure Ω) (f : ι → Ω → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∑ i, f i x ∂ν = ∑ i, ∫⁻ x, f i x ∂ν := by
  classical
  exact lintegral_finsetSum (Finset.univ : Finset ι) (fun i _ => hf i)

/-- The actual first-moment recursion for the finite-slot offspring model. -/
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

/-- The initial generation consists of the single root. -/
theorem generationFirstMoment_zero {ι : Type*} [Countable ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) : generationFirstMoment μ 0 = 1 := by
  rw [generationFirstMoment]
  simp [Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize_zero]

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

/-- The actual second-moment recursion for a finite offspring-slot model.
The summands are weighted by the probabilities that the indicated root slots
are present. The diagonal terms use the generation second moment; distinct
slots use the square of the generation first moment, by independence of the
presampled child-subtree fields. This is proved from `law μ` and its product
field representation, rather than assumed as a recursion. -/
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


/-- The second-moment constant obtained from the Galton--Watson recursion. -/
noncomputable def normalizedSecondMomentConstant (ρ variance : ℝ) : ℝ :=
  1 + variance / (ρ * (ρ - 1))

/-- A reproduction variable bounded by two has a finite second moment controlled
by its first moment. This is the estimate that makes an offspring truncation
usable even when the original offspring count has no second moment. -/
theorem integral_sq_le_two_mul_integral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ) (hXmeas : Measurable X)
    (hX_nonneg : 0 ≤ᵐ[μ] X) (hX_le_two : X ≤ᵐ[μ] fun _ => 2) :
    ∫ ω, X ω ^ 2 ∂μ ≤ 2 * ∫ ω, X ω ∂μ := by
  have hX_memLp : MemLp X 2 μ :=
    MemLp.of_bound hXmeas.aestronglyMeasurable 2 <| by
      filter_upwards [hX_nonneg, hX_le_two] with ω hnonneg hle
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact hle
  have hX_integrable : Integrable X μ :=
    hX_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hX2_integrable : Integrable (fun ω => X ω ^ 2) μ := hX_memLp.integrable_sq
  have hscaled_integrable : Integrable (fun ω => (2 : ℝ) * X ω) μ := by
    change Integrable (fun ω => (2 : ℝ) • X ω) μ
    exact hX_integrable.smul (2 : ℝ)
  have hpointwise : (fun ω => X ω ^ 2) ≤ᵐ[μ] fun ω => (2 : ℝ) * X ω := by
    filter_upwards [hX_nonneg, hX_le_two] with ω hnonneg hle
    nlinarith [mul_nonneg hnonneg (show 0 ≤ 2 - X ω by linarith)]
  calc
    ∫ ω, X ω ^ 2 ∂μ ≤ ∫ ω, (2 : ℝ) * X ω ∂μ :=
      integral_mono_ae hX2_integrable hscaled_integrable hpointwise
    _ = 2 * ∫ ω, X ω ∂μ := integral_const_mul 2 X

/-- Here `m₂ n` is the unnormalized population second moment `E[Zₙ²]`, and
`variance` is the offspring-count variance. The recursion is the standard
population second-moment recursion. Dividing by `ρ^(2*n)` bounds the second
moment of the normalized population martingale by
`1 + variance / (ρ * (ρ - 1))`. -/
theorem normalizedSecondMoment_le_of_recursion
    (ρ variance : ℝ) (hρ : 1 < ρ) (hvariance : 0 ≤ variance)
    (m₂ : ℕ → ℝ) (hm₂_zero : m₂ 0 = 1)
    (hm₂_succ : ∀ n, m₂ (n + 1) = ρ ^ 2 * m₂ n + variance * ρ ^ n) :
    ∀ n, m₂ n / ρ ^ (2 * n) ≤ normalizedSecondMomentConstant ρ variance := by
  have hρpos : 0 < ρ := by linarith
  have hρne : ρ ≠ 0 := hρpos.ne'
  have hρsubpos : 0 < ρ - 1 := by linarith
  let c : ℝ := variance / (ρ * (ρ - 1))
  let stage : ℕ → ℝ := fun n => 1 + c * (1 - (ρ ^ n)⁻¹)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hstage_zero : stage 0 = 1 := by simp [stage]
  have hstage_succ (n : ℕ) :
      stage (n + 1) = stage n + variance / ρ ^ (n + 2) := by
    dsimp [stage, c]
    rw [pow_succ]
    field_simp [hρne, pow_ne_zero n hρne]
    ring
  have hm₂_formula (n : ℕ) : m₂ n = ρ ^ (2 * n) * stage n := by
    induction n with
    | zero => simp [hm₂_zero, stage]
    | succ n ih =>
        rw [hm₂_succ n, ih, hstage_succ]
        have hpow : ρ ^ (2 * (n + 1)) = ρ ^ 2 * ρ ^ (2 * n) := by
          rw [Nat.mul_succ, pow_add]
          ring
        rw [hpow]
        have hpow' : ρ ^ (2 * n) = (ρ ^ n) ^ 2 := by
          rw [show 2 * n = n * 2 by omega, pow_mul]
        rw [hpow']
        dsimp [stage, c] at *
        field_simp [hρne, hρsubpos.ne', pow_ne_zero n hρne]
        ring
  intro n
  rw [hm₂_formula n]
  have hpowpos : 0 < ρ ^ n := pow_pos hρpos _
  have hinv_nonneg : 0 ≤ (ρ ^ n)⁻¹ := inv_nonneg.mpr hpowpos.le
  have hpow_ge_one : 1 ≤ ρ ^ n := one_le_pow₀ hρ.le
  have hinv_le_one : (ρ ^ n)⁻¹ ≤ 1 := (inv_le_one₀ hpowpos).2 hpow_ge_one
  have hstage_le : stage n ≤ 1 + c := by
    dsimp [stage]
    nlinarith [mul_nonneg hc_nonneg hinv_nonneg]
  have hden : ρ ^ (2 * n) ≠ 0 := pow_ne_zero _ hρne
  rw [mul_div_cancel_left₀ _ hden]
  calc
    stage n ≤ 1 + c := hstage_le
    _ = normalizedSecondMomentConstant ρ variance := by
      simp [normalizedSecondMomentConstant, c]

/-- Paley--Zygmund applied to the actual finite-slot Galton--Watson
generation count. The conversion from the model's ENNReal moments to real
integrals is supplied by the fixed-generation bounds above. -/
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

/-- The normalized second-moment recursion also gives the elementary lower
bound `E[Zₙ²] ≥ (E[Zₙ])²`. -/
theorem rho_pow_sq_le_secondMoment_of_recursion
    (ρ variance : ℝ) (hρ : 1 < ρ) (hvariance : 0 ≤ variance)
    (m₂ : ℕ → ℝ) (hm₂_zero : m₂ 0 = 1)
    (hm₂_succ : ∀ n, m₂ (n + 1) = ρ ^ 2 * m₂ n + variance * ρ ^ n) :
    ∀ n, ρ ^ (2 * n) ≤ m₂ n := by
  have hρ_nonneg : 0 ≤ ρ := by linarith
  intro n
  induction n with
  | zero => simpa using hm₂_zero.ge
  | succ n ih =>
      have hpow : ρ ^ (2 * (n + 1)) = ρ ^ 2 * ρ ^ (2 * n) := by
        rw [Nat.mul_succ, pow_add]
        ring
      rw [hpow, hm₂_succ n]
      calc
        ρ ^ 2 * ρ ^ (2 * n) ≤ ρ ^ 2 * m₂ n :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg ρ)
        _ ≤ ρ ^ 2 * m₂ n + variance * ρ ^ n :=
          le_add_of_nonneg_right (mul_nonneg hvariance (pow_nonneg hρ_nonneg _))

/-- For any finite-horizon population sequence with the Galton--Watson first
and second moment recursions, Paley--Zygmund gives a uniform lower bound on the
chance to reach half its mean. The theorem is stated for real-valued
observations; a bounded-offspring generation count embeds in this interface
after proving its moment recursions. -/
theorem measure_generation_ge_half_mean_of_moment_recursion
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ variance : ℝ) (hρ : 1 < ρ) (hvariance : 0 ≤ variance)
    (Z : ℕ → Ω → ℝ) (m₂ : ℕ → ℝ)
    (hZmeas : ∀ n, Measurable (Z n))
    (hZ_nonneg : ∀ n, 0 ≤ᵐ[μ] Z n)
    (hZ_integrable : ∀ n, Integrable (Z n) μ)
    (hZ_memLp : ∀ n, MemLp (Z n) 2 μ)
    (hmean : ∀ n, ∫ ω, Z n ω ∂μ = ρ ^ n)
    (hm₂_zero : m₂ 0 = 1)
    (hsecond : ∀ n, ∫ ω, Z n ω ^ 2 ∂μ = m₂ n)
    (hm₂_succ : ∀ n, m₂ (n + 1) = ρ ^ 2 * m₂ n + variance * ρ ^ n)
    (n : ℕ) (threshold : ℝ) (hthreshold : 0 ≤ threshold)
    (hthreshold_le : 2 * threshold ≤ ρ ^ n) :
    (μ.real {ω | threshold ≤ Z n ω}) ≥
      1 / (4 * normalizedSecondMomentConstant ρ variance) := by
  have hρpos : 0 < ρ := by linarith
  have hsecond_lower := rho_pow_sq_le_secondMoment_of_recursion ρ variance hρ
    hvariance m₂ hm₂_zero hm₂_succ n
  have hsecond_pos : 0 < m₂ n := lt_of_lt_of_le (pow_pos hρpos _) hsecond_lower
  have hsecond_ratio := normalizedSecondMoment_le_of_recursion ρ variance hρ
    hvariance m₂ hm₂_zero hm₂_succ n
  have hdenom_pos : 0 < ρ ^ (2 * n) := pow_pos hρpos _
  have hsecond_upper : m₂ n ≤ normalizedSecondMomentConstant ρ variance * ρ ^ (2 * n) :=
    (div_le_iff₀ hdenom_pos).1 hsecond_ratio
  have hpow : ρ ^ (2 * n) = (ρ ^ n) ^ 2 := by
    rw [show 2 * n = n * 2 by omega, pow_mul]
  have hsecond_upper' : m₂ n ≤ normalizedSecondMomentConstant ρ variance * (ρ ^ n) ^ 2 :=
    hpow ▸ hsecond_upper
  have hCpos : 0 < normalizedSecondMomentConstant ρ variance := by
    dsimp [normalizedSecondMomentConstant]
    positivity
  exact measure_ge_threshold_of_secondMoment_le μ (Z n) (hZmeas n)
    (hZ_nonneg n) (hZ_integrable n) (hZ_memLp n) (ρ ^ n) (m₂ n) threshold
    (normalizedSecondMomentConstant ρ variance) (hmean n) (hsecond n)
    hthreshold (pow_pos hρpos n) hthreshold_le hsecond_pos hCpos hsecond_upper'

/-- The logarithmic generation choice used in the finite-horizon growth
estimate reaches twice the target scale. -/
theorem rho_pow_ceil_log_ge_two_mul_rpow
    (ρ a : ℝ) (N : ℕ) (hρ : 1 < ρ) (hN : 1 ≤ N) :
    2 * (N : ℝ) ^ a ≤
      ρ ^ ⌈(a * Real.log N + Real.log 2) / Real.log ρ⌉₊ := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  let q : ℝ := (a * Real.log N + Real.log 2) / Real.log ρ
  have hceil : q ≤ (⌈q⌉₊ : ℕ) := by exact_mod_cast Nat.le_ceil q
  have hmul : a * Real.log N + Real.log 2 ≤ (⌈q⌉₊ : ℕ) * Real.log ρ := by
    dsimp [q] at hceil ⊢
    exact (div_le_iff₀ hlogρ).1 hceil
  have hexp : Real.exp (a * Real.log N + Real.log 2) ≤
      Real.exp ((⌈q⌉₊ : ℕ) * Real.log ρ) := Real.exp_le_exp.mpr hmul
  have hNpow : (N : ℝ) ^ a = Real.exp (a * Real.log N) := by
    rw [Real.rpow_def_of_pos hNpos a]
    congr 1
    ring
  have hleft : Real.exp (a * Real.log N + Real.log 2) = 2 * (N : ℝ) ^ a := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), hNpow]
    ring
  have hright : Real.exp ((⌈q⌉₊ : ℕ) * Real.log ρ) =
      ρ ^ ⌈q⌉₊ := by
    rw [← Real.rpow_natCast ρ ⌈q⌉₊, Real.rpow_def_of_pos (by linarith) _]
    congr 1
    ring
  simpa only [hleft, hright] using hexp

/-- The explicit threshold version of the finite-horizon Galton--Watson
growth estimate. If the generation moments obey the bounded-offspring
recursion, then at
`h_N = ceil ((a log N + log 2) / log ρ)` the population reaches
`floor (N^a)` with a probability bounded away from zero. -/
theorem measure_generation_ge_floor_rpow_of_moment_recursion
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ variance : ℝ) (hρ : 1 < ρ) (hvariance : 0 ≤ variance)
    (Z : ℕ → Ω → ℝ) (m₂ : ℕ → ℝ)
    (hZmeas : ∀ n, Measurable (Z n))
    (hZ_nonneg : ∀ n, 0 ≤ᵐ[μ] Z n)
    (hZ_integrable : ∀ n, Integrable (Z n) μ)
    (hZ_memLp : ∀ n, MemLp (Z n) 2 μ)
    (hmean : ∀ n, ∫ ω, Z n ω ∂μ = ρ ^ n)
    (hm₂_zero : m₂ 0 = 1)
    (hsecond : ∀ n, ∫ ω, Z n ω ^ 2 ∂μ = m₂ n)
    (hm₂_succ : ∀ n, m₂ (n + 1) = ρ ^ 2 * m₂ n + variance * ρ ^ n)
    (N : ℕ) (a : ℝ) (hN : 1 ≤ N) :
    (μ.real {ω | (⌊(N : ℝ) ^ a⌋₊ : ℝ) ≤
      Z ⌈(a * Real.log N + Real.log 2) / Real.log ρ⌉₊ ω}) ≥
      1 / (4 * normalizedSecondMomentConstant ρ variance) := by
  have hNpow_nonneg : 0 ≤ (N : ℝ) ^ a :=
    Real.rpow_nonneg (by positivity : 0 ≤ (N : ℝ)) a
  have hfloor_le : (⌊(N : ℝ) ^ a⌋₊ : ℝ) ≤ (N : ℝ) ^ a := Nat.floor_le hNpow_nonneg
  have hscale : 2 * (⌊(N : ℝ) ^ a⌋₊ : ℝ) ≤
      ρ ^ ⌈(a * Real.log N + Real.log 2) / Real.log ρ⌉₊ := by
    exact (mul_le_mul_of_nonneg_left hfloor_le (by norm_num)).trans
      (rho_pow_ceil_log_ge_two_mul_rpow ρ a N hρ hN)
  exact measure_generation_ge_half_mean_of_moment_recursion μ ρ variance hρ
    hvariance Z m₂ hZmeas hZ_nonneg hZ_integrable hZ_memLp hmean hm₂_zero
    hsecond hm₂_succ _ _ (Nat.cast_nonneg _) hscale

end ProbabilityTheory.BranchingProcess.GaltonWatson

end
