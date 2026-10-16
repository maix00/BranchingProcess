/-
Copyright (c) 2026 WANG Yiyang.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
import Probability.BranchingProcess.GaltonWatson.Growth
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Topology.UnitInterval

/-!
# Finite Galton--Watson growth checks

These checks exercise extinction with a supercritical offspring variable
bounded by two, verify the bounded second-moment estimate without an `L²`
input, and record the strongest concrete generation-law connection currently
available in the Galton--Watson API.
-/

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

namespace ProbabilityTheory.BranchingProcess.GaltonWatson

private def pThreeQuarters : I := ⟨3 / 4, by constructor <;> norm_num⟩

private theorem complement_probability_mass :
    (unitInterval.toNNReal (σ pThreeQuarters) : ℝ≥0∞) =
      ENNReal.ofReal (1 / 4 : ℝ) := by
  have hreal :
      (unitInterval.toNNReal (σ pThreeQuarters) : ℝ) = (1 / 4 : ℝ) := by
    norm_num [unitInterval.coe_toNNReal, pThreeQuarters, unitInterval.coe_symm_eq]
  calc
    (unitInterval.toNNReal (σ pThreeQuarters) : ℝ≥0∞) =
        ENNReal.ofReal (unitInterval.toNNReal (σ pThreeQuarters)) :=
      ENNReal.coe_nnreal_eq _
    _ = ENNReal.ofReal (1 / 4 : ℝ) := congrArg ENNReal.ofReal hreal

/-- A supercritical `{0, 2}` offspring variable. The false outcome is
extinction, with positive probability. -/
noncomputable def boundedOffspringMeasure : Measure Bool :=
  bernoulliMeasure true false pThreeQuarters

noncomputable instance boundedOffspringMeasure.isProbabilityMeasure :
    IsProbabilityMeasure boundedOffspringMeasure := by
  unfold boundedOffspringMeasure
  infer_instance

def boundedOffspring (b : Bool) : ℝ := if b then 2 else 0

theorem boundedOffspring_measurable : Measurable boundedOffspring :=
  measurable_of_countable _

theorem boundedOffspring_memLp : MemLp boundedOffspring 2 boundedOffspringMeasure := by
  apply MemLp.of_bound boundedOffspring_measurable.aestronglyMeasurable 2
  filter_upwards [] with b
  cases b <;> norm_num [boundedOffspring]

theorem boundedOffspring_integral :
    ∫ b, boundedOffspring b ∂boundedOffspringMeasure = 3 / 2 := by
  rw [boundedOffspringMeasure, integral_bernoulliMeasure]
  norm_num [boundedOffspring, pThreeQuarters]

theorem boundedOffspring_sq_integral :
    ∫ b, boundedOffspring b ^ 2 ∂boundedOffspringMeasure = 3 := by
  rw [boundedOffspringMeasure, integral_bernoulliMeasure]
  norm_num [boundedOffspring, pThreeQuarters]

private def noChildren : Combinatorics.Branching.Step (Fin 2) PUnit.{1} :=
  fun _ => none

private def twoChildren : Combinatorics.Branching.Step (Fin 2) PUnit.{1} :=
  fun _ => some PUnit.unit

private noncomputable def boundedOffspringConfigurationLaw :
    ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw (Fin 2) PUnit.{1} :=
  (bernoulliMeasure twoChildren noChildren pThreeQuarters).toProbabilityMeasure

private theorem twoChildren_childCount : twoChildren.childCount = 2 := by
  simp [twoChildren, Combinatorics.Branching.Step.childCount,
    Combinatorics.Branching.support, Combinatorics.Branching.survive]

private theorem noChildren_childCount : noChildren.childCount = 0 := by
  simp [noChildren, Combinatorics.Branching.Step.childCount,
    Combinatorics.Branching.support, Combinatorics.Branching.survive]

private theorem boundedOffspringConfigurationLaw_childCountLaw :
    (boundedOffspringConfigurationLaw.childCountLaw : Measure ℕ∞) =
      bernoulliMeasure (2 : ℕ∞) 0 pThreeQuarters := by
  rw [ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.childCountLaw_toMeasure]
  change Measure.map Combinatorics.Branching.Step.childCount
    (bernoulliMeasure twoChildren noChildren pThreeQuarters) = _
  rw [ProbabilityTheory.map_bernoulliMeasure' twoChildren noChildren
    Combinatorics.Branching.Step.childCount_measurable pThreeQuarters]
  rw [twoChildren_childCount, noChildren_childCount]

example :
    (boundedOffspringConfigurationLaw.childCountLaw : Measure ℕ∞) {0} =
      ENNReal.ofReal (1 / 4 : ℝ) := by
  rw [boundedOffspringConfigurationLaw_childCountLaw]
  rw [ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_mem
    (x := (2 : ℕ∞)) (y := (0 : ℕ∞)) pThreeQuarters
    (MeasurableSet.singleton 0) (by norm_num) (by simp)]
  exact complement_probability_mass

example :
    ((law boundedOffspringConfigurationLaw).map
      (fun β : Combinatorics.Branching.Process (Fin 2) => β.generationSize 1) :
        ProbabilityMeasure ℕ∞) = boundedOffspringConfigurationLaw.childCountLaw :=
  generationSize_one_law boundedOffspringConfigurationLaw

example :
    (((law boundedOffspringConfigurationLaw).map
      (fun β : Combinatorics.Branching.Process (Fin 2) => β.generationSize 1) :
        ProbabilityMeasure ℕ∞) : Measure ℕ∞) {0} = ENNReal.ofReal (1 / 4 : ℝ) := by
  rw [generationSize_one_law]
  exact boundedOffspringConfigurationLaw_childCountLaw ▸ by
    rw [ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_mem
      (x := (2 : ℕ∞)) (y := (0 : ℕ∞)) pThreeQuarters
      (MeasurableSet.singleton 0) (by norm_num) (by simp)]
    exact complement_probability_mass

example :
    ∫ b, boundedOffspring b ^ 2 ∂boundedOffspringMeasure ≤
      2 * ∫ b, boundedOffspring b ∂boundedOffspringMeasure := by
  exact integral_sq_le_two_mul_integral boundedOffspringMeasure boundedOffspring
    boundedOffspring_measurable (ae_of_all _ fun b => by
      cases b <;> norm_num [boundedOffspring])
    (ae_of_all _ fun b => by cases b <;> norm_num [boundedOffspring])

example :
    (boundedOffspringMeasure.real {b | (3 / 4 : ℝ) ≤ boundedOffspring b}) ≥
      3 / 16 := by
  have hnonneg : 0 ≤ᵐ[boundedOffspringMeasure] boundedOffspring :=
    ae_of_all _ fun b => by cases b <;> norm_num [boundedOffspring]
  have hmean :
      ∫ b, boundedOffspring b ∂boundedOffspringMeasure = (3 / 2 : ℝ) :=
    boundedOffspring_integral
  have hsecond :
      ∫ b, boundedOffspring b ^ 2 ∂boundedOffspringMeasure = (3 : ℝ) :=
    boundedOffspring_sq_integral
  have hpz := measure_ge_threshold_of_moments boundedOffspringMeasure
    boundedOffspring boundedOffspring_measurable hnonneg
    (boundedOffspring_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    boundedOffspring_memLp (3 / 2) 3 (3 / 4) hmean hsecond (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at hpz ⊢
  exact hpz

/-- The concrete first-generation law is identified with the offspring-count
law, and the finite-slot actual moment recursions are available from the
presampled independent field. -/
example {ι : Type*} [Countable ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι PUnit.{1}) :
    (law μ).map (fun β : Combinatorics.Branching.Process ι => β.generationSize 1) =
      μ.childCountLaw :=
  generationSize_one_law μ

example {ι : Type*} [Fintype ι] (μ :
    ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι PUnit.{1})
    (n : ℕ) :
    generationFirstMoment μ (n + 1) =
      ∑ i, offspringSlotWeight μ i * generationFirstMoment μ n :=
  generationFirstMoment_succ_eq_slotSum μ n

example {ι : Type*} [Fintype ι] (μ :
    ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι PUnit.{1})
    (n : ℕ) :
    generationFirstMoment μ n = offspringMean μ ^ n :=
  generationFirstMoment_eq_offspringMean_pow μ n

example {ι : Type*} [Fintype ι] (μ :
    ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι PUnit.{1}) :
    offspringMean μ = μ.expectedChildCount :=
  offspringMean_eq_expectedChildCount μ

example {ι : Type*} [Fintype ι] [DecidableEq ι] (μ :
    ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι PUnit.{1})
    (n : ℕ) :
    generationSecondMoment μ (n + 1) =
      ∑ i, ∑ j, offspringSlotPairWeight μ i j *
        (if i = j then generationSecondMoment μ n else
          generationFirstMoment μ n * generationFirstMoment μ n) :=
  generationSecondMoment_succ_eq_slotPairSum μ n

example {ι : Type*} [Fintype ι] [DecidableEq ι] (μ :
    ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι PUnit.{1})
    (n : ℕ) :
    generationSecondMoment μ (n + 1) =
      offspringMean μ * generationSecondMoment μ n +
        offspringSecondFactorialMoment μ *
          (generationFirstMoment μ n * generationFirstMoment μ n) :=
  generationSecondMoment_succ_eq_offspringMoments μ n

example {ι : Type*} [Countable ι] (n : ℕ) :
    Measurable (fun β : Combinatorics.Branching.Process ι => β.generationSize n) :=
  generationSize_measurable n

example {ι : Type*} [Countable ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) :
    ∫⁻ β : Combinatorics.Branching.Process ι,
      (β.generationSize 1 : ℝ≥0∞) ∂(law μ : Measure _) =
        μ.expectedChildCount :=
  lintegral_generationSize_one_eq_expectedChildCount μ

example (β : Combinatorics.Branching.BranchingWalk (Fin 2) PUnit PUnit) (n : ℕ) :
    letI : Fintype {p // p ∈ Combinatorics.Branching.survivingParticlesAt β n} :=
      (Combinatorics.Branching.RootIndexed.BranchingWalk.generationSlice_finite
        β n).fintype
    β.generationSize (n + 1) =
      ∑ p : {p // p ∈ Combinatorics.Branching.survivingParticlesAt β n},
        (β.step PUnit.unit p.1.2).childCount :=
  Combinatorics.Branching.BranchingWalk.generationSize_succ_eq_sum_childCount β n

example (field : Combinatorics.Branching.StepField (Fin 2) PUnit) (n : ℕ) :
    letI : Fintype {i : Fin 2 // Combinatorics.Branching.survive (field []) i} :=
      Fintype.ofFinite _
    (Combinatorics.Branching.branchingOfStepField field).generationSize (n + 1) =
      ∑ i : {i : Fin 2 // Combinatorics.Branching.survive (field []) i},
        (Combinatorics.Branching.branchingOfStepField
          (ProbabilityTheory.BranchingProcess.GaltonWatson.childSubtreeField
            field i.1)).generationSize n :=
  ProbabilityTheory.BranchingProcess.GaltonWatson.generationSize_succ_eq_sum_childSubtree
    field n

#print axioms measure_generation_ge_floor_rpow_of_moment_recursion
#print axioms generationSize_one_law
#print axioms generationSecondMoment_succ_eq_offspringMoments

end ProbabilityTheory.BranchingProcess.GaltonWatson

end
