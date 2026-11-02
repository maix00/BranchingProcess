/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingProcess.GaltonWatson.Moments.Definitions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Probability.Independence.InfinitePi

/-!
# Product-field calculations for Galton--Watson moments

## Internal proof declarations

- `generationFieldValue`, `offspringActiveSlot`, `generationSingleTerm`, and
  `generationPairTerm` define the random variables used in the field expansion.
- `offspringSlotPairWeight_le_one`, `offspringSlotPairWeight_ne_top`, and
  `offspringSlotPairWeight_self` bound and identify the one-slot and pair
  weights.
- `generationFieldValue_measurable`, `offspringActiveSlot_measurable`,
  `generationSingleTerm_measurable`, and `generationPairTerm_measurable`
  establish measurability of the corresponding field observables.
- `generationFirstMoment_eq_fieldLaw` and
  `generationSecondMoment_eq_fieldLaw` express the moments using the
  independent offspring field.
- `lintegral_generationSingleTerm`, `lintegral_childSubtree_pair`, and
  `lintegral_generationPairTerm` evaluate the single-slot and pair integrals.
- `enat_toENNReal_fintype_sum`, `generationFieldValue_succ_eq_sum`, and
  `lintegral_fintype_sum` provide the finite-sum conversions and rearrangements
  used in the generation recurrences.

This module contains the proof-specific expansion of generation moments over
the independent offspring field: root-slot indicators, descendant-field
changes of variables, single-slot and slot-pair integrals, and finite-sum
rearrangements. It is kept under `Moments/Lemmas/` because these calculations
serve the moment recurrences and have no independent process interface.

With $Z_n$ the generation size and $I_i$ the indicator that slot $i$ is
occupied, the field expansion and its pair integral are
\[
 Z_{n+1}=\sum_i I_i Z_n^{(i)},\qquad
 \mathbb E[Z_{n+1}^2]
   =\sum_{i,j}\mathbb E[I_iI_j]
       \begin{cases}\mathbb E[Z_n^2],&i=j,\\
                    (\mathbb E[Z_n])^2,&i\ne j.
       \end{cases}
\]
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingProcess.GaltonWatson

noncomputable def generationFieldValue {ι : Type*}
    (n : ℕ) (field : Combinatorics.Branching.StepField ι PUnit.{1}) : ℝ≥0∞ :=
  ENat.toENNReal
    ((Combinatorics.Branching.branchingOfStepField field).generationSize n)

noncomputable def offspringActiveSlot {ι : Type*}
    (step : Combinatorics.Branching.Step ι PUnit.{1}) (i : ι) : ℝ≥0∞ := by
  classical
  exact if Combinatorics.Branching.survive step i then 1 else 0

noncomputable def generationSingleTerm {ι : Type*}
    (n : ℕ) (i : ι)
    (field : Combinatorics.Branching.StepField ι PUnit.{1}) : ℝ≥0∞ :=
  offspringActiveSlot (field []) i *
    generationFieldValue n (childSubtreeField field i)

noncomputable def generationPairTerm {ι : Type*}
    (n : ℕ) (i j : ι)
    (field : Combinatorics.Branching.StepField ι PUnit.{1}) : ℝ≥0∞ :=
  (offspringActiveSlot (field []) i *
    generationFieldValue n (childSubtreeField field i)) *
  (offspringActiveSlot (field []) j *
    generationFieldValue n (childSubtreeField field j))
lemma offspringSlotPairWeight_le_one {ι : Type*}
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

lemma offspringSlotPairWeight_ne_top {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (i j : ι) : offspringSlotPairWeight μ i j ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (offspringSlotPairWeight_le_one μ i j) (by simp))

lemma offspringSlotPairWeight_self {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (i : ι) :
    offspringSlotPairWeight μ i i = offspringSlotWeight μ i := by
  classical
  unfold offspringSlotPairWeight offspringSlotWeight
  apply lintegral_congr_ae
  filter_upwards [] with ξ
  by_cases hs : Combinatorics.Branching.survive ξ i <;> simp [hs]

lemma generationFieldValue_measurable {ι : Type*} [Countable ι]
    (n : ℕ) :
    Measurable (generationFieldValue (ι := ι) n) := by
  have hcast : Measurable (fun x : ℕ∞ => ENat.toENNReal x) :=
    measurable_of_countable _
  exact hcast.comp ((generationSize_measurable n).comp
    Combinatorics.Branching.measurable_branchingOfStepField)

lemma offspringActiveSlot_measurable {ι : Type*} (i : ι) :
    Measurable (offspringActiveSlot (ι := ι) · i) := by
  classical
  unfold offspringActiveSlot
  exact Measurable.ite (Combinatorics.Branching.survive_measurableSet i)
    measurable_const measurable_const

lemma generationSingleTerm_measurable {ι : Type*} [Countable ι]
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

lemma generationPairTerm_measurable {ι : Type*} [Countable ι]
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
lemma generationFirstMoment_eq_fieldLaw {ι : Type*} [Countable ι]
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
lemma generationSecondMoment_eq_fieldLaw {ι : Type*} [Countable ι]
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

lemma lintegral_generationSingleTerm {ι : Type*} [Countable ι]
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
lemma lintegral_childSubtree_pair {ι : Type*} [Countable ι]
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

lemma lintegral_generationPairTerm {ι : Type*} [Countable ι]
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

lemma enat_toENNReal_fintype_sum {ι : Type*} [Fintype ι]
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

lemma generationFieldValue_succ_eq_sum {ι : Type*} [Fintype ι]
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

lemma lintegral_fintype_sum {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (ν : Measure Ω) (f : ι → Ω → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∑ i, f i x ∂ν = ∑ i, ∫⁻ x, f i x ∂ν := by
  classical
  exact lintegral_finsetSum (Finset.univ : Finset ι) (fun i _ => hf i)
end ProbabilityTheory.BranchingProcess.GaltonWatson
