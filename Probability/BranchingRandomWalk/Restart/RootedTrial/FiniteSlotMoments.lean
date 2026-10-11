/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.RootedTrial.FiniteSlotCoupling
import Probability.BranchingProcess.GaltonWatson.Growth

/-!
# Finite-slot population moments

The active labels in the reserve construction expose a finite-population
branching recursion. This file computes its one-step moments from the iid
finite-slot rows.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingProcess
  ProbabilityTheory.BranchingProcess.GaltonWatson

/-- The real-valued size of the active finite-slot population. -/
noncomputable def finiteSlotPopulationSizeReal
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X)) (n : ℕ) : ℝ :=
  ((finiteSlotActiveLabels S ω n).card : ℝ)

theorem finiteSlotPopulationSizeReal_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    Measurable (fun ω => finiteSlotPopulationSizeReal S ω n) := by
  change Measurable (fun ω => ((finiteSlotActiveLabels S ω n).card : ℝ))
  exact (measurable_of_countable fun A : Finset (Fin n → Fin 2) => (A.card : ℝ)).comp <|
    (finiteSlotActiveLabels_measurable S hS hcapacity n).mono
      (generationFiltration (M := Step α X) |>.le n) le_rfl

theorem finiteSlotPopulationSizeReal_bound
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (hcapacity : ∀ ξ, (S ξ).card ≤ 2)
    (ω : Mark α (Step α X)) (n : ℕ) :
    finiteSlotPopulationSizeReal S ω n ≤ (2 : ℝ) ^ n := by
  have hcard : (finiteSlotActiveLabels S ω n).card ≤ 2 ^ n := by
    rw [finiteSlotActiveLabels_card_eq_population_card S ω hcapacity]
    exact StepSelection.population_card_le S 2 hcapacity ω n
  change ((finiteSlotActiveLabels S ω n).card : ℝ) ≤ (2 : ℝ) ^ n
  exact_mod_cast hcard

theorem finiteSlotPopulationSizeReal_integrable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    Integrable (fun ω => finiteSlotPopulationSizeReal S ω n) (stepFieldLaw μ) := by
  have hmeas := finiteSlotPopulationSizeReal_measurable S hS hcapacity n
  have hbound : ∀ ω, ‖finiteSlotPopulationSizeReal S ω n‖ ≤ (2 : ℝ) ^ n := by
    intro ω
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (by simp [finiteSlotPopulationSizeReal])]
    exact finiteSlotPopulationSizeReal_bound S hcapacity ω n
  exact Integrable.of_bound hmeas.aestronglyMeasurable ((2 : ℝ) ^ n)
    (ae_of_all _ hbound)

theorem finiteSlotPopulationSizeReal_sq_integrable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    Integrable (fun ω => finiteSlotPopulationSizeReal S ω n ^ 2) (stepFieldLaw μ) := by
  have hmeas := (finiteSlotPopulationSizeReal_measurable S hS hcapacity n).pow_const 2
  have hbound : ∀ ω,
      ‖finiteSlotPopulationSizeReal S ω n ^ 2‖ ≤ ((2 : ℝ) ^ n) ^ 2 := by
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (by simp [finiteSlotPopulationSizeReal])
        (by positivity : 0 ≤ (2 : ℝ) ^ n)).2
      (finiteSlotPopulationSizeReal_bound S hcapacity ω n)
  exact Integrable.of_bound hmeas.aestronglyMeasurable (((2 : ℝ) ^ n) ^ 2)
    (ae_of_all _ hbound)

/-- The real-valued number of children in a finite-slot offspring step. -/
noncomputable def finiteSlotChildCountReal
    (ξ : Step (Fin 2) PUnit.{1}) : ℝ :=
  (ξ.childCount.toNat : ℝ)

theorem finiteSlotChildCountReal_measurable :
    Measurable finiteSlotChildCountReal := by
  exact (measurable_of_countable fun n : ℕ => (n : ℝ)).comp <|
    (measurable_of_countable fun n : ℕ∞ => n.toNat).comp
      Step.childCount_measurable

theorem finiteSlotChildCountReal_bound (ξ : Step (Fin 2) PUnit.{1}) :
    ‖finiteSlotChildCountReal ξ‖ ≤ 2 := by
  have hnonneg : 0 ≤ finiteSlotChildCountReal ξ := by
    simp [finiteSlotChildCountReal]
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hcount : ξ.childCount ≤ (2 : ℕ∞) := by
    rw [Step.childCount]
    calc
      (support ξ).encard ≤ ENat.card (Fin 2) := Set.encard_le_card
      _ = (2 : ℕ∞) := by simp
  have hnat := ENat.toNat_le_toNat hcount (by simp)
  have hnat' : ξ.childCount.toNat ≤ 2 := by simpa using hnat
  change (ξ.childCount.toNat : ℝ) ≤ (2 : ℝ)
  exact_mod_cast hnat'

/-- The finite first moment of the child count of one retained row. -/
noncomputable def finiteSlotOffspringMeanReal
    (ν : ProbabilityMeasure (Step (Fin 2) PUnit.{1})) : ℝ :=
  ∫ ξ, finiteSlotChildCountReal ξ ∂(ν : Measure _)

theorem finiteSlotChildCountReal_integrable
    (ν : ProbabilityMeasure (Step (Fin 2) PUnit.{1})) :
    Integrable finiteSlotChildCountReal (ν : Measure _) := by
  exact Integrable.of_bound finiteSlotChildCountReal_measurable.aestronglyMeasurable
    2 (ae_of_all _ finiteSlotChildCountReal_bound)

/-- The finite second moment of the child count of one retained row. -/
noncomputable def finiteSlotOffspringSecondMomentReal
    (ν : ProbabilityMeasure (Step (Fin 2) PUnit.{1})) : ℝ :=
  ∫ ξ, finiteSlotChildCountReal ξ ^ 2 ∂(ν : Measure _)

theorem finiteSlotOffspringSecondMomentReal_integrable
    (ν : ProbabilityMeasure (Step (Fin 2) PUnit.{1})) :
    Integrable (fun ξ => finiteSlotChildCountReal ξ ^ 2) (ν : Measure _) := by
  refine Integrable.of_bound
    (finiteSlotChildCountReal_measurable.pow_const 2).aestronglyMeasurable
    4 (ae_of_all _ fun ξ => ?_)
  have h := finiteSlotChildCountReal_bound ξ
  have hn : 0 ≤ finiteSlotChildCountReal ξ := by simp [finiteSlotChildCountReal]
  have hle : finiteSlotChildCountReal ξ ≤ 2 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hn] using h
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hprod : 0 ≤ (2 - finiteSlotChildCountReal ξ) *
      (2 + finiteSlotChildCountReal ξ) :=
    mul_nonneg (sub_nonneg.mpr hle) (by positivity)
  nlinarith

private theorem finiteSlotChildCountReal_pair_integral
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (ν : ProbabilityMeasure (Step (Fin 2) PUnit.{1}))
    (rowsLaw : Measure (ι → Step (Fin 2) PUnit.{1}))
    (hrowsLaw : rowsLaw = Measure.infinitePi (fun _ : ι => (ν : Measure _)))
    (i j : ι) :
    ∫ rows, finiteSlotChildCountReal (rows i) * finiteSlotChildCountReal (rows j)
      ∂rowsLaw =
      if i = j then finiteSlotOffspringSecondMomentReal ν else
        finiteSlotOffspringMeanReal ν * finiteSlotOffspringMeanReal ν := by
  classical
  subst rowsLaw
  by_cases hij : i = j
  · subst j
    have heval := Measure.infinitePi_map_eval
      (fun _ : ι => (ν : Measure (Step (Fin 2) PUnit.{1}))) i
    have hpairMeas : Measurable
        (fun ξ : Step (Fin 2) PUnit.{1} =>
          finiteSlotChildCountReal ξ * finiteSlotChildCountReal ξ) :=
      finiteSlotChildCountReal_measurable.mul finiteSlotChildCountReal_measurable
    have hmap := integral_map_of_stronglyMeasurable
      (μ := Measure.infinitePi (fun _ : ι => (ν : Measure (Step (Fin 2) PUnit.{1}))))
      (φ := fun rows : ι → Step (Fin 2) PUnit.{1} => rows i)
      (f := fun ξ => finiteSlotChildCountReal ξ * finiteSlotChildCountReal ξ)
      (measurable_pi_apply i) hpairMeas.stronglyMeasurable
    rw [← hmap, heval]
    simp [finiteSlotOffspringSecondMomentReal, pow_two]
  · have hmap := Measure.infinitePi_map_eval_prod
      (P := fun _ : ι => (ν : Measure (Step (Fin 2) PUnit.{1}))) hij
    have hpairMeas : Measurable
        (fun p : Step (Fin 2) PUnit.{1} × Step (Fin 2) PUnit.{1} =>
          finiteSlotChildCountReal p.1 * finiteSlotChildCountReal p.2) :=
      (finiteSlotChildCountReal_measurable.comp measurable_fst).mul
        (finiteSlotChildCountReal_measurable.comp measurable_snd)
    have hrowsMeas : Measurable
        (fun rows : ι → Step (Fin 2) PUnit.{1} => (rows i, rows j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    have hmapInt := integral_map_of_stronglyMeasurable
      (μ := Measure.infinitePi (fun _ : ι => (ν : Measure (Step (Fin 2) PUnit.{1}))))
      (φ := fun rows : ι → Step (Fin 2) PUnit.{1} => (rows i, rows j))
      (f := fun p : Step (Fin 2) PUnit.{1} × Step (Fin 2) PUnit.{1} =>
        finiteSlotChildCountReal p.1 * finiteSlotChildCountReal p.2)
      hrowsMeas hpairMeas.stronglyMeasurable
    rw [← hmapInt, hmap, integral_prod_mul]
    simp [hij, finiteSlotOffspringMeanReal]

theorem finiteSlotRowCountSum_sq_integral
    (n : ℕ) (A : Finset (Fin n → Fin 2))
    (ν : ProbabilityMeasure (Step (Fin 2) PUnit.{1})) :
    ∫ rows, finiteSlotRowCountSum n (A, rows) ^ 2 ∂
        Measure.infinitePi (fun _ : (Fin n → Fin 2) => (ν : Measure _)) =
      ∑ u ∈ A, ∑ v ∈ A,
        if u = v then finiteSlotOffspringSecondMomentReal ν else
          finiteSlotOffspringMeanReal ν * finiteSlotOffspringMeanReal ν := by
  classical
  let rowLaw := Measure.infinitePi
    (fun _ : (Fin n → Fin 2) => (ν : Measure (Step (Fin 2) PUnit.{1})))
  let countAt := fun (rows : (Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) u =>
    finiteSlotChildCountReal (rows u)
  have hpairMeas (u v : Fin n → Fin 2) :
      Measurable (fun rows => countAt rows u * countAt rows v) := by
    dsimp [countAt]
    exact (finiteSlotChildCountReal_measurable.comp (measurable_pi_apply u)).mul
      (finiteSlotChildCountReal_measurable.comp (measurable_pi_apply v))
  have hpairIntegrable (u v : Fin n → Fin 2) :
      Integrable (fun rows => countAt rows u * countAt rows v) rowLaw := by
    refine Integrable.of_bound (hpairMeas u v).aestronglyMeasurable 4
      (ae_of_all _ fun rows => ?_)
    have hu := finiteSlotChildCountReal_bound (rows u)
    have hv := finiteSlotChildCountReal_bound (rows v)
    rw [norm_mul]
    calc
      ‖finiteSlotChildCountReal (rows u)‖ *
          ‖finiteSlotChildCountReal (rows v)‖ ≤ 2 * 2 :=
        mul_le_mul hu hv (norm_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  have hinnerIntegrable (u : Fin n → Fin 2) :
      Integrable (fun rows => ∑ v ∈ A, countAt rows u * countAt rows v) rowLaw :=
    integrable_finsetSum A (fun v hv => hpairIntegrable u v)
  have hdoubleIntegrable :
      Integrable (fun rows => ∑ u ∈ A, ∑ v ∈ A,
        countAt rows u * countAt rows v) rowLaw :=
    integrable_finsetSum A (fun u hu => hinnerIntegrable u)
  calc
    _ = ∫ rows, (∑ u ∈ A, countAt rows u) ^ 2 ∂rowLaw := by
      apply integral_congr_ae
      filter_upwards [] with rows
      rw [finiteSlotRowCountSum_eq_sum]
      rfl
    _ = ∫ rows, ∑ u ∈ A, ∑ v ∈ A,
        countAt rows u * countAt rows v ∂rowLaw := by
      apply integral_congr_ae
      filter_upwards [] with rows
      rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ u ∈ A, ∑ v ∈ A,
        ∫ rows, countAt rows u * countAt rows v ∂rowLaw := by
      rw [integral_finsetSum A (fun u hu => hinnerIntegrable u)]
      apply Finset.sum_congr rfl
      intro u hu
      exact integral_finsetSum A (fun v hv => hpairIntegrable u v)
    _ = ∑ u ∈ A, ∑ v ∈ A,
        if u = v then finiteSlotOffspringSecondMomentReal ν else
          finiteSlotOffspringMeanReal ν * finiteSlotOffspringMeanReal ν := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      exact finiteSlotChildCountReal_pair_integral ν rowLaw rfl u v

private theorem finiteSlotPairSum_eq_card_formula
    {ι : Type*} [DecidableEq ι] (A : Finset ι) (m q : ℝ) :
    (∑ u ∈ A, ∑ v ∈ A, if u = v then q else m * m) =
      (A.card : ℝ) * q + (A.card : ℝ) * ((A.card : ℝ) - 1) * (m * m) := by
  classical
  have hinner (u : ι) (hu : u ∈ A) :
      (∑ v ∈ A, if u = v then q else m * m) =
        (A.card : ℝ) * (m * m) + (q - m * m) := by
    calc
      (∑ v ∈ A, if u = v then q else m * m) =
          ∑ v ∈ A, (m * m + if u = v then q - m * m else 0) := by
        apply Finset.sum_congr rfl
        intro v hv
        by_cases huv : u = v
        · simp [huv]
        · simp [huv]
      _ = (∑ v ∈ A, m * m) +
          ∑ v ∈ A, if u = v then q - m * m else 0 := Finset.sum_add_distrib
      _ = (A.card : ℝ) * (m * m) + (q - m * m) := by
        rw [Finset.sum_const, Finset.sum_ite_eq]
        simp [hu, nsmul_eq_mul]
  calc
    (∑ u ∈ A, ∑ v ∈ A, if u = v then q else m * m) =
        ∑ u ∈ A, ((A.card : ℝ) * (m * m) + (q - m * m)) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hinner u hu
    _ = (A.card : ℝ) * ((A.card : ℝ) * (m * m) + (q - m * m)) := by
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul]
    _ = (A.card : ℝ) * q + (A.card : ℝ) * ((A.card : ℝ) - 1) * (m * m) := by ring


theorem finiteSlotRowCountSum_integral
    (n : ℕ) (A : Finset (Fin n → Fin 2))
    (ν : ProbabilityMeasure (Step (Fin 2) PUnit.{1})) :
    ∫ rows, finiteSlotRowCountSum n (A, rows) ∂
        Measure.infinitePi (fun _ : (Fin n → Fin 2) => (ν : Measure _)) =
      (A.card : ℝ) * finiteSlotOffspringMeanReal ν := by
  classical
  let rowLaw := Measure.infinitePi
    (fun _ : (Fin n → Fin 2) => (ν : Measure (Step (Fin 2) PUnit.{1})))
  have hrowCount (u : Fin n → Fin 2) :
      Integrable (fun rows : (Fin n → Fin 2) → Step (Fin 2) PUnit.{1} =>
        finiteSlotChildCountReal (rows u)) rowLaw := by
    exact Integrable.of_bound
      (finiteSlotChildCountReal_measurable.comp (measurable_pi_apply u)).aestronglyMeasurable
      2 (ae_of_all _ fun rows => finiteSlotChildCountReal_bound (rows u))
  calc
    _ = ∫ rows, ∑ u ∈ A, finiteSlotChildCountReal (rows u) ∂rowLaw := by
      apply integral_congr_ae
      filter_upwards [] with rows
      exact finiteSlotRowCountSum_eq_sum n A rows
    _ = ∑ u ∈ A, ∫ rows, finiteSlotChildCountReal (rows u) ∂rowLaw :=
      integral_finsetSum A (fun u _ => hrowCount u)
    _ = ∑ u ∈ A, finiteSlotOffspringMeanReal ν := by
      apply Finset.sum_congr rfl
      intro u hu
      unfold finiteSlotOffspringMeanReal
      have heval := Measure.infinitePi_map_eval
        (fun _ : Fin n → Fin 2 => (ν : Measure (Step (Fin 2) PUnit.{1}))) u
      have hmap := integral_map_of_stronglyMeasurable
        (μ := rowLaw) (φ := fun rows : (Fin n → Fin 2) → Step (Fin 2) PUnit.{1} => rows u)
        (f := finiteSlotChildCountReal) (measurable_pi_apply u)
        finiteSlotChildCountReal_measurable.stronglyMeasurable
      rw [← hmap, heval]
    _ = (A.card : ℝ) * finiteSlotOffspringMeanReal ν := by simp

private theorem finiteSlotOffspringStep_standardBorel :
    StandardBorelSpace (Step (Fin 2) PUnit.{1}) := by
  letI : MeasurableSingletonClass (Option PUnit.{1}) := by
    refine ⟨fun x => ?_⟩
    cases x with
    | none => exact measurableSet_option_none
    | some x =>
      rw [show ({some x} : Set (Option PUnit.{1})) = some '' {x} by
        ext y
        simp]
      exact measurableSet_option_some_image (measurableSet_singleton x)
  letI : MeasurableSingletonClass (Step (Fin 2) PUnit.{1}) := inferInstance
  infer_instance

private theorem finiteSlotRows_standardBorel (n : ℕ) :
    StandardBorelSpace ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) := by
  letI : StandardBorelSpace (Step (Fin 2) PUnit.{1}) :=
    finiteSlotOffspringStep_standardBorel
  infer_instance

/-- The active-label population has the finite-slot offspring mean as its
conditional one-step growth factor. -/
theorem finiteSlotActiveLabels_condExp_succ_card_eq_mean
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    condExp (MeasurableSpace.comap (finiteSlotActiveLabels S · n) inferInstance)
      (stepFieldLaw μ)
      (fun ω => ((finiteSlotActiveLabels S ω (n + 1)).card : ℝ)) =ᵐ[stepFieldLaw μ]
    fun ω => (finiteSlotActiveLabels S ω n).card *
      finiteSlotOffspringMeanReal
        (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS) := by
  classical
  let ν : ProbabilityMeasure (Step α X) := ⟨μ, inferInstance⟩
  let κ := finiteOffspringLaw ν S hS
  have hcond := finiteSlotActiveLabels_condExp_succ_card μ S hS hcapacity n
  filter_upwards [hcond] with ω hω
  calc
    condExp (MeasurableSpace.comap (finiteSlotActiveLabels S · n) inferInstance)
        (stepFieldLaw μ)
        (fun ω => ((finiteSlotActiveLabels S ω (n + 1)).card : ℝ)) ω =
      ∫ row, finiteSlotRowCountSum n
        (finiteSlotActiveLabels S ω n, row) ∂
          Measure.infinitePi (fun _ : (Fin n → Fin 2) => (κ : Measure _)) := by
        simpa [κ, ν] using hω
    _ = (finiteSlotActiveLabels S ω n).card *
        finiteSlotOffspringMeanReal κ :=
      finiteSlotRowCountSum_integral n (finiteSlotActiveLabels S ω n) κ
    _ = (finiteSlotActiveLabels S ω n).card *
        finiteSlotOffspringMeanReal
          (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS) := by
      simp [κ, ν]


/-- Conditional second-moment recursion for the active-label population. -/
theorem finiteSlotActiveLabels_condExp_succ_card_sq
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    condExp (MeasurableSpace.comap (finiteSlotActiveLabels S · n) inferInstance)
      (stepFieldLaw μ)
      (fun ω => ((finiteSlotActiveLabels S ω (n + 1)).card : ℝ) ^ 2) =ᵐ[stepFieldLaw μ]
    fun ω => ∫ row, finiteSlotRowCountSum n
      (finiteSlotActiveLabels S ω n, row) ^ 2 ∂
        Measure.infinitePi (fun _ : (Fin n → Fin 2) =>
          (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _)
            S hS : Measure (Step (Fin 2) PUnit.{1}))) := by
  classical
  let active : Mark α (Step α X) → Finset (Fin n → Fin 2) :=
    fun ω => finiteSlotActiveLabels S ω n
  let rows : Mark α (Step α X) →
      (Fin n → Fin 2) → Step (Fin 2) PUnit.{1} :=
    fun ω => finiteSlotLevelSteps S ω n
  let nextSizeSq : Mark α (Step α X) → ℝ := fun ω =>
    ((finiteSlotActiveLabels S ω (n + 1)).card : ℝ) ^ 2
  let rowSquare : Finset (Fin n → Fin 2) ×
      ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) → ℝ :=
    fun p => finiteSlotRowCountSum n p ^ 2
  have hactive : Measurable active := by
    simpa [active] using
      (finiteSlotActiveLabels_measurable S hS hcapacity n).mono
        (generationFiltration (M := Step α X) |>.le n) le_rfl
  have hrows : Measurable rows := by
    simpa [rows] using finiteSlotLevelSteps_measurable S hS n
  have hind := finiteSlotActiveLabels_levelSteps_independent
    μ S hS hcapacity n
  have hnext : Measurable nextSizeSq := by
    change Measurable (fun ω =>
      ((finiteSlotActiveLabels S ω (n + 1)).card : ℝ) ^ 2)
    exact ((measurable_of_countable fun A : Finset (Fin (n + 1) → Fin 2) =>
      (A.card : ℝ)).comp <|
        (finiteSlotActiveLabels_measurable S hS hcapacity (n + 1)).mono
          (generationFiltration (M := Step α X) |>.le (n + 1)) le_rfl).pow_const 2
  have hnextBound : ∀ ω, ‖nextSizeSq ω‖ ≤ ((2 ^ (n + 1) : ℝ) ^ 2) := by
    intro ω
    change ‖((finiteSlotActiveLabels S ω (n + 1)).card : ℝ) ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hcard : (finiteSlotActiveLabels S ω (n + 1)).card ≤ 2 ^ (n + 1) := by
      rw [finiteSlotActiveLabels_card_eq_population_card S ω hcapacity]
      exact StepSelection.population_card_le S 2 hcapacity ω (n + 1)
    have hreal :
        ((finiteSlotActiveLabels S ω (n + 1)).card : ℝ) ≤
          (2 : ℝ) ^ (n + 1) := by
      exact_mod_cast hcard
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hreal
  have hnextIntegrable : Integrable nextSizeSq (stepFieldLaw μ) :=
    Integrable.of_bound hnext.aestronglyMeasurable
      ((2 ^ (n + 1) : ℝ) ^ 2) (ae_of_all _ hnextBound)
  have hrowMeasurable : Measurable (fun p =>
      finiteSlotRowCountSum n p ^ 2) :=
    (finiteSlotRowCountSum_measurable n).pow_const 2
  have hrowStrong : StronglyMeasurable rowSquare := by
    simpa [rowSquare] using hrowMeasurable.stronglyMeasurable
  have hsample : (fun ω => rowSquare (active ω, rows ω)) = nextSizeSq := by
    funext ω
    have hsum := finiteSlotActiveLabels_card_succ_eq_sum S ω hcapacity n
    have hcount : finiteSlotRowCountSum n
        (finiteSlotActiveLabels S ω n, finiteSlotLevelSteps S ω n) =
          ((finiteSlotActiveLabels S ω (n + 1)).card : ℝ) := by
      rw [finiteSlotRowCountSum_eq_sum]
      simpa only [Nat.cast_sum] using
        congrArg (fun k : ℕ => (k : ℝ)) hsum.symm
    change finiteSlotRowCountSum n
        (finiteSlotActiveLabels S ω n, finiteSlotLevelSteps S ω n) ^ 2 = _
    rw [hcount]
  have hsampleIntegrable :
      Integrable (fun ω => rowSquare (active ω, rows ω)) (stepFieldLaw μ) := by
    rw [hsample]
    exact hnextIntegrable
  letI : MeasurableSingletonClass (Option PUnit.{1}) := by
    refine ⟨fun x => ?_⟩
    cases x with
    | none => exact measurableSet_option_none
    | some x =>
      rw [show ({some x} : Set (Option PUnit.{1})) = some '' {x} by
        ext y
        simp]
      exact measurableSet_option_some_image (measurableSet_singleton x)
  letI : MeasurableSingletonClass (Step (Fin 2) PUnit.{1}) := inferInstance
  letI : StandardBorelSpace (Step (Fin 2) PUnit.{1}) := by infer_instance
  letI : StandardBorelSpace ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) := by
    infer_instance
  have hcond := hind.condExp_prod_ae_eq_integral_map
    hactive hrows hrowStrong hsampleIntegrable
  rw [hsample] at hcond
  have hrowLaw : (stepFieldLaw μ).map rows =
      Measure.infinitePi (fun _ : (Fin n → Fin 2) =>
        (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _)
          S hS : Measure (Step (Fin 2) PUnit.{1}))) := by
    simpa [rows] using finiteSlotLevelSteps_law μ S hS n
  rw [hrowLaw] at hcond
  simpa [active, nextSizeSq, rowSquare] using hcond

/-- The conditional second moment is the diagonal/off-diagonal pair sum of
the finite offspring-row moments. -/
theorem finiteSlotActiveLabels_condExp_succ_card_sq_eq_pair_sum
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    condExp (MeasurableSpace.comap (finiteSlotActiveLabels S · n) inferInstance)
      (stepFieldLaw μ)
      (fun ω => ((finiteSlotActiveLabels S ω (n + 1)).card : ℝ) ^ 2) =ᵐ[stepFieldLaw μ]
    fun ω => ∑ u ∈ finiteSlotActiveLabels S ω n,
      ∑ v ∈ finiteSlotActiveLabels S ω n,
        if u = v then
          finiteSlotOffspringSecondMomentReal
            (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS)
        else
          finiteSlotOffspringMeanReal
            (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS) *
          finiteSlotOffspringMeanReal
            (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS) := by
  classical
  filter_upwards [finiteSlotActiveLabels_condExp_succ_card_sq μ S hS hcapacity n]
    with ω hω
  simpa only [finiteSlotRowCountSum_sq_integral] using hω

/-- Closed conditional second-moment recursion for the active population. If
`m` and `q` are the first two offspring-row moments, this is
`Zₙ q + Zₙ (Zₙ - 1) m²`. -/
theorem finiteSlotActiveLabels_condExp_succ_card_sq_eq_card_formula
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    condExp (MeasurableSpace.comap (finiteSlotActiveLabels S · n) inferInstance)
      (stepFieldLaw μ)
      (fun ω => finiteSlotPopulationSizeReal S ω (n + 1) ^ 2) =ᵐ[stepFieldLaw μ]
    fun ω => finiteSlotPopulationSizeReal S ω n *
        finiteSlotOffspringSecondMomentReal
          (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS) +
      finiteSlotPopulationSizeReal S ω n *
        (finiteSlotPopulationSizeReal S ω n - 1) *
        (finiteSlotOffspringMeanReal
          (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS) ^ 2) := by
  classical
  filter_upwards
    [finiteSlotActiveLabels_condExp_succ_card_sq_eq_pair_sum μ S hS hcapacity n]
    with ω hω
  change condExp (MeasurableSpace.comap (finiteSlotActiveLabels S · n) inferInstance)
      (stepFieldLaw μ)
      (fun ω => ((finiteSlotActiveLabels S ω (n + 1)).card : ℝ) ^ 2) ω =
    (finiteSlotActiveLabels S ω n).card *
        finiteSlotOffspringSecondMomentReal
          (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS) +
      (finiteSlotActiveLabels S ω n).card *
        ((finiteSlotActiveLabels S ω n).card - 1) *
        (finiteSlotOffspringMeanReal
          (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS) ^ 2)
  rw [hω]
  simpa only [finiteSlotPopulationSizeReal, pow_two] using
    (finiteSlotPairSum_eq_card_formula (finiteSlotActiveLabels S ω n)
      (finiteSlotOffspringMeanReal
        (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS))
      (finiteSlotOffspringSecondMomentReal
        (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS)))

/-- Unconditional first-moment recursion for the finite-slot population. -/
theorem finiteSlotPopulationSizeReal_integral_succ_eq
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    ∫ ω, finiteSlotPopulationSizeReal S ω (n + 1) ∂stepFieldLaw μ =
      finiteSlotOffspringMeanReal
        (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS) *
      ∫ ω, finiteSlotPopulationSizeReal S ω n ∂stepFieldLaw μ := by
  classical
  have hactive : Measurable (finiteSlotActiveLabels S · n) :=
    (finiteSlotActiveLabels_measurable S hS hcapacity n).mono
      (generationFiltration (M := Step α X) |>.le n) le_rfl
  have hF :
      MeasurableSpace.comap (finiteSlotActiveLabels S · n) inferInstance ≤
        (inferInstance : MeasurableSpace (Mark α (Step α X))) :=
    measurable_iff_comap_le.mp hactive
  have hcond := finiteSlotActiveLabels_condExp_succ_card_eq_mean
    μ S hS hcapacity n
  calc
    ∫ ω, finiteSlotPopulationSizeReal S ω (n + 1) ∂stepFieldLaw μ =
        ∫ ω, condExp (MeasurableSpace.comap (finiteSlotActiveLabels S · n)
          inferInstance) (stepFieldLaw μ)
          (fun ω => finiteSlotPopulationSizeReal S ω (n + 1)) ω ∂stepFieldLaw μ := by
        symm
        exact integral_condExp hF
    _ = ∫ ω, finiteSlotPopulationSizeReal S ω n *
        finiteSlotOffspringMeanReal
          (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS)
          ∂stepFieldLaw μ := by
        apply integral_congr_ae
        filter_upwards [hcond] with ω hω
        simpa [finiteSlotPopulationSizeReal] using hω
    _ = finiteSlotOffspringMeanReal
        (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS) *
          ∫ ω, finiteSlotPopulationSizeReal S ω n ∂stepFieldLaw μ := by
        rw [integral_mul_const]
        ring

/-- Unconditional second-moment recursion for the finite-slot population.
The offspring row is bounded by two, so all displayed moments are integrable. -/
theorem finiteSlotPopulationSizeReal_sq_integral_succ_eq
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    ∫ ω, finiteSlotPopulationSizeReal S ω (n + 1) ^ 2 ∂stepFieldLaw μ =
      (finiteSlotOffspringMeanReal
        (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS) ^ 2) *
          ∫ ω, finiteSlotPopulationSizeReal S ω n ^ 2 ∂stepFieldLaw μ +
        (finiteSlotOffspringSecondMomentReal
            (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS) -
          finiteSlotOffspringMeanReal
            (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS) ^ 2) *
          ∫ ω, finiteSlotPopulationSizeReal S ω n ∂stepFieldLaw μ := by
  classical
  let m := finiteSlotOffspringMeanReal
    (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS)
  let q := finiteSlotOffspringSecondMomentReal
    (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS)
  have hactive : Measurable (finiteSlotActiveLabels S · n) :=
    (finiteSlotActiveLabels_measurable S hS hcapacity n).mono
      (generationFiltration (M := Step α X) |>.le n) le_rfl
  have hF :
      MeasurableSpace.comap (finiteSlotActiveLabels S · n) inferInstance ≤
        (inferInstance : MeasurableSpace (Mark α (Step α X))) :=
    measurable_iff_comap_le.mp hactive
  have hcond := finiteSlotActiveLabels_condExp_succ_card_sq_eq_card_formula
    μ S hS hcapacity n
  have hsizeInt := finiteSlotPopulationSizeReal_integrable μ S hS hcapacity n
  have hsquareInt := finiteSlotPopulationSizeReal_sq_integrable μ S hS hcapacity n
  have hdifferenceInt : Integrable
      (fun ω => finiteSlotPopulationSizeReal S ω n ^ 2 -
        finiteSlotPopulationSizeReal S ω n) (stepFieldLaw μ) :=
    hsquareInt.sub hsizeInt
  calc
    ∫ ω, finiteSlotPopulationSizeReal S ω (n + 1) ^ 2 ∂stepFieldLaw μ =
        ∫ ω, condExp (MeasurableSpace.comap (finiteSlotActiveLabels S · n)
          inferInstance) (stepFieldLaw μ)
          (fun ω => finiteSlotPopulationSizeReal S ω (n + 1) ^ 2) ω ∂stepFieldLaw μ := by
        symm
        exact integral_condExp hF
    _ = ∫ ω, finiteSlotPopulationSizeReal S ω n * q +
          finiteSlotPopulationSizeReal S ω n *
            (finiteSlotPopulationSizeReal S ω n - 1) * m ^ 2 ∂stepFieldLaw μ := by
        apply integral_congr_ae
        filter_upwards [hcond] with ω hω
        simpa [m, q] using hω
    _ = ∫ ω, q * finiteSlotPopulationSizeReal S ω n +
          m ^ 2 * (finiteSlotPopulationSizeReal S ω n ^ 2 -
            finiteSlotPopulationSizeReal S ω n) ∂stepFieldLaw μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
    _ = q * ∫ ω, finiteSlotPopulationSizeReal S ω n ∂stepFieldLaw μ +
          m ^ 2 * (∫ ω, finiteSlotPopulationSizeReal S ω n ^ 2 ∂stepFieldLaw μ -
            ∫ ω, finiteSlotPopulationSizeReal S ω n ∂stepFieldLaw μ) := by
        rw [integral_add (hsizeInt.const_mul q) (hdifferenceInt.const_mul (m ^ 2)),
          integral_const_mul, integral_const_mul,
          integral_sub hsquareInt hsizeInt]
    _ = m ^ 2 *
          ∫ ω, finiteSlotPopulationSizeReal S ω n ^ 2 ∂stepFieldLaw μ +
        (q - m ^ 2) *
          ∫ ω, finiteSlotPopulationSizeReal S ω n ∂stepFieldLaw μ := by ring

end ProbabilityTheory.BranchingRandomWalk
