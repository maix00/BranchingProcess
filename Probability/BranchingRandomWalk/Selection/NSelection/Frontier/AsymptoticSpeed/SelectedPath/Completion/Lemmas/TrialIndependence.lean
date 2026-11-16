/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Lemmas.FirstSplit.BranchingProperty
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Recursive

import Probability.Sequence.IID.GeometricReward.FirstMoment
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Independence of successive split cycles

## Internal proof declarations

* `splitCycle` iterates the second-child continuation and records the pair $Z_k=(F_k,G_k)$.
* `splitCycle_prefix_map_eq_pi`: the successive pairs $Z_i=(F_i,G_i)$,
  $i<n$, have joint law $\rho^{\otimes n}$ for their common law $\rho$.
* `integral_splitCycle_positiveDisplacement_through_success`: if $kappa$
  is the first successful growth trial and $p$ its single-trial probability,
  $mathbb E[sum_{jlekappa}(X_j)_+]=mathbb E[(X_1)_+]/p$.
* `measure_firstSuccessfulSplitCycle_partialSum_ge_le`: with
  $S_k=\sum_{i<k}F_i$, the first successful growth trial satisfies
  $e^{\lambda x}\mathbb P(\kappa\le K, S_\kappa\ge x)
  \le\sum_{k=1}^K (\mathbb E[e^{\lambda F}])^k$ for $\lambda>0$.

Here $F$ is observed by the first split completion and $G$ is evaluated on
the first child's full subtree. The second child supplies the fresh field
for the next split cycle, including cycles after the first successful trial.
This is the stopped branching argument in Wang Yiyang, *Asymptotic Speed of
the N-Branching Random Walk with Infinite Offspring* (Fudan University,
2026), Chapter 4, Theorem 1.1 at $a=0$.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.BranchingRandomWalk.Selection.Stepwise.SplitTime
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Lemmas.FirstSplit
open SelectedPath.GrowthTrial

variable {α X D E : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [LinearOrder α] [OrderBot α] [MeasurableSpace X] [MeasurableSpace D] [MeasurableSpace E]

private lemma splitCycle_map_eq_prod
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hfinite : ∀ᵐ ω ∂offspringFieldLaw μ, selectedPopulationSplitCompletion R ω ≠ ⊤)
    (F : Mark α (Step α X) → D)
    (hF : Measurable[(selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace] F)
    (G : Mark α (Step α X) → E) (hG : Measurable G) :
    let ν := offspringFieldLaw μ
    ν.map (fun ω => ((F ω, G (selectedPopulationFirstSplitSubtrees R ω 0)),
      selectedPopulationFirstSplitSubtrees R ω 1)) =
      ((ν.map F).prod (ν.map G)).prod ν := by
  intro ν
  let children := selectedPopulationFirstSplitSubtrees R
  let Q := Measure.infinitePi (fun _ : Fin 2 => ν)
  have hF' := hF.mono (selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace_le le_rfl
  have hchildren := selectedPopulationFirstSplitSubtrees_measurable R hR
  have h₀ : Measurable (fun ω => children ω 0) := (measurable_pi_apply 0).comp hchildren
  have h₁ : Measurable (fun ω => children ω 1) := (measurable_pi_apply 1).comp hchildren
  refine Measure.ext_prod₃_iff'.2 ?_
  intro a b c ha hb hc
  have hm : Measurable (fun ω => ((F ω, G (selectedPopulationFirstSplitSubtrees R ω 0)),
      selectedPopulationFirstSplitSubtrees R ω 1)) :=
    (hF'.prodMk (hG.comp h₀)).prodMk h₁
  rw [Measure.map_apply hm ((ha.prod hb).prod hc),
    Measure.prod_prod, Measure.prod_prod, Measure.map_apply hF' ha, Measure.map_apply hG hb]
  let A := F ⁻¹' a
  let B : Set (Fin 2 → Mark α (Step α X)) :=
    (fun v => v 0) ⁻¹' (G ⁻¹' b) ∩ (fun v => v 1) ⁻¹' c
  have hB : MeasurableSet B :=
    ((hG hb).preimage (measurable_pi_apply 0)).inter (hc.preimage (measurable_pi_apply 1))
  have hbranch := selectedPopulation_firstSplit_subtree_vector_factorization
    μ R hR A B (hF ha) hB
  have heq (S : Set (Mark α (Step α X))) :
      S ∩ {ω | selectedPopulationSplitCompletion R ω ≠ ⊤} =ᵐ[ν] S := by
    filter_upwards [hfinite] with ω hω
    simp [hω]
  have hleft :
      (A ∩ {ω | selectedPopulationSplitCompletion R ω ≠ ⊤}) ∩ children ⁻¹' B =ᵐ[ν]
        A ∩ children ⁻¹' B := by
    filter_upwards [heq A] with ω hω
    exact and_congr_left (fun _ => hω)
  change ν ((A ∩ {ω | selectedPopulationSplitCompletion R ω ≠ ⊤}) ∩
    children ⁻¹' B) = ν (A ∩ {ω | selectedPopulationSplitCompletion R ω ≠ ⊤}) *
      Q B at hbranch
  rw [measure_congr hleft, measure_congr (heq A)] at hbranch
  have hindep : IndepFun (fun v : Fin 2 → Mark α (Step α X) => v 0)
      (fun v => v 1) Q :=
    (iIndepFun_infinitePi (P := fun _ : Fin 2 => ν) (X := fun _ => id)
      (fun _ => measurable_id)).indepFun (by decide)
  have hmarg (i : Fin 2) (s : Set (Mark α (Step α X))) (hs : MeasurableSet s) :
      Q ((fun v => v i) ⁻¹' s) = ν s := by
    rw [← Measure.map_apply (measurable_pi_apply i) hs]
    exact congrArg (fun m : Measure (Mark α (Step α X)) => m s)
      (RootIndexed.stepFieldLaw_root_marginal μ i)
  have hQ : Q B = ν (G ⁻¹' b) * ν c := by
    unfold B
    rw [hindep.measure_inter_preimage_eq_mul _ _ (hG hb) hc, hmarg 0 _ (hG hb), hmarg 1 _ hc]
  have hrect :
      (fun ω => ((F ω, G (children ω 0)), children ω 1)) ⁻¹' ((a ×ˢ b) ×ˢ c) =
        A ∩ children ⁻¹' B := by
    ext ω
    simp [A, B, and_assoc]
  change ν ((fun ω => ((F ω, G (children ω 0)), children ω 1)) ⁻¹'
    ((a ×ˢ b) ×ˢ c)) = (ν (F ⁻¹' a) * ν (G ⁻¹' b)) * ν c
  rw [hrect, hbranch, hQ, mul_assoc]

/-- Sample the current split and continue in its second child's field. -/
noncomputable def splitCycle
    (R : Step.FiniteSelection α X)
    (F : Mark α (Step α X) → D) (G : Mark α (Step α X) → E) :
    ℕ → Mark α (Step α X) → D × E
  | 0, ω => (F ω, G (selectedPopulationFirstSplitSubtrees R ω 0))
  | n + 1, ω => splitCycle R F G n (selectedPopulationFirstSplitSubtrees R ω 1)

private lemma measurable_splitCycle
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (F : Mark α (Step α X) → D) (hF : Measurable F)
    (G : Mark α (Step α X) → E) (hG : Measurable G) (n : ℕ) :
    Measurable (splitCycle R F G n) := by
  have hchild (i : Fin 2) : Measurable (fun ω => selectedPopulationFirstSplitSubtrees R ω i) :=
    (measurable_pi_apply i).comp (selectedPopulationFirstSplitSubtrees_measurable R hR)
  induction n with
  | zero => exact hF.prodMk (hG.comp (hchild 0))
  | succ n ih => exact ih.comp (hchild 1)

private lemma measure_splitCycles
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hfinite : ∀ᵐ ω ∂offspringFieldLaw μ, selectedPopulationSplitCompletion R ω ≠ ⊤)
    (F : Mark α (Step α X) → D)
    (hF : Measurable[(selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace] F)
    (G : Mark α (Step α X) → E) (hG : Measurable G)
    (n : ℕ) (A : ℕ → Set (D × E)) (hA : ∀ i, MeasurableSet (A i)) :
    let ν := offspringFieldLaw μ
    let ρ := (ν.map F).prod (ν.map G)
    ν {ω | ∀ i < n, splitCycle R F G i ω ∈ A i} = ∏ i ∈ Finset.range n, ρ (A i) := by
  intro ν ρ
  have hF' := hF.mono (selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace_le le_rfl
  have hstep := splitCycle_map_eq_prod μ R hR hfinite F hF G hG
  induction n generalizing A with
  | zero => simp
  | succ n ih =>
    let tail : Set (Mark α (Step α X)) := {ω | ∀ i < n, splitCycle R F G i ω ∈ A (i + 1)}
    have htail : MeasurableSet tail := by
      rw [show tail = ⋂ i : Fin n, splitCycle R F G i.val ⁻¹' A (i.val + 1) by
        ext ω
        simp [tail, Fin.forall_iff]]
      exact MeasurableSet.iInter (fun i =>
        (hA (i.val + 1)).preimage (measurable_splitCycle R hR F hF' G hG i.val))
    let obs := fun ω => (splitCycle R F G 0 ω, selectedPopulationFirstSplitSubtrees R ω 1)
    have hobs : Measurable obs :=
      (measurable_splitCycle R hR F hF' G hG 0).prodMk
        ((measurable_pi_apply 1).comp (selectedPopulationFirstSplitSubtrees_measurable R hR))
    have hevent : {ω | ∀ i < n + 1, splitCycle R F G i ω ∈ A i} =
        obs ⁻¹' (A 0 ×ˢ tail) := by
      ext ω
      constructor
      · intro h
        exact ⟨h 0 (Nat.zero_lt_succ n), fun i hi => h (i + 1) (Nat.succ_lt_succ hi)⟩
      · rintro ⟨hzero, htail⟩ (i | i) hi
        · exact hzero
        · exact htail i (Nat.lt_of_succ_lt_succ hi)
    rw [hevent, ← Measure.map_apply hobs ((hA 0).prod htail),
      show ν.map obs = ρ.prod ν from hstep, Measure.prod_prod,
      show ν tail = ∏ i ∈ Finset.range n, ρ (A (i + 1)) from
        ih (fun i => A (i + 1)) (fun i => hA (i + 1)), Finset.prod_range_succ', mul_comm]

lemma splitCycle_prefix_map_eq_pi
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hfinite : ∀ᵐ ω ∂offspringFieldLaw μ, selectedPopulationSplitCompletion R ω ≠ ⊤)
    (F : Mark α (Step α X) → D)
    (hF : Measurable[(selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace] F)
    (G : Mark α (Step α X) → E) (hG : Measurable G) (n : ℕ) :
    let ν := offspringFieldLaw μ
    let ρ := (ν.map F).prod (ν.map G)
    ν.map (fun ω (i : Fin n) => splitCycle R F G i.val ω) =
      Measure.pi (fun _ : Fin n => ρ) := by
  classical
  intro ν ρ
  have hF' := hF.mono (selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace_le le_rfl
  have hGπ : Measurable (fun ω (i : Fin n) => splitCycle R F G i.val ω) :=
    measurable_pi_iff.mpr fun i => measurable_splitCycle R hR F hF' G hG i.val
  refine (Measure.pi_eq fun A hA => ?_).symm
  let B (i : ℕ) := if hi : i < n then A ⟨i, hi⟩ else Set.univ
  have hB (i : ℕ) : MeasurableSet (B i) := by
    unfold B
    split
    · exact hA _
    · exact MeasurableSet.univ
  rw [Measure.map_apply hGπ (MeasurableSet.pi Set.countable_univ (fun i _ => hA i))]
  have hevent : (fun ω (i : Fin n) => splitCycle R F G i.val ω) ⁻¹' Set.pi Set.univ A =
      {ω | ∀ i < n, splitCycle R F G i ω ∈ B i} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Fin.forall_iff,
      Set.mem_ofPred_eq]
    exact forall_congr' fun i => forall_congr' fun hi => by simp [B, hi]
  rw [hevent, measure_splitCycles μ R hR hfinite F hF G hG n B hB]
  rw [← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i _
  simp [B, i.isLt, ρ, ν]

private lemma measure_splitCycle_partialSum_ge_le
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hfinite : ∀ᵐ ω ∂offspringFieldLaw μ, selectedPopulationSplitCompletion R ω ≠ ⊤)
    (F : Mark α (Step α X) → ℝ)
    (hF : Measurable[(selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace] F)
    (G : Mark α (Step α X) → E) (hG : Measurable G)
    (lam x : ℝ) (hlam : 0 < lam) (K : ℕ) :
    let ν := offspringFieldLaw μ
    let m := ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * F ω)) ∂ν
    ENNReal.ofReal (Real.exp (lam * x)) *
      ν {ω | ∃ k < K, x ≤
        ∑ j ∈ Finset.range (k + 1), (splitCycle R F G j ω).1} ≤
      ∑ k ∈ Finset.range K, m ^ (k + 1) := by
  classical
  intro ν m
  let ρ := (ν.map F).prod (ν.map G)
  let w (z : ℝ × E) := ENNReal.ofReal (Real.exp (lam * z.1))
  let q := ENNReal.ofReal (Real.exp (lam * x))
  let S (k : ℕ) (ω : Mark α (Step α X)) :=
    ∑ j ∈ Finset.range k, (splitCycle R F G j ω).1
  have hF' := hF.mono (selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace_le le_rfl
  have hw : Measurable w :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_fst)).ennreal_ofReal
  have hm : ∫⁻ z, w z ∂ρ = m := by
    have hfun : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (lam * t))) :=
      (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)).ennreal_ofReal
    change (∫⁻ z : ℝ × E, ENNReal.ofReal (Real.exp (lam * z.1)) ∂ρ) = _
    rw [← lintegral_map hfun measurable_fst]
    have hνG : IsProbabilityMeasure (ν.map G) := (Measure.isProbabilityMeasure_map_iff hG.aemeasurable).2 inferInstance
    rw [show ρ.map Prod.fst = ν.map F from by simp [ρ], lintegral_map hfun hF']
  have hmoment (k : ℕ) :
      (∫⁻ ω, ENNReal.ofReal (Real.exp (lam * S k ω)) ∂ν) = m ^ k := by
    let Y := fun ω (i : Fin k) => splitCycle R F G i.val ω
    have hY : Measurable Y :=
      measurable_pi_iff.mpr fun i => measurable_splitCycle R hR F hF' G hG i.val
    have hYlaw : ν.map Y = Measure.pi (fun _ : Fin k => ρ) :=
      splitCycle_prefix_map_eq_pi μ R hR hfinite F hF G hG k
    let H (z : Fin k → ℝ × E) := ∏ i, w (z i)
    have hH : Measurable H :=
      Finset.measurable_prod _ (fun i _ => hw.comp (measurable_pi_apply i))
    have hcomp (ω : Mark α (Step α X)) :
        ENNReal.ofReal (Real.exp (lam * S k ω)) = H (Y ω) := by
      dsimp only [S, H, Y, w]
      rw [Finset.mul_sum, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
      exact (Fin.prod_univ_eq_prod_range (fun j =>
        ENNReal.ofReal (Real.exp (lam * (splitCycle R F G j ω).1))) k).symm
    simp_rw [hcomp]
    rw [← lintegral_map hH hY, hYlaw]
    have hνF : IsProbabilityMeasure (ν.map F) := (Measure.isProbabilityMeasure_map_iff hF'.aemeasurable).2 inferInstance
    have hνG : IsProbabilityMeasure (ν.map G) := (Measure.isProbabilityMeasure_map_iff hG.aemeasurable).2 inferInstance
    have hρ : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
    have hi := iIndepFun_pi (μ := fun _ : Fin k => ρ) (X := fun _ => w)
      (fun _ => hw.aemeasurable)
    rw [show (∫⁻ z : Fin k → ℝ × E, H z ∂Measure.pi (fun _ : Fin k => ρ)) =
        ∏ i : Fin k, (∫⁻ z : Fin k → ℝ × E, w (z i) ∂Measure.pi (fun _ : Fin k => ρ)) from
      lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hi
        (fun i => hw.comp (measurable_pi_apply i))]
    have hcoord (i : Fin k) :
        (∫⁻ z : Fin k → ℝ × E, w (z i) ∂Measure.pi (fun _ : Fin k => ρ)) = m := by
      rw [← lintegral_map hw (measurable_pi_apply i),
        (measurePreserving_eval (fun _ : Fin k => ρ) i).map_eq, hm]
    simp only [hcoord, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  let event (k : ℕ) := {ω | x ≤ S (k + 1) ω}
  have htail (k : ℕ) : q * ν (event k) ≤ m ^ (k + 1) := by
    have hs : Measurable (S (k + 1)) := Finset.measurable_sum _ (fun j _ =>
      measurable_fst.comp (measurable_splitCycle R hR F hF' G hG j))
    have he : Measurable (fun ω => ENNReal.ofReal (Real.exp (lam * S (k + 1) ω))) :=
      (Real.continuous_exp.measurable.comp (measurable_const.mul hs)).ennreal_ofReal
    have hsub : event k ⊆ {ω | q ≤ ENNReal.ofReal (Real.exp (lam * S (k + 1) ω))} :=
      fun ω hω => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hω hlam.le))
    calc
      q * ν (event k) ≤ q * ν {ω | q ≤ ENNReal.ofReal (Real.exp (lam * S (k + 1) ω))} :=
        mul_le_mul_of_nonneg_left (measure_mono hsub) zero_le
      _ ≤ _ := (mul_meas_ge_le_lintegral he q).trans_eq (hmoment (k + 1))
  have hevent : {ω | ∃ k < K, x ≤ S (k + 1) ω} = ⋃ k ∈ Finset.range K, event k := by
    ext ω
    simp [event]
  change q * ν {ω | ∃ k < K, x ≤ S (k + 1) ω} ≤ _
  rw [hevent]
  calc
    _ ≤ q * ∑ k ∈ Finset.range K, ν (event k) :=
      mul_le_mul_of_nonneg_left (measure_biUnion_finset_le _ _) zero_le
    _ = ∑ k ∈ Finset.range K, q * ν (event k) := Finset.mul_sum ..
    _ ≤ _ := Finset.sum_le_sum fun k _ => htail k

lemma measure_firstSuccessfulSplitCycle_partialSum_ge_le
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select)
    (hfinite : ∀ᵐ ω ∂offspringFieldLaw μ, selectedPopulationSplitCompletion R ω ≠ ⊤)
    (F : Mark α (Step α X) → ℝ)
    (hF : Measurable[(selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace] F)
    (lower upper duration : ℕ) (lam x : ℝ) (hlam : 0 < lam) (K : ℕ) :
    let G := growthTrialSuccess growth lower upper duration
    let ν := offspringFieldLaw μ
    let m := ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * F ω)) ∂ν
    ENNReal.ofReal (Real.exp (lam * x)) *
      ν {ω | ∃ k < K, (splitCycle R F G k ω).2 ∧
        (∀ j < k, ¬ (splitCycle R F G j ω).2) ∧
        x ≤ ∑ j ∈ Finset.range (k + 1), (splitCycle R F G j ω).1} ≤
      ∑ k ∈ Finset.range K, m ^ (k + 1) := by
  intro G ν m
  have hG : Measurable G := by
    apply measurableSet_setOfPred.mp
    exact (generationFiltration (M := Step α X)).le duration _
      (growthTrialSuccess_measurable growth hgrowth lower upper duration)
  refine (mul_le_mul_of_nonneg_left (measure_mono ?_) zero_le).trans
    (measure_splitCycle_partialSum_ge_le μ R hR hfinite F hF G hG lam x hlam K)
  intro ω hω
  obtain ⟨k, hk, _, _, hsum⟩ := hω
  exact ⟨k, hk, hsum⟩

private lemma splitCycle_independence
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hfinite : ∀ᵐ ω ∂offspringFieldLaw μ, selectedPopulationSplitCompletion R ω ≠ ⊤)
    (F : Mark α (Step α X) → D)
    (hF : Measurable[(selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace] F)
    (G : Mark α (Step α X) → E) (hG : Measurable G) :
    let ν := offspringFieldLaw μ
    let ρ := (ν.map F).prod (ν.map G)
    iIndepFun (splitCycle R F G) ν ∧ ∀ n, ν.map (splitCycle R F G n) = ρ := by
  intro ν ρ
  have hFp := hF.mono (selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace_le le_rfl
  have hC := measurable_splitCycle R hR F hFp G hG
  let _ : IsProbabilityMeasure (ν.map F) :=
    (Measure.isProbabilityMeasure_map_iff hFp.aemeasurable).2 inferInstance
  let _ : IsProbabilityMeasure (ν.map G) :=
    (Measure.isProbabilityMeasure_map_iff hG.aemeasurable).2 inferInstance
  let _ : IsProbabilityMeasure ρ := inferInstanceAs (IsProbabilityMeasure ((ν.map F).prod (ν.map G)))
  have hLaw (n : ℕ) : ν.map (splitCycle R F G n) = ρ := by
    let p : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
    have hπ := splitCycle_prefix_map_eq_pi μ R hR hfinite F hF G hG (n + 1)
    have hfun : splitCycle R F G n =
        (Function.eval p) ∘ (fun ω (i : Fin (n + 1)) => splitCycle R F G i.val ω) := rfl
    rw [hfun, ← Measure.map_map (measurable_pi_apply p) (measurable_pi_iff.mpr fun i => hC i.val)]
    change (ν.map (fun ω (i : Fin (n + 1)) => splitCycle R F G i.val ω)).map (Function.eval p) = ρ
    rw [hπ]
    simp [ρ, ν, Measure.pi_map_eval]
  refine ⟨iIndepFun_iff_finset.mpr ?_, hLaw⟩
  intro s
  let k := s.sup id + 1
  have hprefix : iIndepFun (fun i : Fin k => splitCycle R F G i.val) ν := by
    apply (iIndepFun_iff_map_fun_eq_pi_map (fun i : Fin k => (hC i.val).aemeasurable)).2
    simp_rw [hLaw]
    exact splitCycle_prefix_map_eq_pi μ R hR hfinite F hF G hG k
  let e (j : ↑s) : Fin k :=
    ⟨j.val, Nat.lt_succ_of_le (Finset.le_sup (f := id) j.property)⟩
  have hinj : Function.Injective e := fun _ _ h => Subtype.ext (congrArg Fin.val h)
  have he := hprefix.precomp (g := e) hinj
  exact he

/-- The positive displacements through the first successful growth trial
have expected sum equal to the one-cycle positive mean divided by the
growth-trial success probability. -/
lemma integral_splitCycle_positiveDisplacement_through_success
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hfinite : ∀ᵐ ω ∂offspringFieldLaw μ, selectedPopulationSplitCompletion R ω ≠ ⊤)
    (F : Mark α (Step α X) → ℝ)
    (hF : Measurable[(selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace] F)
    (hFi : Integrable F (offspringFieldLaw μ))
    (G : Mark α (Step α X) → E) (hG : Measurable G)
    (success : Set E) (hsuccess : MeasurableSet success)
    (hp : 0 < (offspringFieldLaw μ).real (G ⁻¹' success)) :
    let ν := offspringFieldLaw μ
    let D := splitCycle R F G
    let B : Set (ℝ × E) := Prod.snd ⁻¹' success
    let Y := fun z : ℝ × E => max z.1 0
    Integrable (fun ω => ∑' n, geometricPrefixRewardTerm D B Y n ω) ν ∧
      (∫ ω, ∑' n, geometricPrefixRewardTerm D B Y n ω ∂ν) =
        (∫ ω, max (F ω) 0 ∂ν) / ν.real (G ⁻¹' success) := by
  intro ν D B Y
  let ρ := (ν.map F).prod (ν.map G)
  have hFp := hF.mono (selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace_le le_rfl
  let _ : IsProbabilityMeasure (ν.map F) :=
    (Measure.isProbabilityMeasure_map_iff hFp.aemeasurable).2 inferInstance
  let _ : IsProbabilityMeasure (ν.map G) :=
    (Measure.isProbabilityMeasure_map_iff hG.aemeasurable).2 inferInstance
  let _ : IsProbabilityMeasure ρ := inferInstanceAs (IsProbabilityMeasure ((ν.map F).prod (ν.map G)))
  obtain ⟨hDi, hLaw⟩ := splitCycle_independence μ R hR hfinite F hF G hG
  have hD := measurable_splitCycle R hR F hFp G hG
  have hB : MeasurableSet B := measurable_snd hsuccess
  have hY : Measurable Y := measurable_fst.max measurable_const
  have hYmeas : Measurable (fun y : ℝ => max y 0) := measurable_id.max measurable_const
  have hYi : Integrable Y ρ := by
    have h : Integrable (fun y : ℝ => max y 0) (ν.map F) :=
      (integrable_map_measure hYmeas.aestronglyMeasurable hFp.aemeasurable).2 hFi.real_toNNReal
    exact h.comp_fst (ν.map G)
  have hp' : ρ.real B = ν.real (G ⁻¹' success) := by
    have hb : ρ B = ν (G ⁻¹' success) := by
      change ((ν.map F).prod (ν.map G)) (Prod.snd ⁻¹' success) = _
      rw [← Measure.map_apply measurable_snd hsuccess, Measure.map_snd_prod,
        measure_univ, one_smul, Measure.map_apply hG hsuccess]
    exact congrArg ENNReal.toReal hb
  refine ⟨iidGeometricReward_integrable ν ρ D hD hDi hLaw B hB Y hY hYi _ hp hp', ?_⟩
  rw [iidGeometricReward_integral ν ρ D hD hDi hLaw B hB Y hY hYi _ hp hp']
  congr 1
  change (∫ z, max z.1 0 ∂(ν.map F).prod (ν.map G)) = _
  rw [integral_fun_fst (fun y : ℝ => max y 0), probReal_univ, one_smul,
    integral_map hFp.aemeasurable hYmeas.aestronglyMeasurable]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas
