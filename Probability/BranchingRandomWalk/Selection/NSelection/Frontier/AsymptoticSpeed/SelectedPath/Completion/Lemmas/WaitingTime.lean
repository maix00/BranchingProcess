/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Lemmas.RecursiveClock
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.TrialIndependence
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.SampledMark
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitTime.Finite
import Probability.Sequence.IID.GeometricReward.ExponentialTransform
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop

/-!
# Waiting time to a split along the selected path

## Internal proof declarations

* `splitWaitingTime`: the number of failed split marks in a cycle, equal to
  the generation of the split parent when the cycle starts in generation zero.
* `splitWaitingTime_measurable`: the waiting time is measurable at the birth
  generation of the split children.
* `lintegral_exp_splitWaitingTime`: if $p$ is the split probability, then
  $\mathbb E[e^{\theta G}]=p/(1-e^\theta(1-p))$ whenever the ratio is below
  one. The identity also holds in extended nonnegative reals.

* `splitCount_at_waitingTime_sum_ae`: at generation
  $K+\sum_{j<K}G_j$, precisely $K$ splits have occurred on the selected path.
* `exists_splitWaitingTime_expParameter`: a positive exponent $\theta$
  with $e^\theta(1-p)<1$ exists when $p>0$.
* `one_le_splitWaitingTime_expMoment`: $\mathbb E e^{\theta G}\ge1$ for $\theta\ge0$.
* `measure_splitWaitingTime_sum_ge_le`: the probability that
  $\sum_{j<K}G_j\ge x$ is at most $e^{-\theta x}(\mathbb E e^{\theta G})^K$.

This is the waiting time used in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 4, Theorems 1.1 and 1.2.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas

open Combinatorics.Branching Combinatorics.UlamHarris
open Combinatorics.Branching.Step.FiniteSelection
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.BranchingRandomWalk.Selection.Stepwise.SplitTime
open SelectedPath.GrowthTrial

variable {α X : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [LinearOrder α] [OrderBot α] [MeasurableSpace X]

noncomputable def splitWaitingTime (R : Step.FiniteSelection α X)
    (ω : Mark α (Step α X)) : ℕ :=
  (selectedPopulationSplitCompletion R ω).untopD 0 - 1

omit [LinearOrder α] [OrderBot α] in
lemma splitWaitingTime_measurable
    (R : Step.FiniteSelection α X) (hR : Measurable R.select) :
    Measurable[(selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace]
      (splitWaitingTime R) :=
  (measurable_of_countable fun n : ℕ => n - 1).comp
    ((WithTop.measurable_untopD 0).comp (selectedPopulationSplitCompletion_isStoppingTime R hR).measurable)

set_option maxHeartbeats 600000 in
lemma lintegral_exp_splitWaitingTime
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hne : μ {ξ | (R ξ).Nonempty} = 1) (hp : 0 < μ (splitBy R)) (θ : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * splitWaitingTime R ω)) ∂offspringFieldLaw μ) =
      μ (splitBy R) / (1 - ENNReal.ofReal (Real.exp θ) * (1 - μ (splitBy R))) := by
  let P := RootIndexed.stepFieldLaw (Root := PUnit.{1}) μ
  let eval : RootIndexed.StepField PUnit.{1} α X → Mark α (Step α X) := fun ω => ω PUnit.unit.{1}
  have heval : Measurable eval := measurable_pi_apply _
  have hevalLaw : P.map eval = offspringFieldLaw μ := RootIndexed.stepFieldLaw_root_marginal μ _
  have hB := splitBy_measurable R hR
  have hF := (splitWaitingTime_measurable R hR).mono
    (selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace_le le_rfl
  have hw : Measurable (fun ω => ENNReal.ofReal (Real.exp (θ * splitWaitingTime R ω))) := by
    fun_prop
  have hA : (∫⁻ x, ENNReal.ofReal (Real.exp (θ * (1 : ℝ))) *
      (splitBy R)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) =
        ENNReal.ofReal (Real.exp θ) * (1 - μ (splitBy R)) := by
    rw [lintegral_const_mul _ (measurable_const.indicator hB.compl),
      lintegral_indicator_const hB.compl, prob_compl_eq_one_sub hB]
    simp
  have htransform := iidGeometricFailureExponentialTransform P μ (Coupling.step R PUnit.unit.{1})
    (Coupling.step_measurable R hR _) (Coupling.step_iIndepFun μ R hR _)
    (Coupling.step_law μ R hR _) (splitBy R) hB (fun _ => 1) measurable_const θ _ rfl _ hA
  rw [← hevalLaw, lintegral_map hw heval, ← htransform]
  apply lintegral_congr_ae
  have hfinite' := selectedPopulationSplitCompletion_ae_finite_of_nonempty_and_split_pos μ R hR hne hB hp
  have hfinite : ∀ᵐ ω ∂P, selectedPopulationSplitCompletion R (eval ω) ≠ ⊤ :=
    ae_of_ae_map heval.aemeasurable (by rwa [hevalLaw])
  have hall : ∀ᵐ ω ∂P, ∀ u, (R (eval ω u)).Nonempty := by
    apply ae_all_iff.2
    intro u
    have hset : MeasurableSet {ξ | (R ξ).Nonempty} := by
      rw [show {ξ | (R ξ).Nonempty} = (fun ξ => (R ξ).card) ⁻¹' Set.Ioi 0 by
        ext ξ
        exact Finset.card_pos.symm]
      exact ((measurable_of_countable fun s : Finset α => s.card).comp hR) measurableSet_Ioi
    have hu : Measurable (fun ω => eval ω u) := (measurable_pi_apply u).comp heval
    apply (ae_mem_iff_measure_eq (hu hset).nullMeasurableSet).2
    rw [← Measure.map_apply hu hset, RootIndexed.stepFieldLaw_coordinate_marginal μ _, hne, measure_univ]
  filter_upwards [hfinite, hall] with ω hf hn
  obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp hf
  cases j with
  | zero => exact (selectedPopulationSplitCompletion_ne_zero R _ hj.symm).elim
  | succ n =>
    have hraw := selectedPopulationRawSplitTime_eq_of_completion_eq R _ n hj.symm
    obtain ⟨hs, hbefore⟩ := first_sampled_split_of_rawSplitTime_eq R PUnit.unit.{1} ω n hn hraw
    rw [geometricFailureExponentialTerm_tsum_eq_of_first_success
      (Coupling.step R PUnit.unit.{1}) (splitBy R) (fun _ => 1) θ ω n hs hbefore]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    change ENNReal.ofReal (Real.exp (θ * splitWaitingTime R (eval ω))) = _
    unfold splitWaitingTime
    rw [hj.symm, WithTop.untopD_coe, Nat.add_sub_cancel]

omit [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α] in
lemma exists_splitWaitingTime_expParameter
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hp : 0 < μ (splitBy R)) :
    ∃ θ : ℝ, 0 < θ ∧ ENNReal.ofReal (Real.exp θ) * (1 - μ (splitBy R)) < 1 := by
  let p := (μ (splitBy R)).toReal
  have hp0 : 0 < p := ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top _ _)
  have hp1 : μ (splitBy R) ≤ 1 := (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  let θ := Real.log (1 + p / 2)
  refine ⟨θ, Real.log_pos (by linarith), ?_⟩
  have hsub : 1 - μ (splitBy R) ≠ ∞ := (tsub_le_self.trans_lt ENNReal.one_lt_top).ne
  have hfin : ENNReal.ofReal (Real.exp θ) * (1 - μ (splitBy R)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsub
  apply (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _),
    ENNReal.toReal_sub_of_le hp1 ENNReal.one_ne_top, ENNReal.toReal_one]
  change Real.exp θ * (1 - p) < 1
  rw [show Real.exp θ = 1 + p / 2 from Real.exp_log (by positivity)]
  nlinarith [sq_nonneg p]

lemma one_le_splitWaitingTime_expMoment
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hne : μ {ξ | (R ξ).Nonempty} = 1) (hp : 0 < μ (splitBy R))
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hratio : ENNReal.ofReal (Real.exp θ) * (1 - μ (splitBy R)) < 1) :
    1 ≤ (μ (splitBy R) / (1 - ENNReal.ofReal (Real.exp θ) * (1 - μ (splitBy R)))).toReal := by
  have hfinite := (ENNReal.div_lt_top (measure_ne_top μ (splitBy R))
    (ne_of_gt (tsub_pos_of_lt hratio))).ne
  have h : (1 : ℝ≥0∞) ≤ μ (splitBy R) /
      (1 - ENNReal.ofReal (Real.exp θ) * (1 - μ (splitBy R))) := by
    rw [← lintegral_exp_splitWaitingTime μ R hR hne hp θ]
    calc
      1 = ∫⁻ _ : Mark α (Step α X), 1 ∂offspringFieldLaw μ := by simp
      _ ≤ _ := lintegral_mono fun ω => by
        simpa only [ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal (Real.one_le_exp (by positivity : 0 ≤ θ * splitWaitingTime R ω))
  simpa using ENNReal.toReal_mono hfinite h

omit [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] in
private lemma splitWaitingTime_sum_succ
    (R : Step.FiniteSelection α X) (K : ℕ) (ω : Mark α (Step α X)) :
    (∑ j ∈ Finset.range (K + 1), (splitCycle R (splitWaitingTime R) (fun _ => PUnit.unit.{1}) j ω).1) =
      splitWaitingTime R ω +
        ∑ j ∈ Finset.range K,
          (splitCycle R (splitWaitingTime R) (fun _ => PUnit.unit.{1}) j
            (selectedPopulationFirstSplitSubtrees R ω 1)).1 := by
  rw [Finset.sum_range_succ']
  change (∑ k ∈ Finset.range K, (splitCycle R (splitWaitingTime R) (fun _ => PUnit.unit.{1})
    k (selectedPopulationFirstSplitSubtrees R ω 1)).1) + splitWaitingTime R ω = _
  exact Nat.add_comm _ _

lemma splitCount_at_waitingTime_sum_ae
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hne : μ {ξ | (R ξ).Nonempty} = 1) (hp : 0 < μ (splitBy R)) (K : ℕ) :
    ∀ᵐ ω ∂offspringFieldLaw μ, ∀ (Root : Type) (r : Root)
      (field : RootIndexed.StepField Root α X), field r = ω →
      splitCount R r (K + ∑ j ∈ Finset.range K,
        (splitCycle R (splitWaitingTime R) (fun _ => PUnit.unit.{1}) j ω).1) field = K := by
  let ν := offspringFieldLaw μ
  let child : Mark α (Step α X) → Mark α (Step α X) :=
    fun ω => selectedPopulationFirstSplitSubtrees R ω 1
  have hfin := selectedPopulationSplitCompletion_ae_finite_of_nonempty_and_split_pos
    μ R hR hne (splitBy_measurable R hR) hp
  have hm : Measurable child :=
    (measurable_pi_apply 1).comp (selectedPopulationFirstSplitSubtrees_measurable R hR)
  have hlaw : ν.map child = ν := by
    change ν.map ((fun f : Fin 2 → Mark α (Step α X) => f 1) ∘
      selectedPopulationFirstSplitSubtrees R) = ν
    rw [← Measure.map_map (measurable_pi_apply 1) (selectedPopulationFirstSplitSubtrees_measurable R hR),
      selectedPopulationFirstSplitSubtrees_map_eq_product μ R hR hfin]
    exact (measurePreserving_eval_infinitePi (fun _ : Fin 2 => ν) 1).map_eq
  have hall : ∀ᵐ ω ∂ν, ∀ u, (R (ω u)).Nonempty := by
    apply ae_all_iff.2
    intro u
    have hset : MeasurableSet {ξ | (R ξ).Nonempty} := by
      rw [show {ξ | (R ξ).Nonempty} = (fun ξ => (R ξ).card) ⁻¹' Set.Ioi 0 by
        ext ξ
        exact Finset.card_pos.symm]
      exact ((measurable_of_countable fun s : Finset α => s.card).comp hR) measurableSet_Ioi
    have hu : Measurable (fun ω : Mark α (Step α X) => ω u) := measurable_pi_apply _
    apply (ae_mem_iff_measure_eq (hu hset).nullMeasurableSet).2
    rw [← Measure.map_apply hu hset, ProbabilityTheory.BranchingProcess.offspringFieldLaw_coordinate,
      hne, measure_univ]
  induction K with
  | zero => exact ae_of_all ν fun _ _ _ _ _ => by simp [splitCount]
  | succ K ih =>
    have htail := ae_of_ae_map hm.aemeasurable (by rwa [hlaw] : ∀ᵐ _ ∂ν.map child, _)
    filter_upwards [hfin, hall, htail] with ω hω hnonempty ht
    intro Root r field hfield
    obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp hω
    cases j with
    | zero => exact (selectedPopulationSplitCompletion_ne_zero R _ hj.symm).elim
    | succ n =>
      have hraw := selectedPopulationRawSplitTime_eq_of_completion_eq R _ n hj.symm
      rw [← hfield] at hraw
      obtain ⟨hs, hbefore⟩ :=
        first_sampled_split_of_rawSplitTime_eq R r field n (hfield ▸ hnonempty) hraw
      have halive (i : ℕ) : isAlive R r i field := by
        induction i with
        | zero => trivial
        | succ i hi => exact ⟨hi, hfield ▸ hnonempty _⟩
      have hroot := (firstSplitRoots_eq_of_rawSplitTime_eq R r field n (hfield ▸ hnonempty) hraw).2
      have heq : continuationFieldAtSplit R r n field PUnit.unit.{1} = child ω := by
        funext v
        change continuationFieldAtSplit R r n field PUnit.unit.{1} v =
          selectedPopulationFirstSplitSubtrees R ω 1 v
        rw [← hfield]
        unfold selectedPopulationFirstSplitSubtrees selectedSubtreeStepFieldVector subtreeStepFieldVector
        simp only [subtreeStepField, continuationFieldAtSplit, continuationPrefix, hroot]
      have hsplit : splitWaitingTime R ω = n := by
        unfold splitWaitingTime
        rw [hj.symm, WithTop.untopD_coe, Nat.add_sub_cancel]
      rw [splitWaitingTime_sum_succ, hsplit]
      let m := K + ∑ j ∈ Finset.range K, (splitCycle R (splitWaitingTime R) (fun _ => PUnit.unit.{1})
        j (child ω)).1
      rw [show K + 1 + (n + ∑ j ∈ Finset.range K,
          (splitCycle R (splitWaitingTime R) (fun _ => PUnit.unit.{1})
            j (selectedPopulationFirstSplitSubtrees R ω 1)).1) = n + 1 + m by
        dsimp [m, child]
        omega,
        splitCount_add_after_first_split R r field n m (halive _) hs hbefore]
      rw [ht PUnit.{1} PUnit.unit.{1} _ heq, Nat.add_comm]

lemma measure_splitWaitingTime_sum_ge_le
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hne : μ {ξ | (R ξ).Nonempty} = 1) (hp : 0 < μ (splitBy R))
    (θ x : ℝ) (hθ : 0 < θ) (K : ℕ) :
    let ν := offspringFieldLaw μ
    let B := μ (splitBy R) / (1 - ENNReal.ofReal (Real.exp θ) * (1 - μ (splitBy R)))
    ν {ω | x ≤ ∑ j ∈ Finset.range K,
      ((splitCycle R (splitWaitingTime R) (fun _ => PUnit.unit.{1}) j ω).1 : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-θ * x)) * B ^ K := by
  intro ν B
  let F : Mark α (Step α X) → ℝ := fun ω => splitWaitingTime R ω
  let G : Mark α (Step α X) → PUnit.{1} := fun _ => PUnit.unit.{1}
  have hfin := selectedPopulationSplitCompletion_ae_finite_of_nonempty_and_split_pos
    μ R hR hne (splitBy_measurable R hR) hp
  have hF : Measurable[(selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace] F :=
    (measurable_of_countable fun n : ℕ => (n : ℝ)).comp (splitWaitingTime_measurable R hR)
  have hF' := hF.mono (selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace_le le_rfl
  let S (ω : Mark α (Step α X)) := ∑ j ∈ Finset.range K, (splitCycle R F G j ω).1
  have hS (j : ℕ) (ω : Mark α (Step α X)) : (splitCycle R F G j ω).1 =
      ((splitCycle R (splitWaitingTime R) (fun _ => PUnit.unit.{1}) j ω).1 : ℝ) := by
    induction j generalizing ω with
    | zero => rfl
    | succ j ih => exact ih _
  change ν {ω | x ≤ ∑ j ∈ Finset.range K,
    ((splitCycle R (splitWaitingTime R) (fun _ => PUnit.unit.{1}) j ω).1 : ℝ)} ≤ _
  rw [show {ω | x ≤ ∑ j ∈ Finset.range K,
      ((splitCycle R (splitWaitingTime R) (fun _ => PUnit.unit.{1}) j ω).1 : ℝ)} =
      {ω | x ≤ S ω} by
    ext ω
    change (x ≤ ∑ j ∈ Finset.range K,
      ((splitCycle R (splitWaitingTime R) (fun _ => PUnit.unit.{1}) j ω).1 : ℝ)) ↔ x ≤ S ω
    rw [show S ω = _ from Finset.sum_congr rfl (fun j _ => hS j ω)]]
  have hs : Measurable S := Finset.measurable_sum _ fun j _ =>
    measurable_fst.comp (measurable_splitCycle R hR F hF' G measurable_const j)
  have he : Measurable (fun ω => ENNReal.ofReal (Real.exp (θ * S ω))) :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul hs)).ennreal_ofReal
  let q := ENNReal.ofReal (Real.exp (θ * x))
  have hbound : q * ν {ω | x ≤ S ω} ≤ B ^ K := by
    calc
      _ ≤ q * ν {ω | q ≤ ENNReal.ofReal (Real.exp (θ * S ω))} :=
        mul_le_mul_of_nonneg_left (measure_mono (fun _ h =>
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h hθ.le)))) zero_le
      _ ≤ _ := (mul_meas_ge_le_lintegral he q).trans_eq (by
        rw [lintegral_exp_splitCycle_sum μ R hR hfin F hF G measurable_const θ K]
        exact congrArg (· ^ K) (lintegral_exp_splitWaitingTime μ R hR hne hp θ))
  let inv := ENNReal.ofReal (Real.exp (-θ * x))
  have hinv : inv * q = 1 := by
    dsimp [inv, q]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add,
      show -θ * x + θ * x = 0 by ring, Real.exp_zero, ENNReal.ofReal_one]
  simpa only [← mul_assoc, hinv, one_mul] using mul_le_mul_of_nonneg_left hbound (zero_le (a := inv))

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas
