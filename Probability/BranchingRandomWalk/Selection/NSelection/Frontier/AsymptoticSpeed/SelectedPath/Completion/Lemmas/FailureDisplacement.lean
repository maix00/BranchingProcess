/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Assumptions.Moments
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.SampledMark
import Probability.Sequence.IID.GeometricReward.ExponentialTransform
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Lemmas.RecursiveClock
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitTime.Finite
import Probability.BranchingRandomWalk.Spine.GenerationBranching.Decomposition

/-!
# Exponential moment of the displacement before the first split

## Internal proof declarations

* `splitWaitingDisplacement` is $X_1$, the sum of the leftmost displacements
  strictly before the first split mark. It is measurable at split completion.
* `splitWaitingDisplacement_eq_parentPosition` identifies that sum with
  the potential of the current split's parent relative to the cycle origin.
* `splitChildPosition_le_splitWaitingDisplacement_add` bounds a split
  child's potential by the parent's potential plus the split cutoff $M$.
* `exists_splitWaitingDisplacement_exponentialMoment` identifies its
  exponential moment under the pre-sampled tree law.


This is the single-cycle transform in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 4, Theorem 1.1 at $a=0$.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.BranchingRandomWalk.Selection.Stepwise.SplitTime
open SelectedPath.GrowthTrial
open Combinatorics.Branching.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath
open Combinatorics.Branching.Step.FiniteSelection

private lemma exists_failureWeight_lt_one
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (B : Set X) (hB : MeasurableSet B) (hp : 0 < μ B)
    (Y : X → ℝ) (hY : Measurable Y)
    (lam₀ : ℝ) (hlam₀ : 0 < lam₀) (hexp : Integrable (fun x => Real.exp (lam₀ * Y x)) μ) :
    ∃ lam > (0 : ℝ), (∫⁻ x, ENNReal.ofReal (Real.exp (lam * Y x)) *
      Bᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) < 1 := by
  let lam (n : ℕ) := lam₀ * (1 / ((n : ℝ) + 1))
  have hLam (n : ℕ) : 0 < lam n := by dsimp [lam]; positivity
  have hLamle (n : ℕ) : lam n ≤ lam₀ := by
    dsimp [lam]
    exact mul_le_of_le_one_right hlam₀.le
      (div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity))
  let f (n : ℕ) := Bᶜ.indicator (fun x => Real.exp (lam n * Y x))
  have hf (n : ℕ) : Measurable (f n) :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul hY)).indicator hB.compl
  have hn (n : ℕ) (x : X) : 0 ≤ f n x := by
    by_cases hx : x ∈ B <;> simp [f, hx, (Real.exp_pos _).le]
  have hbound (n : ℕ) (x : X) : ‖f n x‖ ≤ 1 + Real.exp (lam₀ * Y x) := by
    rw [Real.norm_of_nonneg (hn n x)]
    by_cases hx : x ∈ Bᶜ
    · rw [show f n x = Real.exp (lam n * Y x) from Set.indicator_of_mem hx _]
      by_cases hy : 0 ≤ Y x
      · have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hLamle n) hy)
        linarith
      · have he : Real.exp (lam n * Y x) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos (hLam n).le (le_of_not_ge hy))
        linarith [Real.exp_pos (lam₀ * Y x)]
    · rw [show f n x = 0 from Set.indicator_of_notMem hx _]
      positivity
  have hdom := (integrable_const (1 : ℝ)).add hexp
  have hfi (n : ℕ) : Integrable (f n) μ :=
    hdom.mono' (hf n).aestronglyMeasurable (ae_of_all _ (hbound n))
  have hlim : Tendsto lam atTop (𝓝 0) := by
    simpa [lam] using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul lam₀)
  have hconv : Tendsto (fun n => ∫ x, f n x ∂μ) atTop
      (𝓝 (∫ x, Bᶜ.indicator (fun _ => (1 : ℝ)) x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence _ (fun n => (hf n).aestronglyMeasurable)
      hdom (fun n => ae_of_all _ (hbound n))
    apply ae_of_all
    intro x
    by_cases hx : x ∈ Bᶜ
    · have he : Tendsto (fun n => Real.exp (lam n * Y x)) atTop (𝓝 (Real.exp (0 * Y x))) :=
        Real.continuous_exp.continuousAt.tendsto.comp (hlim.mul_const (Y x))
      simpa [f, hx] using he
    · simp [f, hx]
  have hsmall : (∫ x, Bᶜ.indicator (fun _ => (1 : ℝ)) x ∂μ) < 1 := by
    rw [integral_indicator_const _ hB.compl, measureReal_compl hB]
    simpa [measureReal_def] using (sub_lt_self (1 : ℝ)
      (ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top _ _)))
  obtain ⟨n, hn'⟩ := (hconv.eventually_lt_const hsmall).exists
  refine ⟨lam n, hLam n, ?_⟩
  have heq (x : X) : ENNReal.ofReal (f n x) =
      ENNReal.ofReal (Real.exp (lam n * Y x)) * Bᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x := by
    by_cases hx : x ∈ Bᶜ <;> simp [f, hx]
  simp_rw [← heq]
  rw [← ofReal_integral_eq_lintegral_ofReal (hfi n) (ae_of_all _ (hn n))]
  exact ENNReal.ofReal_lt_one.mpr hn'

private lemma exists_firstSplit_failureDisplacement_exponentialMoment
    {Root ι X : Type*} [MeasurableSpace X]
    (L : StepLaw ι ℕ X) [IsProbabilityMeasure L.raw]
    (hexp : HasLeftmostPositiveExponentialMoment L)
    (R : Step.FiniteSelection ℕ ℝ) (hR : Measurable R.select)
    (hp : 0 < L.sortedPotentialImage (splitBy R)) (r : Root) :
    let μ := L.sortedPotentialImage
    let P := RootIndexed.stepFieldLaw (Root := Root) μ
    let Y := fun ξ : Step ℕ ℝ => value' ξ 0
    let B := splitBy R
    ∃ lam > (0 : ℝ), let A := ∫⁻ x, ENNReal.ofReal (Real.exp (lam * Y x)) *
          Bᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ
      A < 1 ∧
        (∫⁻ ω, ∑' n, geometricFailureExponentialTerm (Coupling.step R r) B Y lam n ω ∂P) =
          μ B / (1 - A) ∧ μ B / (1 - A) < ∞ := by
  let μ := L.sortedPotentialImage
  let P := RootIndexed.stepFieldLaw (Root := Root) μ
  let Y := fun ξ : Step ℕ ℝ => value' ξ 0
  let B := splitBy R
  have hB := splitBy_measurable R hR
  have hY : Measurable Y := value'_measurable 0
  obtain ⟨lam₀, hlam₀, hraw⟩ := hexp
  have hs : Integrable (fun ξ : Step ℕ X => Real.exp (lam₀ * ξ.potentialValue' L.potential 0))
      L.sorted := by
    rw [StepLaw.sorted]
    have hm : Measurable (fun ξ : Step ℕ X =>
        Real.exp (lam₀ * ξ.potentialValue' L.potential 0)) :=
      Real.continuous_exp.measurable.comp
        (measurable_const.mul (Step.potentialValue'_measurable L.potential 0))
    apply (integrable_map_measure hm.aestronglyMeasurable
      L.ordering.measurable_ordered.aemeasurable).2
    exact hraw
  have hμ : Integrable (fun ξ => Real.exp (lam₀ * Y ξ)) μ := by
    change Integrable _ (L.sorted.map (fun ξ => ξ.map L.potential))
    apply (integrable_map_measure ((Real.continuous_exp.measurable.comp
      (measurable_const.mul hY)).aestronglyMeasurable)
      (Step.map_measurable L.potential.measurable_toFun).aemeasurable).2
    exact hs
  obtain ⟨lam, hLam, hA⟩ := exists_failureWeight_lt_one μ B hB hp Y hY lam₀ hlam₀ hμ
  have htransform := iidGeometricFailureExponentialTransform P μ (Coupling.step R r)
    (Coupling.step_measurable R hR r) (Coupling.step_iIndepFun μ R hR r)
    (Coupling.step_law μ R hR r) B hB Y hY lam _ rfl _ rfl
  exact ⟨lam, hLam, hA, htransform,
    ENNReal.div_lt_top (measure_ne_top _ _) (ne_of_gt (tsub_pos_of_lt hA))⟩

private abbrev singletonField (ω : Mark ℕ (Step ℕ ℝ)) : RootIndexed.StepField PUnit.{1} ℕ ℝ :=
  fun _ => ω

private noncomputable def waitingSum (R : Step.FiniteSelection ℕ ℝ) (n : ℕ)
    (ω : Mark ℕ (Step ℕ ℝ)) : ℝ :=
  ∑ i ∈ Finset.range n, value' (Coupling.step R PUnit.unit.{1} i (singletonField ω)) 0

/-- Signed displacement accumulated before the split mark of the current cycle. -/
noncomputable def splitWaitingDisplacement (R : Step.FiniteSelection ℕ ℝ)
    (ω : Mark ℕ (Step ℕ ℝ)) : ℝ :=
  waitingSum R ((selectedPopulationSplitCompletion R ω).untopD 0 - 1) ω

lemma splitWaitingDisplacement_measurable
    (R : Step.FiniteSelection ℕ ℝ) (hR : Measurable R.select) :
    Measurable[(selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace]
      (splitWaitingDisplacement R) := by
  classical
  let σ := selectedPopulationSplitCompletion R
  let hσ := selectedPopulationSplitCompletion_isStoppingTime R hR
  have hsingleton (n : ℕ) :
      @Measurable (Mark ℕ (Step ℕ ℝ)) (RootIndexed.StepField PUnit.{1} ℕ ℝ)
        (generationFiltration (M := Step ℕ ℝ) n) (RootIndexed.stepFiltration n)
        singletonField := by
    let markedSpace : MeasurableSpace (RootIndexed.StepField PUnit.{1} ℕ ℝ) := inferInstance
    let coordinates := fun (q : PUnit.{1} × TreeNode ℕ)
      (field : RootIndexed.StepField PUnit.{1} ℕ ℝ) => field q.1 q.2
    have hc (q : PUnit.{1} × TreeNode ℕ) : Measurable (coordinates q) :=
      (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
    exact @Filtration.measurable_to_generatedByCoordinates
      (Mark ℕ (Step ℕ ℝ)) (RootIndexed.StepField PUnit.{1} ℕ ℝ) (PUnit.{1} × TreeNode ℕ)
      ℕ (fun _ => Step ℕ ℝ) (generationFiltration n) markedSpace _ _
      (fun q => q.2.length + 1) coordinates hc singletonField n
      (fun q hq => mark_measurable_of_depth_lt q.2 n (Nat.succ_le_iff.mp hq))
  have hsum (n : ℕ) :
      Measurable[generationFiltration (M := Step ℕ ℝ) n] (waitingSum R (n - 1)) := by
    unfold waitingSum
    apply Finset.measurable_sum
    intro i hi
    have hin : i + 1 ≤ n := by
      have := Finset.mem_range.mp hi
      omega
    exact (value'_measurable 0).comp
      (((SelectedPath.mark_adapted R hR PUnit.unit.{1} i).comp (hsingleton (i + 1))).mono
        ((generationFiltration (M := Step ℕ ℝ)).mono hin) le_rfl)
  intro A hA
  have hp : splitWaitingDisplacement R ⁻¹' A =
      ⋃ n : WithTop ℕ, splitWaitingDisplacement R ⁻¹' A ∩ {ω | σ ω = n} := by
    ext ω
    simp [and_comm]
  rw [hp]
  apply MeasurableSet.iUnion
  intro n
  cases n with
  | top =>
    have htop : MeasurableSet[hσ.measurableSpace] {ω | σ ω = ⊤} :=
      hσ.measurable (measurableSet_singleton _)
    have heq : splitWaitingDisplacement R ⁻¹' A ∩ {ω | σ ω = ⊤} =
        (fun _ : Mark ℕ (Step ℕ ℝ) => (0 : ℝ)) ⁻¹' A ∩ {ω | σ ω = ⊤} := by
      ext ω
      constructor <;> rintro ⟨hw, hn⟩ <;>
        exact ⟨by simpa [splitWaitingDisplacement, waitingSum, show
          selectedPopulationSplitCompletion R ω = ⊤ from hn] using hw, hn⟩
    rw [heq]
    exact (measurable_const hA).inter htop
  | coe n =>
    have heq : splitWaitingDisplacement R ⁻¹' A ∩ {ω | σ ω = (n : WithTop ℕ)} =
        waitingSum R (n - 1) ⁻¹' A ∩ {ω | σ ω = (n : WithTop ℕ)} := by
      ext ω
      change (splitWaitingDisplacement R ω ∈ A ∧ σ ω = (n : WithTop ℕ)) ↔
        (waitingSum R (n - 1) ω ∈ A ∧ σ ω = (n : WithTop ℕ))
      apply and_congr_left
      intro hn
      unfold splitWaitingDisplacement
      rw [show selectedPopulationSplitCompletion R ω = (n : WithTop ℕ) from hn]
      rfl
    change MeasurableSet[hσ.measurableSpace] (splitWaitingDisplacement R ⁻¹' A ∩ {ω | σ ω = (n : WithTop ℕ)})
    rw [heq]
    exact (hσ.measurableSet_inter_eq_iff _ n).2 ((hsum n hA).inter (hσ.measurableSet_eq n))

private lemma exponentialTerm_at_first_sampled_split
    (R : Step.FiniteSelection ℕ ℝ) (ω : RootIndexed.StepField PUnit.{1} ℕ ℝ)
    (n : ℕ) (hn : splitEvent R PUnit.unit.{1} n ω)
    (hbefore : ∀ i < n, ¬ splitEvent R PUnit.unit.{1} i ω)
    (lam : ℝ) :
    (∑' k, geometricFailureExponentialTerm (Coupling.step R PUnit.unit.{1})
      (splitBy R) (fun ξ => value' ξ 0) lam k ω) =
    ENNReal.ofReal (Real.exp (lam * waitingSum R n (ω PUnit.unit.{1}))) := by
  let f := fun k => geometricFailureExponentialTerm (Coupling.step R PUnit.unit.{1})
    (splitBy R) (fun ξ => value' ξ 0) lam k ω
  have hsplit : Coupling.step R PUnit.unit.{1} n ω ∈ splitBy R := hn
  have hfail (i : ℕ) (hi : i < n) : Coupling.step R PUnit.unit.{1} i ω ∉ splitBy R := hbefore i hi
  have hf (k : ℕ) (hk : k ≠ n) : f k = 0 := by
    unfold f geometricFailureExponentialTerm
    by_cases hkn : k < n
    · rw [Finset.prod_range_succ, ite_eq_right (Nat.lt_irrefl _)]
      rw [Set.indicator_of_notMem (hfail k hkn), mul_zero]
    · have hnk : n < k := by omega
      apply Finset.prod_eq_zero (Finset.mem_range.mpr (by omega) : n ∈ Finset.range (k + 1))
      rw [ite_eq_left hnk]
      have hnot : Coupling.step R PUnit.unit.{1} n ω ∉ (splitBy R)ᶜ := fun h => h hsplit
      rw [Set.indicator_of_notMem hnot, mul_zero]
  change (∑' k, f k) = _
  rw [tsum_eq_single n hf]
  unfold f geometricFailureExponentialTerm
  rw [Finset.prod_range_succ, ite_eq_right (Nat.lt_irrefl _), Set.indicator_of_mem hsplit, mul_one,
    waitingSum, Finset.mul_sum, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [ite_eq_left (Finset.mem_range.mp hi),
      Set.indicator_of_mem (show Coupling.step R PUnit.unit.{1} i ω ∈ (splitBy R)ᶜ from hfail i (Finset.mem_range.mp hi)), mul_one]
  · intro i _
    exact (Real.exp_pos _).le

lemma exists_splitWaitingDisplacement_exponentialMoment
    {ι X : Type*} [MeasurableSpace X]
    (L : StepLaw ι ℕ X) [IsProbabilityMeasure L.raw]
    (hexp : HasLeftmostPositiveExponentialMoment L)
    (R : Step.FiniteSelection ℕ ℝ) (hR : Measurable R.select)
    (hne : L.sortedPotentialImage {ξ | (R ξ).Nonempty} = 1)
    (hp : 0 < L.sortedPotentialImage (splitBy R)) :
    let μ := L.sortedPotentialImage
    ∃ lam > (0 : ℝ), let A := ∫⁻ x, ENNReal.ofReal (Real.exp (lam * value' x 0)) *
          (splitBy R)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ
      A < 1 ∧
        (∫⁻ ω, ENNReal.ofReal (Real.exp (lam * splitWaitingDisplacement R ω))
          ∂offspringFieldLaw μ) = μ (splitBy R) / (1 - A) ∧
          μ (splitBy R) / (1 - A) < ∞ := by
  intro μ
  let P := RootIndexed.stepFieldLaw (Root := PUnit.{1}) μ
  obtain ⟨lam, hlam, hA, htransform, hfin⟩ :=
    exists_firstSplit_failureDisplacement_exponentialMoment L hexp R hR hp PUnit.unit.{1}
  refine ⟨lam, hlam, hA, ?_, hfin⟩
  let eval : RootIndexed.StepField PUnit.{1} ℕ ℝ → Mark ℕ (Step ℕ ℝ) := fun ω => ω PUnit.unit.{1}
  have heval : Measurable eval := measurable_pi_apply _
  have hlaw : P.map eval = offspringFieldLaw μ := RootIndexed.stepFieldLaw_root_marginal μ _
  have hF := (splitWaitingDisplacement_measurable R hR).mono
    (selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace_le le_rfl
  have hw : Measurable (fun ω => ENNReal.ofReal (Real.exp (lam * splitWaitingDisplacement R ω))) :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul hF)).ennreal_ofReal
  rw [← hlaw, lintegral_map hw heval, ← htransform]
  apply lintegral_congr_ae
  have hsplit := selectedPopulationSplitCompletion_ae_finite_of_nonempty_and_split_pos μ R hR
    hne (splitBy_measurable R hR) hp
  have hfinite : ∀ᵐ ω ∂P, selectedPopulationSplitCompletion R (ω PUnit.unit.{1}) ≠ ⊤ :=
    ae_of_ae_map heval.aemeasurable (by rwa [hlaw])
  have hall : ∀ᵐ ω ∂P, ∀ u, (R (ω PUnit.unit.{1} u)).Nonempty := by
    apply ae_all_iff.2
    intro u
    have hm : Measurable (fun ξ => (R ξ).card) :=
      (measurable_of_countable fun s : Finset ℕ => s.card).comp hR
    have hs : MeasurableSet {ξ | (R ξ).Nonempty} := by
      have heq : {ξ | (R ξ).Nonempty} = (fun ξ => (R ξ).card) ⁻¹' Set.Ioi 0 := by
        ext ξ
        exact Finset.card_pos.symm
      rw [heq]
      exact hm measurableSet_Ioi
    have hmeas : Measurable (fun ω : RootIndexed.StepField PUnit.{1} ℕ ℝ => ω PUnit.unit.{1} u) :=
      (measurable_pi_apply u).comp heval
    apply (ae_mem_iff_measure_eq (hmeas hs).nullMeasurableSet).2
    rw [← Measure.map_apply hmeas hs, RootIndexed.stepFieldLaw_coordinate_marginal μ _ u, hne]
    exact measure_univ.symm
  filter_upwards [hfinite, hall] with ω hω hnonempty
  obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp hω
  cases j with
  | zero => exact (selectedPopulationSplitCompletion_ne_zero R _ hj.symm).elim
  | succ n =>
    have hn := selectedPopulationRawSplitTime_eq_of_completion_eq R _ n hj.symm
    obtain ⟨hs, hbefore⟩ := first_sampled_split_of_rawSplitTime_eq R PUnit.unit.{1} ω n hnonempty hn
    rw [exponentialTerm_at_first_sampled_split R ω n hs hbefore lam]
    change ENNReal.ofReal (Real.exp (lam * splitWaitingDisplacement R (ω PUnit.unit))) = _
    unfold splitWaitingDisplacement
    rw [hj.symm]
    change ENNReal.ofReal (Real.exp (lam * waitingSum R (n + 1 - 1) (ω PUnit.unit))) = _
    simp

private lemma potential_selectedPath_eq_waitingSum
    (R : Step.FiniteSelection ℕ ℝ) (ω : Mark ℕ (Step ℕ ℝ))
    (n : ℕ) (hne : ∀ u, (R (ω u)).Nonempty)
    (hfirst : ∀ u, firstSelectedSlot R (ω u) = 0)
    (hbefore : ∀ j < n, ¬ splitEvent R PUnit.unit.{1} j (singletonField ω)) :
    Spine.pathPotential realPotential ω
        (selectedPath R PUnit.unit.{1} n (singletonField ω)) = waitingSum R n ω := by
  induction n with
  | zero => simp [selectedPath, waitingSum]
  | succ n ih =>
    let p := selectedPath R PUnit.unit.{1} n (singletonField ω)
    have hnot := hbefore n (Nat.lt_succ_self n)
    change ¬ 2 ≤ (R (ω p)).card at hnot
    have hcard : (R (ω p)).card = 1 := by have := Finset.card_pos.mpr (hne p); omega
    have hslot : continuationSlot R (ω p) = 0 :=
      (continuationSlot_eq_first_of_singleton R _ hcard).trans (hfirst p)
    rw [show selectedPath R PUnit.unit.{1} (n + 1) (singletonField ω) =
        p ++ [0] from congrArg (fun i => p ++ [i]) hslot, Spine.pathPotential_append,
      Spine.pathPotential_singleton]
    have hp : Spine.pathPotential realPotential ω p = waitingSum R n ω :=
      ih (fun j hj => hbefore j (hj.trans (Nat.lt_succ_self n)))
    rw [hp, show waitingSum R (n + 1) ω = waitingSum R n ω + value' (ω p) 0 by
      unfold waitingSum
      rw [Finset.sum_range_succ]
      rfl]
    simp [subtreeStepField, Step.potentialValue', Step.potentialAt?, realPotential, value']


lemma splitWaitingDisplacement_eq_parentPosition
    (R : Step.FiniteSelection ℕ ℝ) (ω : Mark ℕ (Step ℕ ℝ))
    (hne : ∀ u, (R (ω u)).Nonempty)
    (hfirst : ∀ u, firstSelectedSlot R (ω u) = 0) :
    Spine.pathPotential realPotential ω (selectedPopulationFirstSplitRoots R ω 1).dropLast =
      splitWaitingDisplacement R ω := by
  cases hraw : selectedPopulationRawSplitTime R ω with
  | top =>
    simp [selectedPopulationFirstSplitRoots, hraw, splitWaitingDisplacement,
      selectedPopulationSplitCompletion_eq_raw_add_one, waitingSum]
  | coe n =>
    have hroot := (firstSplitRoots_eq_of_rawSplitTime_eq R PUnit.unit.{1}
      (singletonField ω) n hne hraw).2
    obtain ⟨_, hbefore⟩ := first_sampled_split_of_rawSplitTime_eq R PUnit.unit.{1}
      (singletonField ω) n hne hraw
    change selectedPopulationFirstSplitRoots R ω 1 =
      selectedPath R PUnit.unit.{1} n (singletonField ω) ++ [_] at hroot
    rw [hroot, List.dropLast_append_cons]
    simp only [List.dropLast_singleton, List.append_nil]
    rw [potential_selectedPath_eq_waitingSum R ω n hne hfirst hbefore]
    unfold splitWaitingDisplacement
    rw [selectedPopulationSplitCompletion_eq_raw_add_one, hraw]
    change waitingSum R n ω = waitingSum R (n + 1 - 1) ω
    simp

lemma splitChildPosition_le_splitWaitingDisplacement_add
    (R : Step.FiniteSelection ℕ ℝ) (ω : Mark ℕ (Step ℕ ℝ))
    (hne : ∀ u, (R (ω u)).Nonempty)
    (hfirst : ∀ u, firstSelectedSlot R (ω u) = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hcut : ∀ u, 2 ≤ (R (ω u)).card →
      value' (ω u) (firstSelectedSlot R (ω u)) ≤ M ∧
        value' (ω u) (secondSelectedSlot R (ω u)) ≤ M) (i : Fin 2) :
    Spine.pathPotential realPotential ω (selectedPopulationFirstSplitRoots R ω i) ≤
      splitWaitingDisplacement R ω + M := by
  have hparent := splitWaitingDisplacement_eq_parentPosition R ω hne hfirst
  cases hraw : selectedPopulationRawSplitTime R ω with
  | top =>
    rw [← hparent]
    simpa [selectedPopulationFirstSplitRoots, hraw] using hM
  | coe n =>
    let p := selectedPath R PUnit.unit.{1} n (singletonField ω)
    obtain ⟨hzero, hone⟩ :=
      firstSplitRoots_eq_of_rawSplitTime_eq R PUnit.unit.{1} (singletonField ω) n hne hraw
    have hroot₁ : selectedPopulationFirstSplitRoots R ω 1 =
        p ++ [secondSelectedSlot R (ω p)] := hone
    have hs : 2 ≤ (R (ω p)).card :=
      (first_sampled_split_of_rawSplitTime_eq R PUnit.unit.{1} (singletonField ω) n hne hraw).1
    have hchild (j : ℕ) (hj : value' (ω p) j ≤ M) :
        Spine.pathPotential realPotential ω (p ++ [j]) ≤ splitWaitingDisplacement R ω + M := by
      rw [hroot₁, List.dropLast_append_cons] at hparent
      simp only [List.dropLast_singleton, List.append_nil] at hparent
      rw [Spine.pathPotential_append, Spine.pathPotential_singleton, ← hparent]
      simpa [subtreeStepField, Step.potentialValue', Step.potentialAt?, realPotential, value'] using
        add_le_add_left hj (Spine.pathPotential realPotential ω p)
    have hroot₀ : selectedPopulationFirstSplitRoots R ω 0 =
        p ++ [firstSelectedSlot R (ω p)] := hzero
    fin_cases i
    · change Spine.pathPotential realPotential ω (selectedPopulationFirstSplitRoots R ω 0) ≤ _
      rw [hroot₀]
      exact hchild _ (hcut p hs).1
    · change Spine.pathPotential realPotential ω (selectedPopulationFirstSplitRoots R ω 1) ≤ _
      rw [hroot₁]
      exact hchild _ (hcut p hs).2

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas
