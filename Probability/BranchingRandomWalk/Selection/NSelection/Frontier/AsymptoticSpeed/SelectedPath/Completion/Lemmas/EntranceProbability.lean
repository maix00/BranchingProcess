/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.Entrance
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.ClockFailure
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.WaitingTime
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.EntranceScales
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.TrialPosition
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Success
import Combinatorics.UlamHarris.Order

/-!
# Probability of a good entrance from one particle

## Internal proof declarations

* `exists_logarithmicEntrance_failure_le_polynomial`: for $\eta>0$ one
  can choose $\alpha\in(0,1)$ and $\gamma>0$ with $T_N=\lfloor\gamma\log N\rfloor=o(\log^3N)$ and
  $P(G_N^c)\le N^{-b}$ eventually for some $b>0$. On $G_N$ the first trial
  reaching $\lceil N^\alpha\rceil$ completes by $T_N$ and at least
  $\lfloor N^\alpha\rfloor$ actual particles lie below $\eta\log N$.

This is the entrance estimate in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 4, Theorem 1.1 for $a=0$.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas

open Combinatorics.Branching Combinatorics.UlamHarris
open Combinatorics.Branching.Step.FiniteSelection
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Selection.Stepwise.SplitTime
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)
open SelectedPath.GrowthTrial
open SelectedPath.GrowthTrial.FiniteSlot

noncomputable local instance natAddressOrder : LinearOrder (RootIndexed.TreeNode ℕ ℕ) :=
  RootIndexed.addressLinearOrder ℕ ℕ

noncomputable local instance (priority := high) natAddressDecidableEq : DecidableEq (RootIndexed.TreeNode ℕ ℕ) :=
  natAddressOrder.toDecidableEq

lemma exists_logarithmicEntrance_failure_le_polynomial
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hsuper : BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, inferInstance⟩ : BranchingProcess.OffspringConfigurationLaw ℕ ℝ))
    (hne : L.raw nonemptySupport = 1)
    (hexp : HasLeftmostPositiveExponentialMoment L)
    (hnorm : HasBoundaryNormalization realPotential L.sortedPotentialImage)
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop) {t : ℝ} (ht : 0 < t)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    {η : ℝ} (hη : 0 < η) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ ⊕ ℕ) L.sortedPotentialImage
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      ∃ (R growth : Step.FiniteSelection ℕ ℝ)
        (hR : Measurable R.select) (hgrowth : Measurable growth.select)
        (upper duration : ℕ → ℕ) (γ : ℝ), 0 < γ ∧
      let T := fun n => ⌊γ * Real.log (N n : ℝ)⌋₊
      Tendsto (fun n => (T n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, T n ≤ H n) ∧
      ∃ b : ℝ, 0 < b ∧ ∀ᶠ n in atTop,
        let lower := ⌊(N n : ℝ) ^ α⌋₊
        let τ := Completion.time R growth hR hgrowth ⌈(N n : ℝ) ^ α⌉₊ (upper n) (duration n) (0 : ℕ)
        let trials := SelectedPath.Population.leftBRWFamily_finiteSlices R growth
          hR hgrowth (upper n) (duration n) (0 : ℕ)
        let stage := RootIndexed.restartedRealPositionNSelectedBRWField (N n) {0}
          (fun _ => 0) id trials.toFinset
        let Pop := RootIndexed.restartedRealPositionNSelectedBRWPopulation (N n) {0}
          (fun _ => 0) id trials.toFinset
        P {field | ¬ ∃ i ≤ T n, (∃ e : Fin lower ↪ RootIndexed.TreeNode ℕ ℕ,
          ∀ j, e j ∈ Pop i field ∧
            RootIndexed.position (fun _ => 0) id (stage i field) (e j).1 (e j).2 ≤
              η * Real.log (N n : ℝ)) ∧ τ field = i} ≤
          ENNReal.ofReal (Real.exp (-b * Real.log (N n : ℝ))) := by
  intro P
  let μ := L.sortedPotentialImage
  let ν := offspringFieldLaw μ
  let logN := fun n => Real.log (N n : ℝ)
  have hlog : Tendsto logN atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  obtain ⟨M, hρ, hsplit, p₁, hp₁, hsuccess⟩ :=
    exists_success_probability_lower_bound L hne hsuper
  let B₀ := firstNBySlotOrder (α := ℕ) (X := ℝ) 2
  let R := firstOrBelowPotential B₀ realPotential (M : ℝ)
  let growth := B₀.belowPotential realPotential (M : ℝ)
  have hB₀ : Measurable B₀.select := firstTwoBySlotOrder_measurable
  have hR : Measurable R.select := firstOrBelowPotential_measurable B₀ hB₀ realPotential M
  have hgrowth : Measurable growth.select := B₀.belowPotential_measurable hB₀ realPotential M
  let law := Selection.Stepwise.binaryOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _)
    growth hgrowth
  let ρ := finiteSlotOffspringMeanReal law
  have hM : (0 : ℝ) ≤ M := by positivity
  obtain ⟨lam, hlam, hRne, _, hmfinite, hroot⟩ :=
    exists_firstSuccessfulTrial_position_upperTail L hexp hne growth hgrowth M hM hsplit
  let A := ∫⁻ ξ, ENNReal.ofReal (Real.exp (lam * value' ξ 0)) *
    (splitBy R)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ξ ∂μ
  let m := μ (splitBy R) / (1 - A)
  let B := max 1 m.toReal
  let v := (Real.log B + 1) / lam
  have hB : 1 ≤ B := le_max_left _ _
  have hmB : m ≤ ENNReal.ofReal B := (ENNReal.ofReal_toReal hmfinite.ne).ge.trans <|
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hvEq : lam * v = Real.log B + 1 := by dsimp [v]; field_simp
  have hv : 0 < v := div_pos (by linarith [Real.log_nonneg hB]) hlam
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let α := min (1 / 2) (min (Real.log ρ / (4 * Real.log 2))
    (η * Real.log ρ / (4 * ((M : ℝ) + 1))))
  let δ := η / (4 * (v + (M : ℝ) + 1))
  have ha : 0 < α := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have ha1 : α < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : α / Real.log ρ < 1 / (2 * Real.log 2) := by
    have hle : α ≤ Real.log ρ / (4 * Real.log 2) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hle' := (le_div_iff₀ (by positivity : 0 < 4 * Real.log 2)).mp hle
    apply (div_lt_iff₀ hlogρ).mpr
    rw [mul_comm (1 / (2 * Real.log 2)) (Real.log ρ), ← mul_div_assoc, mul_one]
    apply (lt_div_iff₀ (by positivity : 0 < 2 * Real.log 2)).mpr
    nlinarith
  have hbudget : (v + (M : ℝ)) * δ + (M : ℝ) * (α / Real.log ρ) < η := by
    have hle : α ≤ η * Real.log ρ / (4 * ((M : ℝ) + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hd := (le_div_iff₀ (by positivity : 0 < 4 * ((M : ℝ) + 1))).mp hle
    have h₁ : (M : ℝ) * (α / Real.log ρ) ≤ η / 4 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hlogρ).mpr
      nlinarith
    have h₂ : (v + (M : ℝ)) * δ ≤ η / 4 := by
      have hh : δ * (4 * (v + (M : ℝ) + 1)) = η := by
        dsimp [δ]; field_simp
      nlinarith
    linarith
  let K := fun n => ⌊δ * logN n⌋₊
  let duration := fun n => ⌊α * logN n / Real.log ρ⌋₊ + 2
  let upper := fun n => 2 ^ duration n
  let A₀ := α / Real.log ρ
  let lower i := ⌈(N i : ℝ) ^ α⌉₊
  obtain ⟨θ, hθ, hratio⟩ := exists_splitWaitingTime_expParameter μ R hsplit
  let moment := (μ (splitBy R) /
    (1 - ENNReal.ofReal (Real.exp θ) * (1 - μ (splitBy R)))).toReal
  let γ := δ + A₀ + δ / θ * Real.log moment + 1
  have hγ : δ + A₀ + δ / θ * Real.log moment < γ := lt_add_of_pos_right _ one_pos
  have hmoment : 1 ≤ moment :=
    one_le_splitWaitingTime_expMoment μ R hR hRne hsplit hθ.le hratio
  have hγpos : 0 < γ := by
    dsimp [γ, A₀]
    have hlog := Real.log_nonneg hmoment
    positivity
  let T := fun n => ⌊γ * logN n⌋₊
  have hd (i : ℕ) : (duration i : ℝ) ≤ A₀ * logN i + 2 := by
    rw [show A₀ * logN i = α * Real.log (N i : ℝ) / Real.log ρ by dsimp [A₀, logN]; ring]
    exact trialDuration_le hρ ha.le (N i)
  have hscales :=
    logarithmicEntrance_scales hρ ha hδ hM hsmall hbudget hN
      duration (fun i => trialDuration_le hρ ha.le (N i))
  obtain ⟨hT, hTH⟩ := logarithmicEntrance_deadline hγpos hN ht hH
  have hrootBound := eventually_exponential_trialRoot_bound hδ hB hvEq hlog K
    (hscales.mono fun _ h => h.2.1)
  have hcapacity : growth.IsBoundedBy 2 := by
    intro ξ
    exact (Finset.card_le_card (fun i hi =>
      ((Step.FiniteSelection.mem_filter B₀ _ ξ i).mp hi).1)).trans
      (firstNBySlotOrder_isBoundedBy 2 ξ)
  obtain ⟨hdTop, hMarkov⟩ := trialDuration_markov_scales hρ ha ha1 hN
  have hscaleSuccess : ∀ᶠ i in atTop, 0 < N i ∧ 0 < (N i : ℝ) ^ α ∧
      ρ * (N i : ℝ) ^ α ≤ ρ ^ duration i := by
    filter_upwards [hN.eventually_ge_atTop 1] with i hi
    have hNi : 0 < N i := Nat.zero_lt_of_lt hi
    exact ⟨hNi, Real.rpow_pos_of_pos (by exact_mod_cast hNi) α,
      rpow_mul_mean_le_pow_trialDuration hρ (N i) α hi⟩
  have htrialSuccess : ∀ᶠ i in atTop, p₁ ≤ (ν).real
      {ω | growthTrialSuccess growth (lower i) (upper i) (duration i) ω} := by
    filter_upwards [hsuccess duration N (fun i => (N i : ℝ) ^ α) hdTop hscaleSuccess hMarkov,
      hscaleSuccess, hscales] with i hs hscale hbudget
    have hupper : 2 ^ duration i ≤ N i := by
      have hh := hbudget.2.2.1
      nlinarith
    rw [show upper i = 2 ^ duration i by rfl,
      growthTrialSuccess_eq_of_binary_horizon_le growth hcapacity (lower i) (duration i) (N i)
        (Nat.ceil_pos.mpr hscale.2.1) hupper]
    exact hs
  obtain ⟨bClock, hbClock, hclock⟩ := eventually_measure_completionLate_or_trialFailure_le
    μ R growth hR hgrowth hRne hsplit 0 hN K duration lower upper hδ hp₁ hθ
    (hscales.mono fun _ h => ⟨h.1, h.2.1⟩) hd hratio hγ htrialSuccess
  let b := min bClock (δ / 2)
  have hb : 0 < b := lt_min hbClock (by positivity)
  have habsorb : ∀ᶠ i in atTop, 2 ≤ Real.exp (b / 2 * logN i) :=
    (Real.tendsto_exp_atTop.comp (hlog.const_mul_atTop (by positivity))).eventually_ge_atTop 2
  refine ⟨α, ha, ha1, R, growth, hR, hgrowth, upper, duration, γ, hγpos,
    hT, hTH, b / 2, by positivity, ?_⟩
  filter_upwards [hscales, hrootBound, hclock, habsorb, hlog.eventually_ge_atTop 0]
    with i hs hp hci hab hlogi
  dsimp only
  let target := lower i
  let G := growthTrialSuccess growth target (upper i) (duration i)
  let x := v * (δ * logN i)
  let w := Real.exp (-b * logN i)
  have hbound : growth.IsBoundedBy 2 := by
    intro ξ
    apply (Finset.card_le_card ?_).trans (firstNBySlotOrder_isBoundedBy 2 ξ)
    intro j hj
    exact ((Step.FiniteSelection.mem_filter B₀ _ ξ j).mp hj).1
  have hcut : ∀ ξ j, j ∈ growth ξ → ξ.potentialValue' realPotential j ≤ M :=
    fun ξ j hj => ((Step.FiniteSelection.mem_filter B₀ _ ξ j).mp hj).2
  have hexpRoot : Real.exp (-(δ / 2) * logN i) ≤ w := by
    apply Real.exp_le_exp.mpr
    linarith [mul_le_mul_of_nonneg_right (min_le_right bClock (δ / 2)) hlogi]
  have hexpClock : Real.exp (-bClock * logN i) ≤ w := by
    apply Real.exp_le_exp.mpr
    linarith [mul_le_mul_of_nonneg_right (min_le_left bClock (δ / 2)) hlogi]
  let large := {ω | ∃ k < K i, (splitCycle R (splitWaitingDisplacement R) G k ω).2 ∧
    (∀ j < k, ¬ (splitCycle R (splitWaitingDisplacement R) G j ω).2) ∧
    (x + ((K i - 1 : ℕ) : ℝ) * M ≤ Spine.pathPotential realPotential ω (trialSplitParent R k ω) ∨
     x + (K i : ℝ) * M ≤ Spine.pathPotential realPotential ω (trialGrowthRoot R k ω))}
  have hsum : (∑ k ∈ Finset.range (K i), m ^ (k + 1)) ≤
      ENNReal.ofReal (Real.exp (lam * x) * w) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (K i), (ENNReal.ofReal B) ^ (k + 1) :=
        Finset.sum_le_sum fun _ _ => pow_le_pow_left₀ zero_le hmB _
      _ = ENNReal.ofReal (∑ k ∈ Finset.range (K i), B ^ (k + 1)) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => pow_nonneg (by linarith) _)]
        exact Finset.sum_congr rfl fun k _ => (ENNReal.ofReal_pow (by linarith) _).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal <|
      hp.trans (mul_le_mul_of_nonneg_left hexpRoot (Real.exp_nonneg _))
  have hlarge : ν large ≤ ENNReal.ofReal w := by
    have ht := (hroot target (upper i) (duration i) x (K i)).trans hsum
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _),
      ENNReal.toReal_ofReal (by positivity)] at hreal
    have hle := le_of_mul_le_mul_left hreal (Real.exp_pos _)
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν large)]
    exact ENNReal.ofReal_le_ofReal hle
  have hfinite := measure_badEntrance_le μ hnorm (N i) R growth hR hgrowth hRne
    target (upper i) (duration i) (Nat.succ_le_of_lt (pow_pos (by decide) _))
    hbound hs.2.2.1 M hcut (0 : ℕ) (T i) (K i)
    x (η * logN i) hs.2.2.2
  have hci' := hci.trans (ENNReal.ofReal_le_ofReal hexpClock)
  refine (measure_mono (fun {_field} hbad => ?_)).trans
    (hfinite.trans ((add_le_add hci' hlarge).trans ?_))
  · intro hgood
    obtain ⟨j, hj, ⟨e, he⟩, hτ⟩ := hgood
    exact hbad ⟨j, hj, ⟨(Fin.castLEEmb (Nat.floor_le_ceil ((N i : ℝ) ^ α))).trans e,
      fun k => he (Fin.castLEEmb (Nat.floor_le_ceil ((N i : ℝ) ^ α)) k)⟩, hτ⟩
  · have heq : Real.exp (-b * logN i) * Real.exp (b / 2 * logN i) =
        Real.exp (-(b / 2) * logN i) := by rw [← Real.exp_add]; congr 1; ring
    have hlast : w + w ≤ Real.exp (-(b / 2) * logN i) := by
      calc
        _ = w * 2 := by ring
        _ ≤ _ := (mul_le_mul_of_nonneg_left hab (Real.exp_nonneg _)).trans_eq heq
    have hw : 0 ≤ w := Real.exp_nonneg _
    rw [← ENNReal.ofReal_add hw hw]
    exact ENNReal.ofReal_le_ofReal hlast

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas
