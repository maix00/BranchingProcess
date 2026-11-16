/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.Entrance
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.EntranceScales
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.TrialPosition
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Success
import Combinatorics.UlamHarris.Order

/-!
# Probability of a good entrance from one particle

## Internal proof declarations

* `exists_logarithmicEntrance_failure_le_polynomial`: for every $eta>0$,
  one can choose $alphain(0,1)$ and the growth and clock scales so that
  $T_N=o(log^3N)$, and
  $mathbb P(G_N^c)le N^{-b}$ eventually for some $b>0$. The good event
  $G_N$ is successful completion by $T_N$ with at least
  $lfloor N^alpha
floor$ actual particles below $etalog N$.

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
        (upper duration T : ℕ → ℕ),
      Tendsto (fun n => (T n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, T n ≤ H n) ∧
      ∃ b : ℝ, 0 < b ∧ ∀ᶠ n in atTop,
        let lower := ⌊(N n : ℝ) ^ α⌋₊
        let τ := Completion.time R growth hR hgrowth lower (upper n) (duration n) (0 : ℕ)
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
  obtain ⟨M, hρ, hsplit, hp₁, hsuccess⟩ :=
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
  let p₁ := 1 / (4 * normalizedSecondMomentConstant ρ
    (finiteSlotOffspringSecondMomentReal law - ρ ^ 2))
  let p₀ := (μ (splitBy R)).toReal
  have hM : (0 : ℝ) ≤ M := by positivity
  have hp₀ : 0 < p₀ := ENNReal.toReal_pos (ne_of_gt hsplit) (measure_ne_top _ _)
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
  let nClock := fun n => ⌈(4 * δ / p₀) * logN n⌉₊
  let duration := fun n => ⌈(α * logN n + Real.log 2) / Real.log ρ⌉₊
  let upper := fun n => 2 ^ duration n
  let T := fun n => nClock n + duration n
  obtain ⟨hscales, hT, hTH⟩ :=
    logarithmicEntrance_scales hρ hp₀ ha hδ hM hsmall hbudget hN ht hH
  let q := max (1 / 2) (1 - p₁)
  have hq : 0 < q := (show (0 : ℝ) < 1 / 2 by norm_num).trans_le (le_max_left _ _)
  have hq1 : q < 1 := max_lt (by norm_num) (by linarith)
  have hK : ∀ᶠ i in atTop, δ * logN i / 2 ≤ (K i : ℝ) ∧ (K i : ℝ) ≤ δ * logN i ∧
      (K i : ℝ) ≤ (nClock i : ℝ) * p₀ / 4 :=
    hscales.mono fun _ h => ⟨h.2.2.1, h.2.2.2.1, h.2.1⟩
  obtain ⟨b, hb, hprob⟩ :=
    eventually_geometric_and_exponential_entrance_bound hδ hq hq1 hB hvEq hlog K nClock hK
  have habsorb : ∀ᶠ i in atTop, 4 ≤ Real.exp (b / 2 * logN i) :=
    (Real.tendsto_exp_atTop.comp (hlog.const_mul_atTop (by positivity))).eventually_ge_atTop 4
  refine ⟨α, ha, ha1, R, growth, hR, hgrowth, upper, duration, T, hT, hTH,
    b / 2, by positivity, ?_⟩
  filter_upwards [hscales, hprob, habsorb, hN.eventually_ge_atTop 1] with i hs hp hab hN1
  dsimp only
  let lower := ⌊(N i : ℝ) ^ α⌋₊
  let G := growthTrialSuccess growth lower (upper i) (duration i)
  let x := v * (δ * logN i)
  let w := Real.exp (-b * logN i)
  have hbound : growth.IsBoundedBy 2 := by
    intro ξ
    apply (Finset.card_le_card ?_).trans (firstNBySlotOrder_isBoundedBy 2 ξ)
    intro j hj
    exact ((Step.FiniteSelection.mem_filter B₀ _ ξ j).mp hj).1
  have hcut : ∀ ξ j, j ∈ growth ξ → ξ.potentialValue' realPotential j ≤ M :=
    fun ξ j hj => ((Step.FiniteSelection.mem_filter B₀ _ ξ j).mp hj).2
  have hsuccessMeas : MeasurableSet {ω | G ω} :=
    (generationFiltration (M := Step ℕ ℝ)).le (duration i) _
      (growthTrialSuccess_measurable growth hgrowth lower (upper i) (duration i))
  have hsuccess' : p₁ ≤ (ν {ω | G ω}).toReal := hsuccess (N i) α lower hN1
      (Nat.floor_pos.mpr (Real.one_le_rpow (by exact_mod_cast hN1) ha.le))
      (Nat.floor_le_ceil _)
  have hfail : ν {ω | ¬ G ω} ≤ ENNReal.ofReal q := by
    change ν {ω | G ω}ᶜ ≤ ENNReal.ofReal q
    rw [measure_compl hsuccessMeas (measure_ne_top _ _), measure_univ]
    have hle : ν {ω | G ω} ≤ 1 := (measure_mono (Set.subset_univ _)).trans_eq measure_univ
    have hfinite : 1 - ν {ω | G ω} ≠ ∞ :=
      (tsub_le_self.trans_lt ENNReal.one_lt_top).ne
    rw [← ENNReal.ofReal_toReal hfinite, ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top,
      ENNReal.toReal_one]
    exact ENNReal.ofReal_le_ofReal ((sub_le_sub_left hsuccess' 1).trans (le_max_right _ _))
  have hpow : (ν {ω | ¬ G ω}) ^ K i ≤ ENNReal.ofReal w :=
    (pow_le_pow_left₀ zero_le hfail _).trans <| by
      rw [← ENNReal.ofReal_pow hq.le]
      exact ENNReal.ofReal_le_ofReal hp.2.1
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
      _ ≤ _ := ENNReal.ofReal_le_ofReal hp.2.2
  have hlarge : ν large ≤ ENNReal.ofReal w := by
    have ht := (hroot lower (upper i) (duration i) x (K i)).trans hsum
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _),
      ENNReal.toReal_ofReal (by positivity)] at hreal
    have hle := le_of_mul_le_mul_left hreal (Real.exp_pos _)
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν large)]
    exact ENNReal.ofReal_le_ofReal hle
  have hclock : ENNReal.ofReal (Real.exp (-((nClock i : ℝ) * p₀ / 4))) ≤ ENNReal.ofReal w :=
    ENNReal.ofReal_le_ofReal hp.1
  have hfinite := measure_badEntrance_le μ hnorm (N i) R growth hR hgrowth hRne hsplit
    lower (upper i) (duration i) (Nat.succ_le_of_lt (pow_pos (by decide) _))
    hbound hs.2.2.2.2.1 M hcut (0 : ℕ) (nClock i) (K i) hs.1 hs.2.1
    x (η * logN i) hs.2.2.2.2.2
  refine hfinite.trans ((add_le_add (add_le_add (add_le_add hclock hpow) hpow) hlarge).trans ?_)
  have heq : Real.exp (-b * logN i) * Real.exp (b / 2 * logN i) =
      Real.exp (-(b / 2) * logN i) := by rw [← Real.exp_add]; congr 1; ring
  have hlast : w + w + w + w ≤ Real.exp (-(b / 2) * logN i) := by
    calc
      _ = w * 4 := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hab (Real.exp_nonneg _)).trans_eq heq
  have hw : 0 ≤ w := Real.exp_nonneg _
  rw [← ENNReal.ofReal_add hw hw, ← ENNReal.ofReal_add (add_nonneg hw hw) hw,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg hw hw) hw) hw]
  exact ENNReal.ofReal_le_ofReal hlast

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas
