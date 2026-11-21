/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.FiniteSlot.Growth
import Probability.MeasureTheory.Moments.SecondMomentGrowth
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Normalized population of a supercritical binary selector

## Public declarations

* `finiteSlotPopulationSizeReal_div_mean_pow_tendsto_ae`: if the selected
  offspring count is bounded by two and its mean is $\rho>1$, then
  $Z_n/\rho^n\to W$ almost surely on the original offspring field, with
  $W$ measurable, integrable, and $\mathbb E[W]=1$.

* `exists_eventually_measure_growthTrialSuccess_ge`: if $d_n\to\infty$,
  $\rho x_n\le\rho^{d_n}$ eventually, and
  $K_n^{-1}\sum_{j=0}^{d_n}\rho^j\to0$, then the full trial with target
  $\lceil x_n\rceil$ and capacity $K_n$ has probability at least $p/2$
  eventually, where $p=P(W>1/\rho)>0$ is independent of the scales.

This gives the bounded-offspring case of the population limit used in Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026), Chapter 4, Theorem 1.1 for $a=0$.
For the bounded-offspring implication of the Kesten--Stigum theorem, see
Russell Lyons and Yuval Peres, *Probability on Trees and Networks*,
Section 12.2, Kesten--Stigum theorem (iii) implies (ii),
https://www.stat.berkeley.edu/~aldous/206-SNET/Papers/lyons_peres.pdf.
Here the normalized generation sizes form a martingale bounded in $L^2$.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.FiniteSlot

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)

set_option maxHeartbeats 800000 in
public theorem finiteSlotPopulationSizeReal_div_mean_pow_tendsto_ae
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcap : S.IsBoundedBy 2) :
    let ρ := finiteSlotOffspringMeanReal
      (Selection.Stepwise.binaryOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS)
    1 < ρ → ∃ W : Mark α (Step α X) → ℝ,
      Measurable W ∧ Integrable W (offspringFieldLaw μ) ∧
      (∫ ω, W ω ∂offspringFieldLaw μ) = 1 ∧
      ∀ᵐ ω ∂offspringFieldLaw μ,
        Tendsto (fun n => finiteSlotPopulationSizeReal S ω n / ρ ^ n) atTop (𝓝 (W ω)) := by
  classical
  intro ρ hρ
  let Ω := Mark α (Step α X)
  let P := offspringFieldLaw μ
  let ℱ : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace Ω) := generationFiltration
  let ν := Selection.Stepwise.binaryOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS
  let v := finiteSlotOffspringSecondMomentReal ν - ρ ^ 2
  let Z (n : ℕ) (ω : Ω) := finiteSlotPopulationSizeReal S ω n
  let Y (n : ℕ) (ω : Ω) := Z n ω / ρ ^ n
  have hρp : 0 < ρ := zero_lt_one.trans hρ
  have hv : 0 ≤ v := finiteSlotOffspringVarianceReal_nonneg ν
  have hz (n : ℕ) : Measurable[ℱ n] (Z n) :=
    (measurable_of_countable fun A : Finset (Fin n → Fin 2) => (A.card : ℝ)).comp
      (finiteSlotActiveLabels_measurable S hS hcap n)
  have hy (n : ℕ) : Measurable[ℱ n] (Y n) := (hz n).div_const _
  have hYM (n : ℕ) : Measurable (Y n) := (hy n).mono (ℱ.le n) le_rfl
  have hYI (n : ℕ) : Integrable (Y n) P :=
    (finiteSlotPopulationSizeReal_integrable μ S hS hcap n).div_const _
  have hm : Martingale Y ℱ P := by
    apply martingale_nat (fun n => (hy n).stronglyMeasurable) hYI
    intro n
    have hcond := finiteSlotActiveLabels_condExp_succ_card_filtration μ S hS hcap n
    have he : Y (n + 1) = (ρ ^ (n + 1))⁻¹ • Z (n + 1) := by
      funext ω
      simp [Y, div_eq_inv_mul]
    rw [he]
    symm
    refine (condExp_smul (μ := P) (ρ ^ (n + 1))⁻¹ (Z (n + 1)) (ℱ n)).trans ?_
    filter_upwards [hcond] with ω hw
    change (ρ ^ (n + 1))⁻¹ * (P[Z (n + 1) | ℱ n]) ω = Y n ω
    change (P[Z (n + 1) | ℱ n]) ω = Z n ω * ρ at hw
    rw [hw]
    dsimp [Y]
    rw [pow_succ]
    field_simp
  have hmean (n : ℕ) : (∫ ω, Y n ω ∂P) = 1 := by
    change (∫ ω, Z n ω / ρ ^ n ∂P) = 1
    rw [integral_div, finiteSlotPopulationSizeReal_integral_eq_pow μ S hS hcap n]
    exact div_self (pow_ne_zero _ hρp.ne')
  let B := normalizedSecondMomentConstant ρ v
  have hB : 0 ≤ B := by dsimp [B, normalizedSecondMomentConstant]; positivity
  have hsecond (n : ℕ) : (∫ ω, (Y n ω) ^ 2 ∂P) ≤ B := by
    let m₂ n := ∫ ω, (Z n ω) ^ 2 ∂P
    have hz0 (ω : Ω) : Z 0 ω = 1 := by
      change ((finiteSlotActiveLabels S ω 0).card : ℝ) = 1
      rw [finiteSlotActiveLabels_card_eq_population_card S ω hcap]
      simp [Selection.Stepwise.population_zero]
    have hb := normalizedSecondMoment_le_of_recursion ρ v hρ hv m₂ (by simp [m₂, hz0])
      (fun n => finiteSlotPopulationSizeReal_sq_integral_eq_recursion μ S hS hcap n) n
    change (∫ ω, (Z n ω / ρ ^ n) ^ 2 ∂P) ≤ B
    simp only [div_pow]
    rw [integral_div, ← pow_mul, mul_comm n 2]
    exact hb
  have hsqI (n : ℕ) : Integrable (fun ω => (Y n ω) ^ 2) P := by
    simpa only [Y, div_pow] using
      (finiteSlotPopulationSizeReal_sq_integrable μ S hS hcap n).div_const ((ρ ^ n) ^ 2)
  have hUI : UniformIntegrable Y 1 P := by
    apply uniformIntegrable_of le_rfl ENNReal.one_ne_top (fun n => (hYM n).aestronglyMeasurable)
    intro ε hε
    by_cases htop : ε = ∞
    · exact ⟨0, by simp [htop]⟩
    have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    let C : ℝ≥0 := ⟨(B + 1) / ε.toReal, by positivity⟩
    have hC : 0 < (C : ℝ) := div_pos (by linarith) hεr
    refine ⟨C, fun n => ?_⟩
    let A := {ω : Ω | C ≤ ‖Y n ω‖₊}
    have hA : MeasurableSet A := measurableSet_le measurable_const (hYM n).nnNorm
    have hnn (ω : Ω) : 0 ≤ Y n ω := div_nonneg (Nat.cast_nonneg _) (pow_nonneg hρp.le _)
    have hpoint (ω : Ω) : ‖A.indicator (Y n) ω‖ ≤ (Y n ω) ^ 2 / (C : ℝ) := by
      by_cases ha : ω ∈ A
      · have hh : (C : ℝ) ≤ ‖Y n ω‖ := ha
        rw [Real.norm_eq_abs, abs_of_nonneg (hnn ω)] at hh
        rw [Set.indicator_of_mem ha, Real.norm_eq_abs, abs_of_nonneg (hnn ω)]
        apply (le_div_iff₀ hC).mpr
        nlinarith [mul_le_mul_of_nonneg_right hh (hnn ω)]
      · rw [Set.indicator_of_notMem ha, norm_zero]
        positivity
    rw [eLpNorm_one_eq_lintegral_eNorm ((hYM n).indicator hA).aestronglyMeasurable]
    refine (lintegral_mono (g := fun ω => ENNReal.ofReal ((Y n ω) ^ 2 / (C : ℝ))) (fun ω => ?_)).trans ?_
    · simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hpoint ω)
    · rw [← ofReal_integral_eq_lintegral_ofReal ((hsqI n).div_const _)
          (.of_forall fun ω => div_nonneg (sq_nonneg _) hC.le),
        integral_div, ← ENNReal.ofReal_toReal htop]
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ hC).mpr
      have he : ε.toReal * (C : ℝ) = B + 1 := by
        change ε.toReal * ((B + 1) / ε.toReal) = B + 1
        field_simp
      linarith [hsecond n]
  let W := ℱ.limitProcess Y P
  have hW : Measurable W :=
    (Filtration.stronglyMeasurable_limitProcess (X := Y) (𝓕 := ℱ) (P := P)).measurable.mono
      (iSup_le fun n => ℱ.le n) le_rfl
  have hWI : Integrable W P :=
    memLp_one_iff_integrable.mp
      (Filtration.memLp_limitProcess_of_eLpNorm_bdd hUI.aestronglyMeasurable hUI.iSup_eLpNorm_lt)
  have hlim := hm.submartingale.tendsto_eLpNorm_one_limitProcess hUI
  have he : Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop (𝓝 (∫ ω, W ω ∂P)) :=
    tendsto_integral_of_L1' W (Eventually.of_forall hYI) hlim
  simp only [hmean] at he
  refine ⟨W, hW, hWI, (tendsto_nhds_unique tendsto_const_nhds he).symm, ?_⟩
  exact hm.submartingale.ae_tendsto_limitProcess_of_uniformIntegrable hUI

/-- The normalized limit yields the positive terminal probability used in
Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026), proof of Theorem 1.1 for $a=0$. -/
private lemma exists_eventually_measure_normalized_population_gt
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcap : S.IsBoundedBy 2) :
    let ρ := finiteSlotOffspringMeanReal
      (Selection.Stepwise.binaryOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS)
    1 < ρ → ∃ p : ℝ, 0 < p ∧ ∀ᶠ n in atTop,
      3 * p / 4 ≤ (offspringFieldLaw μ).real
        {ω | 1 / ρ < finiteSlotPopulationSizeReal S ω n / ρ ^ n} := by
  intro ρ hρ
  let P := offspringFieldLaw μ
  let Y (n : ℕ) (ω : Mark α (Step α X)) := finiteSlotPopulationSizeReal S ω n / ρ ^ n
  obtain ⟨W, _, hWI, hmean, hlim⟩ :=
    finiteSlotPopulationSizeReal_div_mean_pow_tendsto_ae μ S hS hcap hρ
  let A := {ω | 1 / ρ < W ω}
  have hA : P A ≠ 0 := by
    intro hzero
    have hb : ∀ᵐ ω ∂P, W ω ≤ 1 / ρ := by
      rw [ae_iff]
      simpa only [not_le] using hzero
    have hi := integral_mono_ae hWI (integrable_const (1 / ρ)) hb
    rw [hmean, integral_const, probReal_univ, one_smul] at hi
    exact (not_le_of_gt (one_div_lt_one_div_of_lt zero_lt_one hρ)) (by simpa using hi)
  have hp : 0 < P.real A := ENNReal.toReal_pos hA (measure_ne_top _ _)
  refine ⟨P.real A, hp, ?_⟩
  let B (k : ℕ) := {ω | ∀ n ≥ k, 1 / ρ < Y n ω}
  have hB : Monotone B := fun _ _ h _ hw n hn => hw n (h.trans hn)
  have hsub : A ≤ᵐ[P] ⋃ k, B k := by
    filter_upwards [hlim] with ω hw
    intro ha
    have hf : ∀ᶠ n in atTop, 1 / ρ < Y n ω :=
      hw.eventually (lt_mem_nhds ha)
    obtain ⟨k, hk⟩ := eventually_atTop.mp hf
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  have hmeasure : P.real A ≤ P.real (⋃ k, B k) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have hcont : Tendsto (fun k => P.real (B k)) atTop (𝓝 (P.real (⋃ k, B k))) :=
    (ENNReal.tendsto_toReal (measure_ne_top P _)).comp
      (tendsto_measure_iUnion_atTop hB)
  filter_upwards [hcont.eventually (lt_mem_nhds (show 3 * P.real A / 4 <
      P.real (⋃ k, B k) by linarith))] with n hn
  exact hn.le.trans (measureReal_mono fun ω hw => hw n le_rfl)


/-- Combine the normalized terminal population estimate with Markov's
inequality at each generation. The uniform constant comes from the
normalized limit and is independent of the time and capacity scales. -/
public theorem exists_eventually_measure_growthTrialSuccess_ge
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcap : S.IsBoundedBy 2) :
    let ρ := finiteSlotOffspringMeanReal
      (Selection.Stepwise.binaryOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS)
    1 < ρ → ∃ p : ℝ, 0 < p ∧ ∀ (duration capacity : ℕ → ℕ) (target : ℕ → ℝ),
      Tendsto duration atTop atTop →
      (∀ᶠ n in atTop, 0 < capacity n ∧ 0 < target n ∧ ρ * target n ≤ ρ ^ duration n) →
      Tendsto (fun n => (∑ j ∈ Finset.range (duration n + 1), ρ ^ j) / (capacity n : ℝ))
        atTop (𝓝 0) →
      ∀ᶠ n in atTop, p / 2 ≤ (offspringFieldLaw μ).real
        {ω | growthTrialSuccess S ⌈target n⌉₊ (capacity n) (duration n) ω} := by
  intro ρ hρ
  obtain ⟨p, hp, hterminal⟩ := exists_eventually_measure_normalized_population_gt μ S hS hcap hρ
  refine ⟨p, hp, ?_⟩
  intro duration capacity target hd hscale hbudget
  have hbudget' := hbudget.eventually (gt_mem_nhds (show 0 < p / 4 by positivity))
  filter_upwards [hd.eventually hterminal, hscale, hbudget'] with n hn hs hb
  obtain ⟨hN, htarget, hmean⟩ := hs
  let P := offspringFieldLaw μ
  let d := duration n
  let K := capacity n
  let q := ⌈target n⌉₊
  let terminal : Set (Mark α (Step α X)) :=
    {ω | 1 / ρ < finiteSlotPopulationSizeReal S ω d / ρ ^ d}
  let hit : Set (Mark α (Step α X)) :=
    {ω | ∃ j ≤ d, (K : ℝ) ≤ finiteSlotPopulationSizeReal S ω j}
  let success : Set (Mark α (Step α X)) := {ω | growthTrialSuccess S q K d ω}
  have hcard (ω : Mark α (Step α X)) (j : ℕ) :
      finiteSlotPopulationSizeReal S ω j = (Selection.Stepwise.population S j ω).card := by
    change ((finiteSlotActiveLabels S ω j).card : ℝ) = _
    exact_mod_cast finiteSlotActiveLabels_card_eq_population_card S ω hcap j
  have hsubset : terminal ⊆ success ∪ hit := by
    intro ω hω
    by_cases hh : ω ∈ hit
    · exact Or.inr hh
    · apply Or.inl
      have hρpos : 0 < ρ := zero_lt_one.trans hρ
      have hq : q ≤ (Selection.Stepwise.population S d ω).card := by
        have hZ := (lt_div_iff₀ (pow_pos hρpos d)).mp hω
        have hthreshold := (le_div_iff₀ hρpos).mpr (mul_comm ρ (target n) ▸ hmean)
        rw [one_div_mul_eq_div, hcard] at hZ
        exact Nat.ceil_le.mpr (hthreshold.trans hZ.le)
      have hbelow (j : ℕ) (hj : j ≤ d) : (Selection.Stepwise.population S j ω).card < K := by
        have hhj : ¬ (K : ℝ) ≤ finiteSlotPopulationSizeReal S ω j :=
          fun hj' => hh ⟨j, hj, hj'⟩
        rw [hcard] at hhj
        exact_mod_cast lt_of_not_ge hhj
      have hne := growthTrialSuccess_of_positive_terminal_population S hcap ω q d (2 ^ d)
        (Nat.ceil_pos.mpr htarget) le_rfl hq
      refine ⟨hq, (hbelow d le_rfl).le, fun j => ⟨(hne.2.2 j).1, ?_⟩⟩
      exact hbelow (j.val + 1) (by have := j.isLt; omega)
  have hhit : P.real hit ≤ (∑ j ∈ Finset.range (d + 1), ρ ^ j) / (K : ℝ) :=
    measure_finiteSlotPopulation_hits_capacity_le μ S hS hcap d (by exact_mod_cast hN)
  have htotal : P.real terminal ≤ P.real success + P.real hit :=
    (measureReal_mono hsubset).trans (measureReal_union_le _ _)
  change p / 2 ≤ P.real success
  change 3 * p / 4 ≤ P.real terminal at hn
  linarith


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.FiniteSlot
