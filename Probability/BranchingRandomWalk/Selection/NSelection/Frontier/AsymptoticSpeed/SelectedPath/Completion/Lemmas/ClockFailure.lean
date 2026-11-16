/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.Entrance
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.EntranceScales

/-!
# Probability of a late or unsuccessful entrance

## Internal proof declarations

* `eventually_measure_completionLate_or_trialFailure_le`: if the split
  count and clock scales satisfy the logarithmic entrance inequalities and
  each growth trial succeeds with probability at least $p_1>0$, then
  $P(\tau>n_N+d_N\text{ or the first }K_N\text{ trials fail})\le N^{-b}$
  eventually, for some $b>0$.

This is the exceptional-event probability in Wang Yiyang, *Asymptotic
Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Theorem 1.2.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas

open Combinatorics.Branching Combinatorics.UlamHarris
open Combinatorics.Branching.Step.FiniteSelection
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.BranchingRandomWalk.Coupling
open SelectedPath.GrowthTrial

lemma eventually_measure_completionLate_or_trialFailure_le
    {Root : Type} [MeasurableSpace Root] [MeasurableSingletonClass Root]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (hRne : μ {ξ | (R ξ).Nonempty} = 1) (hsplit : 0 < μ (splitBy R))
    (r : Root) {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (K clock duration lower upper : ℕ → ℕ) {δ p₁ : ℝ} (hδ : 0 < δ) (hp₁ : 0 < p₁)
    (hclock : ∀ᶠ i in atTop, 0 < clock i)
    (hK : ∀ᶠ i in atTop,
      δ * Real.log (N i : ℝ) / 2 ≤ (K i : ℝ) ∧
      (K i : ℝ) ≤ δ * Real.log (N i : ℝ) ∧
      (K i : ℝ) ≤ (clock i : ℝ) * (μ (splitBy R)).toReal / 4)
    (hsuccess : ∀ᶠ i in atTop,
      p₁ ≤ (offspringFieldLaw μ).real
        {ω | growthTrialSuccess growth (lower i) (upper i) (duration i) ω}) :
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ i in atTop,
      let τ := Completion.time R growth hR hgrowth (lower i) (upper i) (duration i) r
      let T := clock i + duration i
      let late := {field | (T : WithTop ℕ) < τ field}
      let failed := (fun field => RootIndexed.StepField.left field r) ⁻¹'
        recursiveFailure R growth (duration i) (lower i) (upper i) (K i)
      P (late ∪ failed) ≤ ENNReal.ofReal (Real.exp (-b * Real.log (N i : ℝ))) := by
  intro P
  let L := fun i => Real.log (N i : ℝ)
  let ν := offspringFieldLaw μ
  have hL : Tendsto L atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  let q := max (1 / 2) (1 - p₁)
  have hq : 0 < q := (show (0 : ℝ) < 1 / 2 by norm_num).trans_le (le_max_left _ _)
  have hq1 : q < 1 := max_lt (by norm_num) (by linarith)
  obtain ⟨b, hb, hscale⟩ :=
    eventually_geometric_and_exponential_entrance_bound hδ hq hq1 (le_refl (1 : ℝ))
      (by simp : (1 : ℝ) * 1 = Real.log 1 + 1) hL K clock hK
  have habsorb : ∀ᶠ i in atTop, 3 ≤ Real.exp (b / 2 * L i) :=
    (Real.tendsto_exp_atTop.comp (hL.const_mul_atTop (by positivity))).eventually_ge_atTop 3
  refine ⟨b / 2, by positivity, ?_⟩
  filter_upwards [hclock, hK, hsuccess, hscale, habsorb] with i hc hk hs hscale hab
  dsimp only
  let G := growthTrialSuccess growth (lower i) (upper i) (duration i)
  let w := Real.exp (-b * L i)
  have hG : MeasurableSet {ω | G ω} :=
    (generationFiltration (M := Step ℕ ℝ)).le (duration i) _
      (growthTrialSuccess_measurable growth hgrowth (lower i) (upper i) (duration i))
  have hqbound : ν {ω | ¬ G ω} ≤ ENNReal.ofReal q := by
    change ν {ω | G ω}ᶜ ≤ ENNReal.ofReal q
    rw [prob_compl_eq_one_sub hG]
    have hle : ν {ω | G ω} ≤ 1 := (measure_mono (Set.subset_univ _)).trans_eq measure_univ
    have hfinite : 1 - ν {ω | G ω} ≠ ∞ := (tsub_le_self.trans_lt ENNReal.one_lt_top).ne
    rw [← ENNReal.ofReal_toReal hfinite, ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top,
      ENNReal.toReal_one]
    exact ENNReal.ofReal_le_ofReal ((sub_le_sub_left hs 1).trans (le_max_right _ _))
  have hpow : (ν {ω | ¬ G ω}) ^ K i ≤ ENNReal.ofReal w :=
    (pow_le_pow_left₀ zero_le hqbound _).trans <| by
      rw [← ENNReal.ofReal_pow hq.le]
      exact ENNReal.ofReal_le_ofReal hscale.2.1
  obtain ⟨hlate, hfailed⟩ := measure_completionLate_and_trialFailure_le
    μ R growth hR hgrowth hRne hsplit (lower i) (upper i) (duration i) r
    (clock i) (K i) hc hk.2.2
  refine (measure_union_le _ _).trans (add_le_add hlate hfailed |>.trans ?_)
  refine (add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hscale.1) hpow) hpow).trans ?_
  have hm : 3 * w ≤ Real.exp (-(b / 2) * L i) := by
    calc
      _ ≤ Real.exp (b / 2 * L i) * w := mul_le_mul_of_nonneg_right hab (by positivity)
      _ = _ := by rw [show w = Real.exp (-b * L i) from rfl, ← Real.exp_add]; congr 1; ring
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ w) (by positivity : 0 ≤ w),
    ← ENNReal.ofReal_add (by positivity) (by positivity : 0 ≤ w)]
  apply ENNReal.ofReal_le_ofReal
  change w + w + w ≤ Real.exp (-(b / 2) * L i)
  linarith only [hm]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas
