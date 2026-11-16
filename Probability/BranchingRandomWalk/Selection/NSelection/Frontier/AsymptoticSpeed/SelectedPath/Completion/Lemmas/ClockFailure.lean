/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.Entrance
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.EntranceScales
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Success

/-!
# Probability of a late or unsuccessful entrance

## Internal proof declarations

* `eventually_measure_completionLate_or_trialFailure_le`: if the split
  count and clock scales satisfy the logarithmic entrance inequalities and
  each growth trial succeeds with probability at least $p_1>0$, then
  $P(\{\tau\le n_N+d_N,\ \kappa\le K_N\}^{c})\le N^{-b}$
  eventually, for some $b>0$.
* `exists_logarithmicTrialClock_failure_le_polynomial`: with the binary cutoff
  rule and $d_N=\lceil(\alpha\log N+\log 2)/\log\rho\rceil$, a fixed
  positive success bound holds at target $\lceil N^\alpha\rceil$. On the
  original candidate tree the good-event complement is $O(N^{-b})$ for
  $T_N=n_N+d_N$ and $K_N=\lfloor\delta\log N\rfloor$.

This is the exceptional-event probability in Wang Yiyang, *Asymptotic
Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Theorem 1.2.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas

open Combinatorics.Branching Combinatorics.UlamHarris
open Combinatorics.Branching.Step.FiniteSelection
open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate)
open ProbabilityTheory.BranchingRandomWalk.Coupling
open SelectedPath.GrowthTrial SelectedPath.GrowthTrial.FiniteSlot
open ProbabilityTheory.BranchingRandomWalk.Step.Selection
open ProbabilityTheory.BranchingRandomWalk.Selection.Stepwise.SplitTime
open ProbabilityTheory.BranchingProcess.GaltonWatson

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
      let E := {field | splitCount R r ((τ field).untopD 0 - (duration i + 1))
        (RootIndexed.StepField.left field) < K i} ∩ {field | τ field ≤ (T : WithTop ℕ)}
      P Eᶜ ≤ ENNReal.ofReal (Real.exp (-b * Real.log (N i : ℝ))) := by
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
  let τ := Completion.time R growth hR hgrowth (lower i) (upper i) (duration i) r
  let T := clock i + duration i
  let left : RootIndexed.StepField (Root ⊕ Root) ℕ ℝ → RootIndexed.StepField Root ℕ ℝ :=
    RootIndexed.StepField.left
  let f := fun field => left field r
  let late := {field | (T : WithTop ℕ) < τ field}
  let failed := f ⁻¹' recursiveFailure R growth (duration i) (lower i) (upper i) (K i)
  have hleft : Measurable left := measurable_pi_iff.mpr fun i => measurable_pi_apply (Sum.inl i)
  have hleftlaw : P.map left = RootIndexed.stepFieldLaw (Root := Root) μ :=
    RootIndexed.stepFieldLaw_reindex μ Sum.inl Sum.inl_injective
  have hf : Measurable f := (measurable_pi_apply r).comp hleft
  have hflaw : P.map f = ν := by
    change P.map ((fun ω : RootIndexed.StepField Root ℕ ℝ => ω r) ∘ left) = ν
    rw [← Measure.map_map (measurable_pi_apply r) hleft, hleftlaw,
      RootIndexed.stepFieldLaw_root_marginal μ r]
  have hRmeas : MeasurableSet {ξ | (R ξ).Nonempty} := by
    rw [show {ξ | (R ξ).Nonempty} = (fun ξ => (R ξ).card) ⁻¹' Set.Ioi 0 by
      ext ξ
      exact Finset.card_pos.symm]
    exact ((measurable_of_countable fun s : Finset ℕ => s.card).comp hR) measurableSet_Ioi
  have hall : ∀ᵐ field ∂P, ∀ u, (R (f field u)).Nonempty := by
    apply ae_all_iff.2
    intro u
    have heval := (measurable_pi_apply u).comp hf
    have hlaw : P.map (fun field => f field u) = μ := by
      change P.map ((fun ω : Mark ℕ (Step ℕ ℝ) => ω u) ∘ f) = μ
      rw [← Measure.map_map (measurable_pi_apply u) hf, hflaw, offspringFieldLaw_coordinate μ u]
    apply (ae_mem_iff_measure_eq (heval hRmeas).nullMeasurableSet).2
    change P ((fun field => f field u) ⁻¹' {ξ | (R ξ).Nonempty}) = P Set.univ
    rw [← Measure.map_apply (show Measurable (fun field => f field u) from heval) hRmeas,
      hlaw, hRne, measure_univ]
  have hsub : ({field | splitCount R r ((τ field).untopD 0 - (duration i + 1))
      (RootIndexed.StepField.left field) < K i} ∩ {field | τ field ≤ (T : WithTop ℕ)})ᶜ
      ≤ᵐ[P] late ∪ failed := by
    filter_upwards [hall] with field hmarks hbad
    by_cases htime : τ field ≤ (T : WithTop ℕ)
    · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
        (ne_top_of_le_ne_top WithTop.coe_ne_top htime)
      let marks := left field
      have hτn : firstSuccessfulCompletion R growth hR (lower i) (upper i)
          (duration i) r marks = (n : WithTop ℕ) := hn.symm
      let declarations : ℕ → Set (RootIndexed.StepField Root ℕ ℝ) := fun s =>
        {ω | ∃ j, ((j + 1 + duration i : ℕ) : WithTop ℕ) = s ∧
          ω ∈ successEvent R growth hR (lower i) (upper i) (duration i) r j}
      have hfirst : firstDeclaredSuccess declarations marks = (n : WithTop ℕ) := hτn
      obtain ⟨j, hj, _⟩ := ((firstDeclaredSuccess_eq_iff declarations marks n).mp hfirst).1
      have hnj : j + 1 + duration i = n := WithTop.coe_injective hj
      have hcount : K i ≤ splitCount R r j marks := by
        apply Nat.le_of_not_gt
        intro hlt
        apply hbad
        have hindex : (τ field).untopD 0 - (duration i + 1) = j := by
          rw [← hn]
          simp only [WithTop.untopD_coe]
          omega
        exact ⟨by simpa only [Set.mem_ofPred_eq, hindex] using hlt, htime⟩
      refine Or.inr (mem_recursiveFailure_of_no_success R growth hR (lower i) (upper i)
        (duration i) (K i) r marks hmarks j hcount ?_)
      intro k hk hs'
      have hearly := (firstDeclaredSuccess_le_iff declarations marks (k + 1 + duration i)).2
        ⟨k + 1 + duration i, le_rfl, k, rfl, hs'⟩
      rw [hfirst] at hearly
      have hle : n ≤ k + 1 + duration i := WithTop.coe_le_coe.mp hearly
      omega
    · exact Or.inl (lt_of_not_ge htime)
  refine (measure_mono_ae hsub).trans ?_
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

/-- The success and clock estimates for the original pre-sampled growth
trial, with the integer target corresponding to population at least
$N^\alpha$. The exponent may be chosen arbitrarily small. -/
lemma exists_logarithmicTrialClock_failure_le_polynomial
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hne : L.raw nonemptySupport = 1)
    (hsuper : BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, inferInstance⟩ : BranchingProcess.OffspringConfigurationLaw ℕ ℝ))
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε)
    (hH : Tendsto (fun i => (H i : ℝ) / Real.log (N i : ℝ) ^ 3) atTop (𝓝 t)) :
    let μ := L.sortedPotentialImage
    let P := RootIndexed.stepFieldLaw (Root := ℕ ⊕ ℕ) μ
    ∃ (M : ℕ) (α ρ p₁ : ℝ), 0 < α ∧ α < 1 ∧ α < ε ∧ 1 < ρ ∧ 0 < p₁ ∧
      let B := Step.FiniteSelection.firstNBySlotOrder (α := ℕ) (X := ℝ) 2
      let R := firstOrBelowPotential B realPotential (M : ℝ)
      let growth := B.belowPotential realPotential (M : ℝ)
      let hR := firstOrBelowPotential_measurable B firstTwoBySlotOrder_measurable realPotential M
      let hgrowth := B.belowPotential_measurable firstTwoBySlotOrder_measurable realPotential M
      let p₀ := (μ (splitBy R)).toReal
      let d i := ⌈(α * Real.log (N i : ℝ) + Real.log 2) / Real.log ρ⌉₊
      let lower i := ⌈(N i : ℝ) ^ α⌉₊
      let upper i := 2 ^ d i
      let τ i := Completion.time R growth hR hgrowth (lower i) (upper i) (d i) (0 : ℕ)
      (∀ᶠ i in atTop, p₁ ≤ (offspringFieldLaw μ).real
        {ω | growthTrialSuccess growth (lower i) (upper i) (d i) ω}) ∧
      ∀ δ : ℝ, 0 < δ →
        let K i := ⌊δ * Real.log (N i : ℝ)⌋₊
        let T i := ⌈(4 * δ / p₀) * Real.log (N i : ℝ)⌉₊ + d i
        let E i := {field | splitCount R 0 ((τ i field).untopD 0 - (d i + 1))
          (RootIndexed.StepField.left field) < K i} ∩ {field | τ i field ≤ (T i : WithTop ℕ)}
        Tendsto (fun i => (T i : ℝ) / Real.log (N i : ℝ) ^ 3) atTop (𝓝 0) ∧
        (∀ᶠ i in atTop, T i ≤ H i ∧ 1 + (d i + 1) * (2 * upper i) ≤ N i) ∧
        ∃ b : ℝ, 0 < b ∧ ∀ᶠ i in atTop,
          P.real (E i)ᶜ ≤ Real.exp (-b * Real.log (N i : ℝ)) := by
  intro μ P
  obtain ⟨M, hρ, hsplit, hp₁, hsuccess⟩ :=
    exists_success_probability_lower_bound L hne hsuper
  let B := Step.FiniteSelection.firstNBySlotOrder (α := ℕ) (X := ℝ) 2
  let R := firstOrBelowPotential B realPotential (M : ℝ)
  let growth := B.belowPotential realPotential (M : ℝ)
  let hR := firstOrBelowPotential_measurable B firstTwoBySlotOrder_measurable realPotential M
  let hgrowth := B.belowPotential_measurable firstTwoBySlotOrder_measurable realPotential M
  let law := Selection.Stepwise.binaryOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _)
    growth hgrowth
  let ρ := finiteSlotOffspringMeanReal law
  let p₁ := 1 / (4 * normalizedSecondMomentConstant ρ
    (finiteSlotOffspringSecondMomentReal law - ρ ^ 2))
  let p₀ := (μ (splitBy R)).toReal
  have hρlog : 0 < Real.log ρ := Real.log_pos hρ
  have hp₀ : 0 < p₀ := ENNReal.toReal_pos (ne_of_gt hsplit) (measure_ne_top _ _)
  let α := min (ε / 2) (min (1 / 2) (Real.log ρ / (4 * Real.log 2)))
  have ha : 0 < α := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have ha1 : α < 1 := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by norm_num)
  have haε : α < ε := (min_le_left _ _).trans_lt (by linarith)
  have hsmall : α / Real.log ρ < 1 / (2 * Real.log 2) := by
    refine (div_le_div_of_nonneg_right
      ((min_le_right _ _).trans (min_le_right _ _)) hρlog.le).trans_lt ?_
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hcancel : (Real.log ρ / (4 * Real.log 2)) / Real.log ρ = 1 / (4 * Real.log 2) := by
      field_simp
    rw [hcancel]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  let d i := ⌈(α * Real.log (N i : ℝ) + Real.log 2) / Real.log ρ⌉₊
  let lower i := ⌈(N i : ℝ) ^ α⌉₊
  let upper i := 2 ^ d i
  have hsuccess' : ∀ᶠ i in atTop, p₁ ≤ (offspringFieldLaw μ).real
       {ω | growthTrialSuccess growth (lower i) (upper i) (d i) ω} := by
    filter_upwards [hN.eventually_ge_atTop 1] with i hi
    exact hsuccess (N i) α (lower i) hi
      (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast Nat.zero_lt_of_lt hi) α)) le_rfl
  refine ⟨M, α, ρ, p₁, ha, ha1, haε, hρ, hp₁, hsuccess', ?_⟩
  intro δ hδ
  let K i := ⌊δ * Real.log (N i : ℝ)⌋₊
  let clock i := ⌈(4 * δ / p₀) * Real.log (N i : ℝ)⌉₊
  let η := (0 + (M : ℝ)) * δ + (M : ℝ) * (α / Real.log ρ) + 1
  have hbudget : (0 + (M : ℝ)) * δ + (M : ℝ) * (α / Real.log ρ) < η :=
    lt_add_of_pos_right _ zero_lt_one
  obtain ⟨hscale, hT, hTH⟩ := logarithmicEntrance_scales
    hρ hp₀ ha hδ (Nat.cast_nonneg M) hsmall hbudget hN ht hH
  have hμne : μ nonemptySupport = 1 := by
    change L.sortedPotentialImage nonemptySupport = 1
    rw [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport]
    exact hne
  let μlaw : BranchingProcess.OffspringConfigurationLaw ℕ ℝ := ⟨μ, inferInstance⟩
  have hRneAE : ∀ᵐ ξ ∂μ, (R ξ).Nonempty := by
    filter_upwards [μlaw.hasAtLeastOneChild_ae hμne] with ξ hξ
    exact firstOrBelowPotential_nonempty_of_selected_nonempty B realPotential M ξ
      (firstNBySlotOrder_nonempty_of_support_nonempty (N := 2) (by norm_num) ξ hξ)
  have hRset : MeasurableSet {ξ | (R ξ).Nonempty} := by
    rw [show {ξ | (R ξ).Nonempty} = (fun ξ => (R ξ).card) ⁻¹' Set.Ioi 0 by
      ext ξ
      exact Finset.card_pos.symm]
    exact ((measurable_of_countable fun s : Finset ℕ => s.card).comp hR) measurableSet_Ioi
  have hRne : μ {ξ | (R ξ).Nonempty} = 1 := by
    have hset := (ae_mem_iff_measure_eq hRset.nullMeasurableSet).1 hRneAE
    simpa only [measure_univ] using hset
  refine ⟨hT, hTH.mp (hscale.mono fun i hs hTHi => ⟨hTHi, hs.2.2.2.2.1⟩), ?_⟩
  obtain ⟨b, hb, hbad⟩ := eventually_measure_completionLate_or_trialFailure_le
    μ R growth hR hgrowth hRne hsplit 0 hN K clock d lower upper hδ hp₁
    (hscale.mono fun _ h => h.1)
    (hscale.mono fun _ h => ⟨h.2.2.1, h.2.2.2.1, h.2.1⟩) hsuccess'
  refine ⟨b, hb, hbad.mono fun i hi => ?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hi).trans_eq
    (ENNReal.toReal_ofReal (Real.exp_nonneg _))

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas
