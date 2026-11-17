/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Basic
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.WaitingTime
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.TrialIndependence
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Lemmas.RecursiveClock
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.EntranceScales
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Success

/-!
# Probability of a late or unsuccessful entrance

## Internal proof declarations

* `eventually_measure_completionLate_or_trialFailure_le`: for a uniform
  one-trial success probability $p_1>0$ and the geometric-moment condition
  on $\gamma$ below, $\mathbb P(\{\kappa\le K_N,\ \tau\le T_N\}^c)
  \le N^{-b}$ eventually for some $b>0$.
* `exists_logarithmicTrialClock_failure_le_polynomial`: with the binary cutoff
  rule and $d_N=\lfloor\alpha\log N/\log\rho\rfloor+2$, a fixed positive
  success bound holds at target $\lceil N^\alpha\rceil$. On the original
  candidate tree the good-event complement is $O(N^{-b})$ for
  $T_N=\lfloor\gamma\log N\rfloor$ and $K_N=\lfloor\delta\log N\rfloor$,
  provided $\gamma>\delta+\alpha/\log\rho+
  \delta\log(\mathbb E e^{\theta G_1})/\theta$ for a positive
  $\theta$ with $e^\theta(1-p_0)<1$.

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
    (K duration lower upper : ℕ → ℕ) {δ p₁ A θ γ : ℝ}
    (hδ : 0 < δ) (hp₁ : 0 < p₁) (hθ : 0 < θ)
    (hK : ∀ᶠ i in atTop,
      δ * Real.log (N i : ℝ) / 2 ≤ (K i : ℝ) ∧ (K i : ℝ) ≤ δ * Real.log (N i : ℝ))
    (hduration : ∀ i, (duration i : ℝ) ≤ A * Real.log (N i : ℝ) + 2)
    (hratio : ENNReal.ofReal (Real.exp θ) * (1 - μ (splitBy R)) < 1)
    (hγ : δ + A + δ / θ *
      Real.log (μ (splitBy R) / (1 - ENNReal.ofReal (Real.exp θ) * (1 - μ (splitBy R)))).toReal < γ)
    (hsuccess : ∀ᶠ i in atTop,
      p₁ ≤ (offspringFieldLaw μ).real
        {ω | growthTrialSuccess growth (lower i) (upper i) (duration i) ω}) :
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ i in atTop,
      let τ := Completion.time R growth hR hgrowth (lower i) (upper i) (duration i) r
      let T := ⌊γ * Real.log (N i : ℝ)⌋₊
      let E := {field | splitCount R r ((τ field).untopD 0 - (duration i + 1))
        (RootIndexed.StepField.left field) < K i} ∩ {field | τ field ≤ (T : WithTop ℕ)}
      P Eᶜ ≤ ENNReal.ofReal (Real.exp (-b * Real.log (N i : ℝ))) := by
  intro P
  let L := fun i => Real.log (N i : ℝ)
  let ν := offspringFieldLaw μ
  have hL : Tendsto L atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  let B := μ (splitBy R) / (1 - ENNReal.ofReal (Real.exp θ) * (1 - μ (splitBy R)))
  let gap := θ * (γ - δ - A) - δ * Real.log B.toReal
  have hBfinite : B ≠ ∞ :=
    (ENNReal.div_lt_top (measure_ne_top _ _) (ne_of_gt (tsub_pos_of_lt hratio))).ne
  have hB : 1 ≤ B.toReal :=
    one_le_splitWaitingTime_expMoment μ R hR hRne hsplit hθ.le hratio
  have hBLog : 0 ≤ Real.log B.toReal := Real.log_nonneg hB
  have hgap : 0 < gap := by
    have heq : θ * (δ / θ) = δ := by field_simp
    dsimp [gap]
    change δ + A + δ / θ * Real.log B.toReal < γ at hγ
    have hm := mul_lt_mul_of_pos_left hγ hθ
    rw [mul_add, ← mul_assoc, heq] at hm
    linarith
  let b := min (gap / 2) (p₁ * δ / 2)
  have hb : 0 < b := lt_min (div_pos hgap two_pos) (by positivity)
  have hblog : b ≤ p₁ * δ / 2 := min_le_right _ _
  have hbgap : b ≤ gap / 2 := min_le_left _ _
  have habsorb : ∀ᶠ i in atTop, 2 ≤ Real.exp (b / 2 * L i) :=
    (Real.tendsto_exp_atTop.comp (hL.const_mul_atTop (by positivity))).eventually_ge_atTop 2
  refine ⟨b / 2, by positivity, ?_⟩
  filter_upwards [hK, hsuccess, habsorb, hL.eventually_ge_atTop 0,
    hL.eventually_ge_atTop (4 * θ / gap)] with i hk hs hab hLog hmargin
  dsimp only
  let G := growthTrialSuccess growth (lower i) (upper i) (duration i)
  let w := Real.exp (-b * L i)
  have hG : MeasurableSet {ω | G ω} :=
    (generationFiltration (M := Step ℕ ℝ)).le (duration i) _
      (growthTrialSuccess_measurable growth hgrowth (lower i) (upper i) (duration i))
  have hqbound : ν {ω | ¬ G ω} ≤ ENNReal.ofReal (Real.exp (-p₁)) := by
    change ν {ω | G ω}ᶜ ≤ ENNReal.ofReal (Real.exp (-p₁))
    rw [prob_compl_eq_one_sub hG]
    have hle : ν {ω | G ω} ≤ 1 := (measure_mono (Set.subset_univ _)).trans_eq measure_univ
    have hfinite : 1 - ν {ω | G ω} ≠ ∞ := (tsub_le_self.trans_lt ENNReal.one_lt_top).ne
    rw [← ENNReal.ofReal_toReal hfinite, ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top,
      ENNReal.toReal_one]
    apply ENNReal.ofReal_le_ofReal
    exact (sub_le_sub_left hs 1).trans (by linarith [Real.add_one_le_exp (-p₁)])
  have hpow : (ν {ω | ¬ G ω}) ^ K i ≤ ENNReal.ofReal w :=
    (pow_le_pow_left₀ zero_le hqbound _).trans <| by
      rw [← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul]
      apply ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      have ha := mul_le_mul_of_nonpos_right hk.1 (neg_nonpos.mpr hp₁.le)
      have hb' := mul_le_mul_of_nonneg_right hblog hLog
      linarith only [ha, hb',
        show (δ * L i / 2) * (-p₁) = -(p₁ * δ / 2) * L i by ring]
  let τ := Completion.time R growth hR hgrowth (lower i) (upper i) (duration i) r
  let T := ⌊γ * L i⌋₊
  let left : RootIndexed.StepField (Root ⊕ Root) ℕ ℝ → RootIndexed.StepField Root ℕ ℝ :=
    RootIndexed.StepField.left
  let f := fun field => left field r
  let x := γ * L i - (K i : ℝ) - (duration i : ℝ)
  let lateCycle : Set (Mark ℕ (Step ℕ ℝ)) := {ω | x ≤ ∑ j ∈ Finset.range (K i),
    ((splitCycle R (splitWaitingTime R) (fun _ => PUnit.unit.{1}) j ω).1 : ℝ)}
  let late := f ⁻¹' lateCycle
  let failed := f ⁻¹' recursiveFailure R growth (duration i) (lower i) (upper i) (K i)
  have hleft : Measurable left := measurable_pi_iff.mpr fun i => measurable_pi_apply (Sum.inl i)
  have hleftlaw : P.map left = RootIndexed.stepFieldLaw (Root := Root) μ :=
    RootIndexed.stepFieldLaw_reindex μ Sum.inl Sum.inl_injective
  have hf : Measurable f := (measurable_pi_apply r).comp hleft
  have hflaw : P.map f = ν := by
    change P.map ((fun ω : RootIndexed.StepField Root ℕ ℝ => ω r) ∘ left) = ν
    rw [← Measure.map_map (measurable_pi_apply r) hleft, hleftlaw,
      RootIndexed.stepFieldLaw_root_marginal μ r]
  have hlateMeas : MeasurableSet lateCycle := by
    have hwait := (splitWaitingTime_measurable R hR).mono
      (selectedPopulationSplitCompletion_isStoppingTime R hR).measurableSpace_le le_rfl
    have hsum : Measurable (fun ω => ∑ j ∈ Finset.range (K i),
        ((splitCycle R (splitWaitingTime R) (fun _ => PUnit.unit.{1}) j ω).1 : ℝ)) :=
      Finset.measurable_sum _ fun j _ =>
        (measurable_of_countable fun k : ℕ => (k : ℝ)).comp
          (measurable_fst.comp (measurable_splitCycle R hR _ hwait _ measurable_const j))
    exact hsum measurableSet_Ici
  have hlate : P late ≤ ENNReal.ofReal w := by
    change P (f ⁻¹' lateCycle) ≤ _
    rw [← Measure.map_apply hf hlateMeas, hflaw]
    refine (measure_splitWaitingTime_sum_ge_le μ R hR hRne hsplit θ x hθ (K i)).trans ?_
    change ENNReal.ofReal (Real.exp (-θ * x)) * B ^ K i ≤ _
    rw [← ENNReal.ofReal_toReal hBfinite, ← ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.exp_log (lt_of_lt_of_le zero_lt_one hB), ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hKlog := mul_le_mul_of_nonneg_right hk.2 hBLog
    have hgapL := (div_le_iff₀ hgap).mp hmargin
    have hbL := mul_le_mul_of_nonneg_right hbgap hLog
    have hx : (δ + A - γ) * L i + 2 ≥ -x := by
      dsimp [x]
      linarith only [hk.2, hduration i,
        show (δ + A - γ) * L i = δ * L i + A * L i - γ * L i by ring]
    have hxθ := mul_le_mul_of_nonneg_left hx hθ.le
    change -θ * x + (K i : ℝ) * Real.log B.toReal ≤ -b * L i
    have he : θ * ((δ + A - γ) * L i + 2) + δ * L i * Real.log B.toReal =
        -(gap * L i) + 2 * θ := by dsimp [gap]; ring
    linarith only [hKlog, hgapL, hbL, hxθ, he,
      show -θ * x = θ * (-x) by ring, mul_comm (L i) gap]
  have hfinite := selectedPopulationSplitCompletion_ae_finite_of_nonempty_and_split_pos
    μ R hR hRne (splitBy_measurable R hR) hsplit
  have hfailed : P failed ≤ ENNReal.ofReal w := by
    change P (f ⁻¹' recursiveFailure R growth (duration i) (lower i) (upper i) (K i)) ≤ _
    rw [← Measure.map_apply hf (recursiveFailure_measurable R growth hR hgrowth _ _ _ _),
      hflaw, measure_recursiveFailure_eq_pow μ R growth hR hgrowth _ _ _ hfinite]
    exact hpow
  have hwait := ae_of_ae_map hf.aemeasurable
    (by rw [hflaw]; exact splitCount_at_waitingTime_sum_ae μ R hR hRne hsplit (K i))
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
    filter_upwards [hall, hwait] with field hmarks hwaitField hbad
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
    · by_cases hLate : field ∈ late
      · exact Or.inl hLate
      let n := K i + ∑ j ∈ Finset.range (K i),
        (splitCycle R (splitWaitingTime R) (fun _ => PUnit.unit.{1}) j (f field)).1
      have hnT : n + duration i ≤ T := by
        apply Nat.le_floor
        change ¬ x ≤ ∑ j ∈ Finset.range (K i),
          ((splitCycle R (splitWaitingTime R) (fun _ => PUnit.unit.{1}) j (f field)).1 : ℝ) at hLate
        have hsum := lt_of_not_ge hLate
        push_cast
        dsimp [n, x] at *
        push_cast
        linarith
      refine Or.inr (mem_recursiveFailure_of_no_success R growth hR (lower i) (upper i)
        (duration i) (K i) r (left field) hmarks n
        (hwaitField Root r (left field) rfl).ge ?_)
      intro k hk hs'
      apply htime
      change firstSuccessfulCompletion R growth hR (lower i) (upper i) (duration i) r
        (left field) ≤ (T : WithTop ℕ)
      exact (firstDeclaredSuccess_le_iff _ _ T).2
        ⟨k + 1 + duration i, by omega, k, rfl, hs'⟩
  refine (measure_mono_ae hsub).trans ((measure_union_le _ _).trans
    ((add_le_add hlate hfailed).trans ?_))
  have hm : 2 * w ≤ Real.exp (-(b / 2) * L i) := by
    calc
      _ ≤ Real.exp (b / 2 * L i) * w := mul_le_mul_of_nonneg_right hab (by positivity)
      _ = _ := by rw [show w = Real.exp (-b * L i) from rfl, ← Real.exp_add]; congr 1; ring
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ w) (by positivity : 0 ≤ w)]
  exact ENNReal.ofReal_le_ofReal (by linarith only [hm])

/-- The success and clock estimates for the original pre-sampled growth
trial, with the integer target corresponding to population at least
$N^\alpha$ at the duration $d_N=\ell-1$. The exponent may be chosen arbitrarily small. -/
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
    ∃ (M : ℕ) (α ρ p₁ : ℝ),
      0 < α ∧ α < 1 ∧ α < ε ∧ 1 < ρ ∧ 0 < p₁ ∧
      let B := Step.FiniteSelection.firstNBySlotOrder (α := ℕ) (X := ℝ) 2
      let R := firstOrBelowPotential B realPotential (M : ℝ)
      let growth := B.belowPotential realPotential (M : ℝ)
      let hR := firstOrBelowPotential_measurable B firstTwoBySlotOrder_measurable realPotential M
      let hgrowth := B.belowPotential_measurable firstTwoBySlotOrder_measurable realPotential M
      let d i := ⌊α * Real.log (N i : ℝ) / Real.log ρ⌋₊ + 2
      let lower i := ⌈(N i : ℝ) ^ α⌉₊
      let upper i := 2 ^ d i
      let τ i := Completion.time R growth hR hgrowth (lower i) (upper i) (d i) (0 : ℕ)
      (∀ᶠ i in atTop, p₁ ≤ (offspringFieldLaw μ).real
        {ω | growthTrialSuccess growth (lower i) (upper i) (d i) ω}) ∧
      ∀ δ θ γ : ℝ, 0 < δ → 0 < θ →
        ENNReal.ofReal (Real.exp θ) * (1 - μ (splitBy R)) < 1 →
        δ + α / Real.log ρ + δ / θ *
          Real.log (μ (splitBy R) / (1 - ENNReal.ofReal (Real.exp θ) *
            (1 - μ (splitBy R)))).toReal < γ →
        let K i := ⌊δ * Real.log (N i : ℝ)⌋₊
        let T i := ⌊γ * Real.log (N i : ℝ)⌋₊
        let E i := {field | splitCount R 0 ((τ i field).untopD 0 - (d i + 1))
          (RootIndexed.StepField.left field) < K i} ∩ {field | τ i field ≤ (T i : WithTop ℕ)}
        Tendsto (fun i => (T i : ℝ) / Real.log (N i : ℝ) ^ 3) atTop (𝓝 0) ∧
        (∀ᶠ i in atTop, T i ≤ H i ∧ 1 + (d i + 1) * (2 * upper i) ≤ N i) ∧
        ∃ b : ℝ, 0 < b ∧ ∀ᶠ i in atTop,
          P.real (E i)ᶜ ≤ Real.exp (-b * Real.log (N i : ℝ)) := by
  intro μ P
  obtain ⟨M, hρ, hsplit, p₁, hp₁, hsuccess⟩ :=
    exists_success_probability_lower_bound L hne hsuper
  let B := Step.FiniteSelection.firstNBySlotOrder (α := ℕ) (X := ℝ) 2
  let R := firstOrBelowPotential B realPotential (M : ℝ)
  let growth := B.belowPotential realPotential (M : ℝ)
  let hR := firstOrBelowPotential_measurable B firstTwoBySlotOrder_measurable realPotential M
  let hgrowth := B.belowPotential_measurable firstTwoBySlotOrder_measurable realPotential M
  let law := Selection.Stepwise.binaryOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _)
    growth hgrowth
  let ρ := finiteSlotOffspringMeanReal law
  have hρlog : 0 < Real.log ρ := Real.log_pos hρ
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
  let d i := ⌊α * Real.log (N i : ℝ) / Real.log ρ⌋₊ + 2
  let lower i := ⌈(N i : ℝ) ^ α⌉₊
  let upper i := 2 ^ d i
  have hparallel := logarithmicEntrance_scales hρ ha (δ := 1) zero_lt_one
    (M := (M : ℝ)) (Nat.cast_nonneg M) (v := 0) hsmall
    (η := (0 + (M : ℝ)) * 1 + (M : ℝ) * (α / Real.log ρ) + 1)
    (lt_add_of_pos_right _ zero_lt_one) hN d (fun i => trialDuration_le hρ ha.le (N i))
  have hcapacity : growth.IsBoundedBy 2 := by
    intro ξ
    exact (Finset.card_le_card (fun i hi =>
      ((Step.FiniteSelection.mem_filter B _ ξ i).mp hi).1)).trans
      (firstNBySlotOrder_isBoundedBy 2 ξ)
  obtain ⟨hdTop, hMarkov⟩ := trialDuration_markov_scales hρ ha ha1 hN
  have hscaleSuccess : ∀ᶠ i in atTop, 0 < N i ∧ 0 < (N i : ℝ) ^ α ∧
      ρ * (N i : ℝ) ^ α ≤ ρ ^ d i := by
    filter_upwards [hN.eventually_ge_atTop 1] with i hi
    have hNi : 0 < N i := Nat.zero_lt_of_lt hi
    exact ⟨hNi, Real.rpow_pos_of_pos (by exact_mod_cast hNi) α,
      rpow_mul_mean_le_pow_trialDuration hρ (N i) α hi⟩
  have hsuccess' : ∀ᶠ i in atTop, p₁ ≤ (offspringFieldLaw μ).real
      {ω | growthTrialSuccess growth (lower i) (upper i) (d i) ω} := by
    filter_upwards [hsuccess d N (fun i => (N i : ℝ) ^ α) hdTop hscaleSuccess hMarkov,
      hscaleSuccess, hparallel] with i hs hscale hbudget
    have hupper : 2 ^ d i ≤ N i := by
      have hh := hbudget.2.2.1
      nlinarith
    rw [show upper i = 2 ^ d i by rfl,
      growthTrialSuccess_eq_of_binary_horizon_le growth hcapacity (lower i) (d i) (N i)
        (Nat.ceil_pos.mpr hscale.2.1) hupper]
    exact hs
  refine ⟨M, α, ρ, p₁, ha, ha1, haε, hρ, hp₁, hsuccess', ?_⟩
  intro δ θ γ hδ hθ hratio hγ
  let K i := ⌊δ * Real.log (N i : ℝ)⌋₊
  let η := (0 + (M : ℝ)) * δ + (M : ℝ) * (α / Real.log ρ) + 1
  have hbudget : (0 + (M : ℝ)) * δ + (M : ℝ) * (α / Real.log ρ) < η :=
    lt_add_of_pos_right _ zero_lt_one
  have hd (i : ℕ) : (d i : ℝ) ≤ (α / Real.log ρ) * Real.log (N i : ℝ) + 2 := by
    rw [show (α / Real.log ρ) * Real.log (N i : ℝ) = α * Real.log (N i : ℝ) / Real.log ρ by
      ring]
    exact trialDuration_le hρ ha.le (N i)
  have hscale := logarithmicEntrance_scales
    hρ ha hδ (Nat.cast_nonneg M) hsmall hbudget hN d
    (fun i => trialDuration_le hρ ha.le (N i))
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
  have hB : 1 ≤ (μ (splitBy R) /
      (1 - ENNReal.ofReal (Real.exp θ) * (1 - μ (splitBy R)))).toReal :=
    one_le_splitWaitingTime_expMoment μ R hR hRne hsplit hθ.le hratio
  have hγ' : 0 < γ :=
    (div_nonneg ha.le hρlog.le).trans_lt <|
    lt_of_le_of_lt (by nlinarith [mul_nonneg (div_nonneg hδ.le hθ.le) (Real.log_nonneg hB)]) hγ
  obtain ⟨hT, hTH⟩ := logarithmicEntrance_deadline hγ' hN ht hH
  refine ⟨hT, hTH.mp (hscale.mono fun i hs hTHi => ⟨hTHi, hs.2.2.1⟩), ?_⟩
  obtain ⟨b, hb, hbad⟩ := eventually_measure_completionLate_or_trialFailure_le
    μ R growth hR hgrowth hRne hsplit 0 hN K d lower upper hδ hp₁ hθ
    (hscale.mono fun _ h => ⟨h.1, h.2.1⟩) hd hratio hγ hsuccess'
  refine ⟨b, hb, hbad.mono fun i hi => ?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hi).trans_eq
    (ENNReal.toReal_ofReal (Real.exp_nonneg _))

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas
