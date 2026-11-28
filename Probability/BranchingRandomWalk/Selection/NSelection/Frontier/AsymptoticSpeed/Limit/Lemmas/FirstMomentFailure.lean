/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.Lemmas.RestartMoment
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.Lemmas.ReserveContinuation
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.RestartEndpoint
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.SampledMark
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Path
import Probability.Independence.Integration.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# First-moment estimate on restart failure

The endpoint is the one in Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (Fudan University, 2026), Appendix A.3. Truncate the sampled displacements before the deadline and use the
generation filtration for the terms at and after it.

## Internal proof declarations

* `integral_restartEndpoint_pos_on_failure_le`:
  $\mathbb E[(M_H^{\mathrm b})_+\mathbf1_{E^c}]
  \le T\mathbb E[(X-b)_+]+(Tb+H(C+2\mathbb E|D|))P(E^c)$, where $D$
  is the leftmost displacement and $X$ its positive part.
* `tendsto_restartEndpoint_on_failure_div_log`: the bound above and the
  exponential bound on the negative part give
  $\mathbb E[M_{H_N}^{\mathrm b}\mathbf1_{E_N^c}]=o(\log N)$ for
  $T_N=O(\log N)$, $H_N=O(\log^3 N)$ and polynomial failure probability.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

open Combinatorics.Branching Combinatorics.UlamHarris
open Combinatorics.Branching.Step.FiniteSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling EndpointDeviation
open SelectedPath SelectedPath.Completion.Lemmas SelectedPath.GrowthTrial

local notation "Ωf" => RootIndexed.StepField (ℕ ⊕ ℕ) ℕ ℝ
local notation "𝔽" => RootIndexed.stepFiltration (Root := ℕ ⊕ ℕ) (α := ℕ) (X := ℝ)

private lemma integral_mark_on_event_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {A : Set Ω} (f : Ω → ℝ) (hf : Integrable f P) (b : ℝ) :
    (∫ ω in A, f ω ∂P) ≤ b * P.real A + ∫ ω, max (f ω - b) 0 ∂P := by
  have he : Integrable (fun ω => max (f ω - b) 0) P :=
    (hf.sub (integrable_const b)).sup (integrable_const 0)
  calc
    _ ≤ ∫ ω in A, b + max (f ω - b) 0 ∂P := by
      apply integral_mono hf.integrableOn ((integrable_const b).add he).integrableOn
      intro ω
      change f ω ≤ b + max (f ω - b) 0
      linarith [le_max_left (f ω - b) (0 : ℝ)]
    _ ≤ _ := by
      rw [integral_add (integrable_const b) he.integrableOn,
        setIntegral_const, smul_eq_mul, mul_comm (P.real A)]
      exact add_le_add_right
        (integral_mono_measure Measure.restrict_le_self
          (ae_of_all _ fun _ => le_max_right _ _) he) _

set_option maxHeartbeats 1000000 in
lemma integral_restartEndpoint_pos_on_failure_le
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hne : L.raw nonemptySupport = 1) (hfirst : HasLeftmostFirstMoment L)
    (M : ℝ) (hM : 0 ≤ M)
    {m N : ℕ} [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hm : 0 < m) (hN : 0 < N) (lower upper duration K T H : ℕ)
    (roots : Ωf → Fin m → RootIndexed.TreeNode (ℕ ⊕ ℕ) ℕ)
    (b : ℝ) (hb : 0 ≤ b) :
    let μ := L.sortedPotentialImage
    let P := RootIndexed.stepFieldLaw (Root := ℕ ⊕ ℕ) μ
    let B := firstNBySlotOrder (α := ℕ) (X := ℝ) 2
    let R := firstOrBelowPotential B realPotential M
    let growth := B.belowPotential realPotential M
    let hB := firstTwoBySlotOrder_measurable (X := ℝ)
    let hR := firstOrBelowPotential_measurable B hB realPotential M
    let hgrowth := B.belowPotential_measurable hB realPotential M
    let τ := SelectedPath.Completion.time R growth hR hgrowth lower upper duration (0 : ℕ)
    let hτ := SelectedPath.Completion.time_isStoppingTime R growth hR hgrowth
      lower upper duration (0 : ℕ)
    let E : Set Ωf := {ω | splitCount R 0 ((τ ω).untopD 0 - (duration + 1))
      (RootIndexed.StepField.left ω) < K} ∩ {ω | τ ω ≤ (T : WithTop ℕ)}
    let F := trialRestartEndpoint N R growth hR hgrowth lower upper duration 0 H roots
    let c := ∫ ξ, |value' ξ 0| ∂μ
    let e := ∫ ξ, max (max (value' ξ 0) 0 - b) 0 ∂μ
    (∀ v, MeasurableSet[hτ.measurableSpace] {ω | roots ω = v}) →
    (∀ ω (n : ℕ), τ ω = n → ∀ i, (roots ω i).2.length = n) →
    (∀ ω, τ ω ≠ ⊤ → Function.Injective (roots ω)) →
    Integrable (fun ω => max (F ω) 0) P ∧
      (∫ ω in Eᶜ, max (F ω) 0 ∂P) ≤
        (T : ℝ) * e + ((T : ℝ) * b + (H : ℝ) * (M + 2 * c)) * P.real Eᶜ := by
  classical
  intro μ P B R growth hB hR hgrowth τ hτ E F c e hfiber hdepth hinj
  let A := Eᶜ
  have hAT : MeasurableSet[𝔽 T] A :=
    ((measurableSet_splitCount_at_stopped_time R hR hτ duration K).2 T).compl
  have hAτ : MeasurableSet[hτ.measurableSpace] A :=
    ((measurableSet_splitCount_at_stopped_time R hR hτ duration K).inter
      (hτ.measurable measurableSet_Iic)).compl
  have hA : MeasurableSet A := (𝔽).le T _ hAT
  let mark := firstSelectedSlotPositivePotential B realPotential
  let step (j : ℕ) := SelectedPath.Coupling.step R (Sum.inl (0 : ℕ) : ℕ ⊕ ℕ) j
  let X (j : ℕ) (ω : Ωf) := mark (step j ω)
  have hmarkm : Measurable mark := firstSelectedSlotPositivePotential_measurable B hB realPotential
  have hmarkPos (ξ) : 0 ≤ mark ξ := by
    simp [mark, firstSelectedSlotPositivePotential]
  have heq : mark =ᵐ[μ] fun ξ => max (value' ξ 0) 0 := firstTwo_positive_eq_slotZero_ae L
  have hs := L.integrable_sortedPotentialImage_firstSlot_abs hboundary hfirst
  have hmark : Integrable mark μ := by
    apply hs.mono' hmarkm.aestronglyMeasurable
    filter_upwards [heq] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (hmarkPos ξ), hξ]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hcm : (∫ ξ, mark ξ ∂μ) ≤ c := by
    apply integral_mono_ae hmark hs
    filter_upwards [heq] with ξ hξ
    rw [hξ]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hc : 0 ≤ c := integral_nonneg fun _ => abs_nonneg _
  have he : 0 ≤ e := integral_nonneg fun _ => le_max_right _ _
  have hstepm (j) : Measurable (step j) := SelectedPath.Coupling.step_measurable R hR _ j
  have hstepLaw (j) : P.map (step j) = μ := SelectedPath.Coupling.step_law μ R hR _ j
  have hXi (j) : Integrable (X j) P :=
    ((hstepLaw j).symm ▸ hmark).comp_aemeasurable (hstepm j).aemeasurable
  have hXlaw (j) : (∫ ω, X j ω ∂P) = ∫ ξ, mark ξ ∂μ := by
    rw [← hstepLaw j]
    exact (integral_map (hstepm j).aemeasurable hmarkm.aestronglyMeasurable).symm
  have hXexcess (j) : (∫ ω, max (X j ω - b) 0 ∂P) = e := by
    have hmExcess : Measurable (fun ξ => max (mark ξ - b) 0) :=
      (hmarkm.sub measurable_const).max measurable_const
    have heMap := integral_map (μ := P) (hstepm j).aemeasurable hmExcess.aestronglyMeasurable
    rw [hstepLaw j] at heMap
    exact heMap.symm.trans (integral_congr_ae (heq.mono fun _ hξ => congrArg (fun x : ℝ => max (x - b) 0) hξ))
  have hXearly (j) : (∫ ω in A, X j ω ∂P) ≤ b * P.real A + e := by
    simpa only [hXexcess j] using integral_mark_on_event_le P (X j) (hXi j) b (A := A)
  have hXlate (j) (hj : T ≤ j) : (∫ ω in A, X j ω ∂P) ≤ c * P.real A := by
    have hind := SelectedPath.Coupling.step_independent μ R hR
      (Sum.inl (0 : ℕ) : ℕ ⊕ ℕ) j
    have hind' : Indep (𝔽 j) (MeasurableSpace.comap (X j) inferInstance) P :=
      indep_of_indep_of_le_right hind
        (hmarkm.comp (comap_measurable (step j))).comap_le
    have hid := integral_abs_mul_indicator_eq_of_indep P (𝔽 j) (X j) A (hXi j)
      ((𝔽).mono hj _ hAT) hA hind'
    have habs (ω) : |X j ω| = X j ω := abs_of_nonneg (hmarkPos (step j ω))
    simp_rw [habs] at hid
    have hprod : (fun ω => X j ω * A.indicator (fun _ => (1 : ℝ)) ω) = A.indicator (X j) := by
      funext ω
      by_cases hω : ω ∈ A <;> simp [hω]
    rw [hprod, integral_indicator hA, hXlaw j] at hid
    exact hid.trans_le (mul_le_mul_of_nonneg_right hcm measureReal_nonneg)
  have hXsum : (∫ ω in A, ∑ j ∈ Finset.range H, X j ω ∂P) ≤
      (T : ℝ) * (b * P.real A + e) + (H : ℝ) * (c * P.real A) := by
    rw [integral_finsetSum _ (fun j _ => (hXi j).integrableOn)]
    let s := (Finset.range H).filter (· < T)
    let u := (Finset.range H).filter (fun j => ¬j < T)
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range H) (p := (· < T))]
    change (∑ j ∈ s, _) + (∑ j ∈ u, _) ≤ _
    apply add_le_add
    · have hcard : s.card ≤ T := by
        simpa using Finset.card_le_card (show s ⊆ Finset.range T from
          fun j hj => Finset.mem_range.mpr (Finset.mem_filter.mp hj).2)
      calc
        _ ≤ ∑ _j ∈ s, (b * P.real A + e) := Finset.sum_le_sum fun j _ => hXearly j
        _ ≤ _ := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    · have hcard : u.card ≤ H := by
        exact (Finset.card_le_card (Finset.filter_subset (fun j => ¬j < T)
          (Finset.range H))).trans_eq (Finset.card_range H)
      calc
        _ ≤ ∑ _j ∈ u, (c * P.real A) :=
          Finset.sum_le_sum fun j hj => hXlate j (le_of_not_gt (Finset.mem_filter.mp hj).2)
        _ ≤ _ := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  let g (i : ℕ) (f : RootIndexed.StepField (Fin m) ℕ ℝ) :=
    max (firstNSelectedEndpointMinimum m N (H - i) f) 0
  let S : Set Ωf := {ω | τ ω ≤ (H : WithTop ℕ)}
  have hS : MeasurableSet S := (𝔽).le H _ (hτ.measurableSet_le H)
  let continuation ω := g ((τ ω).untopD 0) (RootIndexed.selectedSubtreeStepFieldVector roots ω)
  let Y := S.indicator continuation
  have hg (i) : Measurable (g i) :=
    (measurable_firstNSelectedEndpointMinimum m N (H - i)).max measurable_const
  have htest (i) : Integrable (g i) (RootIndexed.stepFieldLaw μ) ∧
      (∫ f, g i f ∂RootIndexed.stepFieldLaw μ) ≤ (H : ℝ) * c := by
    obtain ⟨hi, hiBound⟩ :=
      finiteRootStepFieldLaw_endpointMinimum_firstMoment m N (H - i) hm hN L hboundary hne hfirst
    exact ⟨hi.sup (integrable_const 0), hiBound.trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le H i) hc)⟩
  obtain ⟨hYi, _⟩ := RootIndexed.integral_stopped_selectedSubtreeStepFieldVector_le
    μ τ hτ roots (Set.to_countable _) hfiber hdepth hinj Set.univ MeasurableSet.univ H g hg
    (fun i _ => (htest i).1) _ (fun i _ => (htest i).2)
  have hY : Integrable Y P := by
    rw [integrable_indicator_iff hS]
    simpa [S, continuation] using hYi
  obtain ⟨_, hYb⟩ := RootIndexed.integral_stopped_selectedSubtreeStepFieldVector_le
    μ τ hτ roots (Set.to_countable _) hfiber hdepth hinj A hAτ H g hg
    (fun i _ => (htest i).1) _ (fun i _ => (htest i).2)
  have hYbound : (∫ ω in A, Y ω ∂P) ≤ (H : ℝ) * c * P.real A := by
    rw [integral_indicator hS, Measure.restrict_restrict hS, Set.inter_comm S A]
    exact hYb.trans (by
      rw [mul_comm ((H : ℝ) * c) (P.real A)]
      exact mul_le_mul_of_nonneg_right (measureReal_mono Set.inter_subset_left) (by positivity))
  let U (ω : Ωf) := M * (H : ℝ) + (∑ j ∈ Finset.range H, X j ω) + Y ω
  have hsum : Integrable (fun ω => ∑ j ∈ Finset.range H, X j ω) P :=
    integrable_finsetSum _ fun j _ => hXi j
  have hU : Integrable U P := ((integrable_const _).add hsum).add hY
  have hordered : μ (orderedBySteps realPotential) = 1 := by
    change L.sortedPotentialImage (orderedBySteps realPotential) = 1
    rw [L.sortedPotentialImage_orderedBy]
    simp
  have hμne : μ nonemptySupport = 1 := by
    change L.sortedPotentialImage nonemptySupport = 1
    rwa [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport]
  have hpoint : ∀ᵐ ω ∂P, max (F ω) 0 ≤ U ω := by
    filter_upwards [RootIndexed.stepFieldLaw_ae_all_of_measure_one (Root := ℕ ⊕ ℕ)
        (orderedBySteps_measurable realPotential) μ hordered,
      RootIndexed.stepFieldLaw_ae_all_of_measure_one (Root := ℕ ⊕ ℕ)
        nonemptySupport_measurable μ hμne] with ω ho hsupp
    have hcut : ∀ ξ j, j ∈ growth ξ → ξ.potentialValue' realPotential j ≤ M :=
      fun ξ j hj => ((Step.FiniteSelection.mem_filter B _ ξ j).mp hj).2
    have hpath (j : ℕ) :
        selectedPath R (Sum.inl 0) j ω =
          selectedPath R 0 j (RootIndexed.StepField.left ω) := by
      induction j with
      | zero => simp only [selectedPath]
      | succ j ih => simp only [selectedPath, ih]; rfl
    have hX (j : ℕ) : X j ω =
        mark (RootIndexed.StepField.left ω 0 (selectedPath R 0 j (RootIndexed.StepField.left ω))) := by
      simp only [X, step, SelectedPath.Coupling.step, hpath]
      rfl
    have hbound : max (F ω) 0 ≤
        (M * H + ∑ j ∈ Finset.range H, X j ω) +
          if τ ω ≤ (H : WithTop ℕ) then continuation ω else 0 := by
      simpa only [hX, continuation, g, F, τ, R, mark] using
        trialRestartEndpoint_pos_le N B growth (firstNBySlotOrder_isBoundedBy 2)
          hB hgrowth M hM hcut lower upper duration 0 H roots ω
          (fun j => ho _ _)
          (fun j => firstNBySlotOrder_nonempty_of_support_nonempty (by decide) _ (hsupp _ _))
    by_cases htime : τ ω ≤ (H : WithTop ℕ) <;> simpa [U, Y, S, htime] using hbound
  have hF := measurable_trialRestartEndpoint N R growth hR hgrowth lower upper duration 0 H roots hfiber
  have hpos : Integrable (fun ω => max (F ω) 0) P := hU.mono'
    (hF.max measurable_const).aestronglyMeasurable
    (hpoint.mono fun ω h => by rwa [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)])
  refine ⟨hpos, ?_⟩
  calc
    _ ≤ ∫ ω in A, U ω ∂P :=
      integral_mono_ae hpos.integrableOn hU.integrableOn (ae_restrict_of_ae hpoint)
    _ ≤ _ := by
      have hdecomp :
          (∫ ω in A, U ω ∂P) =
            P.real A * (M * (H : ℝ)) + (∫ ω in A, ∑ j ∈ Finset.range H, X j ω ∂P) +
              ∫ ω in A, Y ω ∂P := by
        change (∫ ω in A, (M * (H : ℝ) + ∑ j ∈ Finset.range H, X j ω) + Y ω ∂P) = _
        rw [integral_add (f := fun ω => M * (H : ℝ) + ∑ j ∈ Finset.range H, X j ω)
          ((integrable_const (M * (H : ℝ))).add hsum.integrableOn)
          hY.integrableOn, integral_add (integrable_const (M * (H : ℝ))) hsum.integrableOn,
          setIntegral_const, smul_eq_mul]
      rw [hdecomp]
      change _ ≤ (T : ℝ) * e + ((T : ℝ) * b + (H : ℝ) * (M + 2 * c)) * P.real A
      linear_combination hXsum + hYbound

private lemma integral_endpoint_neg_le_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {F : Ω → ℝ} (hF : Measurable F)
    (hexp : (∫⁻ ω, ENNReal.ofReal (Real.exp (-F ω)) ∂P) ≤ 1) :
    Integrable (fun ω => max (-F ω) 0) P ∧
      (∫ ω, max (-F ω) 0 ∂P) ≤ 1 := by
  have hm := Real.continuous_exp.measurable.comp hF.neg
  have hInt : Integrable (fun ω => Real.exp (-F ω)) P := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => Real.exp_nonneg _)]
    exact hexp.trans_lt ENNReal.one_lt_top
  have hpoint (ω : Ω) : max (-F ω) 0 ≤ Real.exp (-F ω) :=
    max_le (by linarith [Real.add_one_le_exp (-F ω)]) (Real.exp_nonneg _)
  have hneg : Integrable (fun ω => max (-F ω) 0) P :=
    hInt.mono' (hF.neg.max measurable_const).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact hpoint ω)
  refine ⟨hneg, (integral_mono hneg hInt hpoint).trans ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun ω => Real.exp (-F ω)) (ae_of_all _ fun _ => Real.exp_nonneg _)
    hm.aestronglyMeasurable]
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top hexp

private lemma tendsto_integral_excess_nat {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : Integrable X μ) (hpos : ∀ ω, 0 ≤ X ω) :
    Tendsto (fun b : ℕ => ∫ ω, max (X ω - b) 0 ∂μ) atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence
    (F := fun (b : ℕ) ω => max (X ω - b) 0) (f := fun _ => (0 : ℝ)) X
    (fun b => (hX.aestronglyMeasurable.sub aestronglyMeasurable_const).sup
      aestronglyMeasurable_const) hX
    (fun b => ae_of_all _ fun ω => by
      change ‖max (X ω - (b : ℝ)) 0‖ ≤ X ω
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (sub_le_self _ (Nat.cast_nonneg _)) (hpos ω))
    (ae_of_all _ fun ω => by
      have hnat : Tendsto (fun b : ℕ => (b : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
      filter_upwards [hnat.eventually_ge_atTop (X ω)] with b hb
      exact (max_eq_right (sub_nonpos.mpr hb)).symm)
  simpa using ht

private lemma tendsto_failure_bound_div_log
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX : Integrable X μ) (hXpos : ∀ ω, 0 ≤ X ω)
    {logN : ℕ → ℝ} (hlog : Tendsto logN atTop atTop)
    {T H : ℕ → ℕ} {p u : ℕ → ℝ} {C D a q : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (ha : 0 ≤ a) (hq : 0 < q)
    (hT : ∀ᶠ n in atTop, (T n : ℝ) ≤ C * logN n)
    (hH : ∀ᶠ n in atTop, (H n : ℝ) ≤ D * (logN n)^3)
    (hp : ∀ᶠ n in atTop, 0 ≤ p n ∧ p n ≤ Real.exp (-q * logN n))
    (hu : ∀ᶠ n in atTop, 0 ≤ u n)
    (hbound : ∀ b : ℕ, ∀ᶠ n in atTop,
      u n ≤ (T n : ℝ) * (∫ ω, max (X ω - b) 0 ∂μ) +
        ((T n : ℝ) * b + (H n : ℝ) * a) * p n) :
    Tendsto (fun n => u n / logN n) atTop (𝓝 0) := by
  have hdecay : Tendsto (fun n => (logN n)^2 * Real.exp (-q * logN n)) atTop (𝓝 0) := by
    have hqlog : Tendsto (fun n => q * logN n) atTop atTop := hlog.const_mul_atTop hq
    have ht := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hqlog).const_mul (q⁻¹ ^ 2)
    simp only [mul_zero, Function.comp_apply] at ht
    refine ht.congr fun n => ?_
    field_simp
  have hprob : Tendsto (fun n => Real.exp (-q * logN n)) atTop (𝓝 0) := by
    have hneg : Tendsto (fun n => -q * logN n) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (by linarith : -q < 0)).2 hlog
    exact Real.tendsto_exp_atBot.comp hneg
  have hexcess := (tendsto_integral_excess_nat hX hXpos).const_mul C
  rw [mul_zero] at hexcess
  rw [tendsto_order]
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · filter_upwards [hu, hlog.eventually_gt_atTop 0] with n hn hLn
    exact hz.trans_le (div_nonneg hn hLn.le)
  · obtain ⟨b, hb⟩ := (hexcess.eventually (Iio_mem_nhds (show 0 < z / 2 by positivity))).exists
    let e := ∫ ω, max (X ω - b) 0 ∂μ
    have he : 0 ≤ e := integral_nonneg fun _ => le_max_right _ _
    have hvanish :
        Tendsto (fun n => (C * (b : ℝ)) * Real.exp (-q * logN n) +
          (D * a) * ((logN n)^2 * Real.exp (-q * logN n))) atTop (𝓝 0) := by
      simpa only [mul_zero, add_zero] using
        (hprob.const_mul (C * (b : ℝ))).add (hdecay.const_mul (D * a))
    filter_upwards [hT, hH, hp, hbound b, hlog.eventually_gt_atTop 0,
      hvanish.eventually (Iio_mem_nhds (show 0 < z / 2 by positivity))] with
        n hTn hHn hpn hn hLn hsmall
    have hterm :
        ((T n : ℝ) * b + (H n : ℝ) * a) * p n ≤
          ((C * logN n) * b + (D * (logN n)^3) * a) * Real.exp (-q * logN n) :=
      mul_le_mul
        (add_le_add (mul_le_mul_of_nonneg_right hTn (Nat.cast_nonneg _))
          (mul_le_mul_of_nonneg_right hHn ha)) hpn.2 hpn.1 (by positivity)
    have hdiv : u n / logN n ≤ C * e +
        ((C * (b : ℝ)) * Real.exp (-q * logN n) +
          (D * a) * ((logN n)^2 * Real.exp (-q * logN n))) := by
      apply (div_le_iff₀ hLn).2
      calc
        _ ≤ (T n : ℝ) * e + ((T n : ℝ) * b + (H n : ℝ) * a) * p n := hn
        _ ≤ (C * logN n) * e +
            ((C * logN n) * b + (D * (logN n)^3) * a) * Real.exp (-q * logN n) :=
          add_le_add (mul_le_mul_of_nonneg_right hTn he) hterm
        _ = _ := by ring
    exact hdiv.trans_lt (by
      change C * e < z / 2 at hb
      change _ < z / 2 at hsmall
      linarith)

/-- The endpoint on the actual restart failure event has
expectation $o(\log N)$ under the leftmost first-moment assumption. -/
lemma tendsto_restartEndpoint_on_failure_div_log
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hne : L.raw nonemptySupport = 1) (hfirst : HasLeftmostFirstMoment L)
    (M : ℝ) (hM : 0 ≤ M)
    {m N lower upper duration K T H : ℕ → ℕ}
    (roots : ∀ n, Ωf → Fin (m n) → RootIndexed.TreeNode (ℕ ⊕ ℕ) ℕ)
    {C D q : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hq : 0 < q)
    (hN : Tendsto N atTop atTop)
    (hT : ∀ᶠ n in atTop, (T n : ℝ) ≤ C * Real.log (N n : ℝ))
    (hH : ∀ᶠ n in atTop, (H n : ℝ) ≤ D * Real.log (N n : ℝ) ^ 3) :
    let μ := L.sortedPotentialImage
    let P := RootIndexed.stepFieldLaw (Root := ℕ ⊕ ℕ) μ
    let B := firstNBySlotOrder (α := ℕ) (X := ℝ) 2
    let R := firstOrBelowPotential B realPotential M
    let growth := B.belowPotential realPotential M
    let hB := firstTwoBySlotOrder_measurable (X := ℝ)
    let hR := firstOrBelowPotential_measurable B hB realPotential M
    let hgrowth := B.belowPotential_measurable hB realPotential M
    let τ n := Completion.time R growth hR hgrowth (lower n) (upper n) (duration n) (0 : ℕ)
    let hτ n := Completion.time_isStoppingTime R growth hR hgrowth
      (lower n) (upper n) (duration n) (0 : ℕ)
    let E (n : ℕ) : Set Ωf := {ω | splitCount R 0 ((τ n ω).untopD 0 - (duration n + 1))
      (RootIndexed.StepField.left ω) < K n} ∩ {ω | τ n ω ≤ (T n : WithTop ℕ)}
    let F n := @trialRestartEndpoint (m n) (RootIndexed.addressLinearOrder (Fin (m n)) ℕ)
      (N n) R growth hR hgrowth (lower n) (upper n) (duration n) 0 (H n) (roots n)
    (∀ᶠ n in atTop, 0 < m n ∧ 0 < N n ∧
      (∀ v, MeasurableSet[(hτ n).measurableSpace] {ω | roots n ω = v}) ∧
      (∀ ω (i : ℕ), τ n ω = i → ∀ j, (roots n ω j).2.length = i) ∧
      (∀ ω, τ n ω ≠ ⊤ → Function.Injective (roots n ω))) →
    (∀ᶠ n in atTop, P.real (E n)ᶜ ≤ Real.exp (-q * Real.log (N n : ℝ))) →
    (∀ᶠ n in atTop, let order := RootIndexed.addressLinearOrder (Fin 1) ℕ
      ∀ x : ℝ, (RootIndexed.stepFieldLaw (Root := Fin 1) μ)
        {ω | x ≤ @firstNSelectedEndpointMinimum 1 (N n) (H n) order ω} ≤
          P {ω | x ≤ F n ω}) →
    (∀ᶠ n in atTop, Integrable (F n) P) ∧
    Tendsto (fun n => (∫ ω in (E n)ᶜ, F n ω ∂P) / Real.log (N n : ℝ)) atTop (𝓝 0) := by
  intro μ P B R growth hB hR hgrowth τ hτ E F hroots hprob horder
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hslot := L.integrable_sortedPotentialImage_firstSlot_abs hboundary hfirst
  let X (ξ : Step ℕ ℝ) := max (value' ξ 0) 0
  have hX : Integrable X μ := hslot.mono'
    ((value'_measurable (0 : ℕ)).max measurable_const).aestronglyMeasurable
    (ae_of_all _ fun _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _))
  let c := ∫ ξ, |value' ξ 0| ∂μ
  have hc : 0 ≤ c := integral_nonneg fun _ => abs_nonneg _
  let Lg n := Real.log (N n : ℝ)
  let Xpos n ω := max (F n ω) 0
  let Xneg n ω := max (-F n ω) 0
  have hpositive : Tendsto (fun n => (∫ ω in (E n)ᶜ, Xpos n ω ∂P) / Lg n) atTop (𝓝 0) := by
    apply tendsto_failure_bound_div_log hX (fun _ => le_max_right _ _) hlog
      hC hD (show 0 ≤ M + 2 * c by positivity) hq hT hH
      (hprob.mono fun _ hp => ⟨measureReal_nonneg, hp⟩)
      (Eventually.of_forall fun _ => integral_nonneg fun _ => le_max_right _ _)
    intro b
    filter_upwards [hroots] with n ⟨hm, hNn, hfiber, hdepth, hinj⟩
    let := RootIndexed.addressLinearOrder (Fin (m n)) ℕ
    exact (integral_restartEndpoint_pos_on_failure_le L hboundary hne hfirst M hM hm hNn
      (lower n) (upper n) (duration n) (K n) (T n) (H n) (roots n) b (Nat.cast_nonneg _)
      hfiber hdepth hinj).2
  have hmom : ∀ᶠ n in atTop, Integrable (Xpos n) P ∧ Integrable (Xneg n) P ∧
      (∫ ω, Xneg n ω ∂P) ≤ 1 := by
    filter_upwards [hroots, horder] with n ⟨hm, hNn, hfiber, hdepth, hinj⟩ hord
    let := RootIndexed.addressLinearOrder (Fin (m n)) ℕ
    have hpos := (integral_restartEndpoint_pos_on_failure_le L hboundary hne hfirst
      M hM hm hNn (lower n) (upper n) (duration n) (K n) (T n) (H n) (roots n) 0 le_rfl
      hfiber hdepth hinj).1
    have hF : Measurable (F n) := measurable_trialRestartEndpoint
      (N n) R growth hR hgrowth (lower n) (upper n) (duration n) 0 (H n) (roots n) hfiber
    have hμne : μ nonemptySupport = 1 := by
      change L.sortedPotentialImage nonemptySupport = 1
      rwa [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport]
    have hExp := lintegral_exp_neg_trialRestartEndpoint_le μ
      (L.sortedPotentialImage_hasBoundaryNormalization hboundary) hμne (N n) hNn (H n) (F n) hF hord
    have hneg := integral_endpoint_neg_le_one P hF (by simpa using hExp)
    exact ⟨hpos, hneg⟩
  have hsplit (n) : F n = fun ω => Xpos n ω - Xneg n ω := by
    funext ω
    change F n ω = max (F n ω) 0 - max (-F n ω) 0
    rcases le_total (F n ω) 0 with h | h
    · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  refine ⟨hmom.mono fun n h => hsplit n ▸ h.1.sub h.2.1, ?_⟩
  have hnegative : Tendsto (fun n => (∫ ω in (E n)ᶜ, Xneg n ω ∂P) / Lg n) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hlog)
    · filter_upwards [hlog.eventually_gt_atTop 0] with n hn
      exact div_nonneg (integral_nonneg fun _ => le_max_right _ _) hn.le
    · filter_upwards [hmom, hlog.eventually_gt_atTop 0] with n h hn
      exact div_le_div_of_nonneg_right
        ((integral_mono_measure Measure.restrict_le_self
          (ae_of_all _ fun _ => le_max_right _ _) h.2.1).trans h.2.2) hn.le
  have hdiff := hpositive.sub hnegative
  rw [sub_zero] at hdiff
  apply hdiff.congr'
  filter_upwards [hmom] with n h
  rw [hsplit n, integral_sub h.1.integrableOn h.2.1.integrableOn, sub_div]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed
