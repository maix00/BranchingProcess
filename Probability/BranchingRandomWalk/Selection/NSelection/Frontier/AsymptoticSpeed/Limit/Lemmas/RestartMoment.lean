/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.RestartEndpoint
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Lemmas.Expectation
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.PositiveMoment.Lemmas.PredictableLineage
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.PositiveMoment.Closure
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.StoppingSubtrees.Vector.Expectation
import MeasureTheory.Integral.UpperTailOrder
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.PositiveMoment.FirstMoment
import Mathlib.MeasureTheory.Function.L2Space
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.Lemmas.FailureExpectation
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Success
import Combinatorics.UlamHarris.Order
import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Basic

/-!
# Second moment of the restart endpoint

## Internal proof declarations

* `restartEndpoint_memLp_two_and_eLpNorm_le`: for the first-split selector
  and the bounded growth selector, the real endpoint on the original stopped
  roots is in $L^2$ and satisfies $\|M_H^{\mathrm b}\|_2\le CH$ for $H\ge1$.
* `tendsto_restartEndpoint_badIntegral_div_log`: if $H_N/\log^3 N\to t$ and
  $P(E_N^c)\le N^{-b}$, then $\mathbb E[M_{H_N}^{\mathrm b}\mathbf1_{E_N^c}]=o(\log N)$.
* `integral_firstNSelectedEndpointMinimum_le_restart_terms`: if the mean
  of every centered continuation is at most $b$, then the actual endpoint
  mean is bounded by the entrance mean on $E$, $P(E)b$ and the bad-event integral.

This is the second-moment estimate in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 4, Theorem 1.2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

open Combinatorics.Branching Combinatorics.UlamHarris
open Combinatorics.Branching.Step.FiniteSelection
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
open SelectedPath.Completion.Lemmas SelectedPath.GrowthTrial.Lemmas
open ProbabilityTheory.BranchingRandomWalk.Coupling

local notation "Ωf" => RootIndexed.StepField (ℕ ⊕ ℕ) ℕ ℝ
local notation "𝔽" => RootIndexed.stepFiltration (Root := ℕ ⊕ ℕ) (α := ℕ) (X := ℝ)

private lemma eLpNorm_two_eq_ofReal_sqrt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : MemLp X 2 P) :
    eLpNorm X 2 P = ENNReal.ofReal (Real.sqrt (∫ ω, (X ω) ^ 2 ∂P)) := by
  have hnormSq : (∫ ω, ‖X ω‖ ^ (2 : ℝ) ∂P) = ∫ ω, (X ω) ^ 2 ∂P := by
    apply integral_congr_ae
    filter_upwards with ω
    simp [Real.norm_eq_abs]
  rw [hX.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    show ENNReal.toReal (2 : ℝ≥0∞) = 2 by norm_num, hnormSq,
    Real.sqrt_eq_rpow, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]

private lemma square_of_fourthMoment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEStronglyMeasurable X P) (h4 : Integrable (fun ω => (X ω) ^ 4) P) :
    Integrable (fun ω => (X ω) ^ 2) P ∧
      (∫ ω, (X ω) ^ 2 ∂P) ≤ 1 + ∫ ω, (X ω) ^ 4 ∂P := by
  have hle (ω : Ω) : (X ω) ^ 2 ≤ 1 + (X ω) ^ 4 := by
    nlinarith [sq_nonneg ((X ω) ^ 2 - 1)]
  have hdom := (integrable_const (1 : ℝ)).add h4
  have hint : Integrable (fun ω => (X ω) ^ 2) P := hdom.mono' (hX.pow 2) <|
    ae_of_all P fun ω => by
      change ‖(X ω) ^ 2‖ ≤ 1 + (X ω) ^ 4
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X ω))]
      exact hle ω
  refine ⟨hint, (integral_mono hint hdom hle).trans_eq ?_⟩
  simp [integral_add (integrable_const (1 : ℝ)) h4]

private lemma stoppedPositive_secondMoment
    {m N H : ℕ} [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hnorm : HasBoundaryNormalization L.potential L.raw)
    (hne : L.raw nonemptySupport = 1) (hfour : HasLeftmostFourthMoment L)
    (hm : 0 < m) (hN : 0 < N) (hH : 0 < H)
    (τ : Ωf → WithTop ℕ) (hτ : IsStoppingTime 𝔽 τ)
    (roots : Ωf → Fin m → RootIndexed.TreeNode (ℕ ⊕ ℕ) ℕ)
    (hfiber : ∀ v, MeasurableSet[hτ.measurableSpace] {ω | roots ω = v})
    (hdepth : ∀ ω (n : ℕ), τ ω = n → ∀ i, (roots ω i).2.length = n)
    (hinj : ∀ ω, τ ω ≠ ⊤ → Function.Injective (roots ω)) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ ⊕ ℕ) L.sortedPotentialImage
    let Y (ω : Ωf) := if τ ω ≤ (H : WithTop ℕ) then
      max (firstNSelectedEndpointMinimum m N (H - (τ ω).untopD 0)
        (RootIndexed.selectedSubtreeStepFieldVector roots ω)) 0 else 0
    let Q := ∫ ξ, (L.leftmostPositivePart ξ) ^ 4 ∂L.raw
    MemLp Y 2 P ∧
      (∫ ω, (Y ω) ^ 2 ∂P) ≤ (H : ℝ) ^ 2 * (1 + Q) := by
  intro P Y Q
  let g (i : ℕ) (f : RootIndexed.StepField (Fin m) ℕ ℝ) :=
    (max (firstNSelectedEndpointMinimum m N (H - i) f) 0) ^ 2
  have hg (i : ℕ) : Measurable (g i) :=
    ((measurable_firstNSelectedEndpointMinimum m N (H - i)).max measurable_const).pow_const 2
  have hQ : 0 ≤ Q := integral_nonneg fun _ => by positivity
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  have htest (i : ℕ) : Integrable (g i) (RootIndexed.stepFieldLaw L.sortedPotentialImage) ∧
      (∫ f, g i f ∂RootIndexed.stepFieldLaw L.sortedPotentialImage) ≤ (H : ℝ)^2 * (1 + Q) := by
    let X f := max (firstNSelectedEndpointMinimum m N (H - i) f) 0
    let c := (H : ℝ)
    obtain ⟨h4, h4b⟩ := finiteRootStepFieldLaw_integrable_pow_four_max_firstNSelectedEndpointMinimum_pos
      m N (H - i) hm hN L hnorm hne hfour
    have he (f : RootIndexed.StepField (Fin m) ℕ ℝ) : g i f ≤ c ^ 2 + (X f) ^ 4 / c ^ 2 := by
      have hc : 0 < c ^ 2 := sq_pos_of_pos hHr
      rw [add_div_eq_mul_add_div _ _ hc.ne']
      apply (le_div_iff₀ hc).2
      change (X f) ^ 2 * c ^ 2 ≤ _
      nlinarith [sq_nonneg ((X f) ^ 2 - c ^ 2)]
    have h4d : Integrable (fun f => (X f) ^ 4) (RootIndexed.stepFieldLaw L.sortedPotentialImage) := h4
    have hd : Integrable (fun f => c ^ 2 + (X f) ^ 4 / c ^ 2)
        (RootIndexed.stepFieldLaw L.sortedPotentialImage) :=
      (integrable_const (c ^ 2)).add (h4d.div_const (c ^ 2))
    have hi : Integrable (g i) (RootIndexed.stepFieldLaw L.sortedPotentialImage) := hd.mono'
      (hg i).aestronglyMeasurable (ae_of_all _ fun f => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ g i f from sq_nonneg _)] using he f)
    refine ⟨hi, (integral_mono hi hd he).trans ?_⟩
    rw [integral_add (integrable_const (c ^ 2)) (h4d.div_const (c ^ 2)), integral_const,
      probReal_univ, smul_eq_mul, one_mul, integral_div]
    have hb : (∫ f, (X f)^4 ∂RootIndexed.stepFieldLaw L.sortedPotentialImage) ≤ c ^ 4 * Q :=
      h4b.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (by dsimp [c]; exact_mod_cast Nat.sub_le H i) 4) hQ)
    calc
      _ ≤ c ^ 2 + (c ^ 4 * Q) / c ^ 2 :=
        add_le_add le_rfl (div_le_div_of_nonneg_right hb (sq_nonneg _))
      _ = _ := by dsimp [c]; field_simp
  let A := {ω | τ ω ≤ (H : WithTop ℕ)}
  have hA : MeasurableSet A := (𝔽).le H _ (hτ.measurableSet_le H)
  obtain ⟨hi, hb⟩ := RootIndexed.integral_stopped_selectedSubtreeStepFieldVector_le
    L.sortedPotentialImage τ hτ roots (Set.to_countable _) hfiber hdepth hinj
    Set.univ MeasurableSet.univ H g hg
    (fun i _ => (htest i).1) _ (fun i _ => (htest i).2)
  have heq : (fun ω => (Y ω)^2) =
      A.indicator (fun ω => g ((τ ω).untopD 0) (RootIndexed.selectedSubtreeStepFieldVector roots ω)) := by
    funext ω
    by_cases ht : τ ω ≤ (H : WithTop ℕ) <;> simp [Y, A, ht, g]
  have hYi : Integrable (fun ω => (Y ω)^2) P := by
    rw [heq, integrable_indicator_iff hA]
    simpa only [Set.univ_inter, A] using hi
  have hn (ω : Ωf) : 0 ≤ Y ω := by dsimp [Y]; split <;> positivity
  have hYm : AEStronglyMeasurable Y P := by
    have he : Y = fun ω => Real.sqrt ((Y ω) ^ 2) := by
      funext ω
      exact (Real.sqrt_sq (hn ω)).symm
    rw [he]
    exact (Real.continuous_sqrt.measurable.comp_aemeasurable hYi.aemeasurable).aestronglyMeasurable
  refine ⟨(memLp_two_iff_integrable_sq hYm).2 hYi, ?_⟩
  rw [heq, integral_indicator hA]
  simp only [Set.univ_inter] at hb
  exact hb.trans (mul_le_of_le_one_left (by positivity) measureReal_le_one)

private lemma firstTwo_positive_memLp
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hfour : HasLeftmostFourthMoment L) :
    let B := firstNBySlotOrder (α := ℕ) (X := ℝ) 2
    MemLp (firstSelectedSlotPositivePotential B realPotential) 2 L.sortedPotentialImage := by
  intro B
  let μ := L.sortedPotentialImage
  have hordered : μ orderedSteps = 1 := by
    rw [show orderedSteps = orderedBySteps realPotential by
      ext ξ
      simp [orderedBySteps, Step.IsOrderedBy, realPotential]]
    rw [L.sortedPotentialImage_orderedBy]
    simp
  have heq : firstSelectedSlotPositivePotential B realPotential =ᵐ[μ]
      fun ξ => max (value' ξ 0) 0 := by
    filter_upwards [(ae_mem_iff_measure_eq orderedSteps_measurable.nullMeasurableSet).2
      (hordered.trans measure_univ.symm)] with ξ hξ
    have hzero : firstSelectedSlot B ξ = 0 := by
      by_cases hne : (B ξ).Nonempty
      · obtain ⟨j, hj⟩ := hne
        have hspec := firstNBySlotOrder_spec (α := ℕ) (X := ℝ) 2 ξ
        have hs : survive ξ 0 :=
          orderedSteps_survive_of_le ξ hξ (Nat.zero_le j) (hspec.subset hj)
        have hmem : 0 ∈ B ξ := by
          by_cases hj0 : j = 0
          · simpa [hj0] using hj
          · exact hspec.lower j hj 0 hs (Prod.Lex.left _ _ (Nat.pos_of_ne_zero hj0))
        rw [firstSelectedSlot, dite_eq_left (show (B ξ).Nonempty from ⟨j, hj⟩)]
        exact Nat.le_zero.mp (Finset.min'_le _ _ hmem)
      · simp [firstSelectedSlot, hne]
    simp [firstSelectedSlotPositivePotential, hzero, realPotential, max_comm,
      Step.potentialValue', Step.potentialAt?, value']
  have hm : Measurable (fun ξ : Step ℕ ℝ => max (value' ξ 0) 0) :=
    (value'_measurable (0 : ℕ)).max measurable_const
  have hint := square_of_fourthMoment hm.aestronglyMeasurable
    (integrable_sortedPotentialImage_positiveSlotZero_pow_four L hfour)
  have hb : MemLp (fun ξ : Step ℕ ℝ => max (value' ξ 0) 0) 2 μ :=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hint.1
  have hmark := firstSelectedSlotPositivePotential_measurable B
    (firstTwoBySlotOrder_measurable (X := ℝ)) realPotential
  exact MemLp.congr_norm hb hmark.aestronglyMeasurable (heq.mono fun _ h => congrArg norm h.symm)

set_option maxHeartbeats 1000000 in
lemma restartEndpoint_memLp_two_and_eLpNorm_le
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hnorm : HasBoundaryNormalization L.potential L.raw)
    (hne : L.raw nonemptySupport = 1) (hfour : HasLeftmostFourthMoment L)
    (M : ℝ) (hM : 0 ≤ M) :
    let μ := L.sortedPotentialImage
    let P := RootIndexed.stepFieldLaw (Root := ℕ ⊕ ℕ) μ
    let B := firstNBySlotOrder (α := ℕ) (X := ℝ) 2
    let R := firstOrBelowPotential B realPotential M
    let growth := B.belowPotential realPotential M
    let hB := firstTwoBySlotOrder_measurable (X := ℝ)
    let hR := firstOrBelowPotential_measurable B hB realPotential M
    let hgrowth := B.belowPotential_measurable hB realPotential M
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)],
      ∀ (N lower upper duration H : ℕ),
      0 < N → 0 < m → 0 < H →
      ∀ (roots : Ωf → Fin m → RootIndexed.TreeNode (ℕ ⊕ ℕ) ℕ),
        let τ := SelectedPath.Completion.time R growth hR hgrowth lower upper duration (0 : ℕ)
        let hτ := SelectedPath.Completion.time_isStoppingTime R growth hR hgrowth lower upper duration (0 : ℕ)
        let F := trialRestartEndpoint N R growth hR hgrowth lower upper duration 0 H roots
        (∀ v, MeasurableSet[hτ.measurableSpace] {ω | roots ω = v}) →
        (∀ ω (n : ℕ), τ ω = n → ∀ i, (roots ω i).2.length = n) →
        (∀ ω, τ ω ≠ ⊤ → Function.Injective (roots ω)) →
        (let order := RootIndexed.addressLinearOrder (Fin 1) ℕ
          ∀ x : ℝ, (RootIndexed.stepFieldLaw (Root := Fin 1) μ)
            {ω | x ≤ @firstNSelectedEndpointMinimum 1 N H order ω} ≤ P {ω | x ≤ F ω}) →
        MemLp F 2 P ∧ eLpNorm F 2 P ≤ ENNReal.ofReal (C * (H : ℝ)) := by
  intro μ P B R growth hB hR hgrowth
  let mark := firstSelectedSlotPositivePotential B realPotential
  let a := (eLpNorm mark 2 μ).toReal
  let Q := ∫ ξ, (L.leftmostPositivePart ξ)^4 ∂L.raw
  let C := M + a + Real.sqrt (1 + Q) + Real.sqrt 2049
  have hmark : MemLp mark 2 μ := firstTwo_positive_memLp L hfour
  have hC : 0 ≤ C := by dsimp [C, a]; positivity
  refine ⟨C, hC, ?_⟩
  intro m orderM N lower upper duration H hN hm hH roots τ hτ F hfiber hdepth hinj horder
  have hF := measurable_trialRestartEndpoint N R growth hR hgrowth lower upper duration 0 H roots hfiber
  have hμne : μ nonemptySupport = 1 := by
    change L.sortedPotentialImage nonemptySupport = 1
    rwa [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport]
  have hμnorm := L.sortedPotentialImage_hasBoundaryNormalization hnorm
  let Z := fun ω => max (-F ω) 0
  have hZm : Measurable Z := hF.neg.max measurable_const
  have hneg := lintegral_exp_neg_trialRestartEndpoint_le μ hμnorm hμne N hN H F hF horder
  obtain ⟨hZ4, hz⟩ := integrable_pow_four_max_neg_of_lintegral_exp_neg_le P F hF
    (le_refl (1 : ℝ)) hneg
  obtain ⟨hZ2, hz2⟩ := square_of_fourthMoment hZm.aestronglyMeasurable hZ4
  have hZ : MemLp Z 2 P := (memLp_two_iff_integrable_sq hZm.aestronglyMeasurable).2 hZ2
  have hZb : eLpNorm Z 2 P ≤ ENNReal.ofReal (Real.sqrt 2049) := by
    rw [eLpNorm_two_eq_ofReal_sqrt hZ]
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hz2.trans (by norm_num at hz ⊢; linarith)))
  let Y : Ωf → ℝ := fun ω => if τ ω ≤ (H : WithTop ℕ) then
    max (firstNSelectedEndpointMinimum m N (H - (τ ω).untopD 0)
      (RootIndexed.selectedSubtreeStepFieldVector roots ω)) 0 else 0
  obtain ⟨hY, hY2⟩ := stoppedPositive_secondMoment L hnorm hne hfour hm hN hH
    τ hτ roots hfiber hdepth hinj
  have hYb : eLpNorm Y 2 P ≤ ENNReal.ofReal ((H : ℝ) * Real.sqrt (1 + Q)) := by
    rw [eLpNorm_two_eq_ofReal_sqrt hY, ← Real.sqrt_sq (Nat.cast_nonneg H),
      ← Real.sqrt_mul (sq_nonneg (H : ℝ))]
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hY2)
  let left : Ωf → RootIndexed.StepField ℕ ℕ ℝ := RootIndexed.StepField.left
  let Pleft := RootIndexed.stepFieldLaw (Root := ℕ) μ
  let Xleft : RootIndexed.StepField ℕ ℕ ℝ → ℝ := fun field =>
    M * (H : ℝ) + ∑ j ∈ Finset.range H, mark (SelectedPath.Coupling.step R 0 j field)
  let X := Xleft ∘ left
  have hleft : Measurable left := measurable_pi_iff.mpr fun i => measurable_pi_apply (Sum.inl i)
  have hleftLaw : P.map left = Pleft := RootIndexed.stepFieldLaw_reindex μ Sum.inl Sum.inl_injective
  have hmarkm : Measurable mark := firstSelectedSlotPositivePotential_measurable B hB realPotential
  have hXm : Measurable Xleft :=
    measurable_const.add (Finset.measurable_sum _ fun j _ =>
      hmarkm.comp (SelectedPath.Coupling.step_measurable R hR 0 j))
  have hmap : eLpNorm X 2 P = eLpNorm Xleft 2 Pleft := by
    rw [← hleftLaw]
    exact (eLpNorm_map_measure hXm.aestronglyMeasurable hleft.aemeasurable).symm
  have hXb : eLpNorm X 2 P ≤ ENNReal.ofReal ((H : ℝ) * (M + a)) := by
    rw [hmap, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
      ENNReal.ofReal_add hM ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hmark.eLpNorm_lt_top.ne]
    exact eLpNorm_cutoff_add_selectedMarkSum_le μ B hB realPotential M hM 0 H hmark
  have hordered : μ (orderedBySteps realPotential) = 1 := by
    change L.sortedPotentialImage (orderedBySteps realPotential) = 1
    rw [L.sortedPotentialImage_orderedBy]
    simp
  have hmarks := RootIndexed.stepFieldLaw_ae_all_of_measure_one (Root := ℕ ⊕ ℕ)
    (orderedBySteps_measurable realPotential) μ hordered
  have hsupport := RootIndexed.stepFieldLaw_ae_all_of_measure_one (Root := ℕ ⊕ ℕ)
    nonemptySupport_measurable μ hμne
  have hpoint : ∀ᵐ ω ∂P, ‖F ω‖ ≤ (X + Y + Z) ω := by
    filter_upwards [hmarks, hsupport] with ω ho hs
    have hcut : ∀ ξ j, j ∈ growth ξ → ξ.potentialValue' realPotential j ≤ M :=
      fun ξ j hj => ((Step.FiniteSelection.mem_filter B _ ξ j).mp hj).2
    have hpos := trialRestartEndpoint_pos_le N B growth (firstNBySlotOrder_isBoundedBy 2)
      hB hgrowth M hM hcut lower upper duration 0 H roots ω
      (fun j => ho _ _) (fun j => firstNBySlotOrder_nonempty_of_support_nonempty (by decide) _ (hs _ _))
    have he : X ω = M * H + ∑ j ∈ Finset.range H,
        mark (left ω 0 (selectedPath R 0 j (left ω))) := by
      rfl
    change ‖F ω‖ ≤ X ω + Y ω + Z ω
    rw [Real.norm_eq_abs, he]
    have hdecomp : |F ω| = max (F ω) 0 + max (-F ω) 0 := by
      by_cases h : 0 ≤ F ω
      · simp [abs_of_nonneg h, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      · have h' := le_of_not_ge h
        simp [abs_of_nonpos h', max_eq_right h', max_eq_left (neg_nonneg.mpr h')]
    rw [hdecomp]
    exact add_le_add hpos le_rfl
  have hbound : eLpNorm F 2 P ≤ eLpNorm (X + Y + Z) 2 P :=
    eLpNorm_mono_ae_real hF.aestronglyMeasurable hpoint
  have hnormBound : eLpNorm F 2 P ≤ ENNReal.ofReal (C * (H : ℝ)) := by
    calc
      _ ≤ eLpNorm (X + Y + Z) 2 P := hbound
      _ ≤ (eLpNorm X 2 P + eLpNorm Y 2 P) + eLpNorm Z 2 P :=
        (eLpNorm_add_le (f := X + Y) (g := Z) (by norm_num)).trans
          (add_le_add (eLpNorm_add_le (f := X) (g := Y) (by norm_num)) le_rfl)
      _ ≤ _ := by
        refine (add_le_add (add_le_add hXb hYb) hZb).trans ?_
        rw [← ENNReal.ofReal_add (by positivity : 0 ≤ (H : ℝ) * (M + a)) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (Real.sqrt_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        have hHr : 1 ≤ (H : ℝ) := by exact_mod_cast hH
        dsimp [C]
        nlinarith [mul_le_mul_of_nonneg_right hHr (Real.sqrt_nonneg 2049)]
  refine ⟨?_, hnormBound⟩
  exact hnormBound.trans_lt ENNReal.ofReal_lt_top

/-- With $H_N/\log^3N\to t$, the exceptional-event contribution of the
restart endpoint divided by $\log N$ tends to zero. -/
lemma tendsto_restartEndpoint_badIntegral_div_log
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (E : ℕ → Set Ω) {N H : ℕ → ℕ}
    (hN : Filter.Tendsto N Filter.atTop Filter.atTop)
    {t C b : ℝ} (ht : 0 < t) (hC : 0 ≤ C) (hb : 0 < b)
    (hH : Filter.Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3)
      Filter.atTop (nhds t))
    (hF : ∀ᶠ n in Filter.atTop, MemLp (F n) 2 P)
    (hnorm : ∀ᶠ n in Filter.atTop, eLpNorm (F n) 2 P ≤ ENNReal.ofReal (C * (H n : ℝ)))
    (hprob : ∀ᶠ n in Filter.atTop, P.real (E n)ᶜ ≤ Real.exp (-b * Real.log (N n : ℝ))) :
    Filter.Tendsto (fun n => (∫ ω in (E n)ᶜ, F n ω ∂P) / Real.log (N n : ℝ))
      Filter.atTop (nhds 0) := by
  have hlog : Filter.Tendsto (fun n => Real.log (N n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  refine tendsto_setIntegral_div_log_of_failure P F (fun n => (E n)ᶜ) hF hN
    (C := C * (t + 1)) (by positivity) hb ?_ hprob
  filter_upwards [hF, hnorm, hlog.eventually_gt_atTop 0,
    hH (gt_mem_nhds (lt_add_of_pos_right t one_pos))] with n hFn hn hl hT
  rw [eLpNorm_two_eq_ofReal_sqrt hFn] at hn
  have hnorm' := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (Nat.cast_nonneg _))).mp hn
  have ht' : (H n : ℝ) ≤ (t + 1) * Real.log (N n : ℝ) ^ 3 :=
    (div_le_iff₀ (pow_pos hl 3)).mp hT.le
  exact hnorm'.trans ((mul_le_mul_of_nonneg_left ht' hC).trans_eq (by ring))

open EndpointDeviation in
/-- Decompose the restart mean into the entrance displacement, the centered
stopped continuation and the exceptional-event integral. -/
lemma integral_firstNSelectedEndpointMinimum_le_restart_terms
    {m : ℕ} [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hnorm : HasBoundaryNormalization L.potential L.raw)
    (hne : L.raw nonemptySupport = 1) (hfour : HasLeftmostFourthMoment L)
    (N H T : ℕ) (hN : 0 < N) (hm : 0 < m) (hTH : T ≤ H)
    (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration : ℕ) (roots : Ωf → Fin m → RootIndexed.TreeNode (ℕ ⊕ ℕ) ℕ) :
    let μ := L.sortedPotentialImage
    let P := RootIndexed.stepFieldLaw (Root := ℕ ⊕ ℕ) μ
    let Q := RootIndexed.stepFieldLaw (Root := Fin 1) μ
    let order := RootIndexed.addressLinearOrder (Fin 1) ℕ
    let G := @firstNSelectedEndpointMinimum 1 N H order
    let τ := SelectedPath.Completion.time R growth hR hgrowth lower upper duration (0 : ℕ)
    let hτ := SelectedPath.Completion.time_isStoppingTime R growth hR hgrowth lower upper duration (0 : ℕ)
    let F := trialRestartEndpoint N R growth hR hgrowth lower upper duration 0 H roots
    let C (ω : Ωf) := trialResetPositionAtGeneration R growth hR upper duration 0
      ((τ ω).untopD 0) (RootIndexed.StepField.left ω)
    (∀ v, MeasurableSet[hτ.measurableSpace] {ω | roots ω = v}) →
    (∀ ω (n : ℕ), τ ω = n → ∀ i, (roots ω i).2.length = n) →
    (∀ ω, τ ω ≠ ⊤ → Function.Injective (roots ω)) →
    (∀ x : ℝ, Q {ω | x ≤ G ω} ≤ P {ω | x ≤ F ω}) →
    MemLp F 2 P →
    ∀ (A : Set Ωf), MeasurableSet[hτ.measurableSpace] A →
    ∀ b : ℝ,
      (∀ i ≤ T, (∫ field, firstNSelectedEndpointMinimum m N (H - i) field
        ∂RootIndexed.stepFieldLaw (Root := Fin m) μ) ≤ b) →
    let E := A ∩ {ω | τ ω ≤ (T : WithTop ℕ)}
    IntegrableOn C E P ∧
    (∫ field, G field ∂Q) ≤ (∫ ω in E, C ω ∂P) + P.real E * b + ∫ ω in Eᶜ, F ω ∂P := by
  intro μ P Q order G τ hτ F C hfiber hdepth hinj horder hF A hA b hb E
  let _ : LinearOrder (RootIndexed.TreeNode (Fin 1) ℕ) := order
  have hFm := measurable_trialRestartEndpoint N R growth hR hgrowth lower upper duration 0 H roots hfiber
  have hGm : Measurable G := measurable_firstNSelectedEndpointMinimum 1 N H
  have hFint : Integrable F P := hF.integrable (by norm_num)
  have hfirst := fourthMoment_implies_firstMoment L hfour
  have hGint : Integrable G Q :=
    finiteRootStepFieldLaw_integrable_firstNSelectedEndpointMinimum 1 N H
      (by decide) hN L hnorm hne hfirst
  have hord := integral_le_of_measure_ge_le hGint hFint hGm hFm horder
  have hE : MeasurableSet E :=
    (hτ.measurableSpace_le _ hA).inter ((𝔽).le T _ (hτ.measurableSet_le T))
  let g (i : ℕ) := firstNSelectedEndpointMinimum m N (H - i)
  let Y ω := g ((τ ω).untopD 0) (RootIndexed.selectedSubtreeStepFieldVector roots ω)
  have hg (i : ℕ) : Measurable (g i) := measurable_firstNSelectedEndpointMinimum m N (H - i)
  have hi (i : ℕ) : Integrable (g i) (RootIndexed.stepFieldLaw (Root := Fin m) μ) :=
    finiteRootStepFieldLaw_integrable_firstNSelectedEndpointMinimum m N (H - i)
      hm hN L hnorm hne hfirst
  obtain ⟨hY, hYmean⟩ := RootIndexed.integral_stopped_selectedSubtreeStepFieldVector_le
    μ τ hτ roots (Set.to_countable _) hfiber hdepth hinj A hA T g hg (fun i _ => hi i) b hb
  have he : ∀ᵐ ω ∂P.restrict E, F ω = C ω + Y ω := by
    filter_upwards [ae_restrict_mem hE] with ω hw
    have hwH : τ ω ≤ (H : WithTop ℕ) := hw.2.trans (WithTop.coe_le_coe.mpr hTH)
    change (if τ ω ≤ (H : WithTop ℕ) then _ else _) = _
    rw [ite_eq_left hwH]
  have hCe : C =ᵐ[P.restrict E] fun ω => F ω - Y ω := he.mono fun ω hw => by linarith
  have hC : IntegrableOn C E P := (hFint.integrableOn.sub hY).congr hCe.symm
  have hsum : (∫ ω in E, F ω ∂P) =
      (∫ ω in E, C ω ∂P) + ∫ ω in E, Y ω ∂P := by
    rw [integral_congr_ae he, integral_add hC hY]
  refine ⟨hC, hord.trans ?_⟩
  rw [← integral_add_compl hE hFint, hsum]
  exact add_le_add (add_le_add le_rfl hYmean) le_rfl

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed
