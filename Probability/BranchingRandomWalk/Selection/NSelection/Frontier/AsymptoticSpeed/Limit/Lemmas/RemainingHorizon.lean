/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.L2Limit
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.PositiveMoment.Closure
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.StoppingSubtrees.Vector.Expectation
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.TrialRoots
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.TrialCount

/-!
# Endpoint moments after a successful entrance

## Internal proof declarations

* `eventually_endpointMean_sub_horizon_le`: for $0<a<1$, if
  $H_N/\log^3N\to t>0$ and $T_N=o(\log^3N)$, then
  $\mathbb E[M_{H_N-i}^{N|a}]/\log N\le-a+\pi^2\sigma^2t/2+\varepsilon$
  simultaneously for $0\le i\le T_N$ eventually.
* `exists_firstSuccessfulTrial_remainingMean_le`: after resetting the
  successful growth trial's descendants, the centered continuation mean on
  $E_N$ is bounded by $P(E_N)(-a+\pi^2\sigma^2t/2+\varepsilon)$
  in units of $\log N$.
* `exists_firstSuccessfulTrial_remainingPositive_sq_le`: the positive part
  of the centered reset endpoint has second-moment contribution at most
  $P(\tau\le H)(1+\mathbb E[(\Xi_1)_+^4])H^2$ on $\{\tau\le H\}$.

This is the uniform remaining-horizon use of Theorem 1.1 in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Theorem 1.2.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

open Combinatorics.Branching Combinatorics.UlamHarris
open EndpointDeviation ProbabilityTheory.BranchingRandomWalk.Spine
open SelectedPath SelectedPath.Completion SelectedPath.GrowthTrial SelectedPath.GrowthTrial.Population

lemma eventually_endpointMean_sub_horizon_le
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hsuper : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, inferInstance⟩ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ))
    (hnonempty : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hcross : HasFiniteCrossWeight L.potential L.raw)
    (hfour : HasLeftmostFourthMoment L)
    {sigma a t ε : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (sigma ^ 2))
    (ha : 0 < a) (ha1 : a < 1) (ht : 0 < t) (hε : 0 < ε)
    {N H T : ℕ → ℕ} (hcapacity : ∀ n, 0 < N n)
    (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    (hT : Tendsto (fun n => (T n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 0)) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
    let m n := ⌊(N n : ℝ) ^ a⌋₊
    ∀ᶠ n in atTop, ∀ i ≤ T n,
      (∫ field, @countableRootEndpointMinimum (m n) (N n) (H n - i)
        (RootIndexed.addressLinearOrder (Fin (m n)) ℕ) field / Real.log (N n : ℝ) ∂P) ≤
        -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t + ε := by
  intro P m
  let c := -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t
  let logN := fun n => Real.log (N n : ℝ)
  let M n i := ∫ field, @countableRootEndpointMinimum (m n) (N n) (H n - i)
    (RootIndexed.addressLinearOrder (Fin (m n)) ℕ) field / logN n ∂P
  change ∀ᶠ n in atTop, ∀ i ≤ T n, M n i ≤ c + ε
  by_contra! h
  rw [frequently_atTop] at h
  choose n hn i hi hbad using h
  have hnTop : Tendsto n atTop atTop := tendsto_atTop.2 fun k =>
    (eventually_ge_atTop k).mono fun j hj => hj.trans (hn j)
  have hlog : Tendsto logN atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hTH : ∀ᶠ j in atTop, T j ≤ H j := by
    filter_upwards [hlog.eventually_gt_atTop 0,
      hT.eventually (Iio_mem_nhds (show (0 : ℝ) < t / 2 by positivity)),
      hH.eventually (Ioi_mem_nhds (show t / 2 < t by linarith))] with j hLj hs hh
    exact_mod_cast ((div_lt_div_iff_of_pos_right (pow_pos hLj 3)).mp (hs.trans hh)).le
  have hshort : Tendsto (fun k => (i k : ℝ) / logN (n k) ^ 3) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (hT.comp hnTop)
    · filter_upwards [(hlog.comp hnTop).eventually_gt_atTop 0] with k hk
      positivity
    · filter_upwards [(hlog.comp hnTop).eventually_gt_atTop 0] with k hk
      exact div_le_div_of_nonneg_right (by exact_mod_cast hi k) (pow_pos hk 3).le
  have hremaining :
      Tendsto (fun k => ((H (n k) - i k : ℕ) : ℝ) / logN (n k) ^ 3) atTop (𝓝 t) := by
    have hdiff := (hH.comp hnTop).sub hshort
    rw [sub_zero] at hdiff
    apply hdiff.congr'
    filter_upwards [hnTop.eventually hTH] with k hk
    simp [logN, Nat.cast_sub ((hi k).trans hk), sub_div]
  have hmean : Tendsto (fun k => M (n k) (i k)) atTop (𝓝 c) :=
    tendsto_integral_countableRootEndpointMinimum_div L hsuper hnonempty hboundary
      hcross hfour hsigma hspine ⟨ha.le, ha1.le⟩ ht
      (fun he => (ha.ne' he).elim) (fun k => hcapacity (n k)) (hN.comp hnTop) hremaining
  rw [tendsto_order] at hmean
  obtain ⟨k, hk⟩ := (hmean.2 _ (lt_add_of_pos_right c hε)).exists
  exact (hbad k).not_gt hk

/-- Apply the uniform remaining-horizon mean bound to the zero-position reset
from descendants of the successful trial in Wang Yiyang, Theorem 1.2. -/
lemma exists_firstSuccessfulTrial_remainingMean_le
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hsuper : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, inferInstance⟩ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ))
    (hnonempty : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hcross : HasFiniteCrossWeight L.potential L.raw)
    (hfour : HasLeftmostFourthMoment L)
    {sigma a t ε : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (sigma ^ 2))
    (ha : 0 < a) (ha1 : a < 1) (ht : 0 < t) (hε : 0 < ε)
    {N H T : ℕ → ℕ} (hcapacity : ∀ n, 0 < N n)
    (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    (hT : Tendsto (fun n => (T n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 0))
    (R growth : Step.FiniteSelection ℕ ℝ) (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (upper duration K : ℕ → ℕ) (hupper : ∀ n, 1 ≤ upper n) (r : ℕ) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
    let m n := ⌊(N n : ℝ) ^ a⌋₊
    let lower n := ⌈(N n : ℝ) ^ a⌉₊
    let τ n := firstSuccessfulCompletion R growth hR (lower n) (upper n) (duration n) r
    let E n := {ω | splitCount R r ((τ n ω).untopD 0 - (duration n + 1)) ω < K n} ∩
      {ω | τ n ω ≤ (T n : WithTop ℕ)}
    ∃ roots : ∀ n, RootIndexed.StepField ℕ ℕ ℝ → Fin (m n) → RootIndexed.TreeNode ℕ ℕ,
      (∀ n ω k, τ n ω = ((k + 1 + duration n : ℕ) : WithTop ℕ) →
        ∀ i, roots n ω i ∈ capStoppedCandidate (lineages R hR) R growth (upper n) r
          PUnit.unit (k + 1) (duration n) ω) ∧
      ∀ᶠ n in atTop, (∫ ω in E n,
        @firstNSelectedEndpointMinimum (m n) (N n) (H n - (τ n ω).untopD 0)
          (RootIndexed.addressLinearOrder (Fin (m n)) ℕ)
          (RootIndexed.selectedSubtreeStepFieldVector (roots n) ω) / Real.log (N n : ℝ) ∂P) ≤
        P.real (E n) * (-a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t + ε) := by
  intro P m lower τ E
  choose roots hfiber hdepth hinj hmember using fun n =>
    exists_firstSuccessfulTrialRoots R growth hR hgrowth (m n) (lower n) (upper n) (duration n)
      (Nat.floor_le_ceil _) (hupper n) r
  refine ⟨roots, hmember, ?_⟩
  filter_upwards [eventually_endpointMean_sub_horizon_le L hsuper hnonempty hboundary hcross hfour
    hsigma hspine ha ha1 ht hε hcapacity hN hH hT] with n hn
  let _ := RootIndexed.addressLinearOrder (Fin (m n)) ℕ
  let μ := L.sortedPotentialImage
  let Q := finiteRootStepFieldLaw μ (m n)
  let hτ := firstSuccessfulCompletion_isStoppingTime R growth hR hgrowth (lower n) (upper n) (duration n) r
  let A := {ω | splitCount R r ((τ n ω).untopD 0 - (duration n + 1)) ω < K n}
  let g i (field : FiniteRootStepField (m n) ℕ ℝ) :=
    firstNSelectedEndpointMinimum (m n) (N n) (H n - i) field / Real.log (N n : ℝ)
  have hmeas (i : ℕ) : Measurable (g i) :=
    (measurable_firstNSelectedEndpointMinimum (m n) (N n) (H n - i)).div_const _
  have hone : (1 : ℝ) ≤ N n := by exact_mod_cast hcapacity n
  have hm : 0 < m n := Nat.floor_pos.mpr (Real.one_le_rpow hone ha.le)
  have hint (i : ℕ) : Integrable (g i) Q :=
    (finiteRootStepFieldLaw_integrable_firstNSelectedEndpointMinimum (m n) (N n) (H n - i)
      hm (hcapacity n) L hboundary hnonempty (fourthMoment_implies_firstMoment L hfour)).div_const _
  have hmean (i : ℕ) (hi : i ≤ T n) :
      (∫ field, g i field ∂Q) ≤ -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t + ε := by
    have hpres := RootIndexed.StepField.measurePreserving_first μ (m n)
    have heq : (∫ field, g i (RootIndexed.StepField.first (m n) field) ∂P) =
        ∫ field, g i field ∂Q := hpres.integral_comp_of_integrable (hint i)
    rw [← heq]
    exact hn i hi
  have hA : MeasurableSet[hτ.measurableSpace] A :=
    measurableSet_trialCount_lt_at_completion R growth hR hgrowth (lower n) (upper n)
      (duration n) (K n) r
  have hcount : (Set.range (roots n)).Countable := Set.to_countable _
  exact (RootIndexed.integral_stopped_selectedSubtreeStepFieldVector_le μ (τ n) hτ (roots n)
    hcount (hfiber n) (hdepth n) (hinj n) A hA (T n) g hmeas (fun i _ => hint i) _ hmean).2

/-- Apply the positive endpoint moment bound to the stopped continuation
from the original successful trial, after subtracting the reset position. -/
lemma exists_firstSuccessfulTrial_remainingPositive_sq_le
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1) (hfour : HasLeftmostFourthMoment L)
    (N H m lower upper duration : ℕ) (hN : 0 < N) (hH : 0 < H)
    (hm : 0 < m) (hmLower : m ≤ lower) (hupper : 1 ≤ upper)
    (R growth : Step.FiniteSelection ℕ ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (r : ℕ) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
    let τ := firstSuccessfulCompletion R growth hR lower upper duration r
    ∃ roots : RootIndexed.StepField ℕ ℕ ℝ → Fin m → RootIndexed.TreeNode ℕ ℕ,
      (∀ ω k, τ ω = ((k + 1 + duration : ℕ) : WithTop ℕ) →
        ∀ i, roots ω i ∈ capStoppedCandidate (lineages R hR) R growth upper r
          PUnit.unit (k + 1) duration ω) ∧
      IntegrableOn (fun ω => (max (@firstNSelectedEndpointMinimum m N (H - (τ ω).untopD 0)
        (RootIndexed.addressLinearOrder (Fin m) ℕ)
        (RootIndexed.selectedSubtreeStepFieldVector roots ω)) 0) ^ 2)
        {ω | τ ω ≤ (H : WithTop ℕ)} P ∧
      (∫ ω in {ω | τ ω ≤ (H : WithTop ℕ)},
        (max (@firstNSelectedEndpointMinimum m N (H - (τ ω).untopD 0)
          (RootIndexed.addressLinearOrder (Fin m) ℕ)
          (RootIndexed.selectedSubtreeStepFieldVector roots ω)) 0) ^ 2 ∂P) ≤
        P.real {ω | τ ω ≤ (H : WithTop ℕ)} *
          ((H : ℝ) ^ 2 * (1 + ∫ ξ, (L.leftmostPositivePart ξ) ^ 4 ∂L.raw)) := by
  intro P τ
  obtain ⟨roots, hfiber, hdepth, hinj, hmember⟩ :=
    exists_firstSuccessfulTrialRoots R growth hR hgrowth m lower upper duration hmLower hupper r
  refine ⟨roots, hmember, ?_⟩
  let _ := RootIndexed.addressLinearOrder (Fin m) ℕ
  let μ := L.sortedPotentialImage
  let Q := finiteRootStepFieldLaw μ m
  let hτ := firstSuccessfulCompletion_isStoppingTime R growth hR hgrowth lower upper duration r
  let C := ∫ ξ, (L.leftmostPositivePart ξ) ^ 4 ∂L.raw
  let f i (field : FiniteRootStepField m ℕ ℝ) :=
    max (firstNSelectedEndpointMinimum m N (H - i) field) 0
  let g i (field : FiniteRootStepField m ℕ ℝ) := (f i field) ^ 2
  have hg (i : ℕ) : Measurable (g i) :=
    ((measurable_firstNSelectedEndpointMinimum m N (H - i)).max measurable_const).pow_const 2
  have hC : 0 ≤ C := integral_nonneg fun _ => by positivity
  have hHreal : 0 < (H : ℝ) := by exact_mod_cast hH
  have hpoint (i : ℕ) (field : FiniteRootStepField m ℕ ℝ) :
      g i field ≤ (H : ℝ) ^ 2 + (f i field) ^ 4 / (H : ℝ) ^ 2 := by
    rw [add_div_eq_mul_add_div _ _ (ne_of_gt (sq_pos_of_pos hHreal))]
    apply (le_div_iff₀ (sq_pos_of_pos hHreal)).2
    dsimp [g]
    nlinarith [sq_nonneg ((f i field) ^ 2 - (H : ℝ) ^ 2),
      mul_nonneg (sq_nonneg (f i field)) (sq_nonneg (H : ℝ))]
  have htests (i : ℕ) : Integrable (g i) Q ∧
      (∫ field, g i field ∂Q) ≤ (H : ℝ) ^ 2 * (1 + C) := by
    have h4 := finiteRootStepFieldLaw_integrable_pow_four_max_firstNSelectedEndpointMinimum_pos
      m N (H - i) hm hN L hboundary hnonempty hfour
    have hdom := (integrable_const ((H : ℝ) ^ 2)).add (h4.1.div_const ((H : ℝ) ^ 2))
    change Integrable (fun field => (H : ℝ) ^ 2 + (f i field) ^ 4 / (H : ℝ) ^ 2) Q at hdom
    have hint : Integrable (g i) Q := hdom.mono' (hg i).aestronglyMeasurable <|
      ae_of_all Q fun field => by
        have hnonneg : 0 ≤ g i field := sq_nonneg _
        simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hpoint i field
    refine ⟨hint, (integral_mono hint hdom (hpoint i)).trans ?_⟩
    have h4int : Integrable (fun field => (f i field) ^ 4) Q := h4.1
    rw [integral_add (integrable_const _) (h4int.div_const _), integral_const, probReal_univ,
      smul_eq_mul, one_mul, integral_div]
    have h4bound : (∫ field, (f i field) ^ 4 ∂Q) ≤ (H : ℝ) ^ 4 * C :=
      h4.2.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le H i) 4) hC)
    calc
      _ ≤ (H : ℝ) ^ 2 + ((H : ℝ) ^ 4 * C) / (H : ℝ) ^ 2 :=
        add_le_add_right (div_le_div_of_nonneg_right h4bound (sq_nonneg _)) _
      _ = _ := by field_simp
  have h := RootIndexed.integral_stopped_selectedSubtreeStepFieldVector_le μ τ hτ roots
    (Set.to_countable _) hfiber hdepth hinj Set.univ MeasurableSet.univ H g hg
    (fun i _ => (htests i).1) _ (fun i _ => (htests i).2)
  simpa only [Set.univ_inter] using h

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed
