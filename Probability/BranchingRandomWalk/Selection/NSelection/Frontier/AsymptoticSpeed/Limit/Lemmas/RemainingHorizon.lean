/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.L2Limit
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.StoppingSubtrees.Vector.Expectation
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.TrialRoots

/-!
# Endpoint expectation after a short entrance time

## Internal proof declarations

* `eventually_endpointMean_sub_horizon_le`: for $0<a<1$, if
  $H_N/\log^3N\to t>0$ and $T_N=o(\log^3N)$, then
  $\mathbb E[M_{H_N-i}^{N|a}]/\log N\le-a+\pi^2\sigma^2t/2+\varepsilon$
  simultaneously for $0\le i\le T_N$ eventually.
* `exists_firstSuccessfulTrial_remainingMean_le`: after resetting the
  successful growth trial's descendants, the centered continuation mean on
  $E_N$ is bounded by $P(E_N)(-a+\pi^2\sigma^2t/2+\varepsilon)$
  in units of $\log N$.

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
  exact RootIndexed.integral_stopped_selectedSubtreeStepFieldVector_le μ (τ n) hτ (roots n)
    hcount (hfiber n) (hdepth n) (hinj n) A hA (T n) g hmeas (fun i _ => hint i) _ hmean

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed
