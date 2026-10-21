/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Transition.Event
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.Support
import Probability.Process.Brownian.Meander.Corridor
import Probability.Process.Brownian.Meander.Lemmas.CorridorPositivity
import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Meander.CorridorProbability
/-!
# Positive probabilities for conditioned transition corridors

The public results in this file are:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_normalizedTransitionCorridorProbability_ge`:
  for $D_{\sigma,s}=\{f:\forall t\in[0,1],\ 0\le f(t)\le
  5s/(6\sigma),\ f(1)\in[5s/(12\sigma),11s/(24\sigma)]\}$, if
  $Q_n\circ X_n^{-1}\Rightarrow\mathsf m$, the support of $\mathsf m$
  contains $t\mapsto7t/(16\sigma)$, $X_n\ge0$ almost surely, and
  $s_n\to1$, then some $q>0$ satisfies
  $Q_n(X_n\in D_{\sigma,s_n})\ge q$ eventually.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_interpolatedTransitionConditionalProbability_ge`:
  for the laws $Q_{n+1}$ of the increments conditioned on
  $S_j\ge0$ for $1\le j\le n+1$, the polygonal path limit with support at
  $t\mapsto7t/(16\sigma)$ and $\Delta_n/\sqrt{n+1}\to1$ imply
  $Q_{n+1}(D_{n+1,\Delta_n})\ge q$ eventually for some $q>0$.

These are complete probability estimates for the conditioned-transition
interface, so they live beside its event and transition results rather than
inside a proof-only `Lemmas/` directory. They formalize the transition
probability input in Wang Yiyang, *Asymptotic Speed of the N-Branching Random
Walk with Infinite Offspring*, Appendix A.2, Lemma A.7, used in Chapter 3,
Lemma 3.5. The functional limit input is Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay
Positive*, Ann. Probab. 4(3) (1976), 480--485, DOI
10.1214/aop/1176996098, Theorem 3.2; the limit-law identification is Donald
L. Iglehart, *Functional Central Limit Theorems for Random Walks Conditioned
to Stay Positive*, Ann. Probab. 2(4) (1974), 608--619, DOI
10.1214/aop/1176996607, Section 3, theorem (3.4), p. 616.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

/-- The fixed meander open set fits inside the normalized transition event
when $\Delta/\sqrt N$ is within $\rho$ of one and the conditioned path is
nonnegative. This is the margin comparison in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3,
Lemma 3.5, and Appendix A.2, Lemma A.7. -/
private lemma mem_normalizedTransitionCorridor_of_meanderCorridor
    {sigma rho scale : ℝ} (hsigma : 0 < sigma) (hrho : 0 < rho)
    (hscale : |scale - 1| < rho)
    {path : CadlagPath unitInterval ℝ}
    (hpath : path ∈ BrownianMeander.openCorridor sigma rho)
    (hnonnegative : ∀ t, 0 ≤ path t) :
    path ∈ normalizedTransitionCorridor sigma scale := by
  have hscaleLower : 1 - rho < scale := by
    have h := (abs_lt.mp hscale).1
    linarith
  have hscaleUpper : scale < 1 + rho := by
    have h := (abs_lt.mp hscale).2
    linarith
  have htube : (5 / 6 - rho) / sigma <
      (5 / 6 * scale) / sigma :=
    (div_lt_div_iff_of_pos_right hsigma).2 (by linarith)
  have hendLower : (5 / 12 * scale) / sigma <
      (5 / 12 + rho) / sigma :=
    (div_lt_div_iff_of_pos_right hsigma).2 (by linarith)
  have hendUpper : (11 / 24 - rho) / sigma <
      (11 / 24 * scale) / sigma :=
    (div_lt_div_iff_of_pos_right hsigma).2 (by linarith)
  change Skorokhod.rangeBelow ((5 / 6 - rho) / sigma) path ∧
    path ⊤ ∈ Set.Ioo ((5 / 12 + rho) / sigma)
      ((11 / 24 - rho) / sigma) at hpath
  obtain ⟨⟨margin, hmargin, hupper⟩, hend⟩ := hpath
  change path ∈ Skorokhod.rangeInClosedIntervalEndsIn
    0 ((5 / 6 * scale) / sigma)
      ((5 / 12 * scale) / sigma) ((11 / 24 * scale) / sigma)
  constructor
  · intro t
    exact ⟨hnonnegative t,
      (hupper t).trans ((sub_lt_self _ hmargin).trans htube).le⟩
  · exact ⟨hendLower.le.trans hend.1.le, hend.2.le.trans hendUpper.le⟩

/-- A conditioned random-walk limit with Brownian-meander support gives
an eventual positive probability for the finite-width transition corridor
$D_{\sigma,s}$. The functional limit is Bolthausen, *On a Functional
Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann.
Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098, Theorem 3.2;
Iglehart identifies the limiting law in *Functional Central Limit Theorems
for Random Walks Conditioned to Stay Positive*, Ann. Probab. 2(4) (1974),
608--619, DOI 10.1214/aop/1176996607, Section 3, theorem (3.4), p. 616.
The support input is used in Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5, and Appendix A.2,
Lemma A.7. -/
lemma exists_eventually_normalizedTransitionCorridorProbability_ge
    {Ω Ωm : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωm]
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {Pm : Measure Ωm} [IsProbabilityMeasure Pm]
    {X : ℕ → Ω → CadlagPath unitInterval ℝ}
    {M : Ωm → CadlagPath unitInterval ℝ}
    {sigma rho : ℝ} (hsigma : 0 < sigma)
    (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    (hlimit : TendstoInDistribution X atTop M P Pm)
    (hsupport : Skorokhod.straightPath ((7 / 16) / sigma) ∈
      (Pm.map M).support)
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop (𝓝 1))
    (hnonnegative : ∀ n, ∀ᵐ ω ∂P n, ∀ t, 0 ≤ X n ω t) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      q ≤ (P n).map (X n) (normalizedTransitionCorridor sigma (scale n)) := by
  obtain ⟨q, hq, hevent⟩ :=
    exists_eventually_meanderCorridorProbability_ge
      hsigma hrho hrhoSmall hlimit hsupport
  have hscaleClose : ∀ᶠ n : ℕ in atTop, |scale n - 1| < rho := by
    have h := hscale.eventually (Metric.ball_mem_nhds 1 hrho)
    simpa [Metric.mem_ball, Real.dist_eq] using h
  refine ⟨q, hq, ?_⟩
  filter_upwards [hevent, hscaleClose] with n hn hsn
  have hmono : (P n).map (X n)
      (BrownianMeander.openCorridor sigma rho) ≤
      (P n).map (X n) (normalizedTransitionCorridor sigma (scale n)) := by
    rw [normalizedTransitionCorridor]
    rw [Measure.map_apply_of_aemeasurable (hlimit.forall_aemeasurable n)
        (BrownianMeander.isOpen_openCorridor sigma rho).measurableSet,
      Measure.map_apply_of_aemeasurable (hlimit.forall_aemeasurable n)
        (Skorokhod.isClosed_rangeInClosedIntervalEndsIn _ _ _ _).measurableSet]
    apply measure_mono_ae
    filter_upwards [hnonnegative n] with ω hω hmem
    exact mem_normalizedTransitionCorridor_of_meanderCorridor
      hsigma hrho hsn hmem hω
  exact hn.trans hmono

/-- If the polygonal paths, conditioned on
$S_1,\ldots,S_{n+1}\ge0$, converge to a law with the stated meander support
point and $\Delta_n/\sqrt{n+1}\to1$, then the conditional probability of
$D_{n+1,\Delta_n}$ is bounded below by a positive constant eventually.
This is the transition estimate in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring*, Appendix A.2, Lemma A.7. -/
lemma exists_eventually_interpolatedTransitionConditionalProbability_ge
    {Ωm : Type*} [MeasurableSpace Ωm]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    [∀ n, IsProbabilityMeasure (survivalConditionedLaw ν (n + 1))]
    {Pm : Measure Ωm} [IsProbabilityMeasure Pm]
    {M : Ωm → CadlagPath unitInterval ℝ}
    {sigma rho : ℝ} (hsigma : 0 < sigma)
    (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    (hlimit : TendstoInDistribution
      (fun n increment => normalizedLinearCadlagPathIcc
        (fun j => sigma * Real.sqrt j) (n + 1) increment)
      atTop M (fun n => survivalConditionedLaw ν (n + 1)) Pm)
    (hsupport : Skorokhod.straightPath ((7 / 16) / sigma) ∈
      (Pm.map M).support)
    {width : ℕ → ℝ} (hwidth : ∀ n, 0 ≤ width n)
    (hratio : Tendsto (fun n => width n / Real.sqrt (n + 1))
      atTop (𝓝 1)) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      q ≤ survivalConditionedLaw ν (n + 1)
        (nonnegativeTransitionEvent (n + 1) (width n)) := by
  have hnonnegative (n : ℕ) :
      ∀ᵐ increment ∂survivalConditionedLaw ν (n + 1),
        ∀ t : unitInterval,
          0 ≤ normalizedLinearCadlagPathIcc
            (fun j => sigma * Real.sqrt j) (n + 1) increment t := by
    exact ae_nonnegative_normalizedLinearCadlagPathIcc ν (Nat.succ_pos n)
      (fun j => sigma * Real.sqrt j)
      (mul_pos hsigma
        (Real.sqrt_pos.2 (Nat.cast_pos.mpr (Nat.succ_pos n))))
  obtain ⟨q, hq, hevent⟩ :=
    exists_eventually_normalizedTransitionCorridorProbability_ge
      hsigma hrho hrhoSmall hlimit hsupport hratio hnonnegative
  refine ⟨q, hq, ?_⟩
  filter_upwards [hevent] with n hn
  have hmeas : MeasurableSet
      (normalizedTransitionCorridor sigma
        (width n / Real.sqrt (n + 1))) :=
    (Skorokhod.isClosed_rangeInClosedIntervalEndsIn _ _ _ _).measurableSet
  rw [Measure.map_apply_of_aemeasurable
    (hlimit.forall_aemeasurable n) hmeas] at hn
  have heventEq :
      {increment : ℕ → ℝ |
        normalizedLinearCadlagPathIcc
          (fun j => sigma * Real.sqrt j) (n + 1) increment ∈
        normalizedTransitionCorridor sigma
          (width n / Real.sqrt (n + 1))} =
      nonnegativeTransitionEvent (n + 1) (width n) := by
    ext increment
    simpa only [Set.mem_ofPred_eq, Nat.succ_eq_add_one, Nat.cast_add,
      Nat.cast_one] using
      (mem_nonnegativeTransitionEvent_iff_normalizedInterpolatedTransitionCorridor
        (Nat.succ_pos n) hsigma (hwidth n) increment).symm
  change q ≤ survivalConditionedLaw ν (n + 1)
    {increment : ℕ → ℝ |
      normalizedLinearCadlagPathIcc
        (fun j => sigma * Real.sqrt j) (n + 1) increment ∈
      normalizedTransitionCorridor sigma
        (width n / Real.sqrt (n + 1))} at hn
  rw [heventEq] at hn
  exact hn

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
