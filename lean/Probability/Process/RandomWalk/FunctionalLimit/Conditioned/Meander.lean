/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.Portmanteau
public import Probability.Process.Brownian.Meander.Corridor
public import Probability.Process.Brownian.Meander.Support

/-!
# Conditioned random-walk limits at a Brownian meander

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_meanderCorridorProbability_ge`:
  if the conditioned path laws $Q_n\circ X_n^{-1}$ converge to a law
  $\mathsf m$ with $t\mapsto7t/(16\sigma)$ in its support, then for
  $0<\rho<1/48$ there exists $q>0$ such that
  $Q_n(X_n\in\mathcal U_{\sigma,\rho})\ge q$ eventually.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_meanderCorridorProbability_ge_of_imhofLaw`:
  the same lower bound when the limiting path law is identified with the
  Imhof transform of the radial law of three independent Brownian paths;
  the support point is proved from that concrete representation.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.normalizedTransitionCorridor`:
  $\{f:0\le f(t)\le 5s/(6\sigma),\
  f(1)\in[5s/(12\sigma),11s/(24\sigma)]\}$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.mem_normalizedTransitionCorridor_of_meanderCorridor`:
  for $|s-1|<\rho$, a nonnegative path in
  $\mathcal U_{\sigma,\rho}$ belongs to that transition corridor.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_normalizedTransitionCorridorProbability_ge`:
  if $s_n\to1$ and conditioned paths are nonnegative almost surely,
  then some $q>0$ satisfies
  $Q_n(X_n\in D_{\sigma,s_n})\ge q$ eventually.

The convergence hypothesis is the Brownian-meander functional limit proved
by Donald L. Iglehart, *Functional Central Limit Theorems for Random Walks
Conditioned to Stay Positive*, Ann. Probab. 2(4) (1974), 608–619,
DOI 10.1214/aop/1176996607, and extended by Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay
Positive*, Ann. Probab. 4(3) (1976), 480–485,
DOI 10.1214/aop/1176996098. Francesco Caravenna and Loïc Chaumont recall
this limit in *Invariance principles for random walks conditioned to stay
positive*, equation (3.3), DOI 10.1214/07-AIHP119. Loïc Chaumont and
R. A. Doney give a later treatment in *Invariance principles for local
times at the maximum of random walks and Lévy processes*, Theorem 6,
DOI 10.1214/09-AOP512. The support hypothesis is the one used by
Wang Yiyang, *Asymptotic speed of the $N$-branching random walk with
infinite offspring*, Chapter 3, Lemma 3.5, Appendix A.2. Both hypotheses
are explicit pending formal constructions of the conditioned limit and
Brownian meander law.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

/-- The Portmanteau consequence of the Iglehart--Bolthausen Brownian-meander
limit, recalled by Caravenna--Chaumont in equation (3.3), and used in
Wang Yiyang, *Asymptotic speed of the
$N$-branching random walk with infinite offspring*, Chapter 3, Lemma 3.5,
Appendix A.2. The distributional convergence and the support of the
Brownian meander law are explicit inputs. -/
theorem exists_eventually_meanderCorridorProbability_ge
    {Ω Ωm : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωm]
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {Pm : Measure Ωm} [IsProbabilityMeasure Pm]
    {X : ℕ → Ω → CadlagPath unitInterval ℝ}
    {M : Ωm → CadlagPath unitInterval ℝ}
    {sigma rho : ℝ} (hsigma : 0 < sigma)
    (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    (hlimit : TendstoInDistribution X atTop M P Pm)
    (hsupport : Skorokhod.straightPath ((7 / 16) / sigma) ∈
      (Pm.map M).support) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      q ≤ (P n).map (X n) (BrownianMeander.openCorridor sigma rho) := by
  have hpositive : 0 < (Pm.map M)
      (BrownianMeander.openCorridor sigma rho) :=
    BrownianMeander.measure_openCorridor_pos_of_straightPath_mem_support
      hsigma hrho hrhoSmall hsupport
  exact hlimit.exists_eventually_measure_map_ge_pos_of_isOpen
    (BrownianMeander.isOpen_openCorridor sigma rho) hpositive

/-- The Imhof representation supplies the support input needed by
Wang Yiyang, *Asymptotic speed of the $N$-branching random walk with
infinite offspring*, Chapter 3, Lemma 3.5, Appendix A.2. If the limiting
conditioned path law agrees with the Imhof transform of a BES(3) path law,
the meander corridor has positive mass and Portmanteau gives an eventual
positive lower bound. The law identification is stated explicitly so that
its proof can be formalized independently from this support argument. -/
theorem exists_eventually_meanderCorridorProbability_ge_of_imhofLaw
    {Ω Ωm ΩB : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωm]
    [MeasurableSpace ΩB]
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {Pm : Measure Ωm} [IsProbabilityMeasure Pm]
    {X : ℕ → Ω → CadlagPath unitInterval ℝ}
    {M : Ωm → CadlagPath unitInterval ℝ}
    {PB : Measure ΩB} [IsProbabilityMeasure PB]
    {W : ℝ≥0 → ΩB → ℝ}
    (hBrownian : IsBrownianReal W PB)
    (hWmeasurable : ∀ t, Measurable (W t))
    {sigma rho : ℝ} (hsigma : 0 < sigma)
    (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    (hlimit : TendstoInDistribution X atTop M P Pm)
    (hImhofLaw : Pm.map M = BrownianMeander.imhofTilt
      (BrownianBessel3.pathLawOfBrownian hBrownian hWmeasurable)) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      q ≤ (P n).map (X n) (BrownianMeander.openCorridor sigma rho) := by
  have hsupport : Skorokhod.straightPath ((7 / 16) / sigma) ∈
      (BrownianMeander.imhofTilt
        (BrownianBessel3.pathLawOfBrownian hBrownian hWmeasurable)).support := by
    change Skorokhod.linearPath ((7 / 16) / sigma) ∈
      (BrownianMeander.imhofTilt
        (BrownianBessel3.pathLawOfBrownian hBrownian hWmeasurable)).support
    exact BrownianMeander.linearPath_mem_imhofTilt_support
      hBrownian hWmeasurable
      (div_nonneg (by norm_num) hsigma.le)
  apply exists_eventually_meanderCorridorProbability_ge
    hsigma hrho hrhoSmall hlimit (by rw [hImhofLaw]; exact hsupport)

/-- The path version of $D_{N,\Delta}^{\theta}$ after normalizing the walk by
$\sigma\sqrt N$ and writing $s=\Delta/\sqrt N$. This is the transition
event in Wang Yiyang, *Asymptotic speed of the $N$-branching random walk
with infinite offspring*, Chapter 3, Lemma 3.5, Appendix A.2. -/
def normalizedTransitionCorridor (sigma scale : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  Skorokhod.rangeInClosedIntervalEndsIn
    0 ((5 / 6 * scale) / sigma)
      ((5 / 12 * scale) / sigma) ((11 / 24 * scale) / sigma)

/-- The fixed meander open set fits inside the normalized transition event
when $\Delta/\sqrt N$ is within $\rho$ of one and the conditioned path is
nonnegative. This is the margin comparison in Wang Yiyang, Chapter 3,
Lemma 3.5, Appendix A.2. -/
theorem mem_normalizedTransitionCorridor_of_meanderCorridor
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
an eventual positive probability for the finite-width transition corridor.
The convergence input is the Iglehart--Bolthausen Brownian-meander limit,
recalled by Caravenna--Chaumont in equation (3.3); the support input is used
by Wang Yiyang, *Asymptotic speed of the $N$-branching random walk with
infinite offspring*, Chapter 3, Lemma 3.5, Appendix A.2.
The scale input represents $\Delta/\sqrt{n_\Delta-m}\to1$. -/
theorem exists_eventually_normalizedTransitionCorridorProbability_ge
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

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
