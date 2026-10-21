/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.Portmanteau
public import Mathlib.MeasureTheory.Measure.Support
public import Probability.Process.Brownian.Meander.Corridor

/-!
# Conditioned random-walk limits at a Brownian meander

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_meanderCorridorProbability_ge`:
  if the conditioned path laws $Q_n\circ X_n^{-1}$ converge to a law
  $\mathsf m$ with $t\mapsto7t/(16\sigma)$ in its support, then for
  $0<\rho<1/48$ there exists $q>0$ such that
  $Q_n(X_n\in\mathcal U_{\sigma,\rho})\ge q$ eventually.

The convergence hypothesis is the Brownian-meander functional limit proved
by Donald L. Iglehart, *Functional Central Limit Theorems for Random Walks
Conditioned to Stay Positive*, Ann. Probab. 2(4) (1974), 608--619,
DOI 10.1214/aop/1176996607, Section 3, theorem (3.4), p. 616, and extended by Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976), 480–485,
DOI 10.1214/aop/1176996098. Francesco Caravenna and Loïc Chaumont recall
this limit in *Invariance principles for random walks conditioned to stay
positive*, equation (3.3), DOI 10.1214/07-AIHP119. Loïc Chaumont and
R. A. Doney give a later treatment in *Invariance principles for local
times at the maximum of random walks and Lévy processes*, Theorem 6,
DOI 10.1214/09-AOP512. The support hypothesis is used in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, Lemma 3.5, and Appendix A.2, Lemma A.7. The limit and its
support are established in the Brownian-meander and conditioned
random-walk modules.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

private lemma BrownianMeander.straightPath_mem_openCorridor
    {sigma rho : ℝ} (hsigma : 0 < sigma) (hrho : 0 < rho)
    (hrhoSmall : rho < 1 / 48) :
    Skorokhod.straightPath ((7 / 16) / sigma) ∈
      BrownianMeander.openCorridor sigma rho := by
  let y : ℝ := (7 / 16) / sigma
  let upper : ℝ := (5 / 6 - rho) / sigma
  have hypos : 0 ≤ y := (div_pos (by norm_num) hsigma).le
  have hyupper : y < upper := by
    dsimp [y, upper]
    exact (div_lt_div_iff_of_pos_right hsigma).2 (by linarith)
  have hleft : (5 / 12 + rho) / sigma < y := by
    dsimp [y]
    exact (div_lt_div_iff_of_pos_right hsigma).2 (by linarith)
  have hright : y < (11 / 24 - rho) / sigma := by
    dsimp [y]
    exact (div_lt_div_iff_of_pos_right hsigma).2 (by linarith)
  change Skorokhod.straightPath y ∈
    Skorokhod.rangeBelowEndsIn upper
      ((5 / 12 + rho) / sigma) ((11 / 24 - rho) / sigma)
  constructor
  · refine ⟨(upper - y) / 2, half_pos (sub_pos.mpr hyupper), fun t => ?_⟩
    have ht : (t : ℝ) ≤ 1 := t.property.2
    have hpath : y * (t : ℝ) ≤ y := by
      nlinarith [mul_nonneg hypos (sub_nonneg.mpr ht)]
    change y * (t : ℝ) ≤ upper - (upper - y) / 2
    linarith
  · simpa [Skorokhod.straightPath] using
      (show y ∈ Set.Ioo ((5 / 12 + rho) / sigma)
        ((11 / 24 - rho) / sigma) from ⟨hleft, hright⟩)

/-- The Portmanteau consequence of Iglehart's *Functional Central Limit
Theorems for Random Walks Conditioned to Stay Positive*, Ann. Probab. 2(4)
(1974), 608--619, DOI 10.1214/aop/1176996607, Section 3, theorem (3.4),
p. 616, and
Bolthausen's *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Theorem 3.2, recalled by Caravenna and
Chaumont in *Invariance principles for random walks conditioned to stay
positive*, equation (3.3). The support input is used in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, Lemma 3.5, and Appendix A.2, Lemma A.7. The distributional
convergence and the support of the Brownian meander law are explicit inputs. -/
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
      (BrownianMeander.openCorridor sigma rho) := by
    exact (Measure.mem_support_iff_forall _).1 hsupport _
      ((BrownianMeander.isOpen_openCorridor sigma rho).mem_nhds
        (BrownianMeander.straightPath_mem_openCorridor
          hsigma hrho hrhoSmall))
  exact hlimit.exists_eventually_measure_map_ge_pos_of_isOpen
    (BrownianMeander.isOpen_openCorridor sigma rho) hpositive

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
