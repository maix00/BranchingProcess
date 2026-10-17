/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Moments.Real
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.EndpointEvent
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Reflection
public import Probability.Sequence.IID.Basic
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Setup.Binning
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Binning.Geometry
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Binning.Parameters
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Concrete.Uniform

/-!
# Finite-variance tilted-tube endpoint bounds

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.exists_uniform_driftedTube_endpoint_bounds`: if the increment law has
  mean zero and variance $\sigma^2>0$, $v>0$, $c\ge0$,
  $\varepsilon>0$, and $d'>\pi^2\sigma^2/2$, one width threshold
  gives $e^{-d'L/\Delta^2}\le\mathbb P(A^-_{L,\Delta})$ and
  $e^{-d'L/\Delta^2}\le\mathbb P(A^+_{L,\Delta})$ for every admissible
  initial boundary and horizon $L\ge\lfloor\Delta^{2+\varepsilon}\rfloor$.
  For increments $\xi=(\xi_i)_{i\ge0}$, write
  $Y_j=\sum_{i=0}^{j-1}\xi_i$ and $R_j=r+\mu j/\Delta^2$. These events are
  $A^-_{L,\Delta}=\{R_j\le Y_j\le R_j+\Delta\ (1\le j\le L),\;
  Y_L\in[R_L,R_L+v\Delta]\}$ and
  $A^+_{L,\Delta}=\{R_j\le Y_j\le R_j+\Delta\ (1\le j\le L),\;
  Y_L\in[R_L+(1-v)\Delta,R_L+\Delta]\}$.

This is Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5. Its parameter selection follows
that proof: first choose an intermediate exponential rate, then a finite bin
count, strict window margins, and an intermediate power block length. The
block-rate input is Chapter 3, Lemma 3.1(ii), based on Theorem 3, Section 4,
p. 764 of A. A. Mogul'skii, “Small deviations in the sample function space,”
*Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English
translation, “Small Deviations in a Space of Trajectories,” *Theory of
Probability and Its Applications* 19(1) (1975), 726--736, DOI 10.1137/1119081.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The two endpoint conclusions in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5, share
one real-width threshold uniform in the horizon and initial tube position. -/
theorem exists_uniform_driftedTube_endpoint_bounds
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma v d drift epsilon : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (hv : 0 < v)
    (hrate : (Real.pi ^ 2 / 2) * sigma ^ 2 < d)
    (hdrift : 0 ≤ drift)
    (hepsilon : 0 < epsilon) :
    ∃ threshold : ℝ, 0 < threshold ∧
      ∀ width ≥ threshold, ∀ horizon : ℕ, ∀ base : ℝ,
      Nat.floor (width ^ (2 + epsilon)) ≤ horizon →
      base ≤ 0 → 0 ≤ base + width →
      Real.exp (-d * (horizon : ℝ) / width ^ 2) ≤
        (iidSequenceLaw ν).real
          (driftedTubeEndpointWindowEvent horizon width drift base v) ∧
      Real.exp (-d * (horizon : ℝ) / width ^ 2) ≤
        (iidSequenceLaw ν).real
          (driftedTubeUpperEndpointWindowEvent horizon width drift base v) := by
  let criticalRate : ℝ := (Real.pi ^ 2 / 2) * sigma ^ 2
  let blockRate : ℝ := (criticalRate + d) / 2
  have hcriticalNonneg : 0 ≤ criticalRate := by
    dsimp [criticalRate]
    positivity
  have hblockCritical : criticalRate < blockRate := by
    dsimp [blockRate, criticalRate]
    linarith
  have hblockNonneg : 0 ≤ blockRate :=
    hcriticalNonneg.trans hblockCritical.le
  have hdelta : 0 < d - blockRate := by
    dsimp [blockRate, criticalRate]
    linarith
  obtain ⟨m, hm, hmRate, hmV⟩ :=
    exists_staircase_bin_count hblockCritical hv
  change criticalRate < blockRate * staircaseBinWidth m ^ 2 at hmRate
  let narrowedRate : ℝ :=
    (criticalRate + blockRate * staircaseBinWidth m ^ 2) / 2
  have hnarrowedK : criticalRate < narrowedRate := by
    dsimp [narrowedRate]
    linarith
  have hnarrowedBlock :
      narrowedRate < blockRate * staircaseBinWidth m ^ 2 := by
    dsimp [narrowedRate]
    linarith
  obtain ⟨margin, uInterior, vInterior, uLower, vLower,
    uUpper, vUpper, hmargin, huInterior, huvInterior, hvInterior,
    huLower, huvLower, hvLower, huUpper, huvUpper, hvUpper,
    hinteriorLower, hinteriorUpper, hlowerLower, hlowerUpper,
    hupperLower, hupperUpper⟩ :=
    exists_staircase_geometric_margins hm hmV
  let eta : ℝ := min epsilon 1 / 2
  have heta : 0 < eta := by
    dsimp [eta]
    exact div_pos (lt_min hepsilon (by norm_num)) (by norm_num)
  have hetaOne : eta < 1 := by
    dsimp [eta]
    have h := min_le_right epsilon 1
    linarith
  have hetaEpsilon : eta < epsilon := by
    dsimp [eta]
    have h := min_le_left epsilon 1
    have hpos := lt_min hepsilon (by norm_num : (0 : ℝ) < 1)
    linarith
  have hupperFinal : vUpper + margin ≤
      (1 - 1 / (3 * (m : ℝ))) / staircaseBinWidth m := by
    have hratio : (1 - 1 / (3 * (m : ℝ))) /
        staircaseBinWidth m = 1 := by
      change staircaseBinWidth m / staircaseBinWidth m = 1
      exact div_self (ne_of_gt (staircaseBinWidth_pos hm))
    rw [hratio]
    exact hupperUpper
  obtain ⟨threshold, hthreshold⟩ :=
    exists_uniform_concreteStaircase_bounds_of_powerBlock
    hν hsigma m hm huInterior huvInterior hvInterior huLower huvLower hvLower
    huUpper huvUpper hvUpper hnarrowedK heta hetaOne hetaEpsilon
    hmargin hdrift (by exact le_of_lt hv) hblockNonneg
    hepsilon hdelta hnarrowedBlock
    hinteriorLower hinteriorUpper hlowerLower hlowerUpper
    hupperLower hupperFinal
  refine ⟨max 1 threshold,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left 1 threshold), ?_⟩
  intro width hwidth horizon base hhorizon hbase hbaseWidth
  have hstart : -base ∈ Set.Icc 0 width := by
    constructor <;> linarith
  exact hthreshold width ((le_max_right 1 threshold).trans hwidth)
    horizon base hhorizon hstart

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
