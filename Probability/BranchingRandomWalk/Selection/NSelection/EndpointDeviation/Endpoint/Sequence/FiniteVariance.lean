/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Basic
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.Parameters
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.Sublevel
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Minimum.CountableRoots
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Theorems

/-!
# Polynomial endpoint tails under finite variance

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.eventually_finiteRootStepFieldLaw_firstNSelectedEndpointBelow_le_polynomial_of_centeredFiniteVariance`:
  if $H_n/\log^3 N_n\to t$, $z_n/\log N_n\to\zeta$, and
  $\zeta<-a+\frac{\pi^2}{2}\sigma^2t$, then for $m_n\le N_n^a$ the event
  $E_n=\{\exists p\in\mathcal S_{m_n,N_n,H_n}:X(p)\le z_n\}$ satisfies
  \[
    \mathbb P(E_n)\le N_n^{-\varepsilon}
  \]
  eventually for some $\varepsilon>0$, where $\mathcal S_{m,N,H}$ is the
  generation-$H$ first-$N$ population from $m$ roots and $X(p)$ is the
  position of $p$. The estimate assumes boundary normalization and a centered
  finite-variance tilted-spine law.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.eventually_countableRootEndpointMinimum_le_polynomial_of_centeredFiniteVariance`:
  transfers the same bound to the common countable-root environment when
  offspring are nonempty almost surely and $m_n>0$ eventually.

This is the finite-variance specialization of the finite-horizon endpoint
decomposition in Elie Aïdékon and Yueyun Hu, *Average-weight percolation on
the complete graph*, Proposition 3.1, equation (4.16) (2025), and Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring*, Chapter 4, equation (4.16) (master's thesis, Fudan University,
2026). The one-walk estimate is Wang Yiyang, Chapter 3, Lemma 3.3.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

private lemma tendsto_log_sampleSize_atTop {N : ℕ → ℕ}
    (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => Real.log (N n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)

private lemma eventually_horizon_ge_scaledWidth_rpow
    {N H : ℕ → ℕ} {t b : ℝ}
    (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3)
      atTop (𝓝 t))
    (ht : 0 < t) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop,
      (b * Real.log (N n : ℝ)) ^ ((5 : ℝ) / 2) ≤ (H n : ℝ) := by
  let L : ℕ → ℝ := fun n => Real.log (N n : ℝ)
  have hL : Tendsto L atTop atTop := by simpa [L] using tendsto_log_sampleSize_atTop hN
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  have hhalf : Tendsto (fun n => L n ^ ((1 : ℝ) / 2)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)).comp hL
  have hproduct : Tendsto
      (fun n => L n ^ ((1 : ℝ) / 2) *
        ((H n : ℝ) / L n ^ 3)) atTop atTop :=
    hhalf.atTop_mul_pos ht (by simpa [L] using hH)
  have hbpow : 0 < b ^ ((5 : ℝ) / 2) := Real.rpow_pos_of_pos hb _
  have hratio : Tendsto
      (fun n => (b ^ ((5 : ℝ) / 2))⁻¹ *
        (L n ^ ((1 : ℝ) / 2) * ((H n : ℝ) / L n ^ 3))) atTop atTop :=
    hproduct.const_mul_atTop (inv_pos.mpr hbpow)
  have hratioLarge : ∀ᶠ n : ℕ in atTop,
      1 ≤ (b ^ ((5 : ℝ) / 2))⁻¹ *
        (L n ^ ((1 : ℝ) / 2) * ((H n : ℝ) / L n ^ 3)) :=
    hratio.eventually_ge_atTop 1
  filter_upwards [hLpos, hratioLarge] with n hLn hlarge
  have hwidth : (b * L n) ^ ((5 : ℝ) / 2) =
      b ^ ((5 : ℝ) / 2) * L n ^ ((5 : ℝ) / 2) :=
    Real.mul_rpow hb.le hLn.le
  have hpower : L n ^ ((5 : ℝ) / 2) * L n ^ ((1 : ℝ) / 2) =
      L n ^ 3 := by
    rw [← Real.rpow_natCast (L n) 3, ← Real.rpow_add hLn]
    congr 1
    norm_num
  have hlarge' : b ^ ((5 : ℝ) / 2) ≤
      L n ^ ((1 : ℝ) / 2) * ((H n : ℝ) / L n ^ 3) := by
    calc
      b ^ ((5 : ℝ) / 2) = b ^ ((5 : ℝ) / 2) * 1 := by ring
      _ ≤ b ^ ((5 : ℝ) / 2) *
          ((b ^ ((5 : ℝ) / 2))⁻¹ *
            (L n ^ ((1 : ℝ) / 2) * ((H n : ℝ) / L n ^ 3))) :=
        mul_le_mul_of_nonneg_left hlarge hbpow.le
      _ = L n ^ ((1 : ℝ) / 2) * ((H n : ℝ) / L n ^ 3) := by
        field_simp [ne_of_gt hbpow]
  have hHlower : b ^ ((5 : ℝ) / 2) * L n ^ ((5 : ℝ) / 2) ≤
      (H n : ℝ) := by
    have hpos : 0 < L n ^ ((5 : ℝ) / 2) := Real.rpow_pos_of_pos hLn _
    have hmul := mul_le_mul_of_nonneg_right hlarge' hpos.le
    have heq :
        (L n ^ ((1 : ℝ) / 2) * ((H n : ℝ) / L n ^ 3)) *
            L n ^ ((5 : ℝ) / 2) = (H n : ℝ) := by
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hLn 3)]
      rw [← hpower]
      ring
    calc
      b ^ ((5 : ℝ) / 2) * L n ^ ((5 : ℝ) / 2) ≤
          (L n ^ ((1 : ℝ) / 2) * ((H n : ℝ) / L n ^ 3)) *
            L n ^ ((5 : ℝ) / 2) := hmul
      _ = (H n : ℝ) := heq
  rw [hwidth]
  exact hHlower

/-- A polynomial lower-tail bound for the selected endpoint follows from the
finite-variance drawdown estimate. The parameter choice and exponent conversion
are those of Aïdékon--Hu, Proposition 3.1, equation (4.16). -/
theorem eventually_finiteRootStepFieldLaw_firstNSelectedEndpointBelow_le_polynomial_of_centeredFiniteVariance
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    {sigma a t zeta : ℝ} (hsigma : 0 < sigma)
    (hspine : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    {m N H : ℕ → ℕ} (horder : ∀ n,
      LinearOrder (RootIndexed.TreeNode (Fin (m n)) ℕ))
    (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3)
      atTop (𝓝 t))
    {threshold : ℕ → ℝ}
    (hthreshold : Tendsto (fun n => threshold n / Real.log (N n : ℝ))
      atTop (𝓝 zeta))
    (ht : 0 < t) (ha : 0 ≤ a)
    (hmN : ∀ᶠ n : ℕ in atTop, m n ≤ N n)
    (hma : ∀ᶠ n : ℕ in atTop, (m n : ℝ) ≤ (N n : ℝ) ^ a)
    (hgap : zeta < -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ᶠ n : ℕ in atTop,
      (finiteRootStepFieldLaw μ (m n))
        (@firstNSelectedEndpointBelow (m n) (N n) (H n) (horder n)
          (threshold n)) ≤
        ENNReal.ofReal
          (Real.exp (-epsilon * Real.log (N n : ℝ))) := by
  let C : ℝ := (Real.pi ^ 2 / 2) * sigma ^ 2
  have hgap' : zeta < -a + C * t := by
    dsimp [C]
    nlinarith [hgap]
  obtain ⟨b, d, c, epsilon, hb, hd, hdC, hc, hcHalf,
      hcEndpoint, hepsilon, hepsilonB, hepsilonMargin⟩ :=
    exists_endpoint_deviation_parameters (a := a) (t := t) (C := C)
      (zeta := zeta) ht (by dsimp [C]; positivity) hgap'
  have hrateTarget : 0 < d / sigma ^ 2 := div_pos hd (sq_pos_of_pos hsigma)
  have hrateCritical : d / sigma ^ 2 < Real.pi ^ 2 / 2 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hsigma)).2
    calc
      d < C := hdC
      _ = (Real.pi ^ 2 / 2) * sigma ^ 2 := rfl
  have hmargin : a + zeta < d * t / b ^ 2 := by
    linarith
  have hendpoint : zeta < b / c := by
    have h := hcEndpoint
    linarith
  let L : ℕ → ℝ := fun n => Real.log (N n : ℝ)
  let Delta : ℕ → ℝ := fun n => b * L n
  have hL : Tendsto L atTop atTop := by
    simpa [L] using tendsto_log_sampleSize_atTop hN
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  have hDelta : Tendsto Delta atTop atTop := by
    exact hL.const_mul_atTop (by linarith : 0 < b)
  have hpowerLarge := eventually_horizon_ge_scaledWidth_rpow hN hH ht
    (by linarith : 0 < b)
  obtain ⟨delta0, hdelta0, hdraw⟩ :=
    exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_of_centeredSecondMoment
      ν hspine hsigma c (d / sigma ^ 2) (1 / 2) hc hrateTarget
      hrateCritical (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)
  have hDeltaLarge : ∀ᶠ n : ℕ in atTop, delta0 ≤ Delta n :=
    hDelta.eventually_ge_atTop delta0
  have hthresholdBound : ∀ᶠ n : ℕ in atTop,
      threshold n ≤ Delta n / c := by
    have hscaled := hthreshold.eventually (Iio_mem_nhds hendpoint)
    filter_upwards [hscaled, hLpos] with n hn hLn
    have hmul : threshold n < (b / c) * L n :=
      (div_lt_iff₀ hLn).mp hn
    have heq : (b / c) * L n = Delta n / c := by
      dsimp [Delta]
      ring
    exact le_of_lt (hmul.trans_eq heq)
  have hwalkBound : ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν (noLargeDropEndpointBelowEvent (H n)
        (Delta n) (threshold n)) ≤
        ENNReal.ofReal (Real.exp
          (-d * ((H n : ℝ) / (Delta n) ^ 2))) := by
    filter_upwards [hDeltaLarge, hpowerLarge, hthresholdBound] with n hDlarge hpower hthresholdN
    have hDpos : 0 < Delta n := lt_of_lt_of_le hdelta0 hDlarge
    have hpower' : (Delta n) ^ (2 + (1 : ℝ) / 2) ≤ (H n : ℝ) := by
      change (b * Real.log (N n : ℝ)) ^
        ((2 : ℝ) + (1 : ℝ) / 2) ≤ (H n : ℝ)
      rw [show (2 : ℝ) + (1 : ℝ) / 2 = (5 : ℝ) / 2 by norm_num]
      exact hpower
    have hdrawN := hdraw (Delta n) hDlarge (H n) hpower'
    have hsubset : noLargeDropEndpointBelowEvent (H n) (Delta n)
        (threshold n) ⊆ noLargeDropEndpointBelowEvent (H n) (Delta n)
          (Delta n / c) := by
      intro increment hevent
      exact ⟨hevent.1, hevent.2.trans hthresholdN⟩
    have hrateEq : (-(d / sigma ^ 2) * sigma ^ 2 * (H n : ℝ)) /
        (Delta n) ^ 2 =
          -d * ((H n : ℝ) / (Delta n) ^ 2) := by
      field_simp [ne_of_gt (sq_pos_of_pos hsigma),
        ne_of_gt (sq_pos_of_pos hDpos)]
    calc
      iidSequenceLaw ν (noLargeDropEndpointBelowEvent (H n)
          (Delta n) (threshold n)) ≤
        iidSequenceLaw ν (noLargeDropEndpointBelowEvent (H n)
          (Delta n) (Delta n / c)) := measure_mono hsubset
      _ ≤ ENNReal.ofReal (Real.exp
          (-(d / sigma ^ 2) * sigma ^ 2 * (H n : ℝ) /
            (Delta n) ^ 2)) := hdrawN
      _ = ENNReal.ofReal (Real.exp
          (-d * ((H n : ℝ) / (Delta n) ^ 2))) := by rw [hrateEq]
  have hB : Tendsto (fun n => Delta n / L n) atTop (𝓝 b) := by
    have heq : (fun n => Delta n / L n) =ᶠ[atTop] fun _ => b := by
      filter_upwards [hLpos] with n hn
      simp [Delta, L, hn.ne']
    exact tendsto_const_nhds.congr' heq.symm
  have hfinite : ∀ᶠ n : ℕ in atTop,
      (finiteRootStepFieldLaw μ (m n))
          (@firstNSelectedEndpointBelow (m n) (N n) (H n) (horder n)
            (threshold n)) ≤
        (N n : ℝ≥0∞) *
            (((H n : ℝ≥0∞) + 1) ^ 2 *
              ENNReal.ofReal (Real.exp (-Delta n))) +
          (m n : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp (threshold n)) *
              ENNReal.ofReal (Real.exp
                (-d * ((H n : ℝ) / (Delta n) ^ 2)))) := by
    filter_upwards [hmN, hDeltaLarge, hwalkBound]
      with n hmn hDlarge hwalk
    letI := horder n
    have hDpos : 0 < Delta n := lt_of_lt_of_le hdelta0 hDlarge
    have hbound :=
      measure_firstNSelectedEndpointBelow_le_of_iidSpineBound
        (m n) (N n) (H n) hmn (Delta n) (threshold n) hDpos
        μ hboundary ν hν
        (ENNReal.ofReal (Real.exp
          (-d * ((H n : ℝ) / (Delta n) ^ 2)))) hwalk
    simpa using hbound
  exact eventually_finiteRootStepFieldLaw_firstNSelectedEndpointBelow_le_polynomial_of_finiteHorizonEstimate
    μ horder hN hH hB hthreshold ht hb hma hmargin (by
      simpa [Delta] using hfinite)

/-- Transfer the finite-root endpoint tail to one common countable-root
environment through the law-preserving restriction to the first `m` roots. -/
theorem eventually_countableRootEndpointMinimum_le_polynomial_of_centeredFiniteVariance
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    {sigma a t zeta : ℝ} (hsigma : 0 < sigma)
    (hspine : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    {m N H : ℕ → ℕ} (horder : ∀ n,
      LinearOrder (RootIndexed.TreeNode (Fin (m n)) ℕ))
    (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3)
      atTop (𝓝 t))
    {threshold : ℕ → ℝ}
    (hthreshold : Tendsto (fun n => threshold n / Real.log (N n : ℝ))
      atTop (𝓝 zeta))
    (ht : 0 < t) (ha : 0 ≤ a)
    (hmN : ∀ᶠ n : ℕ in atTop, m n ≤ N n)
    (hmPositive : ∀ᶠ n : ℕ in atTop, 0 < m n)
    (hma : ∀ᶠ n : ℕ in atTop, (m n : ℝ) ≤ (N n : ℝ) ^ a)
    (hgap : zeta < -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ᶠ n : ℕ in atTop,
      (RootIndexed.stepFieldLaw (Root := ℕ) μ)
        {field | countableRootEndpointMinimum (m n) (N n) (H n) field ≤
          threshold n} ≤
        ENNReal.ofReal
          (Real.exp (-epsilon * Real.log (N n : ℝ))) := by
  obtain ⟨epsilon, hepsilon, hfinite⟩ :=
    eventually_finiteRootStepFieldLaw_firstNSelectedEndpointBelow_le_polynomial_of_centeredFiniteVariance
      μ hboundary ν hν hsigma hspine horder hN hH hthreshold ht ha hmN hma hgap
  refine ⟨epsilon, hepsilon, ?_⟩
  have hNpos : ∀ᶠ n : ℕ in atTop, 0 < N n := by
    exact hN.eventually_gt_atTop 0
  filter_upwards [hfinite, hNpos, hmPositive] with n hfiniteN hNn hmNpos
  letI := horder n
  have hminimum :=
    firstNSelectedEndpointMinimum_le_iff_endpointBelow_ae
      (m n) (N n) (H n) hmNpos hNn μ hboundary hnonempty (threshold n)
  have hminMeasure :
      (finiteRootStepFieldLaw μ (m n))
          {field | firstNSelectedEndpointMinimum (m n) (N n) (H n) field ≤
            threshold n} =
        (finiteRootStepFieldLaw μ (m n))
          (@firstNSelectedEndpointBelow (m n) (N n) (H n) (horder n)
            (threshold n)) := by
    have hequiv := hminimum
    apply measure_congr
    filter_upwards [hequiv] with field hfield
    simpa [Set.Iic] using hfield.symm
  have hmap := countableRootEndpointMinimum_map_eq μ (m n) (N n) (H n)
  have hmapMeasure :
      (RootIndexed.stepFieldLaw (Root := ℕ) μ)
          {field | countableRootEndpointMinimum (m n) (N n) (H n) field ≤
            threshold n} =
        (finiteRootStepFieldLaw μ (m n))
          {field | firstNSelectedEndpointMinimum (m n) (N n) (H n) field ≤
            threshold n} := by
    calc
      (RootIndexed.stepFieldLaw (Root := ℕ) μ)
          {field | countableRootEndpointMinimum (m n) (N n) (H n) field ≤
            threshold n} =
        (RootIndexed.stepFieldLaw (Root := ℕ) μ).map
          (countableRootEndpointMinimum (m n) (N n) (H n))
          (Set.Iic (threshold n)) := by
            change (RootIndexed.stepFieldLaw (Root := ℕ) μ)
              ((countableRootEndpointMinimum (m n) (N n) (H n)) ⁻¹'
                Set.Iic (threshold n)) = _
            rw [Measure.map_apply (measurable_countableRootEndpointMinimum
              (m n) (N n) (H n)) measurableSet_Iic]
      _ = (finiteRootStepFieldLaw μ (m n)).map
          (firstNSelectedEndpointMinimum (m n) (N n) (H n))
          (Set.Iic (threshold n)) := by rw [hmap]
      _ = (finiteRootStepFieldLaw μ (m n))
          {field | firstNSelectedEndpointMinimum (m n) (N n) (H n) field ≤
            threshold n} := by
            symm
            change (finiteRootStepFieldLaw μ (m n))
              ((firstNSelectedEndpointMinimum (m n) (N n) (H n)) ⁻¹'
                Set.Iic (threshold n)) = _
            rw [Measure.map_apply (measurable_firstNSelectedEndpointMinimum
              (m n) (N n) (H n)) measurableSet_Iic]
  rw [hmapMeasure, hminMeasure]
  exact hfiniteN

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
