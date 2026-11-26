/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.Event
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.SecondMoment.FiniteVariance
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.IndependentRoot
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.EndpointBounds

/-!
# Survival in a critical affine corridor

## Internal proof declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.CriticalCorridor.exists_criticalCorridor_survival_ge`:
  for a boundary-normalized branching random walk with finite cross-child weight
  and centered spine of variance $\sigma^2>0$, write $K=\pi^2\sigma^2/2$.
  In the corridor $[Kj/\Delta^2,Kj/\Delta^2+\Delta]$ with terminal cutoff
  $KN/\Delta^2+u\Delta$, the survival probability is at least
  $\exp(2(K-d_+)N/\Delta^2)/((N+1)\exp(B))$, where
  $B=4\Delta^v+2u\Delta+2(K-d_-)N/\Delta^2+2d_{-}/\Delta^2$,
  $0<d_-<K<d_+$, $u,v,\varepsilon>0$,
  and $N\ge\max(1,\lfloor\Delta^{2+\varepsilon}\rfloor)$ for sufficiently large $\Delta$.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine.CriticalCorridor

open Combinatorics.Branching
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

private lemma endpointWindow_subset_affineCorridor (N : ℕ) (width K u : ℝ)
    (hwidth : 0 ≤ width) :
    driftedTubeEndpointWindowEvent N width K 0 u ⊆
      {z | history N 0 z ∈
        affineCorridorThrough N 0 (K / width ^ 2) width
          (K * (N : ℝ) / width ^ 2 + u * width)} := by
  intro z hz
  refine ⟨?_, ?_⟩
  · intro j
    by_cases hj : j.val = 0
    · have hj' : j = 0 := Fin.ext hj
      subst j
      simpa using hwidth
    · have h := hz.1 j.val (by omega) (by omega)
      simpa [history_apply, div_mul_eq_mul_div] using h
  · simpa [history_apply] using hz.2.2

/-- The finite-horizon Paley--Zygmund estimate in the proof of equation (3.10)
of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (master's thesis, Fudan University, 2026), Chapter 3, Lemma 3.7.
The corridor slope is the critical small-deviation rate divided by the
squared width. -/
lemma exists_criticalCorridor_survival_ge
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ) (hcross : HasFiniteCrossWeight φ μ)
    {sigma u v ε dLower dUpper : ℝ}
    (hcentered : ProbabilityTheory.IsCenteredSecondMoment (tiltedPotentialLaw φ (-1) μ)
      (sigma ^ 2))
    (hsigma : 0 < sigma) (hu : 0 < u) (hv : 0 < v) (hε : 0 < ε)
    (hdLower : 0 < dLower) (hbelow : dLower < (Real.pi ^ 2 / 2) * sigma ^ 2)
    (habove : (Real.pi ^ 2 / 2) * sigma ^ 2 < dUpper) :
    let K := (Real.pi ^ 2 / 2) * sigma ^ 2
    ∃ width₀ : ℝ, 1 ≤ width₀ ∧
      ∀ width ≥ width₀, ∀ N : ℕ, 1 ≤ N → ⌊width ^ (2 + ε)⌋₊ ≤ N →
        ENNReal.ofReal (Real.exp (2 * (K - dUpper) * (N : ℝ) / width ^ 2)) /
            ((N + 1 : ℝ≥0∞) * ENNReal.ofReal (Real.exp
              (4 * width ^ v + 2 * u * width +
                2 * (K - dLower) * (N : ℝ) / width ^ 2 + 2 * dLower / width ^ 2))) ≤
          (offspringFieldLaw μ) (hasPathHistoryIn φ N 0
            (affineCorridorThrough N 0 (K / width ^ 2) width
              (K * (N : ℝ) / width ^ 2 + u * width))) := by
  intro K
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let ν := tiltedPotentialLaw φ (-1) μ
  let : IsProbabilityMeasure ν := tiltedPotentialLaw_isProbability φ μ hboundary
  obtain ⟨widthLower, _, hlower⟩ :=
    exists_uniform_driftedTube_endpoint_bounds hcentered hsigma hu habove hK hε
  obtain ⟨widthUpper, hwidthUpper, hupper⟩ :=
    exists_lintegral_pathGeneration_affineCorridor_sq_le_exp_sum_of_finiteVariance
      φ μ hboundary hcross hcentered (by positivity) hv hK hdLower hbelow
  refine ⟨max widthLower widthUpper, hwidthUpper.trans (le_max_right _ _), ?_⟩
  intro width hwidth N hN hscale
  have hw : 1 ≤ width := hwidthUpper.trans ((le_max_right _ _).trans hwidth)
  let U := K * (N : ℝ) / width ^ 2 + u * width
  let corridor := affineCorridorThrough N 0 (K / width ^ 2) width U
  let mean := ∫⁻ ω, pathGeneration φ N
    (corridor.indicator (fun _ => (1 : ℝ≥0∞))) 0 ω ∂offspringFieldLaw μ
  let B := 4 * width ^ v + 2 * u * width +
    2 * (K - dLower) * (N : ℝ) / width ^ 2 + 2 * dLower / width ^ 2
  let second : ℝ≥0∞ := (N + 1 : ℝ≥0∞) * ENNReal.ofReal (Real.exp B)
  have hmeas : MeasurableSet corridor := measurableSet_affineCorridorThrough ..
  have hmean : ENNReal.ofReal (Real.exp ((K - dUpper) * (N : ℝ) / width ^ 2)) ≤ mean := by
    have hspine : ENNReal.ofReal (Real.exp (-dUpper * (N : ℝ) / width ^ 2)) ≤
        (tiltedIncrementFieldLaw φ μ) {z | history N 0 z ∈ corridor} := by
      apply le_trans ?_ (measure_mono (endpointWindow_subset_affineCorridor N width K u
        (by linarith)))
      change _ ≤ iidSequenceLaw ν (driftedTubeEndpointWindowEvent N width K 0 u)
      rw [← ofReal_measureReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal
        (hlower width ((le_max_left _ _).trans hwidth) N 0 hscale le_rfl (by linarith)).1
    have h := lintegral_pathGeneration_ge_exp_mul_spineProbability φ μ hboundary N 0
      (K / width ^ 2 * (N : ℝ)) corridor hmeas (fun _ hx => by simpa using
        (hx.1 ⟨N, Nat.lt_succ_self N⟩).1)
    refine le_trans ?_ ((mul_le_mul_right hspine _).trans h)
    apply le_of_eq
    simp only [sub_zero, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2
    ring
  have hsecond : (∫⁻ ω, (pathGeneration φ N
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) 0 ω) ^ 2 ∂offspringFieldLaw μ) ≤
        second := by
    have h := hupper width ((le_max_right _ _).trans hwidth) 0 (by linarith) le_rfl N hN U
    refine h.trans ?_
    have hsum : (∑ m : Fin N, ENNReal.ofReal (Real.exp
        (dLower * (m.val : ℝ) / width ^ 2 - (0 + K / width ^ 2 * (m.val : ℝ))))) ≤
        (N : ℝ≥0∞) := by
      calc
        _ ≤ ∑ _m : Fin N, (1 : ℝ≥0∞) := by
          apply Finset.sum_le_sum
          intro m _
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (by
            rw [zero_add, div_mul_eq_mul_div, ← sub_div, ← sub_mul]
            exact div_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbelow.le) (by positivity))
              (by positivity)))
        _ = _ := by simp
    have hcommon :
        4 * width ^ v + 2 * U - 2 * dLower * ((N : ℝ) - 1) / width ^ 2 = B := by
      dsimp [U, B]
      ring
    have hdiag :
        U + width ^ v - dLower * (N : ℝ) / width ^ 2 ≤ B := by
      dsimp [U, B]
      have h1 : 0 ≤ (K - dLower) * (N : ℝ) / width ^ 2 :=
        div_nonneg (mul_nonneg (sub_nonneg.mpr hbelow.le) (by positivity)) (sq_nonneg _)
      have h2 : 0 ≤ dLower / width ^ 2 := by positivity
      have h3 : 0 ≤ width ^ v := Real.rpow_nonneg (by linarith) _
      have h4 : 0 ≤ u * width := mul_nonneg hu.le (by linarith)
      apply sub_nonneg.mp
      calc
        0 ≤ 3 * (width ^ v) + u * width +
            (K - dLower) * (N : ℝ) / width ^ 2 + 2 * (dLower / width ^ 2) := by
          exact add_nonneg (add_nonneg (add_nonneg (by linarith) h4) h1) (by linarith)
        _ = _ := by ring
    rw [hcommon]
    unfold second
    rw [add_mul, one_mul, mul_comm (N : ℝ≥0∞)]
    exact add_le_add (mul_le_mul_right hsum _)
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hdiag))
  have hpos : 0 < second := by
    change 0 < (↑N + 1 : ℝ≥0∞) * ENNReal.ofReal (Real.exp B)
    exact lt_of_le_of_ne bot_le
      (mul_ne_zero (by simp) (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))).symm
  have hfinite : second ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, ENNReal.one_ne_top⟩)
      ENNReal.ofReal_ne_top
  refine le_trans ?_ (measure_hasPathHistoryIn_ge_of_pathGeneration_moments
    φ μ N 0 corridor hmeas mean second rfl hsecond hpos hfinite)
  change _ ≤ mean ^ 2 / second
  apply ENNReal.div_le_div_right
  calc
    _ = ENNReal.ofReal (Real.exp ((K - dUpper) * (N : ℝ) / width ^ 2)) ^ 2 := by
      simp only [pow_two, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := pow_le_pow_left' hmean 2

end ProbabilityTheory.BranchingRandomWalk.Spine.CriticalCorridor
