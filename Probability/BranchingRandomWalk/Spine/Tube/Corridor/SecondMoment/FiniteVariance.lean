/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Tube.Corridor.SecondMoment
public import Probability.BranchingRandomWalk.Assumptions.CrossWeight
public import Probability.Distributions.Moments.Real
import Probability.BranchingRandomWalk.Spine.Tube.MRCA.PositiveDepth
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceUpper.Basic
import all Probability.BranchingRandomWalk.Spine.Tube.MRCA.Lemmas.AffineCorridorContinuation

/-!
# Finite variance second-moment bound in an affine corridor

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.exists_lintegral_pathGeneration_affineCorridor_sq_le_exp_sum_of_finiteVariance`
  gives, for finite cross-child weight and a centered spine of variance
  $\sigma^2>0$, the uniform bound
  $E[X_N^2]\le e^{4\Delta^v+2U-2d(N-1)/\Delta^2}
  \sum_{m<N}e^{dm/\Delta^2-r_m}+e^{U+\Delta^v-dN/\Delta^2}$,
  for $v>0$, $0<d<\pi^2\sigma^2/2$ and sufficiently large $\Delta$.

Here $r_m=r_0+cm/\Delta^2$, where $c\ge0$ and $r_0\le0\le r_0+\Delta$.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

private lemma measure_affineCorridorPrefix_le_driftedTube
    (ν : Measure (ℕ → ℝ)) (n : ℕ) (initial lower c width : ℝ) :
    ν {increment | history n initial increment ∈
      affineCorridorPrefix n lower (c / width ^ 2) width} ≤
      ν (driftedTubeEvent n width c (lower - initial)) := by
  apply measure_mono
  intro increment h j _ hj
  have hk := h (⟨j, by omega⟩ : Fin (n + 1))
  change lower + (c / width ^ 2) * (j : ℝ) ≤
    history n initial increment ⟨j, by omega⟩ ∧
      history n initial increment ⟨j, by omega⟩ ≤
        lower + (c / width ^ 2) * (j : ℝ) + width at hk
  simp only [history_apply, div_mul_eq_mul_div] at hk
  constructor <;> linarith [hk.1, hk.2]

/-- Equation (3.7) of Wang Yiyang, *Asymptotic Speed of the N-Branching Random
Walk with Infinite Offspring* (master's thesis, Fudan University, 2026),
Chapter 3, Lemma 3.6. Apply the tilted-tube estimate to both descendants after
the split and to the ancestor prefix; the diagonal is a many-to-one term. -/
theorem exists_lintegral_pathGeneration_affineCorridor_sq_le_exp_sum_of_finiteVariance
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ) (hcross : HasFiniteCrossWeight φ μ)
    {variance v c d : ℝ}
    (hcentered : ProbabilityTheory.IsCenteredSecondMoment (tiltedPotentialLaw φ (-1) μ) variance)
    (hvariance : 0 < variance) (hv : 0 < v) (hc : 0 ≤ c)
    (hd : 0 < d) (hcritical : d < (Real.pi ^ 2 / 2) * variance) :
    ∃ width₀ : ℝ, 1 ≤ width₀ ∧
      ∀ width ≥ width₀, ∀ lower : ℝ, -width ≤ lower → lower ≤ 0 →
        ∀ (N : ℕ), 1 ≤ N → ∀ U : ℝ,
        (∫⁻ ω, (pathGeneration φ N
          ((affineCorridorThrough N lower (c / width ^ 2) width U).indicator
            (fun _ => (1 : ℝ≥0∞))) 0 ω) ^ 2 ∂offspringFieldLaw μ) ≤
          ENNReal.ofReal (Real.exp
            (4 * width ^ v + 2 * U - 2 * d * ((N : ℝ) - 1) / width ^ 2)) *
            (∑ m : Fin N, ENNReal.ofReal (Real.exp
              (d * (m.val : ℝ) / width ^ 2 - (lower + c / width ^ 2 * (m.val : ℝ))))) +
          ENNReal.ofReal (Real.exp (U + width ^ v - d * (N : ℝ) / width ^ 2)) := by
  let ν := tiltedPotentialLaw φ (-1) μ
  let : IsProbabilityMeasure ν := tiltedPotentialLaw_isProbability φ μ hboundary
  obtain ⟨widthTube, hwidthTube, htube⟩ :=
    exists_driftedTubeProbability_le_exp_of_finiteVariance
      ν hcentered hvariance hv hc hd hcritical
  let M := ∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ
  obtain ⟨widthCross, hwidthCross⟩ := Filter.eventually_atTop.1
    ((_root_.tendsto_rpow_atTop hv).eventually (Filter.eventually_ge_atTop M.toReal))
  refine ⟨max widthTube widthCross, hwidthTube.trans (le_max_left _ _), ?_⟩
  intro width hwidth lower hlower hupper N hN U
  let s := c / width ^ 2
  let q (n : ℕ) := ENNReal.ofReal (Real.exp (width ^ v - d * ((n : ℝ) / width ^ 2)))
  have hM : M ≤ ENNReal.ofReal (Real.exp (width ^ v)) := by
    rw [← ENNReal.ofReal_toReal (show M ≠ ∞ from hcross)]
    exact ENNReal.ofReal_le_ofReal ((hwidthCross width ((le_max_right _ _).trans hwidth)).trans
      ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)))
  have hprefix (n : ℕ) (a x : ℝ) (hx : a ≤ x ∧ x ≤ a + width) :
      tiltedIncrementFieldLaw φ μ
        {increment | history n x increment ∈ affineCorridorPrefix n a s width} ≤ q n := by
    apply (measure_affineCorridorPrefix_le_driftedTube _ n x a c width).trans
    change iidSequenceLaw ν (driftedTubeEvent n width c (a - x)) ≤ q n
    rw [← MeasureTheory.ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal
      (htube width ((le_max_left _ _).trans hwidth) (a - x) (by linarith [hx.2])
        (sub_nonpos.mpr hx.1) n)
  let corridor := affineCorridorThrough N lower s width U
  have hdiag := lintegral_pathGeneration_le_exp_mul_spineProbability φ μ hboundary N 0 U
    corridor (measurableSet_affineCorridorThrough N lower s width U) (fun _ h => h.2)
  have hdiag' :
      (∫⁻ ω, pathGeneration φ N (corridor.indicator (fun _ => (1 : ℝ≥0∞))) 0 ω
        ∂offspringFieldLaw μ) ≤
      ENNReal.ofReal (Real.exp (U + width ^ v - d * (N : ℝ) / width ^ 2)) := by
    refine hdiag.trans ?_
    have hp := (measure_mono (fun _ (h : _ ∈ {increment |
        history N 0 increment ∈ corridor}) => h.1)).trans
      (hprefix N lower 0 ⟨hupper, by linarith⟩)
    refine (mul_le_mul_right hp _).trans_eq ?_
    simp only [q, sub_zero, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2
    ring
  have hpair (m : Fin N) :
      affineTubeMRCAPairContribution φ μ m.val (N - m.val - 1) 0 lower s width U ≤
        ENNReal.ofReal (Real.exp
          (4 * width ^ v + 2 * U - 2 * d * ((N : ℝ) - 1) / width ^ 2)) *
        ENNReal.ofReal (Real.exp (d * (m.val : ℝ) / width ^ 2 - (lower + s * m.val))) := by
    let n := N - m.val - 1
    rw [affineTubeMRCAPairContribution_eq_normalized]
    refine (lintegral_affineCorridorPrefixContinuationPair_indicator_le_of_continuationBound
      φ μ hboundary m.val n 0 lower s width U (q n) ?_).trans ?_
    · intro x y hxy
      apply (measure_mono ?_).trans (hprefix n (lower + s * (m.val : ℝ) + s) (x + y) hxy)
      intro z hz
      intro j
      have hj := hz.1 j.succ
      simp only [prependHistory_succ] at hj
      change lower + s * (m.val : ℝ) + s * ((j.succ).val : ℝ) ≤ _ ∧
        _ ≤ lower + s * (m.val : ℝ) + s * ((j.succ).val : ℝ) + width at hj
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one, mul_add, mul_one] at hj
      change lower + s * (m.val : ℝ) + s + s * (j.val : ℝ) ≤ _ ∧
        _ ≤ lower + s * (m.val : ℝ) + s + s * (j.val : ℝ) + width
      exact ⟨by linarith [hj.1], by linarith [hj.2]⟩
    · refine (mul_le_mul'
        (mul_le_mul_right hM _)
        (mul_le_mul_right (hprefix m.val lower 0 ⟨hupper, by linarith⟩) _)).trans_eq ?_
      have hnNat : n + m.val + 1 = N := by dsimp [n]; omega
      have hn : (n : ℝ) + (m.val : ℝ) + 1 = (N : ℝ) := by exact_mod_cast hnNat
      simp only [q, mul_assoc, pow_two, zero_sub, mul_zero, neg_zero, Real.exp_zero,
        ENNReal.ofReal_one, one_mul]
      simp only [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      rw [← hn]
      ring
  rw [lintegral_pathGeneration_affineCorridor_sq_eq_firstMoment_add_mrcaContributions
    φ μ hboundary N 0 lower s width U]
  rw [Finset.mul_sum, add_comm]
  exact add_le_add (Finset.sum_le_sum fun m _ => hpair m) hdiag'

end ProbabilityTheory.BranchingRandomWalk.Spine

end
