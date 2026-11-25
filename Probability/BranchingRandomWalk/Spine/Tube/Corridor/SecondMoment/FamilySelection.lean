/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Tube.Corridor.SecondMoment
public import Probability.BranchingRandomWalk.Spine.Tube.MRCA.FamilySelection
public import Probability.Distributions.Moments.Real
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceUpper.Basic

/-!
# Finite-variance second moments after whole-family selection

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.exists_lintegral_pathGeneration_affineCorridor_selectFamily_sq_le_crossWeight_mul_exp_sum_of_finiteVariance`:
  for the actual offspring law `μ_A = μ.map (Step.selectFamily A)`,
  `E[Z_N²] ≤ C_A exp(3Δᵛ+2U-2d(N-1)/Δ²)
  ∑_(m<N) exp(dm/Δ²-r_m) + exp(U+Δᵛ-dN/Δ²)`,
  where `C_A=∫_A crossWeight dμ` and `r_m=l+cm/Δ²`.
  The threshold is uniform over all measurable family events `A`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.exists_lintegral_pathGeneration_affineCorridor_sq_le_cutoff_mul_exp_sum_of_finiteVariance`
  specializes to `A={W≤K}` and replaces `C_A` by `K`, uniformly in `K`.
  In particular `K=exp(αΔ)` is allowed even when the original cross moment
  is infinite.

Only the original law is boundary-normalized with a centered finite-variance
spine. The selected law retains whole-family acceptance along every counted
ancestral path. Its continuation and prefix estimates are derived through the
original-field coupling, without a centering assertion for the selected law.
This is Mallein's family-cutoff MRCA argument, *N-branching random walk with
α-stable spine*, proof of Lemma 3.4, arXiv:1503.03762v2, with the affine
finite-variance tube bounds from Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.6.
-/

open MeasureTheory
open scoped ENNReal
@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk.Spine
open Combinatorics.Branching
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- Whole-family-selection extension of equation (3.7) of Wang Yiyang, *Asymptotic Speed of the N-Branching Random
Walk with Infinite Offspring* (master's thesis, Fudan University, 2026),
Chapter 3, Lemma 3.6. Apply the tilted-tube estimate to both descendants after
the split and to the ancestor prefix; the diagonal is a many-to-one term.
The cross coefficient stays explicit, so the width threshold depends only on
the original spinal tube bound. -/
theorem exists_lintegral_pathGeneration_affineCorridor_selectFamily_sq_le_crossWeight_mul_exp_sum_of_finiteVariance
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    {variance v c d : ℝ}
    (hcentered : ProbabilityTheory.IsCenteredSecondMoment (tiltedPotentialLaw φ (-1) μ) variance)
    (hvariance : 0 < variance) (hv : 0 < v) (hc : 0 ≤ c)
    (hd : 0 < d) (hcritical : d < (Real.pi ^ 2 / 2) * variance) :
    ∃ width₀ : ℝ, 1 ≤ width₀ ∧
      ∀ width ≥ width₀, ∀ A : Set (Step ℕ X), MeasurableSet A → ∀ lower : ℝ, -width ≤ lower → lower ≤ 0 →
        ∀ (N : ℕ), 1 ≤ N → ∀ U : ℝ,
        (∫⁻ ω, (pathGeneration φ N
          ((affineCorridorThrough N lower (c / width ^ 2) width U).indicator
            (fun _ => (1 : ℝ≥0∞))) 0 ω) ^ 2 ∂offspringFieldLaw (μ.map (Step.selectFamily A))) ≤
          (∫⁻ ξ in A, crossPotentialWeight φ (-1) ξ ∂μ) *
          ENNReal.ofReal (Real.exp
            (3 * width ^ v + 2 * U - 2 * d * ((N : ℝ) - 1) / width ^ 2)) *
            (∑ m : Fin N, ENNReal.ofReal (Real.exp
              (d * (m.val : ℝ) / width ^ 2 - (lower + c / width ^ 2 * (m.val : ℝ))))) +
          ENNReal.ofReal (Real.exp (U + width ^ v - d * (N : ℝ) / width ^ 2)) := by
  let ν := tiltedPotentialLaw φ (-1) μ
  let : IsProbabilityMeasure ν := tiltedPotentialLaw_isProbability φ μ hboundary
  obtain ⟨widthTube, hwidthTube, htube⟩ :=
    exists_driftedTubeProbability_le_exp_of_finiteVariance
      ν hcentered hvariance hv hc hd hcritical
  refine ⟨widthTube, hwidthTube, ?_⟩
  intro width hwidth A hA lower hlower hupper N hN U
  let μA := μ.map (Step.selectFamily A)
  let M := ∫⁻ ξ in A, crossPotentialWeight φ (-1) ξ ∂μ
  let s := c / width ^ 2
  let q (n : ℕ) := ENNReal.ofReal (Real.exp (width ^ v - d * ((n : ℝ) / width ^ 2)))
  have hprefix (n : ℕ) (a x : ℝ) (hx : a ≤ x ∧ x ≤ a + width) :
      tiltedIncrementFieldLaw φ μ
        {increment | history n x increment ∈ affineCorridorPrefix n a s width} ≤ q n := by
    apply (measure_mono (affineCorridorPrefix_history_subset_driftedTubeEvent n x a c width)).trans
    change iidSequenceLaw ν (driftedTubeEvent n width c (a - x)) ≤ q n
    rw [← MeasureTheory.ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal
      (htube width hwidth (a - x) (by linarith [hx.2])
        (sub_nonpos.mpr hx.1) n)
  let corridor := affineCorridorThrough N lower s width U
  have hdiag := lintegral_pathGeneration_le_exp_mul_spineProbability φ μ hboundary N 0 U
    corridor (measurableSet_affineCorridorThrough N lower s width U) (fun _ h => h.2)
  have hdiag' :
      (∫⁻ ω, pathGeneration φ N (corridor.indicator (fun _ => (1 : ℝ≥0∞))) 0 ω
        ∂offspringFieldLaw μA) ≤
      ENNReal.ofReal (Real.exp (U + width ^ v - d * (N : ℝ) / width ^ 2)) := by
    refine (lintegral_pathGeneration_selectFamily_le φ μ hA N
      (measurable_const.indicator (measurableSet_affineCorridorThrough N lower s width U))
      0).trans (hdiag.trans ?_)
    have hp := (measure_mono (fun _ (h : _ ∈ {increment |
        history N 0 increment ∈ corridor}) => h.1)).trans
      (hprefix N lower 0 ⟨hupper, by linarith⟩)
    refine (mul_le_mul_right hp _).trans_eq ?_
    simp only [q, sub_zero, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2
    ring
  have hpair (m : Fin N) :
      affineTubeMRCAPairContribution φ μA m.val (N - m.val - 1) 0 lower s width U ≤
        M * ENNReal.ofReal (Real.exp
          (3 * width ^ v + 2 * U - 2 * d * ((N : ℝ) - 1) / width ^ 2)) *
        ENNReal.ofReal (Real.exp (d * (m.val : ℝ) / width ^ 2 - (lower + s * m.val))) := by
    let n := N - m.val - 1
    refine (affineTubeMRCAPairContribution_selectFamily_le φ μ hboundary hA
      m.val n lower s width U (q m.val) (q n)
      (hprefix m.val lower 0 ⟨hupper, by linarith⟩) ?_).trans_eq ?_
    · intro x y hxy
      apply (measure_mono ?_).trans (hprefix n (lower + s * (m.val : ℝ) + s) (x + y) hxy)
      intro z hz j
      have hj := hz.1 j.succ
      simp only [prependHistory_succ] at hj
      change lower + s * (m.val : ℝ) + s * ((j.succ).val : ℝ) ≤ _ ∧
        _ ≤ lower + s * (m.val : ℝ) + s * ((j.succ).val : ℝ) + width at hj
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one, mul_add, mul_one] at hj
      change lower + s * (m.val : ℝ) + s + s * (j.val : ℝ) ≤ _ ∧
        _ ≤ lower + s * (m.val : ℝ) + s + s * (j.val : ℝ) + width
      exact ⟨by linarith [hj.1], by linarith [hj.2]⟩
    · have hnNat : n + m.val + 1 = N := by dsimp [n]; omega
      have hn : (n : ℝ) + (m.val : ℝ) + 1 = (N : ℝ) := by exact_mod_cast hnNat
      calc
        _ = M * (ENNReal.ofReal (Real.exp (2 * U - (lower + s * (m.val : ℝ))))) *
            ((ENNReal.ofReal (Real.exp (width ^ v - d * ((n : ℝ) / width ^ 2)))) ^ 2) *
            ENNReal.ofReal (Real.exp (width ^ v - d * ((m.val : ℝ) / width ^ 2))) := by rfl
        _ = _ := by
          simp only [pow_two, mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
            ← Real.exp_add]
          congr 2
          rw [← hn]
          ring_nf
  rw [lintegral_pathGeneration_affineCorridor_sq_eq_firstMoment_add_mrcaContributions
    φ μA N 0 lower s width U]
  rw [Finset.mul_sum, add_comm]
  exact add_le_add (Finset.sum_le_sum fun m _ => hpair m) hdiag'


/-- The actual all-ancestor cutoff `W≤K` gives the cross coefficient `C_K≤K`,
without any assumption on the original untruncated cross moment. -/
theorem exists_lintegral_pathGeneration_affineCorridor_sq_le_cutoff_mul_exp_sum_of_finiteVariance
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    {variance v c d : ℝ}
    (hcentered : ProbabilityTheory.IsCenteredSecondMoment (tiltedPotentialLaw φ (-1) μ) variance)
    (hvariance : 0 < variance) (hv : 0 < v) (hc : 0 ≤ c)
    (hd : 0 < d) (hcritical : d < (Real.pi ^ 2 / 2) * variance) :
    ∃ width₀ : ℝ, 1 ≤ width₀ ∧
      ∀ width ≥ width₀, ∀ K : ℝ≥0∞, ∀ lower : ℝ, -width ≤ lower → lower ≤ 0 →
        ∀ (N : ℕ), 1 ≤ N → ∀ U : ℝ,
        (∫⁻ ω, (pathGeneration φ N
          ((affineCorridorThrough N lower (c / width ^ 2) width U).indicator
            (fun _ => (1 : ℝ≥0∞))) 0 ω) ^ 2 ∂offspringFieldLaw (μ.map (Step.selectFamily {ξ | totalPotentialWeight φ (-1) ξ ≤ K}))) ≤
          K *
          ENNReal.ofReal (Real.exp
            (3 * width ^ v + 2 * U - 2 * d * ((N : ℝ) - 1) / width ^ 2)) *
            (∑ m : Fin N, ENNReal.ofReal (Real.exp
              (d * (m.val : ℝ) / width ^ 2 - (lower + c / width ^ 2 * (m.val : ℝ))))) +
          ENNReal.ofReal (Real.exp (U + width ^ v - d * (N : ℝ) / width ^ 2)) := by
  obtain ⟨width₀, hwidth₀, hbound⟩ :=
    exists_lintegral_pathGeneration_affineCorridor_selectFamily_sq_le_crossWeight_mul_exp_sum_of_finiteVariance
      φ μ hboundary hcentered hvariance hv hc hd hcritical
  refine ⟨width₀, hwidth₀, ?_⟩
  intro width hwidth K lower hlower hupper N hN U
  have hA : MeasurableSet {ξ : Step ℕ X | totalPotentialWeight φ (-1) ξ ≤ K} :=
    measurableSet_le (totalPotentialWeight_measurable φ (-1)) measurable_const
  refine (hbound width hwidth _ hA lower hlower hupper N hN U).trans ?_
  have hcross := lintegral_crossPotentialWeight_on_totalWeight_le_of_boundary φ μ hboundary K
  exact add_le_add (mul_le_mul' (mul_le_mul' hcross le_rfl) le_rfl) le_rfl


end ProbabilityTheory.BranchingRandomWalk.Spine
