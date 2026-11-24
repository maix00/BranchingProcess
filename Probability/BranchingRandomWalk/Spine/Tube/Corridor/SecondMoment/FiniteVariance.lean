/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Tube.Corridor.SecondMoment
public import Probability.BranchingRandomWalk.Assumptions.CrossWeight
public import Probability.Distributions.Moments.Real
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.SecondMoment.FamilySelection

/-!
# Finite variance second-moment bound in an affine corridor

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.exists_lintegral_pathGeneration_affineCorridor_sq_le_crossWeight_mul_exp_sum_of_finiteVariance`
  gives the bound below with the coefficient `C = ∫ crossPotentialWeight dμ`
  retained explicitly:
  `E[X_N²] ≤ C exp(3Δᵛ + 2U - 2d(N-1)/Δ²) ∑_(m<N) exp(dm/Δ²-r_m)`
  `+ exp(U+Δᵛ-dN/Δ²)`. Its width threshold is independent of `C`,
  and no finite-cross-weight assumption is required.
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

/-- Equation (3.7) of Wang Yiyang, *Asymptotic Speed of the N-Branching Random
Walk with Infinite Offspring* (master's thesis, Fudan University, 2026),
Chapter 3, Lemma 3.6. Apply the tilted-tube estimate to both descendants after
the split and to the ancestor prefix; the diagonal is a many-to-one term.
The cross coefficient stays explicit, so the width threshold depends only on
the original spinal tube bound. -/
theorem exists_lintegral_pathGeneration_affineCorridor_sq_le_crossWeight_mul_exp_sum_of_finiteVariance
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
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
          (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) *
          ENNReal.ofReal (Real.exp
            (3 * width ^ v + 2 * U - 2 * d * ((N : ℝ) - 1) / width ^ 2)) *
            (∑ m : Fin N, ENNReal.ofReal (Real.exp
              (d * (m.val : ℝ) / width ^ 2 - (lower + c / width ^ 2 * (m.val : ℝ))))) +
          ENNReal.ofReal (Real.exp (U + width ^ v - d * (N : ℝ) / width ^ 2)) := by
  obtain ⟨width₀, hwidth₀, hbound⟩ :=
    exists_lintegral_pathGeneration_affineCorridor_selectFamily_sq_le_crossWeight_mul_exp_sum_of_finiteVariance
      φ μ hboundary hcentered hvariance hv hc hd hcritical
  refine ⟨width₀, hwidth₀, ?_⟩
  intro width hwidth lower hlower hupper N hN U
  have hsel : (Step.selectFamily Set.univ : Step ℕ X → Step ℕ X) = id := by
    funext ξ
    exact Step.selectFamily_of_mem (Set.mem_univ ξ)
  have h := hbound width hwidth Set.univ MeasurableSet.univ lower hlower hupper N hN U
  rw [hsel, Measure.map_id, Measure.restrict_univ] at h
  exact h

/-- The fixed finite-cross-weight version of Wang Yiyang, *Asymptotic Speed
of the N-Branching Random Walk with Infinite Offspring* (2026), Chapter 3,
Lemma 3.6, equation (3.7), follows by absorbing the cross weight into one
additional exponential width error. -/
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
  obtain ⟨widthTube, hwidthTube, htube⟩ :=
    exists_lintegral_pathGeneration_affineCorridor_sq_le_crossWeight_mul_exp_sum_of_finiteVariance
      φ μ hboundary hcentered hvariance hv hc hd hcritical
  let M := ∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ
  obtain ⟨widthCross, hwidthCross⟩ := Filter.eventually_atTop.1
    ((_root_.tendsto_rpow_atTop hv).eventually (Filter.eventually_ge_atTop M.toReal))
  refine ⟨max widthTube widthCross, hwidthTube.trans (le_max_left _ _), ?_⟩
  intro width hwidth lower hlower hupper N hN U
  have hM : M ≤ ENNReal.ofReal (Real.exp (width ^ v)) := by
    rw [← ENNReal.ofReal_toReal (show M ≠ ∞ from hcross)]
    exact ENNReal.ofReal_le_ofReal ((hwidthCross width ((le_max_right _ _).trans hwidth)).trans
      ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)))
  refine (htube width ((le_max_left _ _).trans hwidth) lower hlower hupper N hN U).trans ?_
  apply add_le_add _ le_rfl
  calc
    _ ≤ ENNReal.ofReal (Real.exp (width ^ v)) *
        ENNReal.ofReal (Real.exp
          (3 * width ^ v + 2 * U - 2 * d * ((N : ℝ) - 1) / width ^ 2)) *
        (∑ m : Fin N, ENNReal.ofReal (Real.exp
          (d * (m.val : ℝ) / width ^ 2 - (lower + c / width ^ 2 * (m.val : ℝ))))) := by
      gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 3
      ring

end ProbabilityTheory.BranchingRandomWalk.Spine

end
