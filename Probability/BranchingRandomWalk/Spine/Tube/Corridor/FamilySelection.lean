/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Tube.Corridor.FirstMoment.FamilySelection
public import Probability.BranchingRandomWalk.Spine.Tube.Corridor.SecondMoment.FamilySelection
public import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.PathCount
import all Probability.BranchingRandomWalk.Spine.Tube.Corridor.Lemmas.FamilySelection.ExponentBudget

/-!
# Success probabilities for actual family-selected corridors

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.eventually_measure_hasPathHistoryIn_affineCorridor_cutoff_ge_of_finiteVariance`:
  for the original centered finite-variance spine with Mallein's weak spinal
  weight tail, let `μₙ` accept exactly `W≤exp(αLₙ)`. The actual one-root
  corridor-success probability is at least `Mₙ²/Sₙ`, where
  `Mₙ=exp((b-ρ-a)Lₙ+(c-dLower)Hₙ/Lₙ²)` and `Sₙ` is the explicit
  cutoff MRCA second-moment bound displayed in the theorem. Here
  `0<dUpper<π²σ²/2<dLower`, `Lₙ→∞` and `Lₙ²/Hₙ→0`.

* `ProbabilityTheory.BranchingRandomWalk.Spine.eventually_exp_le_measure_hasPathHistoryIn_affineCorridor_cutoff_of_cubicScale`:
  if `Hₙ/Lₙ³→t>0`, `c≥dUpper`, and
  `β>α+4ρ+a+1/2+2(dLower-dUpper)t`, then the same actual one-root
  success probability is eventually at least `exp(-βLₙ)`.

* `ProbabilityTheory.BranchingRandomWalk.Spine.eventually_exp_le_measure_hasPathHistoryIn_affineCorridor_of_cubicScale`:
  the same `exp(-βLₙ)` lower bound holds for the original BRW, since whole-family
  selection only removes paths. It retains the original weak-tail assumption.

The first and second moments refer to the same `pathGeneration` under the
same actual selected offspring law. The success event is the existing
`hasPathHistoryIn`. The proof calls the existing Paley--Zygmund interface.
No cross moment of the original untruncated offspring law is assumed.

This combines the family-cutoff first and second moments in B. Mallein,
*N-branching random walk with α-stable spine*, proof of Lemma 3.4,
arXiv:1503.03762v2, and *Necessary and sufficient conditions for the convergence
of the consistent maximal displacement of the branching random walk*, proof
of Lemma 3.4, arXiv:1510.00602v2. The affine MRCA estimate extends Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026), Chapter 3, Lemma 3.6, equation (3.7).
-/

@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk.Spine
open MeasureTheory Filter Combinatorics.Branching
open BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.RandomWalk
open scoped ENNReal Topology Classical

set_option backward.isDefEq.respectTransparency false

/-- The actual cutoff corridor succeeds with probability at least the squared
marked first-moment lower bound divided by the cutoff MRCA bound. This is
the Paley--Zygmund step in B. Mallein, *N-branching random walk with α-stable
spine*, proof of Lemma 3.4 (arXiv:1503.03762v2). -/
theorem eventually_measure_hasPathHistoryIn_affineCorridor_cutoff_ge_of_finiteVariance
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    {sigma v c α dUpper dLower a b ρ : ℝ}
    (hcentered : IsCenteredSecondMoment (tiltedPotentialLaw φ (-1) μ) (sigma ^ 2))
    (hσ : 0 < sigma) (htail : HasSpinalWeightTail φ μ)
    (hv : 0 < v) (hc : 0 ≤ c) (hα : 0 < α)
    (hdUpper : 0 < dUpper) (hUpperCritical : dUpper < (Real.pi ^ 2 / 2) * sigma ^ 2)
    (hLowerCritical : (Real.pi ^ 2 / 2) * sigma ^ 2 < dLower)
    (ha : -(1 / 2 : ℝ) < a) (ha' : a < 1 / 2)
    (hb : -(1 / 2 : ℝ) < b) (hb' : b < 1 / 2) (hρ : 0 < ρ)
    {scale : ℕ → ℝ} {horizon : ℕ → ℕ} (hscale : Tendsto scale atTop atTop)
    (horizonPos : ∀ᶠ n in atTop, 0 < horizon n)
    (hsmall : Tendsto (fun n => scale n ^ 2 / (horizon n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      let L := scale n
      let H := horizon n
      let lower := -(a + 1 / 2) * L
      let U := (b + ρ - a) * L + c * (H : ℝ) / L ^ 2
      let K := ENNReal.ofReal (Real.exp (α * L))
      let S := K * ENNReal.ofReal (Real.exp
        (3 * L ^ v + 2 * U - 2 * dUpper * ((H : ℝ) - 1) / L ^ 2)) *
          (∑ m : Fin H, ENNReal.ofReal (Real.exp
            (dUpper * (m.val : ℝ) / L ^ 2 - (lower + c / L ^ 2 * (m.val : ℝ))))) +
          ENNReal.ofReal (Real.exp (U + L ^ v - dUpper * (H : ℝ) / L ^ 2))
      ENNReal.ofReal (Real.exp ((b - ρ - a) * L + (c - dLower) * (H : ℝ) / L ^ 2)) ^ 2 / S ≤
        offspringFieldLaw (μ.map (Step.selectFamily {ξ | totalPotentialWeight φ (-1) ξ ≤ K}))
          (hasPathHistoryIn φ H 0 (affineCorridorThrough H lower (c / L ^ 2) L U)) := by
  obtain ⟨L₀, hL₀, hsecond⟩ :=
    exists_lintegral_pathGeneration_affineCorridor_sq_le_cutoff_mul_exp_sum_of_finiteVariance
      φ μ hboundary hcentered (sq_pos_of_pos hσ) hv hc hdUpper hUpperCritical
  have hfirst := eventually_lintegral_pathGeneration_affineCorridor_cutoff_ge_of_finiteVariance
    φ μ hboundary hcentered hσ htail hc hα hLowerCritical ha ha' hb hb' hρ hscale horizonPos hsmall
  filter_upwards [hfirst, hscale.eventually_ge_atTop L₀, hscale.eventually_gt_atTop 0,
    horizonPos] with n hfirstN hlarge hL hH
  dsimp only
  let L := scale n
  let H := horizon n
  let lower := -(a + 1 / 2) * L
  let U := (b + ρ - a) * L + c * (H : ℝ) / L ^ 2
  let K := ENNReal.ofReal (Real.exp (α * L))
  let A := {ξ : Step ℕ X | totalPotentialWeight φ (-1) ξ ≤ K}
  have hA : MeasurableSet A := measurableSet_le (totalPotentialWeight_measurable φ (-1)) measurable_const
  let μA := μ.map (Step.selectFamily A)
  let : IsProbabilityMeasure μA :=
    (Measure.isProbabilityMeasure_map_iff (Step.selectFamily_measurable hA).aemeasurable).2 inferInstance
  let C := affineCorridorThrough H lower (c / L ^ 2) L U
  have hC : MeasurableSet C := measurableSet_affineCorridorThrough _ _ _ _ _
  let S := K * ENNReal.ofReal (Real.exp
    (3 * L ^ v + 2 * U - 2 * dUpper * ((H : ℝ) - 1) / L ^ 2)) *
      (∑ m : Fin H, ENNReal.ofReal (Real.exp
        (dUpper * (m.val : ℝ) / L ^ 2 - (lower + c / L ^ 2 * (m.val : ℝ))))) +
      ENNReal.ofReal (Real.exp (U + L ^ v - dUpper * (H : ℝ) / L ^ 2))
  have hlower : -L ≤ lower := by
    dsimp [lower]
    nlinarith only [mul_le_mul_of_nonneg_right ha'.le hL.le]
  have hupper : lower ≤ 0 := by
    dsimp [lower]
    nlinarith only [mul_le_mul_of_nonneg_right ha.le hL.le]
  have hsecondN := hsecond L hlarge K lower hlower hupper H hH U
  have hSpos : 0 < S := by dsimp [S]; positivity
  have hSfinite : S ≠ ∞ := by
    dsimp [S, K]
    apply ENNReal.add_ne_top.mpr
    constructor
    · apply ENNReal.mul_ne_top
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      · exact ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top)
    · exact ENNReal.ofReal_ne_top
  have hpz := measure_hasPathHistoryIn_ge_of_pathGeneration_moments φ μA H 0 C hC
    _ S rfl hsecondN hSpos hSfinite
  refine (ENNReal.div_le_div_right (pow_le_pow_left' hfirstN 2) S).trans hpz

/-- Exponential one-root success on cubic time scales, obtained by simplifying
Mallein's cutoff first/second-moment ratio. See B. Mallein, *N-branching
random walk with α-stable spine*, proof of Lemma 3.4 (arXiv:1503.03762v2). -/
theorem eventually_exp_le_measure_hasPathHistoryIn_affineCorridor_cutoff_of_cubicScale
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    {sigma c α dUpper dLower a b ρ t β : ℝ}
    (hcentered : IsCenteredSecondMoment (tiltedPotentialLaw φ (-1) μ) (sigma ^ 2))
    (hσ : 0 < sigma) (htail : HasSpinalWeightTail φ μ) (hα : 0 < α)
    (hdUpper : 0 < dUpper) (hUpperCritical : dUpper < (Real.pi ^ 2 / 2) * sigma ^ 2)
    (hLowerCritical : (Real.pi ^ 2 / 2) * sigma ^ 2 < dLower) (hc : dUpper ≤ c)
    (ha : -(1 / 2 : ℝ) < a) (ha' : a < 1 / 2)
    (hb : -(1 / 2 : ℝ) < b) (hb' : b < 1 / 2) (hρ : 0 < ρ) (ht : 0 < t)
    (hβ : α + 4 * ρ + a + 1 / 2 + 2 * (dLower - dUpper) * t < β)
    {scale : ℕ → ℝ} {horizon : ℕ → ℕ} (hscale : Tendsto scale atTop atTop)
    (hH : Tendsto (fun n => (horizon n : ℝ) / scale n ^ 3) atTop (𝓝 t)) :
    ∀ᶠ n in atTop, ENNReal.ofReal (Real.exp (-β * scale n)) ≤
      offspringFieldLaw (μ.map (Step.selectFamily
        {ξ | totalPotentialWeight φ (-1) ξ ≤ ENNReal.ofReal (Real.exp (α * scale n))}))
        (hasPathHistoryIn φ (horizon n) 0
          (affineCorridorThrough (horizon n) (-(a + 1 / 2) * scale n)
            (c / scale n ^ 2) (scale n)
            ((b + ρ - a) * scale n + c * (horizon n : ℝ) / scale n ^ 2))) := by
  obtain ⟨hpos, hsmall, _, _⟩ := cutoffCorridor_cubicScaleFacts hscale hH ht
  have hprob := eventually_measure_hasPathHistoryIn_affineCorridor_cutoff_ge_of_finiteVariance
    (v := 1 / 2) φ μ hboundary hcentered hσ htail (by norm_num)
    (hdUpper.le.trans hc) hα hdUpper hUpperCritical hLowerCritical ha ha' hb hb' hρ
    hscale hpos hsmall
  have hbudget := eventually_cutoffCorridor_expBudget_le_ratio
    hscale hH ht hα.le hb hρ hdUpper.le hc hβ
  filter_upwards [hprob, hbudget] with n hp hbnd
  exact hbnd.trans hp

/-- The original BRW inherits the cutoff process's weak-tail success bound.
This removes the truncation only after its first/second moments have been used;
the original spine remains the centered law throughout. See B. Mallein,
*N-branching random walk with α-stable spine*, Lemma 3.4,
arXiv:1503.03762v2. -/
theorem eventually_exp_le_measure_hasPathHistoryIn_affineCorridor_of_cubicScale
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    {sigma c α dUpper dLower a b ρ t β : ℝ}
    (hcentered : IsCenteredSecondMoment (tiltedPotentialLaw φ (-1) μ) (sigma ^ 2))
    (hσ : 0 < sigma) (htail : HasSpinalWeightTail φ μ) (hα : 0 < α)
    (hdUpper : 0 < dUpper) (hUpperCritical : dUpper < (Real.pi ^ 2 / 2) * sigma ^ 2)
    (hLowerCritical : (Real.pi ^ 2 / 2) * sigma ^ 2 < dLower) (hc : dUpper ≤ c)
    (ha : -(1 / 2 : ℝ) < a) (ha' : a < 1 / 2)
    (hb : -(1 / 2 : ℝ) < b) (hb' : b < 1 / 2) (hρ : 0 < ρ) (ht : 0 < t)
    (hβ : α + 4 * ρ + a + 1 / 2 + 2 * (dLower - dUpper) * t < β)
    {scale : ℕ → ℝ} {horizon : ℕ → ℕ} (hscale : Tendsto scale atTop atTop)
    (hH : Tendsto (fun n => (horizon n : ℝ) / scale n ^ 3) atTop (𝓝 t)) :
    ∀ᶠ n in atTop, ENNReal.ofReal (Real.exp (-β * scale n)) ≤
      offspringFieldLaw μ
        (hasPathHistoryIn φ (horizon n) 0
          (affineCorridorThrough (horizon n) (-(a + 1 / 2) * scale n)
            (c / scale n ^ 2) (scale n)
            ((b + ρ - a) * scale n + c * (horizon n : ℝ) / scale n ^ 2))) := by
  have h := eventually_exp_le_measure_hasPathHistoryIn_affineCorridor_cutoff_of_cubicScale
    φ μ hboundary hcentered hσ htail hα hdUpper hUpperCritical hLowerCritical hc
    ha ha' hb hb' hρ ht hβ hscale hH
  filter_upwards [h] with n hn
  exact hn.trans (measure_hasPathHistoryIn_selectFamily_le φ μ
    (measurableSet_le (totalPotentialWeight_measurable φ (-1)) measurable_const)
    (horizon n) 0 _ (measurableSet_affineCorridorThrough _ _ _ _ _))

end ProbabilityTheory.BranchingRandomWalk.Spine
