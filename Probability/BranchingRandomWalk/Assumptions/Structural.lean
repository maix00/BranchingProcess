/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Measure.ExponentialWeight
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Structural assumptions on the child law

These predicates express structural assumptions on a branching law. A
raw law is never assumed to have ordered slots. Indexed children are read from
the sorted pushforward supplied by `StepLaw.ordering`.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching MeasureTheory



/-- The boundary normalization `E[∑ exp(-Ξᵢ)] = 1`. This sum is invariant
under slot permutations, so it is evaluated directly on the raw law. -/
def HasBoundaryNormalization {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X)
    (μ : Measure (Combinatorics.Branching.Step ι X)) : Prop :=
  ∫⁻ ξ, totalPotentialWeight φ (-1) ξ ∂μ = 1

/-- Boundary normalization forces the negative exponential offspring weight
to be finite almost surely. -/
theorem HasBoundaryNormalization.ae_totalPotentialWeight_ne_top
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (h : HasBoundaryNormalization φ μ) :
    ∀ᵐ ξ ∂μ, totalPotentialWeight φ (-1) ξ ≠ ∞ := by
  have hintegral :
      (∫⁻ ξ, totalPotentialWeight φ (-1) ξ ∂μ) ≠ ∞ := by
    rw [h]
    exact ENNReal.one_ne_top
  filter_upwards [ae_lt_top
    (totalPotentialWeight_measurable φ (-1)) hintegral] with ξ hξ
  exact hξ.ne

/-- Boundary normalization makes the negative-exponential offspring weight
an integrable real-valued observable after taking `ENNReal.toReal`. This is
the one-step `L¹` bound used to control negative endpoint excursions. -/
theorem HasBoundaryNormalization.integrable_totalPotentialWeight_toReal
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (h : HasBoundaryNormalization φ μ) :
    Integrable (fun ξ => (totalPotentialWeight φ (-1) ξ).toReal) μ := by
  apply integrable_toReal_of_lintegral_ne_top
  · exact (totalPotentialWeight_measurable φ (-1)).aemeasurable
  · rw [h]
    exact ENNReal.one_ne_top

/-- Under boundary normalization, the negative part of any fixed child's
potential is integrable. Presence contributes one term to the total
exponential weight; absence gives the zero-defaulted potential `0`. -/
theorem HasBoundaryNormalization.integrable_negativePotentialValue
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (i : ι) (h : HasBoundaryNormalization φ μ) :
    Integrable (fun ξ => max (-(ξ.potentialValue' φ i)) 0) μ := by
  let negativePart : Combinatorics.Branching.Step ι X → ℝ :=
    fun ξ => max (-(ξ.potentialValue' φ i)) 0
  have hnegativeMeasurable : Measurable negativePart := by
    dsimp [negativePart]
    exact (Step.potentialValue'_measurable φ i).neg.max measurable_const
  have hweight := h.integrable_totalPotentialWeight_toReal φ μ
  apply hweight.mono' hnegativeMeasurable.aestronglyMeasurable
  filter_upwards [h.ae_totalPotentialWeight_ne_top φ μ] with ξ hfinite
  have hg : 0 ≤ negativePart ξ := le_max_right _ _
  have hpoint : ENNReal.ofReal (negativePart ξ) ≤
      totalPotentialWeight φ (-1) ξ := by
    by_cases hi : survive ξ i
    · have hexp : negativePart ξ ≤ Real.exp (-(ξ.potentialValue' φ i)) := by
        dsimp [negativePart]
        refine max_le ?_ ?_
        · linarith [Real.add_one_le_exp (-(ξ.potentialValue' φ i))]
        · exact (Real.exp_pos _).le
      have hterm : ENNReal.ofReal (Real.exp (-(ξ.potentialValue' φ i))) =
          realizedPotentialWeight φ (-1) ξ i := by
        simp [realizedPotentialWeight, hi]
      calc
        ENNReal.ofReal (negativePart ξ) ≤
            ENNReal.ofReal (Real.exp (-(ξ.potentialValue' φ i))) :=
          ENNReal.ofReal_le_ofReal hexp
        _ = realizedPotentialWeight φ (-1) ξ i := hterm
        _ ≤ totalPotentialWeight φ (-1) ξ := by
          unfold totalPotentialWeight
          exact ENNReal.le_tsum i
    · have hnone : ξ i = none := by
        simpa [survive_iff_ne_none] using hi
      have hvalue : ξ.potentialValue' φ i = 0 := by
        simp [Step.potentialValue', Step.potentialAt?, hnone]
      simp [negativePart, hvalue]
  have hbound : negativePart ξ ≤
      (totalPotentialWeight φ (-1) ξ).toReal := by
    calc
      negativePart ξ = (ENNReal.ofReal (negativePart ξ)).toReal :=
        (ENNReal.toReal_ofReal hg).symm
      _ ≤ (totalPotentialWeight φ (-1) ξ).toReal :=
        ENNReal.toReal_mono hfinite hpoint
  simpa only [Real.norm_eq_abs, abs_of_nonneg hg,
    abs_of_nonneg ENNReal.toReal_nonneg] using hbound

end ProbabilityTheory.BranchingRandomWalk
