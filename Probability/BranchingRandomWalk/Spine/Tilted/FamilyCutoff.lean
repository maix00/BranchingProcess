/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Tilted.FamilyChild

/-!
# Truncating the total reproductive weight

## Public declarations

In `ProbabilityTheory.BranchingRandomWalk.Spine`:

* `lintegral_crossPotentialWeight_on_totalWeight_le` proves
  `∫_(W ≤ K) C dμ ≤ K ∫ W dμ`, without any global cross-moment assumption.
* `lintegral_crossPotentialWeight_on_totalWeight_le_of_boundary` gives
  `C_K ≤ K` under boundary normalization, in particular `C_L ≤ exp(α L)`.
* `tiltedFamilyChildLaw_restrict_family` identifies the unchanged spinal
  law restricted by a family event `A` with the joint bias of `μ.restrict A`.
  This is a restriction, with no new normalization or centering assertion.

This is the whole-family cutoff used to implement the reproductive-mark
restriction in B. Mallein, *N-branching random walk with α-stable spine*
(2015), proof of Lemma 3.4, arXiv:1503.03762. It is also the cutoff needed
for the finite-variance specialization of the marked-walk argument in
B. Mallein, *Necessary and sufficient conditions for the convergence of the
consistent maximal displacement of the branching random walk*, proof of
Lemma 3.3, arXiv:1510.00602v2. The displayed cross bound follows directly
from `C ≤ W² ≤ K W`; it does not assert that the truncated law satisfies
the boundary condition.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk.Spine
open MeasureTheory Combinatorics.Branching
open scoped ENNReal

theorem lintegral_crossPotentialWeight_on_totalWeight_le {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (μ : Measure (Step ι X)) (K : ℝ≥0∞) :
    (∫⁻ ξ in {ξ | totalPotentialWeight φ θ ξ ≤ K}, crossPotentialWeight φ θ ξ ∂μ) ≤
      K * ∫⁻ ξ, totalPotentialWeight φ θ ξ ∂μ := by
  have hset : MeasurableSet {ξ : Step ι X | totalPotentialWeight φ θ ξ ≤ K} :=
    measurableSet_le (totalPotentialWeight_measurable φ θ) measurable_const
  rw [← lintegral_indicator hset,
    ← lintegral_const_mul K (totalPotentialWeight_measurable φ θ)]
  apply lintegral_mono
  intro ξ
  by_cases hξ : totalPotentialWeight φ θ ξ ≤ K
  · rw [Set.indicator_of_mem hξ]
    exact (crossPotentialWeight_le_totalPotentialWeight_sq φ θ ξ).trans
      (by simpa only [pow_two] using mul_le_mul_left hξ (totalPotentialWeight φ θ ξ))
  · simp [hξ]

theorem lintegral_crossPotentialWeight_on_totalWeight_le_of_boundary {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ι X))
    (h : HasBoundaryNormalization φ μ) (K : ℝ≥0∞) :
    (∫⁻ ξ in {ξ | totalPotentialWeight φ (-1) ξ ≤ K},
      crossPotentialWeight φ (-1) ξ ∂μ) ≤ K := by
  have hb := lintegral_crossPotentialWeight_on_totalWeight_le φ (-1) μ K
  change (∫⁻ ξ, totalPotentialWeight φ (-1) ξ ∂μ) = 1 at h
  simpa only [h, mul_one] using hb

/-- Restricting the original family/child law retains exactly the original
weights on the accepted family event; no rebiased increment law is introduced. -/
theorem tiltedFamilyChildLaw_restrict_family {ι X : Type*}
    [Countable ι] [MeasurableSpace ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (μ : Measure (Step ι X))
    {A : Set (Step ι X)} (hA : MeasurableSet A) :
    (tiltedFamilyChildLaw φ θ μ).restrict (Prod.fst ⁻¹' A) =
      tiltedFamilyChildLaw φ θ (μ.restrict A) := by
  apply Measure.ext
  intro B hB
  rw [Measure.restrict_apply hB, ← lintegral_indicator_one
    (hB.inter (hA.preimage measurable_fst)), ← lintegral_indicator_one hB]
  change (∫⁻ p, (B ∩ Prod.fst ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) p
    ∂tiltedFamilyChildLaw φ θ μ) =
      ∫⁻ p, B.indicator (fun _ => (1 : ℝ≥0∞)) p
        ∂tiltedFamilyChildLaw φ θ (μ.restrict A)
  rw [lintegral_tiltedFamilyChildLaw φ θ μ
      (measurable_const.indicator (hB.inter (hA.preimage measurable_fst))),
    lintegral_tiltedFamilyChildLaw φ θ (μ.restrict A)
      (measurable_const.indicator hB), ← lintegral_indicator hA]
  apply lintegral_congr
  intro ξ
  by_cases hξ : ξ ∈ A
  · rw [Set.indicator_of_mem hξ]
    apply tsum_congr
    intro i
    by_cases hBξ : (ξ, i) ∈ B <;> simp [hξ, hBξ]
  · rw [Set.indicator_of_notMem hξ]
    simp [hξ]

end ProbabilityTheory.BranchingRandomWalk.Spine
