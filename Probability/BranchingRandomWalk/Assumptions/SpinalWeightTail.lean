/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Tilted.Law
public import MeasureTheory.Measure.Tails.Quadratic

/-!
# Weak reproductive tails under the original spinal measure

## Public declarations

In `ProbabilityTheory.BranchingRandomWalk`:

* `relativeSpinalWeight φ (ξ,i)` is `log W(ξ) + φ(ξᵢ)`.
* `relativeSpinalWeight_measurable` gives measurability of the relative mark.
* `relativeSpinalWeight_nonneg` proves `log W + X ≥ 0` at a finite-weight surviving slot;
  `ae_relativeSpinalWeight_nonneg` gives this almost surely under the spinal law.
* `HasSpinalWeightTail φ μ` means `x² μ̂{log W + X > x} → 0`.
* `hasSpinalWeightTail_iff_totalWeightTail` proves that this is equivalent to
  `x² (μ.withDensity W){log W > x} → 0` under boundary normalization and
  finite spinal second moment. No logarithmic second moment is assumed.

The deterministic `logTotalPotentialWeight` observation is imported from
`Combinatorics/BranchingWalk/Step/Measure/ExponentialWeight.lean`.
Here `μ̂ = Spine.tiltedFamilyChildLaw φ (-1) μ` is the existing joint family/child
bias and `X = φ(ξᵢ)` has the original scalar law `Spine.tiltedPotentialLaw`.
This is condition (1.9) in B. Mallein, *N-branching random walk with α-stable
spine* (2015), Theorem 1.1, arXiv:1503.03762, reflected to leftmost selection
and specialized to finite variance. The total-weight version is condition (1.4)
in B. Mallein, *Necessary and sufficient conditions for the convergence of the
consistent maximal displacement of the branching random walk*, arXiv:1510.00602v2.

The real logarithm is totalized using `ENNReal.toReal`; under boundary
normalization the infinite-weight set is null. The zero-weight set has zero
spinal measure. Dependence between the displacement and the family weight is
retained throughout, and no independence premise is introduced.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk
open MeasureTheory Combinatorics.Branching
open Spine
open scoped ENNReal

variable {ι X : Type*} [Countable ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace X]

/-- Relative exponential family weight seen from the distinguished child. -/
noncomputable def relativeSpinalWeight (φ : Potential X) (p : Step ι X × ι) : ℝ :=
  logTotalPotentialWeight φ p.1 + p.1.potentialValue' φ p.2

theorem relativeSpinalWeight_measurable (φ : Potential X) :
    Measurable (relativeSpinalWeight (ι := ι) φ) :=
  ((logTotalPotentialWeight_measurable φ).comp measurable_fst).add
    (measurable_from_prod_countable_left (fun i => Step.potentialValue'_measurable φ i))

omit [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The selected child's own positive weight is one summand of the total;
the relative reproductive mark is therefore nonnegative at every finite-weight
family with that child present. -/
theorem relativeSpinalWeight_nonneg (φ : Potential X) (p : Step ι X × ι)
    (hfinite : totalPotentialWeight φ (-1) p.1 ≠ ∞) (hs : survive p.1 p.2) :
    0 ≤ relativeSpinalWeight φ p := by
  have hw : ENNReal.ofReal (Real.exp (-p.1.potentialValue' φ p.2)) ≤
      totalPotentialWeight φ (-1) p.1 := by
    simpa only [totalPotentialWeight, realizedPotentialWeight, hs, ↓reduceIte, neg_one_mul] using
      (le_tsum (realizedPotentialWeight φ (-1) p.1) p.2)
  have hr : Real.exp (-p.1.potentialValue' φ p.2) ≤
      (totalPotentialWeight φ (-1) p.1).toReal := by
    simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using ENNReal.toReal_mono hfinite hw
  have hp : 0 < (totalPotentialWeight φ (-1) p.1).toReal :=
    (Real.exp_pos _).trans_le hr
  have hl := (Real.le_log_iff_exp_le hp).mpr hr
  change 0 ≤ Real.log (totalPotentialWeight φ (-1) p.1).toReal +
    p.1.potentialValue' φ p.2
  linarith

theorem ae_relativeSpinalWeight_nonneg (φ : Potential X) (μ : Measure (Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) :
    ∀ᵐ p ∂tiltedFamilyChildLaw φ (-1) μ, 0 ≤ relativeSpinalWeight φ p := by
  have hraw : ∀ᵐ ξ ∂μ.withDensity (totalPotentialWeight φ (-1)),
      totalPotentialWeight φ (-1) ξ ≠ ∞ :=
    (hboundary.ae_totalPotentialWeight_ne_top φ μ).filter_mono
      (Measure.ae_le_iff_absolutelyContinuous.mpr (withDensity_absolutelyContinuous μ _))
  have hmap : ∀ᵐ ξ ∂(tiltedFamilyChildLaw φ (-1) μ).map Prod.fst,
      totalPotentialWeight φ (-1) ξ ≠ ∞ := by
    rw [tiltedFamilyChildLaw_fst]
    exact hraw
  filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hmap,
    ae_tiltedFamilyChildLaw_survive φ (-1) μ] with p hp hs
  exact relativeSpinalWeight_nonneg φ p hp hs

/-- Mallein's weak tail condition on the relative reproductive mark. -/
def HasSpinalWeightTail (φ : Potential X) (μ : Measure (Step ι X)) : Prop :=
  HasVanishingQuadraticTail (tiltedFamilyChildLaw φ (-1) μ) (relativeSpinalWeight φ)

/-- Finite spinal variance makes the relative-mark and total-log-weight
conditions equivalent, by two half-threshold union bounds.
This compares Mallein (2015), arXiv:1503.03762, condition (1.9), with
Mallein, arXiv:1510.00602v2, condition (1.4), in the finite-variance case. -/
theorem hasSpinalWeightTail_iff_totalWeightTail
    (φ : Potential X) (μ : Measure (Step ι X))
    (hboundary : HasBoundaryNormalization φ μ)
    (hsq : Integrable (fun x : ℝ => x ^ 2) (tiltedPotentialLaw φ (-1) μ)) :
    HasSpinalWeightTail φ μ ↔
      HasVanishingQuadraticTail (μ.withDensity (totalPotentialWeight φ (-1)))
        (logTotalPotentialWeight φ) := by
  let P := tiltedFamilyChildLaw φ (-1) μ
  have : IsProbabilityMeasure P := tiltedFamilyChildLaw_isProbability φ μ hboundary
  have hX : Measurable (fun p : Step ι X × ι => p.1.potentialValue' φ p.2) :=
    measurable_from_prod_countable_left (fun i => Step.potentialValue'_measurable φ i)
  have hsq' : Integrable (fun p : Step ι X × ι => (p.1.potentialValue' φ p.2) ^ 2) P := by
    have hi : Integrable (fun x : ℝ => x ^ 2) (P.map
        (fun p => p.1.potentialValue' φ p.2)) := by
      simpa only [P, tiltedFamilyChildLaw_map_potential] using hsq
    exact hi.comp_measurable hX
  have he := hasVanishingQuadraticTail_add_iff_of_integrable_sq
    (f := fun p : Step ι X × ι => logTotalPotentialWeight φ p.1) hX hsq'
  have hf := hasVanishingQuadraticTail_map_iff (μ := P)
    Prod.fst measurable_fst (logTotalPotentialWeight φ)
    (logTotalPotentialWeight_measurable φ)
  rw [show P.map Prod.fst = μ.withDensity (totalPotentialWeight φ (-1)) from
    tiltedFamilyChildLaw_fst φ (-1) μ] at hf
  exact he.trans hf.symm

end ProbabilityTheory.BranchingRandomWalk
