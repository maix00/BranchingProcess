/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Step.Ordering.Law
public import Probability.BranchingRandomWalk.Spine.Tilted.Marked
public import Probability.BranchingRandomWalk.Assumptions.SpinalWeightTail

/-!
# Spinal laws and reproductive tails under offspring ordering

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.StepLaw.tiltedMarkedPotentialLaw_totalWeight_sortedPotentialImage`:
  the existing biased joint law of `(φ(child),W_φ(family))` is unchanged by
  ordering and potential projection, for every tilt `θ` and raw measure.
* `ProbabilityTheory.BranchingRandomWalk.StepLaw.tiltedPotentialLaw_sortedPotentialImage`:
  `ν_(sortedPotentialImage,realPotential,θ)=ν_(raw,φ,θ)`.
* `ProbabilityTheory.BranchingRandomWalk.StepLaw.sortedPotentialImage_hasSpinalWeightTail_iff`:
  `HasSpinalWeightTail realPotential sortedPotentialImage ↔
   HasSpinalWeightTail φ raw`. No normalization, variance or moment hypothesis
  is required for any of these identities.

Ordering preserves the complete offspring point measure. The existing marked
spinal integral formula therefore gives the same weighted joint law, rather
than a second bias construction. The relative reproductive mark is
`log(W)+φ(child)`, as in B. Mallein, *N-branching random walk with α-stable
spine*, §2.1 and Theorem 1.1, condition (1.9), arXiv:1503.03762v2.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk
open MeasureTheory Combinatorics.Branching Spine
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

/-- Reordering and scalar projection preserve the full biased displacement /
family-weight joint law, before normalization or moment assumptions. -/
theorem StepLaw.tiltedMarkedPotentialLaw_totalWeight_sortedPotentialImage
    {ι κ X : Type*} [Countable ι] [Countable κ] [LT κ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] [MeasurableSpace X]
    (L : StepLaw ι κ X) (θ : ℝ) :
    tiltedMarkedPotentialLaw realPotential θ L.sortedPotentialImage
      (fun p => totalPotentialWeight realPotential (-1) p.1) =
      tiltedMarkedPotentialLaw L.potential θ L.raw
        (fun p => totalPotentialWeight L.potential (-1) p.1) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_tiltedMarkedPotentialLaw (mark := fun p => totalPotentialWeight realPotential (-1) p.1)
      realPotential θ L.sortedPotentialImage
      ((totalPotentialWeight_measurable realPotential (-1)).comp measurable_fst) hf,
    lintegral_tiltedMarkedPotentialLaw (mark := fun p => totalPotentialWeight L.potential (-1) p.1)
      L.potential θ L.raw
      ((totalPotentialWeight_measurable L.potential (-1)).comp measurable_fst) hf]
  have hm : Measurable (fun ξ : Step κ ℝ => ∑' i : κ,
      realizedPotentialWeight realPotential θ ξ i *
        f (ξ.potentialValue' realPotential i, totalPotentialWeight realPotential (-1) ξ)) := by
    apply Measurable.tsum
    intro i
    exact (realizedPotentialWeight_measurable realPotential θ i).mul
      (hf.comp ((Step.potentialValue'_measurable realPotential i).prodMk
        (totalPotentialWeight_measurable realPotential (-1))))
  rw [StepLaw.sortedPotentialImage, lintegral_map hm (Step.map_measurable L.potential.measurable_toFun)]
  have himage (ξ : Step κ X) :
      (∑' i : κ, realizedPotentialWeight realPotential θ (ξ.map L.potential) i *
        f ((ξ.map L.potential).potentialValue' realPotential i,
          totalPotentialWeight realPotential (-1) (ξ.map L.potential))) =
        ∑' i : κ, realizedPotentialWeight L.potential θ ξ i *
          f (ξ.potentialValue' L.potential i, totalPotentialWeight L.potential (-1) ξ) := by
    rw [Step.totalPotentialWeight_map]
    apply tsum_congr
    intro i
    cases hi : ξ i <;> simp [Step.map, realizedPotentialWeight, Step.potentialValue',
      Step.potentialAt?, realPotential, survive, hi]
  simp_rw [himage]
  have hm' : Measurable (fun ξ : Step κ X => ∑' i : κ,
      realizedPotentialWeight L.potential θ ξ i *
        f (ξ.potentialValue' L.potential i, totalPotentialWeight L.potential (-1) ξ)) := by
    apply Measurable.tsum
    intro i
    exact (realizedPotentialWeight_measurable L.potential θ i).mul
      (hf.comp ((Step.potentialValue'_measurable L.potential i).prodMk
        (totalPotentialWeight_measurable L.potential (-1))))
  rw [StepLaw.sorted, lintegral_map hm' L.ordering.measurable_ordered]
  apply lintegral_congr
  intro ξ
  rw [L.totalPotentialWeight_ordering ξ,
    ← lintegral_stepPointMeasure_potential (f := fun z => f (z, totalPotentialWeight L.potential (-1) ξ))
      L.potential θ (L.ordering ξ) (hf.comp (measurable_id.prodMk measurable_const)),
    L.sorted_pointMeasure ξ,
    lintegral_stepPointMeasure_potential (f := fun z => f (z, totalPotentialWeight L.potential (-1) ξ))
      L.potential θ ξ (hf.comp (measurable_id.prodMk measurable_const))]

/-- The unnormalized scalar spine law is the common displacement marginal of
one invariant joint law. -/
theorem StepLaw.tiltedPotentialLaw_sortedPotentialImage
    {ι κ X : Type*} [Countable ι] [Countable κ] [LT κ] [MeasurableSpace X]
    (L : StepLaw ι κ X) (θ : ℝ) :
    tiltedPotentialLaw realPotential θ L.sortedPotentialImage =
      tiltedPotentialLaw L.potential θ L.raw := by
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  let : MeasurableSpace κ := ⊤
  let : MeasurableSingletonClass κ := ⟨fun _ => trivial⟩
  have h := congrArg (fun ν : Measure (ℝ × ℝ≥0∞) => ν.map Prod.fst)
    (L.tiltedMarkedPotentialLaw_totalWeight_sortedPotentialImage θ)
  simpa only [tiltedMarkedPotentialLaw_fst (mark := fun p => totalPotentialWeight realPotential (-1) p.1)
    realPotential θ L.sortedPotentialImage
    ((totalPotentialWeight_measurable realPotential (-1)).comp measurable_fst),
    tiltedMarkedPotentialLaw_fst (mark := fun p => totalPotentialWeight L.potential (-1) p.1)
    L.potential θ L.raw
      ((totalPotentialWeight_measurable L.potential (-1)).comp measurable_fst)] using h

/-- Mallein's condition (1.9) is invariant under the measurable ordered
realization, without strengthening it to a moment condition. -/
theorem StepLaw.sortedPotentialImage_hasSpinalWeightTail_iff
    {ι κ X : Type*} [Countable ι] [Countable κ] [LT κ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] [MeasurableSpace X]
    (L : StepLaw ι κ X) :
    HasSpinalWeightTail realPotential L.sortedPotentialImage ↔
      HasSpinalWeightTail L.potential L.raw := by
  let g := fun p : ℝ × ℝ≥0∞ => Real.log p.2.toReal + p.1
  have hg : Measurable g := by fun_prop
  have hmφ : Measurable (fun p : Step ι X × ι =>
      (p.1.potentialValue' L.potential p.2, totalPotentialWeight L.potential (-1) p.1)) :=
    (measurable_from_prod_countable_left
      (fun i => Step.potentialValue'_measurable L.potential i)).prodMk
      ((totalPotentialWeight_measurable L.potential (-1)).comp measurable_fst)
  have hmℝ : Measurable (fun p : Step κ ℝ × κ =>
      (p.1.potentialValue' realPotential p.2, totalPotentialWeight realPotential (-1) p.1)) :=
    (measurable_from_prod_countable_left
      (fun i => Step.potentialValue'_measurable realPotential i)).prodMk
      ((totalPotentialWeight_measurable realPotential (-1)).comp measurable_fst)
  have hφ := hasVanishingQuadraticTail_map_iff
    (μ := tiltedFamilyChildLaw L.potential (-1) L.raw) _ hmφ g hg
  have hℝ := hasVanishingQuadraticTail_map_iff
    (μ := tiltedFamilyChildLaw realPotential (-1) L.sortedPotentialImage) _ hmℝ g hg
  change HasVanishingQuadraticTail
    (tiltedMarkedPotentialLaw L.potential (-1) L.raw _) g ↔ _ at hφ
  change HasVanishingQuadraticTail
    (tiltedMarkedPotentialLaw realPotential (-1) L.sortedPotentialImage _) g ↔ _ at hℝ
  rw [L.tiltedMarkedPotentialLaw_totalWeight_sortedPotentialImage (-1)] at hℝ
  change _ ↔ HasSpinalWeightTail L.potential L.raw at hφ
  change _ ↔ HasSpinalWeightTail realPotential L.sortedPotentialImage at hℝ
  exact hℝ.symm.trans hφ

end ProbabilityTheory.BranchingRandomWalk
