/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Tilted.Law

/-!
# Joint tilted displacements and reproductive marks

## Public declarations

In `ProbabilityTheory.BranchingRandomWalk.Spine`:

* `tiltedMarkedPotentialLaw φ θ μ mark` is the pushforward of the joint
  family/child bias under `(ξ,i) ↦ (φ(ξᵢ), mark(ξ,i))`.
* `tiltedMarkedPotentialLaw_fst` gives exactly the original increment marginal.
* `tiltedMarkedPotentialLaw_isProbability` gives unit mass under boundary
  normalization and measurable marks.
* `lintegral_tiltedMarkedPotentialLaw` gives
  `∫ F dν̂ = ∫ ∑ᵢ wᵢ F(φ(ξᵢ),mark(ξ,i)) dμ`.
* `lintegral_tiltedMarkedPotentialLaw_cancel` gives the marked one-generation
  many-to-one identity
  `∫ exp(-θ x) F(x,b) dν̂ = ∫ ∑_(i surviving) F(φ(ξᵢ),mark(ξ,i)) dμ`.

The mark space is arbitrary measurable. A mark may depend on the full family
and the selected child, and need not be independent of the displacement.
This is the enriched increment used by B. Mallein, *Necessary and sufficient
conditions for the convergence of the consistent maximal displacement of the
branching random walk*, §2, Theorem 2.3, arXiv:1510.00602v2, and the marked
many-to-one computation in the proof of Lemma 3.3. The bias and cancellation
are inherited from `tiltedFamilyChildLaw`; no second spinal bias is constructed.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk.Spine
open MeasureTheory Combinatorics.Branching
open scoped ENNReal Classical

variable {ι X M : Type*} [Countable ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace X] [MeasurableSpace M]

/-- Read a displacement and an arbitrary joint reproductive mark from the
original biased family/child pair. -/
noncomputable def tiltedMarkedPotentialLaw (φ : Potential X) (θ : ℝ)
    (μ : Measure (Step ι X)) (mark : Step ι X × ι → M) : Measure (ℝ × M) :=
  (tiltedFamilyChildLaw φ θ μ).map
    (fun p => (p.1.potentialValue' φ p.2, mark p))

private lemma measurable_markedPotential (φ : Potential X)
    {mark : Step ι X × ι → M} (hm : Measurable mark) :
    Measurable (fun p : Step ι X × ι => (p.1.potentialValue' φ p.2, mark p)) :=
  (measurable_from_prod_countable_left
    (fun i => Step.potentialValue'_measurable φ i)).prodMk hm

theorem tiltedMarkedPotentialLaw_fst (φ : Potential X) (θ : ℝ)
    (μ : Measure (Step ι X)) {mark : Step ι X × ι → M} (hm : Measurable mark) :
    (tiltedMarkedPotentialLaw φ θ μ mark).map Prod.fst =
      tiltedPotentialLaw φ θ μ := by
  rw [tiltedMarkedPotentialLaw, Measure.map_map measurable_fst
    (measurable_markedPotential φ hm)]
  exact tiltedFamilyChildLaw_map_potential φ θ μ

theorem tiltedMarkedPotentialLaw_isProbability (φ : Potential X)
    (μ : Measure (Step ι X)) (hboundary : HasBoundaryNormalization φ μ)
    {mark : Step ι X × ι → M} (hm : Measurable mark) :
    IsProbabilityMeasure (tiltedMarkedPotentialLaw φ (-1) μ mark) := by
  have := tiltedFamilyChildLaw_isProbability φ μ hboundary
  constructor
  rw [tiltedMarkedPotentialLaw, Measure.map_apply (measurable_markedPotential φ hm)
    MeasurableSet.univ]
  simp

theorem lintegral_tiltedMarkedPotentialLaw (φ : Potential X) (θ : ℝ)
    (μ : Measure (Step ι X)) {mark : Step ι X × ι → M} (hm : Measurable mark)
    {F : ℝ × M → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F p ∂tiltedMarkedPotentialLaw φ θ μ mark) =
      ∫⁻ ξ, ∑' i, realizedPotentialWeight φ θ ξ i *
        F (ξ.potentialValue' φ i, mark (ξ, i)) ∂μ := by
  rw [tiltedMarkedPotentialLaw, lintegral_map hF (measurable_markedPotential φ hm)]
  exact lintegral_tiltedFamilyChildLaw φ θ μ (hF.comp (measurable_markedPotential φ hm))

/-- The reproductive mark remains attached to the displacement during
compensation; no product of separate marginal laws is used. -/
theorem lintegral_tiltedMarkedPotentialLaw_cancel (φ : Potential X) (θ : ℝ)
    (μ : Measure (Step ι X)) {mark : Step ι X × ι → M} (hm : Measurable mark)
    {F : ℝ × M → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, ENNReal.ofReal (Real.exp (-θ * p.1)) * F p
      ∂tiltedMarkedPotentialLaw φ θ μ mark) =
      ∫⁻ ξ, ∑' i, if survive ξ i then
        F (ξ.potentialValue' φ i, mark (ξ, i)) else 0 ∂μ := by
  have hG : Measurable (fun p : ℝ × M =>
      ENNReal.ofReal (Real.exp (-θ * p.1)) * F p) := by fun_prop
  rw [tiltedMarkedPotentialLaw, lintegral_map hG (measurable_markedPotential φ hm)]
  exact lintegral_tiltedFamilyChildLaw_cancel φ θ μ
    (hF.comp (measurable_markedPotential φ hm))

end ProbabilityTheory.BranchingRandomWalk.Spine
