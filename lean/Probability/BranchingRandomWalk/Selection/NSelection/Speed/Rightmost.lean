/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Speed.KingmanInterface
public import Probability.BranchingRandomWalk.Selection.NSelection.Speed.OrderDualEnvironment

/-!
# Rightmost speed for a fixed number of selected particles

The rightmost process is expressed through the `OrderDual` observation of
the original offspring law. Its right boundary and first-moment conditions
are stated on that same law. The existing leftmost Kingman result is applied
to the ordered dual observation, whose real potential records the negative
of the original displacement.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

/-- The rightmost first-moment condition on the original law, read through
the ordering stored in its order-dual `StepLaw` model. The compatibility of
that model with the original law is stated in the speed theorem below. -/
def HasRightmostFirstMoment
    (μ : Measure (Step ℕ ℝ))
    (L : StepLaw ℕ ℕ (OrderDual ℝ)) : Prop :=
  Integrable (fun ξ => L.leftmostPositivePart (stepOrderDual ξ)) μ

/-- The rightmost endpoint path is the negative of the leftmost path in the
order-dual potential coordinates. -/
noncomputable def rightmostRunOfOrderDualEnvironment {N : ℕ}
    (ω : GenerationEnvironment N)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (ω t))
    (initial : Fin N → ℝ) : ℕ → Fin N → ℝ :=
  fun n i => -infiniteOffspringRun ω hgood (fun j => -initial j) n i

/-- The totalized, measurable version of the rightmost path used in the
`L¹` conclusion. -/
noncomputable def measurableRepairedRightmostRun {N : ℕ} (n : ℕ)
    (initial : Fin N → ℝ) (ω : GenerationEnvironment N) : Fin N → ℝ :=
  fun i => -measurableRepairedInfiniteOffspringRun n (initial, ω) i

/-- The exact-`N` rightmost trajectory has an almost-sure speed and converges
to that speed in `L¹`. The `StepLaw` argument is the existing canonical
measurable ordering model for the order-dual observation of the same original
offspring law; the probabilistic hypotheses themselves are stated on that
original law. -/
theorem infiniteOffspringRun_rightmost_ae_hasAsymptoticSpeed_and_L1_of_stepLaw
    {N : ℕ} (hN : 0 < N)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (L : StepLaw ℕ ℕ (OrderDual ℝ))
    (hpotential : L.potential = orderDualPotential)
    (hraw : L.raw = Measure.map stepOrderDual μ)
    (hboundary : HasRightBoundaryNormalization μ)
    (hnonempty : μ nonemptySupport = 1)
    (hfirst : HasRightmostFirstMoment μ L) :
    ∃ cRight : ℝ,
      (∀ᵐ ω ∂generationEnvironmentLaw
          L.sortedPotentialImage N,
        ∃ hgood : ∀ t, IsGoodInfiniteOffspringBatch (ω t),
          Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
            (𝕜 := ℝ)
            (fun n => rightmostRunOfOrderDualEnvironment ω hgood
              (fun _ => 0) n ⟨0, hN⟩)
            cRight) ∧
      Tendsto
        (fun n : ℕ => eLpNorm
          (fun ω : GenerationEnvironment N =>
            (n : ℝ)⁻¹ *
              measurableRepairedRightmostRun n (fun _ => 0) ω ⟨0, hN⟩ - cRight)
          (1 : ℝ≥0∞)
          (generationEnvironmentLaw
            L.sortedPotentialImage N))
        atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure L.raw := by
    rw [hraw]
    infer_instance
  have hboundaryDual : HasBoundaryNormalization L.potential L.raw := by
    rw [hpotential, hraw]
    exact HasRightBoundaryNormalization.orderDual μ hboundary
  have hnonemptyDual : L.raw nonemptySupport = 1 := by
    rw [hraw]
    rw [Measure.map_apply measurable_stepOrderDual
      nonemptySupport_measurable]
    have hpreimage : stepOrderDual ⁻¹' nonemptySupport = nonemptySupport := by
      ext ξ
      exact mem_nonemptySupport_stepOrderDual_iff ξ
    rw [hpreimage]
    exact hnonempty
  have hfirstDual : HasLeftmostFirstMoment L := by
    change Integrable L.leftmostPositivePart L.raw
    rw [hraw]
    exact (integrable_map_measure
      L.leftmostPositivePart_measurable.aestronglyMeasurable
      measurable_stepOrderDual.aemeasurable).mpr hfirst
  obtain ⟨c, hspeed, hL1⟩ :=
    infiniteOffspringRun_leftmost_ae_hasAsymptoticSpeed_and_L1_of_stepLaw
      hN L hboundaryDual hnonemptyDual hfirstDual
  refine ⟨c, ?_, ?_⟩
  · filter_upwards [hspeed] with ω hω
    rcases hω with ⟨hgood, hleftSpeed⟩
    refine ⟨hgood, ?_⟩
    change Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ *
        infiniteOffspringRun ω hgood (fun _ => 0) n ⟨0, hN⟩)
      atTop (𝓝 (-c)) at hleftSpeed
    have hneg := hleftSpeed.neg
    simpa [Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed,
      rightmostRunOfOrderDualEnvironment, neg_zero, mul_neg, smul_neg] using hneg
  · have hseq :
      (fun n : ℕ => eLpNorm
        (fun ω : GenerationEnvironment N =>
          (n : ℝ)⁻¹ *
            measurableRepairedRightmostRun n (fun _ => 0) ω ⟨0, hN⟩ - c)
        (1 : ℝ≥0∞)
        (generationEnvironmentLaw L.sortedPotentialImage N)) =
      fun n : ℕ => eLpNorm
        (fun ω : GenerationEnvironment N =>
          (n : ℝ)⁻¹ * measurableRepairedInfiniteOffspringRun n
            ((fun _ : Fin N => (0 : ℝ)), ω) ⟨0, hN⟩ - (-c))
        (1 : ℝ≥0∞)
        (generationEnvironmentLaw L.sortedPotentialImage N) := by
      funext n
      have hfun :
          (fun ω : GenerationEnvironment N =>
            (n : ℝ)⁻¹ *
              measurableRepairedRightmostRun n (fun _ => 0) ω ⟨0, hN⟩ - c) =
          fun ω => -((n : ℝ)⁻¹ *
            measurableRepairedInfiniteOffspringRun n
              ((fun _ : Fin N => (0 : ℝ)), ω) ⟨0, hN⟩ - (-c)) := by
        funext ω
        simp [measurableRepairedRightmostRun]
        ring
      rw [hfun]
      exact eLpNorm_neg _ _ _
    have hL1right : Tendsto
        (fun n : ℕ => eLpNorm
          (fun ω : GenerationEnvironment N =>
            (n : ℝ)⁻¹ *
              measurableRepairedRightmostRun n (fun _ => 0) ω ⟨0, hN⟩ - c)
          (1 : ℝ≥0∞) (generationEnvironmentLaw L.sortedPotentialImage N))
        atTop (𝓝 0) := by
      rw [hseq]
      exact hL1
    exact hL1right

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
