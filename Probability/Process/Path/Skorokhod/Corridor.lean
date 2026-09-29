import Mathlib.Topology.UnitInterval
import Probability.ConvergenceInDistribution.Portmanteau
import Topology.Cadlag.Skorokhod.Corridor

/-!
# Corridor events for càdlàg stochastic processes

This file applies Portmanteau to uniformly interior corridor events in the
Skorokhod `J₁` path space.
-/

open Filter MeasureTheory
open scoped Topology

namespace ProbabilityTheory

variable {I Ω' : Type*} {Ω : I → Type*}
  {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : I) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {X : (i : I) → Ω i → CadlagPath unitInterval ℝ}
  {Z : Ω' → CadlagPath unitInterval ℝ}
  {l : Filter I}

/-- Portmanteau lower bound for a positive-margin corridor in Skorokhod
path space. -/
theorem MeasureTheory.TendstoInDistribution.measure_skorokhodCorridor_le_liminf
    (h : TendstoInDistribution X l Z μ μ') (lower upper : ℝ) :
    μ'.map Z (Skorokhod.rangeInOpenInterval lower upper) ≤
      l.liminf (fun i =>
        (μ i).map (X i) (Skorokhod.rangeInOpenInterval lower upper)) :=
  h.measure_map_le_liminf_of_isOpen
    (Skorokhod.isOpen_rangeInOpenInterval lower upper)

/-- Portmanteau upper bound for a closed interval corridor in Skorokhod path
space. -/
theorem MeasureTheory.TendstoInDistribution.limsup_measure_skorokhodCorridor_le
    (h : TendstoInDistribution X l Z μ μ') (lower upper : ℝ) :
    l.limsup (fun i =>
        (μ i).map (X i) (Skorokhod.rangeInClosedInterval lower upper)) ≤
      μ'.map Z (Skorokhod.rangeInClosedInterval lower upper) :=
  h.limsup_measure_map_le_of_isClosed
    (Skorokhod.isClosed_rangeInClosedInterval lower upper)

end ProbabilityTheory
