/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Probability.ConvergenceInDistribution.Portmanteau
public import Topology.ContinuousMap.Corridor

public section

/-!
# Corridor events for continuous stochastic processes

This file supplies the probability layer for deterministic continuous-path
corridors.  In particular, functional convergence in distribution gives the
Portmanteau lower bound for every open horizontal corridor.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace ProbabilityTheory

variable {I T Ω' : Type*} {Ω : I → Type*}
  {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : I) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  [TopologicalSpace T] [CompactSpace T]
  [MeasurableSpace C(T, ℝ)]
  [OpensMeasurableSpace C(T, ℝ)] [HasOuterApproxClosed C(T, ℝ)]
  {X : (i : I) → Ω i → C(T, ℝ)} {Z : Ω' → C(T, ℝ)}
  {l : Filter I}

/-- Portmanteau lower bound for the event that an entire continuous path
stays inside a fixed nonempty open interval. -/
theorem MeasureTheory.TendstoInDistribution.measure_horizontalCorridor_le_liminf
    (h : TendstoInDistribution X l Z μ μ')
    {lower upper : ℝ} (hlowerUpper : lower < upper) :
    μ'.map Z (ContinuousMap.rangeInOpenInterval lower upper) ≤
      l.liminf (fun i =>
        (μ i).map (X i) (ContinuousMap.rangeInOpenInterval lower upper)) :=
  h.measure_map_le_liminf_of_isOpen
    (ContinuousMap.isOpen_rangeInOpenInterval hlowerUpper)

/-- Portmanteau upper bound for the event that an entire continuous path
stays inside a fixed closed interval. -/
theorem MeasureTheory.TendstoInDistribution.limsup_measure_horizontalCorridor_le
    [Nonempty T] (h : TendstoInDistribution X l Z μ μ')
    (lower upper : ℝ) :
    l.limsup (fun i =>
        (μ i).map (X i) (ContinuousMap.rangeInClosedInterval lower upper)) ≤
      μ'.map Z (ContinuousMap.rangeInClosedInterval lower upper) :=
  h.limsup_measure_map_le_of_isClosed
    (ContinuousMap.isClosed_rangeInClosedInterval lower upper)

end ProbabilityTheory
