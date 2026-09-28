import Probability.ConvergenceInDistribution.Basic

/-!
# Event probabilities under convergence in distribution

Portmanteau bounds exposed directly for `TendstoInDistribution`.
-/

open Filter ProbabilityTheory Set
open scoped Topology

namespace MeasureTheory

variable {I E Ω' : Type*} {Ω : I → Type*}
  {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : I) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {mE : MeasurableSpace E} [TopologicalSpace E] [OpensMeasurableSpace E]
  [HasOuterApproxClosed E]
  {X : (i : I) → Ω i → E} {Z : Ω' → E} {l : Filter I}

/-- Portmanteau lower bound for an open event, stated for random variables
converging in distribution. -/
theorem TendstoInDistribution.measure_map_le_liminf_of_isOpen
    (h : TendstoInDistribution X l Z μ μ')
    {G : Set E} (hG : IsOpen G) :
    μ'.map Z G ≤ l.liminf (fun i => (μ i).map (X i) G) := by
  exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto h.tendsto hG

/-- Portmanteau upper bound for a closed event, stated for random variables
converging in distribution. -/
theorem TendstoInDistribution.limsup_measure_map_le_of_isClosed
    (h : TendstoInDistribution X l Z μ μ')
    {F : Set E} (hF : IsClosed F) :
    l.limsup (fun i => (μ i).map (X i) F) ≤ μ'.map Z F := by
  exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto hF

/-- Event probabilities converge when the limiting law gives no mass to the
event boundary. -/
theorem TendstoInDistribution.tendsto_measure_map_of_null_frontier
    (h : TendstoInDistribution X l Z μ μ')
    {event : Set E} (hboundary : μ'.map Z (frontier event) = 0) :
    Tendsto (fun i => (μ i).map (X i) event) l
      (nhds (μ'.map Z event)) := by
  exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    h.tendsto hboundary

end MeasureTheory
