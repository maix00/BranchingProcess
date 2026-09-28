import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Metrizable.Basic

/-!
# Event probabilities under convergence in distribution

This file exposes the Portmanteau bounds directly from
`TendstoInDistribution`.  The underlying weak-convergence results are those
already provided by mathlib for `ProbabilityMeasure`.
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

omit [HasOuterApproxClosed E] in
/-- Convergence in distribution is preserved by a cofinal reindexing. -/
theorem TendstoInDistribution.comp_tendsto
    (h : TendstoInDistribution X l Z μ μ')
    {J : Type*} {g : J → I} {l' : Filter J} (hg : Tendsto g l' l) :
    TendstoInDistribution (fun j => X (g j)) l' Z
      (fun j => μ (g j)) μ' where
  forall_aemeasurable j := h.forall_aemeasurable (g j)
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.comp hg

omit [HasOuterApproxClosed E] in
/-- Changing the approximating random variables almost everywhere at only an
eventually cofinal set of indices preserves convergence in distribution. -/
theorem TendstoInDistribution.congr_eventually
    {Y : (i : I) → Ω i → E}
    (h : TendstoInDistribution X l Z μ μ')
    (hXY : ∀ᶠ i in l, X i =ᵐ[μ i] Y i)
    (hY : ∀ i, AEMeasurable (Y i) (μ i)) :
    TendstoInDistribution Y l Z μ μ' where
  forall_aemeasurable := hY
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.congr' <| hXY.mono fun i hi => by
    apply Subtype.ext
    exact Measure.map_congr hi

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

namespace MeasureTheory

variable {I E F Ω' Ω'' : Type*} {Ω : I → Type*}
  {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : I) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {mΩ'' : MeasurableSpace Ω''} {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
  {mE : MeasurableSpace E} [TopologicalSpace E] [OpensMeasurableSpace E]
  {mF : MeasurableSpace F} [TopologicalSpace F] [OpensMeasurableSpace F]
  [SecondCountableTopology E] [SecondCountableTopology F]
  [TopologicalSpace.PseudoMetrizableSpace E]
  [TopologicalSpace.PseudoMetrizableSpace F]
  {X : (i : I) → Ω i → E} {Y : (i : I) → Ω i → F}
  {Z : Ω' → E} {T : Ω'' → F} {l : Filter I}

/-- Joint convergence of two independent random variables follows from their
marginal convergence.  The limiting variables are placed on the product
probability space, so their independence is part of the conclusion rather
than an additional assumption on an arbitrarily chosen common realization.

This is the binary building block for finite-dimensional convergence of
processes assembled from independent increments. -/
theorem TendstoInDistribution.prodMk_of_indepFun
    (hX : TendstoInDistribution X l Z μ μ')
    (hY : TendstoInDistribution Y l T μ μ'')
    (hZ : Measurable Z) (hT : Measurable T)
    (hXY : ∀ i, IndepFun (X i) (Y i) (μ i)) :
    TendstoInDistribution
      (fun i ω => (X i ω, Y i ω)) l
      (fun ω => (Z ω.1, T ω.2)) μ (μ'.prod μ'') := by
  refine ⟨fun i => (hX.forall_aemeasurable i).prodMk
      (hY.forall_aemeasurable i), ?_, ?_⟩
  · exact (hZ.comp measurable_fst).prodMk (hT.comp measurable_snd) |>.aemeasurable
  · change Tendsto
      (fun i => ((μ i).map (fun ω => (X i ω, Y i ω))).toProbabilityMeasure)
      l
      (nhds (((μ'.prod μ'').map
        (fun ω => (Z ω.1, T ω.2))).toProbabilityMeasure))
    have hmarginals := hX.tendsto.prodMk_nhds hY.tendsto
    have hproducts := ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
      hmarginals
    have hlimit :
        ((μ'.prod μ'').map (fun ω => (Z ω.1, T ω.2))).toProbabilityMeasure =
          (μ'.map Z).toProbabilityMeasure.prod
            (μ''.map T).toProbabilityMeasure := by
      apply Subtype.ext
      exact (Measure.map_prod_map μ' μ'' hZ hT).symm
    rw [hlimit]
    apply hproducts.congr'
    filter_upwards [] with i
    apply Subtype.ext
    exact ((hXY i).map_prod_eq_prod_map_map
      (hX.forall_aemeasurable i) (hY.forall_aemeasurable i)).symm

end MeasureTheory
