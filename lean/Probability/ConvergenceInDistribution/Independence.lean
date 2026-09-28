import Probability.ConvergenceInDistribution.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Metrizable.Basic

/-!
# Joint convergence of independent random variables

Weak convergence of independent coordinates, using continuity of product
probability measures.
-/

open Filter ProbabilityTheory
open scoped Topology

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
marginal convergence. The limiting variables are placed on the product
probability space, so their independence is part of the conclusion.

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
