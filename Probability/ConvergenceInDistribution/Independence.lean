module

public import Probability.ConvergenceInDistribution.Basic
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.Metrizable.Basic

public section

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

namespace MeasureTheory

variable {I J : Type*} [Fintype J]
  {E : J → Type*} {Ω : I → Type*} {Ω' : J → Type*}
  {mE : ∀ j, MeasurableSpace (E j)}
  {tE : ∀ j, TopologicalSpace (E j)}
  [∀ j, OpensMeasurableSpace (E j)]
  [∀ j, SecondCountableTopology (E j)]
  [∀ j, TopologicalSpace.PseudoMetrizableSpace (E j)]
  {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : I) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {mΩ' : ∀ j, MeasurableSpace (Ω' j)}
  {μ' : (j : J) → Measure (Ω' j)} [∀ j, IsProbabilityMeasure (μ' j)]
  {X : (i : I) → (j : J) → Ω i → E j}
  {Z : (j : J) → Ω' j → E j} {l : Filter I}

/-- Joint convergence of a finite independent family follows from convergence
of every coordinate. The limiting family is realized on the finite product
of the coordinate probability spaces. -/
theorem TendstoInDistribution.pi_of_iIndepFun
    (hX : ∀ j, TendstoInDistribution (fun i => X i j) l (Z j) μ (μ' j))
    (hZ : ∀ j, Measurable (Z j))
    (h_indep : ∀ i, iIndepFun (X i) (μ i)) :
    TendstoInDistribution
      (fun i ω j => X i j ω) l
      (fun ω j => Z j (ω j)) μ (Measure.pi μ') := by
  refine ⟨fun i => AEMeasurable.of_eval fun j => (hX j).forall_aemeasurable i,
    ?_, ?_⟩
  · exact (measurable_pi_iff.2 fun j =>
      (hZ j).comp (measurable_pi_apply j)).aemeasurable
  · change Tendsto
      (fun i => ((μ i).map (fun ω j => X i j ω)).toProbabilityMeasure)
      l
      (nhds (((Measure.pi μ').map
        (fun ω j => Z j (ω j))).toProbabilityMeasure))
    have hmarginals : Tendsto
        (fun i j => ((μ i).map (X i j)).toProbabilityMeasure) l
        (nhds (fun j => ((μ' j).map (Z j)).toProbabilityMeasure)) :=
      tendsto_pi_nhds.2 fun j => (hX j).tendsto
    have hproducts := ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp
      hmarginals
    have hlimit :
        ((Measure.pi μ').map (fun ω j => Z j (ω j))).toProbabilityMeasure =
          ProbabilityMeasure.pi
            (fun j => ((μ' j).map (Z j)).toProbabilityMeasure) := by
      apply Subtype.ext
      exact Measure.pi_map_pi (fun j => (hZ j).aemeasurable)
    rw [hlimit]
    apply hproducts.congr'
    filter_upwards [] with i
    apply Subtype.ext
    exact (iIndepFun.map_fun_eq_pi_map
      (fun j => (hX j).forall_aemeasurable i) (h_indep i)).symm

end MeasureTheory
