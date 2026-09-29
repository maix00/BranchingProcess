module

public import Probability.BranchingRandomWalk.Spine.EndpointManyToOne
public import Probability.BranchingRandomWalk.Spine.PointMeasure
public import Probability.PointProcess.Tilted

/-!
# Enumeration-free endpoint many-to-one recursion

The offspring law in this file is a law on measures over an arbitrary
measurable mark space.  One branching transition is expressed by integration
against the sampled measure, so neither the mark space nor an auxiliary set
of child slots is assumed countable.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open MeasureTheory

/-- One exponentially weighted branching transition obtained directly from
a law on random measures. -/
noncomputable def pointMeasureWeightedEndpointOperator
    {E : Type*} [MeasurableSpace E]
    (potential : E → ℝ) (θ : ℝ) (law : Measure (Measure E))
    (f : ℝ → ENNReal) (x : ℝ) : ENNReal :=
  ∫⁻ ν, ∫⁻ z, PointProcess.exponentialWeight potential θ z *
    f (x + potential z) ∂ν ∂law

/-- One unweighted branching transition obtained directly from a law on
random measures. -/
noncomputable def pointMeasureEndpointOperator
    {E : Type*} [MeasurableSpace E]
    (potential : E → ℝ) (law : Measure (Measure E))
    (f : ℝ → ENNReal) (x : ℝ) : ENNReal :=
  ∫⁻ ν, ∫⁻ z, f (x + potential z) ∂ν ∂law

theorem pointMeasureWeightedEndpointOperator_eq_tilted
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (θ : ℝ) (law : Measure (Measure E))
    {f : ℝ → ENNReal} (hf : Measurable f) :
    pointMeasureWeightedEndpointOperator potential θ law f =
      tiltedEndpointOperator (PointProcess.tiltedLaw potential θ law) f := by
  funext x
  symm
  exact PointProcess.lintegral_tiltedLaw hpotential θ law
    (hf.comp (measurable_const.add measurable_id))

theorem pointMeasureEndpointOperator_eq_untilted
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    {f : ℝ → ENNReal} (hf : Measurable f) :
    pointMeasureEndpointOperator potential law f =
      untiltedEndpointOperator
        (PointProcess.tiltedLaw potential (-1) law) f := by
  funext x
  symm
  simpa [untiltedEndpointOperator, pointMeasureEndpointOperator] using
    (PointProcess.lintegral_tiltedLaw_cancel hpotential (-1) law
      (f := fun y : ℝ => f (x + y))
      (hf.comp (measurable_const.add measurable_id)))

/-- Iterated weighted generation intensity, defined without a child
enumeration. -/
noncomputable def pointMeasureWeightedEndpointIterate
    {E : Type*} [MeasurableSpace E]
    (potential : E → ℝ) (θ : ℝ) (law : Measure (Measure E)) :
    ℕ → (ℝ → ENNReal) → ℝ → ENNReal
  | 0, f => f
  | n + 1, f => pointMeasureWeightedEndpointOperator potential θ law
      (pointMeasureWeightedEndpointIterate potential θ law n f)

/-- Iterated unweighted generation intensity, defined without a child
enumeration. -/
noncomputable def pointMeasureEndpointIterate
    {E : Type*} [MeasurableSpace E]
    (potential : E → ℝ) (law : Measure (Measure E)) :
    ℕ → (ℝ → ENNReal) → ℝ → ENNReal
  | 0, f => f
  | n + 1, f => pointMeasureEndpointOperator potential law
      (pointMeasureEndpointIterate potential law n f)

theorem measurable_pointMeasureWeightedEndpointIterate
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (θ : ℝ) (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential θ law)
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, Measurable
      (pointMeasureWeightedEndpointIterate potential θ law n f)
  | 0 => hf
  | n + 1 => by
      let _ : IsProbabilityMeasure
          (PointProcess.tiltedLaw potential θ law) :=
        PointProcess.tiltedLaw_isProbability hpotential θ law hnormalization
      rw [pointMeasureWeightedEndpointIterate,
        pointMeasureWeightedEndpointOperator_eq_tilted hpotential θ law
          (measurable_pointMeasureWeightedEndpointIterate hpotential θ law
            hnormalization hf n)]
      exact measurable_tiltedEndpointOperator _
        (measurable_pointMeasureWeightedEndpointIterate hpotential θ law
          hnormalization hf n)

/-- Enumeration-free weighted many-to-one recursion. -/
theorem pointMeasureWeightedEndpointManyToOne
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (θ : ℝ) (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential θ law)
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, pointMeasureWeightedEndpointIterate potential θ law n f =
      tiltedEndpointIterate
        (PointProcess.tiltedLaw potential θ law) n f
  | 0 => rfl
  | n + 1 => by
      let _ : IsProbabilityMeasure
          (PointProcess.tiltedLaw potential θ law) :=
        PointProcess.tiltedLaw_isProbability hpotential θ law hnormalization
      rw [pointMeasureWeightedEndpointIterate, tiltedEndpointIterate,
        pointMeasureWeightedEndpointManyToOne hpotential θ law
          hnormalization hf n]
      exact pointMeasureWeightedEndpointOperator_eq_tilted hpotential θ law
        (measurable_tiltedEndpointIterate _ hf n)

theorem measurable_pointMeasureEndpointIterate
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law)
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, Measurable (pointMeasureEndpointIterate potential law n f)
  | 0 => hf
  | n + 1 => by
      let _ : IsProbabilityMeasure
          (PointProcess.tiltedLaw potential (-1) law) :=
        PointProcess.tiltedLaw_isProbability hpotential (-1) law hnormalization
      rw [pointMeasureEndpointIterate,
        pointMeasureEndpointOperator_eq_untilted hpotential law
          (measurable_pointMeasureEndpointIterate hpotential law
            hnormalization hf n)]
      exact measurable_untiltedEndpointOperator _
        (measurable_pointMeasureEndpointIterate hpotential law
          hnormalization hf n)

/-- Enumeration-free unweighted many-to-one recursion. -/
theorem pointMeasureEndpointManyToOne
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law)
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, pointMeasureEndpointIterate potential law n f =
      untiltedEndpointIterate
        (PointProcess.tiltedLaw potential (-1) law) n f
  | 0 => rfl
  | n + 1 => by
      let _ : IsProbabilityMeasure
          (PointProcess.tiltedLaw potential (-1) law) :=
        PointProcess.tiltedLaw_isProbability hpotential (-1) law hnormalization
      rw [pointMeasureEndpointIterate, untiltedEndpointIterate,
        pointMeasureEndpointManyToOne hpotential law hnormalization hf n]
      exact pointMeasureEndpointOperator_eq_untilted hpotential law
        (measurable_untiltedEndpointIterate _ hf n)

/-- A labelled offspring step realizes the abstract weighted random-measure
transition through its counting measure. -/
theorem pointMeasureWeightedEndpointOperator_map_stepPointMeasure
    {ι E : Type*} [Countable ι] [MeasurableSpace E] [Zero E]
    (φ : Combinatorics.Branching.Potential E)
    (μ : Measure (Combinatorics.Branching.Step ι E))
    {f : ℝ → ENNReal} (hf : Measurable f) :
    pointMeasureWeightedEndpointOperator φ (-1)
        (μ.map (Combinatorics.Branching.stepPointMeasure
          (ι := ι) (X := E))) f =
      weightedBranchingEndpointOperator φ μ f := by
  rw [pointMeasureWeightedEndpointOperator_eq_tilted
      φ.measurable_toFun (-1)
        (μ.map (Combinatorics.Branching.stepPointMeasure
          (ι := ι) (X := E))) hf,
    weightedBranchingEndpointOperator_eq_tilted φ μ hf,
    pointMeasure_tiltedLaw_eq_tiltedPotentialLaw]

/-- A labelled offspring step realizes the abstract unweighted random-measure
transition through its counting measure. -/
theorem pointMeasureEndpointOperator_map_stepPointMeasure
    {ι E : Type*} [Countable ι] [MeasurableSpace E] [Zero E]
    (φ : Combinatorics.Branching.Potential E)
    (μ : Measure (Combinatorics.Branching.Step ι E))
    {f : ℝ → ENNReal} (hf : Measurable f) :
    pointMeasureEndpointOperator φ
        (μ.map (Combinatorics.Branching.stepPointMeasure
          (ι := ι) (X := E))) f =
      branchingEndpointOperator φ μ f := by
  rw [pointMeasureEndpointOperator_eq_untilted
      φ.measurable_toFun
        (μ.map (Combinatorics.Branching.stepPointMeasure
          (ι := ι) (X := E))) hf,
    branchingEndpointOperator_eq_untilted φ μ hf,
    pointMeasure_tiltedLaw_eq_tiltedPotentialLaw]

theorem pointMeasureWeightedEndpointIterate_map_stepPointMeasure
    {ι E : Type*} [Countable ι] [MeasurableSpace E] [Zero E]
    (φ : Combinatorics.Branching.Potential E)
    (μ : Measure (Combinatorics.Branching.Step ι E))
    (hboundary : HasBoundaryNormalization φ μ)
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, pointMeasureWeightedEndpointIterate φ (-1)
        (μ.map (Combinatorics.Branching.stepPointMeasure
          (ι := ι) (X := E))) n f =
      weightedBranchingEndpointIterate φ μ n f
  | 0 => rfl
  | n + 1 => by
      rw [pointMeasureWeightedEndpointIterate,
        weightedBranchingEndpointIterate,
        pointMeasureWeightedEndpointIterate_map_stepPointMeasure
          φ μ hboundary hf n]
      exact pointMeasureWeightedEndpointOperator_map_stepPointMeasure φ μ
        (by
          rw [← pointMeasureWeightedEndpointIterate_map_stepPointMeasure
            φ μ hboundary hf n]
          exact measurable_pointMeasureWeightedEndpointIterate
            φ.measurable_toFun (-1)
              (μ.map (Combinatorics.Branching.stepPointMeasure
                (ι := ι) (X := E)))
              (pointMeasure_hasNormalization φ μ hboundary) hf n)

theorem pointMeasureEndpointIterate_map_stepPointMeasure
    {ι E : Type*} [Countable ι] [MeasurableSpace E] [Zero E]
    (φ : Combinatorics.Branching.Potential E)
    (μ : Measure (Combinatorics.Branching.Step ι E))
    (hboundary : HasBoundaryNormalization φ μ)
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, pointMeasureEndpointIterate φ
        (μ.map (Combinatorics.Branching.stepPointMeasure
          (ι := ι) (X := E))) n f =
      branchingEndpointIterate φ μ n f
  | 0 => rfl
  | n + 1 => by
      rw [pointMeasureEndpointIterate, branchingEndpointIterate,
        pointMeasureEndpointIterate_map_stepPointMeasure
          φ μ hboundary hf n]
      exact pointMeasureEndpointOperator_map_stepPointMeasure φ μ
        (by
          rw [← pointMeasureEndpointIterate_map_stepPointMeasure
            φ μ hboundary hf n]
          exact measurable_pointMeasureEndpointIterate
            φ.measurable_toFun
              (μ.map (Combinatorics.Branching.stepPointMeasure
                (ι := ι) (X := E)))
              (pointMeasure_hasNormalization φ μ hboundary) hf n)

end ProbabilityTheory.BranchingRandomWalk.Spine
