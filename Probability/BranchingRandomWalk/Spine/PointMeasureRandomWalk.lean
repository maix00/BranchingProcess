import Probability.BranchingRandomWalk.Spine.PointMeasureEndpoint
import Probability.BranchingRandomWalk.Spine.EndpointRealization
import Probability.BranchingRandomWalk.Walk.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration

/-!
# Spine random walk from a random-measure offspring law

Boundary normalization turns the enumeration-free tilted law into a
probability law.  Its countable product supplies the independent increments
of the spine random walk used by the many-to-one formula.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Spine

/-- Independent increment field with the enumeration-free tilted marginal. -/
noncomputable def pointMeasureIncrementLaw
    {E : Type*} [MeasurableSpace E]
    (potential : E → ℝ) (law : Measure (Measure E)) : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ =>
    PointProcess.tiltedLaw potential (-1) law

theorem pointMeasureIncrementLaw_eq_independentIncrementLaw
    {E : Type*} [MeasurableSpace E]
    (potential : E → ℝ) (law : Measure (Measure E)) :
    pointMeasureIncrementLaw potential law =
      independentIncrementLaw
        (PointProcess.tiltedLaw potential (-1) law) := rfl

theorem pointMeasureIncrementLaw_isProbability
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law) :
    IsProbabilityMeasure (pointMeasureIncrementLaw potential law) := by
  let _ : IsProbabilityMeasure
      (PointProcess.tiltedLaw potential (-1) law) :=
    PointProcess.tiltedLaw_isProbability hpotential (-1) law hnormalization
  unfold pointMeasureIncrementLaw
  infer_instance

theorem pointMeasureIncrementLaw_coordinate
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law)
    (n : ℕ) :
    (pointMeasureIncrementLaw potential law).map (fun increment => increment n) =
      PointProcess.tiltedLaw potential (-1) law := by
  let _ : IsProbabilityMeasure
      (PointProcess.tiltedLaw potential (-1) law) :=
    PointProcess.tiltedLaw_isProbability hpotential (-1) law hnormalization
  unfold pointMeasureIncrementLaw
  exact Measure.infinitePi_map_eval
    (fun _ : ℕ => PointProcess.tiltedLaw potential (-1) law) n

theorem pointMeasureIncrementLaw_independent
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law) :
    iIndepFun (fun n (increment : ℕ → ℝ) => increment n)
      (pointMeasureIncrementLaw potential law) := by
  let _ : IsProbabilityMeasure
      (PointProcess.tiltedLaw potential (-1) law) :=
    PointProcess.tiltedLaw_isProbability hpotential (-1) law hnormalization
  unfold pointMeasureIncrementLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : ℕ => PointProcess.tiltedLaw potential (-1) law)
    (X := fun _ : ℕ => id) (fun _ => measurable_id))

/-- The random walk canonically supplied by an offspring random-measure law. -/
noncomputable def pointMeasureSpineRandomWalk
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law) :
    RandomWalk ℝ ℝ where
  initial := 0
  incrementLaw := pointMeasureIncrementLaw potential law
  prob := pointMeasureIncrementLaw_isProbability hpotential law hnormalization

@[simp] theorem pointMeasureSpineRandomWalk_initial
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law) :
    (pointMeasureSpineRandomWalk hpotential law hnormalization).initial = 0 := rfl

@[simp] theorem pointMeasureSpineRandomWalk_incrementLaw
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law) :
    (pointMeasureSpineRandomWalk hpotential law hnormalization).incrementLaw =
      pointMeasureIncrementLaw potential law := rfl

theorem pointMeasureSpineRandomWalk_independent
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law) :
    iIndepFun (fun n (increment : ℕ → ℝ) => increment n)
      (pointMeasureSpineRandomWalk hpotential law hnormalization).incrementLaw :=
  pointMeasureIncrementLaw_independent hpotential law hnormalization

theorem pointMeasureSpineRandomWalk_positionAt
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law)
    (n : ℕ) (increment : ℕ → ℝ) :
    (pointMeasureSpineRandomWalk hpotential law hnormalization).process
        id n increment = tiltedPosition n increment := by
  simp [RandomWalk.process, RandomWalk.positionAt, tiltedPosition]

/-- The enumeration-free weighted generation recursion is represented by the
endpoint of the constructed spine random walk. -/
theorem pointMeasureWeightedEndpointManyToOne_randomWalk
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law)
    {f : ℝ → ENNReal} (hf : Measurable f) (n : ℕ) (x : ℝ) :
    pointMeasureWeightedEndpointIterate potential (-1) law n f x =
      ∫⁻ increment,
        f (x + (pointMeasureSpineRandomWalk hpotential law hnormalization).process
          id n increment)
        ∂(pointMeasureSpineRandomWalk hpotential law hnormalization).incrementLaw := by
  let ν := PointProcess.tiltedLaw potential (-1) law
  let _ : IsProbabilityMeasure ν :=
    PointProcess.tiltedLaw_isProbability hpotential (-1) law hnormalization
  rw [pointMeasureWeightedEndpointManyToOne hpotential (-1) law
    hnormalization hf n]
  rw [pointMeasureSpineRandomWalk_incrementLaw,
    pointMeasureIncrementLaw_eq_independentIncrementLaw]
  simp_rw [pointMeasureSpineRandomWalk_positionAt]
  exact (lintegral_independentPosition_eq_iterate ν hf n x).symm

/-- The enumeration-free unweighted generation recursion is represented by
the same spine random walk with the reciprocal terminal weight. -/
theorem pointMeasureEndpointManyToOne_randomWalk
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law)
    {f : ℝ → ENNReal} (hf : Measurable f) (n : ℕ) (x : ℝ) :
    pointMeasureEndpointIterate potential law n f x =
      ∫⁻ increment,
        ENNReal.ofReal (Real.exp
          ((pointMeasureSpineRandomWalk hpotential law hnormalization).process
            id n increment)) *
          f (x +
            (pointMeasureSpineRandomWalk hpotential law hnormalization).process
              id n increment)
        ∂(pointMeasureSpineRandomWalk hpotential law hnormalization).incrementLaw := by
  let ν := PointProcess.tiltedLaw potential (-1) law
  let _ : IsProbabilityMeasure ν :=
    PointProcess.tiltedLaw_isProbability hpotential (-1) law hnormalization
  rw [pointMeasureEndpointManyToOne hpotential law hnormalization hf n]
  rw [pointMeasureSpineRandomWalk_incrementLaw,
    pointMeasureIncrementLaw_eq_independentIncrementLaw]
  simp_rw [pointMeasureSpineRandomWalk_positionAt]
  exact (lintegral_independentPosition_untilted_eq_iterate ν hf n x).symm

/-- Existential many-to-one statement: a spine random walk exists for every
normalized offspring random-measure law. -/
theorem exists_pointMeasureSpineRandomWalk
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law)
    {f : ℝ → ENNReal} (hf : Measurable f) (n : ℕ) (x : ℝ) :
    ∃ walk : RandomWalk ℝ ℝ,
      pointMeasureWeightedEndpointIterate potential (-1) law n f x =
        ∫⁻ increment, f (x + walk.process id n increment)
          ∂walk.incrementLaw := by
  refine ⟨pointMeasureSpineRandomWalk hpotential law hnormalization, ?_⟩
  exact pointMeasureWeightedEndpointManyToOne_randomWalk
    hpotential law hnormalization hf n x

end ProbabilityTheory.BranchingRandomWalk.Spine
