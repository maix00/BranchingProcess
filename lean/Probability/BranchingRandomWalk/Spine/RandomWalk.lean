import Probability.BranchingRandomWalk.Spine.EndpointRealization
import Probability.BranchingRandomWalk.Walk.Basic

/-!
# The spine random walk

The tilted increment product law defines an actual single-root random walk.
Its canonical branching realization has child-slot type `PUnit`, so every
generation contains exactly the unique address `Walk.lineNode n`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching MeasureTheory

/-- The random walk supplied by the tilted law in the many-to-one formula. -/
noncomputable def spineRandomWalk {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) : RandomWalk ℝ ℝ where
  initial := 0
  incrementLaw := tiltedIncrementFieldLaw φ μ
  prob := tiltedIncrementFieldLaw_isProbability φ μ hboundary

@[simp] theorem spineRandomWalk_initial {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) :
    (spineRandomWalk φ μ hboundary).initial = 0 := rfl

@[simp] theorem spineRandomWalk_incrementLaw {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) :
    (spineRandomWalk φ μ hboundary).incrementLaw =
      tiltedIncrementFieldLaw φ μ := rfl

/-- The position process of the constructed random walk is the partial-sum
process previously used to realize endpoint recursion. -/
theorem spineRandomWalk_positionAt {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (increment : ℕ → ℝ) :
    (spineRandomWalk φ μ hboundary).process id n increment =
      tiltedPosition n increment := by
  simp [RandomWalk.process, RandomWalk.positionAt, tiltedPosition]

/-- The increments of the spine random walk are independent. -/
theorem spineRandomWalk_independent {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) :
    iIndepFun (fun n (increment : ℕ → ℝ) => increment n)
      (spineRandomWalk φ μ hboundary).incrementLaw :=
  tiltedIncrementFieldLaw_independent φ μ hboundary

/-- Every increment of the spine random walk has the tilted potential law. -/
theorem spineRandomWalk_incrementLaw_coordinate {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) (n : ℕ) :
    (spineRandomWalk φ μ hboundary).incrementLaw.map
        (fun increment => increment n) =
      tiltedPotentialLaw φ (-1) μ :=
  tiltedIncrementFieldLaw_coordinate φ μ hboundary n

/-- Weighted many-to-one, with its right side expressed through the position
of the constructed random walk. -/
theorem weightedEndpointManyToOne_randomWalk
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    {f : ℝ → ENNReal} (hf : Measurable f) (n : ℕ) (x : ℝ) :
    weightedBranchingEndpointIterate (potential.comp d hd) μ n f x =
      ∫⁻ increment,
        f (x + (spineRandomWalk (potential.comp d hd) μ hboundary).process
          id n increment)
        ∂(spineRandomWalk (potential.comp d hd) μ hboundary).incrementLaw := by
  rw [weightedEndpointManyToOne_product d hd potential μ hboundary hf n x]
  apply lintegral_congr
  intro increment
  rw [spineRandomWalk_positionAt]

/-- Unweighted many-to-one, with the reciprocal exponential weight and the
position of the constructed random walk. -/
theorem endpointManyToOne_randomWalk
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    {f : ℝ → ENNReal} (hf : Measurable f) (n : ℕ) (x : ℝ) :
    branchingEndpointIterate (potential.comp d hd) μ n f x =
      ∫⁻ increment,
        ENNReal.ofReal (Real.exp
          ((spineRandomWalk (potential.comp d hd) μ hboundary).process
            id n increment)) *
          f (x + (spineRandomWalk (potential.comp d hd) μ hboundary).process
            id n increment)
        ∂(spineRandomWalk (potential.comp d hd) μ hboundary).incrementLaw := by
  rw [endpointManyToOne_product d hd potential μ hboundary hf n x]
  apply lintegral_congr
  intro increment
  rw [spineRandomWalk_positionAt]

/-- Existential form traditionally used to state many-to-one: the tilted
kernel constructs a random walk whose endpoint represents the weighted
branching endpoint recursion. -/
theorem exists_randomWalk_weightedEndpointManyToOne
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    {f : ℝ → ENNReal} (hf : Measurable f) (n : ℕ) (x : ℝ) :
    ∃ walk : RandomWalk ℝ ℝ,
      weightedBranchingEndpointIterate (potential.comp d hd) μ n f x =
        ∫⁻ increment, f (x + walk.process id n increment)
          ∂walk.incrementLaw := by
  refine ⟨spineRandomWalk (potential.comp d hd) μ hboundary, ?_⟩
  exact weightedEndpointManyToOne_randomWalk
    d hd potential μ hboundary hf n x

end ProbabilityTheory.BranchingRandomWalk.Spine
