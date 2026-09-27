import Probability.BranchingRandomWalk.Spine.TiltedLaw
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Endpoint form of the iterated many-to-one identity

This file isolates the analytic induction behind the endpoint version of the
many-to-one formula.  A branching transition sums over every surviving slot;
the corresponding spine transition integrates against the tilted potential
law.  The one-generation identities imply equality of their iterates.

The later tree theorem identifies the recursive branching transition with the
actual generation of the pre-sampled branching field.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching MeasureTheory

/-- Apply one additive spine increment to an endpoint test. -/
noncomputable def tiltedEndpointOperator (ν : Measure ℝ)
    (f : ℝ → ENNReal) (x : ℝ) : ENNReal :=
  ∫⁻ y, f (x + y) ∂ν

/-- Apply one spine increment and undo the exponential tilt. -/
noncomputable def untiltedEndpointOperator (ν : Measure ℝ)
    (f : ℝ → ENNReal) (x : ℝ) : ENNReal :=
  ∫⁻ y, ENNReal.ofReal (Real.exp y) * f (x + y) ∂ν

/-- One exponentially weighted branching generation, viewed from position
`x`. -/
noncomputable def weightedBranchingEndpointOperator {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (f : ℝ → ENNReal) (x : ℝ) : ENNReal :=
  ∫⁻ ξ, ∑' i : ι, realizedPotentialWeight φ (-1) ξ i *
    f (x + ξ.potentialValue' φ i) ∂μ

/-- One unweighted branching generation, viewed from position `x`. -/
noncomputable def branchingEndpointOperator {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (f : ℝ → ENNReal) (x : ℝ) : ENNReal :=
  ∫⁻ ξ, ∑' i : ι,
    survivingPotentialTest φ (fun y => f (x + y)) ξ i ∂μ

theorem measurable_tiltedEndpointOperator
    (ν : Measure ℝ) [SFinite ν] {f : ℝ → ENNReal} (hf : Measurable f) :
    Measurable (tiltedEndpointOperator ν f) := by
  apply Measurable.lintegral_prod_right
  fun_prop

theorem measurable_untiltedEndpointOperator
    (ν : Measure ℝ) [SFinite ν] {f : ℝ → ENNReal} (hf : Measurable f) :
    Measurable (untiltedEndpointOperator ν f) := by
  apply Measurable.lintegral_prod_right
  fun_prop

/-- The weighted branching transition is exactly the tilted spine
transition. -/
theorem weightedBranchingEndpointOperator_eq_tilted {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    {f : ℝ → ENNReal} (hf : Measurable f) :
    weightedBranchingEndpointOperator φ μ f =
      tiltedEndpointOperator (tiltedPotentialLaw φ (-1) μ) f := by
  funext x
  symm
  exact lintegral_tiltedPotentialLaw φ (-1) μ
    (fun y => f (x + y)) (by fun_prop)

/-- The unweighted branching transition is the reciprocal-weight spine
transition. -/
theorem branchingEndpointOperator_eq_untilted {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    {f : ℝ → ENNReal} (hf : Measurable f) :
    branchingEndpointOperator φ μ f =
      untiltedEndpointOperator (tiltedPotentialLaw φ (-1) μ) f := by
  funext x
  symm
  simpa [untiltedEndpointOperator, branchingEndpointOperator] using
    (lintegral_tiltedPotentialLaw_cancel φ (-1) μ
      (fun y => f (x + y)) (by fun_prop))

/-- Recursive `n`-step weighted branching endpoint functional. -/
noncomputable def weightedBranchingEndpointIterate {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X)) :
    ℕ → (ℝ → ENNReal) → ℝ → ENNReal
  | 0, f => f
  | n + 1, f => weightedBranchingEndpointOperator φ μ
      (weightedBranchingEndpointIterate φ μ n f)

/-- Recursive `n`-step unweighted branching endpoint functional. -/
noncomputable def branchingEndpointIterate {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X)) :
    ℕ → (ℝ → ENNReal) → ℝ → ENNReal
  | 0, f => f
  | n + 1, f => branchingEndpointOperator φ μ
      (branchingEndpointIterate φ μ n f)

/-- Recursive `n`-step tilted spine endpoint functional. -/
noncomputable def tiltedEndpointIterate (ν : Measure ℝ) :
    ℕ → (ℝ → ENNReal) → ℝ → ENNReal
  | 0, f => f
  | n + 1, f => tiltedEndpointOperator ν (tiltedEndpointIterate ν n f)

/-- Recursive `n`-step spine endpoint functional with the reciprocal
exponential factor at every step. -/
noncomputable def untiltedEndpointIterate (ν : Measure ℝ) :
    ℕ → (ℝ → ENNReal) → ℝ → ENNReal
  | 0, f => f
  | n + 1, f => untiltedEndpointOperator ν
      (untiltedEndpointIterate ν n f)

theorem measurable_tiltedEndpointIterate
    (ν : Measure ℝ) [SFinite ν] {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, Measurable (tiltedEndpointIterate ν n f)
  | 0 => hf
  | n + 1 => measurable_tiltedEndpointOperator ν
      (measurable_tiltedEndpointIterate ν hf n)

theorem measurable_untiltedEndpointIterate
    (ν : Measure ℝ) [SFinite ν] {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, Measurable (untiltedEndpointIterate ν n f)
  | 0 => hf
  | n + 1 => measurable_untiltedEndpointOperator ν
      (measurable_untiltedEndpointIterate ν hf n)

/-- Weighted endpoint recursion when raw edge marks are first interpreted in
an abstract position space and then observed through a real potential. -/
theorem weightedEndpointManyToOne
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, weightedBranchingEndpointIterate (potential.comp d hd) μ n f =
      tiltedEndpointIterate
        (tiltedPotentialLaw (potential.comp d hd) (-1) μ) n f
  | 0 => rfl
  | n + 1 => by
      let φ := potential.comp d hd
      let _ : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
        tiltedPotentialLaw_isProbability φ μ hboundary
      rw [weightedBranchingEndpointIterate, tiltedEndpointIterate,
        weightedEndpointManyToOne d hd potential μ hboundary hf n]
      exact weightedBranchingEndpointOperator_eq_tilted φ μ
        (measurable_tiltedEndpointIterate _ hf n)

/-- Unweighted endpoint recursion with separate raw marks, positions, and
real-valued potential. -/
theorem endpointManyToOne
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, branchingEndpointIterate (potential.comp d hd) μ n f =
      untiltedEndpointIterate
        (tiltedPotentialLaw (potential.comp d hd) (-1) μ) n f
  | 0 => rfl
  | n + 1 => by
      let φ := potential.comp d hd
      let _ : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
        tiltedPotentialLaw_isProbability φ μ hboundary
      rw [branchingEndpointIterate, untiltedEndpointIterate,
        endpointManyToOne d hd potential μ hboundary hf n]
      exact branchingEndpointOperator_eq_untilted φ μ
        (measurable_untiltedEndpointIterate _ hf n)

end ProbabilityTheory.BranchingRandomWalk.Spine
