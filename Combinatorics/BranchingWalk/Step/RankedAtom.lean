import Combinatorics.BranchingWalk.Step.PointMeasure
import Mathlib.Data.EReal.Basic

/-!
# The children of a step, ranked by increasing value

The children of a step `ξ : Step α ℝ` can be listed by increasing value: the `n`-th of them is the least
threshold whose cumulative mass has reached `n + 1`, and multiplicity is kept because that mass counts slots.
Nothing here mentions a measure on configurations or a sample space — the input is the step itself, so the
construction is measurable in the step, and a law on steps pulls the atoms back as random variables. That is
where the randomness of the thesis's `Ξᵢ` comes from.

The rational thresholds keep the construction countable, hence measurable: a countable infimum of measurable
candidates. The slot type is arbitrary; only the mark type is fixed to the real line, because a list by
increasing value needs a countable dense order to be measurable.
-/

open MeasureTheory
open scoped ENNReal

namespace Combinatorics

namespace Branching

/-- A rational candidate threshold for the child of rank `n`: the threshold itself where the cumulative mass
has already reached `n + 1`, and `⊤` where it has not. -/
noncomputable def Step.rankedAtomCandidate {α : Type*} (n : ℕ) (q : ℚ)
    (ξ : Step α ℝ) : EReal :=
  if (n + 1 : ENNReal) ≤ stepPointMeasure ξ (Set.Iic (q : ℝ)) then ((q : ℝ) : EReal) else ⊤

theorem Step.rankedAtomCandidate_measurable {α : Type*} [Countable α] (n : ℕ) (q : ℚ) :
    Measurable (Step.rankedAtomCandidate (α := α) n q) := by
  unfold Step.rankedAtomCandidate
  have hcount : Measurable
      (fun ξ : Step α ℝ => stepPointMeasure ξ (Set.Iic (q : ℝ))) :=
    (Measure.measurable_coe measurableSet_Iic).comp stepPointMeasure_measurable
  have hset : MeasurableSet {ξ : Step α ℝ |
      (n + 1 : ENNReal) ≤ stepPointMeasure ξ (Set.Iic (q : ℝ))} :=
    measurableSet_le measurable_const hcount
  exact measurable_const.ite hset measurable_const

/-- The location of the `n`-th child of the step by increasing value. It is `⊤` when the step has at most `n`
children. -/
noncomputable def Step.rankedAtomEReal {α : Type*} (n : ℕ) (ξ : Step α ℝ) : EReal :=
  ⨅ q : ℚ, Step.rankedAtomCandidate n q ξ

theorem Step.rankedAtomEReal_measurable {α : Type*} [Countable α] (n : ℕ) :
    Measurable (Step.rankedAtomEReal (α := α) n) :=
  Measurable.iInf (Step.rankedAtomCandidate_measurable n)

/-- The displacement of the `n`-th child of the step by increasing value. Its value is irrelevant when the
step has fewer than `n + 1` children, which is what `Step.rankedAtomPresent` decides. -/
noncomputable def Step.rankedAtom {α : Type*} (n : ℕ) (ξ : Step α ℝ) : ℝ :=
  (Step.rankedAtomEReal n ξ).toReal

/-- The ranked atom is a measurable function of the step: a law on steps makes it a random variable, with no
sample space or Giry measurable space in the statement. -/
theorem Step.rankedAtom_measurable {α : Type*} [Countable α] (n : ℕ) :
    Measurable (Step.rankedAtom (α := α) n) :=
  (Step.rankedAtomEReal_measurable n).ereal_toReal

/-- The step has a child of rank `n`, equivalently at least `n + 1` children, the mass counting slots. -/
def Step.rankedAtomPresent {α : Type*} (n : ℕ) (ξ : Step α ℝ) : Prop :=
  (n + 1 : ENNReal) ≤ stepPointMeasure ξ Set.univ

theorem Step.rankedAtomPresent_measurable {α : Type*} [Countable α] (n : ℕ) :
    MeasurableSet {ξ : Step α ℝ | Step.rankedAtomPresent n ξ} := by
  unfold Step.rankedAtomPresent
  exact measurableSet_le measurable_const
    ((Measure.measurable_coe MeasurableSet.univ).comp stepPointMeasure_measurable)

end Branching

end Combinatorics
