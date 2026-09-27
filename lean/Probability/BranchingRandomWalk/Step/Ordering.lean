import Probability.BranchingRandomWalk.Step.Basic
import Combinatorics.BranchingWalk.Step.Ordering

/-!
# Ordering a random branching step

The raw random input is first realized as a deterministic optional-slot step.
An orderability witness then reindexes every realized step.  The result still
has the ordinary `Step ℕ X` type; orderedness is a property, not a wrapper.

Pointwise orderability alone does not imply that the choice of relabelling is
measurable.  The measurable sorting theorem for a concrete step law must
therefore prove `Measurable (S.orderedRealization h)` explicitly.  Once that is
available, the first ordered slot is a measurable random displacement and is
the leftmost child whenever a child exists.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

/-- Realize a random step and reindex each sample into a chosen increasing
normal form. -/
noncomputable def Step.orderedRealization
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LinearOrder X] (S : Step Ω ℕ X)
    (h : ∀ ω, (S ω).IsOrderable) :
    Ω → Combinatorics.Branching.Step ℕ X :=
  fun ω => (S ω).order (h ω)

theorem Step.orderedRealization_isOrdered
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LinearOrder X] (S : Step Ω ℕ X)
    (h : ∀ ω, (S ω).IsOrderable) (ω : Ω) :
    (S.orderedRealization h ω).IsOrdered :=
  (S ω).order_isOrdered (h ω)

/-- Samplewise ordering preserves the random point measure exactly. -/
theorem Step.orderedRealization_pointMeasure
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LinearOrder X] (S : Step Ω ℕ X)
    (h : ∀ ω, (S ω).IsOrderable) (ω : Ω) :
    stepPointMeasure (S.orderedRealization h ω) = S.pointMeasure ω :=
  stepPointMeasure_order (S ω) (h ω)

theorem Step.orderedRealization_pointMeasure_measurable
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LinearOrder X] [Zero X]
    (S : Step Ω ℕ X) (h : ∀ ω, (S ω).IsOrderable)
    (hmeas : Measurable (S.orderedRealization h)) :
    Measurable (fun ω => stepPointMeasure (S.orderedRealization h ω)) :=
  stepPointMeasure_measurable.comp hmeas

/-- Consequently the pushforward point-measure law is unchanged by any
measurable realization of the ordering map. -/
theorem Step.orderedRealization_branchingLaw
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LinearOrder X] [Zero X]
    (S : Step Ω ℕ X) (P : Measure Ω)
    (h : ∀ ω, (S ω).IsOrderable) :
    P.map (fun ω => stepPointMeasure (S.orderedRealization h ω)) =
      S.branchingLaw P := by
  rw [show (fun ω => stepPointMeasure (S.orderedRealization h ω)) =
      S.pointMeasure from funext (S.orderedRealization_pointMeasure h)]
  rfl

/-- The random leftmost displacement is the first slot after measurable
ordering.  It is `none` exactly when the ordered realization has no child. -/
noncomputable def Step.leftmostDisplacement?
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LinearOrder X] (S : Step Ω ℕ X)
    (h : ∀ ω, (S ω).IsOrderable) : Ω → Option X :=
  fun ω => S.orderedRealization h ω 0

theorem Step.leftmostDisplacement?_measurable
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LinearOrder X] (S : Step Ω ℕ X)
    (h : ∀ ω, (S ω).IsOrderable)
    (hmeas : Measurable (S.orderedRealization h)) :
    Measurable (S.leftmostDisplacement? h) :=
  (measurable_pi_apply 0).comp hmeas

/-- On every nonempty realization, the random first ordered slot is below
every displacement of the raw realization. -/
theorem Step.leftmostDisplacement?_eq_some_le
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LinearOrder X] (S : Step Ω ℕ X)
    (h : ∀ ω, (S ω).IsOrderable) (ω : Ω)
    (hne : ∃ j, survive (S ω) j) :
    ∃ x, S.leftmostDisplacement? h ω = some x ∧
      ∀ j y, S ω j = some y → x ≤ y :=
  Combinatorics.Branching.Step.leftmost?_eq_some_le (S ω) (h ω) hne

end ProbabilityTheory.BranchingRandomWalk
