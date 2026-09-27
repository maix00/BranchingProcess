import Probability.BranchingRandomWalk.Step.Basic
import Combinatorics.BranchingWalk.Step.Ordering

/-!
# Measurable ordering of a random branching step

The raw random input is realized as an optional-slot step. A measurably
orderable random step admits a measurable ordered realization that contains
every raw child and preserves the complete point measure. The ordered
realization still has the ordinary deterministic `Step ι X` type;
`Step.IsOrdered` is its property, not a wrapper type.

The slot type is abstract. A least slot is required only when reading the
leftmost displacement. Pointwise existence of an ordering is insufficient:
the ordered realization itself must be measurable.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

/-- A random step has a measurable ordering when it has a measurable ordered
realization, every raw child occurs in that realization, and the complete
point measure (hence multiplicity) is preserved. -/
def Step.IsMeasurablyOrderable
    {Ω ι X : Type*} (κ : Type*) [MeasurableSpace Ω] [MeasurableSpace X]
    [LT κ] [LE X] (S : Step Ω ι X) : Prop :=
  ∃ T : Ω → Combinatorics.Branching.Step κ X,
    Measurable T ∧
    (∀ ω, (T ω).IsOrdered) ∧
    (∀ ω j y, S ω j = some y → ∃ i, T ω i = some y) ∧
    ∀ ω, stepPointMeasure (T ω) = S.pointMeasure ω

/-- An already measurably realized ordered input supplies its own ordering. -/
theorem Step.isMeasurablyOrderable_of_isOrdered
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LT ι] [LE X] (S : Step Ω ι X)
    (h : ∀ ω, (S ω).IsOrdered) : S.IsMeasurablyOrderable ι := by
  refine ⟨S, S.measurable_toFun, h, ?_, fun _ => rfl⟩
  intro ω j y hj
  exact ⟨j, hj⟩

/-- Choose the measurable ordered realization supplied by the property. -/
noncomputable def Step.orderedRealization
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LT κ] [LE X] (S : Step Ω ι X)
    (h : S.IsMeasurablyOrderable κ) :
    Ω → Combinatorics.Branching.Step κ X :=
  Classical.choose h

theorem Step.orderedRealization_measurable
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LT κ] [LE X] (S : Step Ω ι X)
    (h : S.IsMeasurablyOrderable κ) :
    Measurable (S.orderedRealization h) :=
  (Classical.choose_spec h).1

theorem Step.orderedRealization_isOrdered
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LT κ] [LE X] (S : Step Ω ι X)
    (h : S.IsMeasurablyOrderable κ) (ω : Ω) :
    (S.orderedRealization h ω).IsOrdered :=
  (Classical.choose_spec h).2.1 ω

theorem Step.raw_child_mem_orderedRealization
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LT κ] [LE X] (S : Step Ω ι X)
    (h : S.IsMeasurablyOrderable κ) (ω : Ω) {j : ι} {y : X}
    (hj : S ω j = some y) :
    ∃ i, S.orderedRealization h ω i = some y :=
  (Classical.choose_spec h).2.2.1 ω j y hj

/-- Measurable ordering preserves the random point measure exactly. -/
theorem Step.orderedRealization_pointMeasure
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LT κ] [LE X] (S : Step Ω ι X)
    (h : S.IsMeasurablyOrderable κ) (ω : Ω) :
    stepPointMeasure (S.orderedRealization h ω) = S.pointMeasure ω :=
  (Classical.choose_spec h).2.2.2 ω

theorem Step.orderedRealization_pointMeasure_measurable
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable κ] [LT κ] [LE X] [Zero X]
    (S : Step Ω ι X) (h : S.IsMeasurablyOrderable κ) :
    Measurable (fun ω => stepPointMeasure (S.orderedRealization h ω)) :=
  stepPointMeasure_measurable.comp (S.orderedRealization_measurable h)

/-- Consequently the pushforward point-measure law is unchanged. -/
theorem Step.orderedRealization_branchingLaw
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] [Countable κ] [LT κ] [LE X] [Zero X]
    (S : Step Ω ι X) (P : Measure Ω)
    (h : S.IsMeasurablyOrderable κ) :
    P.map (fun ω => stepPointMeasure (S.orderedRealization h ω)) =
      S.branchingLaw P := by
  rw [show (fun ω => stepPointMeasure (S.orderedRealization h ω)) =
      S.pointMeasure from funext (S.orderedRealization_pointMeasure h)]
  rfl

/-- The random leftmost displacement is read at the least slot after
measurable ordering. It is optional because a step may have no children. -/
noncomputable def Step.leftmostDisplacement?
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [PartialOrder κ] [OrderBot κ] [LE X] (S : Step Ω ι X)
    (h : S.IsMeasurablyOrderable κ) : Ω → Option X :=
  fun ω => S.orderedRealization h ω ⊥

theorem Step.leftmostDisplacement?_measurable
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [PartialOrder κ] [OrderBot κ] [LE X] (S : Step Ω ι X)
    (h : S.IsMeasurablyOrderable κ) :
    Measurable (S.leftmostDisplacement? h) :=
  (measurable_pi_apply ⊥).comp (S.orderedRealization_measurable h)

/-- On a nonempty realization, the least ordered slot is no larger than every
raw child displacement. -/
theorem Step.leftmostDisplacement?_eq_some_le
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [PartialOrder κ] [OrderBot κ] [LinearOrder X]
    (S : Step Ω ι X) (h : S.IsMeasurablyOrderable κ) (ω : Ω)
    (hne : ∃ j, survive (S ω) j) :
    ∃ x, S.leftmostDisplacement? h ω = some x ∧
      ∀ j y, S ω j = some y → x ≤ y := by
  obtain ⟨j, y, hj⟩ := hne
  obtain ⟨i, hi⟩ := S.raw_child_mem_orderedRealization h ω hj
  have hordered := S.orderedRealization_isOrdered h ω
  have hfirst : survive (S.orderedRealization h ω) ⊥ :=
    orderedSteps_survive_of_le _ hordered bot_le ⟨y, hi⟩
  obtain ⟨x, hx⟩ := hfirst
  refine ⟨x, hx, ?_⟩
  intro k z hk
  obtain ⟨r, hr⟩ := S.raw_child_mem_orderedRealization h ω hk
  by_cases hrbot : r = ⊥
  · subst r
    exact le_of_eq (Option.some.inj (hx.symm.trans hr))
  · exact hordered.2 ⊥ r x z (bot_lt_iff_ne_bot.mpr hrbot) hx hr

end ProbabilityTheory.BranchingRandomWalk
