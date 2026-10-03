module

public import Probability.BranchingRandomWalk.Step.Presentation
public import Probability.BranchingRandomWalk.Step.PointMeasure
public import Combinatorics.BranchingWalk.Step.Ordering
public import Combinatorics.BranchingWalk.Step.Potential

/-!
# Measurable ordering of a random branching step

The raw random input is realized as an optional-slot step. A measurably
orderable random step admits a measurable ordered realization that contains
every raw child and preserves the complete point measure. The ordered
realization still has the ordinary deterministic `Step ι X` type;
`orderedSteps` is its property, not a wrapper type.

The slot type is abstract. A least slot is required only when reading the
leftmost displacement. Pointwise existence of an ordering is insufficient:
the ordered realization itself must be measurable.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

/-- A measurable deterministic ordering rule for branching steps.  The rule
reads only the step supplied to it; consequently, when it is applied at a
tree node it cannot inspect marks at other nodes or future generations. -/
structure MeasurableStepOrdering
    (ι κ X : Type*) [MeasurableSpace X] [LT κ]
    (φ : Potential X) where
  ordered : Combinatorics.Branching.Step ι X →
    Combinatorics.Branching.Step κ X
  measurable_ordered : Measurable ordered
  isOrderedBy : ∀ ξ, (ordered ξ).IsOrderedBy φ
  covers : ∀ ξ j y, ξ j = some y → ∃ i, ordered ξ i = some y
  pointMeasure_ordered : ∀ ξ,
    stepPointMeasure (ordered ξ) = stepPointMeasure ξ

instance {ι κ X : Type*} [MeasurableSpace X] [LT κ] {φ : Potential X} :
    CoeFun (MeasurableStepOrdering ι κ X φ)
      (fun _ => Combinatorics.Branching.Step ι X →
        Combinatorics.Branching.Step κ X) :=
  ⟨MeasurableStepOrdering.ordered⟩

/-- The optional first child selected by a deterministic measurable ordering
rule. -/
def MeasurableStepOrdering.first?
    {ι κ X : Type*} [MeasurableSpace X]
    [PartialOrder κ] [OrderBot κ] {φ : Potential X}
    (R : MeasurableStepOrdering ι κ X φ)
    (ξ : Combinatorics.Branching.Step ι X) : Option X :=
  R ξ ⊥

theorem MeasurableStepOrdering.first?_measurable
    {ι κ X : Type*} [MeasurableSpace X]
    [PartialOrder κ] [OrderBot κ] {φ : Potential X}
    (R : MeasurableStepOrdering ι κ X φ) :
    Measurable R.first? :=
  (measurable_pi_apply ⊥).comp R.measurable_ordered

/-- A random step has a measurable ordering when it has a measurable ordered
realization, every raw child occurs in that realization, and the complete
point measure (hence multiplicity) is preserved. -/
def StepPresentation.IsMeasurablyOrderable
    {Ω ι X : Type*} (κ : Type*) [MeasurableSpace Ω] [MeasurableSpace X]
    [LT κ] (φ : Potential X) (S : StepPresentation Ω ι X) : Prop :=
  ∃ T : Ω → Combinatorics.Branching.Step κ X,
    Measurable T ∧
    (∀ ω, (T ω).IsOrderedBy φ) ∧
    (∀ ω j y, S ω j = some y → ∃ i, T ω i = some y) ∧
    ∀ ω, stepPointMeasure (T ω) = S.pointMeasure ω

/-- A deterministic measurable ordering rule supplies a measurable ordering
of every random step by composition. This stronger route preserves the fact
that the ordered observation at a node reads only that node's mark. -/
theorem MeasurableStepOrdering.random_isMeasurablyOrderable
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LT κ] {φ : Potential X} (R : MeasurableStepOrdering ι κ X φ)
    (S : StepPresentation Ω ι X) : S.IsMeasurablyOrderable κ φ := by
  refine ⟨fun ω => R (S ω), R.measurable_ordered.comp S.measurable_toFun,
    fun ω => R.isOrderedBy (S ω), ?_, fun ω => R.pointMeasure_ordered (S ω)⟩
  intro ω j y hj
  exact R.covers (S ω) j y hj

/-- An already measurably realized ordered input supplies its own ordering. -/
theorem StepPresentation.isMeasurablyOrderable_of_isOrdered
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LT ι] (φ : Potential X) (S : StepPresentation Ω ι X)
    (h : ∀ ω, (S ω).IsOrderedBy φ) : S.IsMeasurablyOrderable ι φ := by
  refine ⟨S, S.measurable_toFun, h, ?_, fun _ => rfl⟩
  intro ω j y hj
  exact ⟨j, hj⟩

/-- Choose the measurable ordered realization supplied by the property. -/
noncomputable def StepPresentation.orderedRealization
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LT κ] {φ : Potential X} (S : StepPresentation Ω ι X)
    (h : S.IsMeasurablyOrderable κ φ) :
    Ω → Combinatorics.Branching.Step κ X :=
  Classical.choose h

theorem StepPresentation.orderedRealization_measurable
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LT κ] {φ : Potential X} (S : StepPresentation Ω ι X)
    (h : S.IsMeasurablyOrderable κ φ) :
    Measurable (S.orderedRealization h) :=
  (Classical.choose_spec h).1

theorem StepPresentation.orderedRealization_isOrderedBy
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LT κ] {φ : Potential X} (S : StepPresentation Ω ι X)
    (h : S.IsMeasurablyOrderable κ φ) (ω : Ω) :
    (S.orderedRealization h ω).IsOrderedBy φ :=
  (Classical.choose_spec h).2.1 ω

theorem StepPresentation.raw_child_mem_orderedRealization
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LT κ] {φ : Potential X} (S : StepPresentation Ω ι X)
    (h : S.IsMeasurablyOrderable κ φ) (ω : Ω) {j : ι} {y : X}
    (hj : S ω j = some y) :
    ∃ i, S.orderedRealization h ω i = some y :=
  (Classical.choose_spec h).2.2.1 ω j y hj

/-- Measurable ordering preserves the random point measure exactly. -/
theorem StepPresentation.orderedRealization_pointMeasure
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LT κ] {φ : Potential X} (S : StepPresentation Ω ι X)
    (h : S.IsMeasurablyOrderable κ φ) (ω : Ω) :
    stepPointMeasure (S.orderedRealization h ω) = S.pointMeasure ω :=
  (Classical.choose_spec h).2.2.2 ω

theorem StepPresentation.orderedRealization_pointMeasure_measurable
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable κ] [LT κ] {φ : Potential X}
    (S : StepPresentation Ω ι X) (h : S.IsMeasurablyOrderable κ φ) :
    Measurable (fun ω => stepPointMeasure (S.orderedRealization h ω)) :=
  stepPointMeasure_measurable.comp (S.orderedRealization_measurable h)

/-- Consequently the pushforward point-measure law is unchanged. -/
theorem StepPresentation.orderedRealization_branchingLaw
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] [Countable κ] [LT κ] {φ : Potential X}
    (S : StepPresentation Ω ι X) (P : Measure Ω)
    (h : S.IsMeasurablyOrderable κ φ) :
    P.map (fun ω => stepPointMeasure (S.orderedRealization h ω)) =
      S.branchingLaw P := by
  rw [show (fun ω => stepPointMeasure (S.orderedRealization h ω)) =
      S.pointMeasure from funext (S.orderedRealization_pointMeasure h)]
  rfl

/-- The random leftmost displacement is read at the least slot after
measurable ordering. It is optional because a step may have no children. -/
noncomputable def StepPresentation.leftmostDisplacement?
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [PartialOrder κ] [OrderBot κ] {φ : Potential X} (S : StepPresentation Ω ι X)
    (h : S.IsMeasurablyOrderable κ φ) : Ω → Option X :=
  fun ω => S.orderedRealization h ω ⊥

theorem StepPresentation.leftmostDisplacement?_measurable
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [PartialOrder κ] [OrderBot κ] {φ : Potential X} (S : StepPresentation Ω ι X)
    (h : S.IsMeasurablyOrderable κ φ) :
    Measurable (S.leftmostDisplacement? h) :=
  (measurable_pi_apply ⊥).comp (S.orderedRealization_measurable h)

/-- On a nonempty realization, the least ordered slot is no larger than every
raw child displacement. -/
theorem StepPresentation.leftmostDisplacement?_eq_some_le
    {Ω ι κ X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [PartialOrder κ] [OrderBot κ] {φ : Potential X}
    (S : StepPresentation Ω ι X) (h : S.IsMeasurablyOrderable κ φ) (ω : Ω)
    (hne : ∃ j, survive (S ω) j) :
    ∃ x, S.leftmostDisplacement? h ω = some x ∧
      ∀ j y, S ω j = some y → φ x ≤ φ y := by
  obtain ⟨j, y, hj⟩ := hne
  obtain ⟨i, hi⟩ := S.raw_child_mem_orderedRealization h ω hj
  have hordered := S.orderedRealization_isOrderedBy h ω
  have himap : (S.orderedRealization h ω).map φ i = some (φ y) := by
    simp [hi]
  have hfirstMap : survive ((S.orderedRealization h ω).map φ) ⊥ :=
    orderedSteps_survive_of_le _ hordered bot_le ⟨φ y, himap⟩
  have hfirst : survive (S.orderedRealization h ω) ⊥ :=
    (survive_map_iff φ _ _).1 hfirstMap
  obtain ⟨xmark, hx⟩ := hfirst
  have hxmap : (S.orderedRealization h ω).map φ ⊥ = some (φ xmark) := by
    simp [hx]
  refine ⟨xmark, hx, ?_⟩
  intro k z hk
  obtain ⟨r, hr⟩ := S.raw_child_mem_orderedRealization h ω hk
  have hrmap : (S.orderedRealization h ω).map φ r = some (φ z) := by
    simp [hr]
  by_cases hrbot : r = ⊥
  · subst r
    exact le_of_eq (Option.some.inj (hxmap.symm.trans hrmap))
  · exact hordered.2 ⊥ r (φ xmark) (φ z) (bot_lt_iff_ne_bot.mpr hrbot) hxmap hrmap

end ProbabilityTheory.BranchingRandomWalk
