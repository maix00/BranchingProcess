import Combinatorics.BranchingWalk.Step.Relation
import Combinatorics.BranchingWalk.Step.Basic
import Combinatorics.BranchingWalk.Step.Measurability

/-!
# Ordered branching steps

`Ordered` is the slot-level property that a single branching step lists its
survive children from the left, ordered by mark and without gaps: the survive
slots form an initial segment and their marks do not decrease. `IsMonotone`
is the increasing mark-order case and `IsAntitone` its decreasing mirror;
`orderedSteps` and `antitoneSteps` are the two order-dual sets of such steps.
This file also carries the measurability of both sets.
-/

open MeasureTheory

namespace Combinatorics

namespace Branching


/-- The increasing case of `siblingRel`, used by the thesis's
left-to-right optional-slot enumeration. -/
def IsMonotone {ι X : Type*} [LT ι] [LE X]
    (ξ : Step ι X) : Prop :=
  siblingRel (· ≤ ·) ξ

/-- The decreasing mirror image of `IsMonotone`. -/
def IsAntitone {ι X : Type*} [LT ι] [LE X]
    (ξ : Step ι X) : Prop :=
  siblingRel (fun x y => y ≤ x) ξ

/-- The decreasing version is the increasing version read in the dual order. -/
theorem antitone_iff_orderDual {ι X : Type*} [LT ι] [LE X]
    (ξ : Step ι X) :
    IsAntitone ξ ↔
      IsMonotone (X := OrderDual X)
        (fun i => (ξ i).map OrderDual.toDual) := by
  exact (siblingRel_optionMap_iff (fun x y : X => y ≤ x) (· ≤ ·)
    OrderDual.toDual (fun a b => OrderDual.toDual_le_toDual) ξ).symm

/-- An ordered step: absence is parent-closed and the survive marks are
increasing in the slot order. -/
def Step.IsOrdered {ι X : Type*} [LT ι] [LE X]
    (ξ : Step ι X) : Prop :=
  Step.IsSiblingClosed ξ ∧ IsMonotone ξ

/-- A step together with the proof that its existing slot order is already a
standard ordered representation.  This structure does not itself reindex a
raw step: a reindexing construction produces an `OrderedStep` by supplying a
linearly ordered slot type and proving sibling closure and mark monotonicity.

The slot type remains polymorphic.  In the canonical countable representation
used by the branching-random-walk layer it is specialized to `ℕ`; countability
alone would not determine which sibling is the first, second, and so on. -/
structure OrderedStep (ι X : Type*) [LT ι] [LE X] where
  toStep : Step ι X
  siblingClosed : Step.IsSiblingClosed toStep
  monotone : IsMonotone toStep

instance {ι X : Type*} [LT ι] [LE X] :
    CoeFun (OrderedStep ι X) (fun _ => Step ι X) :=
  ⟨OrderedStep.toStep⟩

theorem OrderedStep.isSiblingClosed {ι X : Type*} [LT ι] [LE X]
    (ξ : OrderedStep ι X) :
    Step.IsSiblingClosed ξ := ξ.siblingClosed

theorem OrderedStep.isMonotone {ι X : Type*} [LT ι] [LE X]
    (ξ : OrderedStep ι X) :
    IsMonotone ξ := ξ.monotone

/-- The survive slots of a step are listed from the left. -/
abbrev OrderedNatStep {X : Type*} [LE X] (ξ : NatStep X) : Prop :=
  Step.IsOrdered ξ

/-- The paper's ordered real-valued branching step. -/
abbrev OrderedNatRealStep (ξ : NatRealStep) : Prop := OrderedNatStep ξ

theorem survive_of_later
    {ι X : Type*} [LT ι]
    (ξ : Step ι X)
    (hparent : Step.IsSiblingClosed ξ)
    {i j : ι} (hij : i < j) (h : survive ξ j) :
    survive ξ i := by
  classical
  by_contra hi
  simp only [survive, not_exists] at hi
  have hnone : ξ i = none := by
    cases hxi : ξ i with
    | none => simp
    | some x => exact (hi x hxi).elim
  obtain ⟨y, hy⟩ := h
  have hjnone := hparent i j hij hnone
  rw [hy] at hjnone
  cases hjnone

/-- A later survive slot forces every earlier slot to be survive, stated for
the non-strict order so that `i = j` needs no separate case. -/
theorem survive_of_le
    {ι X : Type*} [PartialOrder ι]
    (ξ : Step ι X)
    (hparent : Step.IsSiblingClosed ξ)
    {i j : ι} (hij : i ≤ j) (h : survive ξ j) :
    survive ξ i := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact h
  · exact survive_of_later ξ hparent hlt h

theorem value'_mono_of_survive
    {ι X : Type*} [PartialOrder ι] [Zero X] [Preorder X]
    (ξ : Step ι X) (hordered : IsMonotone ξ)
    {i j : ι} (hij : i ≤ j)
    (hi : survive ξ i) (hj : survive ξ j) :
    value' ξ i ≤ value' ξ j := by
  rcases hi with ⟨x, hx⟩
  rcases hj with ⟨y, hy⟩
  by_cases heq : i = j
  · subst j
    exact le_rfl
  · have hlt : i < j := lt_of_le_of_ne hij heq
    rw [value'_some ξ i x hx, value'_some ξ j y hy]
    exact hordered i j x y hlt hx hy

theorem orderedNatStep_support_initial {X : Type*} [LE X]
    (ξ : NatStep X) (hξ : OrderedNatStep ξ)
    {i j : ℕ} (hij : i < j) (hj : survive ξ j) :
    survive ξ i :=
  survive_of_later ξ hξ.1 hij hj

theorem orderedNatStep_support_bounded {X : Type*} [LE X]
    (ξ : NatStep X) (_hξ : OrderedNatStep ξ)
    (hfinite : (support ξ).Finite) :
    ∃ n, ∀ i, survive ξ i → i < n := by
  classical
  obtain ⟨n, hn⟩ := hfinite.bddAbove
  refine ⟨n + 1, ?_⟩
  intro i hi
  exact lt_of_le_of_lt (hn hi) (Nat.lt_succ_self n)

/-- Steps whose survive slots form a parent-closed initial segment and whose
survive marks satisfy `rel` in increasing slot order. -/
def orderedStepsOf {ι X : Type*} [LT ι]
    (rel : X → X → Prop) : Set (Step ι X) :=
  {ξ | Step.IsSiblingClosed ξ ∧ siblingRel rel ξ}

/-- The increasing simultaneous enumeration of the optional children. -/
def orderedSteps {ι X : Type*} [LT ι] [LE X] : Set (Step ι X) :=
  orderedStepsOf (· ≤ ·)

/-- The decreasing mirror image of `orderedSteps`. -/
def antitoneSteps {ι X : Type*} [LT ι] [LE X] : Set (Step ι X) :=
  orderedStepsOf (fun x y => y ≤ x)

theorem mem_orderedSteps_iff {ι X : Type*} [LT ι] [LE X]
    (ξ : Step ι X) :
    ξ ∈ orderedSteps ↔ Step.IsOrdered ξ := Iff.rfl

theorem mem_antitoneSteps_iff {ι X : Type*} [LT ι] [LE X]
    (ξ : Step ι X) :
    ξ ∈ antitoneSteps ↔ Step.IsSiblingClosed ξ ∧ IsAntitone ξ := Iff.rfl

/-- Under the ordering condition, a survive later slot forces every earlier
slot to be survive. -/
theorem orderedSteps_survive_of_le {ι X : Type*}
    [PartialOrder ι] [LE X] (ξ : Step ι X)
    (hξ : ξ ∈ orderedSteps) {i j : ι} (hij : i ≤ j)
    (hj : survive ξ j) :
    survive ξ i :=
  survive_of_le ξ hξ.1 hij hj

/-- Optional child values are nondecreasing along the enumeration. -/
theorem orderedSteps_value_mono {ι X : Type*}
    [PartialOrder ι] [Zero X] [Preorder X]
    (ξ : Step ι X) (hξ : ξ ∈ orderedSteps) {i j : ι}
    (hij : i ≤ j) (hj : survive ξ j) :
    value' ξ i ≤ value' ξ j :=
  value'_mono_of_survive ξ hξ.2 hij
    (survive_of_le ξ hξ.1 hij hj) hj

/-- The ambient mark space itself does not enforce the leftmost-slot rule. -/
def unorderedExample : NatRealStep :=
  fun i => if i = 0 then some 1 else if i = 1 then some 0 else none

theorem unorderedExample_not_ordered :
    unorderedExample ∉ orderedSteps := by
  intro h
  have hone : survive unorderedExample 1 := by
    simp [unorderedExample, survive]
  have hle : value' unorderedExample 0 ≤
      value' unorderedExample 1 :=
    orderedSteps_value_mono unorderedExample h
      (Nat.zero_le 1) hone
  norm_num [unorderedExample, value'] at hle


/-- A condition on two slots that only forbids a later survive slot before an
earlier absent one is measurable. -/
private theorem coord_none_measurable {ι X : Type*} [MeasurableSpace X]
    (i : ι) :
    MeasurableSet {ξ : Step ι X | ξ i = none} := by
  rw [show {ξ : Step ι X | ξ i = none} =
      (fun ξ : Step ι X => ξ i) ⁻¹' ({none} : Set (Option X)) from rfl]
  exact (measurable_pi_apply i) measurableSet_option_none

private theorem siblingClosedPair_measurable {ι X : Type*} [MeasurableSpace X]
    (i j : ι) :
    MeasurableSet {ξ : Step ι X | ξ i = none → ξ j = none} := by
  have hi := coord_none_measurable (X := X) i
  have hj := coord_none_measurable (X := X) j
  rw [show {ξ : Step ι X | ξ i = none → ξ j = none} =
      {ξ : Step ι X | ξ i = none}ᶜ ∪
        {ξ : Step ι X | ξ j = none} by
    ext ξ
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_union]
    tauto]
  exact hi.compl.union hj

/-- The pairwise monotonicity condition is measurable as soon as the
comparison graph on the optional slot values is measurable. -/
private theorem siblingRelGraph_measurable_of {ι X : Type*} [MeasurableSpace X]
    (rel : X → X → Prop)
    (hgraph : MeasurableSet {p : Option X × Option X |
      ∀ x y, p.1 = some x → p.2 = some y → rel x y}) (i j : ι) :
    MeasurableSet {ξ : Step ι X |
      ∀ x y, ξ i = some x → ξ j = some y → rel x y} := by
  have hpair : Measurable (fun ξ : Step ι X => (ξ i, ξ j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  simpa only [Set.preimage_ofPred_eq] using hpair hgraph

/-- The comparison graph of the real order is measurable. -/
private theorem optionGraph_le_measurable :
    MeasurableSet {p : Option ℝ × Option ℝ |
      ∀ x y, p.1 = some x → p.2 = some y → x ≤ y} := by
  have hnone : MeasurableSet ({none} : Set (Option ℝ)) :=
    measurableSet_option_none
  have hgetD : Measurable (fun p : Option ℝ × Option ℝ =>
      ((p.1).getD 0, (p.2).getD 0)) :=
    ((measurable_optionGetD 0).comp measurable_fst).prodMk
      ((measurable_optionGetD 0).comp measurable_snd)
  have hle : MeasurableSet {p : Option ℝ × Option ℝ |
      ((p.1).getD 0) ≤ ((p.2).getD 0)} :=
    hgetD measurableSet_le'
  rw [show {p : Option ℝ × Option ℝ |
        ∀ x y, p.1 = some x → p.2 = some y → x ≤ y} =
      ({none} ×ˢ (Set.univ : Set (Option ℝ))) ∪
        ((Set.univ : Set (Option ℝ)) ×ˢ {none}) ∪
          {p : Option ℝ × Option ℝ |
            ((p.1).getD 0) ≤ ((p.2).getD 0)} by
    ext p
    constructor
    · intro h
      by_cases hnone₁ : p.1 = none
      · left
        left
        exact ⟨hnone₁, trivial⟩
      · by_cases hnone₂ : p.2 = none
        · left
          right
          exact ⟨trivial, hnone₂⟩
        · right
          cases hx : p.1 with
          | none => exact absurd hx hnone₁
          | some x =>
            cases hy : p.2 with
            | none => exact absurd hy hnone₂
            | some y => simpa [hx, hy] using h x y hx hy
    · intro h x y hx hy
      rcases h with (hnone₁ | hnone₂) | hle
      · have h₁ : p.1 = none := by simpa [Set.mem_prod] using hnone₁
        simp [h₁] at hx
      · have h₂ : p.2 = none := by simpa [Set.mem_prod] using hnone₂
        simp [h₂] at hy
      · simpa [hx, hy] using hle]
  exact ((hnone.prod MeasurableSet.univ).union
    (MeasurableSet.univ.prod hnone)).union hle

/-- The comparison graph for the reverse order of `ℝ` is measurable. -/
private theorem optionGraph_ge_measurable :
    MeasurableSet {p : Option ℝ × Option ℝ |
      ∀ x y, p.1 = some x → p.2 = some y → y ≤ x} := by
  have hswap : Measurable (fun p : Option ℝ × Option ℝ => (p.2, p.1)) :=
    measurable_snd.prodMk measurable_fst
  have h := hswap optionGraph_le_measurable
  convert h using 1
  ext p
  constructor
  · intro hp x y hx hy
    exact hp y x hy hx
  · intro hp x y hx hy
    exact hp y x hy hx

/-- A relation-ordered slot condition is measurable once its comparison graph
on optional slot values is measurable. -/
theorem orderedStepsOf_measurable_of {ι X : Type*}
    [Countable ι] [MeasurableSpace X] [LT ι]
    (rel : X → X → Prop)
    (hgraph : MeasurableSet {p : Option X × Option X |
      ∀ x y, p.1 = some x → p.2 = some y → rel x y}) :
    MeasurableSet (orderedStepsOf (ι := ι) rel) := by
  have hset : orderedStepsOf (ι := ι) rel = ⋂ i : ι, ⋂ j : ι,
      {ξ : Step ι X |
        (i < j → ξ i = none → ξ j = none) ∧
        (i < j → ∀ x y, ξ i = some x → ξ j = some y → rel x y)} := by
    ext ξ
    simp only [orderedStepsOf, Step.IsSiblingClosed, siblingRel,
      Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h i j
      exact ⟨fun hij => h.1 i j hij,
        fun hij x y hx hy => h.2 i j x y hij hx hy⟩
    · intro h
      exact ⟨fun i j hij => (h i j).1 hij,
        fun i j x y hij hx hy => (h i j).2 hij x y hx hy⟩
  rw [hset]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i < j
  · rw [show {ξ : Step ι X |
          (i < j → ξ i = none → ξ j = none) ∧
          (i < j → ∀ x y, ξ i = some x → ξ j = some y → rel x y)} =
        {ξ : Step ι X | ξ i = none → ξ j = none} ∩
        {ξ : Step ι X |
          ∀ x y, ξ i = some x → ξ j = some y → rel x y} by
      ext ξ
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · intro h
        exact ⟨h.1 hij, h.2 hij⟩
      · intro h
        exact ⟨fun _ => h.1, fun _ => h.2⟩]
    exact (siblingClosedPair_measurable i j).inter
      (siblingRelGraph_measurable_of rel hgraph i j)
  · rw [show {ξ : Step ι X |
          (i < j → ξ i = none → ξ j = none) ∧
          (i < j → ∀ x y, ξ i = some x → ξ j = some y → rel x y)} =
        Set.univ by
      ext ξ
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact ⟨fun h => absurd h hij, fun h => absurd h hij⟩]
    exact MeasurableSet.univ

/-- The increasing ordered-slot condition is measurable once the comparison
graph on optional slot values is measurable. -/
theorem orderedSteps_measurable_of {ι X : Type*}
    [Countable ι] [MeasurableSpace X] [LT ι] [LE X]
    (hgraph : MeasurableSet {p : Option X × Option X |
      ∀ x y, p.1 = some x → p.2 = some y → x ≤ y}) :
    MeasurableSet (orderedSteps (ι := ι) (X := X)) :=
  orderedStepsOf_measurable_of (ι := ι) (X := X) (· ≤ ·) hgraph

/-- The decreasing ordered-slot condition is measurable once the comparison
graph for the reverse order is measurable. -/
theorem antitoneSteps_measurable_of {ι X : Type*}
    [Countable ι] [MeasurableSpace X] [LT ι] [LE X]
    (hgraph : MeasurableSet {p : Option X × Option X |
      ∀ x y, p.1 = some x → p.2 = some y → y ≤ x}) :
    MeasurableSet (antitoneSteps (ι := ι) (X := X)) :=
  orderedStepsOf_measurable_of (ι := ι) (X := X)
    (fun x y : X => y ≤ x) hgraph

/-- The thesis's real-valued increasing ordered-slot condition is
measurable. -/
theorem orderedSteps_measurable {ι : Type*} [Countable ι] [LT ι] :
    MeasurableSet (orderedSteps (ι := ι) (X := ℝ)) :=
  orderedSteps_measurable_of (ι := ι) (X := ℝ) optionGraph_le_measurable

/-- The reverse real-valued ordered-slot condition is measurable. -/
theorem antitoneSteps_measurable {ι : Type*} [Countable ι] [LT ι] :
    MeasurableSet (antitoneSteps (ι := ι) (X := ℝ)) :=
  antitoneSteps_measurable_of (ι := ι) (X := ℝ) optionGraph_ge_measurable

section IsOrderable

variable {ι X : Type*} [LT ι] [Preorder X]

/-- A step is orderable when an injective relabeling of its slots makes it both sibling closed and
increasing: the surviving slots become an initial segment and their marks increase along the slot
order. This is the thesis's normal form of a step, listing the children from the left by increasing
displacement. The relabeling is a pullback on the slots, and the direction of the mark comparison is
the one of `X`, so the mirrored form is read in `OrderDual X` rather than by exchanging anything. -/
class Step.IsOrderable (ξ : Step ι X) : Prop where
  exists_relabel : ∃ f : ι → ι, Function.Injective f ∧
    Step.IsSiblingClosed (fun i => ξ (f i)) ∧ IsMonotone (fun i => ξ (f i))

/-- A step that is already sibling closed and increasing is orderable: the identity relabels nothing. -/
theorem Step.isOrderable_of_isSiblingClosed_of_isMonotone {ξ : Step ι X}
    (hclosed : Step.IsSiblingClosed ξ) (hmono : IsMonotone ξ) : Step.IsOrderable ξ :=
  ⟨id, Function.injective_id, hclosed, hmono⟩

/-- On a pair of a slot type and a mark type, every step is orderable. This is the strong form of the
property, and it is a property of the pair rather than of a step: it fails for a mark type in which a
family of children has no leftmost member, whatever the slot type. Finiteness of the support is a
sufficient condition and not the definition — `Step.IsFinitelySupported` states it — and a step with
infinitely many children is orderable as soon as those children can be listed from the left with
nondecreasing marks. -/
def IsOrderable (ι X : Type*) [LT ι] [Preorder X] : Prop :=
  ∀ ξ : Step ι X, Step.IsOrderable ξ

/-- A step has an increasing enumeration of its children when they can be listed in one go, without gaps
and with marks that do not decrease: a slot `n` and an injection `e` whose range is exactly the children,
its domain the initial segment below `n`, along which an earlier member of the listing never carries a
larger mark. Finiteness is not asked — an infinite family of children has one as soon as it can be counted
from the left with nondecreasing marks, and that is the case in which the step is orderable. The domain is an initial
segment: `Step.IsSiblingClosed` says that an absent slot forces every larger one absent, so the surviving
slots are the initial segment and the children of a closed step are the leftmost slots. -/
def Step.HasIncreasingEnumeration (ξ : Step ι X) : Prop :=
  ∃ n : ι, ∃ e : ι → ι, Function.Injective e ∧ (∀ i, i < n → survive ξ (e i)) ∧
    (∀ j, survive ξ j → ∃ i, i < n ∧ e i = j) ∧
    ∀ i j, i < j → j < n → ∀ x y, ξ (e i) = some x → ξ (e j) = some y → x ≤ y

end IsOrderable

end Branching

end Combinatorics
