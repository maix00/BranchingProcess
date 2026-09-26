import MeasureTheory.BranchingWalk.Relation.Basic
import MeasureTheory.BranchingWalk.Step.Basic
import MeasureTheory.BranchingWalk.Step.Measurability

/-!
# Ordered branching steps

`Ordered` is the slot-level property that a single branching step lists its
present children from the left, ordered by mark and without gaps: the present
slots form an initial segment and their marks do not decrease. `markOrdered`
is the increasing mark-order case and `markAntitone` its decreasing mirror;
`orderedSteps` and `antitoneSteps` are the two order-dual sets of such steps.
This file also carries the measurability of both sets.
-/

open MeasureTheory

namespace MeasureTheory

namespace BranchingWalk


/-- The increasing case of `parentRel`, used by the thesis's
left-to-right optional-slot enumeration. -/
def markOrdered {ι X : Type*} [LT ι] [LE X]
    (ξ : Step ι X) : Prop :=
  parentRel (· ≤ ·) ξ

/-- The decreasing mirror image of `markOrdered`. -/
def markAntitone {ι X : Type*} [LT ι] [LE X]
    (ξ : Step ι X) : Prop :=
  parentRel (fun x y => y ≤ x) ξ

/-- The decreasing version is the increasing version read in the dual order. -/
theorem parentAntitone_iff_orderDual {ι X : Type*} [LT ι] [LE X]
    (ξ : Step ι X) :
    markAntitone ξ ↔
      markOrdered (X := OrderDual X)
        (fun i => (ξ i).map OrderDual.toDual) := by
  exact (parentRel_optionMap_iff (fun x y : X => y ≤ x) (· ≤ ·)
    OrderDual.toDual (fun a b => OrderDual.toDual_le_toDual) ξ).symm

/-- An ordered step: absence is parent-closed and the present marks are
increasing in the slot order. -/
def Ordered {ι X : Type*} [LT ι] [LE X]
    (ξ : Step ι X) : Prop :=
  presenceParent ξ ∧ markOrdered ξ

/-- The present slots of a step are listed from the left. -/
abbrev OrderedNatStep {X : Type*} [LE X] (ξ : NatStep X) : Prop :=
  Ordered ξ

/-- The paper's ordered real-valued branching step. -/
abbrev OrderedNatRealStep (ξ : NatRealStep) : Prop := OrderedNatStep ξ

theorem present_of_later
    {ι X : Type*} [LT ι]
    (ξ : Step ι X)
    (hparent : presenceParent ξ)
    {i j : ι} (hij : i < j) (h : present ξ j) :
    present ξ i := by
  classical
  by_contra hi
  simp only [present, not_exists] at hi
  have hnone : ξ i = none := by
    cases hxi : ξ i with
    | none => simp
    | some x => exact (hi x hxi).elim
  obtain ⟨y, hy⟩ := h
  have hjnone := hparent i j hij hnone
  rw [hy] at hjnone
  cases hjnone

/-- A later present slot forces every earlier slot to be present, stated for
the non-strict order so that `i = j` needs no separate case. -/
theorem present_of_le
    {ι X : Type*} [PartialOrder ι]
    (ξ : Step ι X)
    (hparent : presenceParent ξ)
    {i j : ι} (hij : i ≤ j) (h : present ξ j) :
    present ξ i := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact h
  · exact present_of_later ξ hparent hlt h

theorem value'_mono_of_present
    {ι X : Type*} [PartialOrder ι] [Zero X] [Preorder X]
    (ξ : Step ι X) (hordered : markOrdered ξ)
    {i j : ι} (hij : i ≤ j)
    (hi : present ξ i) (hj : present ξ j) :
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
    {i j : ℕ} (hij : i < j) (hj : present ξ j) :
    present ξ i :=
  present_of_later ξ hξ.1 hij hj

theorem orderedNatStep_support_bounded {X : Type*} [LE X]
    (ξ : NatStep X) (_hξ : OrderedNatStep ξ)
    (hfinite : (support ξ).Finite) :
    ∃ n, ∀ i, present ξ i → i < n := by
  classical
  obtain ⟨n, hn⟩ := hfinite.bddAbove
  refine ⟨n + 1, ?_⟩
  intro i hi
  exact lt_of_le_of_lt (hn hi) (Nat.lt_succ_self n)

/-- Steps whose present slots form a parent-closed initial segment and whose
present marks satisfy `rel` in increasing slot order. -/
def orderedStepsOf {ι X : Type*} [LT ι]
    (rel : X → X → Prop) : Set (Step ι X) :=
  {ξ | presenceParent ξ ∧ parentRel rel ξ}

/-- The increasing simultaneous enumeration of the optional children. -/
def orderedSteps {ι X : Type*} [LT ι] [LE X] : Set (Step ι X) :=
  orderedStepsOf (· ≤ ·)

/-- The decreasing mirror image of `orderedSteps`. -/
def antitoneSteps {ι X : Type*} [LT ι] [LE X] : Set (Step ι X) :=
  orderedStepsOf (fun x y => y ≤ x)

theorem mem_orderedSteps_iff {ι X : Type*} [LT ι] [LE X]
    (ξ : Step ι X) :
    ξ ∈ orderedSteps ↔ Ordered ξ := Iff.rfl

theorem mem_antitoneSteps_iff {ι X : Type*} [LT ι] [LE X]
    (ξ : Step ι X) :
    ξ ∈ antitoneSteps ↔ presenceParent ξ ∧ markAntitone ξ := Iff.rfl

/-- Under the ordering condition, a present later slot forces every earlier
slot to be present. -/
theorem orderedSteps_present_of_le {ι X : Type*}
    [PartialOrder ι] [LE X] (ξ : Step ι X)
    (hξ : ξ ∈ orderedSteps) {i j : ι} (hij : i ≤ j)
    (hj : present ξ j) :
    present ξ i :=
  present_of_le ξ hξ.1 hij hj

/-- Optional child values are nondecreasing along the enumeration. -/
theorem orderedSteps_value_mono {ι X : Type*}
    [PartialOrder ι] [Zero X] [Preorder X]
    (ξ : Step ι X) (hξ : ξ ∈ orderedSteps) {i j : ι}
    (hij : i ≤ j) (hj : present ξ j) :
    value' ξ i ≤ value' ξ j :=
  value'_mono_of_present ξ hξ.2 hij
    (present_of_le ξ hξ.1 hij hj) hj

/-- The ambient mark space itself does not enforce the leftmost-slot rule. -/
def unorderedExample : NatRealStep :=
  fun i => if i = 0 then some 1 else if i = 1 then some 0 else none

theorem unorderedExample_not_ordered :
    unorderedExample ∉ orderedSteps := by
  intro h
  have hone : present unorderedExample 1 := by
    simp [unorderedExample, present]
  have hle : value' unorderedExample 0 ≤
      value' unorderedExample 1 :=
    orderedSteps_value_mono unorderedExample h
      (Nat.zero_le 1) hone
  norm_num [unorderedExample, value'] at hle


/-- A condition on two slots that only forbids a later present slot before an
earlier absent one is measurable. -/
private theorem coord_none_measurable {ι X : Type*} [MeasurableSpace X]
    (i : ι) :
    MeasurableSet {ξ : Step ι X | ξ i = none} := by
  rw [show {ξ : Step ι X | ξ i = none} =
      (fun ξ : Step ι X => ξ i) ⁻¹' ({none} : Set (Option X)) from rfl]
  exact (measurable_pi_apply i) measurableSet_option_none

private theorem pairPrefix_measurable {ι X : Type*} [MeasurableSpace X]
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
private theorem pairRel_measurable_of {ι X : Type*} [MeasurableSpace X]
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
    simp only [orderedStepsOf, presenceParent, parentRel,
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
    exact (pairPrefix_measurable i j).inter
      (pairRel_measurable_of rel hgraph i j)
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

end BranchingWalk

end MeasureTheory
