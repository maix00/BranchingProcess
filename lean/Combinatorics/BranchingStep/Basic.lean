import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Option-valued child-slot encoding

This is the semantic slot encoding: `some x` is a child at displacement `x`
and `none` is an absent slot.  Absence is a first-class value, so a slot field
may have no children at all.
-/

open MeasureTheory
open Classical

/-- A branching step: one optional child mark per slot label. -/
abbrev BranchingStep (ι X : Type*) := ι → Option X

namespace BranchingStep


/-! `Option` is the presence/absence wrapper. Its measurable structure is the
    disjoint-union one: a set is measurable exactly when its `some`-part is a
    measurable subset of `X`. This makes `some` measurable, `none` a measurable
    point, and `getD d` measurable — the three facts the slot calculus needs.
    The discrete structure would make `some` non-measurable and would therefore
    destroy the measurability of a step constructed from a measure. -/
instance branchingStepOptionMeasurableSpace {X : Type*} [MeasurableSpace X] :
    MeasurableSpace (Option X) where
  MeasurableSet' s := MeasurableSet (some ⁻¹' s)
  measurableSet_empty := by
    rw [show (some ⁻¹' (∅ : Set (Option X))) = (∅ : Set X) by
      ext x
      simp]
    exact MeasurableSet.empty
  measurableSet_compl s hs := by
    simp [Set.preimage_compl, hs]
  measurableSet_iUnion f hf := by
    simpa [Set.preimage_iUnion] using MeasurableSet.iUnion hf

/-- `none` is a measurable point of the disjoint-union structure. -/
theorem measurableSet_option_none {X : Type*} [MeasurableSpace X] :
    MeasurableSet ({none} : Set (Option X)) := by
  change MeasurableSet (some ⁻¹' ({none} : Set (Option X)))
  rw [show (some ⁻¹' ({none} : Set (Option X))) = (∅ : Set X) by
    ext x
    simp]
  exact MeasurableSet.empty

/-- The image of a measurable set under `some` is measurable. -/
theorem measurableSet_option_some_image {X : Type*} [MeasurableSpace X]
    {s : Set X} (hs : MeasurableSet s) :
    MeasurableSet (some '' s) := by
  change MeasurableSet (some ⁻¹' (some '' s))
  rwa [Set.preimage_image_eq s (Option.some_injective X)]

/-- The presence constructor is measurable. -/
theorem measurable_option_some {X : Type*} [MeasurableSpace X] :
    Measurable (some : X → Option X) := by
  intro s hs
  exact hs

/-- Substituting a default value on the absent slot is measurable. -/
theorem measurable_optionGetD {X : Type*} [MeasurableSpace X] (d : X) :
    Measurable (fun o : Option X => o.getD d) := by
  intro s hs
  change MeasurableSet (some ⁻¹' ((fun o : Option X => o.getD d) ⁻¹' s))
  rw [show (some ⁻¹' ((fun o : Option X => o.getD d) ⁻¹' s)) = s by
    ext x
    simp]
  exact hs

/-! The measurable structure on a branching step is the coordinate-wise
    measurable structure.  This belongs to the abstract step layer; concrete
    point-process realizations may add further structure later. -/
instance branchingStepMeasurableSpace {ι X : Type*} [MeasurableSpace X] :
    MeasurableSpace (BranchingStep ι X) := MeasurableSpace.pi

def branchingStepPresent {ι X : Type*}
    (ξ : BranchingStep ι X) (i : ι) : Prop := ∃ x, ξ i = some x

theorem branchingStepPresent_iff_ne_none {ι X : Type*}
    (ξ : BranchingStep ι X) (i : ι) :
    branchingStepPresent ξ i ↔ ξ i ≠ none := by
  cases h : ξ i with
  | none => simp [branchingStepPresent, h]
  | some x => simp [branchingStepPresent, h]

theorem branchingStepPresent_measurableSet
    {ι X : Type*} [MeasurableSpace X] (i : ι) :
    MeasurableSet {ξ : BranchingStep ι X | branchingStepPresent ξ i} := by
  rw [show {ξ : BranchingStep ι X | branchingStepPresent ξ i} =
      (fun ξ : BranchingStep ι X => ξ i) ⁻¹' ({none}ᶜ) by
        ext ξ
        simp [branchingStepPresent_iff_ne_none]]
  exact (measurable_pi_apply i) measurableSet_option_none.compl

/-- The slots present in `ξ` are listed in the order prescribed by the binary
relation `rel`: an earlier slot never compares above a later one. The relation
is an explicit parameter, so the increasing and the decreasing enumeration of
the same step are two instances of one definition rather than two separate
constructions. This is what makes the condition left--right symmetric; the
order-dual form is `branchingStepPrefixRel_optionMap_iff`. -/
def branchingStepPrefixRel {ι X : Type*} [LT ι]
    (rel : X → X → Prop) (ξ : BranchingStep ι X) : Prop :=
  ∀ i j x y, i < j → ξ i = some x → ξ j = some y → rel x y

/-- The increasing case of `branchingStepPrefixRel`, used by the thesis's
left-to-right optional-slot enumeration. -/
def branchingStepPrefixOrdered {ι X : Type*} [LT ι] [LE X]
    (ξ : BranchingStep ι X) : Prop :=
  branchingStepPrefixRel (· ≤ ·) ξ

/-- The decreasing mirror image of `branchingStepPrefixOrdered`. -/
def branchingStepPrefixAntitone {ι X : Type*} [LT ι] [LE X]
    (ξ : BranchingStep ι X) : Prop :=
  branchingStepPrefixRel (fun x y => y ≤ x) ξ

/-- Left--right symmetry of the ordering condition, in the form used by the
thesis: transporting a step along an order embedding turns the condition for
one relation into the condition for the other. Reversing the order on the
marks (`e = OrderDual.toDual`) is the instance that swaps "from the left" and
"from the right"; no direction is singled out by the definition. -/
theorem branchingStepPrefixRel_optionMap_iff {ι X Y : Type*} [LT ι]
    (rel : X → X → Prop) (rel' : Y → Y → Prop) (e : X → Y)
    (he : ∀ a b, rel' (e a) (e b) ↔ rel a b) (ξ : BranchingStep ι X) :
    branchingStepPrefixRel rel' (fun i => (ξ i).map e) ↔
      branchingStepPrefixRel rel ξ := by
  constructor
  · intro h i j x y hij hx hy
    exact (he x y).1 (h i j (e x) (e y) hij
      (by simp [hx]) (by simp [hy]))
  · intro h i j x y hij hx hy
    rcases Option.map_eq_some_iff.1 hx with ⟨a, ha, rfl⟩
    rcases Option.map_eq_some_iff.1 hy with ⟨b, hb, rfl⟩
    exact (he a b).2 (h i j a b hij ha hb)

/-- The decreasing version is the increasing version read in the dual order. -/
theorem branchingStepPrefixAntitone_iff_orderDual {ι X : Type*} [LT ι] [LE X]
    (ξ : BranchingStep ι X) :
    branchingStepPrefixAntitone ξ ↔
      branchingStepPrefixOrdered (X := OrderDual X)
        (fun i => (ξ i).map OrderDual.toDual) := by
  exact (branchingStepPrefixRel_optionMap_iff (fun x y : X => y ≤ x) (· ≤ ·)
    OrderDual.toDual (fun a b => OrderDual.toDual_le_toDual) ξ).symm

def branchingStepPresencePrefix {ι X : Type*} [LT ι]
    (ξ : BranchingStep ι X) : Prop :=
  ∀ i j, i < j → ξ i = none → ξ j = none

def OrderedBranchingStep {ι X : Type*} [LT ι] [LE X]
    (ξ : BranchingStep ι X) : Prop :=
  branchingStepPresencePrefix ξ ∧ branchingStepPrefixOrdered ξ

def branchingStepIncrement {X : Type*} [Zero X]
    (ξ : BranchingStep ι X) (i : ι) : X :=
  (ξ i).getD 0

theorem branchingStepIncrement_measurable
    {ι X : Type*} [MeasurableSpace X] [Zero X] (i : ι) :
    Measurable (fun ξ : BranchingStep ι X => branchingStepIncrement ξ i) := by
  unfold branchingStepIncrement
  exact (measurable_optionGetD (0 : X)).comp (measurable_pi_apply i)

theorem branchingStepIncrement_none {ι X : Type*} [Zero X]
    (ξ : BranchingStep ι X) (i : ι) (h : ξ i = none) :
    branchingStepIncrement ξ i = 0 := by
  simp [branchingStepIncrement, h]

theorem branchingStepIncrement_some {ι X : Type*} [Zero X]
    (ξ : BranchingStep ι X) (i : ι) (x : X) (h : ξ i = some x) :
    branchingStepIncrement ξ i = x := by
  simp [branchingStepIncrement, h]

def branchingStepSupport {ι X : Type*} (ξ : BranchingStep ι X) : Set ι :=
  {i | branchingStepPresent ξ i}

theorem branchingStep_support_finite_of_fintype
    {ι X : Type*} [Fintype ι] (ξ : BranchingStep ι X) :
    (branchingStepSupport ξ).Finite := Set.toFinite _

theorem branchingStep_value_of_present
    {ι X : Type*} (ξ : BranchingStep ι X) {i : ι}
    (hi : branchingStepPresent ξ i) : ∃ x, ξ i = some x := hi

theorem branchingStep_present_of_later
    {ι X : Type*} [LT ι]
    (ξ : BranchingStep ι X)
    (hprefix : branchingStepPresencePrefix ξ)
    {i j : ι} (hij : i < j) (h : branchingStepPresent ξ j) :
    branchingStepPresent ξ i := by
  classical
  by_contra hi
  simp only [branchingStepPresent, not_exists] at hi
  have hnone : ξ i = none := by
    cases hxi : ξ i with
    | none => simpa [hxi]
    | some x => exact (hi x hxi).elim
  obtain ⟨y, hy⟩ := h
  have hjnone := hprefix i j hij hnone
  rw [hy] at hjnone
  cases hjnone

/-- A later present slot forces every earlier slot to be present, stated for
the non-strict order so that `i = j` needs no separate case. -/
theorem branchingStep_present_of_le
    {ι X : Type*} [PartialOrder ι]
    (ξ : BranchingStep ι X)
    (hprefix : branchingStepPresencePrefix ξ)
    {i j : ι} (hij : i ≤ j) (h : branchingStepPresent ξ j) :
    branchingStepPresent ξ i := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact h
  · exact branchingStep_present_of_later ξ hprefix hlt h

theorem branchingStepIncrement_mono_of_present
    {X : Type*} [Zero X] [Preorder X]
    (ξ : BranchingStep ℕ X) (hordered : branchingStepPrefixOrdered ξ)
    {i j : ℕ} (hij : i ≤ j)
    (hi : branchingStepPresent ξ i) (hj : branchingStepPresent ξ j) :
    branchingStepIncrement ξ i ≤ branchingStepIncrement ξ j := by
  rcases hi with ⟨x, hx⟩
  rcases hj with ⟨y, hy⟩
  by_cases heq : i = j
  · subst j
    exact le_rfl
  · have hlt : i < j := lt_of_le_of_ne hij heq
    rw [branchingStepIncrement_some ξ i x hx,
      branchingStepIncrement_some ξ j y hy]
    exact hordered i j x y hlt hx hy

abbrev NatRealBranchingStep := BranchingStep ℕ ℝ

def branchingStepChildPresent (ξ : NatRealBranchingStep) (i : ℕ) : Prop :=
  branchingStepPresent ξ i

def branchingStepNatRealOrdered (ξ : NatRealBranchingStep) : Prop :=
  branchingStepPrefixOrdered ξ

def branchingStepNatRealPresencePrefix (ξ : NatRealBranchingStep) : Prop :=
  branchingStepPresencePrefix ξ

def OrderedNatRealBranchingStep (ξ : NatRealBranchingStep) : Prop :=
  OrderedBranchingStep ξ

theorem orderedNatRealBranchingStep_support_initial
    (ξ : NatRealBranchingStep) (hξ : OrderedNatRealBranchingStep ξ)
    {i j : ℕ} (hij : i < j) (hj : branchingStepChildPresent ξ j) :
    branchingStepChildPresent ξ i :=
  branchingStep_present_of_later ξ hξ.1 hij hj

theorem orderedNatRealBranchingStep_support_bounded
    (ξ : NatRealBranchingStep) (hξ : OrderedNatRealBranchingStep ξ)
    (hfinite : (branchingStepSupport ξ).Finite) :
    ∃ n, ∀ i, branchingStepChildPresent ξ i → i < n := by
  classical
  obtain ⟨n, hn⟩ := hfinite.bddAbove
  refine ⟨n + 1, ?_⟩
  intro i hi
  exact lt_of_le_of_lt (hn hi) (Nat.lt_succ_self n)

end BranchingStep
