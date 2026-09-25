import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Option-valued offspring encoding

This is the semantic slot encoding: `some x` is a child at displacement `x`
and `none` is an absent slot.  It is kept separate from the legacy weighted
slot implementation so that the latter can be migrated without changing the
pre-sampled-tree API in one step.
-/

open MeasureTheory
open Classical

namespace ThesisSpeed

abbrev BranchingStep (ι X : Type*) := ι → Option X

/-! `Option` is used only as the presence/absence wrapper.  Giving it the
    discrete measurable structure keeps both constructors measurable for any
    underlying displacement space. -/
instance branchingStepOptionMeasurableSpace {X : Type*} [MeasurableSpace X] :
    MeasurableSpace (Option X) := ⊤

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
  exact (measurable_pi_apply i) (measurableSet_singleton none).compl

def branchingStepPrefixOrdered {ι X : Type*} [LT ι] [LE X]
    (ξ : BranchingStep ι X) : Prop :=
  ∀ i j x y, i < j → ξ i = some x → ξ j = some y → x ≤ y

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
  exact (Measurable.of_discrete (f := fun o : Option X => o.getD 0)).comp
    (measurable_pi_apply i)

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

end ThesisSpeed
