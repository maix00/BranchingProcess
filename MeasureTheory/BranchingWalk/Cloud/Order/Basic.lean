import MeasureTheory.BranchingWalk.Displace.Node
import MeasureTheory.BranchingWalk.Step.Value
import MeasureTheory.BranchingWalk.Step.Prefix
import MeasureTheory.BranchingWalk.Step.Slot

/-!
# Ordered child marks

The thesis writes `Ξ₁`, `Ξ₂`, ... for the successive optional children of a
parent, listed from the left. The ordering condition is the abstract
`OrderedStep`: the present slots form an initial segment and their
displacements do not decrease. Nothing in the condition refers to `ℝ`.
The measurability of the condition is reduced to the measurability of the
comparison graph on `Option X × Option X`; the real-line specialization then
discharges that hypothesis from the Borel order on `ℝ`.
-/

open MeasureTheory

namespace MeasureTheory

namespace BranchingWalk

open MeasureTheory.UlamHarris



/-- The child steps whose optional slots are enumerated from the left. The
value type is arbitrary; measurability is reduced below to a comparison-graph
hypothesis on `Option X × Option X`. -/
def orderedSteps {X : Type*} [LE X] : Set (NatStep X) :=
  {ξ | OrderedStep ξ}

theorem mem_orderedSteps_iff {X : Type*} [LE X] (ξ : NatStep X) :
    ξ ∈ orderedSteps ↔ OrderedStep ξ := Iff.rfl

/-- A condition on two slots that only forbids a later present slot before an
earlier absent one is measurable. -/
private theorem coord_none_measurable {X : Type*} [MeasurableSpace X]
    (i : ℕ) :
    MeasurableSet {ξ : NatStep X | ξ i = none} := by
  rw [show {ξ : NatStep X | ξ i = none} =
      (fun ξ : NatStep X => ξ i) ⁻¹' ({none} : Set (Option X)) from rfl]
  exact (measurable_pi_apply i) measurableSet_option_none

private theorem pairPrefix_measurable {X : Type*} [MeasurableSpace X]
    (i j : ℕ) :
    MeasurableSet {ξ : NatStep X | ξ i = none → ξ j = none} := by
  have hi := coord_none_measurable (X := X) i
  have hj := coord_none_measurable (X := X) j
  rw [show {ξ : NatStep X | ξ i = none → ξ j = none} =
      {ξ : NatStep X | ξ i = none}ᶜ ∪
        {ξ : NatStep X | ξ j = none} by
    ext ξ
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_union]
    tauto]
  exact hi.compl.union hj

/-- The pairwise monotonicity condition is measurable as soon as the
comparison graph on the optional slot values is measurable. -/
private theorem pairOrdered_measurable_of {X : Type*} [MeasurableSpace X] [LE X]
    (hgraph : MeasurableSet {p : Option X × Option X |
      ∀ x y, p.1 = some x → p.2 = some y → x ≤ y}) (i j : ℕ) :
    MeasurableSet {ξ : NatStep X |
      ∀ x y, ξ i = some x → ξ j = some y → x ≤ y} := by
  have hpair : Measurable (fun ξ : NatStep X => (ξ i, ξ j)) :=
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

/-- The ordered-slot condition is measurable once the comparison graph on
optional slot values is measurable. -/
theorem orderedSteps_measurable_of {X : Type*} [MeasurableSpace X] [LE X]
    (hgraph : MeasurableSet {p : Option X × Option X |
      ∀ x y, p.1 = some x → p.2 = some y → x ≤ y}) :
    MeasurableSet (orderedSteps (X := X)) := by
  have hset : orderedSteps (X := X) = ⋂ i : ℕ, ⋂ j : ℕ,
      {ξ : NatStep X |
        (i < j → ξ i = none → ξ j = none) ∧
        (i < j → ∀ x y, ξ i = some x → ξ j = some y → x ≤ y)} := by
    ext ξ
    simp only [orderedSteps, OrderedStep, presencePrefix,
      prefixOrdered, prefixRel, Set.mem_ofPred_eq,
      Set.mem_iInter]
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
  · rw [show {ξ : NatStep X |
          (i < j → ξ i = none → ξ j = none) ∧
          (i < j → ∀ x y, ξ i = some x → ξ j = some y → x ≤ y)} =
        {ξ : NatStep X | ξ i = none → ξ j = none} ∩
        {ξ : NatStep X |
          ∀ x y, ξ i = some x → ξ j = some y → x ≤ y} by
      ext ξ
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · intro h
        exact ⟨h.1 hij, h.2 hij⟩
      · intro h
        exact ⟨fun _ => h.1, fun _ => h.2⟩]
    exact (pairPrefix_measurable i j).inter
      (pairOrdered_measurable_of hgraph i j)
  · rw [show {ξ : NatStep X |
          (i < j → ξ i = none → ξ j = none) ∧
          (i < j → ∀ x y, ξ i = some x → ξ j = some y → x ≤ y)} =
        Set.univ by
      ext ξ
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact ⟨fun h => absurd h hij, fun h => absurd h hij⟩]
    exact MeasurableSet.univ

/-- The thesis's real-valued ordered-slot condition is measurable. -/
theorem orderedSteps_measurable :
    MeasurableSet (orderedSteps (X := ℝ)) :=
  orderedSteps_measurable_of (X := ℝ) optionGraph_le_measurable

/-- Under the ordering condition a later present slot forces slot zero to be
present: the leftmost optional child exists whenever any child does. -/
theorem orderedSteps_first_present {X : Type*} [LE X] (ξ : NatStep X)
    (hξ : ξ ∈ orderedSteps) (i : ℕ) (hi : ξ ∈ childPresent i) :
    ξ ∈ childPresent 0 :=
  present_of_le ξ hξ.1 (Nat.zero_le i) hi

/-- Optional child values are nondecreasing along the enumeration. -/
theorem orderedSteps_value_mono {X : Type*} [Zero X] [Preorder X]
    (ξ : NatStep X) (hξ : ξ ∈ orderedSteps) {i j : ℕ}
    (hij : i ≤ j) (hj : ξ ∈ childRealized j) :
    value ξ i ≤ value ξ j :=
  value_mono_of_present ξ hξ.2 hij
    (present_of_le ξ hξ.1 hij hj) hj

/-- The ambient mark space itself does not enforce the leftmost-slot rule. -/
def unorderedExample : NatRealStep :=
  fun i => if i = 0 then some 1 else if i = 1 then some 0 else none

theorem unorderedExample_not_ordered :
    unorderedExample ∉ orderedSteps := by
  intro h
  have hone : unorderedExample ∈ childPresent 1 := by
    simp [unorderedExample, childPresent, present]
  have hle : value unorderedExample 0 ≤
      value unorderedExample 1 :=
    orderedSteps_value_mono unorderedExample h
      (Nat.zero_le 1) hone
  norm_num [unorderedExample, value] at hle

end BranchingWalk

end MeasureTheory
