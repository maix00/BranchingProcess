import MeasureTheory.BranchingWalk.Step.Basic
import MeasureTheory.BranchingWalk.Step.Measurability
import MeasureTheory.BranchingWalk.Step.Ordered.Basic

/-!
# Measurable ordered child marks

The thesis writes `Ξ₁`, `Ξ₂`, ... for the successive optional children of a
parent, listed from the left. The ordering condition is the abstract
`OrderedStep`: the present slots form an initial segment and their
displacements do not decrease. Nothing in the condition refers to `ℝ`.
The relation is an explicit parameter, so increasing and decreasing
enumerations are the two order-dual instances of one construction. The
measurability of each instance is reduced to the measurability of the
comparison graph on `Option X × Option X`; the real-line specialization then
discharges both hypotheses from the Borel order on `ℝ`.

The underlying sets `orderedStepsOf`, `orderedSteps`, and `antitoneSteps` are
defined in `Step/Ordered/Basic.lean`; this file adds their measurability.
-/

open MeasureTheory

namespace MeasureTheory

namespace BranchingWalk

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
