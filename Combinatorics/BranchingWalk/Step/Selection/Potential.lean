/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Potential
public import Combinatorics.BranchingWalk.Step.Ordering.ByPotential
public import Combinatorics.BranchingWalk.Step.Selection.Finite
public import Combinatorics.BranchingWalk.Step.Selection.Slot
public import Combinatorics.BranchingWalk.Step.Measure.ExponentialWeight

/-!
# Potential-based finite selections from a branching step

These operations select children by a measurable real-valued potential. A
finite lower section of the potential value, with the slot order as a tie
breaker, guarantees that the first-`N` segment exists.

## Public declarations

- `Combinatorics.Branching.Step.FiniteSelection.belowPotential R φ a`
  retains `i ∈ R ξ` when `ξ.potentialValue' φ i ≤ a`.
- `Combinatorics.Branching.Step.FiniteSelection.firstSelectedSlotPositivePotential R φ`
  is the one-step observable
  $\xi\mapsto\max\{0,\xi.\mathrm{potentialValue}'(\varphi,
  \mathrm{firstSelectedSlot}(R,\xi))\}$.
- `Combinatorics.Branching.Step.FiniteSelection.firstNByPotential N φ h`
  selects by `(ξ.potentialValue' φ i, i)`;
  `Combinatorics.Branching.Step.FiniteSelection.admitsFirstNByPotential_of_level_finite`
  constructs the required existence witness when every lower potential level
  is finite.
- `Combinatorics.Branching.Step.FiniteSelection.admitsFirstNByPotential_of_totalChildWeight_ne_top`
  states that finite total negative exponential weight in the real-mark model
  gives existence of the first-`N` potential selection.
- `Combinatorics.Branching.Step.FiniteSelection.preserveFirstBelowPotential`
  retains the first child and the first-`N` potential segment below `a`;
  `Combinatorics.Branching.Step.FiniteSelection.mem_preserveFirstBelowPotential_iff`
  gives membership, and
  `Combinatorics.Branching.Step.FiniteSelection.preserveFirstBelowPotential_isBoundedBy`
  proves the selected cardinality is at most `N` when `1 ≤ N`.
- `firstOnlySelectedChild R` retains the least slot of `R ξ`, and
  `reserveSelectionBelowPotential R φ M` retains this first child together
  with the selected children whose potential is at most `M`.
- `reserveSelectionBelowPotential_subset` and
  `reserveSelectionBelowPotential_isBoundedBy` give inclusion and capacity;
  `reserveSelectionBelowPotential_nonempty_of_selected_nonempty` preserves
  nonemptiness, and
  `reserveSelectionBelowPotential_card_ge_two_of_boundedSecond` gives a split
  when the second selected child's potential is at most the cutoff.
- `potentialValue'_firstSelectedSlot_le_second_of_ordered` compares the
  selected children's potentials on an ordered step.
-/

@[expose] public section

namespace Combinatorics.Branching

namespace Step.FiniteSelection

variable {α X : Type*}

open Selection.NSelection

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Kill selected children whose potential exceeds a threshold. -/
noncomputable def belowPotential [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (φ : Potential X) (a : ℝ) :
    Step.FiniteSelection α X :=
  R.filter fun ξ i => ξ.potentialValue' φ i ≤ a

/-- Keep only the least slot in a finite selected family. -/
noncomputable def firstOnlySelectedChild [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) : Step.FiniteSelection α X :=
  R.filter fun ξ i => i = firstSelectedSlot R ξ

/-- The positive part of the potential at the first slot selected by `R`.
This is an observable of the selected child slot, with no distinguished label
or probability law built into its definition. -/
noncomputable def firstSelectedSlotPositivePotential
    [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (φ : Potential X) : Step α X → ℝ :=
  fun ξ => max 0 (ξ.potentialValue' φ (firstSelectedSlot R ξ))

/-- Retain the least selected slot unconditionally and retain every other
selected slot whose potential is at most the cutoff. -/
noncomputable def reserveSelectionBelowPotential
    [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (φ : Potential X) (M : ℝ) :
    Step.FiniteSelection α X where
  select ξ := firstOnlySelectedChild R ξ ∪ (R.belowPotential φ M) ξ
  subset_support ξ i hi := by
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (firstOnlySelectedChild R).subset_support ξ i hi
    · exact (R.belowPotential φ M).subset_support ξ i hi

theorem reserveSelectionBelowPotential_subset
    [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (φ : Potential X) (M : ℝ)
    (ξ : Step α X) :
    reserveSelectionBelowPotential R φ M ξ ⊆ R ξ := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact (Step.FiniteSelection.mem_filter R
      (fun ξ i => i = firstSelectedSlot R ξ) ξ i).mp hi |>.1
  · exact (Step.FiniteSelection.mem_filter R
      (fun ξ i => ξ.potentialValue' φ i ≤ M) ξ i).mp (by
        simpa [Step.FiniteSelection.belowPotential] using hi) |>.1

theorem reserveSelectionBelowPotential_isBoundedBy
    [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (φ : Potential X) (M : ℝ)
    {N : ℕ} (hR : R.IsBoundedBy N) :
    (reserveSelectionBelowPotential R φ M).IsBoundedBy N := by
  intro ξ
  exact (Finset.card_le_card
    (reserveSelectionBelowPotential_subset R φ M ξ)).trans (hR ξ)

theorem firstOnlySelectedChild_nonempty_of_selected_nonempty
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hne : (R ξ).Nonempty) :
    (firstOnlySelectedChild R ξ).Nonempty := by
  have hfirst := firstSelectedSlot_mem R ξ hne
  refine ⟨firstSelectedSlot R ξ, ?_⟩
  rw [firstOnlySelectedChild, Step.FiniteSelection.mem_filter]
  exact ⟨hfirst, rfl⟩

theorem reserveSelectionBelowPotential_nonempty_of_selected_nonempty
    [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (φ : Potential X) (M : ℝ)
    (ξ : Step α X) (hne : (R ξ).Nonempty) :
    (reserveSelectionBelowPotential R φ M ξ).Nonempty := by
  obtain ⟨i, hi⟩ := firstOnlySelectedChild_nonempty_of_selected_nonempty
    R ξ hne
  exact ⟨i, Finset.mem_union.mpr (Or.inl hi)⟩

theorem reserveSelectionBelowPotential_card_ge_two_of_boundedSecond
    [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (φ : Potential X) (M : ℝ)
    (ξ : Step α X) (hcard : 2 ≤ (R ξ).card)
    (hbound : ξ.potentialValue' φ (secondSelectedSlot R ξ) ≤ M) :
    2 ≤ (reserveSelectionBelowPotential R φ M ξ).card := by
  have hslots := secondSelectedSlot_mem_of_card R ξ hcard
  have hfirst : firstSelectedSlot R ξ ∈ R ξ :=
    firstSelectedSlot_mem R ξ (Finset.card_pos.mp (by omega))
  have hfirstOnly : firstSelectedSlot R ξ ∈ firstOnlySelectedChild R ξ := by
    rw [firstOnlySelectedChild, Step.FiniteSelection.mem_filter]
    exact ⟨hfirst, rfl⟩
  have hsecondBelow : secondSelectedSlot R ξ ∈ (R.belowPotential φ M) ξ := by
    simp [Step.FiniteSelection.belowPotential,
      Step.FiniteSelection.mem_filter, hslots.1, hbound]
  have hfirstReserve : firstSelectedSlot R ξ ∈
      reserveSelectionBelowPotential R φ M ξ :=
    Finset.mem_union.mpr (Or.inl hfirstOnly)
  have hsecondReserve : secondSelectedSlot R ξ ∈
      reserveSelectionBelowPotential R φ M ξ :=
    Finset.mem_union.mpr (Or.inr hsecondBelow)
  have hlt : 1 < (reserveSelectionBelowPotential R φ M ξ).card :=
    Finset.one_lt_card_iff.mpr
      ⟨firstSelectedSlot R ξ, secondSelectedSlot R ξ,
        hfirstReserve, hsecondReserve, hslots.2⟩
  omega

theorem reserveSelectionBelowPotential_card_ge_two_iff_boundedSecond
    [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : R.IsBoundedBy 2)
    (φ : Potential X) (M : ℝ) (ξ : Step α X) :
    2 ≤ (reserveSelectionBelowPotential R φ M ξ).card ↔
      2 ≤ (R ξ).card ∧
        ξ.potentialValue' φ (secondSelectedSlot R ξ) ≤ M := by
  constructor
  · intro hsplit
    have hsubset := reserveSelectionBelowPotential_subset R φ M ξ
    have hScard_le :
        (reserveSelectionBelowPotential R φ M ξ).card ≤ (R ξ).card :=
      Finset.card_le_card hsubset
    have hRcap : (R ξ).card ≤ 2 := hR ξ
    have hRcard : (R ξ).card = 2 := by omega
    have hSeq : reserveSelectionBelowPotential R φ M ξ = R ξ := by
      apply Finset.eq_of_subset_of_card_le hsubset
      rw [hRcard]
      exact hsplit
    have hsecond := secondSelectedSlot_mem_of_card R ξ
      (by omega : 2 ≤ (R ξ).card)
    have hsecondS : secondSelectedSlot R ξ ∈
        reserveSelectionBelowPotential R φ M ξ := by
      rw [hSeq]
      exact hsecond.1
    have hunion : secondSelectedSlot R ξ ∈
        firstOnlySelectedChild R ξ ∪ (R.belowPotential φ M) ξ := by
      simpa [reserveSelectionBelowPotential] using hsecondS
    have hbelow : secondSelectedSlot R ξ ∈ (R.belowPotential φ M) ξ := by
      rcases Finset.mem_union.mp hunion with hfirst | hbounded
      · have hfirst' :=
          (Step.FiniteSelection.mem_filter R
            (fun ξ i => i = firstSelectedSlot R ξ) ξ
            (secondSelectedSlot R ξ)).mp (by
              simpa [firstOnlySelectedChild] using hfirst)
        exact (hsecond.2 hfirst'.2.symm).elim
      · exact hbounded
    have hbelow' :=
      (Step.FiniteSelection.mem_filter R
        (fun ξ i => ξ.potentialValue' φ i ≤ M) ξ
        (secondSelectedSlot R ξ)).mp (by
          simpa [Step.FiniteSelection.belowPotential] using hbelow)
    exact ⟨by omega, hbelow'.2⟩
  · rintro ⟨hcard, hbound⟩
    exact reserveSelectionBelowPotential_card_ge_two_of_boundedSecond
      R φ M ξ hcard hbound

theorem potentialValue'_firstSelectedSlot_le_second_of_ordered
    [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (φ : Potential X) (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hordered : ξ.IsOrderedBy φ) (hcard : 2 ≤ (R ξ).card) :
    ξ.potentialValue' φ (firstSelectedSlot R ξ) ≤
      ξ.potentialValue' φ (secondSelectedSlot R ξ) := by
  have hsecond := secondSelectedSlot_mem_of_card R ξ hcard
  have hsurvive : survive (ξ.map φ) (secondSelectedSlot R ξ) :=
    (survive_map_iff φ ξ _).2 (R.mem_support ξ hsecond.1)
  have hmono := orderedSteps_value_mono (ξ.map φ) hordered
    (firstSelectedSlot_lt_second_of_card R ξ hcard).le hsurvive
  simpa [Step.potentialValue', Step.potentialAt?, Step.map, value'] using hmono

theorem reserveSelectionBelowPotential_edgePotentials_le_of_ordered
    [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : R.IsBoundedBy 2)
    (φ : Potential X) (M : ℝ) (ξ : Step α X)
    (hordered : ξ.IsOrderedBy φ)
    (hsplit : 2 ≤ (reserveSelectionBelowPotential R φ M ξ).card) :
    ξ.potentialValue' φ
        (firstSelectedSlot (reserveSelectionBelowPotential R φ M) ξ) ≤ M ∧
      ξ.potentialValue' φ
        (secondSelectedSlot (reserveSelectionBelowPotential R φ M) ξ) ≤ M := by
  have hbounded :=
    (reserveSelectionBelowPotential_card_ge_two_iff_boundedSecond
      R hR φ M ξ).mp hsplit
  have hRcard : (R ξ).card = 2 := by
    have hSleR := Finset.card_le_card
      (reserveSelectionBelowPotential_subset R φ M ξ)
    have hRcap : (R ξ).card ≤ 2 := hR ξ
    omega
  have hSeq : reserveSelectionBelowPotential R φ M ξ = R ξ := by
    apply Finset.eq_of_subset_of_card_le
      (reserveSelectionBelowPotential_subset R φ M ξ)
    rw [hRcard]
    exact hsplit
  have hfirstEq :
      firstSelectedSlot (reserveSelectionBelowPotential R φ M) ξ =
        firstSelectedSlot R ξ := by
    simp [firstSelectedSlot, hSeq]
  have hsecondEq :
      secondSelectedSlot (reserveSelectionBelowPotential R φ M) ξ =
        secondSelectedSlot R ξ := by
    simp [secondSelectedSlot, hSeq, hfirstEq]
  have hfirst_le := potentialValue'_firstSelectedSlot_le_second_of_ordered
    φ R ξ hordered hbounded.1
  constructor
  · rw [hfirstEq]
    exact hfirst_le.trans hbounded.2
  · rw [hsecondEq]
    exact hbounded.2

/-- First-`N` selection ordered by a real-valued potential of the child
mark.  Raw slots serve only as a deterministic tie breaker. -/
noncomputable def firstNByPotential
    [MeasurableSpace X] [LinearOrder α]
    (N : ℕ) (φ : Potential X)
    (hadmits : ∀ ξ : Step α X, AdmitsFirstNBy N
      (fun i => ξ.potentialValue' φ i) (support ξ)) :
    Step.FiniteSelection α X :=
  firstNBy N (fun ξ i => ξ.potentialValue' φ i) hadmits

/-- Finite lower potential levels guarantee existence of the intrinsic
first-`N` child selection.  This also rules out an unattained left edge such
as displacements `1 / n`. -/
theorem admitsFirstNByPotential_of_level_finite
    [MeasurableSpace X] [LinearOrder α]
    (N : ℕ) (φ : Potential X) (ξ : Step α X)
    (hlevel : ∀ a : ℝ,
      {i | survive ξ i ∧ ξ.potentialValue' φ i ≤ a}.Finite) :
    AdmitsFirstNBy N (fun i => ξ.potentialValue' φ i) (support ξ) := by
  exact admitsFirstNBy_of_lowerFinite N _
    (isLowerFiniteBy_of_level_finite
      (fun i => ξ.potentialValue' φ i) (candidates := support ξ) hlevel)

/-- Finite total negative exponential weight makes each lower displacement
level finite, hence supplies the first-`N` selection for real marks. -/
theorem admitsFirstNByPotential_of_totalChildWeight_ne_top
    [LinearOrder α] (N : ℕ) (ξ : Step α ℝ)
    (hsum : totalChildWeight ξ ≠ ⊤) :
    AdmitsFirstNBy N (fun i => ξ.potentialValue' realPotential i) (support ξ) := by
  apply admitsFirstNByPotential_of_level_finite N realPotential ξ
  intro a
  simpa [Step.potentialValue', Step.potentialAt?, realPotential, value'] using
    finite_realized_children_below ξ hsum a

/-- Preserve the first child whenever it exists, and keep the remaining
members of the first `N` segment only below a potential threshold.  The
branching step itself need not be ordered and may be empty. -/
noncomputable def preserveFirstBelowPotential
    [MeasurableSpace X] [LinearOrder α]
    (N : ℕ) (φ : Potential X) (a : ℝ)
    (hlevel : ∀ ξ : Step α X, ∀ b : ℝ,
      {i | survive ξ i ∧ ξ.potentialValue' φ i ≤ b}.Finite) :
    Step.FiniteSelection α X := by
  let admits : ∀ k ξ, AdmitsFirstNBy k
      (fun i => ξ.potentialValue' φ i) (support ξ) :=
    fun k ξ => admitsFirstNByPotential_of_level_finite k φ ξ (hlevel ξ)
  let first := firstNByPotential 1 φ (admits 1)
  let initial := firstNByPotential N φ (admits N)
  exact {
    select := fun ξ => first ξ ∪ (initial.belowPotential φ a) ξ
    subset_support := fun ξ i hi => by
      rcases Finset.mem_union.mp hi with hi | hi
      · exact first.subset_support ξ i hi
      · exact (initial.belowPotential φ a).subset_support ξ i hi }

theorem mem_preserveFirstBelowPotential_iff
    [MeasurableSpace X] [LinearOrder α]
    (N : ℕ) (φ : Potential X) (a : ℝ)
    (hlevel : ∀ ξ : Step α X, ∀ b : ℝ,
      {i | survive ξ i ∧ ξ.potentialValue' φ i ≤ b}.Finite)
    (ξ : Step α X) (i : α) :
    i ∈ preserveFirstBelowPotential N φ a hlevel ξ ↔
      i ∈ firstNByPotential 1 φ
          (fun ξ => admitsFirstNByPotential_of_level_finite
            1 φ ξ (hlevel ξ)) ξ ∨
        (i ∈ firstNByPotential N φ
            (fun ξ => admitsFirstNByPotential_of_level_finite
              N φ ξ (hlevel ξ)) ξ ∧
          ξ.potentialValue' φ i ≤ a) := by
  simp [preserveFirstBelowPotential, belowPotential, mem_filter]

theorem preserveFirstBelowPotential_isBoundedBy
    [MeasurableSpace X] [LinearOrder α]
    (N : ℕ) (hN : 1 ≤ N) (φ : Potential X) (a : ℝ)
    (hlevel : ∀ ξ : Step α X, ∀ b : ℝ,
      {i | survive ξ i ∧ ξ.potentialValue' φ i ≤ b}.Finite) :
    (preserveFirstBelowPotential N φ a hlevel).IsBoundedBy N := by
  intro ξ
  let admits : ∀ k ξ, AdmitsFirstNBy k
      (fun i => ξ.potentialValue' φ i) (support ξ) :=
    fun k ξ => admitsFirstNByPotential_of_level_finite k φ ξ (hlevel ξ)
  let first := firstNByPotential 1 φ (admits 1)
  let initial := firstNByPotential N φ (admits N)
  have hfirst : first ξ ⊆ initial ξ :=
    firstNBy_subset_of_le hN
      (fun ξ i => ξ.potentialValue' φ i) (admits 1) (admits N) ξ
  have hunion : first ξ ∪ (initial.belowPotential φ a) ξ ⊆ initial ξ := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hfirst hi
    · have hi' : i ∈ initial.filter
          (fun ξ i => ξ.potentialValue' φ i ≤ a) ξ := by
        simpa only [belowPotential] using hi
      exact (mem_filter initial
        (fun ξ i => ξ.potentialValue' φ i ≤ a) ξ i).mp hi' |>.1
  apply (Finset.card_le_card hunion).trans
  exact (firstNBy_spec N
    (fun ξ i => ξ.potentialValue' φ i) (admits N) ξ).card_le

end Step.FiniteSelection

end Combinatorics.Branching

end
