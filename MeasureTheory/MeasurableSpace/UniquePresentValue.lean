/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.MeasurableSpace.Option

/-!
# Reading the unique present value of a countable family

## Public declarations

* `Function.uniquePresentValue d f` reads the value of the unique present coordinate
  of `f : I → Option S`, returning `d` when there is no unique coordinate.
* `Function.uniquePresentValue_eq` states that `uniquePresentValue d f = s` whenever
  `f i = some s` and all other coordinates are absent.
* `measurableSet_unique_present` states that having exactly one present
  coordinate is a measurable event for countable `I`.
* `measurable_uniquePresentValue` proves measurability of the readout for countable
  `I` and arbitrary measurable `S`; no equality test on `S` is required.

This is a coordinate observation, with no branching or probability assumptions.
-/

@[expose] public section

open MeasureTheory

/-- Read the unique present coordinate, using the supplied default otherwise. -/
noncomputable def Function.uniquePresentValue {I S : Type*} (d : S) (f : I → Option S) : S := by
  classical
  exact if h : ∃! i, f i ≠ none then (f (Classical.choose h)).getD d else d

/-- A single present coordinate determines the observation. -/
theorem Function.uniquePresentValue_eq {I S : Type*} (d : S) (f : I → Option S)
    (i : I) (s : S) (hi : f i = some s) (ho : ∀ j, j ≠ i → f j = none) :
    Function.uniquePresentValue d f = s := by
  classical
  have hu : ∃! j, f j ≠ none := by
    refine ⟨i, by simp [hi], ?_⟩
    intro j hj
    by_contra hji
    simp [ho j hji] at hj
  rw [Function.uniquePresentValue, dite_eq_left hu]
  have he : Classical.choose hu = i := hu.unique (Classical.choose_spec hu).1 (by simp [hi])
  rw [he, hi]
  rfl

/-- Uniqueness of the present coordinate is a countable measurable condition. -/
theorem measurableSet_unique_present {I S : Type*} [Countable I] [MeasurableSpace S] :
    MeasurableSet {f : I → Option S | ∃! i, f i ≠ none} := by
  classical
  have hp (i : I) : MeasurableSet {f : I → Option S | f i ≠ none} :=
    (measurableSet_option_none.preimage (measurable_pi_apply i)).compl
  change MeasurableSet {f : I → Option S | ∃ i,
    f i ≠ none ∧ ∀ j, f j ≠ none → j = i}
  rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  rw [Set.ofPred_and]
  apply (hp i).inter
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  by_cases hji : j = i
  · simp [hji]
  · convert (hp j).compl using 1
    ext f
    simp [hji]

/-- Reading the unique coordinate is measurable without a countability condition on the values. -/
theorem measurable_uniquePresentValue {I S : Type*} [Countable I] [MeasurableSpace S] (d : S) :
    Measurable (Function.uniquePresentValue (I := I) d) := by
  classical
  intro A hA
  have hp (i : I) : MeasurableSet {f : I → Option S | f i ≠ none ∧
      ∀ j, f j ≠ none → j = i} := by
    have hmeas (j : I) : MeasurableSet {f : I → Option S | f j ≠ none} :=
      (measurableSet_option_none.preimage (measurable_pi_apply j)).compl
    rw [Set.ofPred_and]
    apply (hmeas i).inter
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    by_cases hji : j = i
    · simp [hji]
    · convert (hmeas j).compl using 1
      ext f
      simp [hji]
  have he : (Function.uniquePresentValue (I := I) d) ⁻¹' A =
      ({f : I → Option S | ∃! i, f i ≠ none}ᶜ ∩ {f | d ∈ A}) ∪
        ⋃ i : I, {f : I → Option S | f i ≠ none ∧ ∀ j, f j ≠ none → j = i} ∩
          (fun f => (f i).getD d) ⁻¹' A := by
    ext f
    by_cases hu : ∃! i, f i ≠ none
    · obtain ⟨i, hi, huniq⟩ := hu
      have hv : Function.uniquePresentValue d f = (f i).getD d := by
        have hu : ∃! j, f j ≠ none := ⟨i, hi, huniq⟩
        rw [Function.uniquePresentValue, dite_eq_left hu]
        rw [huniq _ (Classical.choose_spec (show ∃! i, f i ≠ none from ⟨i, hi, huniq⟩)).1]
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
        Set.mem_ofPred_eq, Set.mem_iUnion, hv]
      constructor
      · intro h; exact Or.inr ⟨i, ⟨hi, huniq⟩, h⟩
      · rintro (⟨h, _⟩ | ⟨j, hj, h⟩)
        · exact False.elim (h ⟨i, hi, huniq⟩)
        · rwa [huniq j hj.1] at h
    · simp only [Function.uniquePresentValue, dite_eq_right hu, Set.mem_preimage, Set.mem_union,
        Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro hd; exact Or.inl ⟨hu, hd⟩
      · rintro (⟨_, hd⟩ | ⟨i, hi, _⟩)
        · exact hd
        · exact False.elim (hu ⟨i, hi.1, hi.2⟩)
  rw [he]
  apply (measurableSet_unique_present.compl.inter (by by_cases hd : d ∈ A <;> simp [hd])).union
  exact MeasurableSet.iUnion fun i => (hp i).inter
    ((measurable_optionGetD d).comp (measurable_pi_apply i) hA)

end
