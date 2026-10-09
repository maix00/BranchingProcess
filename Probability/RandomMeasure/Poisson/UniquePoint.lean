/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.RandomMeasure.Poisson.Basic

/-!
# A unique atom of a Poisson point family

The count of a region is the cardinality of the set of *source slots* in that
region. Working with source slots keeps repeated marks distinct.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- The source slots whose realized marks belong to `A`. -/
def poissonSlots {Ω E : Type} (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E) (A : Set E) (ω : Ω) : Set (ℕ × ℕ) :=
  {p | p.2 < K p.1 ω ∧ X p.1 p.2 ω ∈ A}

theorem poissonRandomMeasure_apply_eq_slots_encard
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {A : Set E} (hA : MeasurableSet A) (ω : Ω) :
    (poissonRandomMeasure K X ω : Measure E) A =
      (poissonSlots K X A ω).encard := by
  classical
  rw [poissonRandomMeasure_apply hA, ← ENNReal.tsum_set_one]
  rw [tsum_subtype (poissonSlots K X A ω) (fun _ => (1 : ENNReal))]
  simp only [poissonSlots, Set.mem_ofPred_eq, Set.indicator_apply]
  rw [ENNReal.tsum_prod']
  congr 1
  funext k
  rw [thinnedCount, Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [sum_eq_tsum_indicator
    (fun n => (if X k n ω ∈ A then (1 : ENNReal) else 0))
    (Finset.range (K k ω))]
  apply tsum_congr
  intro n
  by_cases hn : n < K k ω <;> by_cases hx : X k n ω ∈ A <;> simp [hn, hx]

/-- A region with count one contains exactly one source slot. The mark itself
need not be unique as a value elsewhere in the point family. -/
theorem poissonRandomMeasure_one_iff_unique_slot
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {A : Set E} (hA : MeasurableSet A) (ω : Ω) :
    (poissonRandomMeasure K X ω : Measure E) A = 1 ↔
      ∃! p : ℕ × ℕ, p.2 < K p.1 ω ∧ X p.1 p.2 ω ∈ A := by
  rw [poissonRandomMeasure_apply_eq_slots_encard (m := m) hA]
  rw [← ENat.toENNReal_one, ENat.toENNReal_inj, Set.encard_eq_one]
  constructor
  · rintro ⟨p, hp⟩
    have hp' : p.2 < K p.1 ω ∧ X p.1 p.2 ω ∈ A := by
      have : p ∈ poissonSlots K X A ω := by rw [hp]; simp
      exact this
    refine ⟨p, hp', ?_⟩
    intro q hq
    have : q ∈ poissonSlots K X A ω := hq
    rw [hp] at this
    exact this
  · rintro ⟨p, hp, huniq⟩
    refine ⟨p, Set.eq_singleton_iff_unique_mem.mpr ?_⟩
    exact ⟨hp, fun q hq => huniq q hq⟩

/-- Zero count means that no source slot has a mark in the region. -/
theorem poissonRandomMeasure_zero_iff_no_slot
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {A : Set E} (hA : MeasurableSet A) (ω : Ω) :
    (poissonRandomMeasure K X ω : Measure E) A = 0 ↔
      ∀ p : ℕ × ℕ, p.2 < K p.1 ω → X p.1 p.2 ω ∉ A := by
  rw [poissonRandomMeasure_apply_eq_slots_encard (m := m) hA]
  rw [← ENat.toENNReal_zero, ENat.toENNReal_inj, Set.encard_eq_zero]
  constructor
  · intro h p hp hmark
    have : p ∈ poissonSlots K X A ω := ⟨hp, hmark⟩
    rw [h] at this
    exact this
  · intro h
    ext p
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hp
    exact h p hp.1 hp.2

open Classical in
/-- Once a region contains exactly one source point, the count of any
measurable subregion is determined by whether it contains that point. -/
theorem poissonRandomMeasure_apply_subset_of_unique_slot
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {A C : Set E} (hC : MeasurableSet C) (hsub : C ⊆ A) (ω : Ω)
    {p : ℕ × ℕ}
    (hp : p.2 < K p.1 ω ∧ X p.1 p.2 ω ∈ A)
    (hunique : ∀ q : ℕ × ℕ,
      q.2 < K q.1 ω ∧ X q.1 q.2 ω ∈ A → q = p) :
    (poissonRandomMeasure K X ω : Measure E) C =
      if X p.1 p.2 ω ∈ C then 1 else 0 := by
  classical
  rw [poissonRandomMeasure_apply_eq_slots_encard (m := m) hC]
  by_cases hmark : X p.1 p.2 ω ∈ C
  · have hslots : poissonSlots K X C ω = {p} := by
      ext q
      constructor
      · intro hq
        exact Set.mem_singleton_iff.mpr (hunique q ⟨hq.1, hsub hq.2⟩)
      · intro hq
        have hqp : q = p := Set.mem_singleton_iff.mp hq
        subst q
        exact ⟨hp.1, hmark⟩
    simp [hmark, hslots]
  · have hslots : poissonSlots K X C ω = ∅ := by
      ext q
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hq
      have hqp : q = p := hunique q ⟨hq.1, hsub hq.2⟩
      subst q
      exact hmark hq.2
    simp [hmark, hslots]

/-- One point in `J` and none in `B` make the random measure, restricted to
their union, a single Dirac mass. This is a pathwise result and does not
require a measurable choice of the source slot. -/
theorem poissonRandomMeasure_restrict_union_eq_dirac_of_one_zero
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {J B : Set E} (hJ : MeasurableSet J) (hB : MeasurableSet B)
    (ω : Ω)
    (hOne : (poissonRandomMeasure K X ω : Measure E) J = 1)
    (hZero : (poissonRandomMeasure K X ω : Measure E) B = 0) :
    ∃ p : ℕ × ℕ,
      p.2 < K p.1 ω ∧ X p.1 p.2 ω ∈ J ∧
      (poissonRandomMeasure K X ω : Measure E).restrict (J ∪ B) =
        Measure.dirac (X p.1 p.2 ω) := by
  classical
  obtain ⟨p, hp, huniq⟩ :=
    (poissonRandomMeasure_one_iff_unique_slot (m := m) hJ ω).mp hOne
  have hnone := (poissonRandomMeasure_zero_iff_no_slot (m := m) hB ω).mp hZero
  have huniqUnion : ∀ q : ℕ × ℕ,
      q.2 < K q.1 ω ∧ X q.1 q.2 ω ∈ J ∪ B → q = p := by
    intro q hq
    rcases hq.2 with hj | hb
    · exact huniq q ⟨hq.1, hj⟩
    · exact False.elim (hnone q hq.1 hb)
  refine ⟨p, hp.1, hp.2, ?_⟩
  apply Measure.ext
  intro C hC
  rw [Measure.restrict_apply hC, Measure.dirac_apply' _ hC]
  have hsub : C ∩ (J ∪ B) ⊆ J ∪ B := Set.inter_subset_right
  rw [poissonRandomMeasure_apply_subset_of_unique_slot
    (m := m) (hC.inter (hJ.union hB)) hsub ω
    ⟨hp.1, Or.inl hp.2⟩ huniqUnion]
  simp [Set.indicator_apply, hp.2]

/-- Every nonnegative observable of the unique large point reduces to
evaluation at its mark. -/
theorem poissonRandomMeasure_lintegral_union_of_one_zero
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSingletonClass E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {J B : Set E} (hJ : MeasurableSet J) (hB : MeasurableSet B)
    (ω : Ω)
    (hOne : (poissonRandomMeasure K X ω : Measure E) J = 1)
    (hZero : (poissonRandomMeasure K X ω : Measure E) B = 0)
    (f : E → ENNReal) :
    ∃ p : ℕ × ℕ,
      p.2 < K p.1 ω ∧ X p.1 p.2 ω ∈ J ∧
      (∫⁻ z in J ∪ B, f z ∂(poissonRandomMeasure K X ω)) =
        f (X p.1 p.2 ω) := by
  obtain ⟨p, hpK, hpJ, hmeasure⟩ :=
    poissonRandomMeasure_restrict_union_eq_dirac_of_one_zero
      (m := m) hJ hB ω hOne hZero
  refine ⟨p, hpK, hpJ, ?_⟩
  rw [hmeasure, lintegral_dirac]

/-- The same single-point reduction for a signed or vector-valued Bochner
integral, ready for the time-indexed jump-sum construction. -/
theorem poissonRandomMeasure_integral_union_of_one_zero
    {Ω E F : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSingletonClass E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {J B : Set E} (hJ : MeasurableSet J) (hB : MeasurableSet B)
    (ω : Ω)
    (hOne : (poissonRandomMeasure K X ω : Measure E) J = 1)
    (hZero : (poissonRandomMeasure K X ω : Measure E) B = 0)
    (f : E → F) :
    ∃ p : ℕ × ℕ,
      p.2 < K p.1 ω ∧ X p.1 p.2 ω ∈ J ∧
      (∫ z in J ∪ B, f z ∂(poissonRandomMeasure K X ω)) =
        f (X p.1 p.2 ω) := by
  obtain ⟨p, hpK, hpJ, hmeasure⟩ :=
    poissonRandomMeasure_restrict_union_eq_dirac_of_one_zero
      (m := m) hJ hB ω hOne hZero
  refine ⟨p, hpK, hpJ, ?_⟩
  rw [hmeasure, integral_dirac]

end ProbabilityTheory
