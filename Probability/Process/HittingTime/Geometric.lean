/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.HittingTime.Declarations
public import Mathlib.Probability.Independence.Basic

/-!
# First-success laws for independent events

## Public declarations

- `firstDeclaredSuccess_eq_top_event` identifies no success at any index:
  $\{\omega:\tau(\omega)=\top\}=\bigcap_{n\geq0}A_n^c$.
- `measurableSet_firstDeclaredSuccess_eq` and
  `measurableSet_firstDeclaredSuccess_eq_top` give measurability of finite
  first-success fibers and the no-success event.
- `measure_firstDeclaredSuccess_eq` proves the geometric law for independent
  events of common probability $p$:
  $\mathbb P(\tau=k)=p(1-p)^k$ for zero-based indexing.

This is the general event-sequence result used by the fixed-age branching
trial specialization. The independent-event products use Mathlib's
`iIndepSet` API.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

private theorem iIndepSet_measure_biInter_choose
    {ι : Type*} {events : ι → Set Ω}
    (h_indep : iIndepSet events μ) (S : Finset ι)
    (choose : ι → Bool) :
    μ (⋂ i ∈ S, if choose i then events i else (events i)ᶜ) =
      ∏ i ∈ S, μ (if choose i then events i else (events i)ᶜ) := by
  apply (iIndepSet_iff events μ).mp h_indep S
  intro i _
  by_cases hi : choose i
  · simp only [hi, ↓reduceIte]
    exact MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)
  · have hi' : choose i = false := Bool.eq_false_of_not_eq_true hi
    simp only [hi', Bool.false_eq]
    exact (MeasurableSpace.measurableSet_generateFrom
      (Set.mem_singleton _)).compl

omit [MeasurableSpace Ω] in
/-- The event that the first declaration occurs at `k` is a success at `k`
intersected with all earlier failures. -/
private theorem firstDeclaredSuccess_eq_event
    (events : ℕ → Set Ω) (k : ℕ) :
    {ω | firstDeclaredSuccess events ω = k} =
      events k ∩ ⋂ i ∈ Finset.range k, (events i)ᶜ := by
  ext ω
  simp only [Set.mem_ofPred_eq, firstDeclaredSuccess_eq_iff,
    Set.mem_inter_iff, Set.mem_iInter, Finset.mem_range, Set.mem_compl_iff]

/-- A finite first-declaration fiber is measurable whenever each declaration
event is measurable.  Only a finite intersection is used. -/
theorem measurableSet_firstDeclaredSuccess_eq
    {events : ℕ → Set Ω} (h_meas : ∀ i, MeasurableSet (events i)) (k : ℕ) :
    MeasurableSet {ω | firstDeclaredSuccess events ω = k} := by
  rw [firstDeclaredSuccess_eq_event]
  exact (h_meas k).inter <|
    MeasurableSet.biInter (Finset.countable_toSet (Finset.range k)) fun i _ =>
      (h_meas i).compl

omit [MeasurableSpace Ω] in
/-- No declaration occurs exactly when every declaration event fails. -/
theorem firstDeclaredSuccess_eq_top_event (events : ℕ → Set Ω) :
    {ω | firstDeclaredSuccess events ω = ⊤} = (⋃ i, events i)ᶜ := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion]
  constructor
  · intro htop ⟨i, hi⟩
    have hle : firstDeclaredSuccess events ω ≤ i :=
      (firstDeclaredSuccess_le_iff events ω i).2 ⟨i, le_rfl, hi⟩
    rw [htop] at hle
    exact WithTop.not_top_le_coe i hle
  · intro hnone
    by_contra hne
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hne
    have hsuccess := (firstDeclaredSuccess_eq_iff events ω k).1 hk.symm |>.1
    exact hnone ⟨k, hsuccess⟩

/-- The infinite first-declaration fiber is measurable.  This is the one
place where the countable trial clock enters: it is the complement of a
countable union of declaration events. -/
theorem measurableSet_firstDeclaredSuccess_eq_top
    {events : ℕ → Set Ω} (h_meas : ∀ i, MeasurableSet (events i)) :
    MeasurableSet {ω | firstDeclaredSuccess events ω = ⊤} := by
  rw [firstDeclaredSuccess_eq_top_event]
  exact (MeasurableSet.iUnion h_meas).compl

/-- Independent events with common probability `p` have the geometric
first-success law, with indices starting at zero. -/
theorem measure_firstDeclaredSuccess_eq
    {events : ℕ → Set Ω} [IsProbabilityMeasure μ]
    (h_meas : ∀ i, MeasurableSet (events i))
    (h_indep : iIndepSet events μ) (p : ENNReal)
    (h_prob : ∀ i, μ (events i) = p) (k : ℕ) :
    μ {ω | firstDeclaredSuccess events ω = k} =
      p * (1 - p) ^ k := by
  let chosen : ℕ → Bool := fun i => decide (i = k)
  have hblock := iIndepSet_measure_biInter_choose h_indep
    (Finset.range (k + 1)) chosen
  have hset :
      (⋂ i ∈ Finset.range (k + 1),
        if chosen i then events i else (events i)ᶜ) =
        events k ∩ ⋂ i ∈ Finset.range k, (events i)ᶜ := by
    ext ω
    simp only [Set.mem_iInter, Finset.mem_range, Set.mem_inter_iff,
      Set.mem_compl_iff, chosen]
    constructor
    · intro h
      have hk := h k (Nat.lt_succ_self k)
      refine ⟨by simpa using hk, ?_⟩
      intro i hik
      have hi := h i (hik.trans_le (Nat.le_succ k))
      simpa [Nat.ne_of_lt hik] using hi
    · rintro ⟨hk, hearlier⟩ i hik
      by_cases hi : i = k
      · simpa [hi] using hk
      · have hlt : i < k := by omega
        simpa [hi] using hearlier i hlt
  rw [firstDeclaredSuccess_eq_event, ← hset, hblock,
    Finset.prod_range_succ]
  have hprior :
      (∏ i ∈ Finset.range k,
        μ (if chosen i then events i else (events i)ᶜ)) =
        (1 - p) ^ k := by
    calc
      (∏ i ∈ Finset.range k,
          μ (if chosen i then events i else (events i)ᶜ)) =
          ∏ _i ∈ Finset.range k, (1 - p) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hik : i < k := Finset.mem_range.mp hi
        have hine : i ≠ k := Nat.ne_of_lt hik
        have hchosen : chosen i = false := by simp [chosen, hine]
        rw [show (if chosen i then events i else (events i)ᶜ) =
          (events i)ᶜ by simp [hchosen]]
        rw [measure_compl (h_meas i) (by finiteness), measure_univ, h_prob i]
      _ = (1 - p) ^ k := by simp
  rw [hprior]
  simp [chosen, h_prob, mul_comm]

end ProbabilityTheory
