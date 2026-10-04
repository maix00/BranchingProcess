/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.HittingTime.Declarations
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Probability.Independence.Basic

/-!
# Joint-transform geometric trial calculation

For a waiting step, `a` contributes `E[exp (λ Ξ₁) 1_{no split}]`, not
`P(no split) * E[exp (λ Ξ₁)]`. The probabilistic identification of each term
with `p * a ^ g` remains a separate independence proof obligation.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/- The event-level interface used when a trial is split into an observable
  success event and an independent continuation event.  Keeping this lemma
  at the event level avoids baking a particular offspring or displacement
  model into the geometric-series calculation below. -/
theorem independent_trial_events_probability
    {success continuation : Set Ω}
    (h_indep : IndepSet success continuation μ) :
    μ (success ∩ continuation) = μ success * μ continuation := by
  exact h_indep.measure_inter_eq_mul

/-- Finite products of independent trial events.  This is the form used for
  a prescribed string of failures followed by a success. -/
theorem independent_trial_preimage_probability
    {ι : Type*} {β : ι → Type*}
    {mβ : ∀ i, MeasurableSpace (β i)}
    {X : ∀ i, Ω → β i} (h_indep : iIndepFun X μ)
    (S : Finset ι) (events : ∀ i, Set (β i))
    (h_meas : ∀ i, i ∈ S → MeasurableSet[mβ i] (events i)) :
    μ (⋂ i ∈ S, X i ⁻¹' events i) =
      ∏ i ∈ S, μ (X i ⁻¹' events i) := by
  exact h_indep.measure_inter_preimage_eq_mul S h_meas

/-- If all events in a finite independent block have the same probability,
  the block probability is the corresponding power. -/
theorem independent_trial_preimage_probability_eq_pow
    {ι : Type*} {β : ι → Type*}
    {mβ : ∀ i, MeasurableSpace (β i)}
    {X : ∀ i, Ω → β i} (h_indep : iIndepFun X μ)
    (S : Finset ι) (events : ∀ i, Set (β i)) (a : ENNReal)
    (h_meas : ∀ i, i ∈ S → MeasurableSet[mβ i] (events i))
    (h_prob : ∀ i, i ∈ S → μ (X i ⁻¹' events i) = a) :
    μ (⋂ i ∈ S, X i ⁻¹' events i) = a ^ S.card := by
  rw [independent_trial_preimage_probability h_indep S events h_meas]
  rw [Finset.prod_eq_pow_card]
  intro i hi
  exact h_prob i hi

/-- In a finite independent family of events, one may independently choose
either each event or its complement. -/
theorem iIndepSet_measure_biInter_choose
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
theorem firstDeclaredSuccess_eq_event
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

/-- The final algebraic step for a geometric waiting term: an independent
  success event after a block of failures has probability `p * a^g`. -/
theorem independent_success_after_failure_block
    {success failures : Set Ω} (p a : ENNReal) (g : ℕ)
    (h_indep : IndepSet success failures μ)
    (h_success : μ success = p)
    (h_failures : μ failures = a ^ g) :
    μ (success ∩ failures) = p * a ^ g := by
  rw [h_indep.measure_inter_eq_mul, h_success, h_failures]


/-- The geometric-series step of the correct one-trial transform. -/
theorem geometric_trial_transform (p a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a < 1) :
    (∑' g : ℕ, p * a ^ g) = p / (1 - a) := by
  rw [tsum_mul_left, tsum_geometric_of_lt_one ha₀ ha₁]
  simp [div_eq_mul_inv]

/-- The same transform in `ENNReal`, the native codomain of event measures. -/
theorem geometric_trial_transform_ennreal (p a : ENNReal) :
    (∑' g : ℕ, p * a ^ g) = p / (1 - a) := by
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  simp [div_eq_mul_inv]

end ProbabilityTheory.BranchingRandomWalk
