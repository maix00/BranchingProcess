/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Conditional probability bounds along a filtration

The public declarations in this file are:

- `ProbabilityTheory.measureReal_inter_ge_of_condExp_indicator_ge` and
  `ProbabilityTheory.measureReal_inter_le_of_condExp_indicator_le`: integrate
  lower and upper conditional-probability bounds over a measurable past event.
- `ProbabilityTheory.conditionalBlockIntersection` and
  `ProbabilityTheory.mem_conditionalBlockIntersection_iff`: define the event
  that the first `n` successive block events all hold.
- `ProbabilityTheory.measureReal_conditionalBlockIntersection_ge_prod` and
  `ProbabilityTheory.measureReal_conditionalBlockIntersection_le_prod`:
  iterate lower and upper conditional bounds to obtain a product estimate.
- `ProbabilityTheory.measureReal_conditionalBlockIntersection_le_pow`:
  the uniform upper-bound specialization.
- `ProbabilityTheory.measureReal_initialInterConditionalBlockIntersection_ge_mul_prod`
  and
  `ProbabilityTheory.measureReal_initialInterConditionalBlockIntersection_ge_mul_prod_prefix`:
  the lower product estimate with an initial event measurable before the first block.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

/-- Integrating a conditional probability lower bound over a measurable
past event gives the one-step reverse Markov product bound. -/
theorem measureReal_inter_ge_of_condExp_indicator_ge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {A E : Set Ω} (hA : MeasurableSet[m] A)
    (hE : MeasurableSet[mΩ] E)
    {p : ℝ}
    (hcond : ∀ᵐ ω ∂P, ω ∈ A →
      p ≤ condExp m P (E.indicator fun _ => (1 : ℝ)) ω) :
    p * P.real A ≤ P.real (A ∩ E) := by
  let f : Ω → ℝ := E.indicator fun _ => (1 : ℝ)
  have hf : Integrable f P :=
    (integrable_const (c := (1 : ℝ))).indicator hE
  have hAE : MeasurableSet[mΩ] (A ∩ E) := (hm A hA).inter hE
  have hindicator : (A ∩ E).indicator (fun _ => (1 : ℝ)) = A.indicator f := by
    funext ω
    by_cases hωA : ω ∈ A <;> by_cases hωE : ω ∈ E <;>
      simp [f, hωA, hωE]
  calc
    p * P.real A = ∫ ω in A, p ∂P := by
      rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ ∫ ω in A, condExp m P f ω ∂P := by
      apply setIntegral_mono_on_ae
      · exact (integrable_const p).integrableOn
      · exact integrable_condExp.integrableOn
      · exact hm A hA
      · exact hcond
    _ = ∫ ω in A, f ω ∂P :=
      setIntegral_condExp hm hf hA
    _ = ∫ ω, (A ∩ E).indicator (fun _ => (1 : ℝ)) ω ∂P := by
      rw [hindicator, integral_indicator (hm A hA)]
    _ = P.real (A ∩ E) :=
      integral_indicator_one hAE

/-- Integrating a conditional probability upper bound over a measurable
past event gives the one-step Markov product bound. -/
theorem measureReal_inter_le_of_condExp_indicator_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {A E : Set Ω} (hA : MeasurableSet[m] A)
    (hE : MeasurableSet[mΩ] E)
    {p : ℝ}
    (hcond : ∀ᵐ ω ∂P, ω ∈ A →
      condExp m P (E.indicator fun _ => (1 : ℝ)) ω ≤ p) :
    P.real (A ∩ E) ≤ p * P.real A := by
  let f : Ω → ℝ := E.indicator fun _ => (1 : ℝ)
  have hf : Integrable f P :=
    (integrable_const (c := (1 : ℝ))).indicator hE
  have hAE : MeasurableSet[mΩ] (A ∩ E) := (hm A hA).inter hE
  have hindicator : (A ∩ E).indicator (fun _ => (1 : ℝ)) = A.indicator f := by
    funext ω
    by_cases hωA : ω ∈ A <;> by_cases hωE : ω ∈ E <;>
      simp [f, hωA, hωE]
  calc
    P.real (A ∩ E) = ∫ ω, (A ∩ E).indicator (fun _ => (1 : ℝ)) ω ∂P :=
      (integral_indicator_one hAE).symm
    _ = ∫ ω in A, f ω ∂P := by
      rw [hindicator, integral_indicator (hm A hA)]
    _ = ∫ ω in A, condExp m P f ω ∂P :=
      (setIntegral_condExp hm hf hA).symm
    _ ≤ ∫ ω in A, p ∂P := by
      apply setIntegral_mono_on_ae
      · exact integrable_condExp.integrableOn
      · exact (integrable_const p).integrableOn
      · exact hm A hA
      · exact hcond
    _ = p * P.real A := by
      rw [setIntegral_const, smul_eq_mul, mul_comm]

/-- The intersection of the first `n` successive block events. -/
def conditionalBlockIntersection
    {Ω : Type*} [MeasurableSpace Ω]
    (events : ℕ → Set Ω) : ℕ → Set Ω
  | 0 => Set.univ
  | n + 1 => conditionalBlockIntersection events n ∩ events n

/-- Membership in the first `n` block events is equivalent to membership
in each indexed event before `n`. -/
theorem mem_conditionalBlockIntersection_iff
    {Ω : Type*} [MeasurableSpace Ω]
    (events : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    ω ∈ conditionalBlockIntersection events n ↔
      ∀ j, j < n → ω ∈ events j := by
  induction n with
  | zero => simp [conditionalBlockIntersection]
  | succ n ih =>
      rw [conditionalBlockIntersection, Set.mem_inter_iff, ih]
      constructor
      · rintro ⟨hprev, hlast⟩ j hj
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with h | rfl
        · exact hprev j h
        · exact hlast
      · intro hall
        exact ⟨fun j hj => hall j (Nat.lt_succ_of_lt hj),
          hall n (Nat.lt_succ_self n)⟩

/-- Iterating the reverse Markov inequality gives the product of the
conditional lower bounds for successive blocks. -/
theorem measureReal_conditionalBlockIntersection_ge_prod
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (filtration : ℕ → MeasurableSpace Ω)
    (hfiltrationMono : ∀ n, filtration n ≤ filtration (n + 1))
    (hfiltrationAmbient : ∀ n, filtration n ≤ mΩ)
    (events : ℕ → Set Ω)
    (heventMeasurable : ∀ n,
      MeasurableSet[filtration (n + 1)] (events n))
    (bounds : ℕ → ℝ) (hboundNonneg : ∀ n, 0 ≤ bounds n)
    (hconditional : ∀ n, ∀ᵐ ω ∂P,
      ω ∈ conditionalBlockIntersection events n →
        bounds n ≤ condExp (filtration n) P
          ((events n).indicator fun _ => (1 : ℝ)) ω)
    (n : ℕ) :
    (∏ j ∈ Finset.range n, bounds j) ≤
      P.real (conditionalBlockIntersection events n) := by
  have hmeas : ∀ k,
      MeasurableSet[filtration k]
        (conditionalBlockIntersection events k) := by
    intro k
    induction k with
    | zero => simp [conditionalBlockIntersection]
    | succ k ih =>
        rw [conditionalBlockIntersection]
        exact (hfiltrationMono k _ ih).inter (heventMeasurable k)
  induction n with
  | zero => simp [conditionalBlockIntersection, Measure.real]
  | succ k ih =>
      rw [conditionalBlockIntersection]
      calc
        (∏ j ∈ Finset.range (k + 1), bounds j) =
            bounds k * (∏ j ∈ Finset.range k, bounds j) := by
          rw [Finset.prod_range_succ]
          ring
        _ ≤ bounds k * P.real (conditionalBlockIntersection events k) :=
          mul_le_mul_of_nonneg_left ih (hboundNonneg k)
        _ ≤ P.real
            (conditionalBlockIntersection events k ∩ events k) :=
          measureReal_inter_ge_of_condExp_indicator_ge
            (filtration k) (hfiltrationAmbient k) (hmeas k)
            (hfiltrationAmbient (k + 1) (events k)
              (heventMeasurable k)) (hconditional k)

/-- Iterating conditional upper bounds on the preceding block intersection
gives the product upper bound for a finite sequence of events. -/
theorem measureReal_conditionalBlockIntersection_le_prod
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (filtration : ℕ → MeasurableSpace Ω)
    (hfiltrationMono : ∀ n, filtration n ≤ filtration (n + 1))
    (hfiltrationAmbient : ∀ n, filtration n ≤ mΩ)
    (events : ℕ → Set Ω)
    (heventMeasurable : ∀ n,
      MeasurableSet[filtration (n + 1)] (events n))
    (bounds : ℕ → ℝ) (hboundNonneg : ∀ n, 0 ≤ bounds n)
    (hconditional : ∀ n, ∀ᵐ ω ∂P,
      ω ∈ conditionalBlockIntersection events n →
        condExp (filtration n) P
          ((events n).indicator fun _ => (1 : ℝ)) ω ≤ bounds n)
    (n : ℕ) :
    P.real (conditionalBlockIntersection events n) ≤
      ∏ j ∈ Finset.range n, bounds j := by
  have hmeas : ∀ k,
      MeasurableSet[filtration k]
        (conditionalBlockIntersection events k) := by
    intro k
    induction k with
    | zero => simp [conditionalBlockIntersection]
    | succ k ih =>
        rw [conditionalBlockIntersection]
        exact (hfiltrationMono k _ ih).inter (heventMeasurable k)
  induction n with
  | zero => simp [conditionalBlockIntersection]
  | succ k ih =>
      rw [conditionalBlockIntersection]
      calc
        P.real (conditionalBlockIntersection events k ∩ events k) ≤
            bounds k * P.real (conditionalBlockIntersection events k) :=
          measureReal_inter_le_of_condExp_indicator_le
            (filtration k) (hfiltrationAmbient k) (hmeas k)
            (hfiltrationAmbient (k + 1) (events k)
              (heventMeasurable k)) (hconditional k)
        _ ≤ bounds k * (∏ j ∈ Finset.range k, bounds j) :=
          mul_le_mul_of_nonneg_left ih (hboundNonneg k)
        _ = ∏ j ∈ Finset.range (k + 1), bounds j := by
          rw [Finset.prod_range_succ]
          ring

/-- If the conditional probability of each next event is at most `p` on
the preceding block intersection, then the probability that all first `n`
events hold is at most `p ^ n`. -/
theorem measureReal_conditionalBlockIntersection_le_pow
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (filtration : ℕ → MeasurableSpace Ω)
    (hfiltrationMono : ∀ n, filtration n ≤ filtration (n + 1))
    (hfiltrationAmbient : ∀ n, filtration n ≤ mΩ)
    (events : ℕ → Set Ω)
    (heventMeasurable : ∀ n,
      MeasurableSet[filtration (n + 1)] (events n))
    {p : ℝ} (hp : 0 ≤ p)
    (hconditional : ∀ n, ∀ᵐ ω ∂P,
      ω ∈ conditionalBlockIntersection events n →
        condExp (filtration n) P
          ((events n).indicator fun _ => (1 : ℝ)) ω ≤ p)
    (n : ℕ) :
    P.real (conditionalBlockIntersection events n) ≤ p ^ n := by
  have hprod := measureReal_conditionalBlockIntersection_le_prod
    filtration hfiltrationMono hfiltrationAmbient events heventMeasurable
    (fun _ => p) (fun _ => hp) hconditional n
  simpa [Finset.prod_const, Finset.card_range] using hprod

/-- The reverse Markov product with an initial event observable before the
first block. -/
theorem measureReal_initialInterConditionalBlockIntersection_ge_mul_prod
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (filtration : ℕ → MeasurableSpace Ω)
    (hfiltrationMono : ∀ n, filtration n ≤ filtration (n + 1))
    (hfiltrationAmbient : ∀ n, filtration n ≤ mΩ)
    (initial : Set Ω) (hinitial : MeasurableSet[filtration 0] initial)
    (events : ℕ → Set Ω)
    (heventMeasurable : ∀ n,
      MeasurableSet[filtration (n + 1)] (events n))
    (bounds : ℕ → ℝ) (hboundNonneg : ∀ n, 0 ≤ bounds n)
    (hconditional : ∀ n, ∀ᵐ ω ∂P,
      ω ∈ initial ∩ conditionalBlockIntersection events n →
        bounds n ≤ condExp (filtration n) P
          ((events n).indicator fun _ => (1 : ℝ)) ω)
    (n : ℕ) :
    P.real initial * (∏ j ∈ Finset.range n, bounds j) ≤
      P.real (initial ∩ conditionalBlockIntersection events n) := by
  have hmeas : ∀ k,
      MeasurableSet[filtration k]
        (initial ∩ conditionalBlockIntersection events k) := by
    intro k
    induction k with
    | zero => simpa [conditionalBlockIntersection] using hinitial
    | succ k ih =>
        rw [conditionalBlockIntersection, ← Set.inter_assoc]
        exact (hfiltrationMono k _ ih).inter (heventMeasurable k)
  induction n with
  | zero => simp [conditionalBlockIntersection]
  | succ k ih =>
      calc
        P.real initial * (∏ j ∈ Finset.range (k + 1), bounds j) =
            bounds k * (P.real initial *
              (∏ j ∈ Finset.range k, bounds j)) := by
          rw [Finset.prod_range_succ]
          ring
        _ ≤ bounds k *
            P.real (initial ∩ conditionalBlockIntersection events k) :=
          mul_le_mul_of_nonneg_left ih (hboundNonneg k)
        _ ≤ P.real
            ((initial ∩ conditionalBlockIntersection events k) ∩ events k) :=
          measureReal_inter_ge_of_condExp_indicator_ge
            (filtration k) (hfiltrationAmbient k) (hmeas k)
            (hfiltrationAmbient (k + 1) (events k)
              (heventMeasurable k)) (hconditional k)
        _ = P.real
            (initial ∩ conditionalBlockIntersection events (k + 1)) := by
          rw [conditionalBlockIntersection, Set.inter_assoc]

/-- The reverse Markov product through a fixed finite number of blocks,
using conditional and measurability assumptions only for those blocks. -/
theorem measureReal_initialInterConditionalBlockIntersection_ge_mul_prod_prefix
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (filtration : ℕ → MeasurableSpace Ω)
    (hfiltrationMono : ∀ n, filtration n ≤ filtration (n + 1))
    (hfiltrationAmbient : ∀ n, filtration n ≤ mΩ)
    (initial : Set Ω) (hinitial : MeasurableSet[filtration 0] initial)
    (events : ℕ → Set Ω)
    (bounds : ℕ → ℝ) (hboundNonneg : ∀ n, 0 ≤ bounds n)
    (n : ℕ)
    (heventMeasurable : ∀ j, j < n →
      MeasurableSet[filtration (j + 1)] (events j))
    (hconditional : ∀ j, j < n → ∀ᵐ ω ∂P,
      ω ∈ initial ∩ conditionalBlockIntersection events j →
        bounds j ≤ condExp (filtration j) P
          ((events j).indicator fun _ => (1 : ℝ)) ω) :
    P.real initial * (∏ j ∈ Finset.range n, bounds j) ≤
      P.real (initial ∩ conditionalBlockIntersection events n) := by
  have hmeas : ∀ k, k ≤ n →
      MeasurableSet[filtration k]
        (initial ∩ conditionalBlockIntersection events k) := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa [conditionalBlockIntersection] using hinitial
    | succ k ih =>
        intro hk
        have hk' : k < n := by omega
        rw [conditionalBlockIntersection, ← Set.inter_assoc]
        exact (hfiltrationMono k _ (ih (by omega))).inter
          (heventMeasurable k hk')
  have hprod : ∀ k, k ≤ n →
      P.real initial * (∏ j ∈ Finset.range k, bounds j) ≤
        P.real (initial ∩ conditionalBlockIntersection events k) := by
    intro k
    induction k with
    | zero =>
        intro _
        simp [conditionalBlockIntersection]
    | succ k ih =>
        intro hk
        have hk' : k < n := by omega
        calc
          P.real initial *
              (∏ j ∈ Finset.range (k + 1), bounds j) =
              bounds k * (P.real initial *
                (∏ j ∈ Finset.range k, bounds j)) := by
            rw [Finset.prod_range_succ]
            ring
          _ ≤ bounds k *
              P.real (initial ∩ conditionalBlockIntersection events k) :=
            mul_le_mul_of_nonneg_left (ih (by omega)) (hboundNonneg k)
          _ ≤ P.real
              ((initial ∩ conditionalBlockIntersection events k) ∩ events k) :=
            measureReal_inter_ge_of_condExp_indicator_ge
              (filtration k) (hfiltrationAmbient k) (hmeas k (by omega))
              (hfiltrationAmbient (k + 1) (events k)
                (heventMeasurable k hk')) (hconditional k hk')
          _ = P.real
              (initial ∩ conditionalBlockIntersection events (k + 1)) := by
            rw [conditionalBlockIntersection, Set.inter_assoc]
  exact hprod n le_rfl

end ProbabilityTheory

end
