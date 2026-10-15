/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Survival

/-!
# The final one-sided segment of a finite random walk

The public definitions and theorems in this file are:

- `ProbabilityTheory.RandomWalk.SignStableFrom`:
  $S_j\ge0$ for every $k\le j\le n$, or $S_j\le0$ for every such $j$.
- `ProbabilityTheory.RandomWalk.lastSignChangeIndex`:
  $\mu_n=\min\{k\le n:\operatorname{SignStableFrom}(n,k)\}$.
- `ProbabilityTheory.RandomWalk.lastSignChangeIndex_le`:
  $\mu_n\le n$.
- `ProbabilityTheory.RandomWalk.signStableFrom_lastSignChangeIndex`:
  the tail beginning at $\mu_n$ has one weak sign.
- `ProbabilityTheory.RandomWalk.signStableFrom_mono_start`:
  $k\le l$ and one weak sign from $k$ imply one weak sign from $l$.
- `ProbabilityTheory.RandomWalk.measurableSet_signStableFrom`:
  the event that $S_k,\ldots,S_n$ have one weak sign is measurable.
- `ProbabilityTheory.RandomWalk.nonnegativeTail_iff_shiftedSurvival`:
  when $S_k=0$, nonnegativity of $S_k,\ldots,S_n$ is equivalent
  to nonnegative survival of the next $n-k$ increments.
- `ProbabilityTheory.RandomWalk.nonpositiveTail_iff_negShiftedSurvival`:
  when $S_k=0$, nonpositivity of $S_k,\ldots,S_n$ is equivalent
  to nonnegative survival of the reflected next $n-k$ increments.
- `ProbabilityTheory.RandomWalk.signStableFrom_iff_shiftedSurvival`:
  when $S_k=0$, the tail has one weak sign exactly when either
  the shifted increments or their negatives survive nonnegatively.
- `ProbabilityTheory.RandomWalk.not_signStableFrom_before_lastSignChangeIndex`:
  every $k<\mu_n$ has both positive and negative values among
  $S_k,\ldots,S_n$.
- `ProbabilityTheory.RandomWalk.lastSignChangeIndex_eq_iff`:
  for $0<k\le n$, $\mu_n=k$ exactly when the tail from $k$
  has one weak sign and the tail from $k-1$ does not.
- `ProbabilityTheory.RandomWalk.measurable_lastSignChangeIndex`:
  the random time $\mu_n$ is measurable.
- `ProbabilityTheory.RandomWalk.terminalSignStableLength`:
  $\nu_n=n-\mu_n$.

These are the discrete last-sign-change time $\mu_n$ and terminal
length $\nu_n$ used in the final paragraph of Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned to
stay positive*, Ann. Probab. 4(3) (1976), 480--485, page 484.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- The walk has one weak sign from time `start` through time `n`. -/
def SignStableFrom (n start : ℕ) (increment : ℕ → ℝ) : Prop :=
  (∀ j : ℕ, start ≤ j → j ≤ n →
    0 ≤ AdditivePath.displacement j increment) ∨
  (∀ j : ℕ, start ≤ j → j ≤ n →
    AdditivePath.displacement j increment ≤ 0)

/-- At time `n` the one-point tail always has one weak sign. -/
theorem signStableFrom_self (n : ℕ) (increment : ℕ → ℝ) :
    SignStableFrom n n increment := by
  rcases le_total (0 : ℝ) (AdditivePath.displacement n increment) with h | h
  · exact Or.inl (fun j hnj hjn => by simpa [Nat.le_antisymm hnj hjn] using h)
  · exact Or.inr (fun j hnj hjn => by simpa [Nat.le_antisymm hnj hjn] using h)

/-- Bolthausen's earliest time after which the finite walk has a
constant weak sign. -/
noncomputable def lastSignChangeIndex (n : ℕ) (increment : ℕ → ℝ) : ℕ :=
  by
    classical
    exact Nat.find (show ∃ k : ℕ, SignStableFrom n k increment from
      ⟨n, signStableFrom_self n increment⟩)

theorem lastSignChangeIndex_le (n : ℕ) (increment : ℕ → ℝ) :
    lastSignChangeIndex n increment ≤ n := by
  classical
  unfold lastSignChangeIndex
  exact Nat.find_min' (show ∃ k : ℕ, SignStableFrom n k increment from
    ⟨n, signStableFrom_self n increment⟩) (signStableFrom_self n increment)

theorem signStableFrom_lastSignChangeIndex
    (n : ℕ) (increment : ℕ → ℝ) :
    SignStableFrom n (lastSignChangeIndex n increment) increment := by
  classical
  unfold lastSignChangeIndex
  exact Nat.find_spec (show ∃ k : ℕ, SignStableFrom n k increment from
    ⟨n, signStableFrom_self n increment⟩)

/-- Restricting a tail with one weak sign preserves that property. -/
theorem signStableFrom_mono_start (n : ℕ) (increment : ℕ → ℝ)
    {k l : ℕ} (hkl : k ≤ l) (h : SignStableFrom n k increment) :
    SignStableFrom n l increment := by
  rcases h with h | h
  · exact Or.inl (fun j hlj hjn => h j (hkl.trans hlj) hjn)
  · exact Or.inr (fun j hlj hjn => h j (hkl.trans hlj) hjn)

/-- A nonnegative tail starting at zero is the survival event for
the shifted increments. -/
theorem nonnegativeTail_iff_shiftedSurvival
    (n start : ℕ) (increment : ℕ → ℝ) (hstart : start ≤ n)
    (hzero : AdditivePath.displacement start increment = 0) :
    (∀ j : ℕ, start ≤ j → j ≤ n →
      0 ≤ AdditivePath.displacement j increment) ↔
      SurvivesNonnegative (n - start) (fun k => increment (start + k)) := by
  rw [SurvivesNonnegative.shift_iff]
  constructor
  · intro h j
    rw [hzero]
    apply h (start + ((j : ℕ) + 1))
    · omega
    · have := j.isLt
      omega
  · intro h j hjstart hjn
    by_cases hj : j = start
    · simp [hj, hzero]
    · have hindex : j - start - 1 < n - start := by omega
      have hposition := h ⟨j - start - 1, hindex⟩
      have heq : start + ((j - start - 1) + 1) = j := by omega
      rw [heq, hzero] at hposition
      exact hposition

/-- The reflected version of the one-sided tail/survival identity. -/
theorem nonpositiveTail_iff_negShiftedSurvival
    (n start : ℕ) (increment : ℕ → ℝ) (hstart : start ≤ n)
    (hzero : AdditivePath.displacement start increment = 0) :
    (∀ j : ℕ, start ≤ j → j ≤ n →
      AdditivePath.displacement j increment ≤ 0) ↔
      SurvivesNonnegative (n - start)
        (fun k => -increment (start + k)) := by
  have hzeroNeg : AdditivePath.displacement start
      (fun k => -increment k) = 0 := by simp [hzero]
  have h := nonnegativeTail_iff_shiftedSurvival n start
    (fun k => -increment k) hstart hzeroNeg
  simpa only [AdditivePath.displacement_neg, neg_nonneg] using h

/-- At a zero of the walk, the terminal one-sign event splits into
the positive and reflected negative survival events. -/
theorem signStableFrom_iff_shiftedSurvival
    (n start : ℕ) (increment : ℕ → ℝ) (hstart : start ≤ n)
    (hzero : AdditivePath.displacement start increment = 0) :
    SignStableFrom n start increment ↔
      SurvivesNonnegative (n - start)
        (fun k => increment (start + k)) ∨
      SurvivesNonnegative (n - start)
        (fun k => -increment (start + k)) := by
  exact or_congr
    (nonnegativeTail_iff_shiftedSurvival n start increment hstart hzero)
    (nonpositiveTail_iff_negShiftedSurvival n start increment hstart hzero)

/-- The one-sided terminal segment is a measurable event on increment
sequences. -/
theorem measurableSet_signStableFrom (n start : ℕ) :
    MeasurableSet {increment : ℕ → ℝ | SignStableFrom n start increment} := by
  have hpos : MeasurableSet {increment : ℕ → ℝ |
      ∀ j : ℕ, start ≤ j → j ≤ n →
        0 ≤ AdditivePath.displacement j increment} := by
    have heq : {increment : ℕ → ℝ |
        ∀ j : ℕ, start ≤ j → j ≤ n →
          0 ≤ AdditivePath.displacement j increment} =
        ⋂ j : ℕ, if start ≤ j ∧ j ≤ n then
          {increment | 0 ≤ AdditivePath.displacement j increment} else Set.univ := by
      ext increment
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h j
        split_ifs with hj
        · exact h j hj.1 hj.2
        · trivial
      · intro h j hjstart hjn
        simpa [hjstart, hjn] using h j
    rw [heq]
    exact MeasurableSet.iInter fun j => by
      split_ifs
      · exact measurableSet_Ici.preimage (displacement_measurable j)
      · exact MeasurableSet.univ
  have hneg : MeasurableSet {increment : ℕ → ℝ |
      ∀ j : ℕ, start ≤ j → j ≤ n →
        AdditivePath.displacement j increment ≤ 0} := by
    have heq : {increment : ℕ → ℝ |
        ∀ j : ℕ, start ≤ j → j ≤ n →
          AdditivePath.displacement j increment ≤ 0} =
        ⋂ j : ℕ, if start ≤ j ∧ j ≤ n then
          {increment | AdditivePath.displacement j increment ≤ 0} else Set.univ := by
      ext increment
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h j
        split_ifs with hj
        · exact h j hj.1 hj.2
        · trivial
      · intro h j hjstart hjn
        simpa [hjstart, hjn] using h j
    rw [heq]
    exact MeasurableSet.iInter fun j => by
      split_ifs
      · exact measurableSet_Iic.preimage (displacement_measurable j)
      · exact MeasurableSet.univ
  exact hpos.union hneg

theorem not_signStableFrom_before_lastSignChangeIndex
    (n : ℕ) (increment : ℕ → ℝ)
    {k : ℕ} (hk : k < lastSignChangeIndex n increment) :
    ¬ SignStableFrom n k increment := by
  classical
  unfold lastSignChangeIndex at hk
  exact Nat.find_min (show ∃ j : ℕ, SignStableFrom n j increment from
    ⟨n, signStableFrom_self n increment⟩) hk

/-- The finite-walk event `μₙ = k` is the difference of the tail-sign
events at consecutive starting times. -/
theorem lastSignChangeIndex_eq_iff (n : ℕ) (increment : ℕ → ℝ)
    {k : ℕ} (hk : 0 < k) :
    lastSignChangeIndex n increment = k ↔
      SignStableFrom n k increment ∧
        ¬ SignStableFrom n (k - 1) increment := by
  constructor
  · intro heq
    refine ⟨heq ▸ signStableFrom_lastSignChangeIndex n increment, ?_⟩
    apply not_signStableFrom_before_lastSignChangeIndex n increment
    rw [heq]
    omega
  · rintro ⟨hstable, hprev⟩
    have hle : lastSignChangeIndex n increment ≤ k := by
      classical
      unfold lastSignChangeIndex
      exact Nat.find_min' (show ∃ j : ℕ, SignStableFrom n j increment from
        ⟨n, signStableFrom_self n increment⟩) hstable
    have hge : k ≤ lastSignChangeIndex n increment := by
      by_contra h
      have hidx : lastSignChangeIndex n increment ≤ k - 1 := by omega
      exact hprev (signStableFrom_mono_start n increment hidx
        (signStableFrom_lastSignChangeIndex n increment))
    exact Nat.le_antisymm hle hge

/-- At zero, the earliest one-sided segment starts at zero precisely
when the whole path already has one weak sign. -/
theorem lastSignChangeIndex_eq_zero_iff (n : ℕ) (increment : ℕ → ℝ) :
    lastSignChangeIndex n increment = 0 ↔ SignStableFrom n 0 increment := by
  constructor
  · intro h
    simpa [h] using signStableFrom_lastSignChangeIndex n increment
  · intro h
    have hle : lastSignChangeIndex n increment ≤ 0 := by
      classical
      unfold lastSignChangeIndex
      exact Nat.find_min' (show ∃ j : ℕ, SignStableFrom n j increment from
        ⟨n, signStableFrom_self n increment⟩) h
    omega

/-- The finite-walk last-sign-change time is a measurable random
variable. -/
theorem measurable_lastSignChangeIndex (n : ℕ) :
    Measurable (fun increment : ℕ → ℝ =>
      lastSignChangeIndex n increment) := by
  apply measurable_to_countable'
  intro k
  by_cases hk : k = 0
  · subst k
    simpa only [Set.preimage, Set.mem_singleton_iff,
      lastSignChangeIndex_eq_zero_iff] using
      measurableSet_signStableFrom n 0
  · have hpos : 0 < k := Nat.pos_of_ne_zero hk
    have heq : {increment : ℕ → ℝ | lastSignChangeIndex n increment = k} =
        {increment | SignStableFrom n k increment} ∩
          {increment | ¬ SignStableFrom n (k - 1) increment} := by
      ext increment
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff,
        lastSignChangeIndex_eq_iff n increment hpos]
    change MeasurableSet {increment : ℕ → ℝ | lastSignChangeIndex n increment = k}
    rw [heq]
    exact (measurableSet_signStableFrom n k).inter
      (measurableSet_signStableFrom n (k - 1)).compl

/-- Number of increments in the final segment with one weak sign. -/
noncomputable def terminalSignStableLength (n : ℕ) (increment : ℕ → ℝ) : ℕ :=
  n - lastSignChangeIndex n increment

end ProbabilityTheory.RandomWalk

end
