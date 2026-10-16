/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Rotation.Cover
public import Algebra.BigOperators.CyclicReindex
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Inclusion and exclusion for cyclic survival

The public definitions and theorems in this file are:

- `ProbabilityTheory.RandomWalk.cyclicSurvivalEvent`: the event that the
  cyclic rotation at $k$ has all $n+1$ partial sums nonnegative.
- `ProbabilityTheory.RandomWalk.measurableSet_cyclicSurvivalEvent`:
  each such event is measurable in the finite product space.
- `ProbabilityTheory.RandomWalk.cyclicSurvivalEvent_eq_preimage`:
  $B_n^{k+1}$ is ordinary nonnegative survival after the cyclic
  permutation $i\mapsto(k+i)\bmod n$ of increments.
- `ProbabilityTheory.RandomWalk.measure_pi_cyclicSurvivalEvent_eq_survival`:
  every $B_n^{k+1}$ has the length-$n$ nonnegative-survival probability
  under an i.i.d. finite product law.
- `ProbabilityTheory.RandomWalk.measure_pi_nonnegative_endpoint_le_card_mul_survival`:
  for every $n>0$ and any i.i.d. real increments,
  $\mathbb P(S_n\ge0)\le n\mathbb P(S_j\ge0\text{ for }1\le j\le n)$.
- `ProbabilityTheory.RandomWalk.measureReal_nonnegative_endpoint_eq_cyclicSurvival_sum`:
  $\mathbb P(S_n\ge0)$ is the alternating sum of probabilities of nonempty
  intersections of cyclic survival events.

This is equation (A.4) in M. Bauer, C. Godrèche, and J.-M. Luck,
*Statistics of persistent events in the binomial random walk: Will the
drunken sailor hit the sober man?*, Appendix A (arXiv:cond-mat/9905252).
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

/-- The cyclic survival event $B_n^{k+1}$ in Bauer--Godrèche--Luck,
Appendix A, equation (A.3). -/
def cyclicSurvivalEvent {n : ℕ} (k : Fin n) : Set (Fin n → ℝ) :=
  {x | ∀ j : Fin (n + 1),
    0 ≤ Fin.cyclicPartialSum (Fin.partialSum x) k j}

/-- A cyclic survival event is the preimage of ordinary nonnegative
survival under the corresponding coordinate permutation. -/
theorem cyclicSurvivalEvent_eq_preimage {n : ℕ} (hn : 0 < n)
    (k : Fin n) :
    cyclicSurvivalEvent k =
      (fun x : Fin n → ℝ =>
        fun i : Fin n => x (Fin.cyclicCoordinateReindex hn k i)) ⁻¹'
        {y : Fin n → ℝ |
          ∀ j : Fin (n + 1), 0 ≤ Fin.partialSum y j} := by
  ext x
  change (∀ j : Fin (n + 1),
      0 ≤ Fin.cyclicPartialSum (Fin.partialSum x) k j) ↔
    (∀ j : Fin (n + 1),
      0 ≤ Fin.partialSum
        (fun i => x (Fin.cyclicCoordinateReindex hn k i)) j)
  simp_rw [Fin.partialSum_cyclicCoordinateReindex hn x k]

private lemma measurable_finitePartialSum {n : ℕ}
    (j : Fin (n + 1)) :
    Measurable (fun x : Fin n → ℝ => Fin.partialSum x j) := by
  induction j using Fin.induction with
  | zero => simp
  | succ j ih =>
    have hsum :
        (fun x : Fin n → ℝ => Fin.partialSum x j.succ) =
          fun x => Fin.partialSum x j.castSucc + x j :=
      funext fun x => Fin.partialSum_succ x j
    rw [hsum]
    exact ih.add (measurable_pi_apply j)

private lemma measurable_cyclicPartialSum {n : ℕ}
    (k : Fin n) (j : Fin (n + 1)) :
    Measurable (fun x : Fin n → ℝ =>
      Fin.cyclicPartialSum (Fin.partialSum x) k j) := by
  by_cases h : k.val + j.val ≤ n
  · convert (measurable_finitePartialSum
        (⟨k.val + j.val, Nat.lt_succ_of_le h⟩ : Fin (n + 1))).sub
        (measurable_finitePartialSum k.castSucc) using 1
    funext x
    simp [Fin.cyclicPartialSum, h, Pi.sub_apply]
  · convert ((measurable_finitePartialSum (Fin.last n)).sub
        (measurable_finitePartialSum k.castSucc)).add
        (measurable_finitePartialSum
          (⟨k.val + j.val - n, by omega⟩ : Fin (n + 1))) using 1
    funext x
    simp [Fin.cyclicPartialSum, h, Pi.sub_apply, Pi.add_apply]

/-- Every cyclic survival event is measurable. -/
theorem measurableSet_cyclicSurvivalEvent {n : ℕ} (k : Fin n) :
    MeasurableSet (cyclicSurvivalEvent k) := by
  have h : MeasurableSet (⋂ j : Fin (n + 1),
      {x : Fin n → ℝ |
        0 ≤ Fin.cyclicPartialSum (Fin.partialSum x) k j}) := by
    exact MeasurableSet.iInter fun j =>
      measurableSet_Ici.preimage (measurable_cyclicPartialSum k j)
  simpa only [cyclicSurvivalEvent, Set.iInter_ofPred] using h

/-- A single cyclic survival event has the ordinary survival probability
under an IID finite-product law. This is the one-block case of
Bauer--Godrèche--Luck, Appendix A, equation (A.6). -/
theorem measure_pi_cyclicSurvivalEvent_eq_survival
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) (k : Fin n) :
    Measure.pi (fun _ : Fin n => ν) (cyclicSurvivalEvent k) =
      Measure.pi (fun _ : Fin n => ν)
        {x : Fin n → ℝ |
          ∀ j : Fin (n + 1), 0 ≤ Fin.partialSum x j} := by
  let e := Fin.cyclicCoordinateReindex hn k
  let T : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e.symm
  have hmap : (Measure.pi (fun _ : Fin n => ν)).map T =
      Measure.pi (fun _ : Fin n => ν) := by
    simpa [T] using Measure.pi_map_piCongrLeft e.symm
      (fun _ : Fin n => ν)
  have hsafe : MeasurableSet
      {x : Fin n → ℝ |
        ∀ j : Fin (n + 1), 0 ≤ Fin.partialSum x j} := by
    have h : MeasurableSet (⋂ j : Fin (n + 1),
        {x : Fin n → ℝ | 0 ≤ Fin.partialSum x j}) := by
      exact MeasurableSet.iInter fun j =>
        measurableSet_Ici.preimage (measurable_finitePartialSum j)
    simpa only [Set.iInter_ofPred] using h
  rw [cyclicSurvivalEvent_eq_preimage hn k]
  have hT (x : Fin n → ℝ) (i : Fin n) : T x i = x (e i) := by
    simpa [T, MeasurableEquiv.coe_piCongrLeft] using
      (Equiv.piCongrLeft_apply_apply (P := fun _ : Fin n => ℝ)
        e.symm x (e i))
  have hpreimage :
      (fun x : Fin n → ℝ =>
        fun i : Fin n => x (Fin.cyclicCoordinateReindex hn k i)) ⁻¹'
          {x : Fin n → ℝ |
            ∀ j : Fin (n + 1), 0 ≤ Fin.partialSum x j} =
        T ⁻¹' {x : Fin n → ℝ |
          ∀ j : Fin (n + 1), 0 ≤ Fin.partialSum x j} := by
    ext x
    change (∀ j : Fin (n + 1),
        0 ≤ Fin.partialSum
          (fun i => x (Fin.cyclicCoordinateReindex hn k i)) j) ↔
      (∀ j : Fin (n + 1), 0 ≤ Fin.partialSum (T x) j)
    have hfun :
        (fun i : Fin n => x (Fin.cyclicCoordinateReindex hn k i)) =
          T x := by
      funext i
      exact (hT x i).symm
    rw [hfun]
  rw [hpreimage]
  rw [← Measure.map_apply T.measurable hsafe, hmap]

/-- The union bound applied to the cyclic cover of Bauer--Godrèche--Luck,
Appendix A, immediately after (A.3). It requires only identical independent
increments, with no moment or centering assumptions. -/
theorem measure_pi_nonnegative_endpoint_le_card_mul_survival
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) :
    Measure.pi (fun _ : Fin n => ν)
        {x : Fin n → ℝ | 0 ≤ Fin.partialSum x (Fin.last n)} ≤
      n • Measure.pi (fun _ : Fin n => ν)
        {x : Fin n → ℝ |
          ∀ j : Fin (n + 1), 0 ≤ Fin.partialSum x j} := by
  let μ := Measure.pi (fun _ : Fin n => ν)
  let safe : Set (Fin n → ℝ) :=
    {x | ∀ j : Fin (n + 1), 0 ≤ Fin.partialSum x j}
  calc
    μ {x | 0 ≤ Fin.partialSum x (Fin.last n)} =
        μ (⋃ k : Fin n, cyclicSurvivalEvent k) := by
          simpa only [cyclicSurvivalEvent] using
            congrArg μ (nonnegative_finitePartialSum_eq_iUnion_cyclic_survival hn)
    _ ≤ ∑ k : Fin n, μ (cyclicSurvivalEvent k) :=
      measure_iUnion_fintype_le μ _
    _ = ∑ _k : Fin n, μ safe := by
      apply Finset.sum_congr rfl
      intro k _
      exact measure_pi_cyclicSurvivalEvent_eq_survival ν hn k
    _ = n • μ safe := by simp

/-- Inclusion--exclusion for the union of cyclic survival events,
corresponding to Bauer--Godrèche--Luck, Appendix A, equation (A.4). -/
theorem measureReal_nonnegative_endpoint_eq_cyclicSurvival_sum
    {n : ℕ} (hn : 0 < n) (μ : Measure (Fin n → ℝ))
    [IsFiniteMeasure μ] :
    μ.real {x : Fin n → ℝ | 0 ≤ Fin.partialSum x (Fin.last n)} =
      ∑ u ∈ (Finset.univ : Finset (Fin n)).powerset with u.Nonempty,
        (-1 : ℝ) ^ (u.card + 1) *
          μ.real (⋂ k ∈ u, cyclicSurvivalEvent k) := by
  have hevent :
      {x : Fin n → ℝ | 0 ≤ Fin.partialSum x (Fin.last n)} =
        ⋃ k : Fin n, cyclicSurvivalEvent k := by
    simpa only [cyclicSurvivalEvent] using
      nonnegative_finitePartialSum_eq_iUnion_cyclic_survival hn
  rw [hevent]
  have hformula := measureReal_biUnion_eq_sum_powerset
    (μ := μ) (t := (Finset.univ : Finset (Fin n)))
    (s := cyclicSurvivalEvent)
    (fun k _ => measurableSet_cyclicSurvivalEvent k)
  simpa using hformula

end ProbabilityTheory.RandomWalk

end
