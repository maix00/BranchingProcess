/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Rademacher.ConditionedPathLaw
public import Probability.Process.RandomWalk.Rademacher.TerminalTransform

/-!
# The finite mixture of terminal path laws

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.measure_rademacherTerminalAbsolutePath_eq_mixture`:
  for $n>0$, the law of the terminal path is the finite mixture
  $\mathcal L(\widetilde Y_n)=\sum_{r=1}^n
  \mathbb P(\nu_n=r)\,\mathcal L(Y_r^+)$.

This is the distributional identity in the final paragraph of page 484
of Erwin Bolthausen, *On a functional central limit theorem for random
walks conditioned to stay positive*, Ann. Probab. 4(3) (1976),
480--485, DOI 10.1214/aop/1176996098. The fixed-length identity is
proved in `ConditionedPathLaw`.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open MeasureTheory ProbabilityTheory Set
open FunctionalLimit.Conditioned

/-- The terminal path law is the finite mixture of positive-survival
conditioned path laws, weighted by the terminal length. This is the
distributional identity on page 484 of Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned to
stay positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098. -/
theorem measure_rademacherTerminalAbsolutePath_eq_mixture
    {n : ℕ} (hn : 0 < n)
    (pathEvent : Set C(unitInterval, ℝ)) (hpathEvent : MeasurableSet pathEvent) :
    (iidSequenceLaw fairBoolMeasure).map
        (fun branch => rademacherTerminalAbsolutePath branch n) pathEvent =
      ∑ k ∈ Finset.range n,
        (iidSequenceLaw fairBoolMeasure)
          {branch : ℕ → Bool |
            terminalSignStableLength n (rademacherIncrementPath branch) = k + 1} *
          ((survivalConditionedLaw rademacherMeasure (k + 1)).map
            (normalizedLinearContinuousPathIcc
              (fun j => Real.sqrt j) (k + 1))) pathEvent := by
  have hY : Measurable (fun branch => rademacherTerminalAbsolutePath branch n) :=
    measurable_rademacherTerminalAbsolutePath hn
  have hν : Measurable (fun branch =>
      terminalSignStableLength n (rademacherIncrementPath branch)) := by
    exact (measurable_const.sub (measurable_lastSignChangeIndex n)).comp
      measurable_rademacherIncrementPath
  let cell (k : ℕ) : Set (ℕ → Bool) :=
    {branch | terminalSignStableLength n
        (rademacherIncrementPath branch) = k + 1 ∧
      rademacherTerminalAbsolutePath branch n ∈ pathEvent}
  have hpartition :
      {branch : ℕ → Bool | rademacherTerminalAbsolutePath branch n ∈ pathEvent} =
        ⋃ k ∈ Finset.range n, cell k := by
    ext branch
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, cell]
    constructor
    · intro hmem
      let length := terminalSignStableLength n (rademacherIncrementPath branch)
      have hpos : 0 < length := rademacher_terminalSignStableLength_pos branch hn
      have hle : length ≤ n := Nat.sub_le _ _
      refine ⟨length - 1, by omega, ?_⟩
      exact ⟨by omega, hmem⟩
    · rintro ⟨k, _, _, hmem⟩
      exact hmem
  have hdisj : PairwiseDisjoint (↑(Finset.range n)) cell := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro branch hbi hbj
    have hi' := hbi.1
    have hj' := hbj.1
    omega
  have hcell (k : ℕ) : MeasurableSet (cell k) :=
    (hν (measurableSet_singleton (k + 1))).inter
      (hpathEvent.preimage hY)
  rw [Measure.map_apply hY hpathEvent]
  change (iidSequenceLaw fairBoolMeasure)
      {branch : ℕ → Bool | rademacherTerminalAbsolutePath branch n ∈ pathEvent} = _
  rw [hpartition, measure_biUnion_finset hdisj (fun k _ => hcell k)]
  apply Finset.sum_congr rfl
  intro k hk
  exact measure_terminalAbsolutePath_atLength_eq_conditionedPath
    n (k + 1) (Nat.succ_pos k)
    (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
    pathEvent hpathEvent

end ProbabilityTheory.RandomWalk

end
