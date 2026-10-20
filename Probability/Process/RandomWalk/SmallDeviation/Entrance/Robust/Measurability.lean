/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Adapted.Filtration
public import Probability.Process.RandomWalk.SmallDeviation.Entrance.Robust.Event
/-!
# Prefix-filtration measurability of the robust entrance event

For $S_j=\sum_{i=0}^{j-1}\xi_i$ and
$h_j=cj/\Delta^2$, the public theorem
`ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.measurableSet_robustMovingTransitionEvent`
states that the event
\[
  \mathcal R_{n,\Delta,c}(x)=\{h_j\le x+S_j\le\Delta+h_j\ (1\le j\le n),\
  x+S_n\in[h_n+2\Delta/5,h_n+3\Delta/5]\}
\]
is measurable with respect to the first $n$ increments.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- All constraints of the robust event depend only on the first `n`
increments. -/
lemma measurableSet_robustMovingTransitionEvent
    (n : ℕ) (width drift start : ℝ) :
    MeasurableSet[sequencePrefixFiltration (E := ℝ) n]
      (robustMovingTransitionEvent n width drift start) := by
  have hpath : MeasurableSet[sequencePrefixFiltration (E := ℝ) n]
      {increment : ℕ → ℝ |
        ∀ k : Fin n,
          drift * ((k.val + 1 : ℕ) : ℝ) / width ^ 2 ≤
          start + AdditivePath.displacement (k + 1) increment ∧
          start + AdditivePath.displacement (k + 1) increment ≤
            width + drift * ((k.val + 1 : ℕ) : ℝ) / width ^ 2} := by
    rw [← Set.iInter_ofPred]
    apply MeasurableSet.iInter
    intro k
    have hposition : Measurable[sequencePrefixFiltration (E := ℝ) n]
        (fun increment : ℕ → ℝ =>
          start + AdditivePath.displacement (k + 1) increment) :=
      measurable_const.add
        (ProbabilityTheory.RandomWalk.displacement_measurable_prefix
          (k := (k : ℕ) + 1) (n := n) (Nat.succ_le_of_lt k.isLt))
    exact (measurableSet_Ici.preimage hposition).inter
      (measurableSet_Iic.preimage hposition)
  have hrobust : MeasurableSet[sequencePrefixFiltration (E := ℝ) n]
      {increment : ℕ → ℝ |
        drift * (n : ℝ) / width ^ 2 + 2 * width / 5 ≤
          start + AdditivePath.displacement n increment ∧
        start + AdditivePath.displacement n increment ≤
          drift * (n : ℝ) / width ^ 2 + 3 * width / 5} := by
    have hposition : Measurable[sequencePrefixFiltration (E := ℝ) n]
        (fun increment : ℕ → ℝ =>
          start + AdditivePath.displacement n increment) :=
      measurable_const.add
        (ProbabilityTheory.RandomWalk.displacement_measurable_prefix
          (k := n) (n := n) le_rfl)
    exact (measurableSet_Ici.preimage hposition).inter
      (measurableSet_Iic.preimage hposition)
  simpa only [robustMovingTransitionEvent, movingCorridorEvent,
    Set.ofPred_and] using hpath.inter hrobust

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
