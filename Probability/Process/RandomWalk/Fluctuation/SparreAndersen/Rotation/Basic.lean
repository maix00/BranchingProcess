/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.PartialSum
public import Algebra.BigOperators.CyclicReindex
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Group.Arithmetic
import Probability.Process.RandomWalk.Path.Survival.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Cyclic survival events

## Public declarations

- `ProbabilityTheory.RandomWalk.cyclicSurvivalEvent`: for increments
  $x\in G^n$, the event
  $B_k=\{x: \operatorname{cyclicPartialSum}(\operatorname{partialSum}(x),k,j)
  \ge0\text{ for every }j\le n\}$.
- `ProbabilityTheory.RandomWalk.cyclicSurvivalEvent_eq_preimage`:
  $B_k$ is the preimage of ordinary survival under the coordinate permutation
  $x\mapsto(x_{(k+i)\bmod n})_{i<n}$.
- `ProbabilityTheory.RandomWalk.measurableSet_cyclicSurvivalEvent`:
  if $\{y\in G: y\ge0\}$ is measurable, then $B_k$ is measurable.
The cyclic event and its coordinate-permutation representation are the
combinatorial step in M. Bauer, C. Godrèche, and J.-M. Luck, *Statistics of
persistent events in the binomial random walk: Will the drunken sailor hit
the sober man?*, Appendix A, equation (A.3), *Journal of Statistical
Physics* 96 (1999), 963--1019, DOI 10.1023/A:1004636216365,
arXiv:cond-mat/9905252.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

variable {G : Type*} [AddCommGroup G] [LinearOrder G]

/-- The cyclic survival event $B_n^{k+1}$ in Bauer--Godrèche--Luck,
Appendix A, equation (A.3). -/
def cyclicSurvivalEvent {n : ℕ} (k : Fin n) : Set (Fin n → G) :=
  {x | ∀ j : Fin (n + 1),
    0 ≤ Fin.cyclicPartialSum (Fin.partialSum x) k j}

/-- A cyclic survival event is the preimage of ordinary nonnegative
survival under the corresponding coordinate permutation. -/
theorem cyclicSurvivalEvent_eq_preimage {n : ℕ} (k : Fin n) :
    cyclicSurvivalEvent k =
      (fun x : Fin n → G =>
        fun i : Fin n => x (finCycle k i)) ⁻¹'
        {y : Fin n → G |
          ∀ j : Fin (n + 1), 0 ≤ Fin.partialSum y j} := by
  ext x
  change (∀ j : Fin (n + 1),
      0 ≤ Fin.cyclicPartialSum (Fin.partialSum x) k j) ↔
    (∀ j : Fin (n + 1),
      0 ≤ Fin.partialSum
        (fun i => x (finCycle k i)) j)
  simp_rw [Fin.partialSum_finCycle x k]

variable [MeasurableSpace G] [MeasurableAdd₂ G]

section MeasurableEvents

/-- Every cyclic survival event is measurable. -/
theorem measurableSet_cyclicSurvivalEvent
    (hIci : MeasurableSet (Set.Ici (0 : G))) {n : ℕ} (k : Fin n) :
    MeasurableSet (cyclicSurvivalEvent (G := G) k) := by
  let e := finCycle k
  let T : (Fin n → G) ≃ᵐ (Fin n → G) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => G) e.symm
  have hT (x : Fin n → G) (i : Fin n) : T x i = x (e i) := by
    simpa [T, MeasurableEquiv.coe_piCongrLeft] using
      (Equiv.piCongrLeft_apply_apply (P := fun _ : Fin n => G)
        e.symm x (e i))
  have hmap :
      (fun x : Fin n → G =>
        fun i : Fin n => x (finCycle k i)) = T := by
    funext x i
    exact (hT x i).symm
  rw [cyclicSurvivalEvent_eq_preimage k, hmap]
  exact (measurableSet_nonnegativePartialSum hIci).preimage T.measurable

end MeasurableEvents

end ProbabilityTheory.RandomWalk

end
