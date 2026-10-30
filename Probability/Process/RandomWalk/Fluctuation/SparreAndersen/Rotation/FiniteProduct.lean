/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Rotation.Basic
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Constructions.Pi
import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Rotation.Cover
import Probability.Process.RandomWalk.Path.Survival.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Cyclic survival probabilities under finite product laws

## Public declarations

- `ProbabilityTheory.RandomWalk.measure_pi_cyclicSurvivalEvent_eq_survival`:
  for each rotation $k$, the probability of $B_k$ under $\nu^{\otimes n}$
  equals the probability that every partial sum through time $n$ is
  nonnegative.
- `ProbabilityTheory.RandomWalk.measure_pi_nonnegative_endpoint_le_card_mul_survival`:
  for $n>0$ and identically distributed independent increments in an ordered
  measurable additive group,
  $\mathbb P(S_n\ge0)\le n\mathbb P(S_j\ge0\text{ for }1\le j\le n)$.

The invariance of each rotated finite product event and the resulting union
bound are the steps following the cyclic cover in M. Bauer, C. Godrèche, and
J.-M. Luck, *Statistics of persistent events in the binomial random walk:
Will the drunken sailor hit the sober man?*, Appendix A, equations (A.3)
and (A.6), *Journal of Statistical Physics* 96 (1999), 963--1019,
DOI 10.1023/A:1004636216365, arXiv:cond-mat/9905252.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

variable {G : Type*} [AddCommGroup G] [LinearOrder G]
  [MeasurableSpace G] [MeasurableAdd₂ G]

/-- A single cyclic survival event has the ordinary survival probability
under an IID finite-product law. This is the one-block case of
Bauer--Godrèche--Luck, Appendix A, equation (A.6). -/
theorem measure_pi_cyclicSurvivalEvent_eq_survival
    (hIci : MeasurableSet (Set.Ici (0 : G)))
    (ν : Measure G) [IsProbabilityMeasure ν]
    {n : ℕ} (k : Fin n) :
    Measure.pi (fun _ : Fin n => ν) (cyclicSurvivalEvent k) =
      Measure.pi (fun _ : Fin n => ν)
        {x : Fin n → G |
          ∀ j : Fin (n + 1), 0 ≤ Fin.partialSum x j} := by
  let e := finCycle k
  let T : (Fin n → G) ≃ᵐ (Fin n → G) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => G) e.symm
  have hmap : (Measure.pi (fun _ : Fin n => ν)).map T =
      Measure.pi (fun _ : Fin n => ν) := by
    simpa [T] using Measure.pi_map_piCongrLeft e.symm
      (fun _ : Fin n => ν)
  have hsafe := measurableSet_nonnegativePartialSum (n := n) hIci
  rw [cyclicSurvivalEvent_eq_preimage k]
  have hT (x : Fin n → G) (i : Fin n) : T x i = x (e i) := by
    simpa [T, MeasurableEquiv.coe_piCongrLeft] using
      (Equiv.piCongrLeft_apply_apply (P := fun _ : Fin n => G)
        e.symm x (e i))
  have hpreimage :
      (fun x : Fin n → G =>
        fun i : Fin n => x (finCycle k i)) ⁻¹'
          {x : Fin n → G |
            ∀ j : Fin (n + 1), 0 ≤ Fin.partialSum x j} =
        T ⁻¹' {x : Fin n → G |
          ∀ j : Fin (n + 1), 0 ≤ Fin.partialSum x j} := by
    ext x
    change (∀ j : Fin (n + 1),
        0 ≤ Fin.partialSum
          (fun i => x (finCycle k i)) j) ↔
      (∀ j : Fin (n + 1), 0 ≤ Fin.partialSum (T x) j)
    have hfun :
        (fun i : Fin n => x (finCycle k i)) =
          T x := by
      funext i
      exact (hT x i).symm
    rw [hfun]
  rw [hpreimage]
  rw [← Measure.map_apply T.measurable hsafe, hmap]

variable [IsOrderedAddMonoid G]

/-- The union bound applied to the cyclic cover of Bauer--Godrèche--Luck,
Appendix A, immediately after (A.3). It requires only identical independent
increments, with no moment or centering assumptions. -/
theorem measure_pi_nonnegative_endpoint_le_card_mul_survival
    (hIci : MeasurableSet (Set.Ici (0 : G)))
    (ν : Measure G) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) :
    Measure.pi (fun _ : Fin n => ν)
        {x : Fin n → G | 0 ≤ Fin.partialSum x (Fin.last n)} ≤
      n • Measure.pi (fun _ : Fin n => ν)
        {x : Fin n → G |
          ∀ j : Fin (n + 1), 0 ≤ Fin.partialSum x j} := by
  let μ := Measure.pi (fun _ : Fin n => ν)
  let safe : Set (Fin n → G) :=
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
      exact measure_pi_cyclicSurvivalEvent_eq_survival hIci ν k
    _ = n • μ safe := by simp

end ProbabilityTheory.RandomWalk

end
