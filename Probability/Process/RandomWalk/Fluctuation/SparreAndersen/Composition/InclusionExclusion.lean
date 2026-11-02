/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Rotation.Basic
public import Algebra.BigOperators.PartialSum
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Group.Arithmetic
import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Rotation.Cover

/-!
# Inclusion and exclusion for cyclic survival

## Public declarations

- `ProbabilityTheory.RandomWalk.measureReal_nonnegative_endpoint_eq_cyclicSurvival_sum`:
  for a finite measure $\mu$ on the increment-vector space,
  $\mu_{\mathbb R}(S_n\ge0)=\sum_{\varnothing\ne U\subseteq[0,n-1]}
  (-1)^{|U|+1}\mu_{\mathbb R}(\bigcap_{k\in U}B_k)$, where $B_k$ is the
  cyclic-survival event from `Rotation/Basic.lean`.

This is Bauer, Godrèche, and Luck, *Statistics of persistent events in the
binomial random walk: Will the drunken sailor hit the sober man?*, Appendix A,
equation (A.4), *Journal of Statistical Physics* 96 (1999), 963--1019,
DOI 10.1023/A:1004636216365, arXiv:cond-mat/9905252.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

variable {G : Type*} [AddCommGroup G] [LinearOrder G]
  [IsOrderedAddMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

/-- Inclusion--exclusion for the union of cyclic survival events,
corresponding to Bauer--Godrèche--Luck, Appendix A, equation (A.4). -/
theorem measureReal_nonnegative_endpoint_eq_cyclicSurvival_sum
    (hIci : MeasurableSet (Set.Ici (0 : G)))
    {n : ℕ} (hn : 0 < n) (μ : Measure (Fin n → G))
    [IsFiniteMeasure μ] :
    μ.real {x : Fin n → G | 0 ≤ Fin.partialSum x (Fin.last n)} =
      ∑ u ∈ (Finset.univ : Finset (Fin n)).powerset with u.Nonempty,
        (-1 : ℝ) ^ (u.card + 1) *
          μ.real (⋂ k ∈ u, cyclicSurvivalEvent k) := by
  have hevent :
      {x : Fin n → G | 0 ≤ Fin.partialSum x (Fin.last n)} =
        ⋃ k : Fin n, cyclicSurvivalEvent k := by
    simpa only [cyclicSurvivalEvent] using
      nonnegative_finitePartialSum_eq_iUnion_cyclic_survival hn
  rw [hevent]
  have hformula := measureReal_biUnion_eq_sum_powerset
    (μ := μ) (t := (Finset.univ : Finset (Fin n)))
    (s := cyclicSurvivalEvent)
    (fun k _ => measurableSet_cyclicSurvivalEvent hIci k)
  simpa using hformula

end ProbabilityTheory.RandomWalk

end
