/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Composition.Lemmas.BlockProbability
public import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Composition.Cyclic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Cyclic-gap formula for a finite random walk

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.measureReal_nonnegative_endpoint_eq_cyclicGap_sum`:
  for an i.i.d. law on a linearly ordered additive commutative group whose
  order is compatible with addition, the endpoint probability
  $\mathbb P(S_n\ge0)$ is an alternating sum over nonempty cyclic-start sets;
  each term is the product of the nonnegative-survival probabilities on its
  consecutive cyclic gaps. The assumptions are measurable addition and a
  measurable nonnegative half-line, together with a probability measure for
  one increment law.

This is equation (A.6) of Bauer--Godrèche--Luck. The formalized state-space
generality follows from the proof's hypotheses; the cited article formulates
the calculation for a one-dimensional random walk. Measurability of
subtraction is not needed because each rotated event is the preimage of
ordinary survival under a coordinate permutation.

The source is M. Bauer, C. Godrèche, and J.-M. Luck, “Statistics of
persistent events in the binomial random walk: Will the drunken sailor hit
the sober man?”, Appendix A, equations (A.3)--(A.6), *Journal of Statistical
Physics* 96 (1999), 963--1019, DOI 10.1023/A:1004636216365,
arXiv:cond-mat/9905252. The extension from real increments to ordered
measurable additive groups follows from the hypotheses used in the finite
partial-sum and cyclic-gap arguments.
-/

public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

variable {G : Type*} [AddCommGroup G] [LinearOrder G]
  [IsOrderedAddMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

/-- The finite cyclic-gap expansion of the endpoint probability for an
i.i.d. increment law on an ordered measurable additive group. -/
theorem measureReal_nonnegative_endpoint_eq_cyclicGap_sum
    (hIci : MeasurableSet (Set.Ici (0 : G)))
    (ν : Measure G) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) :
    (Measure.pi (fun _ : Fin n => ν)).real
      {x : Fin n → G | 0 ≤ Fin.partialSum x (Fin.last n)} =
      ∑ u ∈ (Finset.univ : Finset (Fin n)).powerset with u.Nonempty,
        (-1 : ℝ) ^ (u.card + 1) *
          (if hu : u.Nonempty then
            ∏ j : Fin u.card,
              (Measure.pi (fun _ : Fin (cyclicGapLength u hu j) => ν)).real
                {z : Fin (cyclicGapLength u hu j) → G |
                  ∀ t : Fin (cyclicGapLength u hu j + 1),
                    0 ≤ Fin.partialSum z t}
          else 0) := by
  rw [measureReal_nonnegative_endpoint_eq_cyclicBlock_sum
    (hIci := hIci) hn (Measure.pi (fun _ : Fin n => ν))]
  apply Finset.sum_congr rfl
  intro u hu
  have hnonempty : u.Nonempty := (Finset.mem_filter.mp hu).2
  simp only [dite_eq_left hnonempty]
  congr 1
  rw [MeasureTheory.measureReal_def,
    measure_pi_cyclicBlockEvent_eq_prod (hIci := hIci) ν hn u hnonempty,
    ENNReal.toReal_prod]
  rfl

end ProbabilityTheory.RandomWalk

end
