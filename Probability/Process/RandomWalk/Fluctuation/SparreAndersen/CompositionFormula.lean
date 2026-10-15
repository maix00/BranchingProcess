/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.CyclicComposition

/-!
# Composition formula for endpoint probabilities

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.measureReal_nonnegative_endpoint_eq_composition_sum`:
  the probability $\mathbb P(S_n\ge0)$ is an alternating sum over positive
  compositions of $n$, with the product of their nonnegative-survival
  probabilities weighted by the last part's length.

This is equation (A.6) reindexed as in equation (A.7) of M. Bauer,
C. Godrèche, and J.-M. Luck, *Statistics of persistent events in the
binomial random walk: Will the drunken sailor hit the sober man?*,
Appendix A (arXiv:cond-mat/9905252).
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

/-- The composition form of Bauer--Godrèche--Luck, Appendix A, (A.6).
The factor given by the last part counts the available positions of the
first selected start. -/
theorem measureReal_nonnegative_endpoint_eq_composition_sum
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) :
    (Measure.pi (fun _ : Fin n => ν)).real
      {x : Fin n → ℝ | 0 ≤ Fin.partialSum x (Fin.last n)} =
      ∑ c : Composition n,
        (c.blocksFun
          ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩ : ℝ) *
          ((-1 : ℝ) ^ (c.length + 1) *
            ∏ j : Fin c.length,
              (Measure.pi (fun _ : Fin (c.blocksFun j) => ν)).real
                {z : Fin (c.blocksFun j) → ℝ |
                  ∀ t : Fin (c.blocksFun j + 1),
                    0 ≤ Fin.partialSum z t}) := by
  let F : ℕ → ℝ := fun k =>
    (Measure.pi (fun _ : Fin k => ν)).real
      {z : Fin k → ℝ |
        ∀ t : Fin (k + 1), 0 ≤ Fin.partialSum z t}
  have hsource := measureReal_nonnegative_endpoint_eq_cyclicGap_sum ν hn
  have hsum :
      (∑ u ∈ (Finset.univ : Finset (Fin n)).powerset with u.Nonempty,
        (-1 : ℝ) ^ (u.card + 1) *
          (if hu : u.Nonempty then
            ∏ j : Fin u.card, F (cyclicGapLength u hu j)
          else 0)) =
      ∑ u : {u : Finset (Fin n) // u.Nonempty},
        (-1 : ℝ) ^ (u.val.card + 1) *
          ∏ j : Fin u.val.card,
            F (cyclicGapLength u.val u.property j) := by
    classical
    simp [F]
    rw [← Finset.sum_subtype_eq_sum_filter]
    rw [Finset.subtype_univ]
    apply Finset.sum_congr rfl
    intro u _
    simp only [dite_eq_left u.property]
  rw [hsource]
  change _ = ∑ c : Composition n,
    (c.blocksFun
      ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩ : ℝ) *
      ((-1 : ℝ) ^ (c.length + 1) *
        ∏ j : Fin c.length, F (c.blocksFun j))
  rw [hsum]
  exact sum_cyclicGap_products_eq_composition_sum hn
    (fun k => (-1 : ℝ) ^ (k + 1)) F

end ProbabilityTheory.RandomWalk

end
