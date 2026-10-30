/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.PartialSum
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Constructions.Pi
import all Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Survival.Lemmas.Recurrence

/-!
# Finite coefficient recurrence for nonnegative random-walk paths

## Public declarations

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.measureReal_nonnegative_endpoint_recurrence`:
  for every positive $n$, the endpoint sign probability $P_n$ and
  nonnegative-survival probabilities $F_j$ satisfy
  $P_n=nF_n-\sum_{j=1}^{n-1}F_jP_{n-j}$.

This is the coefficient recurrence in equation (2.2) of Section 2 of
M. Bauer, C. Godrèche, and J.-M. Luck, *Statistics of persistent events in
the binomial random walk: Will the drunken sailor hit the sober man?*,
*Journal of Statistical Physics* 96 (1999), 963–1019, DOI
10.1023/A:1004636216365, arXiv:cond-mat/9905252. In Appendix A,
equations (A.7)--(A.8) derive the Sparre--Andersen generating-function
identity that yields this recurrence. The formalization groups the finite
composition sum by its first part: the singleton composition contributes
$nF_n$, and each longer composition contributes a convolution term.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

/-- The finite coefficient recurrence of Bauer--Godrèche--Luck, Section 2,
equation (2.2), obtained from the generating-function identity derived in
Appendix A, equations (A.7)--(A.8). The left side is $P_n$, and the
path-confinement probabilities in the right side are $F_j$. -/
theorem measureReal_nonnegative_endpoint_recurrence
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) :
    (Measure.pi (fun _ : Fin n => ν)).real
      {x : Fin n → ℝ | 0 ≤ Fin.partialSum x (Fin.last n)} =
      (n : ℝ) *
        (Measure.pi (fun _ : Fin n => ν)).real
          {z : Fin n → ℝ |
            ∀ t : Fin (n + 1), 0 ≤ Fin.partialSum z t} -
      ∑ r : Fin (n - 1),
        (Measure.pi (fun _ : Fin (r.val + 1) => ν)).real
          {z : Fin (r.val + 1) → ℝ |
            ∀ t : Fin (r.val + 1 + 1), 0 ≤ Fin.partialSum z t} *
        (Measure.pi (fun _ : Fin (n - (r.val + 1)) => ν)).real
          {x : Fin (n - (r.val + 1)) → ℝ |
            0 ≤ Fin.partialSum x (Fin.last (n - (r.val + 1)))} := by
  exact nonnegativeEndpointProbability_recurrence ν hn

end ProbabilityTheory.RandomWalk

end
