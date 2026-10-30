/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Sequence.IID.Basic
public import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Characteristic functions of i.i.d. sums

## Public declarations

- `ProbabilityTheory.iidSequenceLaw_charFun_sum`: for a probability measure
  $\nu$ on $\mathbb R$, $n\in\mathbb N$, and $t\in\mathbb R$,
  \[
    \operatorname{charFun}\bigl((\texttt{iidSequenceLaw}\,\nu)\circ
      (\omega\mapsto\sum_{k<n}\omega_k)^{-1}\bigr)(t)
      =(\operatorname{charFun}\,\nu(t))^n.
  \]
The proof specializes Mathlib's `ProbabilityTheory.charFun_map_fun_finsetSum_eq_prod` to the finite coordinate family of `iidSequenceLaw`.
-/

open MeasureTheory
open scoped BigOperators

@[expose] public section

namespace ProbabilityTheory

/-- The characteristic function of the sum of the first `n` coordinates of
the canonical i.i.d. sequence is the `n`-th power of the one-step
characteristic function. -/
theorem iidSequenceLaw_charFun_sum
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (n : ℕ) :
    charFun ((iidSequenceLaw ν).map
      (fun sequence : ℕ → ℝ => ∑ k ∈ Finset.range n, sequence k)) =
      fun t => (charFun ν t) ^ n := by
  ext t
  rw [(iidSequenceLaw_independent ν).restrict (Finset.range n)
    |>.charFun_map_fun_finsetSum_eq_prod
    (s := Finset.range n)
    (fun k _ => (measurable_pi_apply k).aemeasurable)]
  simp only [iidSequenceLaw_map_apply]
  simp

end ProbabilityTheory

end
