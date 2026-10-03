module

public import Probability.Sequence.IID
public import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Characteristic functions of i.i.d. sums

Exact characteristic-function formulas for finite sums under the canonical
i.i.d. sequence law.
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
