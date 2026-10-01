module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Drift relative to the stable scale of short blocks

For stable index greater than one, a fixed linear drift over a block of
length `1/(n+1)` is negligible compared with the block's stable scale.
-/

@[expose] public section

namespace ProbabilityTheory

open Filter
open scoped Topology

theorem tendsto_drift_over_stableScale_zero
    (α : ℝ) (hα : 1 < α) (v : ℝ) :
    Tendsto (fun n : ℕ =>
      v * ((n : ℝ) + 1) ^ (1 / α - 1)) atTop (𝓝 0) := by
  have hαpos : 0 < α := by linarith
  have hexp : 0 < 1 - 1 / α := by
    have hdiv : 1 / α < 1 := (div_lt_one hαpos).2 hα
    linarith
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa [Function.comp_def, Nat.cast_add] using
      ((tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
          (tendsto_add_atTop_nat 1))
  have hpow : Tendsto (fun n : ℕ =>
      ((n : ℝ) + 1) ^ (-(1 - 1 / α))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hexp).comp hbase
  convert hpow.const_mul v using 1 <;> simp [sub_eq_add_neg]

end ProbabilityTheory

end
