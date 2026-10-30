/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uniform thresholds from sequential estimates

## Public declarations

- `Asymptotics.eventually_uniform_atTop_of_forall_tendsto_nat`:
  if $D(\Delta_n,x_n)$ implies $P(\Delta_n,x_n)$ eventually along every
  divergent real sequence and every admissible parameter sequence, then
  one threshold works for all $x$ satisfying $D(\Delta,x)$.

This general compactness step converts the sequential probability bounds
used in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with
Infinite Offspring* (master's thesis, Fudan University, 2026), Chapter 3,
proof of Lemma 3.5, to the uniform real-width quantifier in that lemma.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Asymptotics

/-- A counterexample above every real threshold can be selected at each
integer index, producing a divergent counterexample sequence. -/
theorem eventually_uniform_atTop_of_forall_tendsto_nat
    {α : Type*} (D P : ℝ → α → Prop)
    (hseq : ∀ (width : ℕ → ℝ) (parameter : ℕ → α),
      Tendsto width atTop atTop →
      (∀ n, D (width n) (parameter n)) →
      ∀ᶠ n : ℕ in atTop, P (width n) (parameter n)) :
    ∃ threshold : ℝ, ∀ width ≥ threshold, ∀ parameter,
      D width parameter → P width parameter := by
  classical
  by_contra hnot
  push Not at hnot
  have hbad (n : ℕ) : ∃ width : ℝ, (n : ℝ) ≤ width ∧
      ∃ parameter : α, D width parameter ∧ ¬P width parameter := hnot n
  choose width hwidth using hbad
  choose parameter hdomain hfailure using fun n => (hwidth n).2
  have hlimit : Tendsto width atTop atTop := by
    rw [tendsto_atTop]
    intro bound
    have hnat : ∀ᶠ n : ℕ in atTop, bound ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop bound)
    filter_upwards [hnat] with n hn
    exact hn.trans (hwidth n).1
  obtain ⟨n, hn⟩ := (hseq width parameter hlimit hdomain).exists
  exact hfailure n hn

end Asymptotics

end
