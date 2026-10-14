/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.Nat

/-!
# Uniform eventual statements from divergent real sequences

The public theorem in this file is:

- `Asymptotics.eventually_atTop_of_forall_tendsto_nat`:
  if a predicate $P(\Delta)$ holds eventually along every sequence of real
  widths $\Delta_n\to\infty$, then there is a real threshold $\Delta_0$
  such that $P(\Delta)$ holds for every $\Delta\ge\Delta_0$.

This general compactness step converts the sequential probability bounds
used in Wang Yiyang, *Asymptotic speed of the $N$-branching random walk
with infinite offspring*, Chapter 3, proof of Lemma 3.5, to the uniform
real-width quantifier in that lemma.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Asymptotics

/-- Eventual validity on every sequence tending to infinity is equivalent
to eventual validity on the real at-top filter. -/
theorem eventually_atTop_of_forall_tendsto_nat
    {P : ℝ → Prop}
    (hseq : ∀ width : ℕ → ℝ, Tendsto width atTop atTop →
      ∀ᶠ n : ℕ in atTop, P (width n)) :
    ∀ᶠ Delta : ℝ in atTop, P Delta := by
  by_contra hnot
  have hfrequent : ∃ᶠ Delta : ℝ in atTop, ¬P Delta :=
    Filter.not_eventually.mp hnot
  have hbad (n : ℕ) : ∃ Delta : ℝ, (n : ℝ) ≤ Delta ∧ ¬P Delta := by
    obtain ⟨Delta, hDeltaBad, hDeltaLarge⟩ :=
      (hfrequent.and_eventually
        (eventually_ge_atTop (n : ℝ))).exists
    exact ⟨Delta, hDeltaLarge, hDeltaBad⟩
  let width : ℕ → ℝ := fun n => Classical.choose (hbad n)
  have hwidth : Tendsto width atTop atTop := by
    refine tendsto_atTop.2 fun bound => ?_
    obtain ⟨N, hN⟩ := exists_nat_ge bound
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hN.trans ((by exact_mod_cast hn : (N : ℝ) ≤ (n : ℝ)).trans
      (Classical.choose_spec (hbad n)).1)
  obtain ⟨n, hn⟩ := (hseq width hwidth).exists
  exact (Classical.choose_spec (hbad n)).2 hn

end Asymptotics

end
