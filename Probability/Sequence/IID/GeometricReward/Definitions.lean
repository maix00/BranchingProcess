/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Events and terms for geometric trial rewards

## Public declarations

- `geometricFailurePrefix X B n` is $\bigcap_{i<n}\{X_i\notin B\}$, the event that the
  first $n$ trials fail.
- `measurableSet_geometricFailurePrefix` proves measurability when each trial and $B$ are
  measurable.
- `geometricPrefixRewardTerm X B R n` is $R(X_n)$ multiplied by the indicator that every
  earlier trial failed.

These definitions describe the finite event and summand used by the IID geometric-reward
formulas in `FirstMoment.lean`. The exponential-cycle term is defined beside its transform
in `ExponentialTransform.lean`.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The event that the first `n` trials all fail. The current trial at index
`n` is not included, so this event is independent of its mark for an iid
sequence. -/
def geometricFailurePrefix (X : ℕ → Ω → α) (B : Set α) (n : ℕ) : Set Ω :=
  ⋂ i ∈ Finset.range n, X i ⁻¹' Bᶜ

theorem measurableSet_geometricFailurePrefix
    {X : ℕ → Ω → α} {B : Set α}
    (hX : ∀ i, Measurable (X i)) (hB : MeasurableSet B) (n : ℕ) :
    MeasurableSet (geometricFailurePrefix X B n) := by
  unfold geometricFailurePrefix
  exact MeasurableSet.biInter (Finset.countable_toSet (Finset.range n)) fun i hi =>
    MeasurableSet.preimage hB.compl (hX i)

/-- A reward on trial `n` is counted exactly when all earlier trials failed. -/
noncomputable def geometricPrefixRewardTerm
    (X : ℕ → Ω → α) (B : Set α) (R : α → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => R (X n ω) *
    (geometricFailurePrefix X B n).indicator (fun _ => (1 : ℝ)) ω

end ProbabilityTheory

end
