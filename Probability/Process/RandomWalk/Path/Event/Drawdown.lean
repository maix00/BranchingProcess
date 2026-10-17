/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Data.Fin.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Finite-history drawdown events

For $h : \operatorname{Fin}(n+1)\to\mathbb R$,
`ProbabilityTheory.RandomWalk.historyHasNoLargeDrop δ h` means
$h_i-h_j\le\delta$ whenever $i\le j$. The predicate
`ProbabilityTheory.RandomWalk.historyNoLargeDropAndEndpointBelow δ r h` adds
$h_n\le r$. The public measurability results are
`ProbabilityTheory.RandomWalk.measurableSet_historyHasNoLargeDrop` and
`ProbabilityTheory.RandomWalk.measurableSet_historyNoLargeDropAndEndpointBelow`,
which establish measurability in the finite product space.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- A finite path has no drawdown larger than `delta` when every earlier
value exceeds every later value by at most `delta`. -/
def historyHasNoLargeDrop {n : ℕ} (delta : ℝ)
    (history : Fin (n + 1) → ℝ) : Prop :=
  ∀ i j : Fin (n + 1), (i : ℕ) ≤ j → history i - history j ≤ delta

/-- The finite-history event imposing a drawdown bound and an endpoint upper
bound. This deterministic path predicate is shared by random-walk and
branching-walk applications. -/
def historyNoLargeDropAndEndpointBelow {n : ℕ} (delta threshold : ℝ)
    (history : Fin (n + 1) → ℝ) : Prop :=
  historyHasNoLargeDrop delta history ∧
    history ⟨n, Nat.lt_succ_self n⟩ ≤ threshold

theorem measurableSet_historyHasNoLargeDrop {n : ℕ} (delta : ℝ) :
    MeasurableSet {history : Fin (n + 1) → ℝ |
      historyHasNoLargeDrop delta history} := by
  rw [show {history : Fin (n + 1) → ℝ |
      historyHasNoLargeDrop delta history} =
    ⋂ i : Fin (n + 1), ⋂ j : Fin (n + 1),
      {history | (i : ℕ) ≤ j → history i - history j ≤ delta} by
    ext history
    simp [historyHasNoLargeDrop]]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => by
    by_cases hij : (i : ℕ) ≤ j
    · have hdiff : Measurable
          (fun history : Fin (n + 1) → ℝ => history i - history j) :=
        (measurable_pi_apply i).sub (measurable_pi_apply j)
      have hmeas : MeasurableSet
          {history : Fin (n + 1) → ℝ | history i - history j ≤ delta} :=
        measurableSet_Iic.preimage hdiff
      simpa only [hij, true_implies] using hmeas
    · simp [hij]

theorem measurableSet_historyNoLargeDropAndEndpointBelow {n : ℕ}
    (delta threshold : ℝ) :
    MeasurableSet {history : Fin (n + 1) → ℝ |
      historyNoLargeDropAndEndpointBelow delta threshold history} := by
  exact (measurableSet_historyHasNoLargeDrop delta).inter
    (measurableSet_Iic.preimage
      (measurable_pi_apply (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))))

end ProbabilityTheory.RandomWalk

end
