/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.RunningMinimum

/-!
# Reversed increments on a finite time interval

The public definitions and theorems in this file are:

- `ProbabilityTheory.reverseIncrementsBefore`:
  for $0\le u\le t$, the reversed increment is $f(t)-f(t-u)$.
- `ProbabilityTheory.reverseIncrementsBefore_zero`:
  the reversed increment at $u=0$ is zero.
- `ProbabilityTheory.aboveRunningMinimum_eq_sSup_reverseIncrementsBefore`:
  $f(t)-\min_{0\le u\le t}f(u)$ equals the maximum of the reversed
  increments on $[0,t]$.

The final identity is the deterministic time-reversal step underlying
Lévy's reflected-process identity used in Lemma 2.3 of Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open scoped NNReal

namespace ProbabilityTheory

/-- The increment from `t-u` to `t`, indexed in reverse order over
the interval $0\le u\le t$. -/
noncomputable def reverseIncrementsBefore (f : C(ℝ≥0, ℝ)) (t : ℝ≥0) :
    C(Set.Icc (0 : ℝ≥0) t, ℝ) :=
  ⟨fun u => f t - f (t - u.1), by fun_prop⟩

/-- The reversed-increment path starts at zero. -/
theorem reverseIncrementsBefore_zero (f : C(ℝ≥0, ℝ)) (t : ℝ≥0) :
    reverseIncrementsBefore f t ⟨0, by simp⟩ = 0 := by
  simp [reverseIncrementsBefore]

/-- The height above the running minimum is the maximum of the reversed
increments on the finite horizon. -/
theorem aboveRunningMinimum_eq_sSup_reverseIncrementsBefore
    (f : C(ℝ≥0, ℝ)) (t : ℝ≥0) :
    aboveRunningMinimum f t =
      sSup (Set.range (reverseIncrementsBefore f t)) := by
  obtain ⟨v, hv, hmin⟩ := exists_runningMinimum_eq f t
  let u : Set.Icc (0 : ℝ≥0) t :=
    ⟨t - v, bot_le, tsub_le_self⟩
  have hu : t - u.1 = v := by
    dsimp [u]
    exact tsub_tsub_cancel_of_le hv.2
  have hmember : aboveRunningMinimum f t ∈
      Set.range (reverseIncrementsBefore f t) := by
    refine ⟨u, ?_⟩
    simp [reverseIncrementsBefore, aboveRunningMinimum, hu, hmin]
  have hupper : ∀ x ∈ Set.range (reverseIncrementsBefore f t),
      x ≤ aboveRunningMinimum f t := by
    rintro x ⟨w, rfl⟩
    change f t - f (t - w.1) ≤ f t - runningMinimum f t
    exact sub_le_sub_left (runningMinimum_le f tsub_le_self) _
  have hbdd : BddAbove (Set.range (reverseIncrementsBefore f t)) :=
    ⟨aboveRunningMinimum f t, hupper⟩
  exact le_antisymm (le_csSup hbdd hmember)
    (csSup_le ⟨_, hmember⟩ hupper)

end ProbabilityTheory

end
