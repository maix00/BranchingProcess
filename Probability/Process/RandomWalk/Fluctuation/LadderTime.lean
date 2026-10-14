/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.RecordLocalTime

/-!
# Strict ascending ladder times and heights

The public definitions and theorems in this file are:

- ProbabilityTheory.RandomWalk.strictAscendingLadderTime:
  $T_k=\inf\{n\ge0:\ell_n\ge k\}$, with $T_k=\infty$ if the set is empty.
- ProbabilityTheory.RandomWalk.strictAscendingLadderTime_zero:
  $T_0=0$.
- ProbabilityTheory.RandomWalk.strictAscendingLadderTime_mono:
  $k\le l$ implies $T_k\le T_l$.
- ProbabilityTheory.RandomWalk.strictAscendingLadderTime_le_of_localTime_ge:
  $k\le\ell_n$ implies $T_k\le n$.
- ProbabilityTheory.RandomWalk.strictAscendingLadderTime_eq_top_of_localTime_lt:
  if $\ell_n<k$ for every $n$, then $T_k=\infty$.
- ProbabilityTheory.RandomWalk.strictAscendingLadderHeight:
  $H_k=S_{T_k}$ when $T_k<\infty$, and $H_k=\infty$ otherwise.
- ProbabilityTheory.RandomWalk.strictAscendingLadderHeight_zero:
  $H_0=0$.

These objects are the strict ascending ladder time and height in
Loïc Chaumont and R. A. Doney, *Invariance principles for local times at
the maximum of random walks and Lévy processes*, Section 2, after
equation (2.2), DOI 10.1214/09-AOP512.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- The first time at which the discrete local time at the maximum
reaches level k. The infimum of the empty set is infinity. -/
noncomputable def strictAscendingLadderTime
    (increment : ℕ → ℝ) (k : ℕ) : WithTop ℕ :=
  sInf {t : WithTop ℕ |
    ∃ n : ℕ, t = n ∧ k ≤ strictAscendingLocalTime increment n}

/-- The zeroth strict ascending ladder time is the initial time. -/
theorem strictAscendingLadderTime_zero (increment : ℕ → ℝ) :
    strictAscendingLadderTime increment 0 = 0 := by
  apply le_antisymm
  · apply sInf_le
    exact ⟨0, rfl, Nat.zero_le _⟩
  · exact bot_le

/-- Reaching a higher record count cannot occur earlier. -/
theorem strictAscendingLadderTime_mono
    (increment : ℕ → ℝ) {k l : ℕ} (hkl : k ≤ l) :
    strictAscendingLadderTime increment k ≤
      strictAscendingLadderTime increment l := by
  unfold strictAscendingLadderTime
  apply sInf_le_sInf
  rintro t ⟨n, rfl, hn⟩
  exact ⟨n, rfl, hkl.trans hn⟩

/-- A record level reached by time n has ladder time at most n. -/
theorem strictAscendingLadderTime_le_of_localTime_ge
    (increment : ℕ → ℝ) {k n : ℕ}
    (hkn : k ≤ strictAscendingLocalTime increment n) :
    strictAscendingLadderTime increment k ≤ n := by
  unfold strictAscendingLadderTime
  exact sInf_le ⟨n, rfl, hkn⟩

/-- A record level never reached has infinite ladder time. -/
theorem strictAscendingLadderTime_eq_top_of_localTime_lt
    (increment : ℕ → ℝ) {k : ℕ}
    (hk : ∀ n, strictAscendingLocalTime increment n < k) :
    strictAscendingLadderTime increment k = ⊤ := by
  unfold strictAscendingLadderTime
  have hempty :
      {t : WithTop ℕ |
        ∃ n : ℕ, t = n ∧ k ≤ strictAscendingLocalTime increment n} =
        ∅ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨n, _, hn⟩
    exact (Nat.not_le.mpr (hk n)) hn
  rw [hempty, sInf_empty]

/-- The height at a strict ascending ladder time, with infinity when
that time is infinite. -/
noncomputable def strictAscendingLadderHeight
    (increment : ℕ → ℝ) (k : ℕ) : WithTop ℝ :=
  match strictAscendingLadderTime increment k with
  | none => ⊤
  | some n => ((AdditivePath.displacement n increment : ℝ) : WithTop ℝ)

/-- The zeroth ladder height is the initial position. -/
theorem strictAscendingLadderHeight_zero (increment : ℕ → ℝ) :
    strictAscendingLadderHeight increment 0 = 0 := by
  simp [strictAscendingLadderHeight, strictAscendingLadderTime_zero,
    AdditivePath.displacement_zero]

end ProbabilityTheory.RandomWalk

end
