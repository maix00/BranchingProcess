/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Rademacher
public import Probability.Process.RandomWalk.Path.LastSignChange
public import Probability.Process.RandomWalk.Path.Interpolation.Basic

/-!
# The final one-sided segment of a Rademacher walk

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.rademacher_displacement_int`:
  every partial sum $S_n$ of the $\pm1$ walk is an integer.
- `ProbabilityTheory.RandomWalk.rademacher_signStableFrom_penultimate`:
  $S_{n-1},S_n$ have one weak sign when $n\ge1$.
- `ProbabilityTheory.RandomWalk.rademacher_terminalSignStableLength_pos`:
  the terminal one-sided segment satisfies $\nu_n=n-\mu_n\ge1$.
- `ProbabilityTheory.RandomWalk.rademacher_displacement_lastSignChange_eq_zero`:
  $S_{\mu_n}=0$.
- `ProbabilityTheory.RandomWalk.rademacherTerminalAbsolutePath`:
  the continuous polygonal path $\widetilde Y_n$ with grid values
  $\widetilde Y_n(k/\nu_n)=|S_{\mu_n+k}|/\sqrt{\nu_n}$.
- `ProbabilityTheory.RandomWalk.rademacherTerminalAbsolutePath_grid`:
  this grid-value identity for $0\le k\le\nu_n$.

The final assertion is the parenthetical remark following the definitions
of $\mu_n$ and $\nu_n$ on page 484 of Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned to
stay positive*, Ann. Probab. 4(3) (1976), 480--485.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- The partial sums of the Boolean Rademacher walk are integer-valued. -/
theorem rademacher_displacement_int (branch : ℕ → Bool) (n : ℕ) :
    ∃ z : ℤ, AdditivePath.displacement n (rademacherIncrementPath branch) = z := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
      obtain ⟨z, hz⟩ := ih
      refine ⟨z + if branch n then 1 else -1, ?_⟩
      rw [AdditivePath.displacement_succ, hz]
      cases h : branch n <;>
        simp [rademacherIncrementPath, rademacherOfBool, h]

private theorem adjacent_integer_steps_same_weak_sign (z : ℤ) (step : Bool) :
    ((0 : ℤ) ≤ z ∧ 0 ≤ z + (if step then 1 else -1)) ∨
      (z ≤ 0 ∧ z + (if step then 1 else -1) ≤ 0) := by
  cases step <;> simp_all <;> omega

/-- Two consecutive integer partial sums of a nearest-neighbor walk
cannot have opposite strict signs. -/
theorem rademacher_signStableFrom_penultimate (branch : ℕ → Bool)
    {n : ℕ} (hn : 0 < n) :
    SignStableFrom n (n - 1) (rademacherIncrementPath branch) := by
  obtain ⟨z, hz⟩ := rademacher_displacement_int branch (n - 1)
  have hsucc : (n - 1) + 1 = n := by omega
  have hnval : AdditivePath.displacement n (rademacherIncrementPath branch) =
      (z + if branch (n - 1) then 1 else -1 : ℤ) := by
    conv_lhs => rw [← hsucc, AdditivePath.displacement_succ, hz]
    cases h : branch (n - 1) <;>
      simp [rademacherIncrementPath, rademacherOfBool, h]
  rcases adjacent_integer_steps_same_weak_sign z (branch (n - 1)) with h | h
  · left
    intro j hjleft hjright
    have hj : j = n - 1 ∨ j = n := by omega
    rcases hj with rfl | rfl
    · rw [hz]
      exact_mod_cast h.1
    · rw [hnval]
      exact_mod_cast h.2
  · right
    intro j hjleft hjright
    have hj : j = n - 1 ∨ j = n := by omega
    rcases hj with rfl | rfl
    · rw [hz]
      exact_mod_cast h.1
    · rw [hnval]
      exact_mod_cast h.2

/-- The terminal one-sided part of a simple symmetric walk has at
least one increment, as observed by Bolthausen on page 484. -/
theorem rademacher_terminalSignStableLength_pos (branch : ℕ → Bool)
    {n : ℕ} (hn : 0 < n) :
    0 < terminalSignStableLength n (rademacherIncrementPath branch) := by
  have hle : lastSignChangeIndex n (rademacherIncrementPath branch) ≤ n - 1 := by
    classical
    unfold lastSignChangeIndex
    exact Nat.find_min' (show ∃ j : ℕ,
      SignStableFrom n j (rademacherIncrementPath branch) from
        ⟨n, signStableFrom_self n (rademacherIncrementPath branch)⟩)
      (rademacher_signStableFrom_penultimate branch hn)
  unfold terminalSignStableLength
  omega

/-- The selected last-sign-change segment starts at a zero of the
simple symmetric walk. -/
theorem rademacher_displacement_lastSignChange_eq_zero
    (branch : ℕ → Bool) (n : ℕ) :
    AdditivePath.displacement
      (lastSignChangeIndex n (rademacherIncrementPath branch))
      (rademacherIncrementPath branch) = 0 := by
  let m := lastSignChangeIndex n (rademacherIncrementPath branch)
  by_cases hm : m = 0
  · simp [m, hm]
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hmle : m ≤ n := lastSignChangeIndex_le n (rademacherIncrementPath branch)
  have hnotprev : ¬ SignStableFrom n (m - 1)
      (rademacherIncrementPath branch) :=
    not_signStableFrom_before_lastSignChangeIndex n
      (rademacherIncrementPath branch) (by change m - 1 < m; omega)
  obtain ⟨z, hz⟩ := rademacher_displacement_int branch (m - 1)
  have hsucc : (m - 1) + 1 = m := by omega
  have hmval : AdditivePath.displacement m (rademacherIncrementPath branch) =
      (z + if branch (m - 1) then 1 else -1 : ℤ) := by
    conv_lhs => rw [← hsucc, AdditivePath.displacement_succ, hz]
    cases h : branch (m - 1) <;>
      simp [rademacherIncrementPath, rademacherOfBool, h]
  have hstable : SignStableFrom n m (rademacherIncrementPath branch) :=
    signStableFrom_lastSignChangeIndex n (rademacherIncrementPath branch)
  change AdditivePath.displacement m (rademacherIncrementPath branch) = 0
  rcases hstable with hnonneg | hnonpos
  · have hmnonneg := hnonneg m le_rfl hmle
    have hprevneg : AdditivePath.displacement (m - 1)
        (rademacherIncrementPath branch) < 0 := by
      by_contra h
      have hprev : 0 ≤ AdditivePath.displacement (m - 1)
          (rademacherIncrementPath branch) := le_of_not_gt h
      apply hnotprev
      left
      intro j hj hjn
      by_cases hjprev : j = m - 1
      · simpa [hjprev] using hprev
      · exact hnonneg j (by omega) hjn
    rw [hz] at hprevneg
    rw [hmval] at hmnonneg
    have hzneg : z < 0 := by exact_mod_cast hprevneg
    have hznonneg : (0 : ℤ) ≤ z + (if branch (m - 1) then 1 else -1) := by
      exact_mod_cast hmnonneg
    have hz0 : z + (if branch (m - 1) then 1 else -1) = 0 := by
      cases h : branch (m - 1) <;> simp only [h, ↓reduceIte] at hznonneg ⊢ <;> omega
    rw [hmval]
    exact_mod_cast hz0
  · have hmnonpos := hnonpos m le_rfl hmle
    have hprevpos : 0 < AdditivePath.displacement (m - 1)
        (rademacherIncrementPath branch) := by
      by_contra h
      have hprev : AdditivePath.displacement (m - 1)
          (rademacherIncrementPath branch) ≤ 0 := le_of_not_gt h
      apply hnotprev
      right
      intro j hj hjn
      by_cases hjprev : j = m - 1
      · simpa [hjprev] using hprev
      · exact hnonpos j (by omega) hjn
    rw [hz] at hprevpos
    rw [hmval] at hmnonpos
    have hzpos : 0 < z := by exact_mod_cast hprevpos
    have hznonpos : z + (if branch (m - 1) then 1 else -1) ≤ (0 : ℤ) := by
      exact_mod_cast hmnonpos
    have hz0 : z + (if branch (m - 1) then 1 else -1) = 0 := by
      cases h : branch (m - 1) <;> simp only [h, ↓reduceIte] at hznonpos ⊢ <;> omega
    rw [hmval]
    exact_mod_cast hz0

/-- Bolthausen's nonnegative polygonal interpolation of the last
one-sided segment of the simple symmetric walk. -/
noncomputable def rademacherTerminalAbsolutePath
    (branch : ℕ → Bool) (n : ℕ) : C(unitInterval, ℝ) where
  toFun t :=
    |normalizedLinearContinuousPathIcc
      (fun j => Real.sqrt j)
      (terminalSignStableLength n (rademacherIncrementPath branch))
      (fun j => rademacherIncrementPath branch
        (lastSignChangeIndex n (rademacherIncrementPath branch) + j)) t|
  continuous_toFun := by
    apply continuous_abs.comp
    exact (normalizedLinearContinuousPathIcc
      (fun j => Real.sqrt j)
      (terminalSignStableLength n (rademacherIncrementPath branch))
      (fun j => rademacherIncrementPath branch
        (lastSignChangeIndex n (rademacherIncrementPath branch) + j))).continuous

/-- At every grid point, the transformed path is the normalized
absolute value of the original partial sum after the last sign change. -/
theorem rademacherTerminalAbsolutePath_grid
    (branch : ℕ → Bool) {n k : ℕ} (hn : 0 < n)
    (hk : k ≤ terminalSignStableLength n (rademacherIncrementPath branch))
    (t : unitInterval)
    (ht : (t : ℝ) =
      (k : ℝ) / terminalSignStableLength n (rademacherIncrementPath branch)) :
    rademacherTerminalAbsolutePath branch n t =
      |(Real.sqrt (terminalSignStableLength n
        (rademacherIncrementPath branch) : ℝ))⁻¹ *
        AdditivePath.displacement
          (lastSignChangeIndex n (rademacherIncrementPath branch) + k)
          (rademacherIncrementPath branch)| := by
  let μ := lastSignChangeIndex n (rademacherIncrementPath branch)
  let ν := terminalSignStableLength n (rademacherIncrementPath branch)
  have hν : 0 < ν := rademacher_terminalSignStableLength_pos branch hn
  have hzero : AdditivePath.displacement μ (rademacherIncrementPath branch) = 0 :=
    rademacher_displacement_lastSignChange_eq_zero branch n
  change |normalizedLinearContinuousPathIcc
      (fun j => Real.sqrt j) ν
      (fun j => rademacherIncrementPath branch (μ + j)) t| = _
  rw [normalizedLinearContinuousPathIcc_apply, ht,
    normalizedLinearPath_grid (fun j => Real.sqrt j) hν hk]
  rw [AdditivePath.displacement_add μ k (rademacherIncrementPath branch), hzero]
  simp only [zero_add, ν]

end ProbabilityTheory.RandomWalk

end
