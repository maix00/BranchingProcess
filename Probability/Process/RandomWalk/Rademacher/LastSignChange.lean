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
- `ProbabilityTheory.RandomWalk.rademacher_lastSignChangeIndex_eq_iff_crossing`:
  for $0<m<n$, the event $\mu_n=m$ is the union of a negative-to-zero
  crossing followed by a nonnegative tail and its reflected counterpart.
- `ProbabilityTheory.RandomWalk.rademacher_normalizedPath_terminalSignStable`:
  the polygonal walk has one weak sign on the interval
  $[\mu_n/n,1]$.

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

private theorem first_branch_true_of_survival (branch : ℕ → Bool)
    {length : ℕ} (hlength : 0 < length)
    (h : SurvivesNonnegative length (rademacherIncrementPath branch)) :
    branch 0 = true := by
  have hfirst := h ⟨0, hlength⟩
  cases hzero : branch 0
  · simp [AdditivePath.displacement, rademacherIncrementPath,
      rademacherOfBool, hzero] at hfirst
    norm_num at hfirst
  · rfl

private theorem first_branch_false_of_reflectedSurvival (branch : ℕ → Bool)
    {length : ℕ} (hlength : 0 < length)
    (h : SurvivesNonnegative length
      (fun k => -rademacherIncrementPath branch k)) :
    branch 0 = false := by
  have hfirst := h ⟨0, hlength⟩
  cases hzero : branch 0
  · rfl
  · simp [AdditivePath.displacement, rademacherIncrementPath,
      rademacherOfBool, hzero] at hfirst
    norm_num at hfirst

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
        (rademacherIncrementPath branch) < 0 :=
      previous_negative_of_nonnegative_terminal n
        (rademacherIncrementPath branch) hmpos hnonneg
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
        (rademacherIncrementPath branch) :=
      previous_positive_of_nonpositive_terminal n
        (rademacherIncrementPath branch) hmpos hnonpos
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

private theorem lastSignChangeIndex_eq_of_positiveCrossing
    (branch : ℕ → Bool) (n start : ℕ) (hstart : 0 < start)
    (hbefore : start < n)
    (hprevious : AdditivePath.displacement (start - 1)
      (rademacherIncrementPath branch) < 0)
    (hzero : AdditivePath.displacement start
      (rademacherIncrementPath branch) = 0)
    (hsurvive : SurvivesNonnegative (n - start)
      (fun k => rademacherIncrementPath branch (start + k))) :
    lastSignChangeIndex n (rademacherIncrementPath branch) = start := by
  have htail := (nonnegativeTail_iff_shiftedSurvival n start
    (rademacherIncrementPath branch) (by omega) hzero).2 hsurvive
  have hfirst : branch start = true := by
    have hshift : (fun k => rademacherIncrementPath branch (start + k)) =
        rademacherIncrementPath (fun k => branch (start + k)) := by
      funext k
      rfl
    rw [hshift] at hsurvive
    have h := first_branch_true_of_survival (fun k => branch (start + k))
      (show 0 < n - start by omega)
      hsurvive
    simpa using h
  have hnext : 0 < AdditivePath.displacement (start + 1)
      (rademacherIncrementPath branch) := by
    rw [AdditivePath.displacement_succ, hzero]
    simp [rademacherIncrementPath, rademacherOfBool, hfirst]
  apply (lastSignChangeIndex_eq_iff n
    (rademacherIncrementPath branch) hstart).2
  refine ⟨Or.inl htail, ?_⟩
  intro hprev
  rcases hprev with hnonneg | hnonpos
  · have h := hnonneg (start - 1) le_rfl (by omega)
    linarith
  · have h := hnonpos (start + 1) (by omega) (by omega)
    linarith

private theorem lastSignChangeIndex_eq_of_negativeCrossing
    (branch : ℕ → Bool) (n start : ℕ) (hstart : 0 < start)
    (hbefore : start < n)
    (hprevious : 0 < AdditivePath.displacement (start - 1)
      (rademacherIncrementPath branch))
    (hzero : AdditivePath.displacement start
      (rademacherIncrementPath branch) = 0)
    (hsurvive : SurvivesNonnegative (n - start)
      (fun k => -rademacherIncrementPath branch (start + k))) :
    lastSignChangeIndex n (rademacherIncrementPath branch) = start := by
  have htail := (nonpositiveTail_iff_negShiftedSurvival n start
    (rademacherIncrementPath branch) (by omega) hzero).2 hsurvive
  have hfirst : branch start = false := by
    have hshift : (fun k => -rademacherIncrementPath branch (start + k)) =
        (fun k => -rademacherIncrementPath (fun i => branch (start + i)) k) := by
      funext k
      rfl
    rw [hshift] at hsurvive
    have h := first_branch_false_of_reflectedSurvival
      (fun k => branch (start + k)) (show 0 < n - start by omega) hsurvive
    simpa using h
  have hnext : AdditivePath.displacement (start + 1)
      (rademacherIncrementPath branch) < 0 := by
    rw [AdditivePath.displacement_succ, hzero]
    simp [rademacherIncrementPath, rademacherOfBool, hfirst]
  apply (lastSignChangeIndex_eq_iff n
    (rademacherIncrementPath branch) hstart).2
  refine ⟨Or.inr htail, ?_⟩
  intro hprev
  rcases hprev with hnonneg | hnonpos
  · have h := hnonneg (start + 1) (by omega) (by omega)
    linarith
  · have h := hnonpos (start - 1) le_rfl (by omega)
    linarith

/-- For a simple symmetric walk, fixing the last-sign-change time
splits the path into a crossing at zero and a one-sided terminal block.
The terminal block is described by its shifted increments. -/
theorem rademacher_lastSignChangeIndex_eq_iff_crossing
    (branch : ℕ → Bool) (n start : ℕ)
    (hstart : 0 < start) (hbefore : start < n) :
    lastSignChangeIndex n (rademacherIncrementPath branch) = start ↔
      (AdditivePath.displacement (start - 1)
          (rademacherIncrementPath branch) < 0 ∧
        AdditivePath.displacement start
          (rademacherIncrementPath branch) = 0 ∧
        SurvivesNonnegative (n - start)
          (fun k => rademacherIncrementPath branch (start + k))) ∨
      (0 < AdditivePath.displacement (start - 1)
          (rademacherIncrementPath branch) ∧
        AdditivePath.displacement start
          (rademacherIncrementPath branch) = 0 ∧
        SurvivesNonnegative (n - start)
          (fun k => -rademacherIncrementPath branch (start + k))) := by
  constructor
  · intro heq
    have hzero := rademacher_displacement_lastSignChange_eq_zero branch n
    rw [heq] at hzero
    rcases signStableFrom_lastSignChangeIndex n
        (rademacherIncrementPath branch) with hpositive | hnegative
    · have hprevious := previous_negative_of_nonnegative_terminal n
        (rademacherIncrementPath branch) (by rw [heq]; exact hstart) hpositive
      rw [heq] at hprevious
      have htail : ∀ j : ℕ, start ≤ j → j ≤ n →
          0 ≤ AdditivePath.displacement j
            (rademacherIncrementPath branch) := by
        simpa only [heq] using hpositive
      exact Or.inl ⟨hprevious, hzero,
        (nonnegativeTail_iff_shiftedSurvival n start
          (rademacherIncrementPath branch) (by omega) hzero).1 htail⟩
    · have hprevious := previous_positive_of_nonpositive_terminal n
        (rademacherIncrementPath branch) (by rw [heq]; exact hstart) hnegative
      rw [heq] at hprevious
      have htail : ∀ j : ℕ, start ≤ j → j ≤ n →
          AdditivePath.displacement j
            (rademacherIncrementPath branch) ≤ 0 := by
        simpa only [heq] using hnegative
      exact Or.inr ⟨hprevious, hzero,
        (nonpositiveTail_iff_negShiftedSurvival n start
          (rademacherIncrementPath branch) (by omega) hzero).1 htail⟩
  · rintro (⟨hprevious, hzero, hsurvive⟩ |
      ⟨hprevious, hzero, hsurvive⟩)
    · exact lastSignChangeIndex_eq_of_positiveCrossing branch n start
        hstart hbefore hprevious hzero hsurvive
    · exact lastSignChangeIndex_eq_of_negativeCrossing branch n start
        hstart hbefore hprevious hzero hsurvive

/-- The selected one-sided tail remains one-sided after polygonal
interpolation. -/
theorem rademacher_normalizedPath_terminalSignStable
    (branch : ℕ → Bool) (n : ℕ) (hn : 0 < n) :
    (∀ t : unitInterval,
        (lastSignChangeIndex n (rademacherIncrementPath branch) : ℝ) ≤
          (n : ℝ) * (t : ℝ) →
        0 ≤ normalizedLinearContinuousPathIcc
          (fun j => Real.sqrt j) n (rademacherIncrementPath branch) t) ∨
      (∀ t : unitInterval,
        (lastSignChangeIndex n (rademacherIncrementPath branch) : ℝ) ≤
          (n : ℝ) * (t : ℝ) →
        normalizedLinearContinuousPathIcc
          (fun j => Real.sqrt j) n (rademacherIncrementPath branch) t ≤ 0) := by
  let μ := lastSignChangeIndex n (rademacherIncrementPath branch)
  have hμle : μ ≤ n := lastSignChangeIndex_le n _
  have hsqrt : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hn)
  rcases signStableFrom_lastSignChangeIndex n
      (rademacherIncrementPath branch) with hpositive | hnegative
  · left
    intro t ht
    rw [normalizedLinearContinuousPathIcc_apply]
    exact normalizedLinearPath_nonneg_after_grid
      (fun j => Real.sqrt j) hn hsqrt hμle
      (rademacherIncrementPath branch)
      (fun j hμj hjn => hpositive j hμj hjn) t ht
  · right
    intro t ht
    rw [normalizedLinearContinuousPathIcc_apply]
    exact normalizedLinearPath_nonpos_after_grid
      (fun j => Real.sqrt j) hn hsqrt hμle
      (rademacherIncrementPath branch)
      (fun j hμj hjn => hnegative j hμj hjn) t ht

end ProbabilityTheory.RandomWalk

end
