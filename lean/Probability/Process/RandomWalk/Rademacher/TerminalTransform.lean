/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Rademacher.LastSignChange
public import Probability.Process.RandomWalk.Path.Interpolation
public import Topology.ContinuousMap.LastSignChange

/-!
# Bolthausen's sign-stable tail time of a simple symmetric walk

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.rademacher_firstSignStableStart_eq_lastSignChangeIndex`:
  for $n>0$, the first sign-stable time of the normalized polygonal
  path is $\tau'(X_n)=\mu_n/n$.
- `ProbabilityTheory.RandomWalk.rademacher_signStableMeanderTransform_eq_terminalAbsolutePath`:
  $\Psi(X_n)=\widetilde Y_n$ as continuous paths.
- `ProbabilityTheory.RandomWalk.measurable_rademacherTerminalAbsolutePath`:
  for $n>0$, the map $\omega\mapsto\widetilde Y_n(\omega)$ is Borel measurable.

This is the discrete path identification used on page 484 of Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned
to stay positive*, Ann. Probab. 4(3) (1976), 480--485.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

private theorem negativePolygonalValues_before_return
    (branch : ℕ → Bool) {n m : ℕ}
    (hn : 0 < n) (hmpos : 0 < m) (hmle : m ≤ n)
    (hzero : AdditivePath.displacement m
      (rademacherIncrementPath branch) = 0)
    (hprevious : AdditivePath.displacement (m - 1)
      (rademacherIncrementPath branch) < 0)
    (t : unitInterval) (ht : (t : ℝ) < (m : ℝ) / n) :
    ∃ s : unitInterval, t ≤ s ∧ (s : ℝ) < (m : ℝ) / n ∧
      normalizedLinearContinuousPathIcc
        (fun j => Real.sqrt j) n (rademacherIncrementPath branch) s < 0 := by
  let cut : unitInterval := ⟨(m : ℝ) / n, by
    constructor
    · positivity
    · apply (div_le_one (by exact_mod_cast hn)).2
      exact_mod_cast hmle⟩
  let previous : unitInterval := ⟨((m - 1 : ℕ) : ℝ) / n, by
    constructor
    · positivity
    · apply (div_le_one (by exact_mod_cast hn)).2
      exact_mod_cast (by omega : m - 1 ≤ n)⟩
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hpreviousCut : previous < cut := by
    change ((m - 1 : ℕ) : ℝ) / n < (m : ℝ) / n
    apply div_lt_div_of_pos_right _ hnreal
    exact_mod_cast (by omega : m - 1 < m)
  have htCut : t < cut := ht
  have hbelow : max t previous < cut := max_lt htCut hpreviousCut
  obtain ⟨s, hmax, hcut⟩ := exists_between hbelow
  have hprevs : previous ≤ s := (le_max_right _ _).trans hmax.le
  have hts : t ≤ s := (le_max_left _ _).trans hmax.le
  have hleft : ((m - 1 : ℕ) : ℝ) ≤ (n : ℝ) * (s : ℝ) := by
    have hs : ((m - 1 : ℕ) : ℝ) / n ≤ (s : ℝ) := hprevs
    exact (div_le_iff₀ hnreal).mp hs |>.trans_eq (mul_comm _ _)
  have hrightStrict : (n : ℝ) * (s : ℝ) < (m : ℝ) := by
    have hs : (s : ℝ) < (m : ℝ) / n := hcut
    simpa only [mul_comm] using (lt_div_iff₀ hnreal).mp hs
  have hright : (n : ℝ) * (s : ℝ) ≤ ((m - 1 + 1 : ℕ) : ℝ) := by
    simpa [Nat.sub_add_cancel hmpos] using hrightStrict.le
  have hmminus : m - 1 < n := by omega
  have hzero' : AdditivePath.displacement (m - 1 + 1)
      (rademacherIncrementPath branch) = 0 := by
    simpa [Nat.sub_add_cancel hmpos] using hzero
  have hformula := normalizedLinearPath_before_zero
    (fun j => Real.sqrt j) hmminus (rademacherIncrementPath branch)
    hzero' (s : ℝ) hleft hright
  have hfactor : 0 < 1 - ((n : ℝ) * (s : ℝ) - (m - 1 : ℕ)) := by
    have hcast : ((m - 1 + 1 : ℕ) : ℝ) = (m : ℝ) := by
      simp [Nat.sub_add_cancel hmpos]
    push_cast at hcast
    nlinarith
  have hsqrt : 0 < (Real.sqrt (n : ℝ))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.2 hnreal)
  refine ⟨s, hts, hcut, ?_⟩
  rw [normalizedLinearContinuousPathIcc_apply, hformula]
  exact mul_neg_of_pos_of_neg
    (mul_pos hsqrt hfactor) hprevious

private theorem positivePolygonalValues_before_return
    (branch : ℕ → Bool) {n m : ℕ}
    (hn : 0 < n) (hmpos : 0 < m) (hmle : m ≤ n)
    (hzero : AdditivePath.displacement m
      (rademacherIncrementPath branch) = 0)
    (hprevious : 0 < AdditivePath.displacement (m - 1)
      (rademacherIncrementPath branch))
    (t : unitInterval) (ht : (t : ℝ) < (m : ℝ) / n) :
    ∃ s : unitInterval, t ≤ s ∧ (s : ℝ) < (m : ℝ) / n ∧
      0 < normalizedLinearContinuousPathIcc
        (fun j => Real.sqrt j) n (rademacherIncrementPath branch) s := by
  let cut : unitInterval := ⟨(m : ℝ) / n, by
    constructor
    · positivity
    · apply (div_le_one (by exact_mod_cast hn)).2
      exact_mod_cast hmle⟩
  let previous : unitInterval := ⟨((m - 1 : ℕ) : ℝ) / n, by
    constructor
    · positivity
    · apply (div_le_one (by exact_mod_cast hn)).2
      exact_mod_cast (by omega : m - 1 ≤ n)⟩
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hpreviousCut : previous < cut := by
    change ((m - 1 : ℕ) : ℝ) / n < (m : ℝ) / n
    apply div_lt_div_of_pos_right _ hnreal
    exact_mod_cast (by omega : m - 1 < m)
  have htCut : t < cut := ht
  have hbelow : max t previous < cut := max_lt htCut hpreviousCut
  obtain ⟨s, hmax, hcut⟩ := exists_between hbelow
  have hprevs : previous ≤ s := (le_max_right _ _).trans hmax.le
  have hts : t ≤ s := (le_max_left _ _).trans hmax.le
  have hleft : ((m - 1 : ℕ) : ℝ) ≤ (n : ℝ) * (s : ℝ) := by
    have hs : ((m - 1 : ℕ) : ℝ) / n ≤ (s : ℝ) := hprevs
    exact (div_le_iff₀ hnreal).mp hs |>.trans_eq (mul_comm _ _)
  have hrightStrict : (n : ℝ) * (s : ℝ) < (m : ℝ) := by
    have hs : (s : ℝ) < (m : ℝ) / n := hcut
    simpa only [mul_comm] using (lt_div_iff₀ hnreal).mp hs
  have hright : (n : ℝ) * (s : ℝ) ≤ ((m - 1 + 1 : ℕ) : ℝ) := by
    simpa [Nat.sub_add_cancel hmpos] using hrightStrict.le
  have hmminus : m - 1 < n := by omega
  have hzero' : AdditivePath.displacement (m - 1 + 1)
      (rademacherIncrementPath branch) = 0 := by
    simpa [Nat.sub_add_cancel hmpos] using hzero
  have hformula := normalizedLinearPath_before_zero
    (fun j => Real.sqrt j) hmminus (rademacherIncrementPath branch)
    hzero' (s : ℝ) hleft hright
  have hfactor : 0 < 1 - ((n : ℝ) * (s : ℝ) - (m - 1 : ℕ)) := by
    have hcast : ((m - 1 + 1 : ℕ) : ℝ) = (m : ℝ) := by
      simp [Nat.sub_add_cancel hmpos]
    push_cast at hcast
    nlinarith
  have hsqrt : 0 < (Real.sqrt (n : ℝ))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.2 hnreal)
  refine ⟨s, hts, hcut, ?_⟩
  rw [normalizedLinearContinuousPathIcc_apply, hformula]
  exact mul_pos (mul_pos hsqrt hfactor) hprevious

private theorem normalizedPolygonalValue_after_return_ne_zero
    (branch : ℕ → Bool) {n m : ℕ}
    (hn : 0 < n) (hm : m < n)
    (hzero : AdditivePath.displacement m
      (rademacherIncrementPath branch) = 0) :
    ∃ s : unitInterval,
      (s : ℝ) = ((m + 1 : ℕ) : ℝ) / n ∧
      normalizedLinearContinuousPathIcc
        (fun j => Real.sqrt j) n (rademacherIncrementPath branch) s ≠ 0 := by
  let s : unitInterval := ⟨((m + 1 : ℕ) : ℝ) / n, by
    constructor
    · positivity
    · apply (div_le_one (by exact_mod_cast hn)).2
      exact_mod_cast (by omega : m + 1 ≤ n)⟩
  refine ⟨s, rfl, ?_⟩
  rw [normalizedLinearContinuousPathIcc_apply,
    normalizedLinearPath_grid (fun j => Real.sqrt j) hn
      (by omega : m + 1 ≤ n)]
  rw [AdditivePath.displacement_succ, hzero, zero_add]
  have hsqrt : (Real.sqrt (n : ℝ))⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn))
  apply mul_ne_zero hsqrt
  cases h : branch m <;>
    norm_num [rademacherIncrementPath, rademacherOfBool, h]

/-- For a simple symmetric polygonal walk, Bolthausen's first
sign-stable tail begins at the interpolated last-sign-change index:
$\tau'(X_n)=\mu_n/n$. -/
theorem rademacher_firstSignStableStart_eq_lastSignChangeIndex
    (branch : ℕ → Bool) {n : ℕ} (hn : 0 < n) :
    ContinuousMap.firstSignStableStart
      (normalizedLinearContinuousPathIcc
        (fun j => Real.sqrt j) n (rademacherIncrementPath branch)) =
      ⟨(lastSignChangeIndex n
        (rademacherIncrementPath branch) : ℝ) / n, by
        constructor
        · positivity
        · apply (div_le_one (by exact_mod_cast hn)).2
          exact_mod_cast (lastSignChangeIndex_le n
            (rademacherIncrementPath branch))⟩ := by
  let μ := lastSignChangeIndex n (rademacherIncrementPath branch)
  let f := normalizedLinearContinuousPathIcc
    (fun j => Real.sqrt j) n (rademacherIncrementPath branch)
  let cut : unitInterval := ⟨(μ : ℝ) / n, by
    constructor
    · positivity
    · apply (div_le_one (by exact_mod_cast hn)).2
      exact_mod_cast (lastSignChangeIndex_le n
        (rademacherIncrementPath branch))⟩
  change ContinuousMap.firstSignStableStart f = cut
  have hμlt : μ < n := by
    have h := rademacher_terminalSignStableLength_pos branch hn
    unfold terminalSignStableLength at h
    omega
  have hzero : AdditivePath.displacement μ
      (rademacherIncrementPath branch) = 0 :=
    rademacher_displacement_lastSignChange_eq_zero branch n
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨later, hlaterGrid, hlaterNe⟩ :=
    normalizedPolygonalValue_after_return_ne_zero branch hn hμlt hzero
  have hcutlater : cut ≤ later := by
    change (μ : ℝ) / n ≤ (later : ℝ)
    rw [hlaterGrid]
    apply div_le_div_of_nonneg_right _ hnreal.le
    exact_mod_cast Nat.le_succ μ
  have hμle : μ ≤ n := lastSignChangeIndex_le n _
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnreal
  rcases signStableFrom_lastSignChangeIndex n
      (rademacherIncrementPath branch) with hpositive | hnegative
  · have hpost : ∀ s : unitInterval, cut ≤ s → 0 ≤ f s := by
      intro s hcuts
      have hs : (μ : ℝ) ≤ (n : ℝ) * (s : ℝ) := by
        have hs' : (μ : ℝ) / n ≤ (s : ℝ) := hcuts
        exact (div_le_iff₀ hnreal).mp hs' |>.trans_eq (mul_comm _ _)
      rw [normalizedLinearContinuousPathIcc_apply]
      exact normalizedLinearPath_nonneg_after_grid
        (fun j => Real.sqrt j) hn hsqrt hμle
        (rademacherIncrementPath branch)
        (fun j hμj hjn => hpositive j hμj hjn) s hs
    apply ContinuousMap.firstSignStableStart_eq_of_positiveTail f cut hpost
    · intro t htcut
      by_cases hμzero : μ = 0
      · have hcutzero : cut = ⊥ := by
          ext
          simp [cut, hμzero]
        rw [hcutzero] at htcut
        exact (not_lt_bot htcut).elim
      · exact negativePolygonalValues_before_return branch hn
          (Nat.pos_of_ne_zero hμzero) hμle hzero
          (previous_negative_of_nonnegative_terminal n
            (rademacherIncrementPath branch)
            (Nat.pos_of_ne_zero hμzero) hpositive) t htcut
    · exact ⟨later, hcutlater,
        lt_of_le_of_ne (hpost later hcutlater) (Ne.symm hlaterNe)⟩
  · have hpost : ∀ s : unitInterval, cut ≤ s → f s ≤ 0 := by
      intro s hcuts
      have hs : (μ : ℝ) ≤ (n : ℝ) * (s : ℝ) := by
        have hs' : (μ : ℝ) / n ≤ (s : ℝ) := hcuts
        exact (div_le_iff₀ hnreal).mp hs' |>.trans_eq (mul_comm _ _)
      rw [normalizedLinearContinuousPathIcc_apply]
      exact normalizedLinearPath_nonpos_after_grid
        (fun j => Real.sqrt j) hn hsqrt hμle
        (rademacherIncrementPath branch)
        (fun j hμj hjn => hnegative j hμj hjn) s hs
    apply ContinuousMap.firstSignStableStart_eq_of_negativeTail f cut hpost
    · intro t htcut
      by_cases hμzero : μ = 0
      · have hcutzero : cut = ⊥ := by
          ext
          simp [cut, hμzero]
        rw [hcutzero] at htcut
        exact (not_lt_bot htcut).elim
      · exact positivePolygonalValues_before_return branch hn
          (Nat.pos_of_ne_zero hμzero) hμle hzero
          (previous_positive_of_nonpositive_terminal n
            (rademacherIncrementPath branch)
            (Nat.pos_of_ne_zero hμzero) hnegative) t htcut
    · exact ⟨later, hcutlater,
        lt_of_le_of_ne (hpost later hcutlater) hlaterNe⟩

/-- Bolthausen's sign-stable transform of the normalized walk is its
normalized absolute terminal polygonal segment, pointwise on $[0,1]$. -/
theorem rademacher_signStableMeanderTransform_eq_terminalAbsolutePath
    (branch : ℕ → Bool) {n : ℕ} (hn : 0 < n) :
    ContinuousMap.signStableMeanderTransform
      (normalizedLinearContinuousPathIcc
        (fun j => Real.sqrt j) n (rademacherIncrementPath branch)) =
      rademacherTerminalAbsolutePath branch n := by
  let μ := lastSignChangeIndex n (rademacherIncrementPath branch)
  let ν := terminalSignStableLength n (rademacherIncrementPath branch)
  let cut : unitInterval := ⟨(μ : ℝ) / n, by
    constructor
    · positivity
    · apply (div_le_one (by exact_mod_cast hn)).2
      exact_mod_cast (lastSignChangeIndex_le n
        (rademacherIncrementPath branch))⟩
  have hμle : μ ≤ n := lastSignChangeIndex_le n _
  have hν : 0 < ν := rademacher_terminalSignStableLength_pos branch hn
  have hνeq : ν = n - μ := rfl
  have hzero : AdditivePath.displacement μ
      (rademacherIncrementPath branch) = 0 :=
    rademacher_displacement_lastSignChange_eq_zero branch n
  have hcut : ContinuousMap.firstSignStableStart
      (normalizedLinearContinuousPathIcc
        (fun j => Real.sqrt j) n (rademacherIncrementPath branch)) = cut :=
    rademacher_firstSignStableStart_eq_lastSignChangeIndex branch hn
  have hcutTop : cut ≠ ⊤ := by
    have hμlt : μ < n := by omega
    intro h
    have hreal : (μ : ℝ) / n = 1 := congrArg Subtype.val h
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hμreal : (μ : ℝ) < n := by exact_mod_cast hμlt
    have hlt : (μ : ℝ) / n < 1 :=
      (div_lt_one hnreal).mpr hμreal
    linarith
  ext t
  change (if ContinuousMap.firstSignStableStart
      (normalizedLinearContinuousPathIcc
        (fun j => Real.sqrt j) n (rademacherIncrementPath branch)) = ⊤
    then 0 else
      |normalizedLinearContinuousPathIcc
        (fun j => Real.sqrt j) n (rademacherIncrementPath branch)
          (ContinuousMap.tailAffineTime
            (ContinuousMap.firstSignStableStart
              (normalizedLinearContinuousPathIcc
                (fun j => Real.sqrt j) n (rademacherIncrementPath branch))) t)| /
        Real.sqrt (1 -
          (ContinuousMap.firstSignStableStart
            (normalizedLinearContinuousPathIcc
              (fun j => Real.sqrt j) n
              (rademacherIncrementPath branch)) : ℝ))) = _
  rw [hcut]
  simp only [hcutTop, ↓reduceIte]
  have htime : (ContinuousMap.tailAffineTime cut t : ℝ) =
      (μ : ℝ) / n + ((n - μ : ℕ) : ℝ) / n * (t : ℝ) := by
    change (μ : ℝ) / n + (1 - (μ : ℝ) / n) * (t : ℝ) = _
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hνcast : ((n - μ : ℕ) : ℝ) = (n : ℝ) - μ :=
      Nat.cast_sub hμle
    rw [hνcast]
    field_simp
  rw [normalizedLinearContinuousPathIcc_apply, htime,
    normalizedLinearPath_tail_after_zero
      (fun j => Real.sqrt j) hn hμle
      (rademacherIncrementPath branch) hzero t]
  change |(Real.sqrt (n : ℝ))⁻¹ *
      ∑ j ∈ Finset.range ν,
        linearIncrementWeight ν j (t : ℝ) *
          rademacherIncrementPath branch (μ + j)| /
        Real.sqrt (1 - (cut : ℝ)) =
      |normalizedLinearPath (fun j => Real.sqrt j) ν
        (fun j => rademacherIncrementPath branch (μ + j)) (t : ℝ)|
  have hratio : 1 - (cut : ℝ) = (ν : ℝ) / n := by
    change 1 - (μ : ℝ) / n = (ν : ℝ) / n
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hνcast : (ν : ℝ) = (n : ℝ) - μ := by
      change ((n - μ : ℕ) : ℝ) = _
      exact Nat.cast_sub hμle
    rw [hνcast]
    field_simp
  rw [hratio, Real.sqrt_div (Nat.cast_nonneg ν)]
  unfold normalizedLinearPath
  have hnroot : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hνroot : 0 < Real.sqrt (ν : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hν)
  rw [abs_mul, abs_mul, abs_inv, abs_inv,
    abs_of_pos hnroot, abs_of_pos hνroot]
  field_simp

/-- The terminal polygonal path of the simple symmetric walk is a
measurable continuous-path-valued random variable. This is the path
used on page 484 of Erwin Bolthausen, *On a functional central limit
theorem for random walks conditioned to stay positive*, Ann. Probab.
4(3) (1976), 480--485, DOI 10.1214/aop/1176996098. -/
theorem measurable_rademacherTerminalAbsolutePath
    {n : ℕ} (hn : 0 < n) :
    Measurable (fun branch => rademacherTerminalAbsolutePath branch n) := by
  have heq : (fun branch => rademacherTerminalAbsolutePath branch n) =
      fun branch => ContinuousMap.signStableMeanderTransform
        (normalizedLinearContinuousPathIcc
          (fun j => Real.sqrt j) n (rademacherIncrementPath branch)) := by
    funext branch
    exact (rademacher_signStableMeanderTransform_eq_terminalAbsolutePath
      branch hn).symm
  rw [heq]
  exact ContinuousMap.measurable_signStableMeanderTransform.comp
    ((measurable_normalizedLinearContinuousPathIcc _ _).comp
      measurable_rademacherIncrementPath)

end ProbabilityTheory.RandomWalk

end
