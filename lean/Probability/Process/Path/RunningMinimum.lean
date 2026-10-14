/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Continuous
public import Probability.Process.Path.FirstPassage

/-!
# Running minimum of a continuous path

The public definitions and theorems in this file are:

- `ProbabilityTheory.runningMinimum`: $m_f(t)=\min_{0\le u\le t}f(u)$.
- `ProbabilityTheory.exists_runningMinimum_eq`: the minimum is attained.
- `ProbabilityTheory.runningMinimum_le`: $m_f(t)\le f(u)$ for $u\le t$.
- `ProbabilityTheory.runningMinimum_antitone`: $m_f$ is antitone.
- `ProbabilityTheory.runningMinimum_le_iff_firstPassageBelow_le`:
  $m_f(t)\le a$ exactly when first passage below $a$ occurs by $t$.
- `ProbabilityTheory.measurableSet_runningMinimum_lt_zero`:
  $\{f:m_f(t)<0\}$ is measurable on continuous path space.
- `ProbabilityTheory.runningMinimum_eq_of_between`: if
  $m_f(t+1)=m_f(t)$, then $m_f(t+u)=m_f(t)$ for $0\le u\le1$.
- `ProbabilityTheory.aboveRunningMinimum`: $D_f(t)=f(t)-m_f(t)$.
- `ProbabilityTheory.aboveRunningMinimum_eq_zero_iff`:
  $D_f(t)=0$ exactly when $f(t)=m_f(t)$.

These continuous-path facts supply the running-minimum step in the proof of
Lemma 2.3 of Erwin Bolthausen, *On a functional central limit theorem for
random walks conditioned to stay positive*, Ann. Probab. 4(3) (1976),
480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open scoped NNReal

namespace ProbabilityTheory

/-- The minimum of a continuous path on the time interval $[0,t]$. -/
noncomputable def runningMinimum (f : C(ℝ≥0, ℝ)) (t : ℝ≥0) : ℝ :=
  sInf (f '' Set.Icc 0 t)

/-- A continuous path attains its running minimum. -/
theorem exists_runningMinimum_eq (f : C(ℝ≥0, ℝ)) (t : ℝ≥0) :
    ∃ u ∈ Set.Icc (0 : ℝ≥0) t, f u = runningMinimum f t := by
  have hne : (Set.Icc (0 : ℝ≥0) t).Nonempty :=
    ⟨0, bot_le, bot_le⟩
  obtain ⟨u, hu, hmin⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) t)).exists_isMinOn
      hne f.continuous.continuousOn
  have hcompact : IsCompact (f '' Set.Icc (0 : ℝ≥0) t) :=
    isCompact_Icc.image f.continuous
  have himage : (f '' Set.Icc (0 : ℝ≥0) t).Nonempty :=
    ⟨f 0, 0, ⟨bot_le, bot_le⟩, rfl⟩
  have hvalue : f u = sInf (f '' Set.Icc (0 : ℝ≥0) t) := by
    apply le_antisymm
    · apply le_csInf himage
      rintro v ⟨w, hw, rfl⟩
      exact hmin hw
    · exact csInf_le hcompact.bddBelow ⟨u, hu, rfl⟩
  exact ⟨u, hu, hvalue⟩

/-- The running minimum bounds every path value up to the same time. -/
theorem runningMinimum_le (f : C(ℝ≥0, ℝ)) {u t : ℝ≥0}
    (hut : u ≤ t) : runningMinimum f t ≤ f u := by
  have hcompact : IsCompact (f '' Set.Icc (0 : ℝ≥0) t) :=
    isCompact_Icc.image f.continuous
  exact csInf_le hcompact.bddBelow ⟨u, ⟨bot_le, hut⟩, rfl⟩

/-- The running minimum decreases as the time interval grows. -/
theorem runningMinimum_antitone (f : C(ℝ≥0, ℝ)) :
    Antitone (runningMinimum f) := by
  intro s t hst
  obtain ⟨u, hu, hmin⟩ := exists_runningMinimum_eq f s
  calc
    runningMinimum f t ≤ f u := runningMinimum_le f (hu.2.trans hst)
    _ = runningMinimum f s := hmin

/-- A path's running minimum is at most `a` by time `t` exactly when
its first passage below `a` occurs by `t`. -/
theorem runningMinimum_le_iff_firstPassageBelow_le
    (f : C(ℝ≥0, ℝ)) (t : ℝ≥0) (a : ℝ) :
    runningMinimum f t ≤ a ↔ firstPassageBelow f a ≤ t := by
  rw [firstPassageBelow_le_iff]
  constructor
  · intro hmin
    obtain ⟨u, hu, hvalue⟩ := exists_runningMinimum_eq f t
    exact ⟨u, hu.2, hvalue.le.trans hmin⟩
  · rintro ⟨u, hu, hvalue⟩
    exact (runningMinimum_le f hu).trans hvalue

/-- Strict negativity of the running minimum is a measurable path event.
It is the union of the closed negative-level passage events. -/
theorem measurableSet_runningMinimum_lt_zero (t : ℝ≥0) :
    MeasurableSet {f : C(ℝ≥0, ℝ) | runningMinimum f t < 0} := by
  let level : ℕ → ℝ := fun n => -(1 / (n + 1 : ℝ))
  have hset : {f : C(ℝ≥0, ℝ) | runningMinimum f t < 0} =
      ⋃ n, {f | runningMinimum f t ≤ level n} := by
    ext f
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hf
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.mpr hf)
      refine ⟨n, ?_⟩
      dsimp [level]
      linarith
    · rintro ⟨n, hn⟩
      have hlevel : level n < 0 := by
        dsimp [level]
        exact neg_neg_of_pos (by positivity)
      exact hn.trans_lt hlevel
  rw [hset]
  apply MeasurableSet.iUnion
  intro n
  have hfirst : MeasurableSet {f : C(ℝ≥0, ℝ) |
      firstPassageBelow f (level n) ≤ (t : WithTop ℝ≥0)} :=
    (measurable_firstPassageBelow _) measurableSet_Iic
  convert hfirst using 1
  ext f
  exact runningMinimum_le_iff_firstPassageBelow_le f t _

/-- A running minimum constant over a unit interval is constant at each
intermediate time. -/
theorem runningMinimum_eq_of_between (f : C(ℝ≥0, ℝ)) {t : ℝ≥0}
    (hflat : runningMinimum f (t + 1) = runningMinimum f t)
    {u : ℝ≥0} (hu : u ≤ 1) :
    runningMinimum f (t + u) = runningMinimum f t := by
  apply le_antisymm
  · exact runningMinimum_antitone f (le_add_of_nonneg_right u.property)
  · rw [← hflat]
    exact runningMinimum_antitone f (add_le_add_right hu t)

/-- The height of a continuous path above its running minimum. -/
noncomputable def aboveRunningMinimum (f : C(ℝ≥0, ℝ)) (t : ℝ≥0) : ℝ :=
  f t - runningMinimum f t

/-- The height above the running minimum vanishes precisely at a
running-minimum time. -/
theorem aboveRunningMinimum_eq_zero_iff (f : C(ℝ≥0, ℝ)) (t : ℝ≥0) :
    aboveRunningMinimum f t = 0 ↔ f t = runningMinimum f t := by
  simp [aboveRunningMinimum, sub_eq_zero]

end ProbabilityTheory
