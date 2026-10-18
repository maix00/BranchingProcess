/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Representation.Continuous
public import Probability.Process.Path.FirstPassage.Basic

/-!
# Running minimum of a continuous path

The public definitions and theorems in this file are:

- `ProbabilityTheory.runningMinimum`: $m_f(t)=\min_{0\le u\le t}f(u)$.
- `ProbabilityTheory.exists_runningMinimum_eq`: the minimum is attained.
- `ProbabilityTheory.runningMinimum_le`: $m_f(t)\le f(u)$ for $u\le t$.
- `ProbabilityTheory.runningMinimum_antitone`: $m_f$ is antitone.
- `ProbabilityTheory.runningMinimum_le_iff_firstPassageBelow_le`:
  $m_f(t)\le a$ exactly when first passage below $a$ occurs by $t$.
- `ProbabilityTheory.runningMinimum_eq_of_firstPassageBelow_eq`:
  when a continuous path first enters $(-\infty,a]$ at positive time
  $t$, its running minimum at $t$ equals $a$.
- `ProbabilityTheory.measurable_runningMinimum`:
  $f\mapsto m_f(t)$ is measurable on continuous path space.
- `ProbabilityTheory.measurable_firstPassageBelow_pair`:
  first passage is jointly measurable in the path and the level.
- `ProbabilityTheory.runningMinimum_freezeAfter_eq`:
  for $t\le r$, freezing the path after $r$ preserves $m_f(t)$.
- `ProbabilityTheory.runningMinimum_shiftToZero_eq_of_record`:
  a record value attained between $r$ and $q$ gives the minimum of
  the increment path on $[0,q-r]$.
- `ProbabilityTheory.measurableSet_runningMinimum_lt_zero`:
  $\{f:m_f(t)<0\}$ is measurable on continuous path space.
- `ProbabilityTheory.runningMinimum_eq_of_between`: if
  $m_f(t+1)=m_f(t)$, then $m_f(t+u)=m_f(t)$ for $0\le u\le1$.
- `ProbabilityTheory.aboveRunningMinimum`: $D_f(t)=f(t)-m_f(t)$.
- `ProbabilityTheory.aboveRunningMinimum_eq_zero_iff`:
  $D_f(t)=0$ exactly when $f(t)=m_f(t)$.

These continuous-path facts supply the running-minimum step in the proof of
Lemma 2.3 of Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976),
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

/-- At a positive first-passage time, the running minimum is the
level reached. -/
theorem runningMinimum_eq_of_firstPassageBelow_eq
    (f : C(ℝ≥0, ℝ)) (a : ℝ) {t : ℝ≥0} (ht : 0 < t)
    (hpass : firstPassageBelow f a = t) :
    runningMinimum f t = a := by
  have hhit : ∃ u : ℝ≥0, f u ≤ a := by
    by_contra h
    have htop : firstPassageBelow f a = ⊤ :=
      (firstPassageBelow_eq_top_iff f a).2
        (fun u => lt_of_not_ge (fun hu => h ⟨u, hu⟩))
    rw [hpass] at htop
    exact WithTop.coe_ne_top htop
  have hinf : (sInf {u : ℝ≥0 | f u ≤ a}) = t := by
    exact WithTop.coe_eq_coe.mp (by
      simpa [firstPassageBelow, firstPassageLE, hhit] using hpass)
  have h0 : a < f 0 := by
    apply firstPassageBelow_no_earlier f a hhit
    rw [hinf]
    exact ht
  have hvalue : f t = a := by
    rw [← hinf]
    exact firstPassageBelow_value_eq f a h0 hhit
  obtain ⟨u, hu, hmin⟩ := exists_runningMinimum_eq f t
  have hge : a ≤ runningMinimum f t := by
    rw [← hmin]
    by_cases hut : u < t
    · have hearly := firstPassageBelow_no_earlier f a hhit
        (show u < sInf {v : ℝ≥0 | f v ≤ a} by rw [hinf]; exact hut)
      exact hearly.le
    · have hueq : u = t := le_antisymm hu.2 (le_of_not_gt hut)
      rw [hueq, hvalue]
  exact le_antisymm (by simpa [hvalue] using runningMinimum_le f (le_refl t)) hge

/-- Evaluation of the running minimum at a fixed time is measurable.
Its closed sublevel sets are closed-level first-passage events. -/
theorem measurable_runningMinimum (t : ℝ≥0) :
    Measurable (fun f : C(ℝ≥0, ℝ) => runningMinimum f t) := by
  apply measurable_of_Iic
  intro a
  have hset : {f : C(ℝ≥0, ℝ) | runningMinimum f t ≤ a} =
      {f | firstPassageBelow f a ≤ (t : WithTop ℝ≥0)} := by
    ext f
    exact runningMinimum_le_iff_firstPassageBelow_le f t a
  rw [show (fun f : C(ℝ≥0, ℝ) => runningMinimum f t) ⁻¹' Set.Iic a =
    {f | runningMinimum f t ≤ a} from rfl, hset]
  exact (measurable_firstPassageBelow a) measurableSet_Iic

/-- First passage below a level is jointly measurable in the path and
the level. -/
theorem measurable_firstPassageBelow_pair :
    Measurable (fun p : C(ℝ≥0, ℝ) × ℝ =>
      firstPassageBelow p.1 p.2) := by
  apply measurable_of_Iic
  intro t
  by_cases ht : t = ⊤
  · subst t
    simp
  · obtain ⟨u, rfl⟩ := WithTop.ne_top_iff_exists.mp ht
    have hset :
        (fun p : C(ℝ≥0, ℝ) × ℝ => firstPassageBelow p.1 p.2) ⁻¹'
          Set.Iic (u : WithTop ℝ≥0) =
        {p | runningMinimum p.1 u ≤ p.2} := by
      ext p
      exact (runningMinimum_le_iff_firstPassageBelow_le p.1 u p.2).symm
    rw [hset]
    exact measurableSet_le
      ((measurable_runningMinimum u).comp measurable_fst) measurable_snd

/-- Freezing a path after `r` preserves its running minimum at times
up to `r`. -/
theorem runningMinimum_freezeAfter_eq (f : C(ℝ≥0, ℝ))
    {t r : ℝ≥0} (htr : t ≤ r) :
    runningMinimum (freezeAfter f r) t = runningMinimum f t := by
  unfold runningMinimum
  congr 1
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    simp [freezeAfter, min_eq_left (hu.2.trans htr)]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    simp [freezeAfter, min_eq_left (hu.2.trans htr)]

/-- If the running minimum stays constant from `r` to `q` and is
attained at `v` in this interval, the minimum of the increments from
`r` is the previous minimum minus the value at `r`. -/
theorem runningMinimum_shiftToZero_eq_of_record (f : C(ℝ≥0, ℝ))
    {r v q : ℝ≥0} (hrv : r ≤ v) (hvq : v ≤ q)
    (hflat : runningMinimum f q = runningMinimum f r)
    (hrecord : f v = runningMinimum f r) :
    runningMinimum (shiftToZero f r) (q - r) =
      runningMinimum f r - f r := by
  have hrq : r ≤ q := hrv.trans hvq
  apply le_antisymm
  · have hv : v - r ≤ q - r := tsub_le_tsub_right hvq r
    have hle := runningMinimum_le (shiftToZero f r) hv
    have hrv' : r + (v - r) = v := add_tsub_cancel_of_le hrv
    simpa [shiftToZero, hrv', hrecord] using hle
  · obtain ⟨u, hu, hmin⟩ :=
      exists_runningMinimum_eq (shiftToZero f r) (q - r)
    have hruq : r + u ≤ q := by
      calc
        r + u ≤ r + (q - r) := by simpa [add_comm] using add_le_add_left hu.2 r
        _ = q := add_tsub_cancel_of_le hrq
    have hle := runningMinimum_le f hruq
    rw [hflat] at hle
    rw [← hmin]
    change runningMinimum f r - f r ≤ f (r + u) - f r
    linarith
/-- Strict negativity of the running minimum is a measurable path event.
It is the union of the closed negative-level passage events. -/
theorem measurableSet_runningMinimum_lt_zero (t : ℝ≥0) :
    MeasurableSet {f : C(ℝ≥0, ℝ) | runningMinimum f t < 0} := by
  exact (measurable_runningMinimum t) measurableSet_Iio

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
