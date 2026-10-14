/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Window.Continuous

/-!
# First windows and the running minimum of a continuous path

The public definitions and theorems in this file are:

- `ProbabilityTheory.runningMinimum`: $m_f(t)=\min_{0\le u\le t}f(u)$.
- `ProbabilityTheory.exists_runningMinimum_eq`: the minimum is attained.
- `ProbabilityTheory.runningMinimum_le`: $m_f(t)\le f(u)$ for $u\le t$.
- `ProbabilityTheory.runningMinimum_antitone`: $m_f$ is antitone.
- `ProbabilityTheory.runningMinimum_eq_of_between`: if
  $m_f(t+1)=m_f(t)$, then $m_f(t+u)=m_f(t)$ for $0\le u\le1$.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_runningMinimum`:
  if $T^s(f)=t<\infty$, then $f(t)=m_f(t)=m_f(t+1)$.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_eq_runningMinimum_iff`:
  for $0\le u\le1$ and $T^s(f)=t$, the equality $f(t+u)=f(t)$
  holds exactly when $f(t+u)=m_f(t+u)$.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_eq_coe_iff_runningMinimum`:
  $T^s(f)=t$ exactly when $t+1\le s$ and $t$ is the first time for
  which $m_f(t+1)=m_f(t)$.

The last equality is the deterministic observation at the beginning of the
proof of Lemma 2.3 in Erwin Bolthausen, *On a functional central limit
theorem for random walks conditioned to stay positive*, Ann. Probab. 4(3)
(1976), 480--485, DOI 10.1214/aop/1176996098.
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

private theorem earlier_nonnegativeWindowStart_of_runningMinimum_lt
    (f : C(ℝ≥0, ℝ)) {t : ℝ≥0}
    (ht : IsNonnegativeWindowStart f t)
    (hlt : runningMinimum f t < f t) :
    ∃ u < t, IsNonnegativeWindowStart f u := by
  obtain ⟨u, hu, hmin⟩ := exists_runningMinimum_eq f t
  have hut : u < t := by
    have hne : u ≠ t := by
      intro heq
      rw [heq] at hmin
      exact (lt_irrefl (f t)) (hmin ▸ hlt)
    exact hu.2.lt_of_ne hne
  refine ⟨u, hut, ?_⟩
  intro v
  by_cases huv : u + v ≤ t
  · calc
      f u = runningMinimum f t := hmin
      _ ≤ f (u + v) := runningMinimum_le f huv
  · have htv : t < u + v := lt_of_not_ge huv
    have huvt : u + v ≤ t + 1 := by
      calc
        u + v ≤ u + 1 := add_le_add_right v.property.2 u
        _ ≤ t + 1 := add_le_add_left hu.2 1
    let w : Set.Icc (0 : ℝ≥0) 1 :=
      ⟨u + v - t, bot_le, (tsub_le_iff_right).2 (by simpa [add_comm] using huvt)⟩
    have htw : t + w = u + v := add_tsub_cancel_of_le htv.le
    calc
      f u = runningMinimum f t := hmin
      _ ≤ f t := (runningMinimum_le f le_rfl)
      _ ≤ f (t + w) := ht w
      _ = f (u + v) := by rw [htw]

private theorem runningMinimum_add_one_eq_of_windowStart
    (f : C(ℝ≥0, ℝ)) {t : ℝ≥0}
    (ht : IsNonnegativeWindowStart f t)
    (hrecord : f t = runningMinimum f t) :
    runningMinimum f (t + 1) = runningMinimum f t := by
  apply le_antisymm
  · exact runningMinimum_antitone f (le_add_of_nonneg_right (by positivity))
  · obtain ⟨u, hu, hmin⟩ := exists_runningMinimum_eq f (t + 1)
    rw [← hmin]
    by_cases hut : u ≤ t
    · exact runningMinimum_le f hut
    · let v : Set.Icc (0 : ℝ≥0) 1 :=
        ⟨u - t, bot_le, (tsub_le_iff_right).2 (by simpa [add_comm] using hu.2)⟩
      have htv : t + v = u := add_tsub_cancel_of_le (lt_of_not_ge hut).le
      rw [← hrecord, ← htv]
      exact ht v

/-- The first length-one window begins at the running minimum, which
stays unchanged during that window. This is Bolthausen's deterministic
identity in the proof of Lemma 2.3. -/
theorem firstNonnegativeWindowStartUpTo_runningMinimum
    (f : C(ℝ≥0, ℝ)) (s t : ℝ≥0)
    (hfirst : firstNonnegativeWindowStartUpTo f s = t) :
    f t = runningMinimum f t ∧
      runningMinimum f (t + 1) = runningMinimum f t := by
  obtain ⟨_, ht, hleast⟩ :=
    (firstNonnegativeWindowStartUpTo_eq_coe_iff f s t).mp hfirst
  have hrecord : f t = runningMinimum f t := by
    apply le_antisymm
    · by_contra h
      have hlt : runningMinimum f t < f t := lt_of_not_ge h
      obtain ⟨u, hut, hu⟩ :=
        earlier_nonnegativeWindowStart_of_runningMinimum_lt f ht hlt
      have hus : u + 1 ≤ s := by
        exact (add_le_add_left hut.le 1).trans
          ((firstNonnegativeWindowStartUpTo_eq_coe_iff f s t).mp hfirst).1
      exact (not_le_of_gt hut) (hleast u hus hu)
    · exact runningMinimum_le f le_rfl
  exact ⟨hrecord, runningMinimum_add_one_eq_of_windowStart f ht hrecord⟩

/-- During the first eligible window, returning to its starting value is
equivalent to meeting the running minimum again. This is the path event
in Bolthausen's Lemma 2.3, equation (2.4). -/
theorem firstNonnegativeWindowStartUpTo_eq_runningMinimum_iff
    (f : C(ℝ≥0, ℝ)) (s t : ℝ≥0)
    (hfirst : firstNonnegativeWindowStartUpTo f s = t)
    {u : ℝ≥0} (hu : u ≤ 1) :
    f (t + u) = f t ↔ f (t + u) = runningMinimum f (t + u) := by
  obtain ⟨hrecord, hflat⟩ :=
    firstNonnegativeWindowStartUpTo_runningMinimum f s t hfirst
  rw [runningMinimum_eq_of_between f hflat hu, ← hrecord]

private theorem exists_nonnegativeWindowStart_le_of_runningMinimum_eq
    (f : C(ℝ≥0, ℝ)) {t : ℝ≥0}
    (hflat : runningMinimum f (t + 1) = runningMinimum f t) :
    ∃ u ≤ t, IsNonnegativeWindowStart f u := by
  obtain ⟨u, hu, hmin⟩ := exists_runningMinimum_eq f t
  refine ⟨u, hu.2, ?_⟩
  intro v
  have huv : u + v ≤ t + 1 := by
    calc
      u + v ≤ u + 1 := add_le_add_right v.property.2 u
      _ ≤ t + 1 := add_le_add_left hu.2 1
  calc
    f u = runningMinimum f t := hmin
    _ = runningMinimum f (t + 1) := hflat.symm
    _ ≤ f (u + v) := runningMinimum_le f huv

private theorem firstNonnegativeWindowStartUpTo_le_of_runningMinimum_eq
    (f : C(ℝ≥0, ℝ)) {s t : ℝ≥0}
    (hts : t + 1 ≤ s)
    (hflat : runningMinimum f (t + 1) = runningMinimum f t) :
    firstNonnegativeWindowStartUpTo f s ≤ t := by
  obtain ⟨u, hut, hu⟩ :=
    exists_nonnegativeWindowStart_le_of_runningMinimum_eq f hflat
  have hus : u + 1 ≤ s := (add_le_add_left hut 1).trans hts
  have hnonempty : ∃ r : ℝ≥0,
      r + 1 ≤ s ∧ IsNonnegativeWindowStart f r := ⟨u, hus, hu⟩
  have hfirst : firstNonnegativeWindowStartUpTo f s ≤ u := by
    simp only [firstNonnegativeWindowStartUpTo,
      dite_eq_left hnonempty, WithTop.coe_le_coe]
    exact csInf_le ⟨0, fun _ _ => bot_le⟩ ⟨hus, hu⟩
  exact hfirst.trans (WithTop.coe_le_coe.mpr hut)

/-- A finite first-window time is precisely the first flat unit interval
of the path's running minimum. This is the identity used by Bolthausen
at the start of the proof of Lemma 2.3. -/
theorem firstNonnegativeWindowStartUpTo_eq_coe_iff_runningMinimum
    (f : C(ℝ≥0, ℝ)) (s t : ℝ≥0) :
    firstNonnegativeWindowStartUpTo f s = t ↔
      t + 1 ≤ s ∧
        runningMinimum f (t + 1) = runningMinimum f t ∧
        ∀ u : ℝ≥0, u + 1 ≤ s →
          runningMinimum f (u + 1) = runningMinimum f u → t ≤ u := by
  constructor
  · intro hfirst
    obtain ⟨hts, _, _⟩ :=
      (firstNonnegativeWindowStartUpTo_eq_coe_iff f s t).mp hfirst
    have hflat := (firstNonnegativeWindowStartUpTo_runningMinimum f s t hfirst).2
    refine ⟨hts, hflat, ?_⟩
    intro u hus hu
    have hle : (t : WithTop ℝ≥0) ≤ u := by
      rw [← hfirst]
      exact firstNonnegativeWindowStartUpTo_le_of_runningMinimum_eq
        f hus hu
    exact WithTop.coe_le_coe.mp hle
  · rintro ⟨hts, hflat, hleast⟩
    have hle : firstNonnegativeWindowStartUpTo f s ≤ t :=
      firstNonnegativeWindowStartUpTo_le_of_runningMinimum_eq f hts hflat
    have hfinite : firstNonnegativeWindowStartUpTo f s < ⊤ :=
      hle.trans_lt (WithTop.coe_lt_top t)
    obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp
      (WithTop.lt_top_iff_ne_top.mp hfinite)
    have hus : u + 1 ≤ s :=
      ((firstNonnegativeWindowStartUpTo_eq_coe_iff f s u).mp hu.symm).1
    have huflat :=
      (firstNonnegativeWindowStartUpTo_runningMinimum f s u hu.symm).2
    have hule : u ≤ t := by
      have hle' : (u : WithTop ℝ≥0) ≤ t := by rw [hu]; exact hle
      exact WithTop.coe_le_coe.mp hle'
    have htu : t ≤ u := hleast u hus huflat
    simpa [le_antisymm hule htu] using hu.symm

end ProbabilityTheory

end
