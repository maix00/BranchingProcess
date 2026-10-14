/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.AboveStart.Continuous
public import Probability.Process.Path.DescendingHittingTime
public import Probability.Process.Path.RunningMinimum
public import Probability.Process.Path.TimeGrid.NonnegativeRationals

/-!
# First windows and the running minimum of a continuous path

The public definitions and theorems in this file are:

- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_runningMinimum`:
  if $T^s(f)=t<\infty$, then $f(t)=m_f(t)=m_f(t+1)$.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_eq_runningMinimum_iff`:
  for $0\le u\le1$ and $T^s(f)=t$, the equality $f(t+u)=f(t)$
  holds exactly when $f(t+u)=m_f(t+u)$.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_return_rationalInterval`:
  an interior return in the first unit window gives rational times
  $r<q$ enclosing a repeated running-minimum value.
- `ProbabilityTheory.IsUnitExcursionAt`: the height above the running
  minimum vanishes at $t$ and $t+1$ and is positive between them.
- `ProbabilityTheory.HasTripleRunningMinimumContact`: three ordered
  contacts with one running-minimum value, Bolthausen's event $U$.
- `ProbabilityTheory.HasTripleRunningMinimumContact.rationalInterval`:
  such contacts yield a rational interval on which the old minimum is
  attained again.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_endpointReturn_firstPassageBelow`:
  outside the three-contact event, an endpoint return at $t$ is the
  first passage of the level $f(t)$.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_endpointReturn_unitExcursion`:
  outside that event, the two endpoint contacts enclose one unit
  excursion above the running minimum.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_endpointReturn_descendingHittingTime`:
  at level $x=-f(t)\ge0$ the descending passage occurs at $t$, while
  passage to every lower level occurs after $t+1$.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_endpointReturn_cases`:
  an endpoint return yields either an interior return or a unit
  excursion above the running minimum.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_lastStart_aboveRunningMinimum_eq_zero`:
  $T^{t+1}(f)=t$ implies $D_f(t)=0$.
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

/-- An interior return of the first unit window to its starting
level yields a rational interval on which the old running minimum is
attained again. This is the rational covering step in Bolthausen's
Lemma 2.3, equation (2.4). -/
theorem firstNonnegativeWindowStartUpTo_return_rationalInterval
    (f : C(ℝ≥0, ℝ)) (s t : ℝ≥0)
    (hfirst : firstNonnegativeWindowStartUpTo f s = t)
    {u : ℝ≥0} (hu0 : 0 < u) (hu1 : u < 1)
    (hreturn : f (t + u) = f t) :
    ∃ r q : ℚ≥0,
      nonnegativeRationalTime r < nonnegativeRationalTime q ∧
      runningMinimum f (nonnegativeRationalTime q) =
        runningMinimum f (nonnegativeRationalTime r) ∧
      ∃ v, nonnegativeRationalTime r ≤ v ∧
        v ≤ nonnegativeRationalTime q ∧
        f v = runningMinimum f (nonnegativeRationalTime r) := by
  obtain ⟨hrecord, hflat⟩ :=
    firstNonnegativeWindowStartUpTo_runningMinimum f s t hfirst
  have htv : t < t + u := lt_add_of_pos_right t hu0
  have hvt : t + u < t + 1 := by simpa [add_comm] using add_lt_add_left hu1 t
  obtain ⟨r, htr, hrv⟩ := exists_nonnegativeRationalTime_between htv
  obtain ⟨q, hvq, hqt⟩ := exists_nonnegativeRationalTime_between hvt
  have hbetween (x : ℝ≥0) (htx : t ≤ x) (hxt : x ≤ t + 1) :
      runningMinimum f x = runningMinimum f t := by
    apply le_antisymm
    · exact runningMinimum_antitone f htx
    · rw [← hflat]
      exact runningMinimum_antitone f hxt
  have hmr := hbetween (nonnegativeRationalTime r) htr.le
    (hrv.le.trans hvt.le)
  have hmq := hbetween (nonnegativeRationalTime q)
    (htv.le.trans hvq.le) hqt.le
  refine ⟨r, q, hrv.trans hvq, hmq.trans hmr.symm,
    t + u, hrv.le, hvq.le, ?_⟩
  rw [hmr, hreturn, hrecord]

/-- A unit-length excursion of a path above its running minimum,
starting at time `t`. -/
def IsUnitExcursionAt (f : C(ℝ≥0, ℝ)) (t : ℝ≥0) : Prop :=
  aboveRunningMinimum f t = 0 ∧
    aboveRunningMinimum f (t + 1) = 0 ∧
    ∀ u : ℝ≥0, 0 < u → u < 1 →
      0 < aboveRunningMinimum f (t + u)

/-- Three ordered contacts with a common running-minimum value.
This is the path event `U` in Bolthausen's Lemma 2.3. -/
def HasTripleRunningMinimumContact (f : C(ℝ≥0, ℝ)) : Prop :=
  ∃ u v w : ℝ≥0, u < v ∧ v < w ∧
    runningMinimum f u = runningMinimum f v ∧
    runningMinimum f v = runningMinimum f w ∧
    aboveRunningMinimum f u = 0 ∧
    aboveRunningMinimum f v = 0 ∧
    aboveRunningMinimum f w = 0

/-- Bolthausen's rational covering of the three-contact event: choose
rational times between the first two and the last two contacts. -/
theorem HasTripleRunningMinimumContact.rationalInterval
    {f : C(ℝ≥0, ℝ)} (h : HasTripleRunningMinimumContact f) :
    ∃ r q : ℚ≥0,
      nonnegativeRationalTime r < nonnegativeRationalTime q ∧
      runningMinimum f (nonnegativeRationalTime q) =
        runningMinimum f (nonnegativeRationalTime r) ∧
      ∃ v, nonnegativeRationalTime r ≤ v ∧
        v ≤ nonnegativeRationalTime q ∧
        f v = runningMinimum f (nonnegativeRationalTime r) := by
  obtain ⟨u, v, w, huv, hvw, hmuv, hmvw, _, hDv, _⟩ := h
  obtain ⟨r, hur, hrv⟩ := exists_nonnegativeRationalTime_between huv
  obtain ⟨q, hvq, hqw⟩ := exists_nonnegativeRationalTime_between hvw
  have hmr : runningMinimum f (nonnegativeRationalTime r) =
      runningMinimum f u := by
    apply le_antisymm
    · exact runningMinimum_antitone f hur.le
    · rw [hmuv]
      exact runningMinimum_antitone f hrv.le
  have hmq : runningMinimum f (nonnegativeRationalTime q) =
      runningMinimum f v := by
    apply le_antisymm
    · exact runningMinimum_antitone f hvq.le
    · rw [hmvw]
      exact runningMinimum_antitone f hqw.le
  refine ⟨r, q, hrv.trans hvq, ?_, v, hrv.le, hvq.le, ?_⟩
  · rw [hmq, hmr, hmuv]
  · rw [(aboveRunningMinimum_eq_zero_iff f v).mp hDv, hmr, hmuv]

/-- Outside Bolthausen's three-contact event, the beginning of a first
unit window that returns to its starting level is the first time the
path reaches that level. This identifies the level of the descending
hitting-time process used in Lemma 2.3, equation (2.2). -/
theorem firstNonnegativeWindowStartUpTo_endpointReturn_firstPassageBelow
    (f : C(ℝ≥0, ℝ)) (s t : ℝ≥0)
    (hfirst : firstNonnegativeWindowStartUpTo f s = t)
    (hend : f (t + 1) = f t)
    (hno : ¬ HasTripleRunningMinimumContact f) :
    firstPassageBelow f (f t) = t := by
  obtain ⟨hrecord, hflat⟩ :=
    firstNonnegativeWindowStartUpTo_runningMinimum f s t hfirst
  have hbefore (u : ℝ≥0) (hut : u < t) : f t < f u := by
    by_contra h
    have hfu : f u ≤ f t := le_of_not_gt h
    have hmu : runningMinimum f u = f t := by
      apply le_antisymm
      · exact (runningMinimum_le f le_rfl).trans hfu
      · calc
          f t = runningMinimum f t := hrecord
          _ ≤ runningMinimum f u := runningMinimum_antitone f hut.le
    have hcontact : f u = runningMinimum f u := by
      apply le_antisymm
      · rw [hmu]
        exact hfu
      · exact runningMinimum_le f le_rfl
    apply hno
    refine ⟨u, t, t + 1, hut, lt_add_of_pos_right t (by norm_num),
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmu, ← hrecord]
    · exact hflat.symm
    · exact (aboveRunningMinimum_eq_zero_iff f u).2 hcontact
    · exact (aboveRunningMinimum_eq_zero_iff f t).2 hrecord
    · apply (aboveRunningMinimum_eq_zero_iff f (t + 1)).2
      rw [hend, hflat, hrecord]
  have hex : ∃ u : ℝ≥0, f u ≤ f t := ⟨t, le_rfl⟩
  have hleast : sInf {u : ℝ≥0 | f u ≤ f t} = t := by
    apply le_antisymm
    · exact csInf_le ⟨0, fun _ _ => bot_le⟩
        (show t ∈ {u : ℝ≥0 | f u ≤ f t} by simp)
    · apply le_csInf (s := {u : ℝ≥0 | f u ≤ f t})
        ⟨t, show f t ≤ f t from le_rfl⟩
      intro u hu
      exact le_of_not_gt (fun hut => not_le_of_gt (hbefore u hut) hu)
  simpa [firstPassageBelow, firstPassageLE, hex] using
    congrArg (fun u : ℝ≥0 => (u : WithTop ℝ≥0)) hleast

/-- The endpoint equality in Bolthausen's Lemma 2.3, equation (2.2),
reduces to the interior-return event of (2.4) or a unit-length
excursion of the height above the running minimum. -/
theorem firstNonnegativeWindowStartUpTo_endpointReturn_cases
    (f : C(ℝ≥0, ℝ)) (s t : ℝ≥0)
    (hfirst : firstNonnegativeWindowStartUpTo f s = t)
    (hend : f (t + 1) = f t) :
    (∃ u : ℝ≥0, 0 < u ∧ u < 1 ∧ f (t + u) = f t) ∨
      IsUnitExcursionAt f t := by
  by_cases hreturn : ∃ u : ℝ≥0, 0 < u ∧ u < 1 ∧ f (t + u) = f t
  · exact Or.inl hreturn
  · right
    obtain ⟨hrecord, hflat⟩ :=
      firstNonnegativeWindowStartUpTo_runningMinimum f s t hfirst
    refine ⟨(aboveRunningMinimum_eq_zero_iff f t).2 hrecord,
      (aboveRunningMinimum_eq_zero_iff f (t + 1)).2 ?_, ?_⟩
    · rw [hend, hflat, hrecord]
    · intro u hu0 hu1
      have hne : f (t + u) ≠ f t := by
        intro heq
        exact hreturn ⟨u, hu0, hu1, heq⟩
      have hnemin : f (t + u) ≠ runningMinimum f (t + u) := by
        intro heq
        exact hne ((firstNonnegativeWindowStartUpTo_eq_runningMinimum_iff
          f s t hfirst hu1.le).2 heq)
      have hle : runningMinimum f (t + u) ≤ f (t + u) :=
        runningMinimum_le f le_rfl
      exact sub_pos.mpr (lt_of_le_of_ne hle (Ne.symm hnemin))

/-- Outside Bolthausen's event `U`, an endpoint return of the first
unit window encloses a unit excursion above the running minimum. -/
theorem firstNonnegativeWindowStartUpTo_endpointReturn_unitExcursion
    (f : C(ℝ≥0, ℝ)) (s t : ℝ≥0)
    (hfirst : firstNonnegativeWindowStartUpTo f s = t)
    (hend : f (t + 1) = f t)
    (hno : ¬ HasTripleRunningMinimumContact f) :
    IsUnitExcursionAt f t := by
  rcases firstNonnegativeWindowStartUpTo_endpointReturn_cases
      f s t hfirst hend with ⟨u, hu0, hu1, hreturn⟩ | hexc
  · obtain ⟨hrecord, hflat⟩ :=
      firstNonnegativeWindowStartUpTo_runningMinimum f s t hfirst
    apply False.elim (hno ?_)
    refine ⟨t, t + u, t + 1, lt_add_of_pos_right t hu0, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa [add_comm] using add_lt_add_left hu1 t
    · exact (runningMinimum_eq_of_between f hflat hu1.le).symm
    · exact (runningMinimum_eq_of_between f hflat hu1.le).trans hflat.symm
    · exact (aboveRunningMinimum_eq_zero_iff f t).2 hrecord
    · exact (aboveRunningMinimum_eq_zero_iff f (t + u)).2 (by
        rw [hreturn, runningMinimum_eq_of_between f hflat hu1.le, hrecord])
    · exact (aboveRunningMinimum_eq_zero_iff f (t + 1)).2 (by
        rw [hend, hflat, hrecord])
  · exact hexc

/-- The first-window endpoint return produces the unit-length gap in
the descending hitting-time process used in Bolthausen's proof of
Lemma 2.3, equation (2.2): the original level is first reached at
`t`, and all strictly lower levels are reached after `t+1`. -/
theorem firstNonnegativeWindowStartUpTo_endpointReturn_descendingHittingTime
    (f : C(ℝ≥0, ℝ)) (s t x : ℝ≥0)
    (hfirst : firstNonnegativeWindowStartUpTo f s = t)
    (hend : f (t + 1) = f t)
    (hlevel : f t = -(x : ℝ))
    (hno : ¬ HasTripleRunningMinimumContact f) :
    descendingHittingTime f x = t ∧
      ∀ y : ℝ≥0, x < y →
        (t + 1 : WithTop ℝ≥0) < descendingHittingTime f y := by
  obtain ⟨hrecord, hflat⟩ :=
    firstNonnegativeWindowStartUpTo_runningMinimum f s t hfirst
  constructor
  · simpa [descendingHittingTime, ← hlevel] using
      firstNonnegativeWindowStartUpTo_endpointReturn_firstPassageBelow
        f s t hfirst hend hno
  · intro y hxy
    have hlevel' : -(y : ℝ) < f t := by
      rw [hlevel]
      exact neg_lt_neg (by exact_mod_cast hxy)
    have hmin : -(y : ℝ) < runningMinimum f (t + 1) := by
      rw [hflat, ← hrecord]
      exact hlevel'
    have hnot : ¬ descendingHittingTime f y ≤ (t + 1 : WithTop ℝ≥0) := by
      intro hpass
      have hminle :=
        (runningMinimum_le_iff_firstPassageBelow_le f (t + 1) (-(y : ℝ))).2 hpass
      exact (not_le_of_gt hmin) hminle
    exact lt_of_not_ge hnot

/-- If the first unit window begins at the last admissible time, its
starting height above the running minimum is zero. This is the event
inclusion used for equation (2.3) in Bolthausen's Lemma 2.3. -/
theorem firstNonnegativeWindowStartUpTo_lastStart_aboveRunningMinimum_eq_zero
    (f : C(ℝ≥0, ℝ)) (t : ℝ≥0)
    (hfirst : firstNonnegativeWindowStartUpTo f (t + 1) = t) :
    aboveRunningMinimum f t = 0 := by
  exact (aboveRunningMinimum_eq_zero_iff f t).2
    (firstNonnegativeWindowStartUpTo_runningMinimum f (t + 1) t hfirst).1

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
