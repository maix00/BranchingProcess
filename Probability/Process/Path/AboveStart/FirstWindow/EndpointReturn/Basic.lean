/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.AboveStart.FirstWindow.Time.Basic
public import Probability.Process.Path.AboveStart.FirstWindow.Time.RunningMinimum
public import Probability.Process.Path.FirstPassage.Descending
public import Probability.Process.Path.Extrema.RunningMinimum

/-!
# Endpoint returns of the first unit window

## Public declarations

The public declarations in this file are:

- `ProbabilityTheory.IsUnitExcursionAt`: with $D_f(t)=f(t)-m_f(t)$,
  $D_f(t)=D_f(t+1)=0$ and $D_f(t+u)>0$ for all $0<u<1$.
- `ProbabilityTheory.HasTripleRunningMinimumContact`:
  $\exists u<v<w$ with $m_f(u)=m_f(v)=m_f(w)$ and
  $D_f(u)=D_f(v)=D_f(w)=0$; this is Bolthausen's event $U$.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_endpointReturn_firstPassageBelow`:
  if $T^s(f)=t$, $f(t+1)=f(t)$, and $U$ fails, then
  $\inf\{u:f(u)\le f(t)\}=t$.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_endpointReturn_unitExcursion`:
  under the same hypotheses, $D_f(t)=D_f(t+1)=0$ and
  $D_f(t+u)>0$ for all $0<u<1$.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_endpointReturn_descendingHittingTime`:
  if also $f(t)=-x$, then $\tau_x=t$ and $t+1<\tau_y$ for every $y>x$.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_endpointReturn_hittingTimeRightLimit`:
  if also $\exists w, f(w)<f(t)$, then for every $v>t+1$ there is $y>x$
  with $\tau_y\le v$.

These pathwise results formalize the endpoint-return argument in equation
(2.2) of Lemma 2.3 in Erwin Bolthausen, *On a Functional Central Limit
Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3)
(1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open scoped NNReal

namespace ProbabilityTheory

/-- During the first eligible window, returning to its starting value is
equivalent to meeting the running minimum again. This is the path event
in Bolthausen's Lemma 2.3, equation (2.4). -/
private lemma firstNonnegativeWindowStartUpTo_eq_runningMinimum_iff
    (f : C(ℝ≥0, ℝ)) (s t : ℝ≥0)
    (hfirst : firstNonnegativeWindowStartUpTo f s = t)
    {u : ℝ≥0} (hu : u ≤ 1) :
    f (t + u) = f t ↔ f (t + u) = runningMinimum f (t + u) := by
  obtain ⟨hrecord, hflat⟩ :=
    firstNonnegativeWindowStartUpTo_runningMinimum f s t hfirst
  rw [runningMinimum_eq_of_between f hflat hu, ← hrecord]


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
  simpa [firstPassageBelow, firstPassageLE_eq_sInf, hex] using
    congrArg (fun u : ℝ≥0 => (u : WithTop ℝ≥0)) hleast


/-- The endpoint equality in Bolthausen's Lemma 2.3, equation (2.2),
reduces to the interior-return event of (2.4) or a unit-length
excursion of the height above the running minimum. -/
private lemma firstNonnegativeWindowStartUpTo_endpointReturn_cases
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


/-- Outside Bolthausen's three-contact event, an endpoint return of the
first unit window is followed arbitrarily soon by a new running minimum,
provided the path eventually reaches a lower value. This is the
pathwise right-limit step for the hitting-time jump in Lemma 2.3,
equation (2.2). -/
private lemma firstNonnegativeWindowStartUpTo_endpointReturn_immediateDescent
    (f : C(ℝ≥0, ℝ)) (s t : ℝ≥0)
    (hfirst : firstNonnegativeWindowStartUpTo f s = t)
    (hend : f (t + 1) = f t)
    (hno : ¬ HasTripleRunningMinimumContact f)
    (hlower : ∃ w : ℝ≥0, f w < f t)
    (v : ℝ≥0) (hvt : t + 1 < v) :
    ∃ u : ℝ≥0, t + 1 < u ∧ u ≤ v ∧ f u < f t := by
  classical
  obtain ⟨hrecord, hflat⟩ :=
    firstNonnegativeWindowStartUpTo_runningMinimum f s t hfirst
  by_contra hnone
  have hbefore (u : ℝ≥0) (huv : u ≤ v) : f t ≤ f u := by
    by_cases hut : u ≤ t + 1
    · calc
        f t = runningMinimum f t := hrecord
        _ = runningMinimum f (t + 1) := hflat.symm
        _ ≤ f u := runningMinimum_le f hut
    · have htu : t + 1 < u := lt_of_not_ge hut
      exact le_of_not_gt (fun hlt => hnone ⟨u, htu, huv, hlt⟩)
  have hfv : f t < f v := by
    rcases (hbefore v le_rfl).eq_or_lt with heq | hgt
    · have hmv : runningMinimum f v = f t := by
        apply le_antisymm
        · rw [heq]
          exact runningMinimum_le f le_rfl
        · obtain ⟨u, hu, hmin⟩ := exists_runningMinimum_eq f v
          rw [← hmin]
          exact hbefore u hu.2
      apply False.elim (hno ⟨t, t + 1, v,
        lt_add_of_pos_right t (by norm_num), hvt,
        hflat.symm, (hflat.trans hrecord.symm).trans hmv.symm, ?_, ?_, ?_⟩)
      · exact (aboveRunningMinimum_eq_zero_iff f t).2 hrecord
      · exact (aboveRunningMinimum_eq_zero_iff f (t + 1)).2 (by
          rw [hend, hflat, hrecord])
      · exact (aboveRunningMinimum_eq_zero_iff f v).2 (by
          rw [← heq, hmv])
    · exact hgt
  let A : Set ℝ≥0 := {u | v ≤ u ∧ f u ≤ f t}
  have hAclosed : IsClosed A :=
    isClosed_Ici.inter (isClosed_Iic.preimage f.continuous)
  obtain ⟨w, hw⟩ := hlower
  have hvw : v < w := by
    by_contra h
    exact (not_lt_of_ge (hbefore w (le_of_not_gt h))) hw
  have hAne : A.Nonempty := ⟨w, hvw.le, hw.le⟩
  let z : ℝ≥0 := sInf A
  have hzmem : z ∈ A := hAclosed.csInf_mem hAne ⟨0, fun _ _ => bot_le⟩
  have hvz : v < z := by
    have hvzle : v ≤ z := hzmem.1
    exact hvzle.lt_of_ne (fun heq => (not_le_of_gt hfv) (by
      simpa [z, heq] using hzmem.2))
  have hzvalue : f z = f t := by
    rcases hzmem.2.eq_or_lt with heq | hlt
    · exact heq
    · have hbetween : f t ∈ Set.Icc (f z) (f v) := ⟨hlt.le, hfv.le⟩
      obtain ⟨u, hu, hvalue⟩ :=
        (intermediate_value_Icc' hvz.le f.continuous.continuousOn) hbetween
      have huz : u < z := hu.2.lt_of_ne (fun heq' => by
        rw [heq'] at hvalue
        exact (ne_of_lt hlt) hvalue)
      have hzu : z ≤ u := csInf_le ⟨0, fun _ _ => bot_le⟩
        (show u ∈ A from ⟨hu.1, hvalue.le⟩)
      exact False.elim ((not_le_of_gt huz) hzu)
  have hminz : runningMinimum f z = f t := by
    apply le_antisymm
    · rw [← hzvalue]
      exact runningMinimum_le f le_rfl
    · obtain ⟨u, hu, hmin⟩ := exists_runningMinimum_eq f z
      rw [← hmin]
      by_cases huv : u ≤ v
      · exact hbefore u huv
      · have hvu : v < u := lt_of_not_ge huv
        by_cases huz : u = z
        · rw [huz, hzvalue]
        · have huzlt : u < z := hu.2.lt_of_ne huz
          exact le_of_not_gt (fun hlt =>
            (not_le_of_gt huzlt) (csInf_le ⟨0, fun _ _ => bot_le⟩
              (show u ∈ A from ⟨hvu.le, hlt.le⟩)))
  apply hno
  refine ⟨t, t + 1, z, lt_add_of_pos_right t (by norm_num),
    hvt.trans hvz, hflat.symm, ?_, ?_, ?_, ?_⟩
  · exact (hflat.trans hrecord.symm).trans hminz.symm
  · exact (aboveRunningMinimum_eq_zero_iff f t).2 hrecord
  · exact (aboveRunningMinimum_eq_zero_iff f (t + 1)).2 (by
      rw [hend, hflat, hrecord])
  · exact (aboveRunningMinimum_eq_zero_iff f z).2 (by rw [hzvalue, hminz])


/-- The right-hand hitting-time values approach the end of the unit
excursion: every later time already contains passage to some strictly
lower level. Together with the preceding lower bound, this expresses
the exact unit jump used in Bolthausen's Lemma 2.3, equation (2.2). -/
theorem firstNonnegativeWindowStartUpTo_endpointReturn_hittingTimeRightLimit
    (f : C(ℝ≥0, ℝ)) (s t x : ℝ≥0)
    (hfirst : firstNonnegativeWindowStartUpTo f s = t)
    (hend : f (t + 1) = f t)
    (hlevel : f t = -(x : ℝ))
    (hno : ¬ HasTripleRunningMinimumContact f)
    (hlower : ∃ w : ℝ≥0, f w < f t)
    (v : ℝ≥0) (hvt : t + 1 < v) :
    ∃ y : ℝ≥0, x < y ∧ descendingHittingTime f y ≤ v := by
  obtain ⟨u, _, huv, hfu⟩ :=
    firstNonnegativeWindowStartUpTo_endpointReturn_immediateDescent
      f s t hfirst hend hno hlower v hvt
  have hnegative : 0 ≤ -f u := by
    rw [hlevel] at hfu
    have hx : 0 ≤ (x : ℝ) := x.property
    linarith
  let y : ℝ≥0 := ⟨-f u, hnegative⟩
  have hxy : x < y := by
    change (x : ℝ) < -f u
    rw [hlevel] at hfu
    linarith
  refine ⟨y, hxy, ?_⟩
  have hpass : descendingHittingTime f y ≤ u :=
    (firstPassageBelow_le_iff f (-(y : ℝ)) u).2
      ⟨u, le_rfl, by change f u ≤ -(-f u); linarith⟩
  exact hpass.trans (WithTop.coe_le_coe.mpr huv)


end ProbabilityTheory

end
