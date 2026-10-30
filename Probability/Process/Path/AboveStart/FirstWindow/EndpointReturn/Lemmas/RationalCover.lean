/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.Path.AboveStart.FirstWindow.Time.RunningMinimum
import Probability.Process.Path.AboveStart.FirstWindow.EndpointReturn.Basic
import Topology.Order.NNReal.Rational

/-!
# Rational-time covers for first-window returns

## Internal proof declarations

The proof-support lemmas in this file are:

- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_return_rationalInterval`:
  if $T^s(f)=t$, $0<u<1$, and $f(t+u)=f(t)$, then there are rational times
  $r<q$ with $m_f(r)=m_f(q)$ and a $v\in[r,q]$ satisfying $f(v)=m_f(r)$.
- `ProbabilityTheory.HasTripleRunningMinimumContact.rationalInterval`:
  three ordered contacts $u<v<w$ with $m_f(u)=m_f(v)=m_f(w)$ and
  $D_f(u)=D_f(v)=D_f(w)=0$ give the same rational interval.
These are the rational-cover steps in equation (2.4) of Lemma 2.3 in Erwin
Bolthausen, *On a Functional Central Limit Theorem for Random Walks
Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098.
-/

section

open scoped NNReal

namespace ProbabilityTheory

/-- An interior return of the first unit window to its starting
level yields a rational interval on which the old running minimum is
attained again. This is the rational covering step in Bolthausen's
Lemma 2.3, equation (2.4). -/
lemma firstNonnegativeWindowStartUpTo_return_rationalInterval
    (f : C(ℝ≥0, ℝ)) (s t : ℝ≥0)
    (hfirst : firstNonnegativeWindowStartUpTo f s = t)
    {u : ℝ≥0} (hu0 : 0 < u) (hu1 : u < 1)
    (hreturn : f (t + u) = f t) :
    ∃ r q : ℚ≥0,
      (r : ℝ≥0) < (q : ℝ≥0) ∧
      runningMinimum f ((q : ℝ≥0)) =
        runningMinimum f ((r : ℝ≥0)) ∧
      ∃ v, (r : ℝ≥0) ≤ v ∧
        v ≤ (q : ℝ≥0) ∧
        f v = runningMinimum f ((r : ℝ≥0)) := by
  obtain ⟨hrecord, hflat⟩ :=
    firstNonnegativeWindowStartUpTo_runningMinimum f s t hfirst
  have htv : t < t + u := lt_add_of_pos_right t hu0
  have hvt : t + u < t + 1 := by simpa [add_comm] using add_lt_add_left hu1 t
  obtain ⟨r, htr, hrv⟩ := NNRat.exists_between_nnreal htv
  obtain ⟨q, hvq, hqt⟩ := NNRat.exists_between_nnreal hvt
  have hbetween (x : ℝ≥0) (htx : t ≤ x) (hxt : x ≤ t + 1) :
      runningMinimum f x = runningMinimum f t := by
    apply le_antisymm
    · exact runningMinimum_antitone f htx
    · rw [← hflat]
      exact runningMinimum_antitone f hxt
  have hmr := hbetween ((r : ℝ≥0)) htr.le
    (hrv.le.trans hvt.le)
  have hmq := hbetween ((q : ℝ≥0))
    (htv.le.trans hvq.le) hqt.le
  refine ⟨r, q, hrv.trans hvq, hmq.trans hmr.symm,
    t + u, hrv.le, hvq.le, ?_⟩
  rw [hmr, hreturn, hrecord]


/-- Bolthausen's rational covering of the three-contact event: choose
rational times between the first two and the last two contacts. -/
lemma HasTripleRunningMinimumContact.rationalInterval
    {f : C(ℝ≥0, ℝ)} (h : HasTripleRunningMinimumContact f) :
    ∃ r q : ℚ≥0,
      (r : ℝ≥0) < (q : ℝ≥0) ∧
      runningMinimum f ((q : ℝ≥0)) =
        runningMinimum f ((r : ℝ≥0)) ∧
      ∃ v, (r : ℝ≥0) ≤ v ∧
        v ≤ (q : ℝ≥0) ∧
        f v = runningMinimum f ((r : ℝ≥0)) := by
  obtain ⟨u, v, w, huv, hvw, hmuv, hmvw, _, hDv, _⟩ := h
  obtain ⟨r, hur, hrv⟩ := NNRat.exists_between_nnreal huv
  obtain ⟨q, hvq, hqw⟩ := NNRat.exists_between_nnreal hvw
  have hmr : runningMinimum f ((r : ℝ≥0)) =
      runningMinimum f u := by
    apply le_antisymm
    · exact runningMinimum_antitone f hur.le
    · rw [hmuv]
      exact runningMinimum_antitone f hrv.le
  have hmq : runningMinimum f ((q : ℝ≥0)) =
      runningMinimum f v := by
    apply le_antisymm
    · exact runningMinimum_antitone f hvq.le
    · rw [hmvw]
      exact runningMinimum_antitone f hqw.le
  refine ⟨r, q, hrv.trans hvq, ?_, v, hrv.le, hvq.le, ?_⟩
  · rw [hmq, hmr, hmuv]
  · rw [(aboveRunningMinimum_eq_zero_iff f v).mp hDv, hmr, hmuv]


end ProbabilityTheory

end
