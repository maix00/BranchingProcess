/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.AboveStart.Continuous

/-!
# Local windows above the starting level

The public definitions and theorems in this file are:

- `ProbabilityTheory.IsNonnegativeWindowStartFor`:
  $f(t+u)\ge f(t)$ for every $0\le u\le\varepsilon$.
- `ProbabilityTheory.HasNonnegativeWindowBeforeUnit`:
  some $t$ with $t+\varepsilon\le1$ starts such a window.
- `ProbabilityTheory.exists_nonnegativeWindow_before_unit_of_increase`:
  if $0\le a<b\le1$ and $f(a)<f(b)$, then such a window exists
  for some $\varepsilon>0$.
- `ProbabilityTheory.antitoneOn_of_no_nonnegativeWindow`:
  if every positive-duration window event fails, then $f$ is
  antitone on $[0,1]$.

The minimum-on-an-interval argument supplies the deterministic
implication used in Erwin Bolthausen, *On a functional central limit
theorem for random walks conditioned to stay positive*, Lemma 2.2,
p. 481, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open scoped NNReal

namespace ProbabilityTheory

/-- A continuous path stays above its value at the beginning of a
window of duration `duration`. -/
def IsNonnegativeWindowStartFor
    (f : C(ℝ≥0, ℝ)) (t duration : ℝ≥0) : Prop :=
  ∀ u : Set.Icc (0 : ℝ≥0) duration, f t ≤ f (t + u)

/-- The path has a positive-level window of the specified duration
inside the unit time interval. -/
def HasNonnegativeWindowBeforeUnit
    (f : C(ℝ≥0, ℝ)) (duration : ℝ≥0) : Prop :=
  ∃ t : ℝ≥0, t + duration ≤ 1 ∧
    IsNonnegativeWindowStartFor f t duration

/-- An increase of a continuous path inside $[0,1]$ produces a
positive-duration window above its starting level. Choose the first
minimum on the interval witnessing the increase. -/
theorem exists_nonnegativeWindow_before_unit_of_increase
    (f : C(ℝ≥0, ℝ)) {a b : ℝ≥0}
    (hab : a < b) (hb : b ≤ 1) (hfab : f a < f b) :
    ∃ duration : ℝ≥0, 0 < duration ∧
      HasNonnegativeWindowBeforeUnit f duration := by
  have hne : (Set.Icc a b).Nonempty :=
    ⟨a, le_rfl, hab.le⟩
  obtain ⟨t, ht, hmin⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc a b)).exists_isMinOn
      hne f.continuous.continuousOn
  have htb : t < b := by
    refine ht.2.lt_of_ne ?_
    intro hEq
    have hfa : f t ≤ f a := hmin ⟨le_rfl, hab.le⟩
    rw [hEq] at hfa
    exact (not_le_of_gt hfab) hfa
  let duration : ℝ≥0 := b - t
  have hduration : 0 < duration := tsub_pos_iff_lt.mpr htb
  have hsum : t + duration = b := add_tsub_cancel_of_le ht.2
  refine ⟨duration, hduration, t, hsum ▸ hb, ?_⟩
  intro u
  have htu : t + u ≤ b := by
    rw [← hsum]
    exact add_le_add_right u.property.2 t
  have hmem : t + u ∈ Set.Icc a b :=
    ⟨ht.1.trans (le_add_of_nonneg_right u.property.1), htu⟩
  exact hmin hmem

/-- If the path has no positive-duration window inside $[0,1]$,
its values are antitone there. This is the event containment needed
in Bolthausen's Lemma 2.2. -/
theorem antitoneOn_of_no_nonnegativeWindow
    (f : C(ℝ≥0, ℝ))
    (h : ∀ duration : ℝ≥0, 0 < duration →
      ¬ HasNonnegativeWindowBeforeUnit f duration) :
    AntitoneOn f (Set.Icc (0 : ℝ≥0) 1) := by
  intro a ha b hb hab
  by_contra hle
  have hfab : f a < f b := lt_of_not_ge hle
  have hab' : a < b := by
    exact hab.lt_of_ne (by intro heq; subst b; exact (lt_irrefl _ hfab))
  obtain ⟨duration, hduration, hwindow⟩ :=
    exists_nonnegativeWindow_before_unit_of_increase
      f hab' hb.2 hfab
  exact h duration hduration hwindow

end ProbabilityTheory

end
