/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.FirstPassage

/-!
# Restarting a continuous path at first passage

The public theorems in this file are:

- `ProbabilityTheory.firstPassageBelow_shiftToZero_eq`:
  if $b<a<f(0)$ and the first passages $\tau_a,\tau_b$ are finite,
  then $\tau_b=\tau_a+\tau_{b-a}(f(\tau_a+\cdot)-f(\tau_a))$.
- `ProbabilityTheory.firstPassageBelow_freezeAfter_eq`:
  the first passage can be read from the path frozen at that time.
- `ProbabilityTheory.firstPassageBelow_shiftToZero_eq_of_before`:
  for $q<\tau_a(f)<\infty$, passage after time $q$ occurs at
  the elapsed time $\tau_a(f)-q$.
- `ProbabilityTheory.firstPassageBelow_shiftToZero_eq_of_strictUntil`:
  if a path is above $a$ on $[q,d)$ and reaches $a$ at $d$,
  its path shifted at $q$ first enters $(-\infty,a-f(q)]$ at $d-q$.

This deterministic identity is used with the Brownian strong Markov
property to obtain stationary independent increments of the descending
hitting-time process. It is the pathwise component of the Lévy
decomposition invoked by Erwin Bolthausen, *On a functional central
limit theorem for random walks conditioned to stay positive*,
Lemma 2.3, equation (2.2), Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open scoped NNReal

namespace ProbabilityTheory

/-- The first-passage time is unchanged when a path is frozen at its
finite first passage. -/
theorem firstPassageBelow_freezeAfter_eq
    (f : C(ℝ≥0, ℝ)) (a : ℝ) (τ : ℝ≥0)
    (hτ : firstPassageBelow f a = τ) :
    firstPassageBelow (freezeAfter f τ) a = τ := by
  have hprefix (u : ℝ≥0) (hu : u ≤ τ) :
      f u = (freezeAfter f τ) u := by
    change f u = f (min u τ)
    rw [min_eq_left hu]
  have heq := firstPassageBelow_eq_of_agreeOn f (freezeAfter f τ) a τ
    hprefix (by rw [hτ])
  rw [hτ] at heq
  exact heq.symm

/-- Restarting at any time strictly before a finite first passage
subtracts that observation time from the passage time. -/
theorem firstPassageBelow_shiftToZero_eq_of_before
    (f : C(ℝ≥0, ℝ)) (a : ℝ) {q t : ℝ≥0}
    (hqt : q < t) (hpass : firstPassageBelow f a = t) :
    firstPassageBelow (shiftToZero f q) (a - f q) =
      ((t - q : ℝ≥0) : WithTop ℝ≥0) := by
  have hhit : ∃ u : ℝ≥0, f u ≤ a := by
    by_contra h
    have htop : firstPassageBelow f a = ⊤ :=
      (firstPassageBelow_eq_top_iff f a).2
        (fun u => lt_of_not_ge (fun hu => h ⟨u, hu⟩))
    rw [hpass] at htop
    exact WithTop.coe_ne_top htop
  have hinf : sInf {u : ℝ≥0 | f u ≤ a} = t :=
    WithTop.coe_eq_coe.mp (by
      simpa [firstPassageBelow, firstPassageLE, hhit] using hpass)
  have hft : f t ≤ a := by
    rw [← hinf]
    exact firstPassageBelow_attained f a hhit
  have htime : q + (t - q) = t := add_tsub_cancel_of_le hqt.le
  have hhitShift : ∃ u : ℝ≥0, (shiftToZero f q) u ≤ a - f q := by
    refine ⟨t - q, ?_⟩
    change f (q + (t - q)) - f q ≤ a - f q
    rw [htime]
    exact sub_le_sub_right hft _
  have hupper : firstPassageBelow (shiftToZero f q) (a - f q) ≤
      (t - q : ℝ≥0) := by
    apply (firstPassageBelow_le_iff _ _ _).2
    refine ⟨t - q, le_rfl, ?_⟩
    change f (q + (t - q)) - f q ≤ a - f q
    rw [htime]
    exact sub_le_sub_right hft _
  have hlower : (t - q : WithTop ℝ≥0) ≤
      firstPassageBelow (shiftToZero f q) (a - f q) := by
    by_contra h
    have hlt : firstPassageBelow (shiftToZero f q) (a - f q) <
        (t - q : WithTop ℝ≥0) := lt_of_not_ge h
    obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp
      (ne_top_of_lt hlt)
    have huReal : u < t - q := by
      rw [← hu] at hlt
      exact WithTop.coe_lt_coe.mp hlt
    have huInf : sInf {v : ℝ≥0 | (shiftToZero f q) v ≤ a - f q} = u :=
      WithTop.coe_eq_coe.mp (by
        simpa [firstPassageBelow, firstPassageLE, hhitShift] using hu.symm)
    have huVal : (shiftToZero f q) u ≤ a - f q := by
      rw [← huInf]
      exact firstPassageBelow_attained _ _ hhitShift
    have hqu : q + u < t := by
      calc
        q + u < q + (t - q) := by simpa [add_comm] using add_lt_add_left huReal q
        _ = t := htime
    have hearly := firstPassageBelow_no_earlier f a hhit
      (show q + u < sInf {v : ℝ≥0 | f v ≤ a} by rw [hinf]; exact hqu)
    change f (q + u) - f q ≤ a - f q at huVal
    linarith
  exact le_antisymm hupper hlower

/-- A path's first return after an observation time is the passage
time of its future increment path at the corresponding relative level. -/
theorem firstPassageBelow_shiftToZero_eq_of_strictUntil
    (f : C(ℝ≥0, ℝ)) (a : ℝ) {q d : ℝ≥0} (hqd : q < d)
    (hd : f d ≤ a)
    (hstrict : ∀ u : ℝ≥0, q ≤ u → u < d → a < f u) :
    firstPassageBelow (shiftToZero f q) (a - f q) =
      ((d - q : ℝ≥0) : WithTop ℝ≥0) := by
  have htime : q + (d - q) = d := add_tsub_cancel_of_le hqd.le
  have hhit : ∃ u : ℝ≥0, (shiftToZero f q) u ≤ a - f q := by
    refine ⟨d - q, ?_⟩
    change f (q + (d - q)) - f q ≤ a - f q
    rw [htime]
    exact sub_le_sub_right hd _
  have hupper : firstPassageBelow (shiftToZero f q) (a - f q) ≤
      (d - q : ℝ≥0) := by
    apply (firstPassageBelow_le_iff _ _ _).2
    refine ⟨d - q, le_rfl, ?_⟩
    change f (q + (d - q)) - f q ≤ a - f q
    rw [htime]
    exact sub_le_sub_right hd _
  have hlower : (d - q : WithTop ℝ≥0) ≤
      firstPassageBelow (shiftToZero f q) (a - f q) := by
    by_contra h
    have hlt : firstPassageBelow (shiftToZero f q) (a - f q) <
        (d - q : WithTop ℝ≥0) := lt_of_not_ge h
    obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
    have huReal : u < d - q := by
      rw [← hu] at hlt
      exact WithTop.coe_lt_coe.mp hlt
    have huInf : sInf {v : ℝ≥0 | (shiftToZero f q) v ≤ a - f q} = u :=
      WithTop.coe_eq_coe.mp (by
        simpa [firstPassageBelow, firstPassageLE, hhit] using hu.symm)
    have huVal : (shiftToZero f q) u ≤ a - f q := by
      rw [← huInf]
      exact firstPassageBelow_attained _ _ hhit
    have hqu : q + u < d := by
      calc
        q + u < q + (d - q) := by simpa [add_comm] using add_lt_add_left huReal q
        _ = d := htime
    have hearly := hstrict (q + u) (le_add_of_nonneg_right bot_le) hqu
    change f (q + u) - f q ≤ a - f q at huVal
    linarith
  exact le_antisymm hupper hlower

/-- First passage below a deeper level decomposes into the first passage
of the higher level and the first passage by the restarted increment path. -/
theorem firstPassageBelow_shiftToZero_eq
    (f : C(ℝ≥0, ℝ)) {a b : ℝ} {τa τb : ℝ≥0}
    (hba : b < a) (h0 : a < f 0)
    (ha : firstPassageBelow f a = τa)
    (hb : firstPassageBelow f b = τb) :
    firstPassageBelow (shiftToZero f τa) (b - a) =
      ((τb - τa : ℝ≥0) : WithTop ℝ≥0) := by
  have hhitA : ∃ t : ℝ≥0, f t ≤ a := by
    by_contra h
    have htop := (firstPassageBelow_eq_top_iff f a).mpr
      (fun t => lt_of_not_ge (fun ht => h ⟨t, ht⟩))
    rw [ha] at htop
    exact WithTop.coe_ne_top htop
  have hhitB : ∃ t : ℝ≥0, f t ≤ b := by
    by_contra h
    have htop := (firstPassageBelow_eq_top_iff f b).mpr
      (fun t => lt_of_not_ge (fun ht => h ⟨t, ht⟩))
    rw [hb] at htop
    exact WithTop.coe_ne_top htop
  have hinfA : sInf {t : ℝ≥0 | f t ≤ a} = τa := by
    apply WithTop.coe_injective
    simpa [firstPassageBelow, firstPassageLE, hhitA] using ha
  have hinfB : sInf {t : ℝ≥0 | f t ≤ b} = τb := by
    apply WithTop.coe_injective
    simpa [firstPassageBelow, firstPassageLE, hhitB] using hb
  have hvalueA : f τa = a := by
    rw [← hinfA]
    exact firstPassageBelow_value_eq f a h0 hhitA
  have hvalueB : f τb ≤ b := by
    rw [← hinfB]
    exact firstPassageBelow_attained f b hhitB
  have hle : τa ≤ τb := by
    have h := (firstPassageBelow_le_iff f a τb).mpr
      ⟨τb, le_rfl, hvalueB.trans hba.le⟩
    rw [ha] at h
    exact WithTop.coe_le_coe.mp h
  have hsum : τa + (τb - τa) = τb := add_tsub_cancel_of_le hle
  have hvalShift : (shiftToZero f τa) (τb - τa) ≤ b - a := by
    change f (τa + (τb - τa)) - f τa ≤ b - a
    rw [hsum, hvalueA]
    exact sub_le_sub_right hvalueB _
  have hhitShift : ∃ t : ℝ≥0, (shiftToZero f τa) t ≤ b - a :=
    ⟨τb - τa, hvalShift⟩
  have hupper : firstPassageBelow (shiftToZero f τa) (b - a) ≤
      ((τb - τa : ℝ≥0) : WithTop ℝ≥0) :=
    (firstPassageBelow_le_iff (shiftToZero f τa) (b - a) (τb - τa)).mpr
      ⟨τb - τa, le_rfl, hvalShift⟩
  have hhitAt :
      (shiftToZero f τa)
        (sInf {t : ℝ≥0 | (shiftToZero f τa) t ≤ b - a}) ≤ b - a :=
    firstPassageBelow_attained (shiftToZero f τa) (b - a) hhitShift
  have hlower : τb - τa ≤
      sInf {t : ℝ≥0 | (shiftToZero f τa) t ≤ b - a} := by
    have hfa : f (τa + sInf {t : ℝ≥0 |
        (shiftToZero f τa) t ≤ b - a}) ≤ b := by
      change f (τa + sInf {t : ℝ≥0 |
        (shiftToZero f τa) t ≤ b - a}) - f τa ≤ b - a at hhitAt
      rw [hvalueA] at hhitAt
      linarith
    have hτb : τb ≤ τa + sInf {t : ℝ≥0 |
        (shiftToZero f τa) t ≤ b - a} := by
      have h := (firstPassageBelow_le_iff f b _).mpr
        ⟨_, le_rfl, hfa⟩
      rw [hb] at h
      exact WithTop.coe_le_coe.mp h
    apply tsub_le_iff_right.mpr
    simpa [add_comm] using hτb
  apply le_antisymm hupper
  have hshiftEq : firstPassageBelow (shiftToZero f τa) (b - a) =
      (sInf {t : ℝ≥0 | (shiftToZero f τa) t ≤ b - a} : ℝ≥0) := by
    simp [firstPassageBelow, firstPassageLE, hhitShift]
    rfl
  rw [hshiftEq]
  exact WithTop.coe_le_coe.mpr hlower

end ProbabilityTheory

end
