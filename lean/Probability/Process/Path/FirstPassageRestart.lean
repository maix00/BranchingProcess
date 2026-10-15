/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.FirstPassage

/-!
# Restarting a continuous path at first passage

The public theorem in this file is:

- `ProbabilityTheory.firstPassageBelow_shiftToZero_eq`:
  if $b<a<f(0)$ and the first passages $\tau_a,\tau_b$ are finite,
  then $\tau_b=\tau_a+\tau_{b-a}(f(\tau_a+\cdot)-f(\tau_a))$.

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
