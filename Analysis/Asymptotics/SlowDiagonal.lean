/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Order.Filter.SlowDiagonal

/-!
# Real-valued slow diagonal estimates

This module strengthens the order-theoretic slow diagonal selector with a
real-valued error constraint. It does not depend on regular variation.
-/

@[expose] public section

open Filter

namespace Asymptotics

/-- Along any nonnegative error sequence tending to zero, choose the
fixed-parameter diagonal slowly enough that the parameter times the error
also tends to zero. -/
theorem exists_tendsto_slowDiagonal_mul_tendsto_zero
    {P : ℕ → ℕ → Prop} {r : ℕ → ℝ}
    (hP : ∀ k, ∀ᶠ n : ℕ in atTop, P k n)
    (hr : Tendsto r atTop (nhds 0))
    (hr_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ r n) :
    ∃ d : ℕ → ℕ, Monotone d ∧ Tendsto d atTop atTop ∧
      (∀ᶠ n : ℕ in atTop, P (d n) n) ∧
      Tendsto (fun n => (d n : ℝ) * r n) atTop (nhds 0) := by
  have hcombined : ∀ k, ∀ᶠ n : ℕ in atTop,
      P k n ∧ (k : ℝ) * r n ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have hmul : Tendsto (fun n => (k : ℝ) * r n) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hr
    have hbound : ∀ᶠ n : ℕ in atTop,
        (k : ℝ) * r n < 1 / ((k : ℝ) + 1) :=
      hmul.eventually (Iio_mem_nhds (by positivity))
    exact (hP k).and (hbound.mono fun n hn => le_of_lt hn)
  obtain ⟨d, hmono, hd, hdiag⟩ := Filter.exists_tendsto_slowDiagonal hcombined
  have hproperty : ∀ᶠ n : ℕ in atTop, P (d n) n :=
    hdiag.mono fun n hn => hn.1
  have hbound : ∀ᶠ n : ℕ in atTop,
      (d n : ℝ) * r n ≤ 1 / ((d n : ℝ) + 1) :=
    hdiag.mono fun n hn => hn.2
  have hdcast : Tendsto (fun n => (d n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hd
  have hdplus : Tendsto (fun n => (d n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 hdcast
  have hdenomInv : Tendsto (fun n => ((d n : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hdplus
  have hdenom : Tendsto (fun n => 1 / ((d n : ℝ) + 1)) atTop (nhds 0) := by
    simpa only [one_div] using hdenomInv
  have hproduct_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ (d n : ℝ) * r n :=
    hr_nonneg.mono fun n hn => mul_nonneg (Nat.cast_nonneg _) hn
  exact ⟨d, hmono, hd, hproperty,
    squeeze_zero' hproduct_nonneg hbound hdenom⟩

end Asymptotics

end
