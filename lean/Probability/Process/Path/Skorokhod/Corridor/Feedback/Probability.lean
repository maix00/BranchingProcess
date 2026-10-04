/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Bounds.Feedback
public import Mathlib.MeasureTheory.Measure.Basic

/-!
# Probability of finite feedback-controlled blocks

This measure-theoretic induction is separate from the pathwise feedback
bound. The product identities are the precise inputs supplied by independence
of each fresh complete block path from the past.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- When either of two fresh-block choices has probability at least `q`,
feedback selection based on the past succeeds for `n` steps with probability
at least `q ^ n`. -/
theorem measure_feedbackSuccess_ge_pow
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (success sign plus minus : ℕ → Set Ω)
    (q qPlus qMinus : ENNReal)
    (hqPlus : q ≤ qPlus) (hqMinus : q ≤ qMinus)
    (hzero : P (success 0) = 1)
    (hmeasSuccess : ∀ k, MeasurableSet (success k))
    (hmeasSign : ∀ k, MeasurableSet (sign k))
    (hmeasPlus : ∀ k, MeasurableSet (plus k))
    (hmeasMinus : ∀ k, MeasurableSet (minus k))
    (hstep : ∀ k,
      (success k ∩ sign k ∩ minus k) ∪
        (success k ∩ (sign k)ᶜ ∩ plus k) ⊆ success (k + 1))
    (hprodMinus : ∀ k,
      P (success k ∩ sign k ∩ minus k) =
        P (success k ∩ sign k) * qMinus)
    (hprodPlus : ∀ k,
      P (success k ∩ (sign k)ᶜ ∩ plus k) =
        P (success k ∩ (sign k)ᶜ) * qPlus) :
    ∀ n, q ^ n ≤ P (success n) := by
  intro n
  induction n with
  | zero => simp [hzero]
  | succ k ih =>
    let A := success k ∩ sign k ∩ minus k
    let B := success k ∩ (sign k)ᶜ ∩ plus k
    have hdisjoint : Disjoint A B := by
      apply Set.disjoint_left.mpr
      intro ω hA hB
      exact hB.1.2 hA.1.2
    have hmeasA : MeasurableSet A :=
      ((hmeasSuccess k).inter (hmeasSign k)).inter (hmeasMinus k)
    have hmeasB : MeasurableSet B :=
      ((hmeasSuccess k).inter ((hmeasSign k).compl)).inter (hmeasPlus k)
    have hsplit : P (success k ∩ sign k) +
        P (success k ∩ (sign k)ᶜ) = P (success k) := by
      rw [← measure_union]
      · congr 1
        ext ω
        simp
      · exact Set.disjoint_left.mpr (by
          intro ω hω hω'
          exact hω'.2 hω.2)
      · exact (hmeasSuccess k).inter ((hmeasSign k).compl)
    have hbound : P (success k) * q ≤ P (A ∪ B) := by
      rw [measure_union hdisjoint hmeasB, hprodMinus k, hprodPlus k,
        ← hsplit]
      rw [add_mul]
      exact add_le_add
        (by simpa [mul_comm] using
          mul_le_mul_right hqMinus (P (success k ∩ sign k)))
        (by simpa [mul_comm] using
          mul_le_mul_right hqPlus (P (success k ∩ (sign k)ᶜ)))
    calc
      q ^ (k + 1) = q ^ k * q := pow_succ q k
      _ ≤ P (success k) * q := by
        simpa [mul_comm] using mul_le_mul_right ih q
      _ ≤ P (A ∪ B) := hbound
      _ ≤ P (success (k + 1)) := measure_mono (hstep k)

/-- A fixed finite number of feedback choices therefore has strictly
positive probability whenever both fresh-block choices do. -/
theorem measure_feedbackSuccess_pos
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (success sign plus minus : ℕ → Set Ω)
    (q qPlus qMinus : ENNReal) (hq : 0 < q)
    (hqPlus : q ≤ qPlus) (hqMinus : q ≤ qMinus)
    (hzero : P (success 0) = 1)
    (hmeasSuccess : ∀ k, MeasurableSet (success k))
    (hmeasSign : ∀ k, MeasurableSet (sign k))
    (hmeasPlus : ∀ k, MeasurableSet (plus k))
    (hmeasMinus : ∀ k, MeasurableSet (minus k))
    (hstep : ∀ k,
      (success k ∩ sign k ∩ minus k) ∪
        (success k ∩ (sign k)ᶜ ∩ plus k) ⊆ success (k + 1))
    (hprodMinus : ∀ k,
      P (success k ∩ sign k ∩ minus k) =
        P (success k ∩ sign k) * qMinus)
    (hprodPlus : ∀ k,
      P (success k ∩ (sign k)ᶜ ∩ plus k) =
        P (success k ∩ (sign k)ᶜ) * qPlus)
    (n : ℕ) : 0 < P (success n) :=
  (ENNReal.pow_pos hq n).trans_le
    (measure_feedbackSuccess_ge_pow P success sign plus minus q qPlus qMinus
      hqPlus hqMinus hzero hmeasSuccess hmeasSign hmeasPlus hmeasMinus
      hstep hprodMinus hprodPlus n)

end ProbabilityTheory

end
