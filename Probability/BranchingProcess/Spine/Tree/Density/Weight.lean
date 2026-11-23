/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.LocalBias.Weight
public import Mathlib.Data.Fin.Tuple.Take

/-!
# Fixed-address ancestral weights

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `addressWeight h n z x` is the product of the successive child/parent
  weight ratios along the fixed address `z` through the finite history `x`.
  A ratio is zero when its parent has zero or infinite weight; `W₀ = 1`.
* `addressWeight_zero` and `addressWeight_succ` give its inherited recursion.
* `measurable_addressWeight` proves measurability for any measurable `h`.
* `totalWeight h n x = ∑_z W_z(x)` is the total density;
  `measurable_totalWeight` proves its measurability for countable child slots.
* `addressWeight_eq_endpointRatio` proves
  `W_z = 1_{eligible strict ancestors} h(x_z)/h(x_root)` for an eligible root.

This is the ancestral density used in Zhan Shi, *Branching Random Walks*
(2015), §4.5, (4.12)–(4.13), DOI 10.1007/978-3-319-25372-5.
The weight includes the entire ancestral eligibility condition. Ordinary
branches that leave and later reenter the eligible region do not regain
spinal weight. Zero-offspring families remain part of the original law.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.Branching Finset Preorder
open scoped ENNReal

/-- Successive fixed-child Radon--Nikodym ratios, with eligibility checked at each parent. -/
noncomputable def addressWeight {S ι : Type*} (h : S → ℝ≥0∞) (n : ℕ)
    (z : Fin n → ι) (x : Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S) : ℝ≥0∞ :=
  LocalBias.addressWeight (LocalBias.ofWeight h) n z x

private lemma stepWeight_ofWeight {S ι : Type*} (h : S → ℝ≥0∞)
    (o : Option S) (ξ : Step ι S) (i : ι) :
    LocalBias.stepWeight (LocalBias.ofWeight h) o ξ i =
      if o.elim 0 h ≠ 0 ∧ o.elim 0 h ≠ ∞ then
        (ξ i).elim 0 h / o.elim 0 h else 0 := by
  classical
  cases o with
  | none => simp [LocalBias.stepWeight]
  | some s =>
    by_cases hz : h s = 0 <;> by_cases ht : h s = ∞ <;>
      simp [LocalBias.stepWeight, LocalBias.ofWeight, LocalBias.weighted, hz, ht]

@[simp] theorem addressWeight_zero {S ι : Type*} (h : S → ℝ≥0∞)
    (z : Fin 0 → ι) (x : Π k : Iic 0, (Unit × (Fin k.1 → ι)) → Option S) :
    addressWeight h 0 z x = 1 := rfl

/-- The ratio-product recursion is inherited from the general local-bias product. -/
theorem addressWeight_succ {S ι : Type*} (h : S → ℝ≥0∞) (n : ℕ)
    (z : Fin (n + 1) → ι)
    (x : Π k : Iic (n + 1), (Unit × (Fin k.1 → ι)) → Option S) :
    addressWeight h (n + 1) z x =
      addressWeight h n (Fin.init z) (fun k => x ⟨k.1, mem_Iic.mpr
        ((mem_Iic.mp k.2).trans (Nat.le_succ n))⟩) *
      if (x ⟨n, by simp⟩ ((), Fin.init z)).elim 0 h ≠ 0 ∧
          (x ⟨n, by simp⟩ ((), Fin.init z)).elim 0 h ≠ ∞ then
        (x ⟨n + 1, by simp⟩ ((), z)).elim 0 h /
          (x ⟨n, by simp⟩ ((), Fin.init z)).elim 0 h else 0 := by
  unfold addressWeight
  rw [LocalBias.addressWeight, stepWeight_ofWeight]
  simp only [Fin.snoc_init_self]

@[fun_prop]
theorem measurable_addressWeight {S ι : Type*} [MeasurableSpace S]
    {h : S → ℝ≥0∞} (hh : Measurable h) (n : ℕ) (z : Fin n → ι) :
    Measurable (addressWeight h n z) :=
  LocalBias.measurable_addressWeight (LocalBias.ofWeight h)
    ((hh (MeasurableSet.singleton 0).compl).inter
      (hh (MeasurableSet.singleton ∞).compl))
    (fun i => ((measurable_option_elim 0 hh).comp
      ((measurable_pi_apply i).comp measurable_snd)).div (hh.comp measurable_fst)) n z

/-- Total fixed-address density at a generation. -/
noncomputable def totalWeight {S ι : Type*} (h : S → ℝ≥0∞) (n : ℕ)
    (x : Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S) : ℝ≥0∞ :=
  ∑' z : Fin n → ι, addressWeight h n z x

@[fun_prop]
theorem measurable_totalWeight {S ι : Type*} [MeasurableSpace S] [Countable ι]
    {h : S → ℝ≥0∞} (hh : Measurable h) (n : ℕ) : Measurable (totalWeight (ι := ι) h n) :=
  Measurable.tsum (fun z => measurable_addressWeight hh n z)

/-- On eligible ancestors the successive ratios telescope to the endpoint/root ratio. -/
theorem addressWeight_eq_endpointRatio {S ι : Type*} (h : S → ℝ≥0∞) (n : ℕ)
    (z : Fin n → ι) (x : Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S)
    (hroot : (x ⟨0, by simp⟩ ((), fun j : Fin 0 => j.elim0)).elim 0 h ≠ 0 ∧
      (x ⟨0, by simp⟩ ((), fun j : Fin 0 => j.elim0)).elim 0 h ≠ ∞) :
    addressWeight h n z x =
      if ∀ k : Fin n,
          (x ⟨k.1, mem_Iic.mpr (Nat.le_of_lt k.isLt)⟩
            ((), Fin.take k.1 (Nat.le_of_lt k.isLt) z)).elim 0 h ≠ 0 ∧
          (x ⟨k.1, mem_Iic.mpr (Nat.le_of_lt k.isLt)⟩
            ((), Fin.take k.1 (Nat.le_of_lt k.isLt) z)).elim 0 h ≠ ∞ then
        (x ⟨n, by simp⟩ ((), z)).elim 0 h /
          (x ⟨0, by simp⟩ ((), fun j : Fin 0 => j.elim0)).elim 0 h else 0 := by
  classical
  induction n with
  | zero =>
    have hz : z = (fun j : Fin 0 => j.elim0) := Subsingleton.elim _ _
    simp [addressWeight_zero, hz, ENNReal.div_self hroot.1 hroot.2]
  | succ n ih =>
    let x' : Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S :=
      fun k => x ⟨k.1, mem_Iic.mpr ((mem_Iic.mp k.2).trans n.le_succ)⟩
    have hi := ih (Fin.init z) x' hroot
    rw [addressWeight_succ, hi]
    simp only [Fin.forall_fin_succ']
    simp only [Fin.val_castSucc, Fin.take_init, Fin.val_last, Fin.take_eq_init]
    dsimp only [x']
    let A : Prop := ∀ k : Fin n,
      (x ⟨k.1, mem_Iic.mpr ((Nat.le_of_lt k.isLt).trans n.le_succ)⟩
        ((), Fin.take k.1 ((Nat.le_of_lt k.isLt).trans n.le_succ) z)).elim 0 h ≠ 0 ∧
      (x ⟨k.1, mem_Iic.mpr ((Nat.le_of_lt k.isLt).trans n.le_succ)⟩
        ((), Fin.take k.1 ((Nat.le_of_lt k.isLt).trans n.le_succ) z)).elim 0 h ≠ ∞
    let a := (x ⟨n, by simp⟩ ((), Fin.init z)).elim 0 h
    let b := (x ⟨0, by simp⟩ ((), fun j : Fin 0 => j.elim0)).elim 0 h
    let c := (x ⟨n + 1, by simp⟩ ((), z)).elim 0 h
    let B : Prop := a ≠ 0 ∧ a ≠ ∞
    change (if A then a / b else 0) * (if B then c / a else 0) =
      if A ∧ B then c / b else 0
    by_cases ha : A <;> by_cases hb : B <;>
      simp only [ha, hb, and_self, true_and, false_and, ite_true, ite_false, mul_zero, zero_mul]
    change a ≠ 0 ∧ a ≠ ∞ at hb
    simp only [div_eq_mul_inv]
    calc
      _ = c * b⁻¹ * (a * a⁻¹) := by ac_rfl
      _ = _ := by rw [ENNReal.mul_inv_cancel hb.1 hb.2, mul_one]

end ProbabilityTheory.BranchingProcess.Spine

end
