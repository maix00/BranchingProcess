/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Basic
public import Probability.Independence.Finite
public import Probability.Sequence.IID.StoppingTime
public import Mathlib.Probability.Independence.Basic

/-!
# Laws of increment-coordinate blocks

Distributional and independence results for finite coordinate blocks of an
IID increment sequence. Variable-length blocks are the primary interface;
equal-length statements are specializations.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

variable {E : Type*} [MeasurableSpace E]

/-- The vector of consecutive variable-length blocks, padded by an explicit
default value, is independent of the next block. -/
theorem indepFun_variableConsecutivePaddedBlockCoordinates_next
    (ν : Measure E) [IsProbabilityMeasure ν]
    (length : ℕ → ℕ) (blocks : ℕ) (default : E) :
    IndepFun
      (fun increment (j : Fin blocks) =>
        Combinatorics.Sequence.paddedBlockCoordinates (AdditivePath.blockStart length j.val)
          (length j.val) default increment)
      (Combinatorics.Sequence.paddedBlockCoordinates (AdditivePath.blockStart length blocks)
        (length blocks) default)
      (iidSequenceLaw ν) := by
  classical
  let total := AdditivePath.blockStart length blocks
  let S := Finset.range total
  let T := Finset.Ico total (total + length blocks)
  have hdisjoint : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro k hkS hkT
    simp only [S, T, Finset.mem_range, Finset.mem_Ico] at hkS hkT
    omega
  have htuple := (iidSequenceLaw_independent ν).indepFun_finset S T hdisjoint
    (fun k => measurable_pi_apply k)
  let left : (S → E) → Fin blocks → ℕ → E := fun x j k =>
    if hk : k < length j.val then
      x ⟨AdditivePath.blockStart length j.val + k, Finset.mem_range.mpr (by
        have hstop : AdditivePath.blockStart length j.val + length j.val ≤ total := by
          calc
            AdditivePath.blockStart length j.val + length j.val =
                AdditivePath.blockStart length (j.val + 1) :=
                  (AdditivePath.blockStart_succ length j.val).symm
            _ ≤ total := by
              dsimp [total]
              exact AdditivePath.blockStart_mono length
                (Nat.succ_le_of_lt j.isLt)
        exact lt_of_lt_of_le (Nat.add_lt_add_left hk _) hstop)⟩
    else default
  let right : (T → E) → ℕ → E := fun x k =>
    if hk : k < length blocks then
      x ⟨total + k, Finset.mem_Ico.mpr
        ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hk _⟩⟩
    else default
  have hleftMeasurable : Measurable left := by
    rw [measurable_pi_iff]
    intro j
    rw [measurable_pi_iff]
    intro k
    by_cases hk : k < length j.val
    · simp only [left, dite_eq_left hk]
      exact measurable_pi_apply _
    · simp only [left, dite_eq_right hk]
      exact measurable_const
  have hrightMeasurable : Measurable right := by
    rw [measurable_pi_iff]
    intro k
    by_cases hk : k < length blocks
    · simp only [right, dite_eq_left hk]
      exact measurable_pi_apply _
    · simp only [right, dite_eq_right hk]
      exact measurable_const
  have h := htuple.comp hleftMeasurable hrightMeasurable
  have hleft :
      left ∘ (fun increment (k : S) => increment k) =
        (fun increment (j : Fin blocks) =>
          Combinatorics.Sequence.paddedBlockCoordinates (AdditivePath.blockStart length j.val)
            (length j.val) default increment) := by
    funext increment j k
    by_cases hk : k < length j.val
    · simp [left, Combinatorics.Sequence.paddedBlockCoordinates, hk]
    · simp [left, Combinatorics.Sequence.paddedBlockCoordinates, hk]
  have hright :
      right ∘ (fun increment (k : T) => increment k) =
        Combinatorics.Sequence.paddedBlockCoordinates total (length blocks) default := by
    funext increment k
    by_cases hk : k < length blocks
    · simp [right, total, Combinatorics.Sequence.paddedBlockCoordinates, hk]
    · simp [right, total, Combinatorics.Sequence.paddedBlockCoordinates, hk]
  simpa only [hleft, hright] using h

/-- Any finite family of consecutive variable-length blocks, padded by an
explicit default value, is mutually independent. -/
theorem iIndepFun_variableConsecutivePaddedBlockCoordinates
    (ν : Measure E) [IsProbabilityMeasure ν]
    (length : ℕ → ℕ) (blocks : ℕ) (default : E) :
    iIndepFun (fun (j : Fin blocks) increment =>
      Combinatorics.Sequence.paddedBlockCoordinates (AdditivePath.blockStart length j.val)
        (length j.val) default increment) (iidSequenceLaw ν) := by
  induction blocks with
  | zero => exact iIndepFun.of_subsingleton
  | succ blocks ih =>
      apply iIndepFun.finSucc
      · intro j
        exact (paddedBlockCoordinates_measurable
          (AdditivePath.blockStart length j.val) (length j.val) default).aemeasurable
      · simpa using ih
      · simpa using indepFun_variableConsecutivePaddedBlockCoordinates_next
          ν length blocks default

/-- Any finite family of consecutive variable-length coordinate blocks of an
IID sequence is mutually independent. -/
theorem iIndepFun_variableConsecutiveBlockCoordinates
    (ν : Measure E) [IsProbabilityMeasure ν]
    (length : ℕ → ℕ) (blocks : ℕ) :
    iIndepFun (fun (j : Fin blocks) increment =>
      Combinatorics.Sequence.blockCoordinates (AdditivePath.blockStart length j.val)
        (length j.val) increment) (iidSequenceLaw ν) := by
  classical
  let default : E := Classical.choice (nonempty_of_isProbabilityMeasure ν)
  let restrict : ∀ j : Fin blocks, (ℕ → E) → Fin (length j.val) → E :=
    fun _ x k => x k
  have hrestrict (j : Fin blocks) : Measurable (restrict j) := by
    fun_prop
  have h :=
    (iIndepFun_variableConsecutivePaddedBlockCoordinates ν length blocks default).comp
      restrict hrestrict
  have hEq : (fun (j : Fin blocks) (increment : ℕ → E) => restrict j
      (Combinatorics.Sequence.paddedBlockCoordinates (AdditivePath.blockStart length j.val)
        (length j.val) default increment)) =
      (fun (j : Fin blocks) (increment : ℕ → E) => Combinatorics.Sequence.blockCoordinates
        (AdditivePath.blockStart length j.val) (length j.val) increment) := by
    funext j increment k
    simp [restrict, Combinatorics.Sequence.blockCoordinates, k.isLt]
  rw [← hEq]
  exact h

/-- The vector of the first variable-length coordinate blocks is independent
of the next coordinate block. -/
theorem indepFun_variableConsecutiveBlockCoordinates_next
    (ν : Measure E) [IsProbabilityMeasure ν]
    (length : ℕ → ℕ) (blocks : ℕ) :
    IndepFun
      (fun increment (j : Fin blocks) =>
        Combinatorics.Sequence.blockCoordinates (AdditivePath.blockStart length j.val)
          (length j.val) increment)
      (Combinatorics.Sequence.blockCoordinates (AdditivePath.blockStart length blocks)
        (length blocks))
      (iidSequenceLaw ν) := by
  classical
  let default : E := Classical.choice (nonempty_of_isProbabilityMeasure ν)
  have hleft : Measurable (fun x : Fin blocks → ℕ → E =>
      fun j : Fin blocks => fun k : Fin (length j.val) => x j k) := by
    fun_prop
  have hright : Measurable (fun x : ℕ → E => fun k : Fin (length blocks) => x k) := by
    fun_prop
  have h := (indepFun_variableConsecutivePaddedBlockCoordinates_next
    ν length blocks default).comp hleft hright
  have hleftEq : (fun (increment : ℕ → E) (j : Fin blocks) =>
      fun k : Fin (length j.val) =>
      Combinatorics.Sequence.paddedBlockCoordinates (AdditivePath.blockStart length j.val)
        (length j.val) default increment k) =
      (fun (increment : ℕ → E) (j : Fin blocks) => Combinatorics.Sequence.blockCoordinates
        (AdditivePath.blockStart length j.val) (length j.val) increment) := by
    funext increment j k
    simp [Combinatorics.Sequence.paddedBlockCoordinates, Combinatorics.Sequence.blockCoordinates, k.isLt]
  have hrightEq : (fun (increment : ℕ → E) (k : Fin (length blocks)) =>
      Combinatorics.Sequence.paddedBlockCoordinates (AdditivePath.blockStart length blocks)
        (length blocks) default increment k) =
      Combinatorics.Sequence.blockCoordinates (AdditivePath.blockStart length blocks)
        (length blocks) := by
    funext increment k
    simp [Combinatorics.Sequence.paddedBlockCoordinates, Combinatorics.Sequence.blockCoordinates, k.isLt]
  rw [← hleftEq, ← hrightEq]
  exact h

/-- Equal-length coordinate blocks are a specialization of the variable-length
independence theorem. -/
theorem indepFun_consecutiveBlockCoordinates_next
    (ν : Measure E) [IsProbabilityMeasure ν]
    (blocks length : ℕ) :
    IndepFun
      (fun increment (j : Fin blocks) =>
        Combinatorics.Sequence.blockCoordinates (j * length) length increment)
      (Combinatorics.Sequence.blockCoordinates (blocks * length) length)
      (iidSequenceLaw ν) := by
  simpa only [AdditivePath.blockStart_const] using
    indepFun_variableConsecutiveBlockCoordinates_next ν (fun _ => length) blocks

/-- A finite family of equal-length coordinate blocks is a specialization of
variable-length block independence. -/
theorem iIndepFun_consecutiveBlockCoordinates
    (ν : Measure E) [IsProbabilityMeasure ν]
    (blocks length : ℕ) :
    iIndepFun (fun (j : Fin blocks) increment =>
      Combinatorics.Sequence.blockCoordinates (j * length) length increment) (iidSequenceLaw ν) := by
  simpa only [AdditivePath.blockStart_const] using
    iIndepFun_variableConsecutiveBlockCoordinates ν (fun _ => length) blocks

end ProbabilityTheory.RandomWalk

end
