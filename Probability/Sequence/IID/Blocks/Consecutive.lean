/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Sequence.Block
public import Probability.Independence.Finite
public import Probability.Sequence.IID.Basic
public import Mathlib.Probability.Independence.Basic

/-!
# Independence of consecutive blocks in an IID sequence

The public theorems in this file concern a canonical IID sequence
$(X_n)_{n\geq 0}$ with one-coordinate law $\nu$:

- `indepFun_blockCoordinates_blockCoordinates` proves
  $\operatorname{IndepFun}((X_{s+k})_{k<m},(X_{s+m+k})_{k<n})$.
- `indepFun_variableConsecutiveBlockCoordinates_next` proves independence of
  $( (X_{b_j+k})_{k<\ell_j})_{j<q}$ and $(X_{b_q+k})_{k<\ell_q}$, where
  $b_j=\sum_{i<j}\ell_i$.
- `iIndepFun_variableConsecutiveBlockCoordinates` proves mutual independence
  of the finite family $((X_{b_j+k})_{k<\ell_j})_{j<q}$.
- `iidSequenceLaw_measure_forall_variableConsecutiveBlockEvent` proves
  $\mathbb P(\forall j<q,\,(X_{b_j+k})_{k<\ell_j}\in A_j)
    =\prod_{j<q}\mathbb P((X_k)_{k<\ell_j}\in A_j)$ for measurable $A_j$.
- `iidSequenceLaw_measure_forall_consecutiveBlockEvent` specializes this to
  equal block lengths and one common event, giving the corresponding power
  $\mathbb P(\forall j<q,\,(X_{jm+k})_{k<m}\in A)
    =\mathbb P((X_k)_{k<m}\in A)^q$.

These statements require only the IID sequence law; they do not require
addition on the state space or path regularity.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E]

/-- Two consecutive finite coordinate blocks of an IID sequence are
independent. -/
theorem indepFun_blockCoordinates_blockCoordinates
    (ν : Measure E) [IsProbabilityMeasure ν]
    (start m n : ℕ) :
    IndepFun (Combinatorics.Sequence.blockCoordinates (E := E) start m)
      (Combinatorics.Sequence.blockCoordinates (start + m) n) (iidSequenceLaw ν) := by
  let S := Finset.Ico start (start + m)
  let T := Finset.Ico (start + m) (start + m + n)
  have hdisjoint : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro k hkS hkT
    simp only [S, T, Finset.mem_Ico] at hkS hkT
    omega
  have htuple := (iidSequenceLaw_independent ν).indepFun_finset S T hdisjoint
    (fun k => measurable_pi_apply k)
  let left : (S → E) → (Fin m → E) := fun x k =>
    x ⟨start + k, by simp [S, k.isLt]⟩
  let right : (T → E) → (Fin n → E) := fun x k =>
    x ⟨start + m + k, by simp [T, k.isLt]⟩
  have hleftMeasurable : Measurable left := by
    rw [measurable_pi_iff]
    intro k
    exact measurable_pi_apply _
  have hrightMeasurable : Measurable right := by
    rw [measurable_pi_iff]
    intro k
    exact measurable_pi_apply _
  have h := htuple.comp hleftMeasurable hrightMeasurable
  convert h using 1 <;> funext sequence k <;>
    simp [left, right, Combinatorics.Sequence.blockCoordinates, Nat.add_assoc]

/-- The vector of consecutive variable-length blocks, padded by an explicit
default value, is independent of the next block. -/
private theorem indepFun_variableConsecutivePaddedBlockCoordinates_next
    (ν : Measure E) [IsProbabilityMeasure ν]
    (length : ℕ → ℕ) (blocks : ℕ) (default : E) :
    IndepFun
      (fun increment (j : Fin blocks) =>
        Combinatorics.Sequence.paddedBlockCoordinates (Combinatorics.Sequence.blockStart length j.val)
          (length j.val) default increment)
      (Combinatorics.Sequence.paddedBlockCoordinates (Combinatorics.Sequence.blockStart length blocks)
        (length blocks) default)
      (iidSequenceLaw ν) := by
  classical
  let total := Combinatorics.Sequence.blockStart length blocks
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
      x ⟨Combinatorics.Sequence.blockStart length j.val + k, Finset.mem_range.mpr (by
        have hstop : Combinatorics.Sequence.blockStart length j.val + length j.val ≤ total := by
          calc
            Combinatorics.Sequence.blockStart length j.val + length j.val =
                Combinatorics.Sequence.blockStart length (j.val + 1) :=
                  (Combinatorics.Sequence.blockStart_succ length j.val).symm
            _ ≤ total := by
              dsimp [total]
              exact Combinatorics.Sequence.blockStart_mono length
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
          Combinatorics.Sequence.paddedBlockCoordinates (Combinatorics.Sequence.blockStart length j.val)
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
private theorem iIndepFun_variableConsecutivePaddedBlockCoordinates
    (ν : Measure E) [IsProbabilityMeasure ν]
    (length : ℕ → ℕ) (blocks : ℕ) (default : E) :
    iIndepFun (fun (j : Fin blocks) increment =>
      Combinatorics.Sequence.paddedBlockCoordinates (Combinatorics.Sequence.blockStart length j.val)
        (length j.val) default increment) (iidSequenceLaw ν) := by
  induction blocks with
  | zero => exact iIndepFun.of_subsingleton
  | succ blocks ih =>
      apply iIndepFun.finSucc
      · intro j
        exact (paddedBlockCoordinates_measurable
          (Combinatorics.Sequence.blockStart length j.val) (length j.val) default).aemeasurable
      · simpa using ih
      · simpa using indepFun_variableConsecutivePaddedBlockCoordinates_next
          ν length blocks default

/-- Any finite family of consecutive variable-length coordinate blocks of an
IID sequence is mutually independent. -/
theorem iIndepFun_variableConsecutiveBlockCoordinates
    (ν : Measure E) [IsProbabilityMeasure ν]
    (length : ℕ → ℕ) (blocks : ℕ) :
    iIndepFun (fun (j : Fin blocks) increment =>
      Combinatorics.Sequence.blockCoordinates (Combinatorics.Sequence.blockStart length j.val)
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
      (Combinatorics.Sequence.paddedBlockCoordinates (Combinatorics.Sequence.blockStart length j.val)
        (length j.val) default increment)) =
      (fun (j : Fin blocks) (increment : ℕ → E) => Combinatorics.Sequence.blockCoordinates
        (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment) := by
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
        Combinatorics.Sequence.blockCoordinates (Combinatorics.Sequence.blockStart length j.val)
          (length j.val) increment)
      (Combinatorics.Sequence.blockCoordinates (Combinatorics.Sequence.blockStart length blocks)
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
      Combinatorics.Sequence.paddedBlockCoordinates (Combinatorics.Sequence.blockStart length j.val)
        (length j.val) default increment k) =
      (fun (increment : ℕ → E) (j : Fin blocks) => Combinatorics.Sequence.blockCoordinates
        (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment) := by
    funext increment j k
    simp [Combinatorics.Sequence.paddedBlockCoordinates, Combinatorics.Sequence.blockCoordinates, k.isLt]
  have hrightEq : (fun (increment : ℕ → E) (k : Fin (length blocks)) =>
      Combinatorics.Sequence.paddedBlockCoordinates (Combinatorics.Sequence.blockStart length blocks)
        (length blocks) default increment k) =
      Combinatorics.Sequence.blockCoordinates (Combinatorics.Sequence.blockStart length blocks)
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
  simpa only [Combinatorics.Sequence.blockStart_const] using
    indepFun_variableConsecutiveBlockCoordinates_next ν (fun _ => length) blocks

/-- A finite family of equal-length coordinate blocks is a specialization of
variable-length block independence. -/
theorem iIndepFun_consecutiveBlockCoordinates
    (ν : Measure E) [IsProbabilityMeasure ν]
    (blocks length : ℕ) :
    iIndepFun (fun (j : Fin blocks) increment =>
      Combinatorics.Sequence.blockCoordinates (j * length) length increment) (iidSequenceLaw ν) := by
  simpa only [Combinatorics.Sequence.blockStart_const] using
    iIndepFun_variableConsecutiveBlockCoordinates ν (fun _ => length) blocks


/-- Under an IID increment law, the probability that every one of finitely
many consecutive equal-length coordinate blocks belongs to the same
measurable set is the corresponding power of the one-block probability.

The statement is phrased for any measurable finite-block event; applications
such as block oscillation can then use it without reproving the product-law
calculation. -/
theorem iidSequenceLaw_measure_forall_consecutiveBlockEvent
    (ν : Measure E) [IsProbabilityMeasure ν]
    (blocks length : ℕ) (event : Set (Fin length → E))
    (hmeas : MeasurableSet event) :
    iidSequenceLaw ν {increment : ℕ → E | ∀ j : Fin blocks,
        Combinatorics.Sequence.blockCoordinates (j * length) length increment ∈ event} =
      (iidSequenceLaw ν {increment : ℕ → E |
        Combinatorics.Sequence.blockCoordinates 0 length increment ∈ event}) ^ blocks := by
  let blockMap : Fin blocks → (ℕ → E) → (Fin length → E) := fun j =>
    Combinatorics.Sequence.blockCoordinates (j * length) length
  let allBlocks : (ℕ → E) → (Fin blocks → Fin length → E) := fun increment j =>
    blockMap j increment
  let productSet : Set (Fin blocks → Fin length → E) :=
    Set.univ.pi fun _ : Fin blocks => event
  have hblockMeasurable (j : Fin blocks) : Measurable (blockMap j) :=
    measurable_blockCoordinates (j * length) length
  have hallBlocksMeasurable : Measurable allBlocks := by
    rw [measurable_pi_iff]
    exact fun j => (hblockMeasurable j).comp measurable_id
  have hindep := iIndepFun_consecutiveBlockCoordinates ν blocks length
  have hmap : (iidSequenceLaw ν).map allBlocks =
      Measure.pi fun j : Fin blocks => (iidSequenceLaw ν).map (blockMap j) :=
    (iIndepFun_iff_map_fun_eq_pi_map
      (fun j => (hblockMeasurable j).aemeasurable)).mp hindep
  have hproductSet : MeasurableSet productSet :=
    MeasurableSet.pi Set.countable_univ fun _ _ => hmeas
  have hevent :
      {increment : ℕ → E | ∀ j : Fin blocks, blockMap j increment ∈ event} =
        allBlocks ⁻¹' productSet := by
    ext increment
    simp [productSet, allBlocks, blockMap, Set.mem_pi]
  have hshift (j : Fin blocks) :
      (iidSequenceLaw ν).map (blockMap j) event =
        (iidSequenceLaw ν).map
          (Combinatorics.Sequence.blockCoordinates 0 length) event := by
    exact congrArg (fun measure : Measure (Fin length → E) => measure event)
      (iidSequenceLaw_map_blockCoordinates ν (j * length) length)
  calc
    _ = (iidSequenceLaw ν).map allBlocks productSet := by
      change (iidSequenceLaw ν)
          {increment : ℕ → E | ∀ j : Fin blocks, blockMap j increment ∈ event} = _
      rw [hevent]
      exact (Measure.map_apply hallBlocksMeasurable hproductSet).symm
    _ = (Measure.pi fun j : Fin blocks =>
          (iidSequenceLaw ν).map (blockMap j)) productSet := by rw [hmap]
    _ = ∏ j : Fin blocks, (iidSequenceLaw ν).map (blockMap j) event := by
      change (Measure.pi fun j : Fin blocks =>
          (iidSequenceLaw ν).map (blockMap j))
        (Set.univ.pi fun _ : Fin blocks => event) = _
      rw [Measure.pi_pi]
    _ = ∏ _j : Fin blocks, (iidSequenceLaw ν).map
          (Combinatorics.Sequence.blockCoordinates 0 length) event := by
      apply Finset.prod_congr rfl
      intro j hj
      exact hshift j
    _ = ((iidSequenceLaw ν).map
          (Combinatorics.Sequence.blockCoordinates 0 length) event) ^ blocks := by
      simp
    _ = _ := by
      rw [Measure.map_apply (measurable_blockCoordinates 0 length) hmeas]
      rfl

/-- Under an IID increment law, a finite family of consecutive blocks may
have different lengths and different measurable block events. The joint
probability is the product of the corresponding one-block probabilities.

This is the finite-partition form of block independence used when a
piecewise-constant corridor is cut at its finitely many jump times. -/
theorem iidSequenceLaw_measure_forall_variableConsecutiveBlockEvent
    (ν : Measure E) [IsProbabilityMeasure ν]
    (length : ℕ → ℕ) (blocks : ℕ)
    (event : ∀ j : Fin blocks, Set (Fin (length j.val) → E))
    (hmeas : ∀ j, MeasurableSet (event j)) :
    iidSequenceLaw ν {increment : ℕ → E | ∀ j : Fin blocks,
        Combinatorics.Sequence.blockCoordinates
          (Combinatorics.Sequence.blockStart length j.val) (length j.val) increment ∈ event j} =
      ∏ j : Fin blocks, iidSequenceLaw ν {increment : ℕ → E |
        Combinatorics.Sequence.blockCoordinates 0 (length j.val) increment ∈ event j} := by
  let blockMap : (j : Fin blocks) → (ℕ → E) → (Fin (length j.val) → E) :=
    fun j => Combinatorics.Sequence.blockCoordinates
      (Combinatorics.Sequence.blockStart length j.val) (length j.val)
  let allBlocks : (ℕ → E) → ∀ j : Fin blocks, Fin (length j.val) → E :=
    fun increment j => blockMap j increment
  let productSet : Set (∀ j : Fin blocks, Fin (length j.val) → E) :=
    Set.univ.pi event
  have hblockMeasurable (j : Fin blocks) : Measurable (blockMap j) :=
    measurable_blockCoordinates _ _
  have hallBlocksMeasurable : Measurable allBlocks := by
    rw [measurable_pi_iff]
    exact fun j => (hblockMeasurable j).comp measurable_id
  have hindep := iIndepFun_variableConsecutiveBlockCoordinates ν length blocks
  have hmap : (iidSequenceLaw ν).map allBlocks =
      Measure.pi fun j : Fin blocks => (iidSequenceLaw ν).map (blockMap j) :=
    (iIndepFun_iff_map_fun_eq_pi_map
      (fun j => (hblockMeasurable j).aemeasurable)).mp hindep
  have hproductSet : MeasurableSet productSet :=
    MeasurableSet.pi Set.countable_univ fun j _ => hmeas j
  have hevent :
      {increment : ℕ → E | ∀ j : Fin blocks, blockMap j increment ∈ event j} =
        allBlocks ⁻¹' productSet := by
    ext increment
    simp [productSet, allBlocks, Set.mem_pi]
  have hshift (j : Fin blocks) :
      (iidSequenceLaw ν).map (blockMap j) (event j) =
        (iidSequenceLaw ν).map
          (Combinatorics.Sequence.blockCoordinates 0 (length j.val)) (event j) := by
    exact congrArg (fun μ : Measure (Fin (length j.val) → E) => μ (event j))
      (iidSequenceLaw_map_blockCoordinates ν (Combinatorics.Sequence.blockStart length j.val)
        (length j.val))
  calc
    _ = (iidSequenceLaw ν).map allBlocks productSet := by
      change iidSequenceLaw ν
          {increment : ℕ → E | ∀ j : Fin blocks, blockMap j increment ∈ event j} = _
      rw [hevent]
      exact (Measure.map_apply hallBlocksMeasurable hproductSet).symm
    _ = (Measure.pi fun j : Fin blocks =>
          (iidSequenceLaw ν).map (blockMap j)) productSet := by rw [hmap]
    _ = ∏ j : Fin blocks, (iidSequenceLaw ν).map (blockMap j) (event j) := by
      change (Measure.pi fun j : Fin blocks =>
        (iidSequenceLaw ν).map (blockMap j)) (Set.univ.pi event) = _
      rw [Measure.pi_pi]
    _ = ∏ j : Fin blocks, (iidSequenceLaw ν).map
          (Combinatorics.Sequence.blockCoordinates 0 (length j.val)) (event j) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact hshift j
    _ = ∏ j : Fin blocks, iidSequenceLaw ν {increment : ℕ → E |
          Combinatorics.Sequence.blockCoordinates 0 (length j.val) increment ∈ event j} := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [Measure.map_apply (measurable_blockCoordinates 0 (length j.val)) (hmeas j)]
      rfl
    _ = _ := rfl


end ProbabilityTheory

end
