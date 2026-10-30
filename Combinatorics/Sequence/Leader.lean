/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Order.Basic
import Mathlib.Data.Nat.Find

/-!
# Leaders in finite sequences of partial sums

## Public declarations

* `Combinatorics.Sequence.leaderIndices`: the indices `u < n` for which some later partial sum
  satisfies `S j < S u`.
* `Combinatorics.Sequence.sum_leaders_nonpos`: for partial sums in a linearly ordered additive
  commutative group,
  `∑ u ∈ leaderIndices S n, (S (u + 1) - S u) ≤ 0`.

The second statement is Riesz's combinatorial lemma about leaders, in the partial-sum formulation
of Lemma 3.2 in Anders Karlsson, “A Proof of the Subadditive Ergodic Theorem,” Chapter 12 of
*Groups, Graphs and Random Walks*, London Mathematical Society Lecture Note Series 436, Cambridge
University Press (2017), pp. 343–354, DOI 10.1017/9781316576571.014. The proof is by finite induction;
the statement uses only the ordered additive structure of the values.
-/

@[expose] public section

namespace Combinatorics.Sequence

/-- Indices `u < n` for which a later partial sum is strictly below `S u`. -/
noncomputable def leaderIndices {α : Type*} [LinearOrder α] (S : ℕ → α) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun u => ∃ j, u < j ∧ j ≤ n ∧ S j < S u)

private def natShiftEmbedding (s : ℕ) : ℕ ↪ ℕ :=
  ⟨fun n => n + s, fun _ _ h => Nat.add_right_cancel h⟩

@[simp] private theorem natShiftEmbedding_apply (s n : ℕ) :
    natShiftEmbedding s n = n + s := rfl

private theorem mem_leaderIndices_shift {α : Type*} [LinearOrder α]
    (S : ℕ → α) (s n u : ℕ) (hsn : s ≤ n) :
    (u + s ∈ leaderIndices S n ∧ s ≤ u + s) ↔
      u ∈ leaderIndices (fun j => S (j + s)) (n - s) := by
  classical
  simp only [leaderIndices, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, j, hj1, hj2, hj3⟩, _⟩
    refine ⟨by omega, j - s, by omega, by omega, ?_⟩
    rwa [Nat.sub_add_cancel (by omega)]
  · rintro ⟨hu, j, hj1, hj2, hj3⟩
    refine ⟨⟨by omega, j + s, by omega, by omega, hj3⟩, by omega⟩

/-- **Riesz's leader lemma** (Karlsson, Lemma 3.2), in partial-sum form. Given
`S : ℕ → α`, an index `u < n` is a leader when some later value is strictly below `S u`.
The sum of the increments `S (u+1) - S u` over all such indices is nonpositive. The values may
lie in any linearly ordered additive commutative group. -/
theorem sum_leaders_nonpos {α : Type*} [AddCommGroup α] [LinearOrder α]
    [IsOrderedAddMonoid α] :
    ∀ (n : ℕ) (S : ℕ → α),
      ∑ u ∈ leaderIndices S n, (S (u + 1) - S u) ≤ 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S
    match n with
    | 0 => simp [leaderIndices]
    | n + 1 =>
      classical
      by_cases h0 : (0 : ℕ) ∈ leaderIndices S (n + 1)
      · simp only [leaderIndices, Finset.mem_filter, Finset.mem_range] at h0
        obtain ⟨_, j0, hj01, hj02, hj03⟩ := h0
        set P : ℕ → Prop := fun j => j ≤ n + 1 ∧ S j < S 0 with hP
        have hPex : ∃ j, P j := ⟨j0, hj02, hj03⟩
        set k : ℕ := Nat.find hPex with hk
        have hkP : P k := Nat.find_spec hPex
        have hk0 : 0 < k := by
          rcases Nat.eq_zero_or_pos k with h | h
          · exfalso
            rw [h] at hkP
            exact lt_irrefl _ hkP.2
          · exact h
        have hkle : k ≤ n + 1 := hkP.1
        have hkmin : ∀ m, m < k → ¬ P m := fun m hm => Nat.find_min hPex hm
        have hbeat : ∀ i, i < k → S k < S i := by
          intro i hik
          rcases Nat.eq_zero_or_pos i with hi0 | _
          · subst hi0
            exact hkP.2
          · have hSi : S 0 ≤ S i := by
              by_contra hlt
              rw [not_le] at hlt
              exact hkmin i hik ⟨by omega, hlt⟩
            exact lt_of_lt_of_le hkP.2 hSi
        have hprefix : ∀ i, i < k → i ∈ leaderIndices S (n + 1) := by
          intro i hik
          simp only [leaderIndices, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, k, hik, hkle, hbeat i hik⟩
        rw [← Finset.sum_filter_add_sum_filter_not (leaderIndices S (n + 1)) (fun u => u < k)
          (fun u => S (u + 1) - S u)]
        have hpref_eq : (leaderIndices S (n + 1)).filter (fun u => u < k) = Finset.range k := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
          intro hu
          exact hprefix u hu
        rw [hpref_eq, Finset.sum_range_sub S k]
        have htail :
            ∑ u ∈ (leaderIndices S (n + 1)).filter (fun u ↦ ¬ u < k),
                (S (u + 1) - S u) ≤ 0 := by
          set S' : ℕ → α := fun j => S (j + k) with hS'
          have hmap : (leaderIndices S (n + 1)).filter (fun u ↦ ¬ u < k) =
              (leaderIndices S' (n + 1 - k)).map (natShiftEmbedding k) := by
            ext u
            simp only [Finset.mem_filter, Finset.mem_map, natShiftEmbedding_apply, not_lt]
            constructor
            · rintro ⟨hmem, hku⟩
              refine ⟨u - k, ?_, by omega⟩
              have := (mem_leaderIndices_shift S k (n + 1) (u - k) hkle).1
              rw [Nat.sub_add_cancel hku] at this
              exact this ⟨hmem, by omega⟩
            · rintro ⟨v, hv, rfl⟩
              refine ⟨?_, by omega⟩
              exact ((mem_leaderIndices_shift S k (n + 1) v hkle).2 hv).1
          rw [hmap, Finset.sum_map]
          simp only [natShiftEmbedding_apply]
          have hval : ∀ v, S (v + k + 1) - S (v + k) = S' (v + 1) - S' v := by
            intro v
            simp [hS', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          simp_rw [hval]
          exact ih (n + 1 - k) (by omega) S'
        have hpref : S k - S 0 ≤ 0 := sub_nonpos.mpr hkP.2.le
        exact add_nonpos hpref htail
      · set S' : ℕ → α := fun j => S (j + 1) with hS'
        have hmap : leaderIndices S (n + 1) =
            (leaderIndices S' n).map (natShiftEmbedding 1) := by
          ext u
          simp only [Finset.mem_map, natShiftEmbedding_apply]
          constructor
          · intro hmem
            have hu0 : u ≠ 0 := by
              rintro rfl
              exact h0 hmem
            refine ⟨u - 1, ?_, by omega⟩
            have := (mem_leaderIndices_shift S 1 (n + 1) (u - 1) (by omega)).1
            rw [Nat.sub_add_cancel (by omega)] at this
            exact this ⟨hmem, by omega⟩
          · rintro ⟨v, hv, rfl⟩
            exact ((mem_leaderIndices_shift S 1 (n + 1) v (by omega)).2 hv).1
        rw [hmap, Finset.sum_map]
        simp only [natShiftEmbedding_apply]
        have hval : ∀ v, S (v + 1 + 1) - S (v + 1) = S' (v + 1) - S' v :=
          fun v => by simp [hS', Nat.add_comm, Nat.add_left_comm]
        simp_rw [hval]
        exact ih n (by omega) S'

end Combinatorics.Sequence
