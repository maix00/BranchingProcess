import Combinatorics.UlamHarris.Tree.Truncation
import Mathlib.Data.ENat.Lattice
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The height up to which two trees agree

`heightCongr T T'` is the last generation at which the truncations
`T.truncate n` and `T'.truncate n` agree, valued in `ℕ∞` so that `⊤` records
the coincident case. It is the distance `‖T, T'‖ₕ` and the input of the tree
distance in `Tree/Metric.lean`.

The characteristic property is `coe_le_heightCongr_iff`: the levels `n` with
`(n : ℕ∞) ≤ heightCongr T T'` are exactly the levels at which the truncations
agree. The proof uses the shape of the agreement set rather than the shape of
the supremum: the agreement levels are nonempty (`0` always agrees, since
truncating at level zero discards everything but the root) and downward
closed, so a level that fails to agree forces every agreeing level to lie
below it, which puts the supremum strictly below.
-/

open MeasureTheory

namespace Combinatorics

namespace UlamHarris

namespace Tree

variable {α : Type*} [LT α]

/-- The levels at which the truncations of two trees agree. This is the
`n`-indexed form of `heightCongr`, whose value at `⊤` is read off from
`coe_le_heightCongr_iff`. -/
def agreeLevels (T T' : Tree α) : Set ℕ := {n | T.truncate n = T'.truncate n}

theorem mem_agreeLevels_iff {T T' : Tree α} {n : ℕ} :
    n ∈ agreeLevels T T' ↔ T.truncate n = T'.truncate n := Iff.rfl

/-- Truncating at level zero keeps the root alone, so it carries no
information: all trees have the same level-zero truncation. -/
theorem truncate_zero_eq (T T' : Tree α) : T.truncate 0 = T'.truncate 0 := by
  ext u
  rw [mem_truncate, mem_truncate]
  constructor
  · rintro ⟨hlen, -⟩
    have hu : u = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    exact ⟨hlen, hu ▸ T'.root_mem⟩
  · rintro ⟨hlen, -⟩
    have hu : u = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    exact ⟨hlen, hu ▸ T.root_mem⟩

theorem zero_mem_agreeLevels (T T' : Tree α) : 0 ∈ agreeLevels T T' :=
  truncate_zero_eq T T'

/-- The agreement levels are downward closed: agreement at a level persists
at every lower level, because truncating the agreed truncations again keeps
them equal. -/
theorem agreeLevels_downward {T T' : Tree α} {m n : ℕ}
    (hm : m ∈ agreeLevels T T') (hn : n ≤ m) : n ∈ agreeLevels T T' := by
  have h := congrArg (fun S : Tree α => S.truncate n) hm
  rw [truncate_truncate, truncate_truncate, min_eq_right hn] at h
  exact h

/-- The height up to which two trees agree: the supremum of the levels at
which their truncations agree. It is `⊤` exactly for equal trees and `0` for
trees that first differ at generation one. -/
noncomputable def heightCongr (T T' : Tree α) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : n ∈ agreeLevels T T'), (n : ℕ∞)

/-- The characteristic property of `heightCongr`: a level agrees exactly
when it lies below the height. -/
theorem coe_le_heightCongr_iff {T T' : Tree α} {n : ℕ} :
    (n : ℕ∞) ≤ heightCongr T T' ↔ n ∈ agreeLevels T T' := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hn
    have hnpos : 0 < n :=
      Nat.pos_of_ne_zero fun h0 => hn (h0 ▸ zero_mem_agreeLevels T T')
    have hle : heightCongr T T' ≤ ((n - 1 : ℕ) : ℕ∞) := by
      simp only [heightCongr]
      refine iSup₂_le_iff.2 fun m hm => ?_
      have hmn : m ≤ n - 1 := by
        by_contra hlt
        exact hn (agreeLevels_downward hm (by omega))
      exact_mod_cast hmn
    have hcast : (n : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞) := le_trans h hle
    have : n ≤ n - 1 := ENat.natCast_le_natCast.mp hcast
    omega
  · exact le_iSup₂
      (f := fun m (_ : m ∈ agreeLevels T T') => (m : ℕ∞)) n h

theorem heightCongr_comm (T T' : Tree α) :
    heightCongr T T' = heightCongr T' T := by
  simp only [heightCongr, agreeLevels, Set.mem_ofPred_eq, eq_comm]

@[simp] theorem heightCongr_self (T : Tree α) : heightCongr T T = ⊤ := by
  rw [heightCongr, ← ENat.iSup_natCast]
  refine le_antisymm (iSup₂_le_iff.2 fun n _ => le_iSup (f := fun n : ℕ => (n : ℕ∞)) n) ?_
  exact iSup_le fun n => le_iSup₂
    (f := fun m (_ : m ∈ agreeLevels T T) => (m : ℕ∞)) n rfl

theorem ext_of_forall_truncate_eq {T T' : Tree α}
    (h : ∀ n, T.truncate n = T'.truncate n) : T = T' := by
  ext u
  have := congrArg (fun S : Tree α => u ∈ S.carrier) (h u.length)
  simpa [mem_truncate] using this

/-- Two trees are equal exactly when they agree at every height. -/
theorem heightCongr_eq_top_iff {T T' : Tree α} :
    heightCongr T T' = ⊤ ↔ T = T' := by
  refine ⟨fun h => ext_of_forall_truncate_eq fun n => ?_, fun h => ?_⟩
  · exact coe_le_heightCongr_iff.1 (by rw [h]; exact le_top)
  · subst h
    exact heightCongr_self T

/-- The height is ultrametric: agreement of `T₁` with `T₂` and of `T₂` with
`T₃` up to a level forces agreement of `T₁` with `T₃` up to that level. -/
theorem heightCongr_ultra (T1 T2 T3 : Tree α) :
    min (heightCongr T1 T2) (heightCongr T2 T3) ≤ heightCongr T1 T3 := by
  by_contra hcon
  rw [not_le] at hcon
  have hlt12 : heightCongr T1 T3 < heightCongr T1 T2 :=
    lt_of_lt_of_le hcon (min_le_left _ _)
  have hlt23 : heightCongr T1 T3 < heightCongr T2 T3 :=
    lt_of_lt_of_le hcon (min_le_right _ _)
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (ne_of_lt (hlt12.trans_le le_top))
  have hlt12' : (k : ℕ∞) < heightCongr T1 T2 := by
    rwa [← hk] at hlt12
  have hlt23' : (k : ℕ∞) < heightCongr T2 T3 := by
    rwa [← hk] at hlt23
  have hk12 : ((k + 1 : ℕ) : ℕ∞) ≤ heightCongr T1 T2 := by
    simpa using (ENat.natCast_add_one_le_iff (m := k)
      (n := heightCongr T1 T2)).2 hlt12'
  have hk23 : ((k + 1 : ℕ) : ℕ∞) ≤ heightCongr T2 T3 := by
    simpa using (ENat.natCast_add_one_le_iff (m := k)
      (n := heightCongr T2 T3)).2 hlt23'
  have h13 : ((k + 1 : ℕ) : ℕ∞) ≤ heightCongr T1 T3 :=
    coe_le_heightCongr_iff.2
      ((coe_le_heightCongr_iff.1 hk12).trans (coe_le_heightCongr_iff.1 hk23))
  rw [← hk] at h13
  exact absurd (ENat.natCast_le_natCast.mp h13) (by omega)

end Tree

end UlamHarris

end Combinatorics
