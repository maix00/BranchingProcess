module

public import Combinatorics.BranchingWalk.Population.Basic
public import Combinatorics.BranchingWalk.Basic.ParentSibling

/-!
# Genealogy of populations

The results apply to arbitrary set-valued populations; finite populations
inherit them by forgetting their representation.
-/

@[expose] public section

namespace Combinatorics.Branching.Population

open Combinatorics.UlamHarris

variable {Root α X : Type*} {stepField : Root → StepField α X}

theorem initial_mem_and_surviveAlong (P : Population stepField) :
    ∀ {n : ℕ} {p : RootIndexed.TreeNode Root α},
      p ∈ P n →
        (p.1, []) ∈ P 0 ∧ surviveAlong (stepField p.1) [] p.2 := by
  intro n
  induction n with
  | zero =>
      intro p hp
      have hnil : p.2 = [] := by simpa using P.depth 0 p hp
      have hp_eq : p = (p.1, []) := Prod.ext rfl hnil
      rw [hp_eq] at hp ⊢
      exact ⟨hp, surviveAlong_nil _ _⟩
  | succ n ih =>
      intro q hq
      have hchild := P.successor n hq
      obtain ⟨p, hp, i, hi, rfl⟩ :=
        Selection.Coupling.mem_offspringAddressSet.mp hchild
      have hparent := ih hp
      exact ⟨hparent.1,
        (surviveAlong_root_append_singleton_iff (stepField p.1) p.2 i).2
          ⟨hparent.2, hi⟩⟩

theorem initial_mem_of_mem (P : Population stepField)
    {n : ℕ} {p : RootIndexed.TreeNode Root α} (hp : p ∈ P n) :
    (p.1, []) ∈ P 0 :=
  (P.initial_mem_and_surviveAlong hp).1

theorem surviveAlong_of_mem (P : Population stepField)
    {n : ℕ} {p : RootIndexed.TreeNode Root α} (hp : p ∈ P n) :
    surviveAlong (stepField p.1) [] p.2 :=
  (P.initial_mem_and_surviveAlong hp).2

theorem parent_mem_of_mem_succ (P : Population stepField)
    {n : ℕ} {q : RootIndexed.TreeNode Root α} (hq : q ∈ P (n + 1)) :
    parent q ∈ P n := by
  have hchild := P.successor n hq
  obtain ⟨p, hp, i, hi, rfl⟩ :=
    Selection.Coupling.mem_offspringAddressSet.mp hchild
  simpa [Selection.Coupling.childAddress] using hp

theorem prefix_mem_of_mem (P : Population stepField) :
    ∀ {n : ℕ} {p : RootIndexed.TreeNode Root α},
      p ∈ P n → ∀ k ≤ n, (p.1, p.2.take k) ∈ P k := by
  intro n
  induction n with
  | zero =>
      intro p hp k hk
      have hk0 : k = 0 := by omega
      subst k
      simpa using P.initial_mem_of_mem hp
  | succ n ih =>
      intro p hp k hk
      by_cases htop : k = n + 1
      · subst k
        have hlength : p.2.length = n + 1 := P.depth (n + 1) p hp
        rw [(List.take_eq_self_iff p.2).mpr hlength.le]
        exact hp
      · have hk' : k ≤ n := by omega
        have hparent := P.parent_mem_of_mem_succ hp
        have hprefix := ih hparent k hk'
        have hlength : p.2.length = n + 1 := P.depth (n + 1) p hp
        have hne : p.2 ≠ [] := by
          intro hempty
          simp [hempty] at hlength
        have hdropLength : p.2.dropLast.length = n := by
          rw [List.length_dropLast, hlength]
          omega
        have htake : p.2.take k = p.2.dropLast.take k := by
          calc
            p.2.take k =
                (p.2.dropLast ++ [p.2.getLast hne]).take k := by
              rw [List.dropLast_append_getLast hne]
            _ = p.2.dropLast.take k :=
              List.take_append_of_le_length (by simpa [hdropLength] using hk')
        simpa [parent, htake] using hprefix

end Combinatorics.Branching.Population
