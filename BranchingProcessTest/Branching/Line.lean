import Combinatorics.UlamHarris.Line.Order
import Combinatorics.UlamHarris.Tree.Defs
import Combinatorics.BranchingWalk.Population.Line

open Combinatorics.UlamHarris

-- A line can mix generations, and need not contain any root.
example : IsLine ({[0], [1, 0], [1, 1]} : Set (List ℕ)) := by
  simp [IsLine, IsAntichain, Set.Pairwise]

-- Local lines need not meet every infinite path, even in the full tree.
example : ¬ MeetsEveryRay Set.univ ({[0]} : Set (List ℕ)) := by
  intro h
  obtain ⟨n, hn⟩ := h (fun _ => 1) (fun _ => Set.mem_univ _)
  have heq := Set.mem_singleton_iff.mp hn
  have hlen : n = 1 := by simpa using congrArg List.length heq
  subst n
  simp [lineagePrefix] at heq

-- The empty line covers a tree with no infinite paths: coverage does not
-- impose a requirement on its finite terminal branches.
example : MeetsEveryRay ({[]} : Set (List ℕ)) ∅ := by
  intro f hf
  have h := hf 1
  simp [lineagePrefix] at h

-- The same address at different roots represents incomparable individuals.
example : ¬ RootIndexed.IsAncestor (0, [1, 2]) (1, [1, 2, 3]) := by
  simp [RootIndexed.IsAncestor]

-- All roots form a line, including when there are infinitely many roots.
example : RootIndexed.IsLine {p : RootIndexed.TreeNode ℕ ℕ | p.2 = []} :=
  (RootIndexed.isLine_generation 0).subset (by intro p hp; simp [hp])

-- Native Mathlib antichain operations remain available without wrappers.
example (C : Set (List ℕ)) : IsLine (C ∩ {u | u.length = 4}) :=
  (isLine_generation 4).subset Set.inter_subset_right

-- A realized generation is a line and meets every realized infinite path once.
example (T : Combinatorics.UlamHarris.Tree ℕ) (n : ℕ) (f : ℕ → ℕ) (hf : IsRay T.carrier f) :
    ∃! k, lineagePrefix f k ∈ T.carrier ∩ {u | u.length = n} :=
  (IsLine.meetsEveryRay_iff_existsUnique
    ((isLine_generation n).subset Set.inter_subset_right)).mp
      (meetsEveryRay_generation T.carrier n) f hf

-- The actual population interface gives the same exactly-once assertion,
-- with arbitrary root and mark types and no finite-population assumption.
example {Root α Mark : Type*} {stepField : Root → Combinatorics.Branching.StepField α Mark}
    (P : Combinatorics.Branching.Population stepField) (n : ℕ) (r : Root)
    (f : ℕ → α) (hf : IsRay {u | ∃ k, (r, u) ∈ P k} f) :
    ∃! k, (r, lineagePrefix f k) ∈ P n :=
  (P.isLine n).meetsEveryRay_iff_existsUnique.mp (P.meetsEveryRay n) r f hf

-- Prefix restoration identifies a unique ancestor and suffix even when the
-- members of the line live in different generations.
example {Root α : Type*} {L : Set (RootIndexed.TreeNode Root α)}
    (h : RootIndexed.IsLine L) :
    Function.Injective (fun p : L × TreeNode α => (p.1.1.1, p.1.1.2 ++ p.2)) :=
  h.appendAddresses_injective

#print axioms Combinatorics.UlamHarris.RootIndexed.IsLine.appendAddresses_injective
#print axioms Combinatorics.UlamHarris.RootIndexed.Line.Precedes.antisymm
#print axioms Combinatorics.UlamHarris.RootIndexed.Line.Precedes.meetsEveryRay
#print axioms Combinatorics.Branching.Population.meetsEveryRay
