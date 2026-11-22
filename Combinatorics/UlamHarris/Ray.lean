/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Basic

/-!
# Infinite paths of tree addresses

## Public declarations

In `Combinatorics.UlamHarris`:

* `lineagePrefix f n` is the address `[f 0, …, f (n-1)]`;
  `lineagePrefix_zero`, `lineagePrefix_succ`, and `length_lineagePrefix`
  give its empty prefix, one-step extension, and length `n`.
* `lineagePrefix_prefix` states `n ≤ m → lineagePrefix f n <+: lineagePrefix f m`.
* `IsRay C f` means `∀ n, lineagePrefix f n ∈ C`: all prefixes of the
  infinite child-index sequence `f` belong to the node set `C`.
  `IsRay.mono` states `C ⊆ D → IsRay C f → IsRay D f`.

No order, finite branching, or survival law is required. In particular,
`IsRay T.carrier f` describes a realized infinite path of a deterministic
Ulam--Harris tree, and the same predicate works for a tree with arbitrary
child-index gaps.
-/

@[expose] public section

namespace Combinatorics.UlamHarris

variable {α : Type*}

/-- The first `n` entries of an infinite sequence of child indices. -/
def lineagePrefix (lineage : ℕ → α) (n : ℕ) : TreeNode α :=
  match n with
  | 0 => []
  | n + 1 => lineagePrefix lineage n ++ [lineage n]

@[simp] theorem lineagePrefix_zero (f : ℕ → α) : lineagePrefix f 0 = [] := rfl

@[simp] theorem lineagePrefix_succ (f : ℕ → α) (n : ℕ) :
    lineagePrefix f (n + 1) = lineagePrefix f n ++ [f n] := rfl

@[simp] theorem length_lineagePrefix (f : ℕ → α) (n : ℕ) :
    (lineagePrefix f n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

theorem lineagePrefix_prefix (f : ℕ → α) {n m : ℕ} (hnm : n ≤ m) :
    lineagePrefix f n <+: lineagePrefix f m := by
  induction hnm with
  | refl => exact List.prefix_rfl
  | step _ ih => exact ih.trans (List.prefix_append _ _)

/-- An infinite path all of whose finite prefixes belong to the specified node set. -/
def IsRay (C : Set (TreeNode α)) (f : ℕ → α) : Prop :=
  ∀ n, lineagePrefix f n ∈ C

theorem IsRay.mono {C D : Set (TreeNode α)} {f : ℕ → α}
    (hf : IsRay C f) (hCD : C ⊆ D) : IsRay D f := fun n => hCD (hf n)

end Combinatorics.UlamHarris

end
