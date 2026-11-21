/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Line.Basic
public import Combinatorics.UlamHarris.Ray

/-!
# Lines and coverage of infinite paths

## Public declarations

In `Combinatorics.UlamHarris`:

* `MeetsEveryRay C L` means every `f` with `IsRay C f` has a prefix in `L`.
  `MeetsEveryRay.mono` enlarges `L`; `MeetsEveryRay.restrict` restricts `C`.
* `IsLine.ray_index_unique` states that if the prefixes at `n` and `m`
  both belong to a line `L`, then `n = m`.
* `IsLine.meetsEveryRay_iff_existsUnique` states that coverage by a line
  is equivalent to meeting each realized infinite path exactly once.
* `meetsEveryRay_generation` proves that `C ∩ {u | u.length = n}` meets
  every infinite path in `C`; it uses no finite-branching assumption.

In `Combinatorics.UlamHarris.RootIndexed`:

* `MeetsEveryRay C L` requires the same coverage separately at every root.
* `IsLine.meetsEveryRay_iff_existsUnique` gives exactly one meeting generation
  for every root and every infinite path in its fiber.
* `meetsEveryRay_generation` proves the corresponding forest-generation result.

A line is only an ancestry antichain. Coverage is additional, and is vacuous
for a node set having no infinite paths. It does not assert that every finite
terminal branch meets the line. The terminology for lines follows
A. E. Kyprianou, *Martingale convergence and the stopped branching random walk*
(2000), §2, p. 408, [DOI:10.1007/s004409900036](https://doi.org/10.1007/s004409900036).
-/

@[expose] public section

namespace Combinatorics.UlamHarris

variable {α : Type*}

/-- Each infinite path realized in `C` meets `L`. This is separate from being a line. -/
def MeetsEveryRay (C L : Set (TreeNode α)) : Prop :=
  ∀ f, IsRay C f → ∃ n, lineagePrefix f n ∈ L

theorem MeetsEveryRay.mono {C L M : Set (TreeNode α)}
    (h : MeetsEveryRay C L) (hLM : L ⊆ M) : MeetsEveryRay C M := by
  intro f hf
  obtain ⟨n, hn⟩ := h f hf
  exact ⟨n, hLM hn⟩

theorem MeetsEveryRay.restrict {C D L : Set (TreeNode α)}
    (h : MeetsEveryRay C L) (hDC : D ⊆ C) : MeetsEveryRay D L :=
  fun f hf => h f (hf.mono hDC)

/-- A line has at most one member on any infinite path. -/
theorem IsLine.ray_index_unique {L : Set (TreeNode α)} (hL : IsLine L)
    (f : ℕ → α) {n m : ℕ} (hn : lineagePrefix f n ∈ L)
    (hm : lineagePrefix f m ∈ L) : n = m := by
  have heq : lineagePrefix f n = lineagePrefix f m := by
    rcases le_total n m with h | h
    · exact hL.eq hn hm (lineagePrefix_prefix f h)
    · exact (hL.eq hm hn (lineagePrefix_prefix f h)).symm
  simpa using congrArg List.length heq

theorem IsLine.meetsEveryRay_iff_existsUnique {C L : Set (TreeNode α)}
    (hL : IsLine L) : MeetsEveryRay C L ↔
      ∀ f, IsRay C f → ∃! n, lineagePrefix f n ∈ L := by
  constructor
  · intro h f hf
    obtain ⟨n, hn⟩ := h f hf
    exact ⟨n, hn, fun m hm => hL.ray_index_unique f hm hn⟩
  · intro h f hf
    exact (h f hf).exists

/-- Every infinite path passes through its generation-`n` prefix. -/
theorem meetsEveryRay_generation (C : Set (TreeNode α)) (n : ℕ) :
    MeetsEveryRay C (C ∩ {u | u.length = n}) := by
  intro f hf
  exact ⟨n, hf n, length_lineagePrefix f n⟩

namespace RootIndexed

variable {Root : Type*}

/-- Every infinite path in every root fiber meets the specified forest node set. -/
def MeetsEveryRay (C L : Set (TreeNode Root α)) : Prop :=
  ∀ r, UlamHarris.MeetsEveryRay {u | (r, u) ∈ C} {u | (r, u) ∈ L}

theorem IsLine.meetsEveryRay_iff_existsUnique {C L : Set (TreeNode Root α)}
    (hL : IsLine L) : MeetsEveryRay C L ↔
      ∀ r f, IsRay {u | (r, u) ∈ C} f → ∃! n, (r, lineagePrefix f n) ∈ L := by
  exact forall_congr' (fun r =>
    ((isLine_iff_fibers.mp hL) r).meetsEveryRay_iff_existsUnique)

theorem meetsEveryRay_generation (C : Set (TreeNode Root α)) (n : ℕ) :
    MeetsEveryRay C (C ∩ {p | p.2.length = n}) :=
  fun r => UlamHarris.meetsEveryRay_generation {u | (r, u) ∈ C} n

end RootIndexed
end Combinatorics.UlamHarris

end
