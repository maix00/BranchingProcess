import Mathlib.Data.Finset.Card
import Mathlib.Order.Bounds.Basic

/-!
# Selection mechanisms on finite candidate sets

The paper's `N`-branching walk keeps `N` particles out of all the offspring at
every generation, and the thesis singles out the rule that keeps the `N`
leftmost ones. The rule itself is not a random object: it is a deterministic
map from a finite candidate set to a sub-collection of at most `N` candidates.
This module is the abstract core of that idea.

`rank s q` counts the candidates of `s` that strictly precede `q`, and
`keepFirst N s` keeps those whose rank is below `N`. For a linear order this is
exactly "the `N` smallest candidates", and the companion `keepLast N s` keeps
the `N` greatest ones.

A selection mechanism can be random in general. This file only contains the
deterministic mechanisms: a random selection mechanism is a law on
`Mechanism`, so it belongs to the probability layer.
-/

open Classical

namespace Combinatorics

namespace Branching

namespace Selection

variable {ι : Type*}

/-- The rank of `q` among the candidates `s`: the number of candidates that
strictly precede it. The candidate type is linearly ordered, so the rank is a
complete invariant of the position of a candidate in the candidate set. -/
noncomputable def rank [LinearOrder ι] (s : Finset ι) (q : ι) : ℕ :=
  (s.filter fun p => p < q).card

theorem rank_def [LinearOrder ι] (s : Finset ι) (q : ι) :
    rank s q = (s.filter fun p => p < q).card :=
  rfl

/-- Keep the `N` smallest candidates. -/
noncomputable def keepFirst [LinearOrder ι] (N : ℕ) (s : Finset ι) : Finset ι :=
  s.filter fun q => rank s q < N

theorem keepFirst_def [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    keepFirst N s = s.filter fun q => rank s q < N :=
  rfl

@[simp] theorem mem_keepFirst_iff [LinearOrder ι] {N : ℕ} {s : Finset ι} {q : ι} :
    q ∈ keepFirst N s ↔ q ∈ s ∧ rank s q < N :=
  Finset.mem_filter

theorem keepFirst_subset [LinearOrder ι] (N : ℕ) (s : Finset ι) : keepFirst N s ⊆ s :=
  Finset.filter_subset (s := s) (p := fun q => rank s q < N)

/-- Keep the `N` greatest candidates. -/
noncomputable def keepLast [LinearOrder ι] (N : ℕ) (s : Finset ι) : Finset ι :=
  s.filter fun q => (s.filter fun p => q < p).card < N

theorem keepLast_def [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    keepLast N s = s.filter fun q => (s.filter fun p => q < p).card < N :=
  rfl

@[simp] theorem mem_keepLast_iff [LinearOrder ι] {N : ℕ} {s : Finset ι} {q : ι} :
    q ∈ keepLast N s ↔ q ∈ s ∧ (s.filter fun p => q < p).card < N :=
  Finset.mem_filter

theorem keepLast_subset [LinearOrder ι] (N : ℕ) (s : Finset ι) : keepLast N s ⊆ s :=
  Finset.filter_subset (s := s) (p := fun q => (s.filter fun p => q < p).card < N)

/-- A selection mechanism of capacity `N`: from every finite candidate set it
selects a sub-collection of at most `N` candidates. The mechanism itself is a
deterministic object; a random selection mechanism is a law on this type. -/
structure Mechanism (ι : Type*) (N : ℕ) where
  /-- The selected sub-collection of a candidate set. -/
  select : Finset ι → Finset ι
  /-- Selection keeps only candidates that were already survive. -/
  subset : ∀ s, select s ⊆ s
  /-- The capacity bound. -/
  card_le : ∀ s, (select s).card ≤ N

instance (ι : Type*) (N : ℕ) :
    CoeFun (Mechanism ι N) (fun _ => Finset ι → Finset ι) :=
  ⟨Mechanism.select⟩

variable {N : ℕ}

@[ext] theorem Mechanism.ext {M M' : Mechanism ι N}
    (h : ∀ s, M.select s = M'.select s) : M = M' := by
  have hsel : M.select = M'.select := funext h
  obtain ⟨sel, sub, card⟩ := M
  obtain ⟨sel', sub', card'⟩ := M'
  simp only at hsel
  cases hsel
  rw [Subsingleton.elim sub sub', Subsingleton.elim card card']

theorem Mechanism.select_subset (M : Mechanism ι N) (s : Finset ι) :
    M.select s ⊆ s :=
  M.subset s

theorem Mechanism.select_card_le (M : Mechanism ι N) (s : Finset ι) :
    (M.select s).card ≤ N :=
  M.card_le s

@[simp] theorem Mechanism.select_mem (M : Mechanism ι N) {s : Finset ι} {q : ι}
    (h : q ∈ M.select s) : q ∈ s :=
  M.subset s h

/-- A mechanism preserves the least candidate of every candidate set. The
leftmost-`N` rule has this property, and it is exactly what lets the leftmost
particle survive the selection. -/
def Mechanism.PreservesLeast [LE ι] (M : Mechanism ι N) : Prop :=
  ∀ ⦃s : Finset ι⦄ ⦃x : ι⦄, IsLeast (↑s : Set ι) x → x ∈ M.select s

/-- The order-dual property: a mechanism preserves the greatest candidate of
every candidate set. The rightmost-`N` rule has this property. -/
def Mechanism.PreservesGreatest [LE ι] (M : Mechanism ι N) : Prop :=
  ∀ ⦃s : Finset ι⦄ ⦃x : ι⦄, IsGreatest (↑s : Set ι) x → x ∈ M.select s

end Selection

end Branching

end Combinatorics
