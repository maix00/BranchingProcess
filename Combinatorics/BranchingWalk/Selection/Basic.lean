/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Selection mechanisms

`Mechanism` acts on arbitrary candidate sets and is the mathematical base
interface. `FiniteMechanism` is its finite-input implementation interface for
algorithms using `Finset`.

The abstract concept carries no capacity bound. A mechanism that keeps exactly
`min N s.card` candidates is an `NSelection`, defined in
`Selection/NSelection/Basic.lean`.
`PreservesLeast` and `PreservesGreatest` are the two
order properties that make the leftmost and rightmost rules work; they mention
only `select`, so they belong to the abstract layer.
-/

open Classical

@[expose] public section

namespace Combinatorics

namespace Branching

namespace Selection

variable {ι : Type*}

/-- An abstract selection mechanism on an arbitrary population.  There is no
finiteness, countability, or order assumption on the candidate type. -/
structure Mechanism (ι : Type*) where
  select : Set ι → Set ι
  subset : ∀ s, select s ⊆ s

namespace Mechanism

instance (ι : Type*) : CoeFun (Mechanism ι) (fun _ => Set ι → Set ι) :=
  ⟨Mechanism.select⟩

variable {M M' : Mechanism ι}

@[ext] theorem ext (h : ∀ s, M.select s = M'.select s) : M = M' := by
  have hsel : M.select = M'.select := funext h
  cases M
  cases M'
  simp only at hsel
  cases hsel
  rfl

theorem select_subset (M : Mechanism ι) (s : Set ι) : M.select s ⊆ s :=
  M.subset s

/-- Pointwise selection by a survival predicate.  Killing is this constructor
viewed dynamically: candidates failing `keep` are removed. -/
def filter (keep : ι → Prop) : Mechanism ι where
  select s := {q ∈ s | keep q}
  subset _ _q hq := hq.1

@[simp] theorem mem_filter (keep : ι → Prop) (s : Set ι) (q : ι) :
    q ∈ (filter keep).select s ↔ q ∈ s ∧ keep q :=
  Iff.rfl

@[simp] theorem select_mem (M : Mechanism ι) {s : Set ι} {q : ι}
    (hq : q ∈ M.select s) : q ∈ s :=
  M.subset s hq

end Mechanism

/-- A finite-input implementation of a selection mechanism. -/
structure FiniteMechanism (ι : Type*) where
  /-- The selected sub-collection of a candidate set. -/
  select : Finset ι → Finset ι
  /-- Selection keeps only candidates that were already survive. -/
  subset : ∀ s, select s ⊆ s

namespace FiniteMechanism

instance (ι : Type*) : CoeFun (FiniteMechanism ι) (fun _ => Finset ι → Finset ι) :=
  ⟨FiniteMechanism.select⟩

variable {M M' : FiniteMechanism ι}

/-- Restrict a general mechanism to finite candidate populations. -/
noncomputable def ofMechanism (M : Mechanism ι) : FiniteMechanism ι where
  select s := (s.finite_toSet.subset (M.subset ↑s)).toFinset
  subset s := by
    intro q hq
    have hselected : q ∈ M.select (↑s : Set ι) :=
      (s.finite_toSet.subset (M.subset ↑s)).mem_toFinset.mp hq
    exact M.subset ↑s hselected

@[simp] theorem coe_select_ofMechanism (M : Mechanism ι) (s : Finset ι) :
    ↑((ofMechanism M).select s) = M.select ↑s := by
  classical
  exact (s.finite_toSet.subset (M.subset ↑s)).coe_toFinset

@[ext] theorem ext (h : ∀ s, M.select s = M'.select s) : M = M' := by
  have hsel : M.select = M'.select := funext h
  obtain ⟨sel, sub⟩ := M
  obtain ⟨sel', sub'⟩ := M'
  simp only at hsel
  cases hsel
  rw [Subsingleton.elim sub sub']

theorem select_subset (M : FiniteMechanism ι) (s : Finset ι) :
    M.select s ⊆ s :=
  M.subset s

@[simp] theorem select_mem (M : FiniteMechanism ι) {s : Finset ι} {q : ι}
    (h : q ∈ M.select s) : q ∈ s :=
  M.subset s h

/-- A mechanism preserves the least candidate of every candidate set. The
leftmost-`N` rule has this property, and it is exactly what lets the leftmost
particle survive the selection. -/
def PreservesLeast [LE ι] (M : FiniteMechanism ι) : Prop :=
  ∀ ⦃s : Finset ι⦄ ⦃x : ι⦄, IsLeast (↑s : Set ι) x → x ∈ M.select s

/-- The order-dual property: a mechanism preserves the greatest candidate of
every candidate set. The rightmost-`N` rule has this property. -/
def PreservesGreatest [LE ι] (M : FiniteMechanism ι) : Prop :=
  ∀ ⦃s : Finset ι⦄ ⦃x : ι⦄, IsGreatest (↑s : Set ι) x → x ∈ M.select s

/-- Transport a selection mechanism to the reversed order. The candidate sets
are transported by `OrderDual.ofDual`, selected there, and transported back. -/
noncomputable def mapOrderDual [DecidableEq ι] (M : FiniteMechanism ι) :
    FiniteMechanism (OrderDual ι) where
  select s := (M.select (s.image OrderDual.ofDual)).image OrderDual.toDual
  subset s := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    obtain ⟨r, hr, hrp⟩ := Finset.mem_image.mp (M.subset _ hp)
    rw [← hrp]
    simpa using hr

@[simp] theorem mapOrderDual_select [DecidableEq ι] (M : FiniteMechanism ι)
    (s : Finset (OrderDual ι)) :
    (M.mapOrderDual).select s =
      (M.select (s.image OrderDual.ofDual)).image OrderDual.toDual :=
  rfl

end FiniteMechanism

end Selection

end Branching

end Combinatorics

end
