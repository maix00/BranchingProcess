/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Selection.Coupling.Offspring.Address
public import Combinatorics.BranchingWalk.StepField
public import Combinatorics.BranchingWalk.Step.Basic

/-!
# Populations in a branching field

A population is indexed by the natural-number generations of one fixed
branching field.  It contains no probability space, filtration, measurability,
position, order, or selection mechanism.
-/

@[expose] public section

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

/-- A set-valued population following a fixed root-indexed branching field. -/
structure Population {Root α X : Type*}
    (stepField : Root → StepField α X) where
  particles : ℕ → Set (RootIndexed.TreeNode Root α)
  depth : ∀ n p, p ∈ particles n → p.2.length = n
  successor : ∀ n,
    particles (n + 1) ⊆
      Selection.Coupling.offspringAddressSet (particles n)
        (fun p => support (stepField p.1 p.2))

namespace Population

variable {Root α X : Type*} {stepField : Root → StepField α X}

instance : CoeFun (Population stepField)
    (fun _ => ℕ → Set (RootIndexed.TreeNode Root α)) :=
  ⟨Population.particles⟩

/-- Layerwise finiteness is a property of a population, rather than a
restriction on the underlying set-valued population type. -/
def FiniteSlices (P : Population stepField) : Prop :=
  ∀ n, (P n).Finite

namespace FiniteSlices

/-- A finite representation of one slice, constructed only when an operation
actually needs `Finset`. -/
noncomputable def toFinset {P : Population stepField}
    (hP : P.FiniteSlices) (n : ℕ) :
    Finset (RootIndexed.TreeNode Root α) :=
  (hP n).toFinset

@[simp] theorem mem_toFinset {P : Population stepField}
    (hP : P.FiniteSlices) (n : ℕ)
    (p : RootIndexed.TreeNode Root α) :
    p ∈ hP.toFinset n ↔ p ∈ P n :=
  Set.Finite.mem_toFinset _

@[simp] theorem coe_toFinset {P : Population stepField}
    (hP : P.FiniteSlices) (n : ℕ) :
    ↑(hP.toFinset n) = P n :=
  Set.Finite.coe_toFinset _

end FiniteSlices

end Population
end Combinatorics.Branching
