/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.State.Observation.Basic
public import Mathlib.Probability.Process.Filtration

/-!
# Generation information of a state tree

## Public declarations

In `ProbabilityTheory.BranchingProcess.State`:

* `treeHistory n t` reads all states through depth `n` from the existing tree.
* `measurable_treeHistory` proves that this observation is measurable.
* `treeHistory_restrict` identifies a shorter history with the native restriction
  of a longer one: `H_m = restrict H_n` when `m ≤ n`.
* `treeFiltration` is the native filtration `F_n = σ(treeHistory n)`.
* `treeFiltration_apply` gives its defining sigma algebra.

These are deterministic observations, with arbitrary measurable states and child
indices; no new process, probability law or state recursion is introduced.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.State

open MeasureTheory Finset Preorder

variable {S ι : Type*} [MeasurableSpace S]

/-- The states through a fixed generation, read from the same complete tree. -/
def treeHistory (n : ℕ) (t : List ι → Option S)
    (_k : Iic n) (p : Unit × (Fin _k.1 → ι)) : Option S := t (List.ofFn p.2)

@[fun_prop]
theorem measurable_treeHistory (n : ℕ) : Measurable (treeHistory (S := S) (ι := ι) n) := by
  unfold treeHistory
  fun_prop

omit [MeasurableSpace S] in
theorem treeHistory_restrict {m n : ℕ} (hmn : m ≤ n) (t : List ι → Option S) :
    treeHistory m t = fun k : Iic m => treeHistory n t
      ⟨k.1, mem_Iic.mpr ((mem_Iic.mp k.2).trans hmn)⟩ := rfl

/-- Information of the state tree through generation `n`. -/
def treeFiltration : Filtration ℕ (inferInstance : MeasurableSpace (List ι → Option S)) where
  seq n := MeasurableSpace.comap (treeHistory n) inferInstance
  mono' := by
    intro m n hmn
    let r (x : Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S) :=
      fun k : Iic m => x ⟨k.1, mem_Iic.mpr ((mem_Iic.mp k.2).trans hmn)⟩
    have hr : Measurable r := by fun_prop
    change MeasurableSpace.comap (r ∘ treeHistory n) _ ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hr.comap_le
  le' n := (measurable_treeHistory n).comap_le

@[simp]
theorem treeFiltration_apply (n : ℕ) : treeFiltration (S := S) (ι := ι) n =
    MeasurableSpace.comap (treeHistory n) inferInstance := rfl

end ProbabilityTheory.BranchingProcess.State
