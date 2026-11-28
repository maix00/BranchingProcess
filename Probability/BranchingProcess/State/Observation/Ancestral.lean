/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.State.Observation.History

/-!
# Ancestral state histories on an existing state tree

## Public declarations

In `ProbabilityTheory.BranchingProcess.State`:

* `ancestralHistory d n u t` reads `(t(u.take k)).getD d`, for `0 ≤ k ≤ n`.
  The default records absent nodes without changing the underlying tree.
* `measurable_ancestralHistory` proves measurability of this finite history
  in the tree's generation information at `|u|`. Prefixes longer than `u`
  simply read `u`, so no relation between `n` and `|u|` is needed.

This is a deterministic observation with arbitrary measurable states and child
indices. It uses the existing state tree and its native generation filtration.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.State

open MeasureTheory Finset Preorder

set_option backward.isDefEq.respectTransparency false

variable {S ι : Type*} [MeasurableSpace S]

/-- Ancestral states through time `n`, with an explicit default for absence. -/
def ancestralHistory (d : S) (n : ℕ) (u : List ι) (t : List ι → Option S) :
    Fin (n + 1) → S := fun k => (t (u.take k)).getD d

/-- All prefixes of `u` are observed by generation `|u|`, including when the
requested finite history extends beyond the length of `u`. -/
theorem measurable_ancestralHistory (d : S) (n : ℕ) (u : List ι) :
    Measurable[treeFiltration u.length] (ancestralHistory d n u) := by
  let m := treeFiltration (S := S) (ι := ι) u.length
  let : MeasurableSpace (List ι → Option S) := m
  change Measurable (ancestralHistory d n u)
  apply measurable_pi_iff.mpr
  intro k
  have hH : Measurable
      (treeHistory (S := S) (ι := ι) u.length) := Measurable.of_comap_le le_rfl
  have hm : Measurable
      (fun t : List ι → Option S => t (u.take k)) := by
    have he := (measurable_pi_apply ((), (u.take k).get)).comp
      ((measurable_pi_apply
        (⟨(u.take k).length, mem_Iic.mpr (by simp)⟩ : Iic u.length)).comp hH)
    change Measurable (fun t : List ι → Option S => treeHistory u.length t
      ⟨(u.take k).length, mem_Iic.mpr (by simp)⟩ ((), (u.take k).get)) at he
    simpa only [treeHistory, List.ofFn_get] using he
  have hget : Measurable (fun o : Option S => o.getD d) := by
    have he : (fun o : Option S => o.getD d) = (fun o => o.elim d id) := by
      funext o
      cases o <;> rfl
    rw [he]
    exact measurable_option_elim d measurable_id
  exact hget.comp hm

end ProbabilityTheory.BranchingProcess.State
