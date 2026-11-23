/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Line.FirstEntrance
public import Mathlib.Data.Set.Lattice.Indexed

/-!
# Suprema in ancestral precedence

## Public declarations

In `Combinatorics.UlamHarris.RootIndexed.Line`:

* `supremum L` is the first entrance into `⋂ i, descendantClosure (L i)`.
* `isLine_supremum` proves that this is a line for any indexed family.
* `descendantClosure_supremum` proves `D_(sup L) = ⋂ i, D_(L i)`.
* `supremum_precedes_iff` is the universal property:
  `sup L ≼ M ↔ ∀ i, L i ≼ M`.
* `precedes_supremum` proves `L i ≼ sup L` for each index.

The family index and root/child types are arbitrary. This uses the ancestral
precedence of A. E. Kyprianou, *Martingale convergence and the stopped branching
random walk* (2000), §2, pp. 408–409, DOI 10.1007/s004409900036.
The universal property is derived from descendant closures and the existing
first-entrance construction. It does not assert coverage of infinite rays.
-/

@[expose] public section

namespace Combinatorics.UlamHarris.RootIndexed.Line

variable {I Root α : Type*}

/-- The earliest frontier belonging to every indexed descendant region. -/
def supremum (L : I → Set (TreeNode Root α)) : Set (TreeNode Root α) :=
  firstEntrance (⋂ i, descendantClosure (L i))

theorem isLine_supremum (L : I → Set (TreeNode Root α)) : IsLine (supremum L) :=
  isLine_firstEntrance _

/-- Intersecting descendant regions gives exactly the supremum's descendant region. -/
theorem descendantClosure_supremum (L : I → Set (TreeNode Root α)) :
    descendantClosure (supremum L) = ⋂ i, descendantClosure (L i) := by
  rw [supremum, descendantClosure_firstEntrance]
  apply Set.Subset.antisymm
  · rintro v ⟨u, hu, huv⟩
    apply Set.mem_iInter.mpr
    intro i
    obtain ⟨w, hw, hwu⟩ := Set.mem_iInter.mp hu i
    exact ⟨w, hw, hwu.trans huv⟩
  · exact subset_descendantClosure _

/-- Least-upper-bound property in the existing ancestral precedence relation. -/
theorem supremum_precedes_iff (L : I → Set (TreeNode Root α)) (M : Set (TreeNode Root α)) :
    Precedes (supremum L) M ↔ ∀ i, Precedes (L i) M := by
  rw [precedes_iff_subset_descendantClosure, descendantClosure_supremum]
  constructor
  · intro h i v hv
    exact Set.mem_iInter.mp (h hv) i
  · intro h v hv
    exact Set.mem_iInter.mpr fun i => h i v hv

theorem precedes_supremum (L : I → Set (TreeNode Root α)) (i : I) :
    Precedes (L i) (supremum L) := by
  intro u hu
  have hd := subset_descendantClosure (supremum L) hu
  rw [descendantClosure_supremum] at hd
  exact Set.mem_iInter.mp hd i

end Combinatorics.UlamHarris.RootIndexed.Line

end
