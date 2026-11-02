/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.MetricSpace.Isometry
public import Topology.Cadlag.Skorokhod.Topology
import all Topology.Cadlag.Skorokhod.EDistance.Basic

/-!
# Range-subtype maps on Skorokhod path space

## Public declarations

- `Skorokhod.j1EDist_forgetRange`: for paths `f g : D([0,1], A)`,
  `j1EDist (f.forgetRange) (g.forgetRange) = j1EDist f g`.
- `Skorokhod.isometry_forgetRange`: the map
  `f ↦ f.forgetRange : D([0,1], A) → D([0,1], E)` is an isometry.

The state-space subset `A` need not be closed: forgetting the subtype
preserves the path's càdlàg property and the `J₁` distance.

For subtype-valued paths, forgetting the range preserves distance exactly:
\(\operatorname{j1EDist}(f.\mathrm{forgetRange},g.\mathrm{forgetRange})
=\operatorname{j1EDist}(f,g)\).
-/

@[expose] public section

open scoped ENNReal

namespace Skorokhod

/-- Forgetting a state-range subtype preserves the extended `J₁` distance. -/
theorem j1EDist_forgetRange {E : Type*} [MetricSpace E] {range : Set E}
    (f g : CadlagPath unitInterval range) :
    j1EDist f.forgetRange g.forgetRange = j1EDist f g := by
  have huniform (u v : CadlagPath unitInterval range) :
      uniformEDist u.forgetRange v.forgetRange = uniformEDist u v := by
    rw [uniformEDist_eq_edist, uniformEDist_eq_edist,
      UniformFun.edist_def, UniformFun.edist_def]
    apply iSup_congr
    intro t
    simp [CadlagPath.forgetRange_apply, Subtype.edist_eq]
  have hcost (change : TimeChange) :
      j1Cost f.forgetRange g.forgetRange change = j1Cost f g change := by
    unfold j1Cost
    have hact (u : CadlagPath unitInterval range) :
        (change.act u).forgetRange = change.act u.forgetRange := by
      ext t
      rfl
    rw [← hact f, huniform]
  unfold j1EDist
  exact iInf_congr hcost

/-- Forgetting a state-range subtype is an isometry of Skorokhod path spaces. -/
theorem isometry_forgetRange {E : Type*} [MetricSpace E] {range : Set E} :
    Isometry (fun f : CadlagPath unitInterval range => f.forgetRange) := by
  intro f g
  change edist f.forgetRange g.forgetRange = edist f g
  simp only [edist_cadlagPath_eq_j1EDist, j1EDist_forgetRange]

end Skorokhod

end
