/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Basic
import Mathlib.Topology.Order.IsLUB

/-!
# Range conditions for càdlàg paths

## Public declarations

- `CadlagPath.rangeIn`: the subset of paths whose values satisfy
  `∀ t, path t ∈ range`.
- `IsCadlag.range_subset_of_dense`: if `D` is dense, contains `⊤`, and a
  càdlàg path maps `D` into a closed set `S`, then `Set.range f ⊆ S`.

The path-set definition does not depend on a topology on the space of paths.
The dense-time result is a pathwise extension fact for `IsCadlag` functions;
it uses right continuity and closedness of the target set.
-/

@[expose] public section

open Filter
open scoped Topology

namespace CadlagPath

variable {T E : Type*} [PartialOrder T] [TopologicalSpace T]
  [TopologicalSpace E]

/-- Càdlàg paths whose values all lie in a specified state-space set. -/
def rangeIn (range : Set E) : Set (CadlagPath T E) :=
  {path | ∀ t, path t ∈ range}

end CadlagPath

namespace IsCadlag

/-- A closed range constraint that holds on a dense set of times containing
the top endpoint holds throughout the range of a càdlàg path. -/
theorem range_subset_of_dense
    {T E : Type*} [LinearOrder T] [TopologicalSpace T] [OrderTopology T]
    [DenselyOrdered T] [FirstCountableTopology T] [OrderTop T]
    {D : Set T} (hD : Dense D) (htop : ⊤ ∈ D)
    {path : T → E} [TopologicalSpace E] (hpath : IsCadlag path) {S : Set E}
    (hS : IsClosed S) (hDpath : ∀ t ∈ D, path t ∈ S) :
    Set.range path ⊆ S := by
  rintro _ ⟨t, rfl⟩
  by_cases ht : t = ⊤
  · subst t
    exact hDpath ⊤ htop
  · have httop : t < ⊤ := lt_of_le_of_ne le_top ht
    obtain ⟨u, _, huD, huTendsto⟩ :=
      hD.exists_seq_strictAnti_tendsto_of_lt httop
    have hwithin : Tendsto u atTop (𝓝[Set.Ioi t] t) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨huTendsto, Filter.Eventually.of_forall fun n => (huD n).1.1⟩
    have hvalue : Tendsto (fun n => path (u n)) atTop (𝓝 (path t)) :=
      (hpath.isRightContinuous t).tendsto.comp hwithin
    exact hS.mem_of_tendsto hvalue
      (Filter.Eventually.of_forall fun n => hDpath (u n) (huD n).2)

end IsCadlag

end
