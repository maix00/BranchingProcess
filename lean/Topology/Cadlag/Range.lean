/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Basic

/-!
# Range conditions for càdlàg paths

This file defines the set of càdlàg paths whose values lie in a given subset
of the state space. The definition only uses the path and state-space types;
it does not depend on a topology on path space.
-/

@[expose] public section

namespace CadlagPath

variable {T E : Type*} [PartialOrder T] [TopologicalSpace T]
  [TopologicalSpace E]

/-- Càdlàg paths whose values all lie in a specified state-space set. -/
def rangeIn (range : Set E) : Set (CadlagPath T E) :=
  {path | ∀ t, path t ∈ range}

end CadlagPath

end
