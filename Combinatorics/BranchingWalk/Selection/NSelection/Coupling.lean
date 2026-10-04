/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Selection.NSelection.Coupling.Finite
public import Combinatorics.BranchingWalk.Selection.NSelection.Coupling.Step
public import Combinatorics.BranchingWalk.Selection.NSelection.AtRank

/-!
# Capacity-N selection coupling

This is the public entry point for coupling statements specific to selection
of at most the first `N` particles.  General offspring-set and spatial
coupling facts live in `Selection.Coupling` and do not depend on a capacity.
-/
