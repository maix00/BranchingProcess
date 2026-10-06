/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Endpoint

/-!
# Endpoint-window Portmanteau API checks

These adapters transfer a normalized-step functional limit to strict/open and
weak/closed horizontal tubes with the corresponding terminal window.
-/

#print axioms
  ProbabilityTheory.RandomWalk.measure_centeredSkorokhodCorridorEndsIn_le_liminf_strictTubeEndsIn_of_functionalLimit

#print axioms
  ProbabilityTheory.RandomWalk.limsup_weakTubeEndsIn_le_measure_centeredSkorokhodCorridorEndsIn_of_functionalLimit
