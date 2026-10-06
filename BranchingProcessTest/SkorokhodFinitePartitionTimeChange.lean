/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Topology.Cadlag.Skorokhod.TimeChange.FinitePartition.Homeomorph

#print axioms Skorokhod.TimeChange.FinitePartition.ofMatchingPartitions
#print axioms Skorokhod.TimeChange.FinitePartition.ofMatchingPartitions_distortion_le
#print axioms Skorokhod.TimeChange.FinitePartition.act_ofMatchingPartitions_stepPath
#print axioms Skorokhod.TimeChange.FinitePartition.j1EDist_stepPath_le_ofMatchingPartitions

example {n : ℕ} (hn : 0 < n) (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source)
    (htargetFirst : target ⟨0, by omega⟩ = ⊥)
    (htargetLast : target ⟨n, by omega⟩ = ⊤)
    (htargetStrict : StrictMono target) (ε : ℝ)
    (hpoints : ∀ j, dist (source j) (target j) ≤ ε) :
    (Skorokhod.TimeChange.FinitePartition.ofMatchingPartitions hn source target
      hsourceFirst hsourceLast hsourceStrict htargetFirst htargetLast htargetStrict).distortion ≤ ε :=
  Skorokhod.TimeChange.FinitePartition.ofMatchingPartitions_distortion_le hn source target
    hsourceFirst hsourceLast hsourceStrict htargetFirst htargetLast htargetStrict ε hpoints
