/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.TimeChange.FinitePartition.SecantSlope
public import Topology.Cadlag.Skorokhod.TimeChange.LogDistortion

/-!
# Logarithmic distortion of finite-partition clocks

Piecewise-affine clocks matching two close finite partitions have small
logarithmic distortion.
-/

@[expose] public section

open scoped ENNReal

namespace Skorokhod.TimeChange.FinitePartition

/-- If corresponding knots of two partitions are close, and the target cells
have a positive minimum length, the piecewise-affine matching clock has small
logarithmic distortion. -/
theorem ofMatchingPartitions_logDistortion_le {n : ℕ} (hn : 0 < n)
    (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source)
    (htargetFirst : target ⟨0, by omega⟩ = ⊥)
    (htargetLast : target ⟨n, by omega⟩ = ⊤)
    (htargetStrict : StrictMono target) (mesh δ : ℝ)
    (hmesh : 0 < mesh) (hδ : 0 ≤ δ) (hδsmall : δ < mesh / 8)
    (hgap : ∀ i : Fin n, mesh ≤ dist (target i.castSucc) (target i.succ))
    (hpoints : ∀ i : Fin (n + 1), dist (source i) (target i) ≤ δ) :
    (ofMatchingPartitions hn source target hsourceFirst hsourceLast hsourceStrict
      htargetFirst htargetLast htargetStrict).logDistortion ≤
      ENNReal.ofReal
        (max (Real.log (1 + 4 * δ / mesh)) (-Real.log (1 - 4 * δ / mesh))) := by
  have hq_lt : 4 * δ / mesh < 1 := by
    rw [div_lt_iff₀ hmesh]
    nlinarith
  exact TimeChange.logDistortion_le_of_secantSlope_mem_Icc
    (ofMatchingPartitions hn source target hsourceFirst hsourceLast hsourceStrict
      htargetFirst htargetLast htargetStrict) hq_lt
    (ofMatchingPartitions_secantSlope_mem_Icc hn source target hsourceFirst hsourceLast
      hsourceStrict htargetFirst htargetLast htargetStrict mesh δ hmesh hδ hδsmall
      hgap hpoints)

end Skorokhod.TimeChange.FinitePartition

end
