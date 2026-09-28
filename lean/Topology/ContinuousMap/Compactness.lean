import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Defs.Induced

/-!
# Compact families of continuous paths

This file records the Arzelà--Ascoli consequence used for tightness of
continuous stochastic-process laws.  It is deterministic and independent of
any probability model.
-/

open Set

namespace ContinuousMap

/-- An equicontinuous family of continuous maps whose values are uniformly
bounded in a proper metric state space has compact closure.  The bound is
pointwise uniform over the whole family and the whole time domain. -/
theorem isCompact_closure_of_equicontinuous_of_bounded
    {T E : Type*} [TopologicalSpace T] [CompactlyCoherentSpace T]
    [MetricSpace E] [ProperSpace E]
    (S : Set C(T, E)) (hS : Equicontinuous ((↑) : S → T → E))
    (origin : E) (radius : ℝ)
    (hbound : ∀ f ∈ S, ∀ t, dist (f t) origin ≤ radius) :
    IsCompact (closure S) := by
  let 𝔖 : Set (Set T) := {K | IsCompact K}
  let F : C(T, E) → T → E := (↑)
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (𝔖 := 𝔖) (F := F)
  · intro K hK
    exact hK
  · change Topology.IsClosedEmbedding
      (ContinuousMap.toUniformOnFunIsCompact :
        C(T, E) → UniformOnFun T E {K | IsCompact K})
    constructor
    · exact ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding
    · rw [ContinuousMap.range_toUniformOnFunIsCompact]
      exact UniformOnFun.isClosed_setOfPred_continuous
        CompactlyCoherentSpace.isCoherentWith
  · intro K hK
    exact hS.equicontinuousOn K
  · intro K hK t ht
    refine ⟨Metric.closedBall origin radius,
      isCompact_closedBall origin radius, ?_⟩
    intro f hf
    exact hbound f hf t

end ContinuousMap
