import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Defs.Induced

/-!
# Compact families of continuous paths

This file records the Arzelà--Ascoli consequence used for tightness of
continuous stochastic-process laws.  It is deterministic and independent of
any probability model.
-/

open Filter Set
open scoped Topology

namespace ContinuousMap

/-- A continuous map obeys one prescribed local oscillation bound. -/
def HasOscillationBound {T E : Type*} [PseudoMetricSpace T]
    [PseudoMetricSpace E] (delta epsilon : ℝ) (f : C(T, E)) : Prop :=
  ∀ s t, dist s t < delta → dist (f s) (f t) ≤ epsilon

/-- A continuous map obeys a prescribed global modulus when its oscillation
between any two points is bounded by the modulus evaluated at their
distance. -/
def HasUniformModulus {T E : Type*} [PseudoMetricSpace T]
    [PseudoMetricSpace E] (modulus : ℝ → ℝ) (f : C(T, E)) : Prop :=
  ∀ s t, dist (f s) (f t) ≤ modulus (dist s t)

/-- All continuous maps sharing a modulus that vanishes at zero form an
equicontinuous family. -/
theorem equicontinuous_setOf_hasUniformModulus
    {T E : Type*} [PseudoMetricSpace T] [PseudoMetricSpace E]
    (modulus : ℝ → ℝ) (hmodulus : Tendsto modulus (nhds 0) (nhds 0)) :
    Equicontinuous
      ((↑) : {f : C(T, E) | HasUniformModulus modulus f} → T → E) := by
  apply Metric.equicontinuous_of_continuity_modulus modulus hmodulus
  intro s t f
  exact f.property s t

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

/-- A common modulus, a bound at one anchor point, and a uniform bound for
the modulus on distances from that anchor give a compact path family. -/
theorem isCompact_closure_setOf_hasUniformModulus
    {T E : Type*} [PseudoMetricSpace T] [CompactlyCoherentSpace T]
    [MetricSpace E] [ProperSpace E]
    (modulus : ℝ → ℝ) (hmodulus : Tendsto modulus (nhds 0) (nhds 0))
    (anchor : T) (origin : E) (anchorRadius modulusBound : ℝ)
    (hmodulusBound : ∀ t, modulus (dist t anchor) ≤ modulusBound) :
    IsCompact (closure {f : C(T, E) |
      HasUniformModulus modulus f ∧
        dist (f anchor) origin ≤ anchorRadius}) := by
  let S : Set C(T, E) := {f |
    HasUniformModulus modulus f ∧
      dist (f anchor) origin ≤ anchorRadius}
  refine isCompact_closure_of_equicontinuous_of_bounded
    S ?_ origin (modulusBound + anchorRadius) ?_
  · exact (equicontinuous_setOf_hasUniformModulus modulus hmodulus).comp
      (fun f : S ↦
        (⟨(f : C(T, E)), f.property.1⟩ :
          {g : C(T, E) | HasUniformModulus modulus g}))
  · intro f hf t
    calc
      dist (f t) origin ≤ dist (f t) (f anchor) + dist (f anchor) origin :=
        dist_triangle _ _ _
      _ ≤ modulus (dist t anchor) + anchorRadius :=
        add_le_add (hf.1 t anchor) hf.2
      _ ≤ modulusBound + anchorRadius :=
        by simpa [add_comm] using
          add_le_add_right (hmodulusBound t) anchorRadius

/-- A path satisfies prescribed oscillation bounds at a sequence of time
scales.  This formulation is convenient for multiscale tightness arguments,
where each scale is controlled by a separate probability estimate. -/
def HasOscillationBounds {T E : Type*} [PseudoMetricSpace T]
    [PseudoMetricSpace E] (delta epsilon : ℕ → ℝ)
    (f : C(T, E)) : Prop :=
  ∀ m, HasOscillationBound (delta m) (epsilon m) f

/-- A single oscillation bound cuts out a closed subset of continuous-path
space. -/
theorem isClosed_setOf_hasOscillationBound
    {T E : Type*} [PseudoMetricSpace T] [PseudoMetricSpace E]
    (delta epsilon : ℝ) :
    IsClosed {f : C(T, E) | HasOscillationBound delta epsilon f} := by
  rw [show {f : C(T, E) | HasOscillationBound delta epsilon f} =
      ⋂ s, ⋂ t, ⋂ (_h : dist s t < delta),
        {f | dist (f s) (f t) ≤ epsilon} by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact Iff.rfl]
  exact isClosed_iInter fun s => isClosed_iInter fun t =>
    isClosed_iInter fun _ => isClosed_le (by fun_prop) (by fun_prop)

/-- Paths satisfying prescribed oscillation bounds form a closed set in the
compact-open topology.  No positivity or convergence condition on the bounds
is needed for this topological fact. -/
theorem isClosed_setOf_hasOscillationBounds
    {T E : Type*} [PseudoMetricSpace T] [PseudoMetricSpace E]
    (delta epsilon : ℕ → ℝ) :
    IsClosed {f : C(T, E) | HasOscillationBounds delta epsilon f} := by
  rw [show {f : C(T, E) | HasOscillationBounds delta epsilon f} =
      ⋂ m, {f | HasOscillationBound (delta m) (epsilon m) f} by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact Iff.rfl]
  exact isClosed_iInter fun m =>
    isClosed_setOf_hasOscillationBound (delta m) (epsilon m)

/-- If every time scale is positive and the corresponding oscillation bounds
tend to zero, the paths satisfying all bounds form an equicontinuous family. -/
theorem equicontinuous_setOf_hasOscillationBounds
    {T E : Type*} [PseudoMetricSpace T] [PseudoMetricSpace E]
    (delta epsilon : ℕ → ℝ) (hdelta : ∀ m, 0 < delta m)
    (hepsilon : Tendsto epsilon atTop (nhds 0)) :
    Equicontinuous
      ((↑) : {f : C(T, E) | HasOscillationBounds delta epsilon f} →
        T → E) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro eta heta
  have heventually : ∀ᶠ m in atTop, epsilon m < eta :=
    hepsilon (Iio_mem_nhds heta)
  obtain ⟨m, hm⟩ := heventually.exists
  refine ⟨delta m, hdelta m, ?_⟩
  intro y hy f
  exact (f.property m x y (by simpa [dist_comm] using hy)).trans_lt hm

/-- Multiscale oscillation bounds together with a uniform pointwise bound
give a compact family of continuous paths. -/
theorem isCompact_closure_setOf_hasOscillationBounds
    {T E : Type*} [PseudoMetricSpace T] [CompactlyCoherentSpace T]
    [MetricSpace E] [ProperSpace E]
    (delta epsilon : ℕ → ℝ) (hdelta : ∀ m, 0 < delta m)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (origin : E) (radius : ℝ) :
    IsCompact (closure {f : C(T, E) |
      HasOscillationBounds delta epsilon f ∧
        ∀ t, dist (f t) origin ≤ radius}) := by
  let S : Set C(T, E) := {f |
    HasOscillationBounds delta epsilon f ∧
      ∀ t, dist (f t) origin ≤ radius}
  refine isCompact_closure_of_equicontinuous_of_bounded
    S ?_ origin radius ?_
  · exact (equicontinuous_setOf_hasOscillationBounds
      delta epsilon hdelta hepsilon).comp
        (fun f : S ↦
          (⟨(f : C(T, E)), f.property.1⟩ :
            {g : C(T, E) | HasOscillationBounds delta epsilon g}))
  · intro f hf t
    exact hf.2 t

end ContinuousMap
