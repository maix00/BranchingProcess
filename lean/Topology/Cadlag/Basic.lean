module

public import Mathlib.Topology.Order.Cadlag

@[expose] public section

/-!
# The type of càdlàg paths

Mathlib provides the predicate `IsCadlag`.  This file packages paths
satisfying that predicate into a type on which the Skorokhod topology can be
constructed.  No topology or measurable space is assigned here: in
particular, the product topology on the ambient function type is not silently
used in place of the Skorokhod topology.
-/

open Filter Set
open scoped Topology

/-- Precomposition by a continuous monotone time change preserves càdlàg
paths. -/
theorem IsCadlag.comp_monotone_continuous
    {T S E : Type*} [LinearOrder T] [TopologicalSpace T] [OrderTopology T]
    [PartialOrder S] [TopologicalSpace S] [TopologicalSpace E]
    {f : S → E} (hf : IsCadlag f) {ψ : T → S}
    (hψ : Monotone ψ) (hψc : Continuous ψ) :
    IsCadlag (f ∘ ψ) where
  isRightContinuous := by
    intro x
    rw [continuousWithinAt_Ioi_iff_Ici]
    refine ContinuousWithinAt.comp (t := Set.Ici (ψ x)) ?_
      hψc.continuousWithinAt fun y hy => hψ hy
    exact continuousWithinAt_Ioi_iff_Ici.1 (hf.isRightContinuous (ψ x))
  tendsto_nhdsLT x := by
    by_cases h : ∃ y, y < x ∧ ψ y = ψ x
    · obtain ⟨y, hyx, hy⟩ := h
      refine ⟨f (ψ x), ?_⟩
      have heq : ∀ᶠ z in 𝓝[Set.Iio x] x, f (ψ x) = (f ∘ ψ) z := by
        filter_upwards [Ico_mem_nhdsLT hyx] with z hz
        simp only [Function.comp_apply]
        rw [le_antisymm (hψ hz.2.le) (hy ▸ hψ hz.1)]
      exact tendsto_const_nhds.congr' heq
    · push Not at h
      obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT (ψ x)
      refine ⟨l, hl.comp ?_⟩
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        ψ (hψc.continuousAt.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact lt_of_le_of_ne (hψ hy.le) (h y hy)

/-- A càdlàg path with time domain `T` and state space `E`. -/
structure CadlagPath (T E : Type*) [PartialOrder T] [TopologicalSpace T]
    [TopologicalSpace E] where
  toFun : T → E
  isCadlag_toFun : IsCadlag toFun

namespace CadlagPath

variable {T E : Type*} [PartialOrder T] [TopologicalSpace T]
  [TopologicalSpace E]

instance : CoeFun (CadlagPath T E) fun _ => T → E := ⟨toFun⟩

@[ext] theorem ext {f g : CadlagPath T E} (h : ∀ t, f t = g t) : f = g := by
  cases f
  cases g
  congr
  funext t
  exact h t

@[simp] theorem coe_mk (f : T → E) (hf : IsCadlag f) :
    ⇑(CadlagPath.mk f hf) = f := rfl

/-- Change the clock of a càdlàg path by a continuous monotone map. -/
def compMonotoneContinuous
    {S : Type*} [LinearOrder S] [TopologicalSpace S] [OrderTopology S]
    (f : CadlagPath T E) (ψ : S → T) (hψ : Monotone ψ)
    (hψc : Continuous ψ) : CadlagPath S E :=
  ⟨f ∘ ψ, f.isCadlag_toFun.comp_monotone_continuous hψ hψc⟩

@[simp] theorem compMonotoneContinuous_apply
    {S : Type*} [LinearOrder S] [TopologicalSpace S] [OrderTopology S]
    (f : CadlagPath T E) (ψ : S → T) (hψ : Monotone ψ)
    (hψc : Continuous ψ) (s : S) :
    f.compMonotoneContinuous ψ hψ hψc s = f (ψ s) := rfl

end CadlagPath
