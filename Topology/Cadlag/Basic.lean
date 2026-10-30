/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.Order.Cadlag

/-!
# The type of càdlàg paths

## Public declarations

- `IsCadlag.comp_monotone_continuous`: precomposition by a continuous
  monotone time change preserves `IsCadlag`.
- `IsCadlag.updateTop`: changing only the value at a top endpoint preserves
  `IsCadlag`.
- `CadlagPath`: the subtype of functions `T → E` satisfying `IsCadlag`.
- `CadlagPath.const value` and `CadlagPath.const_apply`: the constant path
  $t\mapsto value$ and its evaluation formula.
- `CadlagPath.ext` and `CadlagPath.coe_mk`: extensionality and the coercion
  equation for constructed paths.
- `CadlagPath.isCadlag_restrictRange`: a path taking values in a closed set
  remains càdlàg when viewed as a path into that subtype.
- `CadlagPath.restrictRange` and `CadlagPath.forgetRange`: move between paths
  valued in a closed subtype and paths in the ambient state space.
- `CadlagPath.forgetRange_apply`, `CadlagPath.compMonotoneContinuous`, and
  `CadlagPath.compMonotoneContinuous_apply`: pointwise formulas for forgetting
  the subtype and changing the path clock.

Mathlib provides the predicate `IsCadlag`; this module supplies the path type
needed to build path-space interfaces. It assigns no topology or measurable
space to the function type.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

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

/-- Changing a càdlàg function's value at the terminal point preserves
càdlàg regularity. Left limits only see times strictly before the point, and
right continuity at the terminal point is vacuous. -/
theorem IsCadlag.updateTop
    {T E : Type*} [LinearOrder T] [TopologicalSpace T] [OrderTopology T]
    [DenselyOrdered T] [OrderTop T] [DecidableEq T] [TopologicalSpace E]
    {f : T → E} (hf : IsCadlag f) (value : E) :
    IsCadlag (fun t => if t = ⊤ then value else f t) := by
  classical
  refine ⟨?_, ?_⟩
  · intro t
    by_cases ht : t = ⊤
    · subst t
      change Tendsto (fun s => if s = ⊤ then value else f s)
        (nhdsWithin (⊤ : T) (Set.Ioi ⊤))
        (nhds (if (⊤ : T) = ⊤ then value else f ⊤))
      have hfilter : nhdsWithin (⊤ : T) (Set.Ioi ⊤) = ⊥ := by
        simp [nhdsWithin]
      rw [hfilter]
      exact Filter.tendsto_bot
    · obtain ⟨u, htu, hut⟩ := exists_between (lt_top_iff_ne_top.mpr ht)
      have hmem : {s : T | s ≠ ⊤} ∈ 𝓝[Set.Ioi t] t := by
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        refine ⟨Set.Iio u, isOpen_Iio.mem_nhds htu, ?_⟩
        intro s hs
        exact ne_of_lt ((Set.mem_inter_iff s _ _).mp hs |>.1 |>.trans hut)
      have heq : f =ᶠ[𝓝[Set.Ioi t] t]
          fun s => if s = ⊤ then value else f s := by
        filter_upwards [hmem] with s hs
        simp [hs]
      have hbase : Tendsto f (nhdsWithin t (Set.Ioi t)) (nhds (f t)) :=
        hf.isRightContinuous t
      change Tendsto (fun s => if s = ⊤ then value else f s)
        (nhdsWithin t (Set.Ioi t))
        (nhds (if t = ⊤ then value else f t))
      rw [ite_eq_right ht]
      exact hbase.congr' heq
  · intro t
    obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT t
    refine ⟨l, hl.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hst : s < ⊤ := lt_of_lt_of_le hs le_top
    simp [ne_of_lt hst]

/-- A càdlàg path with time domain `T` and state space `E`. -/
structure CadlagPath (T E : Type*) [PartialOrder T] [TopologicalSpace T]
    [TopologicalSpace E] where
  toFun : T → E
  isCadlag_toFun : IsCadlag toFun

namespace CadlagPath

variable {T E : Type*} [PartialOrder T] [TopologicalSpace T]
  [TopologicalSpace E]

instance : CoeFun (CadlagPath T E) fun _ => T → E := ⟨toFun⟩

/-- The constant càdlàg path with value `value`. -/
def const (value : E) : CadlagPath T E :=
  ⟨fun _ => value, IsCadlag.const⟩

@[simp]
theorem const_apply (value : E) (t : T) : const value t = value := rfl

@[ext] theorem ext {f g : CadlagPath T E} (h : ∀ t, f t = g t) : f = g := by
  cases f
  cases g
  congr
  funext t
  exact h t

@[simp] theorem coe_mk (f : T → E) (hf : IsCadlag f) :
    ⇑(CadlagPath.mk f hf) = f := rfl

/-- Restrict a càdlàg path to a closed range, viewed as a subtype. -/
theorem isCadlag_restrictRange {f : T → E} (hf : IsCadlag f)
    (range : Set E) (hrange : ∀ t, f t ∈ range) (hrangeClosed : IsClosed range) :
    IsCadlag (fun t => (⟨f t, hrange t⟩ : range)) := by
  refine ⟨?_, ?_⟩
  · intro t
    exact tendsto_subtype_rng.2 (hf.isRightContinuous t)
  · intro t
    by_cases hnebot : NeBot (𝓝[<] t)
    · obtain ⟨limit, hlimit⟩ := hf.tendsto_nhdsLT t
      have hlimitRange : limit ∈ range :=
        @IsClosed.mem_of_tendsto E _ T limit range f (𝓝[<] t) hnebot
          hrangeClosed hlimit (Eventually.of_forall hrange)
      exact ⟨⟨limit, hlimitRange⟩, tendsto_subtype_rng.2 hlimit⟩
    · have hfilter : 𝓝[<] t = ⊥ := Filter.not_neBot.mp hnebot
      exact ⟨⟨f t, hrange t⟩, tendsto_subtype_rng.2 (by rw [hfilter]; exact tendsto_bot)⟩

/-- View a càdlàg path with values in a closed set as a path into that
subtype. -/
def restrictRange (path : CadlagPath T E) (range : Set E)
    (hrange : ∀ t, path t ∈ range) (hrangeClosed : IsClosed range) :
  CadlagPath T range :=
  ⟨fun t => ⟨path t, hrange t⟩,
    isCadlag_restrictRange path.isCadlag_toFun range hrange hrangeClosed⟩

/-- Forget that a càdlàg path takes values in a subtype. -/
def forgetRange {range : Set E} (path : CadlagPath T range) : CadlagPath T E :=
  ⟨fun t => (path t).1,
    path.isCadlag_toFun.continuous_comp continuous_subtype_val⟩

@[simp] theorem forgetRange_apply {range : Set E}
    (path : CadlagPath T range) (t : T) : path.forgetRange t = (path t).1 := rfl

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
