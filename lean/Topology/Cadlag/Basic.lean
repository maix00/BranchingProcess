/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.Order.Cadlag

/-!
# The type of càdlàg paths

Mathlib provides the predicate `IsCadlag`.  This file packages paths
satisfying that predicate into a type on which the Skorokhod topology can be
constructed.  No topology or measurable space is assigned here: in
particular, the product topology on the ambient function type is not silently
used in place of the Skorokhod topology.
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

/-- Right continuity at zero gives a uniform spatial bound on a sufficiently
short initial time interval. -/
theorem IsCadlag.exists_initial_interval_subset_Ioo
    {f : ℝ≥0 → ℝ} (hf : IsCadlag f) {lower upper : ℝ}
    (hlower : lower < f 0) (hupper : f 0 < upper) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : ℝ≥0, t ≤ δ → f t ∈ Set.Ioo lower upper := by
  have hcont : ContinuousAt f 0 := by
    have h := hf.isRightContinuous 0
    rw [continuousWithinAt_Ioi_iff_Ici] at h
    simpa [continuousWithinAt_univ] using h
  have hnear : {t : ℝ≥0 | f t ∈ Set.Ioo lower upper} ∈ 𝓝 (0 : ℝ≥0) :=
    hcont.eventually (isOpen_Ioo.mem_nhds ⟨hlower, hupper⟩)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let δ : ℝ≥0 := ⟨r / 2, by positivity⟩
  refine ⟨δ, by exact_mod_cast half_pos hr, ?_⟩
  intro t ht
  apply hball
  rw [Metric.mem_ball, NNReal.dist_eq]
  have ht' : (t : ℝ) ≤ r / 2 := by exact_mod_cast ht
  simpa [abs_of_nonneg t.property] using (show (t : ℝ) < r by linarith)

/-- Along any sequence of horizons converging to zero, a càdlàg path is
eventually confined to every open spatial interval containing its start. -/
theorem IsCadlag.eventually_initial_interval_subset_Ioo
    {f : ℝ≥0 → ℝ} (hf : IsCadlag f)
    {horizon : ℕ → ℝ≥0} (hhorizon : Filter.Tendsto horizon Filter.atTop (𝓝 0))
    {lower upper : ℝ} (hlower : lower < f 0) (hupper : f 0 < upper) :
    ∀ᶠ n in Filter.atTop, ∀ t : ℝ≥0, t ≤ horizon n →
      f t ∈ Set.Ioo lower upper := by
  obtain ⟨δ, hδ, hpath⟩ := hf.exists_initial_interval_subset_Ioo hlower hupper
  have hnear : Set.Iio δ ∈ 𝓝 (0 : ℝ≥0) :=
    isOpen_Iio.mem_nhds hδ
  filter_upwards [hhorizon.eventually hnear] with n hn t ht
  exact hpath t (le_of_lt (lt_of_le_of_lt ht hn))
