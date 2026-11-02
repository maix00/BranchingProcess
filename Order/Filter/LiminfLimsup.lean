/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Liminf and limsup under vanishing perturbations

For a nontrivial filter on any index type, bounded functions into a densely
ordered, conditionally complete topological additive group whose difference
tends to zero have the same limsup and liminf. The proofs use Mathlib's
`limsup_add_const` and `liminf_add_const` interfaces.

## Public declarations

* `Filter.limsup_eq_of_sub_tendsto_zero`: if `u` and `v` are bounded above
  and below along `l`, and `u - v → 0` along `l`, then
  `limsup u l = limsup v l`.
* `Filter.liminf_eq_of_sub_tendsto_zero`: under the same assumptions,
  `liminf u l = liminf v l`.

For functions `u,v : ι → α` bounded above and below along a nontrivial filter
`l`, the conclusions are
\[
  u-v\xrightarrow[l]{}0
  \quad\Longrightarrow\quad
  \limsup_l u=\limsup_l v,
  \qquad
  \liminf_l u=\liminf_l v.
\]
-/

public section

open Filter Topology

namespace Filter

variable {ι α : Type*} {l : Filter ι} [l.NeBot]
  [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [DenselyOrdered α]
  [IsOrderedAddMonoid α] [TopologicalSpace α] [OrderTopology α]
  [ContinuousAdd α] [ContinuousNeg α]

/-- If two functions into a densely ordered, conditionally complete topological
additive group are bounded above and below along a nontrivial filter and their
difference tends to zero, their limsups agree. -/
theorem limsup_eq_of_sub_tendsto_zero {u v : ι → α}
    (hau : l.IsBoundedUnder (· ≤ ·) u) (hbu : l.IsBoundedUnder (· ≥ ·) u)
    (hav : l.IsBoundedUnder (· ≤ ·) v) (hbv : l.IsBoundedUnder (· ≥ ·) v)
    (h : Tendsto (fun i => u i - v i) l (𝓝 0)) :
    limsup u l = limsup v l := by
  have cou : l.IsCoboundedUnder (· ≤ ·) u := hbu.isCoboundedUnder_le
  have cov : l.IsCoboundedUnder (· ≤ ·) v := hbv.isCoboundedUnder_le
  have key : ∀ (a b : ι → α), l.IsBoundedUnder (· ≥ ·) a →
      l.IsBoundedUnder (· ≤ ·) b → l.IsCoboundedUnder (· ≤ ·) b →
      Tendsto (fun i => a i - b i) l (𝓝 0) → limsup a l ≤ limsup b l := by
    intro a b ha_low hb_up hb_cob hdiff
    have ha_cob : l.IsCoboundedUnder (· ≤ ·) a := ha_low.isCoboundedUnder_le
    have hle : ∀ δ : α, 0 < δ → limsup a l ≤ limsup b l + δ := by
      intro δ hδ
      have heq : limsup (fun i => b i + δ) l = limsup b l + δ :=
        limsup_add_const l b δ hb_up hb_cob
      rw [← heq]
      have hb_up' : l.IsBoundedUnder (· ≤ ·) (fun i => b i + δ) := by
        obtain ⟨M, hM⟩ := hb_up
        refine ⟨M + δ, ?_⟩
        simp only [eventually_map] at hM ⊢
        filter_upwards [hM] with i hi
        simpa [add_comm] using add_le_add_right hi δ
      refine limsup_le_limsup ?_ ha_cob hb_up'
      have hev : ∀ᶠ i in l, a i - b i < δ :=
        (tendsto_order.1 hdiff).2 δ hδ
      filter_upwards [hev] with i hi
      simpa [add_comm] using (sub_le_iff_le_add).1 hi.le
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨c, hbc, hca⟩ := exists_between hcon
    let δ := c - limsup b l
    have hδ : 0 < δ := sub_pos.mpr hbc
    have hbound := hle δ hδ
    have hbound' : limsup a l ≤ c := by
      simpa [δ, add_sub_cancel] using hbound
    exact (not_le_of_gt hca) hbound'
  apply le_antisymm
  · exact key u v hbu hav cov h
  · refine key v u hbv hau cou ?_
    have hneg : (fun i => v i - u i) = fun i => -(u i - v i) := by
      funext i
      simp [sub_eq_add_neg]
    rw [hneg]
    simpa using h.neg

omit [DenselyOrdered α] [ContinuousAdd α] in
private theorem neg_liminf_eq_limsup {u : ι → α}
    (hau : l.IsBoundedUnder (· ≤ ·) u) (hbu : l.IsBoundedUnder (· ≥ ·) u) :
    -liminf u l = limsup (fun i => -u i) l := by
  have h := Antitone.map_limsInf_of_continuousAt
    (F := l.map u) (f := fun x : α => -x)
    (fun _ _ hab => neg_le_neg hab)
    (continuous_neg.continuousAt (x := (l.map u).limsInf))
    hau.isCoboundedUnder_flip hbu
  simpa only [liminf, limsup, Filter.map_map, Function.comp_def] using h

/-- If two functions into a densely ordered, conditionally complete topological
additive group are bounded above and below along a nontrivial filter and their
difference tends to zero, their liminfs agree. This is the order-dual form of
`limsup_eq_of_sub_tendsto_zero`. -/
theorem liminf_eq_of_sub_tendsto_zero {u v : ι → α}
    (hau : l.IsBoundedUnder (· ≤ ·) u) (hbu : l.IsBoundedUnder (· ≥ ·) u)
    (hav : l.IsBoundedUnder (· ≤ ·) v) (hbv : l.IsBoundedUnder (· ≥ ·) v)
    (h : Tendsto (fun i => u i - v i) l (𝓝 0)) :
    liminf u l = liminf v l := by
  have hneg : Tendsto (fun i => -u i - -v i) l (𝓝 0) := by
    have hfun : (fun i => -u i - -v i) = fun i => -(u i - v i) := by
      funext i
      simp [sub_eq_add_neg, add_comm]
    rw [hfun]
    simpa using h.neg
  have hu_up : l.IsBoundedUnder (· ≤ ·) (fun i => -u i) :=
    hbu.comp (fun a b hab => neg_le_neg hab)
  have hu_low : l.IsBoundedUnder (· ≥ ·) (fun i => -u i) :=
    hau.comp (fun a b hab => neg_le_neg hab)
  have hv_up : l.IsBoundedUnder (· ≤ ·) (fun i => -v i) :=
    hbv.comp (fun a b hab => neg_le_neg hab)
  have hv_low : l.IsBoundedUnder (· ≥ ·) (fun i => -v i) :=
    hav.comp (fun a b hab => neg_le_neg hab)
  have hlim := limsup_eq_of_sub_tendsto_zero hu_up hu_low hv_up hv_low hneg
  have hdu := neg_liminf_eq_limsup hau hbu
  have hdv := neg_liminf_eq_limsup hav hbv
  have hu_eq : liminf u l = -limsup (fun i => -u i) l := by
    simpa using congrArg (fun x : α => -x) hdu
  have hv_eq : liminf v l = -limsup (fun i => -v i) l := by
    simpa using congrArg (fun x : α => -x) hdv
  calc
    liminf u l = -limsup (fun i => -u i) l := hu_eq
    _ = -limsup (fun i => -v i) l := by rw [hlim]
    _ = liminf v l := hv_eq.symm

end Filter
