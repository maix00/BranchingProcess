/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Order.Hom.Basic
public import Topology.Cadlag.Basic
public import Mathlib.Topology.UnitInterval
import all Mathlib.Topology.Order.MonotoneContinuity

/-!
# Time changes for the Skorokhod topology

This file defines the increasing homeomorphisms of the compact time interval
`[0, 1]` used in the Skorokhod `J₁` topology.  It only develops the time-change
group and its action on càdlàg paths.  The Skorokhod topology and its Borel
structure are intentionally left to later files.

The admissible clocks are Billingsley's class of strictly increasing
continuous maps of `[0,1]` onto itself; see Patrick Billingsley,
*Convergence of Probability Measures*, 1st ed., Wiley, 1968, Chapter 3,
§14, pp. 111–112
([text](https://ru.djvu.online/file/vaaIHv9IWlVeK)). This module represents
those maps as order isomorphisms of the unit interval.

## Public declarations

- `TimeChange` is an order isomorphism of `[0,1]`; `toHomeomorph` obtains its
  topological homeomorphism from the order topology. `ofHomeomorph` converts
  a strictly increasing homeomorphism into this representation, and
  `ofHomeomorph_apply` records its action on points.
- `ext`, `refl`, `refl_apply`, `trans`, `trans_apply`, and `symm` give
  extensionality, the identity, composition, and inverse. The endpoint and
  group laws are `apply_bot`, `apply_top`, `symm_apply_apply`,
  `apply_symm_apply`, `symm_symm`, `trans_refl`, `refl_trans`, `trans_symm`,
  `symm_trans`, and `trans_assoc`.
- `toContinuousMap` and `toContinuousMap_apply` view a time change as a
  continuous map. `distortion τ = sup_t dist (τ t) t`, and
  `distortion_eq_iSup` gives this supremum formula. Its nonnegativity,
  identity value, pointwise bound, inverse invariance, and composition bound
  are `distortion_nonneg`, `distortion_refl`, `dist_apply_le_distortion`,
  `distortion_symm`, and `distortion_trans_le`.
- `act τ f` is the reparameterized path `t ↦ f (τ t)`; `act_apply`, `refl_act`,
  and `trans_act` give its pointwise, identity, and composition laws.

A time change \(\tau\) is an increasing homeomorphism of \([0,1]\) with
\(\tau(0)=0\) and \(\tau(1)=1\). Its displacement and action are
\(\operatorname{distortion}(\tau)=\sup_t|\tau(t)-t|\) and
\((\tau\cdot f)(t)=f(\tau(t))\).
-/

@[expose] public section

open Set

namespace Skorokhod

/-- A time change for the Skorokhod `J₁` topology is a strictly increasing
homeomorphism of `[0, 1]`. -/
structure TimeChange where
  toOrderIso : unitInterval ≃o unitInterval

namespace TimeChange

/-- Regard an order time change as a homeomorphism for the order topology. -/
abbrev toHomeomorph (τ : TimeChange) : unitInterval ≃ₜ unitInterval :=
  τ.toOrderIso.toHomeomorph

/-- Convert a strictly increasing homeomorphism of the unit interval into an
order isomorphism, hence a Skorokhod time change. -/
noncomputable def ofHomeomorph (h : unitInterval ≃ₜ unitInterval)
    (hstrict : StrictMono h) : TimeChange :=
  ⟨OrderIso.ofSurjective (OrderEmbedding.ofStrictMono h hstrict) h.surjective⟩

@[simp]
theorem ofHomeomorph_apply (h : unitInterval ≃ₜ unitInterval)
    (hstrict : StrictMono h) (t : unitInterval) :
    (ofHomeomorph h hstrict).toOrderIso t = h t := rfl

instance : CoeFun TimeChange (fun _ => unitInterval → unitInterval) :=
  ⟨fun τ => τ.toOrderIso⟩

@[ext]
theorem ext {τ σ : TimeChange} (h : ∀ t, τ t = σ t) : τ = σ := by
  cases τ with
  | mk τ =>
      cases σ with
      | mk σ =>
          congr
          apply OrderIso.ext
          funext t
          exact h t

/-- The identity time change. -/
def refl : TimeChange where
  toOrderIso := OrderIso.refl unitInterval

@[simp]
theorem refl_apply (t : unitInterval) : refl t = t := rfl

@[simp]
theorem apply_bot (τ : TimeChange) : τ ⊥ = ⊥ := τ.toOrderIso.map_bot

@[simp]
theorem apply_top (τ : TimeChange) : τ ⊤ = ⊤ := τ.toOrderIso.map_top

/-- Composition of time changes. -/
def trans (τ σ : TimeChange) : TimeChange where
  toOrderIso := τ.toOrderIso.trans σ.toOrderIso

@[simp]
theorem trans_apply (τ σ : TimeChange) (t : unitInterval) :
    τ.trans σ t = σ (τ t) := rfl

/-- The inverse time change. -/
def symm (τ : TimeChange) : TimeChange := ⟨τ.toOrderIso.symm⟩

@[simp]
theorem symm_apply_apply (τ : TimeChange) (t : unitInterval) : τ.symm (τ t) = t :=
  τ.toHomeomorph.symm_apply_apply t

@[simp]
theorem apply_symm_apply (τ : TimeChange) (t : unitInterval) : τ (τ.symm t) = t :=
  τ.toHomeomorph.apply_symm_apply t

@[simp]
theorem symm_symm (τ : TimeChange) : τ.symm.symm = τ := by
  ext t
  rfl

@[simp]
theorem trans_refl (τ : TimeChange) : τ.trans refl = τ := by
  ext t
  rfl

@[simp]
theorem refl_trans (τ : TimeChange) : refl.trans τ = τ := by
  ext t
  rfl

@[simp]
theorem trans_symm (τ : TimeChange) : τ.trans τ.symm = refl := by
  ext t
  simp [trans, symm, refl]

@[simp]
theorem symm_trans (τ : TimeChange) : τ.symm.trans τ = refl := by
  ext t
  simp [trans, symm, refl]

theorem trans_assoc (τ σ υ : TimeChange) : (τ.trans σ).trans υ = τ.trans (σ.trans υ) := by
  ext t
  rfl

/-- A time change regarded as a continuous map. -/
def toContinuousMap (τ : TimeChange) : C(unitInterval, unitInterval) :=
  τ.toOrderIso.toHomeomorph

@[simp]
theorem toContinuousMap_apply (τ : TimeChange) (t : unitInterval) :
    τ.toContinuousMap t = τ t := rfl

/-- Uniform distance of a time change from the identity clock. -/
noncomputable def distortion (τ : TimeChange) : ℝ :=
  dist τ.toContinuousMap (ContinuousMap.id unitInterval)

theorem distortion_eq_iSup (τ : TimeChange) :
    τ.distortion = ⨆ t : unitInterval, dist (τ t) t := by
  rw [distortion, ContinuousMap.dist_eq_iSup]
  rfl

theorem distortion_nonneg (τ : TimeChange) : 0 ≤ τ.distortion :=
  dist_nonneg

@[simp]
theorem distortion_refl : refl.distortion = 0 := by
  rw [distortion_eq_iSup]
  simp [refl_apply]

theorem dist_apply_le_distortion (τ : TimeChange) (t : unitInterval) :
    dist (τ t) t ≤ τ.distortion := by
  exact ContinuousMap.dist_apply_le_dist
    (f := τ.toContinuousMap) (g := ContinuousMap.id unitInterval) t

@[simp]
theorem distortion_symm (τ : TimeChange) : τ.symm.distortion = τ.distortion := by
  apply le_antisymm
  · rw [distortion, ContinuousMap.dist_le_iff_of_nonempty]
    intro t
    simpa [dist_comm] using τ.dist_apply_le_distortion (τ.symm t)
  · rw [distortion, ContinuousMap.dist_le_iff_of_nonempty]
    intro t
    simpa [dist_comm] using τ.symm.dist_apply_le_distortion (τ t)

theorem distortion_trans_le (τ σ : TimeChange) :
    (τ.trans σ).distortion ≤ τ.distortion + σ.distortion := by
  rw [distortion, ContinuousMap.dist_le_iff_of_nonempty]
  intro t
  calc
    dist (σ (τ t)) t ≤ dist (σ (τ t)) (τ t) + dist (τ t) t :=
      dist_triangle _ _ _
    _ ≤ σ.distortion + τ.distortion :=
      add_le_add (σ.dist_apply_le_distortion (τ t)) (τ.dist_apply_le_distortion t)
    _ = τ.distortion + σ.distortion := add_comm _ _

/-- Reparameterize a càdlàg path by a Skorokhod time change. -/
noncomputable def act {E : Type*} [TopologicalSpace E] (τ : TimeChange)
    (f : CadlagPath unitInterval E) : CadlagPath unitInterval E :=
  f.compMonotoneContinuous τ τ.toOrderIso.monotone
    τ.toHomeomorph.continuous

@[simp]
theorem act_apply {E : Type*} [TopologicalSpace E] (τ : TimeChange)
    (f : CadlagPath unitInterval E) (t : unitInterval) :
    τ.act f t = f (τ t) := rfl

@[simp]
theorem refl_act {E : Type*} [TopologicalSpace E]
    (f : CadlagPath unitInterval E) : refl.act f = f := by
  ext t
  rfl

theorem trans_act {E : Type*} [TopologicalSpace E] (τ σ : TimeChange)
    (f : CadlagPath unitInterval E) : (τ.trans σ).act f = τ.act (σ.act f) := by
  ext t
  rfl

end TimeChange

end Skorokhod
