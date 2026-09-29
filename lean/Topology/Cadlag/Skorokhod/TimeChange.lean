import Mathlib.Topology.ContinuousMap.Compact
import Topology.Cadlag.Basic
import Mathlib.Topology.UnitInterval

/-!
# Time changes for the Skorokhod topology

This file defines the increasing homeomorphisms of the compact time interval
`[0, 1]` used in the Skorokhod `J₁` topology.  It only develops the time-change
group and its action on càdlàg paths.  The Skorokhod topology and its Borel
structure are intentionally left to later files.
-/

open Set

namespace Skorokhod

/-- A time change for the Skorokhod `J₁` topology is a strictly increasing
homeomorphism of `[0, 1]`. -/
structure TimeChange where
  toHomeomorph : unitInterval ≃ₜ unitInterval
  strictMono_toHomeomorph : StrictMono toHomeomorph

namespace TimeChange

instance : CoeFun TimeChange (fun _ => unitInterval → unitInterval) :=
  ⟨fun τ => τ.toHomeomorph⟩

@[ext]
theorem ext {τ σ : TimeChange} (h : ∀ t, τ t = σ t) : τ = σ := by
  cases τ with
  | mk τ hτ =>
      cases σ with
      | mk σ hσ =>
          congr
          exact Homeomorph.ext h

/-- The identity time change. -/
def refl : TimeChange where
  toHomeomorph := Homeomorph.refl unitInterval
  strictMono_toHomeomorph := strictMono_id

@[simp]
theorem refl_apply (t : unitInterval) : refl t = t := rfl

@[simp]
theorem apply_bot (τ : TimeChange) : τ ⊥ = ⊥ := by
  obtain ⟨t, ht⟩ := τ.toHomeomorph.surjective ⊥
  have htbot : t = ⊥ := by
    by_contra h
    have hlt : ⊥ < t := bot_lt_iff_ne_bot.2 h
    have := τ.strictMono_toHomeomorph hlt
    rw [ht] at this
    exact (not_lt_of_ge bot_le this).elim
  calc
    τ ⊥ = τ t := congrArg τ htbot.symm
    _ = ⊥ := ht

@[simp]
theorem apply_top (τ : TimeChange) : τ ⊤ = ⊤ := by
  obtain ⟨t, ht⟩ := τ.toHomeomorph.surjective ⊤
  have httop : t = ⊤ := by
    by_contra h
    have hlt : t < ⊤ := lt_top_iff_ne_top.2 h
    have := τ.strictMono_toHomeomorph hlt
    rw [ht] at this
    exact (not_lt_of_ge le_top this).elim
  calc
    τ ⊤ = τ t := congrArg τ httop.symm
    _ = ⊤ := ht

/-- Composition of time changes. -/
def trans (τ σ : TimeChange) : TimeChange where
  toHomeomorph := τ.toHomeomorph.trans σ.toHomeomorph
  strictMono_toHomeomorph := σ.strictMono_toHomeomorph.comp τ.strictMono_toHomeomorph

@[simp]
theorem trans_apply (τ σ : TimeChange) (t : unitInterval) :
    τ.trans σ t = σ (τ t) := rfl

private theorem strictMono_symm_of_strictMono
    {α β : Type*} [LinearOrder α] [LinearOrder β] (e : α ≃ β)
    (he : StrictMono e) : StrictMono e.symm := by
  intro a b hab
  rcases lt_trichotomy (e.symm a) (e.symm b) with h | h | h
  · exact h
  · exfalso
    exact (ne_of_lt hab) (e.symm.injective h)
  · have hba : b < a := by simpa using he h
    exact (not_lt_of_ge hab.le hba).elim

/-- The inverse time change. -/
def symm (τ : TimeChange) : TimeChange where
  toHomeomorph := τ.toHomeomorph.symm
  strictMono_toHomeomorph :=
    strictMono_symm_of_strictMono τ.toHomeomorph.toEquiv τ.strictMono_toHomeomorph

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
  τ.toHomeomorph

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
  simp [distortion, toContinuousMap, refl]

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
  f.compMonotoneContinuous τ τ.strictMono_toHomeomorph.monotone
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
