/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Cloud.Order.Slice
public import Order.DominatingMap

/-!
# Particle matching extracted from rankwise domination

Rankwise domination is stated without choosing a global correspondence.  For
the offspring coupling we need one coherent parent map.  This file extracts
that map and proves it is injective whenever ranks distinguish the particles
in the object population.  The particles retain their full multi-root labels
`Root × TreeNode α`; no finiteness or countability of the root type is used.

## Public declarations

- `Cloud.SliceDominatingMap φ C D t` is an injective map from `C`'s particles
  at time `t` to `D`'s particles such that `φ` of each partner position is at
  most `φ` of the matched object position: for its underlying map `f`,
  `\(f '' C.particles(t) \subseteq D.particles(t)\)`,
  `\(\operatorname{InjOn}(f,C.particles(t))\)`, and
  `\(\forall p\in C.particles(t),
  \varphi(D.position((f(p)).1,(f(p)).2))\le
  \varphi(C.position(p.1,p.2))\)`.
- `Cloud.InjectivelyDominatesBy φ C D t` is the corresponding existence
  proposition, and `Cloud.injectivelyDominatesBy_iff_nonempty` states
  `\(C.InjectivelyDominatesBy(\varphi,D,t)
  \iff \operatorname{Nonempty}(Cloud.SliceDominatingMap(\varphi,C,D,t))\)`.
  `Cloud.SliceDominatingMap.injectivelyDominatesBy` forgets a concrete map;
  `Cloud.SliceDominatingMap.refl` and
  `Cloud.SliceDominatingMap.trans` give identity and composition, and
  `Cloud.SliceDominatingMap.ofInjectivelyDominatesBy` chooses one from its
  existence proof.
- `Cloud.injectivelyDominatesBy_refl`,
  `Cloud.injectivelyDominatesBy_of_particles_subset`, and
  `Cloud.injectivelyDominatesBy_trans` give reflexivity, the canonical
  inclusion map under the pointwise position inequality, and transitivity.
  `Cloud.injectivelyDominatesBy_toDual_iff` and
  `Cloud.injectivelyDominates_mapOrderDual_iff` give the value-order and
  position-order dual formulations without exchanging the cloud arguments.
- `exists_injective_match_of_rankwiseDominatesBy` turns rankwise domination
  into a coherent injective matching when the object rank separates particles in the object population. `exists_injective_match_of_rankwiseDominatesBy_of_finite` gives
  the finite-slice specialization. The theorems
  `injectivelyDominatesBy_of_rankwiseDominatesBy` and
  `injectivelyDominatesBy_of_rankwiseDominatesBy_of_finite` package these
  matchings as the existence proposition.
-/

open Combinatorics.UlamHarris

@[expose] public section

namespace Combinatorics.Branching

set_option linter.style.haveILetI false

variable {Time Root α Position Value : Type*}

/-- An order-dominating map between two cloud slices.  This is the cloud-slice
specialization of `Order.DominatingMap`; it is pathwise data rather
than a coupling of probability measures. -/
abbrev Cloud.SliceDominatingMap [Preorder Value]
    (φ : Position → Value) (objectsToMatchCloud availablePartnersCloud : Cloud Time Root α Position)
    (t : Time) :=
  Order.DominatingMap (objectsToMatchCloud.particles t) (availablePartnersCloud.particles t)
    (fun p => φ (objectsToMatchCloud.position p.1 p.2))
    (fun p => φ (availablePartnersCloud.position p.1 p.2))

namespace Cloud.SliceDominatingMap

variable [Preorder Value]

instance (φ : Position → Value) (objectsToMatchCloud availablePartnersCloud : Cloud Time Root α Position)
    (t : Time) : CoeFun (Cloud.SliceDominatingMap φ objectsToMatchCloud availablePartnersCloud t)
      (fun _ => RootIndexed.TreeNode Root α →
        RootIndexed.TreeNode Root α) :=
  ⟨Order.DominatingMap.toFun⟩

/-- The identity dominating map of a cloud slice. -/
def refl (φ : Position → Value) (objectsToMatchCloud : Cloud Time Root α Position)
    (t : Time) : Cloud.SliceDominatingMap φ objectsToMatchCloud objectsToMatchCloud t :=
  Order.DominatingMap.refl (objectsToMatchCloud.particles t)
    (fun p => φ (objectsToMatchCloud.position p.1 p.2))

/-- Composition retains the concrete particle correspondence. -/
def trans {φ : Position → Value} {objectsToMatchCloud availablePartnersCloud nextPartnersCloud : Cloud Time Root α Position} {t : Time}
    (f : Cloud.SliceDominatingMap φ objectsToMatchCloud availablePartnersCloud t)
    (g : Cloud.SliceDominatingMap φ availablePartnersCloud nextPartnersCloud t) :
    Cloud.SliceDominatingMap φ objectsToMatchCloud nextPartnersCloud t :=
  Order.DominatingMap.trans f g

end Cloud.SliceDominatingMap

/-- The coupling invariant needed by offspring propagation: every object
particle is assigned injectively to a partner particle whose observed position
lies weakly to its left.  This definition is independent of the ambient order
on particle addresses and therefore applies to random spatial configurations
without pretending that their addresses are already position-sorted. -/
def Cloud.InjectivelyDominatesBy [Preorder Value]
    (φ : Position → Value) (objectsToMatchCloud availablePartnersCloud : Cloud Time Root α Position) (t : Time) : Prop :=
  ∃ partnerOfObject : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α,
    Set.MapsTo partnerOfObject (objectsToMatchCloud.particles t) (availablePartnersCloud.particles t) ∧
    Set.InjOn partnerOfObject (objectsToMatchCloud.particles t) ∧
    ∀ p ∈ objectsToMatchCloud.particles t,
      φ (availablePartnersCloud.position (partnerOfObject p).1 (partnerOfObject p).2) ≤
        φ (objectsToMatchCloud.position p.1 p.2)

/-- Forget the concrete coupling state and retain only its existence. -/
theorem Cloud.SliceDominatingMap.injectivelyDominatesBy [Preorder Value]
    {φ : Position → Value} {objectsToMatchCloud availablePartnersCloud : Cloud Time Root α Position} {t : Time}
    (f : Cloud.SliceDominatingMap φ objectsToMatchCloud availablePartnersCloud t) :
    objectsToMatchCloud.InjectivelyDominatesBy φ availablePartnersCloud t :=
  ⟨f, f.mapsTo, f.injOn, f.dominates⟩

/-- The propositional domination relation is exactly the existence of a
concrete dominating injection. -/
theorem Cloud.injectivelyDominatesBy_iff_nonempty [Preorder Value]
    (φ : Position → Value) (objectsToMatchCloud availablePartnersCloud : Cloud Time Root α Position) (t : Time) :
    objectsToMatchCloud.InjectivelyDominatesBy φ availablePartnersCloud t ↔
      Nonempty (Cloud.SliceDominatingMap φ objectsToMatchCloud availablePartnersCloud t) := by
  constructor
  · rintro ⟨f, hmem, hinj, hdom⟩
    exact ⟨⟨f, hmem, hinj, hdom⟩⟩
  · rintro ⟨f⟩
    exact f.injectivelyDominatesBy

/-- Choose a concrete slice map from a proof of its existence.  Iterated
constructions should accept and return `SliceDominatingMap` directly; this
bridge is for compatibility with proposition-level results. -/
noncomputable def Cloud.SliceDominatingMap.ofInjectivelyDominatesBy
    [Preorder Value] {φ : Position → Value}
    {objectsToMatchCloud availablePartnersCloud : Cloud Time Root α Position} {t : Time}
    (h : objectsToMatchCloud.InjectivelyDominatesBy φ availablePartnersCloud t) :
    Cloud.SliceDominatingMap φ objectsToMatchCloud availablePartnersCloud t :=
  Classical.choice ((Cloud.injectivelyDominatesBy_iff_nonempty φ objectsToMatchCloud availablePartnersCloud t).mp h)

theorem Cloud.injectivelyDominatesBy_refl [Preorder Value]
    (φ : Position → Value) (objectsToMatchCloud : Cloud Time Root α Position) (t : Time) :
    objectsToMatchCloud.InjectivelyDominatesBy φ objectsToMatchCloud t := by
  exact (Cloud.SliceDominatingMap.refl φ objectsToMatchCloud t).injectivelyDominatesBy

/-- Inclusion of particle labels gives the canonical injective matching when
the partner position at each retained label is no larger in the observed
order. -/
theorem Cloud.injectivelyDominatesBy_of_particles_subset [Preorder Value]
    (φ : Position → Value) {objectsToMatchCloud availablePartnersCloud : Cloud Time Root α Position} (t : Time)
    (hsubset : objectsToMatchCloud.particles t ⊆ availablePartnersCloud.particles t)
    (hposition : ∀ p ∈ objectsToMatchCloud.particles t,
      φ (availablePartnersCloud.position p.1 p.2) ≤ φ (objectsToMatchCloud.position p.1 p.2)) :
    objectsToMatchCloud.InjectivelyDominatesBy φ availablePartnersCloud t := by
  exact ⟨id, hsubset, Set.injOn_id _, hposition⟩

theorem Cloud.injectivelyDominatesBy_trans [Preorder Value]
    (φ : Position → Value) {objectsToMatchCloud availablePartnersCloud nextPartnersCloud : Cloud Time Root α Position} (t : Time)
    (hObjectToPartner : objectsToMatchCloud.InjectivelyDominatesBy φ availablePartnersCloud t)
    (hPartnerToNext : availablePartnersCloud.InjectivelyDominatesBy φ nextPartnersCloud t) :
    objectsToMatchCloud.InjectivelyDominatesBy φ nextPartnersCloud t := by
  rw [Cloud.injectivelyDominatesBy_iff_nonempty] at hObjectToPartner hPartnerToNext ⊢
  rcases hObjectToPartner with ⟨f⟩
  rcases hPartnerToNext with ⟨g⟩
  exact ⟨f.trans g⟩

/-- Reading the observation in `OrderDual Value` reverses the spatial
inequality while preserving the direction of the particle matching and its
cardinality comparison.  Thus left and right versions use one invariant; the
two cloud arguments are not exchanged. -/
theorem Cloud.injectivelyDominatesBy_toDual_iff [Preorder Value]
    (φ : Position → Value) (objectsToMatchCloud availablePartnersCloud : Cloud Time Root α Position) (t : Time) :
    objectsToMatchCloud.InjectivelyDominatesBy (fun x => OrderDual.toDual (φ x)) availablePartnersCloud t ↔
      ∃ partnerOfObject : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α,
        Set.MapsTo partnerOfObject (objectsToMatchCloud.particles t) (availablePartnersCloud.particles t) ∧
        Set.InjOn partnerOfObject (objectsToMatchCloud.particles t) ∧
        ∀ p ∈ objectsToMatchCloud.particles t,
          φ (objectsToMatchCloud.position p.1 p.2) ≤
            φ (availablePartnersCloud.position (partnerOfObject p).1 (partnerOfObject p).2) := by
  rfl

/-- Same duality when the cloud's position type itself is replaced by its
order dual. -/
theorem Cloud.injectivelyDominates_mapOrderDual_iff [Preorder Position]
    (objectsToMatchCloud availablePartnersCloud : Cloud Time Root α Position) (t : Time) :
    (objectsToMatchCloud.mapOrderDual).InjectivelyDominatesBy id (availablePartnersCloud.mapOrderDual) t ↔
      ∃ partnerOfObject : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α,
        Set.MapsTo partnerOfObject (objectsToMatchCloud.particles t) (availablePartnersCloud.particles t) ∧
        Set.InjOn partnerOfObject (objectsToMatchCloud.particles t) ∧
        ∀ p ∈ objectsToMatchCloud.particles t,
          objectsToMatchCloud.position p.1 p.2 ≤
            availablePartnersCloud.position (partnerOfObject p).1 (partnerOfObject p).2 := by
  rfl

/-- A coherent injective matching of the object slice into the partner slice,
obtained by matching equal ranks.  The partner particle lies weakly to the left
after applying the ordered observation `φ`.

The theorem only asks that ranks separate particles in the object population.  Finite slices
satisfy this through `Cloud.sliceRank_injOn_of_finite`, but the matching itself
does not require a finite or countable root index. -/
theorem Cloud.exists_injective_match_of_rankwiseDominatesBy
    [LT (RootIndexed.TreeNode Root α)] [Preorder Value]
    (φ : Position → Value) {objectsToMatchCloud availablePartnersCloud : Cloud Time Root α Position} (t : Time)
    (hrank : Set.InjOn ((objectsToMatchCloud.mapPosition φ).sliceRank t) (objectsToMatchCloud.particles t))
    (hdom : objectsToMatchCloud.RankwiseDominatesBy φ availablePartnersCloud t) :
    ∃ partnerOfObject : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α,
      Set.MapsTo partnerOfObject (objectsToMatchCloud.particles t) (availablePartnersCloud.particles t) ∧
      Set.InjOn partnerOfObject (objectsToMatchCloud.particles t) ∧
      (∀ p ∈ objectsToMatchCloud.particles t,
        (availablePartnersCloud.mapPosition φ).sliceRank t (partnerOfObject p) =
          (objectsToMatchCloud.mapPosition φ).sliceRank t p) ∧
      ∀ p ∈ objectsToMatchCloud.particles t,
        φ (availablePartnersCloud.position (partnerOfObject p).1 (partnerOfObject p).2) ≤
          φ (objectsToMatchCloud.position p.1 p.2) := by
  classical
  let partnerOfObject : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α :=
    fun p => if hp : p ∈ objectsToMatchCloud.particles t then
      Classical.choose (hdom ((objectsToMatchCloud.mapPosition φ).sliceRank t p) p hp rfl)
    else p
  have hmem : ∀ p (hp : p ∈ objectsToMatchCloud.particles t),
      partnerOfObject p ∈ availablePartnersCloud.particles t := by
    intro p hp
    simp only [partnerOfObject, dite_eq_left hp]
    exact (Classical.choose_spec
      (hdom ((objectsToMatchCloud.mapPosition φ).sliceRank t p) p hp rfl)).1
  have hrank_eq : ∀ p (hp : p ∈ objectsToMatchCloud.particles t),
      (availablePartnersCloud.mapPosition φ).sliceRank t (partnerOfObject p) =
        (objectsToMatchCloud.mapPosition φ).sliceRank t p := by
    intro p hp
    simp only [partnerOfObject, dite_eq_left hp]
    exact (Classical.choose_spec
      (hdom ((objectsToMatchCloud.mapPosition φ).sliceRank t p) p hp rfl)).2.1
  have hle : ∀ p (hp : p ∈ objectsToMatchCloud.particles t),
      φ (availablePartnersCloud.position (partnerOfObject p).1 (partnerOfObject p).2) ≤
      φ (objectsToMatchCloud.position p.1 p.2) := by
    intro p hp
    simp only [partnerOfObject, dite_eq_left hp]
    exact (Classical.choose_spec
      (hdom ((objectsToMatchCloud.mapPosition φ).sliceRank t p) p hp rfl)).2.2
  refine ⟨partnerOfObject, fun p hp => hmem p hp, ?_, hrank_eq, hle⟩
  intro p hp q hq heq
  apply hrank hp hq
  calc
    (objectsToMatchCloud.mapPosition φ).sliceRank t p =
        (availablePartnersCloud.mapPosition φ).sliceRank t (partnerOfObject p) := (hrank_eq p hp).symm
    _ = (availablePartnersCloud.mapPosition φ).sliceRank t (partnerOfObject q) := by rw [heq]
    _ = (objectsToMatchCloud.mapPosition φ).sliceRank t q := hrank_eq q hq

/-- Finite multi-root slices automatically admit the injective rank matching.
Only the slice is finite; the ambient root and child-slot types remain
arbitrary. -/
theorem Cloud.exists_injective_match_of_rankwiseDominatesBy_of_finite
    [LinearOrder (RootIndexed.TreeNode Root α)] [Preorder Value]
    (φ : Position → Value) {objectsToMatchCloud availablePartnersCloud : Cloud Time Root α Position} (t : Time)
    (hfinite : (objectsToMatchCloud.particles t).Finite)
    (hdom : objectsToMatchCloud.RankwiseDominatesBy φ availablePartnersCloud t) :
    ∃ partnerOfObject : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α,
      Set.MapsTo partnerOfObject (objectsToMatchCloud.particles t) (availablePartnersCloud.particles t) ∧
      Set.InjOn partnerOfObject (objectsToMatchCloud.particles t) ∧
      (∀ p ∈ objectsToMatchCloud.particles t,
        (availablePartnersCloud.mapPosition φ).sliceRank t (partnerOfObject p) =
          (objectsToMatchCloud.mapPosition φ).sliceRank t p) ∧
      ∀ p ∈ objectsToMatchCloud.particles t,
        φ (availablePartnersCloud.position (partnerOfObject p).1 (partnerOfObject p).2) ≤
          φ (objectsToMatchCloud.position p.1 p.2) := by
  letI : Fintype ((objectsToMatchCloud.mapPosition φ).particles t) :=
    (show ((objectsToMatchCloud.mapPosition φ).particles t).Finite by simpa using hfinite).fintype
  exact Cloud.exists_injective_match_of_rankwiseDominatesBy φ t
    (Cloud.sliceRank_injOn_of_finite (objectsToMatchCloud.mapPosition φ) t) hdom

/-- Rankwise domination yields the address-order-free matching invariant when
the object ranks separate particles.  This is the safe direction in which the
legacy address-rank interface may be used. -/
theorem Cloud.injectivelyDominatesBy_of_rankwiseDominatesBy
    [LT (RootIndexed.TreeNode Root α)] [Preorder Value]
    (φ : Position → Value) {objectsToMatchCloud availablePartnersCloud : Cloud Time Root α Position} (t : Time)
    (hrank : Set.InjOn ((objectsToMatchCloud.mapPosition φ).sliceRank t) (objectsToMatchCloud.particles t))
    (hdom : objectsToMatchCloud.RankwiseDominatesBy φ availablePartnersCloud t) :
    objectsToMatchCloud.InjectivelyDominatesBy φ availablePartnersCloud t := by
  obtain ⟨f, hfmem, hfinj, _, hfle⟩ :=
    Cloud.exists_injective_match_of_rankwiseDominatesBy φ t hrank hdom
  exact ⟨f, hfmem, hfinj, hfle⟩

theorem Cloud.injectivelyDominatesBy_of_rankwiseDominatesBy_of_finite
    [LinearOrder (RootIndexed.TreeNode Root α)] [Preorder Value]
    (φ : Position → Value) {objectsToMatchCloud availablePartnersCloud : Cloud Time Root α Position} (t : Time)
    (hfinite : (objectsToMatchCloud.particles t).Finite)
    (hdom : objectsToMatchCloud.RankwiseDominatesBy φ availablePartnersCloud t) :
    objectsToMatchCloud.InjectivelyDominatesBy φ availablePartnersCloud t := by
  obtain ⟨f, hfmem, hfinj, _, hfle⟩ :=
    Cloud.exists_injective_match_of_rankwiseDominatesBy_of_finite
      φ t hfinite hdom
  exact ⟨f, hfmem, hfinj, hfle⟩

end Combinatorics.Branching

end
