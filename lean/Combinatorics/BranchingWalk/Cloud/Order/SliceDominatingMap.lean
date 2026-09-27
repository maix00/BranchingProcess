import Combinatorics.BranchingWalk.Cloud.Order.Slice
import Combinatorics.BranchingWalk.Cloud.Order.DominatingMap

/-!
# Particle matching extracted from rankwise domination

Rankwise domination is stated without choosing a global correspondence.  For
the offspring coupling we need one coherent parent map.  This file extracts
that map and proves it is injective whenever ranks distinguish the particles
of the source slice.  The particles retain their full multi-root labels
`Root × TreeNode α`; no finiteness or countability of the root type is used.
-/

open Combinatorics.UlamHarris

namespace Combinatorics.Branching

set_option linter.style.haveILetI false

variable {Time Root α Position Value : Type*}

/-- An order-dominating map between two cloud slices.  This is the cloud-slice
specialization of `Cloud.DominatingMap`; it is pathwise data rather
than a coupling of probability measures. -/
abbrev Cloud.SliceDominatingMap [Preorder Value]
    (φ : Position → Value) (C D : Cloud Time Root α Position)
    (t : Time) :=
  Cloud.DominatingMap (C.particles t) (D.particles t)
    (fun p => φ (C.position p.1 p.2))
    (fun p => φ (D.position p.1 p.2))

namespace Cloud.SliceDominatingMap

variable [Preorder Value]

instance (φ : Position → Value) (C D : Cloud Time Root α Position)
    (t : Time) : CoeFun (Cloud.SliceDominatingMap φ C D t)
      (fun _ => RootIndexed.TreeNode Root α →
        RootIndexed.TreeNode Root α) :=
  ⟨Cloud.DominatingMap.toFun⟩

/-- The identity dominating map of a cloud slice. -/
def refl (φ : Position → Value) (C : Cloud Time Root α Position)
    (t : Time) : Cloud.SliceDominatingMap φ C C t :=
  Cloud.DominatingMap.refl (C.particles t)
    (fun p => φ (C.position p.1 p.2))

/-- Composition retains the concrete particle correspondence. -/
def trans {φ : Position → Value} {C D E : Cloud Time Root α Position} {t : Time}
    (f : Cloud.SliceDominatingMap φ C D t)
    (g : Cloud.SliceDominatingMap φ D E t) :
    Cloud.SliceDominatingMap φ C E t :=
  Cloud.DominatingMap.trans f g

end Cloud.SliceDominatingMap

/-- The coupling invariant needed by offspring propagation: every source
particle is assigned injectively to a target particle whose observed position
lies weakly to its left.  This definition is independent of the ambient order
on particle addresses and therefore applies to random spatial configurations
without pretending that their addresses are already position-sorted. -/
def Cloud.InjectivelyDominatesBy [Preorder Value]
    (φ : Position → Value) (C D : Cloud Time Root α Position) (t : Time) : Prop :=
  ∃ matchParticle : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α,
    Set.MapsTo matchParticle (C.particles t) (D.particles t) ∧
    Set.InjOn matchParticle (C.particles t) ∧
    ∀ p ∈ C.particles t,
      φ (D.position (matchParticle p).1 (matchParticle p).2) ≤
        φ (C.position p.1 p.2)

/-- Forget the concrete coupling state and retain only its existence. -/
theorem Cloud.SliceDominatingMap.injectivelyDominatesBy [Preorder Value]
    {φ : Position → Value} {C D : Cloud Time Root α Position} {t : Time}
    (f : Cloud.SliceDominatingMap φ C D t) :
    C.InjectivelyDominatesBy φ D t :=
  ⟨f, f.mapsTo, f.injOn, f.dominates⟩

/-- The propositional domination relation is exactly the existence of a
concrete dominating injection. -/
theorem Cloud.injectivelyDominatesBy_iff_nonempty [Preorder Value]
    (φ : Position → Value) (C D : Cloud Time Root α Position) (t : Time) :
    C.InjectivelyDominatesBy φ D t ↔
      Nonempty (Cloud.SliceDominatingMap φ C D t) := by
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
    {C D : Cloud Time Root α Position} {t : Time}
    (h : C.InjectivelyDominatesBy φ D t) :
    Cloud.SliceDominatingMap φ C D t :=
  Classical.choice ((Cloud.injectivelyDominatesBy_iff_nonempty φ C D t).mp h)

theorem Cloud.injectivelyDominatesBy_refl [Preorder Value]
    (φ : Position → Value) (C : Cloud Time Root α Position) (t : Time) :
    C.InjectivelyDominatesBy φ C t := by
  exact (Cloud.SliceDominatingMap.refl φ C t).injectivelyDominatesBy

/-- Inclusion of particle labels gives the canonical injective matching when
the target position at each retained label is no larger in the observed
order. -/
theorem Cloud.injectivelyDominatesBy_of_particles_subset [Preorder Value]
    (φ : Position → Value) {C D : Cloud Time Root α Position} (t : Time)
    (hsubset : C.particles t ⊆ D.particles t)
    (hposition : ∀ p ∈ C.particles t,
      φ (D.position p.1 p.2) ≤ φ (C.position p.1 p.2)) :
    C.InjectivelyDominatesBy φ D t := by
  exact ⟨id, hsubset, Set.injOn_id _, hposition⟩

theorem Cloud.injectivelyDominatesBy_trans [Preorder Value]
    (φ : Position → Value) {C D E : Cloud Time Root α Position} (t : Time)
    (hCD : C.InjectivelyDominatesBy φ D t)
    (hDE : D.InjectivelyDominatesBy φ E t) :
    C.InjectivelyDominatesBy φ E t := by
  rw [Cloud.injectivelyDominatesBy_iff_nonempty] at hCD hDE ⊢
  rcases hCD with ⟨f⟩
  rcases hDE with ⟨g⟩
  exact ⟨f.trans g⟩

/-- Reading the observation in `OrderDual Value` reverses the spatial
inequality while preserving the direction of the particle matching and its
cardinality comparison.  Thus left and right versions use one invariant; the
two cloud arguments are not exchanged. -/
theorem Cloud.injectivelyDominatesBy_toDual_iff [Preorder Value]
    (φ : Position → Value) (C D : Cloud Time Root α Position) (t : Time) :
    C.InjectivelyDominatesBy (fun x => OrderDual.toDual (φ x)) D t ↔
      ∃ matchParticle : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α,
        Set.MapsTo matchParticle (C.particles t) (D.particles t) ∧
        Set.InjOn matchParticle (C.particles t) ∧
        ∀ p ∈ C.particles t,
          φ (C.position p.1 p.2) ≤
            φ (D.position (matchParticle p).1 (matchParticle p).2) := by
  rfl

/-- Same duality when the cloud's position type itself is replaced by its
order dual. -/
theorem Cloud.injectivelyDominates_mapOrderDual_iff [Preorder Position]
    (C D : Cloud Time Root α Position) (t : Time) :
    (C.mapOrderDual).InjectivelyDominatesBy id (D.mapOrderDual) t ↔
      ∃ matchParticle : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α,
        Set.MapsTo matchParticle (C.particles t) (D.particles t) ∧
        Set.InjOn matchParticle (C.particles t) ∧
        ∀ p ∈ C.particles t,
          C.position p.1 p.2 ≤
            D.position (matchParticle p).1 (matchParticle p).2 := by
  rfl

/-- A coherent injective matching of the source slice into the target slice,
obtained by matching equal ranks.  The target particle lies weakly to the left
after applying the ordered observation `φ`.

The theorem only asks that ranks separate source particles.  Finite slices
satisfy this through `Cloud.sliceRank_injOn_of_finite`, but the matching itself
does not require a finite or countable root index. -/
theorem Cloud.exists_injective_match_of_rankwiseDominatesBy
    [LT (RootIndexed.TreeNode Root α)] [Preorder Value]
    (φ : Position → Value) {C D : Cloud Time Root α Position} (t : Time)
    (hrank : Set.InjOn ((C.mapPosition φ).sliceRank t) (C.particles t))
    (hdom : C.RankwiseDominatesBy φ D t) :
    ∃ matchParticle : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α,
      Set.MapsTo matchParticle (C.particles t) (D.particles t) ∧
      Set.InjOn matchParticle (C.particles t) ∧
      (∀ p ∈ C.particles t,
        (D.mapPosition φ).sliceRank t (matchParticle p) =
          (C.mapPosition φ).sliceRank t p) ∧
      ∀ p ∈ C.particles t,
        φ (D.position (matchParticle p).1 (matchParticle p).2) ≤
          φ (C.position p.1 p.2) := by
  classical
  let matchParticle : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α :=
    fun p => if hp : p ∈ C.particles t then
      Classical.choose (hdom ((C.mapPosition φ).sliceRank t p) p hp rfl)
    else p
  have hmem : ∀ p (hp : p ∈ C.particles t),
      matchParticle p ∈ D.particles t := by
    intro p hp
    simp only [matchParticle, dite_eq_left hp]
    exact (Classical.choose_spec
      (hdom ((C.mapPosition φ).sliceRank t p) p hp rfl)).1
  have hrank_eq : ∀ p (hp : p ∈ C.particles t),
      (D.mapPosition φ).sliceRank t (matchParticle p) =
        (C.mapPosition φ).sliceRank t p := by
    intro p hp
    simp only [matchParticle, dite_eq_left hp]
    exact (Classical.choose_spec
      (hdom ((C.mapPosition φ).sliceRank t p) p hp rfl)).2.1
  have hle : ∀ p (hp : p ∈ C.particles t),
      φ (D.position (matchParticle p).1 (matchParticle p).2) ≤
      φ (C.position p.1 p.2) := by
    intro p hp
    simp only [matchParticle, dite_eq_left hp]
    exact (Classical.choose_spec
      (hdom ((C.mapPosition φ).sliceRank t p) p hp rfl)).2.2
  refine ⟨matchParticle, fun p hp => hmem p hp, ?_, hrank_eq, hle⟩
  intro p hp q hq heq
  apply hrank hp hq
  calc
    (C.mapPosition φ).sliceRank t p =
        (D.mapPosition φ).sliceRank t (matchParticle p) := (hrank_eq p hp).symm
    _ = (D.mapPosition φ).sliceRank t (matchParticle q) := by rw [heq]
    _ = (C.mapPosition φ).sliceRank t q := hrank_eq q hq

/-- Finite multi-root slices automatically admit the injective rank matching.
Only the slice is finite; the ambient root and child-slot types remain
arbitrary. -/
theorem Cloud.exists_injective_match_of_rankwiseDominatesBy_of_finite
    [LinearOrder (RootIndexed.TreeNode Root α)] [Preorder Value]
    (φ : Position → Value) {C D : Cloud Time Root α Position} (t : Time)
    (hfinite : (C.particles t).Finite)
    (hdom : C.RankwiseDominatesBy φ D t) :
    ∃ matchParticle : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α,
      Set.MapsTo matchParticle (C.particles t) (D.particles t) ∧
      Set.InjOn matchParticle (C.particles t) ∧
      (∀ p ∈ C.particles t,
        (D.mapPosition φ).sliceRank t (matchParticle p) =
          (C.mapPosition φ).sliceRank t p) ∧
      ∀ p ∈ C.particles t,
        φ (D.position (matchParticle p).1 (matchParticle p).2) ≤
          φ (C.position p.1 p.2) := by
  letI : Fintype ((C.mapPosition φ).particles t) :=
    (show ((C.mapPosition φ).particles t).Finite by simpa using hfinite).fintype
  exact Cloud.exists_injective_match_of_rankwiseDominatesBy φ t
    (Cloud.sliceRank_injOn_of_finite (C.mapPosition φ) t) hdom

/-- Rankwise domination yields the address-order-free matching invariant when
the source ranks separate particles.  This is the safe direction in which the
legacy address-rank interface may be used. -/
theorem Cloud.injectivelyDominatesBy_of_rankwiseDominatesBy
    [LT (RootIndexed.TreeNode Root α)] [Preorder Value]
    (φ : Position → Value) {C D : Cloud Time Root α Position} (t : Time)
    (hrank : Set.InjOn ((C.mapPosition φ).sliceRank t) (C.particles t))
    (hdom : C.RankwiseDominatesBy φ D t) :
    C.InjectivelyDominatesBy φ D t := by
  obtain ⟨f, hfmem, hfinj, _, hfle⟩ :=
    Cloud.exists_injective_match_of_rankwiseDominatesBy φ t hrank hdom
  exact ⟨f, hfmem, hfinj, hfle⟩

theorem Cloud.injectivelyDominatesBy_of_rankwiseDominatesBy_of_finite
    [LinearOrder (RootIndexed.TreeNode Root α)] [Preorder Value]
    (φ : Position → Value) {C D : Cloud Time Root α Position} (t : Time)
    (hfinite : (C.particles t).Finite)
    (hdom : C.RankwiseDominatesBy φ D t) :
    C.InjectivelyDominatesBy φ D t := by
  obtain ⟨f, hfmem, hfinj, _, hfle⟩ :=
    Cloud.exists_injective_match_of_rankwiseDominatesBy_of_finite
      φ t hfinite hdom
  exact ⟨f, hfmem, hfinj, hfle⟩

end Combinatorics.Branching
