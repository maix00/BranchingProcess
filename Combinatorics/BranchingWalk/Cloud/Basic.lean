import Mathlib.Data.Set.Basic
import Mathlib.Order.OrderDual
import Combinatorics.BranchingWalk.Basic.Position
import Combinatorics.BranchingWalk.Basic.SurviveAlong
import Combinatorics.BranchingWalk.Basic.Descendant

/-!
# Time-indexed particle clouds

A `Cloud Time Root α X` is an indexed particle cloud: at every time it holds a
set of particles, each one an initial root together with the address it sits at,
and `position` reads the position of a particle. Its `support` is the geometric
image `CloudSet Time X`. The branching-step data and the initial positions
generate the indexed cloud in `Cloud.ofBranchingWalk` (at a time map) and
`Cloud.discreteTimeCloud_ofBranchingWalk` (at the generations); the geometric
image is its `support`.
`Time` is only an indexing type here.  No temporal order or claim that it
contains the natural-number generations is built into `Cloud`.
The multi-root construction is primitive: each root supplies its own step
field and initial position, and the cloud is their union.  The single-root
construction is the special case with the singleton root type `Unit`.
-/

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris

/-- An indexed cloud of points in `X`. -/
structure CloudSet (Time X : Type*) where
  points : Time → Set X

/-- An indexed particle cloud of a branching walk: a particle is an initial root
together with the address it sits at, so the index of a cloud is the walk's own
data and not a free parameter. The index retains root and node identity even
when two particles have the same spatial position, unlike the geometric
`CloudSet` it maps to. -/
structure Cloud (Time Root α X : Type*) where
  particles : Time → Set (RootIndexed.TreeNode Root α)
  position : Root → TreeNode α → X

/-- Replace the particle slices of a cloud by finite labelled populations,
while retaining its position map. Particle identity, and hence multiplicity at
equal positions, is preserved. -/
def Cloud.withFinsetParticles {Time Root α X : Type*}
    (C : Cloud Time Root α X)
    (s : Time → Finset (RootIndexed.TreeNode Root α)) : Cloud Time Root α X where
  particles t := ↑(s t)
  position := C.position

@[simp] theorem Cloud.withFinsetParticles_particles {Time Root α X : Type*}
    (C : Cloud Time Root α X)
    (s : Time → Finset (RootIndexed.TreeNode Root α)) (t : Time) :
    (C.withFinsetParticles s).particles t = ↑(s t) :=
  rfl

@[simp] theorem Cloud.withFinsetParticles_position {Time Root α X : Type*}
    (C : Cloud Time Root α X)
    (s : Time → Finset (RootIndexed.TreeNode Root α)) (r : Root)
    (u : TreeNode α) :
    (C.withFinsetParticles s).position r u = C.position r u :=
  rfl

def Cloud.support {Time Root α X : Type*} (C : Cloud Time Root α X) :
    CloudSet Time X where
  points t := (fun p : RootIndexed.TreeNode Root α => C.position p.1 p.2) '' C.particles t

/-- Apply an observation to every particle position while preserving particle
identity and time slices. -/
def Cloud.mapPosition {Time Root α X Y : Type*} (φ : X → Y)
    (C : Cloud Time Root α X) : Cloud Time Root α Y where
  particles := C.particles
  position r u := φ (C.position r u)

@[simp] theorem Cloud.mapPosition_particles {Time Root α X Y : Type*}
    (φ : X → Y) (C : Cloud Time Root α X) (t : Time) :
    (C.mapPosition φ).particles t = C.particles t :=
  rfl

@[simp] theorem Cloud.mapPosition_position {Time Root α X Y : Type*}
    (φ : X → Y) (C : Cloud Time Root α X) (r : Root) (u : TreeNode α) :
    (C.mapPosition φ).position r u = φ (C.position r u) :=
  rfl

/-- The cloud of a walk read at a time map: the particles alive at `t` are the
realized addresses read at `t`. A walk's selection compares positions, so the time
a cloud is read at is extra structure and not part of the walk. -/
def Cloud.ofBranchingWalk {Time Root α Mark Position : Type*}
    [AddCommMonoid Position] (d : Mark → Position)
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (time : TreeNode α → Time) : Cloud Time Root α Position where
  particles t := {p | time p.2 = t ∧ surviveAlong (β.step p.1) [] p.2}
  position := β.position d

/-- The cloud of a walk read at the generations: the particles alive at
generation `n` are the realized addresses of depth `n`. The generation is the
length of the address, so this is `Cloud.ofBranchingWalk` at `fun u => u.length`. -/
def Cloud.discreteTimeCloud_ofBranchingWalk {Root α Mark Position : Type*}
    [AddCommMonoid Position] (d : Mark → Position)
    (β : RootIndexed.BranchingWalk Root α Mark Position) :
    Cloud ℕ Root α Position :=
  Cloud.ofBranchingWalk d β generation

/-- A child `u ++ [j]` of a realized node `u` of the root `r` is a particle of
the walk's cloud at its own time exactly when the slot `j` survives in the step
at `u`. The cloud is indexed by `RootIndexed.TreeNode Root α` and the slots of one step by
`α`, so this is the correspondence between the two indexings: a rank in the cloud
and a rank in the step can only be compared through it. -/
theorem Cloud.ofBranchingWalk_mem_particles_child
    {Root α Mark Position Time : Type*} [AddCommMonoid Position]
    (d : Mark → Position) (β : RootIndexed.BranchingWalk Root α Mark Position)
    (time : TreeNode α → Time)
    {r : Root} {u : TreeNode α}
    (hu : surviveAlong (β.step r) [] u) (j : α) :
    ((r, u ++ [j]) : RootIndexed.TreeNode Root α) ∈
        (Cloud.ofBranchingWalk d β time).particles (time (u ++ [j])) ↔
      survive (β.step r u) j := by
  have hmem : ((r, u ++ [j]) : RootIndexed.TreeNode Root α) ∈
      (Cloud.ofBranchingWalk d β time).particles (time (u ++ [j])) ↔
      surviveAlong (β.step r) [] (u ++ [j]) := by
    simp [Cloud.ofBranchingWalk]
  rw [hmem, surviveAlong_root_append_singleton_iff]
  exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩

/-- Transport an indexed cloud to the order-dual value type. The particles are the
same; only the positions are read in the reversed order. -/
def Cloud.mapOrderDual (C : Cloud Time Root α X) :
    Cloud Time Root α (OrderDual X) where
  particles := C.particles
  position r u := OrderDual.toDual (C.position r u)

namespace CloudSet

variable {Time X : Type*}

instance : Membership (Time × X) (CloudSet Time X) where
  mem C p := p.2 ∈ C.points p.1

/-- Push a geometric cloud through an arbitrary observation of its points. -/
def map {Y : Type*} (φ : X → Y) (C : CloudSet Time X) : CloudSet Time Y where
  points t := φ '' C.points t

/-- The space-time set of all points of a cloud. -/
def vertexSet (C : CloudSet Time X) : Set (Time × X) :=
  {p | p ∈ C}

@[simp] theorem mem_vertexSet (C : CloudSet Time X) (p : Time × X) :
    p ∈ C.vertexSet ↔ p ∈ C :=
  Iff.rfl

@[ext] theorem ext {C D : CloudSet Time X}
    (h : ∀ t x, x ∈ C.points t ↔ x ∈ D.points t) : C = D := by
  cases C with
  | mk Cpoints =>
    cases D with
    | mk Dpoints =>
      congr
      funext t
      ext x
      exact h t x

@[simp] theorem support_mapPosition {Root α Y : Type*} (φ : X → Y)
    (C : Cloud Time Root α X) :
    (C.mapPosition φ).support = C.support.map φ := by
  apply CloudSet.ext
  intro t y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨C.position p.1 p.2, ⟨p, hp, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨p, hp, hpx⟩, rfl⟩
    refine ⟨p, hp, ?_⟩
    change φ (C.position p.1 p.2) = φ x
    exact congrArg φ hpx

/-- Transport a cloud to the order-dual value type. Reversing the order on
positions reverses the order on every time slice. -/
def mapOrderDual (C : CloudSet Time X) : CloudSet Time (OrderDual X) where
  points t := OrderDual.toDual '' C.points t

@[simp] theorem mem_mapOrderDual_points (C : CloudSet Time X) (t : Time)
    (x : X) :
    OrderDual.toDual x ∈ (C.mapOrderDual).points t ↔ x ∈ C.points t := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := OrderDual.toDual_inj.mp hyx
    simpa [hyx'] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end CloudSet

/-- The particles of a walk's cloud at a time are exactly the surviving particles whose time is that
time: the cloud's slices are the time slices of the walk's realized particles, so the value of
`Cloud.particles` over all times is the set of descendants of the root particles. -/
theorem Cloud.mem_ofBranchingWalk_particles_iff {Time Root α Mark Position : Type*} [AddCommMonoid Position]
    (d : Mark → Position) (β : RootIndexed.BranchingWalk Root α Mark Position)
    (time : TreeNode α → Time) (t : Time)
    (p : RootIndexed.TreeNode Root α) :
    p ∈ (Cloud.ofBranchingWalk d β time).particles t ↔
      time p.2 = t ∧ p ∈ survivingParticles β := by
  unfold Cloud.ofBranchingWalk
  change time p.2 = t ∧ surviveAlong (β.step p.1) [] p.2 ↔
    time p.2 = t ∧ p ∈ survivingParticles β
  rw [← mem_survivingParticles_iff_surviveAlong]

/-- Reading a walk's cloud at the generations cuts the surviving particles by generation: the slice
at `k` is exactly the surviving particles of generation `k`. -/
theorem Cloud.discreteTimeCloud_particles_eq_survivingParticlesAt {Root α Mark Position : Type*}
    [AddCommMonoid Position] (d : Mark → Position)
    (β : RootIndexed.BranchingWalk Root α Mark Position) (k : ℕ) :
    (Cloud.discreteTimeCloud_ofBranchingWalk d β).particles k = survivingParticlesAt β k := by
  ext p
  simp only [Cloud.discreteTimeCloud_ofBranchingWalk]
  rw [Cloud.mem_ofBranchingWalk_particles_iff, mem_survivingParticlesAt_iff, generation_def,
    and_comm]

end Branching

end Combinatorics
