import Combinatorics.BranchingWalk.Cloud.Basic
import MeasureTheory.Measure.DiracSum

/-!
# Dirac sums of a cloud

The Dirac sum of an indexed cloud at time `t` is the sum of the Dirac masses at
the positions of the particles alive at that time:

`Cloud.diracSum C t = Measure.sum fun p => if p ∈ C.particles t then δ_{position p} else 0`.

`Measure.sum` is the supremum of the finite partial sums, so it needs no measurable
structure on the particle index at all, and the definition is exactly the thesis's
`∑ᵢ δ_{xᵢ}` (`contents/n-brw/intro.tex`): one atom per particle, so two particles at
the same position count twice. That multiplicity is what the domination order is
about, and it is why the order is stated for the indexed cloud: the geometric
`CloudSet` records point sets, which cannot tell two particles at one position
apart.

Evaluating the slice on a measurable set needs measurability of *that set in the
value space* only. Identifying the slice with the image of the counting measure on
the particles, `Measure.map (·.position) (Measure.count.restrict (·.particles t))`,
does need the position map to be measurable, i.e. a measurable structure on the
particle index `Root × TreeNode α`; that is the only place where such a structure
is used, and it is why the order below is stated on the Dirac sums themselves.
-/

open Classical MeasureTheory

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris

variable {Time Root α X : Type*}

/-- The Dirac sum of an indexed cloud: at every time, the sum of the Dirac masses
at the positions of the particles alive at that time. -/
noncomputable def Cloud.diracSum [MeasurableSpace X] (C : Cloud Time Root α X) :
    Time → Measure X :=
  fun t => by
    classical
    exact Measure.sum fun p : Root × TreeNode α =>
      if p ∈ C.particles t then Measure.dirac (C.position p.1 p.2) else 0

/-- The slice Dirac sum on a measurable set is the number of particles alive at
that time whose position lies in the set, summed over the particles: two particles
at one position contribute two atoms. -/
theorem Cloud.diracSum_apply [MeasurableSpace X] (C : Cloud Time Root α X)
    (t : Time) {s : Set X} (hs : MeasurableSet s) :
    C.diracSum t s =
      ∑' p : Root × TreeNode α,
        if p ∈ C.particles t ∧ C.position p.1 p.2 ∈ s then 1 else 0 := by
  classical
  rw [Cloud.diracSum, Measure.sum_apply _ hs]
  refine tsum_congr fun p => ?_
  by_cases hp : p ∈ C.particles t
  · rw [ite_eq_left hp, Measure.dirac_apply' _ hs]
    by_cases hps : C.position p.1 p.2 ∈ s
    · rw [ite_eq_left (⟨hp, hps⟩ : p ∈ C.particles t ∧ C.position p.1 p.2 ∈ s)]
      simp [hps]
    · rw [ite_eq_right (fun h => hps h.2)]
      simp [hps]
  · rw [ite_eq_right (fun h => hp h) ]
    simp [hp]

/-- A Dirac mass pushed forward along a measurable map is the Dirac mass at the
image. Mathlib's `Measure.map_dirac` assumes measurable singletons on both sides;
here only the measurability of the map is needed. -/
theorem Measure.map_dirac_of_measurable {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {f : X → Y} (hf : Measurable f) (x : X) :
    Measure.map f (Measure.dirac x) = Measure.dirac (f x) := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.dirac_apply' _ (hf hs),
    Measure.dirac_apply' _ hs, Set.indicator_apply, Set.indicator_apply,
    Set.mem_preimage]
  rfl

/-- Reversing the positions of a cloud reverses its Dirac sums: the Dirac sum of
the order-dual cloud is the image of the Dirac sum along `OrderDual.toDual`. -/
theorem Cloud.mapOrderDual_diracSum [MeasurableSpace X] (C : Cloud Time Root α X) :
    (C.mapOrderDual).diracSum = fun t => (C.diracSum t).map OrderDual.toDual := by
  have hf : Measurable (OrderDual.toDual : X → OrderDual X) := measurable_id
  funext t
  ext s hs
  rw [Cloud.diracSum_apply (C.mapOrderDual) t hs, Measure.map_apply hf hs,
    Cloud.diracSum_apply C t (hf hs)]
  refine tsum_congr fun p => ?_
  simp only [Cloud.mapOrderDual, Set.mem_preimage]
  rfl

/-- The reversed reading of a slice at a threshold is the original slice at the
opposite half-line. The half-line is assumed measurable here, a condition on the
value space and not on the particle index. -/
theorem Cloud.mapOrderDual_diracSum_Iic [MeasurableSpace X] [Preorder X]
    (C : Cloud Time Root α X) (t : Time) (a : X)
    (ha : MeasurableSet (Set.Iic (OrderDual.toDual a))) :
    (C.mapOrderDual).diracSum t (Set.Iic (OrderDual.toDual a)) =
      C.diracSum t (Set.Ici a) := by
  have hf : Measurable (OrderDual.toDual : X → OrderDual X) := measurable_id
  rw [Cloud.mapOrderDual_diracSum, Measure.map_apply hf ha,
    show (OrderDual.toDual : X → OrderDual X) ⁻¹' Set.Iic (OrderDual.toDual a) = Set.Ici a from
      Set.ext fun _ => by
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici, OrderDual.toDual_le_toDual]]

end Branching

end Combinatorics
