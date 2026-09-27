import Combinatorics.BranchingWalk.Cloud.Basic
import MeasureTheory.Measure.DiracSum

/-!
# Dirac sums of a cloud

The Dirac sum of an indexed cloud at time `t` is the sum of the Dirac masses at the
positions of the particles alive at that time:

`Cloud.diracSum C t = Measure.sum fun p : (C.particles t) => δ_{position p}`.

The sum is taken over the particles themselves (`Measure.sum`, the supremum of the
finite partial sums), so it needs no measurable structure on the particle index, and
the definition is exactly the thesis's `∑ᵢ δ_{xᵢ}` (`contents/n-brw/intro.tex`): one
atom per particle, so two particles at the same position count twice. That
multiplicity is what the domination order is about, and it is why the order is
stated for the indexed cloud: the geometric `CloudSet` records point sets, which
cannot tell two particles at one position apart.

Evaluating the slice on a measurable set needs measurability of *that set in the
value space* only. On a finite slice, mathlib's `Measure.sum_coe_finset` and
`Measure.sum_fintype` turn the sum into a finite one, which is what lets the order be
read as a count of particles below a threshold without any `tsum`/`encard`
conversion. The counting form of that comparison is recorded in
`Order/Slice.lean`. Identifying the slice with the image of the counting measure on
the particles, `Measure.map (·.position) (Measure.count.restrict (·.particles t))`, is
the one statement that would need the position map to be measurable, i.e. a
measurable structure on the particle index; it is deliberately not part of this
layer.
-/

open Classical MeasureTheory
open scoped ENNReal

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris

variable {Time Root α X : Type*}

/-- The Dirac sum of an indexed cloud: at every time, the sum of the Dirac masses at
the positions of the particles alive at that time. -/
noncomputable def Cloud.diracSum [MeasurableSpace X] (C : Cloud Time Root α X) :
    Time → Measure X :=
  fun t => Measure.sum fun p : (C.particles t : Set (Root × TreeNode α)) =>
    Measure.dirac (C.position p.1.1 p.1.2)

/-- The slice Dirac sum on a measurable set is the sum of the indicator of that set
over the particles alive at that time, so two particles at one position contribute
two atoms. -/
theorem Cloud.diracSum_apply [MeasurableSpace X] (C : Cloud Time Root α X)
    (t : Time) {s : Set X} (hs : MeasurableSet s) :
    C.diracSum t s = ∑' p : (C.particles t : Set (Root × TreeNode α)),
      (if C.position p.1.1 p.1.2 ∈ s then 1 else 0) := by
  classical
  rw [Cloud.diracSum, Measure.sum_apply _ hs]
  refine tsum_congr fun p => ?_
  rw [Measure.dirac_apply' _ hs]
  by_cases hp : C.position p.1.1 p.1.2 ∈ s <;> simp [hp]

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

/-- Reversing the positions of a cloud reverses its Dirac sums: the Dirac sum of the
order-dual cloud is the image of the Dirac sum along `OrderDual.toDual`. -/
theorem Cloud.mapOrderDual_diracSum [MeasurableSpace X] (C : Cloud Time Root α X) :
    (C.mapOrderDual).diracSum = fun t => (C.diracSum t).map OrderDual.toDual := by
  have hf : Measurable (OrderDual.toDual : X → OrderDual X) := measurable_id
  funext t
  rw [Cloud.diracSum, Cloud.diracSum,
    Measure.map_sum (show AEMeasurable (OrderDual.toDual : X → OrderDual X)
      _ from hf.aemeasurable)]
  refine congr_arg Measure.sum (funext fun p => ?_)
  simp only [Cloud.mapOrderDual]
  exact (Measure.map_dirac_of_measurable hf _).symm

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
