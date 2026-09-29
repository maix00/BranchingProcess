module

public import Combinatorics.BranchingWalk.Cloud.Basic
public import MeasureTheory.Measure.DiracSum

/-!
# Dirac sums of a cloud

The Dirac sum of an indexed cloud at time `t` is the sum of the Dirac masses at the
positions of the particles alive at that time:

`Cloud.diracSum C t = Measure.sum fun p : (C.particles t) => δ_{position p}`.

The sum is taken over the particles themselves (`Measure.sum`, the supremum of the
finite partial sums), so it needs no measurable structure on the particle index, and
the definition is the Dirac sum `∑ᵢ δ_{xᵢ}`: one
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

@[expose] public section

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris

variable {Time Root α X : Type*}

/-- The Dirac sum of an indexed cloud: at every time, the sum of the Dirac masses at
the positions of the particles alive at that time. -/
noncomputable def Cloud.diracSum [MeasurableSpace X] (C : Cloud Time Root α X) :
    Time → Measure X :=
  fun t => Measure.sum fun p : (C.particles t : Set (RootIndexed.TreeNode Root α)) =>
    Measure.dirac (C.position p.1.1 p.1.2)

/-- The slice Dirac sum on a measurable set is the sum of the indicator of that set
over the particles alive at that time, so two particles at one position contribute
two atoms. -/
theorem Cloud.diracSum_apply [MeasurableSpace X] (C : Cloud Time Root α X)
    (t : Time) {s : Set X} (hs : MeasurableSet s) :
    C.diracSum t s = ∑' p : (C.particles t : Set (RootIndexed.TreeNode Root α)),
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

set_option linter.style.haveILetI false in
/-- The indicator sum of a countable set is its `encard`, as a value in `ℝ≥0∞`. No
measurable structure on the index is needed: the counting measure of the index is
taken with the discrete σ-algebra installed inside the proof, and mathlib's
`Measure.count_apply` identifies it with the `encard`. -/
theorem tsum_indicator_eq_encard_of_countable {ι : Type*} [Countable ι] (s : Set ι) :
    ∑' i : ι, (if i ∈ s then (1 : ℝ≥0∞) else 0) = (s.encard : ℝ≥0∞) := by
  classical
  letI : MeasurableSpace ι := ⊤
  have hs : MeasurableSet s := trivial
  rw [← Measure.count_apply hs,
    show (Measure.count : Measure ι) = Measure.sum (fun i => Measure.dirac i) from rfl,
    Measure.sum_apply_of_countable]
  refine tsum_congr fun i => ?_
  rw [Measure.dirac_apply' i hs]
  by_cases hi : i ∈ s <;> simp [hi]

/-- On a countable slice, the slice Dirac sum at *any* test set is the indicator sum
over the particles alive at that time: the test set need not be measurable. -/
theorem Cloud.diracSum_apply_of_countable [MeasurableSpace X] [MeasurableSingletonClass X]
    [Countable (RootIndexed.TreeNode Root α)] (C : Cloud Time Root α X) (t : Time) (s : Set X) :
    C.diracSum t s = ∑' p : (C.particles t : Set (RootIndexed.TreeNode Root α)),
      (if C.position p.1.1 p.1.2 ∈ s then 1 else 0) := by
  classical
  rw [Cloud.diracSum, Measure.sum_apply_of_countable]
  refine tsum_congr fun p => ?_
  by_cases hp : C.position p.1.1 p.1.2 ∈ s
  · rw [ite_eq_left hp, Measure.dirac_apply_of_mem hp]
  · rw [ite_eq_right (fun h => hp h)]
    have hle : Measure.dirac (C.position p.1.1 p.1.2) s ≤
        Measure.dirac (C.position p.1.1 p.1.2) ({C.position p.1.1 p.1.2}ᶜ : Set X) :=
      measure_mono fun j hj => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact fun hji => hp (hji ▸ hj)
    rw [Measure.dirac_apply' _
      (MeasurableSet.compl (measurableSet_singleton (C.position p.1.1 p.1.2)))] at hle
    simpa using hle

/-- On a countable slice, the Dirac sum at a threshold is the number of particles
whose position is at most the threshold. The count is taken in the particle index
itself: no transport between encodings is needed, and multiplicity is kept. -/
theorem Cloud.diracSum_Iic_eq_encard_of_countable [MeasurableSpace X]
    [MeasurableSingletonClass X] [Countable (RootIndexed.TreeNode Root α)] [Preorder X]
    (C : Cloud Time Root α X) (t : Time) (a : X) :
    C.diracSum t (Set.Iic a) =
      (({p : (C.particles t : Set (RootIndexed.TreeNode Root α)) |
          C.position p.1.1 p.1.2 ≤ a} : Set _).encard : ℝ≥0∞) := by
  rw [Cloud.diracSum_apply_of_countable C t (Set.Iic a)]
  refine (tsum_congr fun p => ?_).trans (tsum_indicator_eq_encard_of_countable _)
  by_cases hp : C.position p.1.1 p.1.2 ≤ a <;> simp [hp, Set.mem_Iic]

end Branching

end Combinatorics

end
