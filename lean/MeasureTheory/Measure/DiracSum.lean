module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import MeasureTheory.MeasurableSpace.Option

@[expose] public section

/-!
# Dirac sums

Mathlib already defines the counting measure as
`Measure.count = Measure.sum Measure.dirac` and proves the decomposition
lemmas `Measure.sum_smul_dirac` and `Measure.map_eq_sum`. The one shape used by
the additional construction beyond that API is the Dirac sum of an indexed family of points,
`∑ i, δ_{f i}`. This file packages that shape with its evaluation lemmas; it
introduces no new measure theory.

The set-indexed case needs no new definition: the Dirac sum over a set `s` is
Mathlib's `Measure.count.restrict s`, whose value on a measurable `t` is
`(t ∩ s).encard` by `Measure.count_apply`.
-/

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

namespace Measure

variable {ι X : Type*} [MeasurableSpace X]

/-- The Dirac sum of an indexed family of points of `X`. -/
noncomputable def iDiracSum (f : ι → X) : Measure X :=
  sum fun i => dirac (f i)

/-- The Dirac sum of an option-valued family: absent slots contribute zero. -/
noncomputable def iOptionDiracSum (f : ι → Option X) : Measure X :=
  sum fun i => (f i).elim 0 dirac

/-- The measure contributed by one optional point is measurable in that
optional point. Absence contributes the zero measure, independently of any
algebraic structure on `X`. -/
theorem measurable_option_dirac :
    Measurable (fun x : Option X => x.elim 0 (dirac : X → Measure X)) :=
  measurable_option_elim 0 measurable_dirac

theorem iDiracSum_eq_iOptionDiracSum (f : ι → X) :
    iDiracSum f = iOptionDiracSum (fun i => some (f i)) :=
  rfl

theorem iDiracSum_apply (f : ι → X) {s : Set X} (hs : MeasurableSet s) :
    iDiracSum f s = ∑' i, s.indicator (1 : X → ℝ≥0∞) (f i) := by
  simp only [iDiracSum, sum_apply _ hs]
  exact tsum_congr fun i => dirac_apply' _ hs

theorem iOptionDiracSum_apply (f : ι → Option X) {s : Set X} (hs : MeasurableSet s) :
    iOptionDiracSum f s =
      ∑' i, match f i with
        | some x => s.indicator (1 : X → ℝ≥0∞) x
        | none => 0 := by
  simp only [iOptionDiracSum, sum_apply _ hs]
  refine tsum_congr fun i => ?_
  cases f i <;> simp [dirac_apply' _ hs]

/-- The Dirac sum of a countable optional family is measurable as a
measure-valued function. -/
theorem iOptionDiracSum_measurable [Countable ι] :
    Measurable (iOptionDiracSum : (ι → Option X) → Measure X) := by
  refine measurable_of_measurable_coe _ fun s hs => ?_
  change Measurable (fun f : ι → Option X => iOptionDiracSum f s)
  simp_rw [iOptionDiracSum_apply _ hs]
  have hmatch (o : Option X) :
      (match o with
        | some x => s.indicator (1 : X → ENNReal) x
        | none => 0) = o.elim 0 (fun x => s.indicator 1 x) := by
    cases o <;> rfl
  simp_rw [hmatch]
  change Measurable (fun f : ι → Option X =>
    ∑' i, (f i).elim 0 (fun x => s.indicator 1 x))
  exact Measurable.tsum fun i =>
    (measurable_option_elim 0 (measurable_one.indicator hs)).comp
      (measurable_pi_apply i)

theorem iDiracSum_apply_of_countable [Countable ι] [MeasurableSingletonClass X]
    (f : ι → X) (s : Set X) :
    iDiracSum f s = ∑' i, s.indicator (1 : X → ℝ≥0∞) (f i) := by
  simp only [iDiracSum, sum_apply_of_countable]
  exact tsum_congr fun i => dirac_apply _ _

/-- Restricting the counting measure to a set is the Dirac sum over that set,
so its value on a measurable `t` is the cardinality of `t ∩ s`. -/
theorem count_restrict_apply (s : Set X) {t : Set X} (ht : MeasurableSet t)
    (hst : MeasurableSet (t ∩ s)) :
    (count.restrict s) t = (t ∩ s).encard := by
  rw [restrict_apply ht, count_apply hst]

end Measure

end MeasureTheory
