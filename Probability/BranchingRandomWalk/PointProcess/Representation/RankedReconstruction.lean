import Probability.BranchingRandomWalk.PointProcess.Representation.RankedOrder
import Probability.BranchingRandomWalk.PointProcess.PointMeasure

/-!
# Dirac-sum reconstruction from the canonical ranked slots

The cumulative mass of the reconstructed Dirac sum is the number of present
slots, so the reconstruction returns the original integer-valued, locally
finite counting measure.
-/

open MeasureTheory
open Filter
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingWalk MeasureTheory

noncomputable def rankedIicCountTerm (ν : Measure ℝ) (R : ℝ)
    (n : ℕ) : ENNReal := by
  classical
  exact if rankedAtomPresent n ν ∧ rankedAtom n ν ≤ R then 1 else 0

theorem stepPointMeasure_measureToStep_Iic
    (ν : Measure ℝ) (R : ℝ) :
    stepPointMeasure (measureToStep ν) (Set.Iic R) =
      ∑' n : ℕ, rankedIicCountTerm ν R n := by
  rw [stepPointMeasure_apply_children _ _ measurableSet_Iic]
  congr 1
  funext n
  classical
  by_cases hp : rankedAtomPresent n ν <;>
    by_cases hr : rankedAtom n ν ≤ R <;>
      simp [childRealized, childPresent, present, value',
        measureToStep,
        rankedIicCountTerm, hp, hr]

theorem stepPointMeasure_measureToStep_Iic_eq
    (ν : Measure ℝ) (hcount : IsCountingMeasure ν)
    (hlocal : IsLeftLocallyFinite ν) (R : ℝ) :
    stepPointMeasure (measureToStep ν) (Set.Iic R) =
      ν (Set.Iic R) := by
  obtain ⟨k, hk⟩ := counting_value_nat hcount hlocal R
  rw [stepPointMeasure_measureToStep_Iic, hk]
  have hterm : ∀ n : ℕ, rankedIicCountTerm ν R n =
      if n < k then (1 : ENNReal) else 0 := by
    intro n
    have hiff :
        (rankedAtomPresent n ν ∧ rankedAtom n ν ≤ R) ↔ n < k := by
      rw [rankedAtom_present_and_le_iff hcount hlocal, hk]
      exact_mod_cast Nat.succ_le_iff
    classical
    simp only [rankedIicCountTerm, hiff]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.range k)]
  · simp [Finset.filter_eq_self.2
      (fun n hn => Finset.mem_range.mp hn)]
  · intro n hn
    simp at hn
    simp [hn]

/-- The canonical ranked Dirac sum reconstructs every integer-valued,
left-locally finite measure on `ℝ`. -/
theorem stepPointMeasure_measureToStep_eq
    (ν : Measure ℝ) (hcount : IsCountingMeasure ν)
    (hlocal : IsLeftLocallyFinite ν) :
    stepPointMeasure (measureToStep ν) = ν := by
  apply Measure.ext_of_Ioc'
  · intro a b hab
    apply ne_top_of_le_ne_top (hlocal.apply b)
    calc
      stepPointMeasure (measureToStep ν) (Set.Ioc a b) ≤
          stepPointMeasure (measureToStep ν) (Set.Iic b) :=
        measure_mono Set.Ioc_subset_Iic_self
      _ = ν (Set.Iic b) :=
        stepPointMeasure_measureToStep_Iic_eq
          ν hcount hlocal b
  · intro a b hab
    rw [← Set.Iic_sdiff_Iic]
    have hfinRecA :
        stepPointMeasure (measureToStep ν) (Set.Iic a) ≠ ∞ := by
      rw [stepPointMeasure_measureToStep_Iic_eq
        ν hcount hlocal a]
      exact hlocal.apply a
    rw [measure_sdiff (Set.Iic_subset_Iic.mpr hab.le)
      measurableSet_Iic.nullMeasurableSet hfinRecA]
    rw [measure_sdiff (Set.Iic_subset_Iic.mpr hab.le)
      measurableSet_Iic.nullMeasurableSet (hlocal.apply a)]
    rw [stepPointMeasure_measureToStep_Iic_eq
      ν hcount hlocal a]
    rw [stepPointMeasure_measureToStep_Iic_eq
      ν hcount hlocal b]

end ProbabilityTheory.BranchingRandomWalk
