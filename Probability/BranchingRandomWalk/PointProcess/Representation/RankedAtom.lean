import Probability.BranchingRandomWalk.PointProcess.PointMeasure
import Combinatorics.BranchingStep.Prefix
import Combinatorics.BranchingStep.Slot.Basic
import Mathlib.Data.EReal.Basic

/-!
# The canonical ranked atom of a counting measure

Slot `n` carries the `n`th atom of the cumulative counting function
`R ↦ ν (-∞, R]`. Rational thresholds keep the construction countable and
therefore measurable in the Giry measurable space of measures, and
multiplicity is retained because ranks use `n + 1 ≤ ν (-∞, R]`.

This is the deterministic construction of the enumeration; it mentions no
sample space. The rank-location lemmas are in `RankedAtomLocation.lean`, the
order and nonemptiness of the resulting slot in `RankedOrder.lean`, and the
Dirac-sum reconstruction in `RankedReconstruction.lean`.
-/

open MeasureTheory
open Filter
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory

/-- A rational candidate upper bound for the atom of rank `n`. -/
noncomputable def rankedAtomCandidate (n : ℕ) (q : ℚ)
    (ν : Measure ℝ) : EReal :=
  if (n + 1 : ENNReal) ≤ ν (Set.Iic (q : ℝ)) then
    ((q : ℝ) : EReal)
  else ⊤

theorem rankedAtomCandidate_measurable (n : ℕ) (q : ℚ) :
    Measurable (rankedAtomCandidate n q) := by
  unfold rankedAtomCandidate
  have hcount : Measurable (fun ν : Measure ℝ => ν (Set.Iic (q : ℝ))) :=
    Measure.measurable_coe measurableSet_Iic
  have hset : MeasurableSet
      {ν : Measure ℝ | (n + 1 : ENNReal) ≤ ν (Set.Iic (q : ℝ))} :=
    measurableSet_le measurable_const hcount
  exact measurable_const.ite hset measurable_const

/-- Extended-real rank location. It is `⊤` when the measure has at most `n`
atoms in total. -/
noncomputable def rankedAtomEReal (n : ℕ) (ν : Measure ℝ) : EReal :=
  ⨅ q : ℚ, rankedAtomCandidate n q ν

theorem rankedAtomEReal_measurable (n : ℕ) :
    Measurable (rankedAtomEReal n) := by
  unfold rankedAtomEReal
  exact Measurable.iInf (rankedAtomCandidate_measurable n)

/-- Real-valued displacement used in the optional slot. Its value is
irrelevant when the corresponding presence flag is nonpositive. -/
noncomputable def rankedAtom (n : ℕ) (ν : Measure ℝ) : ℝ :=
  (rankedAtomEReal n ν).toReal

theorem rankedAtom_measurable (n : ℕ) :
    Measurable (rankedAtom n) :=
  (rankedAtomEReal_measurable n).ereal_toReal

/-- Whether the counting measure contains an atom of rank `n`. -/
def rankedAtomPresent (n : ℕ) (ν : Measure ℝ) : Prop :=
  (n + 1 : ENNReal) ≤ ν Set.univ

theorem measurableSet_rankedAtomPresent (n : ℕ) :
    MeasurableSet {ν : Measure ℝ | rankedAtomPresent n ν} := by
  exact measurableSet_le measurable_const
    (Measure.measurable_coe MeasurableSet.univ)

/-- Canonical optional-slot mark extracted from a measure. -/
noncomputable def measureToStep (ν : Measure ℝ) : NatRealStep :=
  by
    classical
    exact fun n => if rankedAtomPresent n ν then some (rankedAtom n ν) else none

theorem measureToStep_measurable :
    Measurable measureToStep := by
  rw [measurable_pi_iff]
  intro n
  exact ((measurable_option_some.comp (rankedAtom_measurable n)).ite
    (measurableSet_rankedAtomPresent n) measurable_const)

theorem measureToStep_childPresent (ν : Measure ℝ) (n : ℕ) :
    measureToStep ν ∈ childPresent n ↔ rankedAtomPresent n ν := by
  classical
  by_cases h : rankedAtomPresent n ν <;>
    simp [measureToStep, childPresent, present, h]

/-- A present slot of the canonical step carries exactly the ranked atom. -/
theorem measureToStep_eq_some (ν : Measure ℝ) {n : ℕ} {x : ℝ}
    (h : measureToStep ν n = some x) : x = rankedAtom n ν := by
  classical
  by_cases hp : rankedAtomPresent n ν
  · simp [measureToStep, hp] at h
    exact h.symm
  · simp [measureToStep, hp] at h

theorem rankedAtomPresent_mono {ν : Measure ℝ} {i j : ℕ}
    (hij : i ≤ j) (hj : rankedAtomPresent j ν) :
    rankedAtomPresent i ν := by
  unfold rankedAtomPresent at *
  have hcast : (i + 1 : ENNReal) ≤ (j + 1 : ENNReal) := by
    exact_mod_cast Nat.succ_le_succ hij
  exact hcast.trans hj

theorem measureToStep_presencePrefix (ν : Measure ℝ) :
    presencePrefix (measureToStep ν) := by
  intro i j hij hnone
  by_contra hj
  have hpres_j : present (measureToStep ν) j :=
    (present_iff_ne_none _ j).2 hj
  have hrank_j : rankedAtomPresent j ν :=
    (measureToStep_childPresent ν j).1 hpres_j
  have hrank_i : rankedAtomPresent i ν :=
    rankedAtomPresent_mono (le_of_lt hij) hrank_j
  have hpres_i : present (measureToStep ν) i :=
    (measureToStep_childPresent ν i).2 hrank_i
  exact (present_iff_ne_none _ i).1 hpres_i hnone

end ProbabilityTheory.BranchingRandomWalk
