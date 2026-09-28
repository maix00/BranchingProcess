import Mathlib.Probability.Independence.InfinitePi

/-!
# Canonical laws of i.i.d. sequences

The countable product of a probability measure is the canonical law of an
i.i.d. sequence.  This construction is independent of random walks and
branching.
-/

open MeasureTheory

namespace ProbabilityTheory

/-- Canonical sequence law with identical independent coordinates of law
`ν`. -/
noncomputable def iidSequenceLaw {X : Type*} [MeasurableSpace X]
    (ν : Measure X) : Measure (ℕ → X) :=
  Measure.infinitePi fun _ : ℕ => ν

noncomputable instance iidSequenceLaw.instIsProbabilityMeasure
    {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (iidSequenceLaw ν) := by
  unfold iidSequenceLaw
  infer_instance

theorem iidSequenceLaw_map_apply {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (n : ℕ) :
    (iidSequenceLaw ν).map (fun sequence => sequence n) = ν := by
  unfold iidSequenceLaw
  exact Measure.infinitePi_map_eval (fun _ : ℕ => ν) n

theorem iidSequenceLaw_independent {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] :
    iIndepFun (fun n (sequence : ℕ → X) => sequence n)
      (iidSequenceLaw ν) := by
  unfold iidSequenceLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : ℕ => ν) (X := fun _ : ℕ => id)
    (fun _ => measurable_id))

end ProbabilityTheory
