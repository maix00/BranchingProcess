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

/-- Applying the same measurable map to every coordinate of a canonical
i.i.d. sequence gives the canonical i.i.d. law of the pushed-forward
one-coordinate law. -/
theorem iidSequenceLaw_map_coordinatewise
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (f : X → Y) (hf : Measurable f) :
    (iidSequenceLaw ν).map (fun sequence n => f (sequence n)) =
      iidSequenceLaw (ν.map f) := by
  have hindep : iIndepFun
      (fun i (sequence : ℕ → X) => f (sequence i))
      (iidSequenceLaw ν) :=
    (iidSequenceLaw_independent ν).comp (fun _ => f) (fun _ => hf)
  calc
    (iidSequenceLaw ν).map (fun sequence n => f (sequence n)) =
        Measure.infinitePi (fun i =>
          (iidSequenceLaw ν).map (fun sequence => f (sequence i))) := by
      simpa [Function.comp_def] using
        hindep.map_fun_eq_infinitePi_map
          (fun i => hf.comp (measurable_pi_apply i))
    _ = Measure.infinitePi (fun _ : ℕ => ν.map f) := by
      congr 1
      funext i
      calc
        (iidSequenceLaw ν).map (fun sequence => f (sequence i)) =
            ((iidSequenceLaw ν).map fun sequence => sequence i).map f := by
          simpa [Function.comp_def] using
            (Measure.map_map hf (measurable_pi_apply i)).symm
        _ = ν.map f := by rw [iidSequenceLaw_map_apply]
    _ = iidSequenceLaw (ν.map f) := rfl

/-- Dropping any finite prefix from a canonical i.i.d. sequence leaves its
law unchanged. -/
theorem iidSequenceLaw_map_natAdd {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (offset : ℕ) :
    (iidSequenceLaw ν).map (fun sequence n => sequence (offset + n)) =
      iidSequenceLaw ν := by
  unfold iidSequenceLaw
  simpa using Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => ν) (f := fun n => offset + n)
    (fun _ _ hij => Nat.add_left_cancel hij)

/-- Union bound for the event that one of the first `n` coordinates of a
canonical IID sequence belongs to a measurable set. -/
theorem iidSequenceLaw_measure_exists_mem_le
    {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (s : Set X) (hs : MeasurableSet s) (n : ℕ) :
    iidSequenceLaw ν {sequence | ∃ k ∈ Finset.range n, sequence k ∈ s} ≤
      (n : ℕ) * ν s := by
  let event : ℕ → Set (ℕ → X) := fun k => {sequence | sequence k ∈ s}
  have hevent : {sequence : ℕ → X |
      ∃ k ∈ Finset.range n, sequence k ∈ s} =
      ⋃ k ∈ Finset.range n, event k := by
    ext sequence
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, event]
    aesop
  rw [hevent]
  calc
    iidSequenceLaw ν (⋃ k ∈ Finset.range n, event k) ≤
        ∑ k ∈ Finset.range n, iidSequenceLaw ν (event k) :=
      measure_biUnion_finset_le _ _
    _ = ∑ _k ∈ Finset.range n, ν s := by
      apply Finset.sum_congr rfl
      intro k hk
      change iidSequenceLaw ν
          ((fun sequence : ℕ → X => sequence k) ⁻¹' s) = ν s
      calc
        _ = (iidSequenceLaw ν).map (fun sequence => sequence k) s :=
          (Measure.map_apply (measurable_pi_apply k) hs).symm
        _ = ν s := by rw [iidSequenceLaw_map_apply ν k]
    _ = (n : ℕ) * ν s := by simp

end ProbabilityTheory
