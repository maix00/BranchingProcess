import MeasureTheory.Measure.Tight.Sequence

open MeasureTheory

private noncomputable def exceptionalSequence (n : ℕ) : Measure ℕ :=
  if n < 3 then Measure.dirac n else 0

#print axioms MeasureTheory.isTightMeasureSet_image_Iio_of_singletons
#print axioms MeasureTheory.isTightMeasureSet_range_of_eventually_uniform_compact_mass_bound

/-- The first three laws are point masses at different points; the tail is
zero. The generic criterion combines the individually tight prefix with its
uniform compact tail without requiring a path-space structure. -/
example : IsTightMeasureSet (Set.range exceptionalSequence) := by
  apply isTightMeasureSet_range_of_eventually_uniform_compact_mass_bound
    exceptionalSequence
  · intro n
    by_cases hn : n < 3
    · simpa [exceptionalSequence, hn] using
        (isTightMeasureSet_singleton (μ := Measure.dirac n))
    · have hzero : exceptionalSequence n = 0 := by
        simp [exceptionalSequence, hn]
      rw [hzero]
      exact isTightMeasureSet_singleton
  · intro ε hε
    refine ⟨3, ∅, isCompact_empty, ?_⟩
    intro n hn
    have hn' : ¬ n < 3 := by omega
    simp [exceptionalSequence, hn']
