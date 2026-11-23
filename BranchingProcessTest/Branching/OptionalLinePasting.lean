import Probability.Process.Tree.Line.Information.Pasting

open MeasureTheory ProbabilityTheory.Tree Combinatorics.UlamHarris

-- An event observable at the later line becomes observable at the pasted
-- line on the cell where that later line is used.
example {Ω Root α : Type*} [MeasurableSpace Ω]
    {past : Set (RootIndexed.TreeNode Root α) → MeasurableSpace Ω}
    {L M : Ω → Set (RootIndexed.TreeNode Root α)}
    (hL : IsOptionalLine past L) (hM : IsOptionalLine past M)
    (hLM : ∀ ω, RootIndexed.Line.Precedes (L ω) (M ω))
    {A B : Set Ω} (hA : MeasurableSet[hL.measurableSpace] A)
    (hB : MeasurableSet[hM.measurableSpace] B) (hBA : B ⊆ Aᶜ) :
    MeasurableSet[(hL.ite_of_precedes hM hLM hA).measurableSpace] B := by
  apply (hL.measurableSet_ite_of_precedes hM hLM hA B).mpr
  have he : B ∩ A = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxB, hxA⟩
    exact hBA hxB hxA
  have hc : B ∩ Aᶜ = B := Set.inter_eq_left.mpr hBA
  rw [he, hc]
  exact ⟨@MeasurableSet.empty Ω hL.measurableSpace, hB⟩

#print axioms ProbabilityTheory.Tree.IsOptionalLine.measurableSet_ite_of_precedes
