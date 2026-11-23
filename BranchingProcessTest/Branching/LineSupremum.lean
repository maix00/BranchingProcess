import Probability.Process.Tree.Line.Supremum

open Combinatorics.UlamHarris
open ProbabilityTheory.Tree

namespace LineSupremumExamples

-- One root stops immediately; the other recedes to arbitrarily large depth.
-- Their supremum is partial, rather than a union or a line covering every ray.
def stages (n : ℕ) : Set (RootIndexed.TreeNode Bool Unit) :=
  {u | (u.1 = false ∧ u.2 = []) ∨ (u.1 = true ∧ u.2.length = n)}

example : RootIndexed.Line.supremum stages = {(false, [])} := by
  ext u
  rw [RootIndexed.Line.supremum, RootIndexed.Line.mem_firstEntrance_iff]
  constructor
  · rintro ⟨hu, hmin⟩
    have hdesc := Set.mem_iInter.mp hu (u.2.length + 1)
    obtain ⟨v, hv, hvu⟩ := hdesc
    rcases hv with hv | hv
    · have hf : u.1 = false := hvu.1 ▸ hv.1
      have hroot : (u.1, []) ∈ ⋂ n, RootIndexed.Line.descendantClosure (stages n) := by
        apply Set.mem_iInter.mpr
        intro n
        exact ⟨(u.1, []), Or.inl ⟨hf, rfl⟩, RootIndexed.IsAncestor.refl _⟩
      have hlen : u.2.length = 0 := by
        by_contra hn
        exact hmin 0 (Nat.pos_of_ne_zero hn) (by simpa using hroot)
      simp only [Set.mem_singleton_iff]
      exact Prod.ext hf (List.length_eq_zero_iff.mp hlen)
    · have hle := hvu.2.length_le
      omega
  · rintro rfl
    refine ⟨Set.mem_iInter.mpr (fun n => ?_), ?_⟩
    · exact ⟨(false, []), Or.inl ⟨rfl, rfl⟩, RootIndexed.IsAncestor.refl _⟩
    · simp

-- No node-countability or branching-process hypothesis enters optional closure.
example {Ω I Root α : Type*} [MeasurableSpace Ω] [Countable I]
    {past : Set (RootIndexed.TreeNode Root α) → MeasurableSpace Ω}
    {L : I → Ω → Set (RootIndexed.TreeNode Root α)}
    (h : ∀ i, IsOptionalLine past (L i)) :
    IsOptionalLine past (fun ω => RootIndexed.Line.supremum (fun i => L i ω)) :=
  IsOptionalLine.supremum h

end LineSupremumExamples

#print axioms Combinatorics.UlamHarris.RootIndexed.Line.descendantClosure_supremum
#print axioms ProbabilityTheory.Tree.IsRandomLine.supremum
#print axioms ProbabilityTheory.Tree.IsOptionalLine.supremum
#print axioms ProbabilityTheory.Tree.IsOptionalLine.measurableSpace_iSup_le_supremum
