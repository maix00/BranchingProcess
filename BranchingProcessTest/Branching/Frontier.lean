import Combinatorics.BranchingWalk.Selection.NSelection.Walk.Frontier
import Mathlib.Data.EReal.Inv

open Combinatorics.Branching

-- An infimum frontier exists even when no particle attains it.
private noncomputable def openRay : CloudSet Unit EReal where
  points _ := Set.Ioi 0

example : openRay.lowerFrontier () = 0 := by
  change sInf (Set.Ioi (0 : EReal)) = 0
  apply le_antisymm
  · by_contra h
    obtain ⟨y, hy0, hy⟩ := exists_between (lt_of_not_ge h)
    exact (not_le_of_gt hy) (sInf_le hy0)
  · exact le_sInf (fun _ h ↦ h.le)

example : openRay.lowerFrontierPoints () = ∅ := by
  ext x
  constructor
  · intro hx
    change IsLeast (Set.Ioi (0 : EReal)) x at hx
    obtain ⟨y, hy0, hyx⟩ := exists_between (show (0 : EReal) < x from hx.1)
    exact (not_le_of_gt hyx) (hx.2 hy0)
  · simp

-- Empty populations have the manuscript's top/bottom convention.
example : (⟨fun _ ↦ ∅⟩ : CloudSet Unit EReal).lowerFrontier () = ⊤ := by
  simp [CloudSet.lowerFrontier]

example : (⟨fun _ ↦ ∅⟩ : CloudSet Unit EReal).upperFrontier () = ⊥ := by
  simp [CloudSet.upperFrontier]

#print axioms Combinatorics.Branching.CloudSet.lowerFrontier_mapOrderDual
#print axioms Combinatorics.Branching.Cloud.lowerFrontierBy_state_eq
#print axioms Combinatorics.Branching.Selection.NSelection.Walk.lowerFrontier_eq_lowerPoint
