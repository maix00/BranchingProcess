import Probability.BranchingRandomWalk.Selection.NSelection.Law.Restarted

open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

private def descendingOffspring : Step ℕ ℝ := fun i => some (-(i : ℝ))

private theorem descendingOffspring_not_lowerFinite :
    ¬ IsLowerFiniteBy (fun i => value' descendingOffspring i)
      (support descendingOffspring) := by
  intro hlower
  have hzero : 0 ∈ support descendingOffspring := by
    simp [support, survive, descendingOffspring]
  have hfinite := hlower 0 hzero
  have hsubset : Set.Ioi (0 : ℕ) ⊆
      {q | q ∈ support descendingOffspring ∧
        valueKey (fun i => value' descendingOffspring i) q ≤
          valueKey (fun i => value' descendingOffspring i) 0} := by
    intro q hq
    have hsupport : q ∈ support descendingOffspring := by
      simp [support, survive, descendingOffspring]
    have hqR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
    have hvalue : value' descendingOffspring q < value' descendingOffspring 0 := by
      simpa [descendingOffspring, value'] using
        (neg_lt_zero.mpr hqR)
    exact ⟨hsupport, (valueKey_lt_of_value_lt _ hvalue).le⟩
  have hfiniteIoi : (Set.Ioi 0).Finite := hfinite.subset hsubset
  exact (Set.Ioi_infinite (0 : ℕ)) hfiniteIoi

example :
    selectFirstNFromSetTotalized 1
      (fun (_ : PUnit) i => value' descendingOffspring i)
      (fun _ => support descendingOffspring) PUnit.unit = ∅ := by
  apply selectFirstNFromSetTotalized_empty_of_not_lowerFinite
  exact descendingOffspring_not_lowerFinite

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Coupling.RootIndexed.rankInstalledField_law
#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.rankInstalledField_totalizedSelectedPopulation_measurable_law
#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.rankInstalledField_causalPopulation_measurable_law
#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.causalPopulationCoupling
#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.restartedRealPositionCoupling
#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.restartedRealPositionCoupledInjection_ae
#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.restartedRealPositionCoupledInjectionOnRoots_ae
