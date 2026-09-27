import Probability.BranchingRandomWalk.Selection.Process
import Combinatorics.BranchingWalk.Cloud.Order.Selection

/-!
# Causal selected-population coupling

This file applies the deterministic cloud comparison pathwise to a causal
random selection rule.  Randomness may come entirely from the common
pre-sampled marked forest. The rule is measurable in the generation domain by
`CausalSelectMechanism.measurable_population`; the comparison itself holds for
every sample point.
-/

open MeasureTheory Combinatorics.UlamHarris

namespace ProbabilityTheory.BranchingRandomWalk.Selection

open Combinatorics.Branching

variable {Time Ω Root α Position Value : Type*}
    [MeasurableSpace (RootIndexed.TreeNode Root α)]

namespace CausalSelectMechanism

/-- Pathwise cloud domination for a causal killed population before its size
exceeds `N`. The retained population may depend on the available information;
only subset selection and the stated pathwise size bound are used in the order
argument. -/
theorem dominatesBy_leftmost_of_card_le
    [LinearOrder (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [MeasurableSpace Value] [MeasurableSingletonClass Value] [Preorder Value]
    {ℱ : Time → MeasurableSpace Ω}
    (R : CausalSelectMechanism Time Ω
      (RootIndexed.TreeNode Root α) ℱ)
    (φ : Position → Value) (N : ℕ)
    (C D : Ω → Cloud Time Root α Position)
    (candidates : Time → Ω → Finset (RootIndexed.TreeNode Root α))
    (hCfinite : ∀ ω t, ((C ω).particles t).Finite)
    (hDfinite : ∀ ω t, ((D ω).particles t).Finite)
    (hcandidates : ∀ ω t, ↑(candidates t ω) ⊆ (C ω).particles t)
    (hcard : ∀ ω t, (R.population candidates t ω).card ≤ N)
    (hCmono : ∀ ω t p, p ∈ (C ω).particles t →
      ∀ q, q ∈ (C ω).particles t → p < q →
        φ ((C ω).position p.1 p.2) ≤ φ ((C ω).position q.1 q.2))
    (hDmono : ∀ ω t p, p ∈ (D ω).particles t →
      ∀ q, q ∈ (D ω).particles t → p < q →
        φ ((D ω).position p.1 p.2) ≤ φ ((D ω).position q.1 q.2))
    (hdom : ∀ ω t, (C ω).RankwiseDominatesBy φ (D ω) t) :
    ∀ ω,
      let right := fun t => Combinatorics.Branching.Selection.NSelection.keepFirst
        N (hDfinite ω t).toFinset
      ((C ω).withFinsetParticles (fun t => R.population candidates t ω)).DominatesBy φ
        ((D ω).withFinsetParticles right) := by
  intro ω
  apply Cloud.dominatesBy_leftmost_of_subset φ N (C ω) (D ω)
    (fun t => R.population candidates t ω)
    (hCfinite ω) (hDfinite ω)
  · intro t p hp
    exact hcandidates ω t (R.population_subset candidates t ω hp)
  · exact hcard ω
  · exact hCmono ω
  · exact hDmono ω
  · exact hdom ω

end CausalSelectMechanism

end ProbabilityTheory.BranchingRandomWalk.Selection
