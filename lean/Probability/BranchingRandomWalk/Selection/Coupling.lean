import Probability.BranchingRandomWalk.Selection.Process
import Combinatorics.BranchingWalk.Cloud.Order.Selection
import Probability.BranchingRandomWalk.Selection.Coupling.Generation

/-!
# Causal selected-population coupling

This file applies the deterministic cloud comparison pathwise to a causal
random selection rule.  Randomness may come entirely from the common
pre-sampled marked forest. The rule is measurable in the generation domain by
`CausalFiniteMechanism.measurable_population`; the comparison itself holds for
every sample point.
-/

open MeasureTheory Combinatorics.UlamHarris

namespace ProbabilityTheory.BranchingRandomWalk.Selection

open Combinatorics.Branching

variable {Time Ω Root α Position Value : Type*}
    [MeasurableSpace (RootIndexed.TreeNode Root α)]

namespace CausalFiniteMechanism

/-- Address-order-free pathwise coupling for a causal retained population.
The target is re-sorted by its observed value at every slice.  Thus particle
addresses are used only as labels and as deterministic tie breakers; no
compatibility between address order and spatial order is assumed. -/
theorem injectivelyDominatesBy_leftmostBy_of_card_le
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    {ℱ : Time → MeasurableSpace Ω}
    (R : CausalFiniteMechanism Time Ω
      (RootIndexed.TreeNode Root α) ℱ)
    (φ : Position → Value) (N : ℕ)
    (C D : Ω → Cloud Time Root α Position)
    (candidates : Time → Ω → Finset (RootIndexed.TreeNode Root α))
    (hCfinite : ∀ ω t, ((C ω).particles t).Finite)
    (hDfinite : ∀ ω t, ((D ω).particles t).Finite)
    (hcandidates : ∀ ω t, ↑(candidates t ω) ⊆ (C ω).particles t)
    (hcard : ∀ ω t, (R.population candidates t ω).card ≤ N)
    (hdom : ∀ ω t, (C ω).InjectivelyDominatesBy φ (D ω) t) :
    ∀ ω t,
      ((C ω).withFinsetParticles
        (fun _ => R.population candidates t ω)).InjectivelyDominatesBy φ
      ((D ω).withFinsetParticles (fun _ =>
        Combinatorics.Branching.Selection.NSelection.selectFirstNBy N
          (fun q => φ ((D ω).position q.1 q.2))
          (hDfinite ω t).toFinset)) t := by
  intro ω t
  apply Cloud.injectivelyDominatesBy_selectFirstNBy_of_subset
    φ N (C ω) (D ω) t (hCfinite ω t) (hDfinite ω t)
    (R.population candidates t ω)
  · intro p hp
    exact hcandidates ω t (R.population_subset candidates t ω hp)
  · exact hcard ω t
  · exact hdom ω t

/-- Pathwise cloud domination for a causal killed population before its size
exceeds `N`. The retained population may depend on the available information;
only subset selection and the stated pathwise size bound are used in the order
argument. -/
theorem dominatesBy_leftmost_of_card_le
    [LinearOrder (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [MeasurableSpace Value] [MeasurableSingletonClass Value] [Preorder Value]
    {ℱ : Time → MeasurableSpace Ω}
    (R : CausalFiniteMechanism Time Ω
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
      let right := fun t => Combinatorics.Branching.Selection.NSelection.selectFirstN
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

end CausalFiniteMechanism

end ProbabilityTheory.BranchingRandomWalk.Selection
