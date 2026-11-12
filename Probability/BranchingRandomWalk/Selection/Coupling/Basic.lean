/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Selection.Process
public import Combinatorics.BranchingWalk.Cloud.Order.Selection

/-!
# Causal selected-population coupling

This file applies the deterministic cloud comparison pathwise to a causal
random selection rule.  Randomness may come entirely from the common
pre-sampled marked forest. The rule is measurable in the generation domain by
`CausalFiniteMechanism.measurable_population`; the comparison itself holds for
every sample point.

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.Selection.CausalFiniteMechanism.injectivelyDominatesBy_leftmostBy_of_card_le`:
  if $R_t(\omega)\subseteq C_t(\omega)$ has at most $N$ particles and
  $C(\omega)$ injectively dominates $D(\omega)$, then the selected cloud
  injectively dominates the $N$ leftmost particles of $D(\omega)$ at every
  time.
- `ProbabilityTheory.BranchingRandomWalk.Selection.CausalFiniteMechanism.dominatesBy_leftmost_of_card_le`:
  under the same subset and size bounds, rankwise domination transfers to
  the selected population and the first-$N$ particles of the comparison cloud when both
  clouds' values are monotone in address order.
-/

open MeasureTheory Combinatorics.UlamHarris
open MeasureTheory.Selection

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection

open Combinatorics.Branching

variable {Time Ω Root α Position OrderKey : Type*}
    [MeasurableSpace (RootIndexed.TreeNode Root α)]

namespace CausalFiniteMechanism

/-- Address-order-free pathwise coupling for a causally selected population.
The comparison cloud is re-sorted by its observed value at every slice.
Particle addresses serve as labels and deterministic tie breakers, while the
spatial order is determined by the observed value. -/
theorem injectivelyDominatesBy_leftmostBy_of_card_le
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    {ℱ : Time → MeasurableSpace Ω}
    (R : CausalFiniteMechanism Time Ω
      (RootIndexed.TreeNode Root α) ℱ)
    (φ : Position → OrderKey) (N : ℕ)
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
        Combinatorics.Selection.NSelection.selectFirstNBy N
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

/-- Pathwise cloud domination for a causally selected population before its size
exceeds `N`. The selected population may depend on the available information;
only subset selection and the stated pathwise size bound are used in the order
argument. -/
theorem dominatesBy_leftmost_of_card_le
    [LinearOrder (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [MeasurableSpace OrderKey] [MeasurableSingletonClass OrderKey] [Preorder OrderKey]
    {ℱ : Time → MeasurableSpace Ω}
    (R : CausalFiniteMechanism Time Ω
      (RootIndexed.TreeNode Root α) ℱ)
    (φ : Position → OrderKey) (N : ℕ)
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
      let right := fun t => Combinatorics.Selection.NSelection.selectFirstN
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

end
