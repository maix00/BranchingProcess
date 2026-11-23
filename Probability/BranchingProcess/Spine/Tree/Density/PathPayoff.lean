/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Tree.Density.AdaptedPayoff
public import Probability.BranchingProcess.Spine.Tree.PathLaw
public import Probability.BranchingProcess.State.Observation.Ancestral

/-!
# Ancestral-path many-to-one from adapted node compensation

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `lintegral_pathPayoff_eq` proves
  `E[∑_(|u|=n) W_u g(X_(u|0),…,X_u)] = E_spine[g(X_(ξ_0),…,X_(ξ_n))]`
  for every nonnegative measurable path payoff and the existing state-dependent
  offspring kernel. Missing states are read with an explicit eligible default;
  the spinal states are the actual unique realized ray.

This generalizes the path form in Zhan Shi, *Branching Random Walks* (2015),
Theorems 1.1 and 4.4(ii), DOI 10.1007/978-3-319-25372-5. It follows from the stronger
adapted-node theorem by concentrating payoffs on generation `n`, then using
uniqueness of the realized spine. There is no second induction on reproduction.
State spaces are arbitrary measurable spaces and child slots are countable
with measurable singletons. Mean harmonicity is needed only where the weight
is positive and finite; no other moment or integrability hypothesis is used.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open Classical MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

/-- The actual ancestral-path formula is a fixed-generation specialization
of the adapted-node compensation identity. -/
theorem lintegral_pathPayoff_eq {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (d s : {s // h s ≠ 0 ∧ h s ≠ ∞}) (n : ℕ)
    {g : (Fin (n + 1) → S) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ t, ∑' u : List ι, if u.length = n then
      addressWeight h u.length u.get (State.treeHistory u.length t) *
        g (State.ancestralHistory d.1 n u t) else 0
      ∂State.treeKernel Q (some s.1)) =
    ∫⁻ t, g (fun k => (statePath d t k).1)
      ∂treeKernel Q hh harmonic (some (Sum.inr s)) := by
  let F (u : List ι) (t : List ι → Option S) :=
    if u.length = n then g (State.ancestralHistory d.1 n u t) else 0
  have hF (u : List ι) : Measurable[State.treeFiltration u.length] (F u) :=
    (hg.comp (State.measurable_ancestralHistory d.1 n u)).ite
      (MeasurableSet.const _) measurable_const
  have hi := lintegral_adaptedPayoff_eq Q hh harmonic s F hF
  refine (lintegral_congr fun t => ?_).trans (hi.trans ?_)
  · apply tsum_congr
    intro u
    by_cases hu : u.length = n <;> simp [F, hu]
  · apply lintegral_congr_ae
    filter_upwards [ae_treeKernel_statePath Q hh harmonic d s] with t ht
    obtain ⟨f, ⟨hf, hc, hstates⟩, _⟩ := ht
    rw [tsum_eq_single (lineagePrefix f n)]
    · have htag : (t (lineagePrefix f n)).any Sum.isRight = true := hf n
      rw [ite_eq_left htag]
      dsimp only [F]
      rw [ite_eq_left (length_lineagePrefix f n)]
      congr 1
      funext k
      have hp := lineagePrefix_prefix f (Nat.le_of_lt_succ k.isLt)
      have he : (lineagePrefix f n).take k = lineagePrefix f k := by
        obtain ⟨tail, ht⟩ := hp
        rw [← ht]
        simp
      simp only [State.ancestralHistory, he, hstates, Option.map_some,
        Sum.elim_inr, Option.getD_some]
    · intro u hune
      by_cases htag : (t u).any Sum.isRight = true
      · rw [ite_eq_left htag]
        have hn : u.length ≠ n := by
          intro hn
          have hu : u ∈ distinguishedNodes t := htag
          rw [hc] at hu
          obtain ⟨k, hk⟩ := hu
          have hkn : k = n := by simpa [hn] using congrArg List.length hk
          exact hune (hkn ▸ hk.symm)
        exact ite_eq_right hn
      · exact ite_eq_right htag

end ProbabilityTheory.BranchingProcess.Spine
