/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.LocalBias.ManyToOne
public import Probability.BranchingProcess.Spine.Tree.Observation.Path
public import Probability.BranchingProcess.State.Observation.Ancestral

/-!
# Ancestral-path many-to-one for a general local offspring bias

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine.LocalBias`:

* `ae_treeKernel_statePath` identifies the observed distinguished states
  with the unique realized infinite ray.
* `lintegral_pathPayoff_eq` states
  `E_Q[∑_(|u|=n) R_u g(X_(u|0),…,X_u)] = E_bias[g(X_(w_0),…,X_(w_n))]`.
  It requires only an admissible local bias, an eligible initial state and
  nonnegative measurable `g`; no harmonic function or offspring mean is needed.

This is the local-density version of Zhan Shi, *Branching Random Walks*
(2015), Theorems 1.1 and 4.4(ii), DOI 10.1007/978-3-319-25372-5.
It specializes the general adapted-payoff theorem and uses the actual ray.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingProcess.Spine.LocalBias
open Classical MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
variable {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι]
  [Countable ι] [MeasurableSingletonClass ι]

/-- The observed states are exactly those on the actual unique realized ray. -/
theorem ae_treeKernel_statePath (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    (B : LocalBias S ι) (hB : B.IsAdmissible Q)
    (d s : B.domain) :
    ∀ᵐ t ∂treeKernel Q B hB (some (Sum.inr s)),
      ∃! f, IsRay (distinguishedNodes t) f ∧
        distinguishedNodes t = Set.range (lineagePrefix f) ∧
        ∀ n, t (lineagePrefix f n) = some (Sum.inr (statePath d t n)) := by
  filter_upwards [ae_treeKernel_unique_spine Q B hB s] with t ht
  obtain ⟨f, ⟨hf, hc⟩, hu⟩ := ht
  exact ⟨f, ⟨hf, hc, statePath_eq_of_isRay d t f hf hc⟩,
    fun g hg => hu g ⟨hg.1, hg.2.1⟩⟩

/-- The actual ancestral-path formula is a fixed-generation specialization
of the adapted-node compensation identity. -/
theorem lintegral_pathPayoff_eq {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    (B : LocalBias S ι) (hB : B.IsAdmissible Q)
    (d s : B.domain) (n : ℕ)
    {g : (Fin (n + 1) → S) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ t, ∑' u : List ι, if u.length = n then
      addressWeight B u.length u.get (State.treeHistory u.length t) *
        g (State.ancestralHistory d.1 n u t) else 0
      ∂State.treeKernel Q (some s.1)) =
    ∫⁻ t, g (fun k => (statePath d t k).1)
      ∂treeKernel Q B hB (some (Sum.inr s)) := by
  let F (u : List ι) (t : List ι → Option S) :=
    if u.length = n then g (State.ancestralHistory d.1 n u t) else 0
  have hF (u : List ι) : Measurable[State.treeFiltration u.length] (F u) :=
    (hg.comp (State.measurable_ancestralHistory d.1 n u)).ite
      (MeasurableSet.const _) measurable_const
  have hi := lintegral_adaptedPayoff_eq Q B hB s F hF
  refine (lintegral_congr fun t => ?_).trans (hi.trans ?_)
  · apply tsum_congr
    intro u
    by_cases hu : u.length = n <;> simp [F, hu]
  · apply lintegral_congr_ae
    filter_upwards [ae_treeKernel_statePath Q B hB d s] with t ht
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

end ProbabilityTheory.BranchingProcess.Spine.LocalBias

end
