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
It specializes the general observed-generation payoff theorem and uses the actual ray.
Reproduction-family payoffs retain the stronger interface in `ManyToOne.lean`.
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
  have hι : Nonempty ι := by
    by_contra h
    have : IsEmpty ι := not_nonempty_iff.mp h
    have hn := hB.normalized s.1 s.2
    simp at hn
  let defaultChild : ι := Classical.choice hι
  let G (u : List ι) (t : List ι → Option S) :=
    g (State.ancestralHistory d.1 n u t)
  have hG (u : List ι) (_ : u.length = n) :
      Measurable[State.treeFiltration u.length] (G u) :=
    hg.comp (State.measurable_ancestralHistory d.1 n u)
  have hi := lintegral_generationPayoff_eq Q B hB s defaultChild n G hG
  refine hi.trans ?_
  apply lintegral_congr_ae
  filter_upwards [ae_treeKernel_statePath Q B hB d s] with t ht
  obtain ⟨f, ⟨hf, hc, hstates⟩, _⟩ := ht
  dsimp only [G]
  rw [spinePrefix_eq_of_isRay defaultChild t f hf hc n]
  congr 1
  funext k
  have hp := lineagePrefix_prefix f (Nat.le_of_lt_succ k.isLt)
  have he : (lineagePrefix f n).take k = lineagePrefix f k := by
    obtain ⟨tail, ht⟩ := hp
    rw [← ht]
    simp
  simp only [State.ancestralHistory, he, hstates, Option.map_some,
    Sum.elim_inr, Option.getD_some]

end ProbabilityTheory.BranchingProcess.Spine.LocalBias

end
