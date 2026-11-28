/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.LocalBias.Density
public import Probability.BranchingProcess.State.Observation.History
public import Probability.BranchingProcess.Spine.LocalBias.Ray
public import Probability.BranchingProcess.Spine.Tree.Observation.Path
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Many-to-one compensation under arbitrary local offspring bias

## Public declarations

* `ProbabilityTheory.BranchingProcess.Spine.LocalBias.lintegral_adaptedPayoff_eq`
  proves `E_Q[∑_u R_u F_u(T)] = E_bias[∑_(u in spine) F_u(erase(T))]`
  for all nonnegative generation-measurable node payoffs. No harmonic
  function, finite depth, line, integrability or finite offspring mean is
  assumed. `LocalBias.IsAdmissible` supplies exactly normalization and
  existing eligible-child support for the local family-dependent density.

* `ProbabilityTheory.BranchingProcess.Spine.LocalBias.lintegral_generationPayoff_eq`
  specializes to `E_Q[∑_(|u|=n) R_u G(u,T)] = E_bias[G(w_n,erase(T))]`.
  The payoff can read the entire history through generation `n`, including
  the ancestral reproduction families, without discarding family marks.

This generalizes the finite-history summation in J. D. Biggins and
A. E. Kyprianou, *Measure change in multitype branching* (2004), proof of
Lemma 14.1, pp. 577–578, DOI 10.1239/aap/1086957585. The native kernel
construction and the single fixed-address density induction are reused.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingProcess.Spine.LocalBias
open Classical MeasureTheory Combinatorics.Branching
open scoped ENNReal
variable {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι]
  [Countable ι] [MeasurableSingletonClass ι]
set_option backward.isDefEq.respectTransparency false

/-- The many-to-one compensation identity for all nonnegative adapted node
payoffs, without requiring the active nodes to form a line. -/
theorem lintegral_adaptedPayoff_eq
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    (B : LocalBias S ι) (hB : B.IsAdmissible Q)
    (s : B.domain)
    (F : List ι → (List ι → Option S) → ℝ≥0∞)
    (hF : ∀ u, Measurable[State.treeFiltration u.length] (F u)) :
    (∫⁻ t, ∑' u : List ι,
      addressWeight B u.length u.get (State.treeHistory u.length t) * F u t
      ∂State.treeKernel Q (some s.1)) =
    ∫⁻ t, ∑' u : List ι, if (t u).any Sum.isRight = true then
      F u (fun v => (t v).map (Sum.elim id Subtype.val)) else 0
      ∂treeKernel Q B hB (some (Sum.inr s)) := by
  choose g hg hge using fun u => (hF u).exists_eq_measurable_comp
  have he : Measurable (fun t : List ι → Option (S ⊕ B.domain) =>
      fun v => (t v).map (Sum.elim id Subtype.val)) := by
    have hm := measurable_option_map (measurable_id.sumElim
      (measurable_subtype_coe : Measurable (Subtype.val : B.domain → S)))
    fun_prop
  have hleft (u : List ι) : Measurable (fun t : List ι → Option S =>
      addressWeight B u.length u.get (State.treeHistory u.length t) * F u t) :=
    ((measurable_addressWeight B hB.measurableSet_domain hB.measurable_density _ _).comp (State.measurable_treeHistory _)).mul
      ((hF u).mono (State.treeFiltration.le _) le_rfl)
  have hright (u : List ι) : Measurable (fun t :
      List ι → Option (S ⊕ B.domain) =>
      if (t u).any Sum.isRight = true then
        F u (fun v => (t v).map (Sum.elim id Subtype.val)) else 0) := by
    have htag : Measurable (fun t :
        List ι → Option (S ⊕ B.domain) => (t u).any Sum.isRight) :=
      (show Measurable (fun o : Option (S ⊕ B.domain) =>
        o.any Sum.isRight) from
        measurable_option_elim false (measurable_const.sumElim measurable_const)).comp
          (measurable_pi_apply u)
    exact (((hF u).mono (State.treeFiltration.le _) le_rfl).comp he).ite
      ((measurableSet_singleton true).preimage htag) measurable_const
  rw [lintegral_tsum (fun u => (hleft u).aemeasurable),
    lintegral_tsum (fun u => (hright u).aemeasurable)]
  apply tsum_congr
  intro u
  have hi := lintegral_treeKernel_fixedAddress Q B hB s u.length u.get (hg u)
  simp only [List.ofFn_get] at hi
  have hread (t : List ι → Option S) : F u t = g u (State.treeHistory u.length t) :=
    congrFun (hge u) t
  calc
    _ = ∫⁻ t, addressWeight B u.length u.get (State.treeHistory u.length t) *
        g u (State.treeHistory u.length t) ∂State.treeKernel Q (some s.1) :=
      lintegral_congr fun t => congrArg _ (hread t)
    _ = _ := hi.symm.trans (lintegral_congr fun t => by
      change (if (t u).any Sum.isRight = true then g u (fun k q => (t (List.ofFn q.2)).map (Sum.elim id Subtype.val)) else 0) = _
      have hr := hread (fun v => (t v).map (Sum.elim id Subtype.val))
      change F u (fun v => (t v).map (Sum.elim id Subtype.val)) =
        g u (fun k q => (t (List.ofFn q.2)).map (Sum.elim id Subtype.val)) at hr
      rw [hr])

/-- Fixed-generation compensation for any payoff of the observed tree and
selected address. In particular the payoff can read every reproduction family
on the ancestral path, so it need not factor through the ancestral states.
This specializes the adapted-payoff formula of Biggins and Kyprianou,
*Measure change in multitype branching* (2004), proof of Lemma 14.1,
DOI 10.1239/aap/1086957585, using the unique realized spine. -/
theorem lintegral_generationPayoff_eq
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    (B : LocalBias S ι) (hB : B.IsAdmissible Q)
    (s : B.domain) (defaultChild : ι) (n : ℕ)
    (G : List ι → (List ι → Option S) → ℝ≥0∞)
    (hG : ∀ u, u.length = n → Measurable[State.treeFiltration u.length] (G u)) :
    (∫⁻ t, ∑' u : List ι, if u.length = n then
      addressWeight B u.length u.get (State.treeHistory u.length t) * G u t else 0
      ∂State.treeKernel Q (some s.1)) =
    ∫⁻ t, G (List.ofFn (spinePrefix defaultChild t n))
      (fun v => (t v).map (Sum.elim id Subtype.val))
      ∂treeKernel Q B hB (some (Sum.inr s)) := by
  let F (u : List ι) (t : List ι → Option S) := if u.length = n then G u t else 0
  have hF (u : List ι) : Measurable[State.treeFiltration u.length] (F u) := by
    by_cases hu : u.length = n
    · simpa only [F, hu, ↓reduceIte] using hG u hu
    · simpa only [F, hu, ↓reduceIte] using
        (measurable_const : Measurable[State.treeFiltration u.length] (fun _ => (0 : ℝ≥0∞)))
  have hi := lintegral_adaptedPayoff_eq Q B hB s F hF
  refine (lintegral_congr fun t => ?_).trans (hi.trans ?_)
  · apply tsum_congr
    intro u
    by_cases hu : u.length = n <;> simp [F, hu]
  · apply lintegral_congr_ae
    filter_upwards [ae_treeKernel_unique_spine Q B hB s] with t ht
    obtain ⟨f, ⟨hf, hc⟩, _⟩ := ht
    rw [spinePrefix_eq_of_isRay defaultChild t f hf hc n,
      tsum_eq_single (Combinatorics.UlamHarris.lineagePrefix f n)]
    · have htag : (t (Combinatorics.UlamHarris.lineagePrefix f n)).any Sum.isRight = true := hf n
      simp only [htag, ↓reduceIte, F,
        Combinatorics.UlamHarris.length_lineagePrefix, ↓reduceIte]
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
