/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Restart.RootedTrial.Coupling.ReserveSpine
import Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Endpoint
import all Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Lemmas.EndpointHorizon.RootFamily
import all Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Lemmas.EndpointHorizon.Geometry
import Probability.BranchingRandomWalk.Restart.RootedTrial.Reserve.Causal
import Probability.Process.Stopping.Selection.Ranked
import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Basic
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.StoppingSubtrees.Vector.Factorization

/-!
# Fresh-field factorization at the endpoint: proof support

## Internal proof declarations

* `selectedReserveSpineRestartEndpointFreshField_factorization_on_finite` factors the fresh
  descendant field below mixed endpoint roots from the stopped domain information.
* `selectedReserveSpineRestartNSelectedBRWFreshField_factorization_on_finite` gives the
  same factorization with the actual rank-installed first-`N` BRW roots on the finite-endpoint event.

For every stopped-domain measurable event $A$ and measurable set $B$ of
descendant-field vectors, the finite-endpoint restriction factors as
\[
 \operatorname{stepFieldLaw}_{\mu}^{\mathrm{Root}\oplus\mathrm{Root}}
   \bigl(A\cap\{\omega:\tau(\omega)\ne\top\}\cap
      \{\omega:F_R(\omega)\in B\}\bigr)
 =\operatorname{stepFieldLaw}_{\mu}^{\mathrm{Root}\oplus\mathrm{Root}}
   \bigl(A\cap\{\omega:\tau(\omega)\ne\top\}\bigr)\,
   \operatorname{stepFieldLaw}_{\mu}^{\mathrm{Fin}(\mathrm{lower})}(B),
\]
where $\tau$ is the first-success completion time, $R(\omega)$ is the
selected mixed root family, and
$F_R(\omega):=\operatorname{selectedSubtreeStepFieldVector}(R,\omega)$.
-/

section

open MeasureTheory ProbabilityTheory
open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Coupling
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

namespace ProbabilityTheory.BranchingRandomWalk.Completion.Lemmas.EndpointHorizon

/-- Fresh descendant fields below the mixed endpoint roots factor from the
domain filtration on every finite first-success event. The root family is
pre-sampled and stopped-measurable; reserve-spine BRW fallback makes depth and
distinctness pointwise even on exceptional raw fields. -/
lemma selectedReserveSpineRestartEndpointFreshField_factorization_on_finite
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (hnodePath : Measurable (fun p : RootIndexed.TreeNode Root α => p.2))
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ)
    (hupper : 1 ≤ upper) (r : Root)
    (A : Set (RootIndexed.StepField (Root ⊕ Root) α ℝ))
    (B : Set (Fin lower → Combinatorics.UlamHarris.TreeNode α → Step α ℝ))
    (hA : MeasurableSet[(selectedReserveSpineRestartEndpointTime_isStoppingTime
      R growth hR hgrowth lower upper duration r).measurableSpace] A)
    (hB : MeasurableSet B) :
    RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
        (A ∩ {field | selectedReserveSpineRestartEndpointTime R growth hR hgrowth
          lower upper duration r field ≠ ⊤} ∩
          RootIndexed.selectedSubtreeStepFieldVector
            (selectedReserveSpineRestartEndpointFreshRoots N initialPosition
              R growth hR hgrowth lower upper duration r) ⁻¹' B) =
      RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
        (A ∩ {field | selectedReserveSpineRestartEndpointTime R growth hR hgrowth
          lower upper duration r field ≠ ⊤}) *
      RootIndexed.stepFieldLaw (Root := Fin lower) μ B := by
  classical
  let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
    lower upper duration r
  let hτ := selectedReserveSpineRestartEndpointTime_isStoppingTime
    R growth hR hgrowth lower upper duration r
  let roots := selectedReserveSpineRestartEndpointFreshRoots N initialPosition
    R growth hR hgrowth lower upper duration r
  let encode := fun field : RootIndexed.StepField (Root ⊕ Root) α ℝ =>
    fun i : Fin lower =>
      match (roots field i).1 with
      | Sum.inl _ => (false, (roots field i).2)
      | Sum.inr _ => (true, (roots field i).2)
  let decode := fun code : Fin lower → Bool × Combinatorics.UlamHarris.TreeNode α =>
    fun i => if (code i).1 then (Sum.inr r, (code i).2) else (Sum.inl r, (code i).2)
  have hdecode (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) :
      roots field = decode (encode field) := by
    funext i
    let nSelectedBRWEndpointRankVector := selectedReserveSpineRestartNSelectedBRWEndpointRankVector N initialPosition
      R growth hR hgrowth lower upper duration r field i
    by_cases hnSelectedBRWEndpointRankVector : nSelectedBRWEndpointRankVector = (r, [])
    · simp [roots, decode, encode, nSelectedBRWEndpointRankVector, hnSelectedBRWEndpointRankVector,
        selectedReserveSpineRestartEndpointFreshRoots]
    · simp [roots, decode, encode, nSelectedBRWEndpointRankVector, hnSelectedBRWEndpointRankVector,
        selectedReserveSpineRestartEndpointFreshRoots]
  have hcount : (Set.range roots).Countable := by
    have hdecodeCountable : (Set.range decode).Countable := Set.countable_range decode
    apply hdecodeCountable.mono
    rintro q ⟨field, rfl⟩
    exact ⟨encode field, (hdecode field).symm⟩
  have hroots : Measurable[hτ.measurableSpace] roots := by
    simpa [roots, hτ] using
      selectedReserveSpineRestartEndpointFreshRoots_measurable hnodePath
        N initialPosition
        R growth hR hgrowth lower upper duration r
  have hfiber (q : Fin lower → (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α) :
      MeasurableSet[hτ.measurableSpace] {field | roots field = q} := by
    have heq : {field | roots field = q} = ⋂ i, {field | roots field i = q i} := by
      ext field
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h i
        exact congrFun h i
      · intro h
        funext i
        exact h i
    rw [heq]
    apply MeasurableSet.iInter
    intro i
    have hcoord : Measurable[hτ.measurableSpace] (fun field => roots field i) :=
      (@measurable_pi_iff
        (RootIndexed.StepField (Root ⊕ Root) α ℝ) (Fin lower)
        (fun _ => (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α)
        hτ.measurableSpace (fun _ => inferInstance) roots).mp hroots i
    have hsumSingleton : ∀ z : Root ⊕ Root,
        MeasurableSet ({z} : Set (Root ⊕ Root)) := by
      intro z
      cases z with
      | inl x =>
          rw [show ({Sum.inl x} : Set (Root ⊕ Root)) =
            Sum.inl '' ({x} : Set Root) by ext y; simp]
          exact (measurableSet_singleton x).inl_image
      | inr x =>
          rw [show ({Sum.inr x} : Set (Root ⊕ Root)) =
            Sum.inr '' ({x} : Set Root) by ext y; simp]
          exact (measurableSet_singleton x).inr_image
    have htag : MeasurableSet[hτ.measurableSpace]
        {field | (roots field i).1 = (q i).1} :=
      (measurable_fst.comp hcoord) (hsumSingleton (q i).1)
    have hnode : MeasurableSet[hτ.measurableSpace]
        {field | (roots field i).2 = (q i).2} :=
      (measurable_snd.comp hcoord) (measurableSet_singleton (q i).2)
    have hpair : {field | roots field i = q i} =
        {field | (roots field i).1 = (q i).1} ∩
          {field | (roots field i).2 = (q i).2} := by
      ext field
      simp [Prod.ext_iff]
    rw [hpair]
    exact htag.inter hnode
  have hdepth (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) (n : ℕ)
      (htime : τ field = (n : WithTop ℕ)) (i : Fin lower) :
      (roots field i).2.length = n := by
    exact selectedReserveSpineRestartEndpointFreshRoots_depth N initialPosition
      R growth hR hgrowth lower upper duration hupper r field n htime i
  have hinj (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (hfinite : τ field ≠ ⊤) : Function.Injective (roots field) := by
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfinite
    exact selectedReserveSpineRestartEndpointFreshRoots_injective N initialPosition
      R growth hR hgrowth lower upper duration hupper r field n hn.symm
  simpa [τ, hτ, roots] using
    RootIndexed.stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite
      μ τ hτ roots hcount hfiber hdepth hinj A B hA hB

/-- On a finite first-success event, the actual rank-installed endpoint roots
have fresh descendant fields with product law, independently of the stopped
domain past. This is the mixed-root factorization for populations started from
multiple roots: the reserve-spine BRW fallback roots is removed using the a.e. endpoint
population comparison. -/
lemma selectedReserveSpineRestartNSelectedBRWFreshField_factorization_on_finite
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (hnodePath : Measurable (fun p : RootIndexed.TreeNode Root α => p.2))
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ)
    (hupper : 1 ≤ upper) (hbounded : growth.IsBoundedBy 2)
    (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N) (r : Root)
    (A : Set (RootIndexed.StepField (Root ⊕ Root) α ℝ))
    (B : Set (Fin lower → Combinatorics.UlamHarris.TreeNode α → Step α ℝ))
    (hA : MeasurableSet[(selectedReserveSpineRestartEndpointTime_isStoppingTime
      R growth hR hgrowth lower upper duration r).measurableSpace] A)
    (hB : MeasurableSet B) :
    RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
        (A ∩ {field | selectedReserveSpineRestartEndpointTime R growth hR hgrowth
          lower upper duration r field ≠ ⊤} ∩
          RootIndexed.selectedSubtreeStepFieldVector
            (fun field i => (Sum.inr r,
              (selectedReserveSpineRestartNSelectedBRWEndpointRankVector N initialPosition
                R growth hR hgrowth lower upper duration r field i).2)) ⁻¹' B) =
      RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
        (A ∩ {field | selectedReserveSpineRestartEndpointTime R growth hR hgrowth
          lower upper duration r field ≠ ⊤}) *
      RootIndexed.stepFieldLaw (Root := Fin lower) μ B := by
  classical
  let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
    lower upper duration r
  let roots := selectedReserveSpineRestartEndpointFreshRoots N initialPosition
    R growth hR hgrowth lower upper duration r
  let nSelectedBRWEndpointRoots : RootIndexed.StepField (Root ⊕ Root) α ℝ → Fin lower →
      (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α := fun field i =>
    ((Sum.inr r : Root ⊕ Root),
      (selectedReserveSpineRestartNSelectedBRWEndpointRankVector N initialPosition
        R growth hR hgrowth lower upper duration r field i).2)
  have hroot := selectedReserveSpineRestartEndpointFreshRoots_eq_nSelectedBRW_ae
    μ hnorm N initialPosition R growth hR hgrowth lower upper duration hupper
    hbounded hcapacity r
  have hset :
      (A ∩ {field | τ field ≠ ⊤} ∩
        RootIndexed.selectedSubtreeStepFieldVector nSelectedBRWEndpointRoots ⁻¹' B) =ᵐ[
        RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ]
      (A ∩ {field | τ field ≠ ⊤} ∩
        RootIndexed.selectedSubtreeStepFieldVector roots ⁻¹' B) := by
    filter_upwards [hroot] with field hroot
    by_cases hfinite : τ field ≠ ⊤
    · have hroots : roots field = nSelectedBRWEndpointRoots field := by
        funext i
        exact hroot hfinite i
      have hvec : RootIndexed.selectedSubtreeStepFieldVector nSelectedBRWEndpointRoots field =
          RootIndexed.selectedSubtreeStepFieldVector roots field := by
        change RootIndexed.subtreeStepFieldVector (nSelectedBRWEndpointRoots field) field =
          RootIndexed.subtreeStepFieldVector (roots field) field
        exact congrArg (fun v => RootIndexed.subtreeStepFieldVector v field) hroots.symm
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
      apply propext
      constructor
      · rintro ⟨⟨hAfield, hfinite'⟩, hBfield⟩
        exact ⟨⟨hAfield, hfinite'⟩, by rw [hvec] at hBfield; exact hBfield⟩
      · rintro ⟨⟨hAfield, hfinite'⟩, hBfield⟩
        exact ⟨⟨hAfield, hfinite'⟩, by rw [← hvec] at hBfield; exact hBfield⟩
    · simp [hfinite]
  calc
    _ = RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
        (A ∩ {field | τ field ≠ ⊤} ∩
          RootIndexed.selectedSubtreeStepFieldVector roots ⁻¹' B) := measure_congr hset
    _ = RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
          (A ∩ {field | τ field ≠ ⊤}) *
          RootIndexed.stepFieldLaw (Root := Fin lower) μ B := by
      exact selectedReserveSpineRestartEndpointFreshField_factorization_on_finite
        hnodePath μ N initialPosition R growth hR hgrowth lower upper duration
        hupper r A B hA hB



end ProbabilityTheory.BranchingRandomWalk.Completion.Lemmas.EndpointHorizon
