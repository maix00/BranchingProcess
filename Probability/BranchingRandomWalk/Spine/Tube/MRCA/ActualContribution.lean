/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Spine.Tube.MRCA.Expansion

/-!
# Actual MRCA contributions in affine corridors

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.measurableSet_affineCorridorThrough`
  establishes measurability of the affine corridor with a terminal upper bound.
* `ProbabilityTheory.BranchingRandomWalk.Spine.affineCorridorThrough_succ_eq_endpointCutoff`
  identifies the corridor through time `n + 1` with
  `affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_pathGenerationMRCAContribution_affineCorridor_eq`
  identifies the expected actual MRCA contribution at generation `m` with
  `affineTubeMRCAPairContribution φ μ m n initial lower drift width endpointUpper`.

This file connects the recursive path-pair count at a positive MRCA depth to
the conditional continuation-pair observable used in affine-tube estimates.
The ancestral prefix keeps its corridor indicator and survival condition.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.RandomWalk

theorem measurableSet_affineCorridorThrough
    (horizon : ℕ) (lower drift width endpointUpper : ℝ) :
    MeasurableSet (affineCorridorThrough horizon lower drift width endpointUpper) := by
  rw [show affineCorridorThrough horizon lower drift width endpointUpper =
      (⋂ k : Fin (horizon + 1),
        {history | lower + drift * (k.val : ℝ) ≤ history k ∧
          history k ≤ lower + drift * (k.val : ℝ) + width}) ∩
        {history | history ⟨horizon, Nat.lt_succ_self horizon⟩ ≤ endpointUpper} by
        ext history
        simp [affineCorridorThrough]]
  exact (MeasurableSet.iInter fun k =>
    (measurableSet_le measurable_const (measurable_pi_apply k)).inter
      (measurableSet_le (measurable_pi_apply k) measurable_const)).inter
    (measurableSet_le
      (measurable_pi_apply (⟨horizon, Nat.lt_succ_self horizon⟩ : Fin (horizon + 1)))
      measurable_const)

theorem affineCorridorThrough_succ_eq_endpointCutoff
    (n : ℕ) (lower drift width endpointUpper : ℝ) :
    affineCorridorThrough (n + 1) lower drift width endpointUpper =
      affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper := by
  ext history
  simp [affineCorridorThrough, affineCorridorHistoryEndpointCutoff,
    affineCorridorHistory]

private lemma pathGenerationMRCAContribution_zeroTest
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (x : ℝ) (ω : StepField ℕ X) :
    pathGenerationMRCAContribution φ 0 (n + 1)
      (fun _ => (0 : ℝ≥0∞)) x ω = 0 := by
  simp [pathGenerationMRCAContribution, pathGenerationChildObservable,
    survivingPotentialTest, Spine.pathGeneration, pathGenerationTerm]

private lemma pathGenerationChildObservable_congr_prependHistory
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ)
    (F G : (Fin (n + 2) → ℝ) → ℝ≥0∞) (x : ℝ)
    (hFG : ∀ tail : Fin (n + 1) → ℝ,
      F (prependHistory x tail) = G (prependHistory x tail))
    (i : ℕ) (ξ : Step ℕ X) (η : StepField ℕ X) :
    pathGenerationChildObservable φ n F x i ξ η =
      pathGenerationChildObservable φ n G x i ξ η := by
  have htest : (fun tail : Fin (n + 1) → ℝ => F (prependHistory x tail)) =
      fun tail => G (prependHistory x tail) := funext hFG
  unfold pathGenerationChildObservable
  rw [htest]

private lemma pathGenerationMRCAContribution_congr_prependHistory
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ)
    (F G : (Fin (n + 2) → ℝ) → ℝ≥0∞) (x : ℝ)
    (ω : StepField ℕ X)
    (hFG : ∀ tail : Fin (n + 1) → ℝ,
      F (prependHistory x tail) = G (prependHistory x tail)) :
    pathGenerationMRCAContribution φ 0 (n + 1) F x ω =
      pathGenerationMRCAContribution φ 0 (n + 1) G x ω := by
  simp only [pathGenerationMRCAContribution]
  apply tsum_congr
  intro i
  apply tsum_congr
  intro j
  by_cases hij : i ≠ j
  · simp only [if_pos hij]
    rw [pathGenerationChildObservable_congr_prependHistory
        φ n F G x hFG i (ω []) (subtreeStepField [i] ω)]
    rw [pathGenerationChildObservable_congr_prependHistory
        φ n F G x hFG j (ω []) (subtreeStepField [j] ω)]
  · simp [hij]

private lemma pathGenerationMRCAContribution_ifTest
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 2) → ℝ) → ℝ≥0∞)
    (p : Prop) [Decidable p] (x : ℝ) (ω : StepField ℕ X) :
    pathGenerationMRCAContribution φ 0 (n + 1)
      (fun h => if p then F h else 0) x ω =
        if p then pathGenerationMRCAContribution φ 0 (n + 1) F x ω else 0 := by
  by_cases hp : p
  · simp [hp]
  · simp [hp, pathGenerationMRCAContribution_zeroTest]

private lemma displaceWith_measurable_generation_actual
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (v p : TreeNode ℕ)
    (hvp : v.length + p.length ≤ n) :
    Measurable[generationFiltration (M := Step ℕ X) n]
      (fun ω : StepField ℕ X =>
        Combinatorics.Branching.displaceWith φ ω v p) := by
  induction p generalizing v with
  | nil => exact measurable_const
  | cons i p ih =>
      have hparent : v.length < n := by
        simp only [List.length_cons] at hvp
        omega
      have hstep : Measurable[generationFiltration (M := Step ℕ X) n]
          (fun ω : StepField ℕ X =>
            value' ((ω v).map φ) i) := by
        exact (value'_measurable i).comp
          ((Step.map_measurable φ.measurable_toFun).comp
            (mark_measurable_of_depth_lt (M := Step ℕ X) v n hparent))
      have htailBound : (v ++ [i]).length + p.length ≤ n := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        simp only [List.length_cons] at hvp
        omega
      have htail := ih (v := v ++ [i]) htailBound
      change Measurable[generationFiltration (M := Step ℕ X) n]
        (fun ω : StepField ℕ X =>
          value' ((ω v).map φ) i +
            Combinatorics.Branching.displaceWith φ ω (v ++ [i]) p)
      exact hstep.add htail

private lemma pathHistory_measurable_generation_actual
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (x : ℝ) (u : TreeNode ℕ)
    (hu : u.length ≤ n) :
    Measurable[generationFiltration (M := Step ℕ X) n]
      (fun ω : StepField ℕ X => pathHistory φ n x ω u) := by
  letI : MeasurableSpace (StepField ℕ X) :=
    generationFiltration (M := Step ℕ X) n
  rw [measurable_pi_iff]
  intro k
  have htake : (u.take k).length ≤ n := by
    have hlen : (u.take k).length ≤ k.val := by
      simp [List.length_take]
    omega
  exact measurable_const.add
    (displaceWith_measurable_generation_actual φ n [] (u.take k)
      (by simpa using htake))

private lemma pathGenerationTerm_measurable_generation_actual
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ)
    {F : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F)
    (x : ℝ) (u : TreeNode ℕ) :
    Measurable[generationFiltration (M := Step ℕ X) n]
      (pathGenerationTerm φ n F x u) := by
  letI : MeasurableSpace (StepField ℕ X) :=
    generationFiltration (M := Step ℕ X) n
  by_cases hu : u.length = n
  · rw [pathGenerationTerm]
    have hhistory := pathHistory_measurable_generation_actual φ n x u (by omega)
    have hvalue : Measurable (fun ω : StepField ℕ X =>
        F (pathHistory φ n x ω u)) := hF.comp hhistory
    have hsurvive : MeasurableSet
        {ω : StepField ℕ X | surviveAlong ω [] u} := by
      exact surviveAlong_measurableSet (X := X) [] u n (by simpa [hu])
    have hset : {ω : StepField ℕ X | u.length = n ∧ surviveAlong ω [] u} =
        {ω : StepField ℕ X | surviveAlong ω [] u} := by
      ext ω
      simp [hu]
    rw [hset]
    exact hvalue.indicator hsurvive
  · rw [pathGenerationTerm]
    have hset : {ω : StepField ℕ X | u.length = n ∧ surviveAlong ω [] u} =
        (∅ : Set (StepField ℕ X)) := by
      ext ω
      simp [hu]
    rw [hset]
    simpa using
      (measurable_const : Measurable (fun _ : StepField ℕ X => (0 : ℝ≥0∞)))

/-- The expected actual MRCA contribution at generation `m` is the
continuation-pair observable averaged against the generation-`m` prefix.
The global path test is the affine corridor through time `m + n + 1`; the
prefix and shifted continuation corridor indicators are both retained. -/
theorem lintegral_pathGenerationMRCAContribution_affineCorridor_eq
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (m n : ℕ) (initial lower drift width endpointUpper : ℝ) :
    (∫⁻ ω, pathGenerationMRCAContribution φ m ((n + 1) + m)
      ((affineCorridorThrough (n + 1 + m) lower drift width endpointUpper).indicator
        (fun _ => (1 : ℝ≥0∞))) initial ω ∂stepFieldLaw μ) =
      affineTubeMRCAPairContribution φ μ m n initial lower drift width endpointUpper := by
  classical
  let prefixCorridor := affineCorridorPrefix m lower drift width
  let continuationCorridor := affineCorridorThrough (n + 1)
    (lower + drift * (m : ℝ)) drift width endpointUpper
  let globalTest : (Fin (((n + 1) + m) + 1) → ℝ) → ℝ≥0∞ :=
    (affineCorridorThrough (n + 1 + m) lower drift width endpointUpper).indicator
      (fun _ => (1 : ℝ≥0∞))
  let prefixTest : (Fin (m + 1) → ℝ) → ℝ≥0∞ :=
    prefixCorridor.indicator (fun _ => (1 : ℝ≥0∞))
  let continuationTest : (Fin (n + 2) → ℝ) → ℝ≥0∞ :=
    continuationCorridor.indicator (fun _ => (1 : ℝ≥0∞))
  let A : TreeNode ℕ → StepField ℕ X → ℝ≥0∞ := fun u ω =>
    pathGenerationTerm φ m prefixTest initial u ω
  let position : TreeNode ℕ → StepField ℕ X → ℝ := fun u ω =>
    if u.length = m then initial + pathPotential φ ω u else initial
  have hprefix : Measurable prefixTest := by
    exact measurable_const.indicator
      (measurableSet_affineCorridorPrefix m lower drift width)
  have hcontinuation : Measurable continuationTest := by
    exact measurable_const.indicator
      (measurableSet_affineCorridorThrough (n + 1)
        (lower + drift * (m : ℝ)) drift width endpointUpper)
  have hG : continuationCorridor =
      affineCorridorHistoryEndpointCutoff n
        (lower + drift * (m : ℝ)) drift width endpointUpper := by
    exact affineCorridorThrough_succ_eq_endpointCutoff n
      (lower + drift * (m : ℝ)) drift width endpointUpper
  have hA (u : TreeNode ℕ) : Measurable (A u) := by
    exact pathGenerationTerm_measurable φ m hprefix initial u
  have hAgen (u : TreeNode ℕ) :
      Measurable[generationFiltration (M := Step ℕ X) m] (A u) := by
    exact pathGenerationTerm_measurable_generation_actual φ m hprefix initial u
  have hAsupport (u : TreeNode ℕ) (hu : u.length ≠ m) :
      A u = fun _ => 0 := by
    funext ω
    simp [A, pathGenerationTerm, hu]
  have hposition (u : TreeNode ℕ) : Measurable (position u) := by
    by_cases hu : u.length = m
    · simp only [position, if_pos hu]
      change Measurable ((fun _ : StepField ℕ X => initial) +
        fun ω => pathPotential φ ω u)
      exact measurable_const.add (pathPotential_measurable φ [] u)
    · simp [position, hu]
  have hpositionGen (u : TreeNode ℕ) :
      Measurable[generationFiltration (M := Step ℕ X) m] (position u) := by
    letI : MeasurableSpace (StepField ℕ X) :=
      generationFiltration (M := Step ℕ X) m
    by_cases hu : u.length = m
    · simp only [position, if_pos hu]
      change Measurable[generationFiltration (M := Step ℕ X) m]
        ((fun _ : StepField ℕ X => initial) +
          fun ω => displaceWith φ ω [] u)
      exact measurable_const.add
        (displaceWith_measurable_generation_actual φ m [] u (by simpa [hu]))
    · simp [position, hu]
  have hterm (u : TreeNode ℕ) (hu : u.length = m) (ω : StepField ℕ X) :
      pathGenerationSurvivingPrefixMRCAContribution φ m n globalTest
        initial ω ⟨u, hu⟩ =
      A u ω * pathGenerationMRCAContribution φ 0 (n + 1) continuationTest
        (position u ω) (subtreeStepField u ω) := by
    let prefixHit : Prop := pathHistory φ m initial ω u ∈ prefixCorridor
    have hsplit (tail : Fin (n + 1) → ℝ) :
        pathGenerationPrefixTest φ m n globalTest initial ω u
            (prependHistory (initial + pathPotential φ ω u) tail) =
          (if prefixHit then continuationTest
            (prependHistory (initial + pathPotential φ ω u) tail) else 0) := by
      have htail :
          (prependHistory (initial + pathPotential φ ω u) tail)
              ⟨0, by omega⟩ =
            pathHistory φ m initial ω u ⟨m, Nat.lt_succ_self m⟩ := by
        simp [pathHistory_last, hu]
      simpa [globalTest, prefixHit, prefixCorridor, continuationCorridor,
        continuationTest] using
        (pathGenerationPrefixTest_affineCorridorThrough φ m n initial lower
          drift width endpointUpper ω u hu
          (prependHistory (initial + pathPotential φ ω u) tail) htail)
    have hlocal :
        pathGenerationPrefixMRCAContribution φ m n globalTest initial ω u =
          if prefixHit then
            pathGenerationMRCAContribution φ 0 (n + 1) continuationTest
              (position u ω) (subtreeStepField u ω)
          else 0 := by
      unfold pathGenerationPrefixMRCAContribution
      have hroot :
          pathGenerationMRCAContribution φ 0 (n + 1)
            (pathGenerationPrefixTest φ m n globalTest initial ω u)
            (initial + pathPotential φ ω u) (subtreeStepField u ω) =
          pathGenerationMRCAContribution φ 0 (n + 1)
            (fun tail => if prefixHit then continuationTest tail else 0)
            (initial + pathPotential φ ω u) (subtreeStepField u ω) := by
        apply pathGenerationMRCAContribution_congr_prependHistory
        exact hsplit
      rw [hroot]
      simpa [position, hu] using
        (pathGenerationMRCAContribution_ifTest φ n continuationTest
          prefixHit (initial + pathPotential φ ω u) (subtreeStepField u ω))
    by_cases hsurvive : surviveAlong ω [] u
    · simp [pathGenerationSurvivingPrefixMRCAContribution, hlocal, A,
        pathGenerationTerm, prefixTest, prefixCorridor, prefixHit, hu,
        hsurvive, Set.indicator_apply]
    · simp [pathGenerationSurvivingPrefixMRCAContribution, A,
        pathGenerationTerm, hu, hsurvive]
  have hpoint (ω : StepField ℕ X) :
      pathGenerationMRCAContribution φ m ((n + 1) + m) globalTest initial ω =
        ∑' u : TreeNode ℕ, A u ω *
          pathGenerationMRCAContribution φ 0 (n + 1) continuationTest
            (position u ω) (subtreeStepField u ω) := by
    rw [pathGenerationMRCAContribution_eq_sum_prefix φ m n globalTest initial ω]
    let s : Set (TreeNode ℕ) := {u | u.length = m}
    let prefixContribution (u : TreeNode ℕ) : ℝ≥0∞ :=
      if hu : u.length = m then
        pathGenerationSurvivingPrefixMRCAContribution φ m n globalTest
          initial ω ⟨u, hu⟩
      else 0
    calc
      _ = ∑' u : s, prefixContribution u := by
            apply tsum_congr
            intro u
            have hu : u.val.length = m := by simpa [s] using u.property
            simp only [prefixContribution, dif_pos hu]
      _ = ∑' u : TreeNode ℕ,
          s.indicator prefixContribution u :=
            tsum_subtype s prefixContribution
      _ = _ := by
            apply tsum_congr
            intro u
            by_cases hu : u.length = m
            · simp [s, prefixContribution, hu]
              exact hterm u hu ω
            · simp [s, prefixContribution, hu, A, pathGenerationTerm]
  calc
    _ = ∫⁻ ω, ∑' u : TreeNode ℕ, A u ω *
          pathGenerationMRCAContribution φ 0 (n + 1) continuationTest
            (position u ω) (subtreeStepField u ω) ∂stepFieldLaw μ := by
          apply lintegral_congr
          exact hpoint
    _ = ∫⁻ ω, ∑' u : TreeNode ℕ, A u ω *
          pathGenerationChildMeanOffDiagonal φ μ n continuationTest
            (position u ω) (ω u) ∂stepFieldLaw μ := by
          exact lintegral_generationPrefixRootMRCAContribution_eq_childMeanOffDiagonal
            φ μ m n continuationTest hcontinuation A position
            hAgen hA hpositionGen hposition hAsupport
    _ = affineTubeMRCAPairContribution φ μ m n initial lower drift width
          endpointUpper := by
          unfold affineTubeMRCAPairContribution
          apply lintegral_congr
          intro ω
          apply tsum_congr
          intro u
          by_cases hu : u.length = m
          · simp [A, position, pathGenerationTerm, prefixCorridor, prefixTest,
              continuationTest, continuationCorridor, hG, hu]
          · simp [A, position, pathGenerationTerm, hu]

end ProbabilityTheory.BranchingRandomWalk.Spine
