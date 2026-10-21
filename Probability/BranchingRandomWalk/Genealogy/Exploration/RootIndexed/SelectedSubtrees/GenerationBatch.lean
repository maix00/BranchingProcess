/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Measurability
public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily
public import Probability.Independence.Finite
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Generation batches sampled at selected roots

A generation-measurably chosen injective family of particles at depth `n`
exposes a fresh root-indexed field.  Reading the root step of each fresh
subtree gives one independent offspring batch.  This file packages the
generation-by-generation independence argument for an adaptive family of
selected roots.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.RootIndexed

open Combinatorics.UlamHarris
open Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed

/-- Read the step at the root of each tree in a finite root-indexed field. -/
def rootStepBatch {N : ℕ} (field : RootIndexed.StepField (Fin N) ℕ ℝ) :
    Fin N → Step ℕ ℝ :=
  fun i => field i []

theorem measurable_rootStepBatch {N : ℕ} :
    Measurable (rootStepBatch (N := N)) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply ([] : TreeNode ℕ)).comp
    (measurable_pi_apply i)

/-- The root steps of an i.i.d. root-indexed field have the usual batch law. -/
theorem stepFieldLaw_map_rootStepBatch
    {N : ℕ} (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] :
    (RootIndexed.stepFieldLaw (Root := Fin N) μ).map
        (rootStepBatch (N := N)) = Measure.pi (fun _ : Fin N => μ) := by
  let P := RootIndexed.stepFieldLaw (Root := Fin N) μ
  let X : Fin N → RootIndexed.StepField (Fin N) ℕ ℝ → Step ℕ ℝ :=
    fun i field => field i []
  have hX : ∀ i, AEMeasurable (X i) P := by
    intro i
    exact ((measurable_pi_apply ([] : TreeNode ℕ)).comp
      (measurable_pi_apply i)).aemeasurable
  have hcoord : iIndepFun
      (fun p : Fin N × TreeNode ℕ =>
        fun field : RootIndexed.StepField (Fin N) ℕ ℝ => field p.1 p.2) P := by
    unfold P RootIndexed.stepFieldLaw
      _root_.ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
      _root_.ProbabilityTheory.BranchingProcess.offspringFieldLaw
    simpa using (iIndepFun_uncurry_infinitePi'
      (μ := fun (_ : Fin N) (_ : TreeNode ℕ) => μ)
      (X := fun (_ : Fin N) (_ : TreeNode ℕ) => id)
      (fun _ _ => measurable_id))
  have hind : iIndepFun X P := by
    have hinj : Function.Injective (fun i : Fin N => (i, ([] : TreeNode ℕ))) := by
      intro i j hij
      exact congrArg Prod.fst hij
    simpa [X] using hcoord.precomp hinj
  have hXi (i : Fin N) : HasLaw (X i) μ P := by
    refine ⟨hX i, ?_⟩
    exact RootIndexed.stepFieldLaw_coordinate_marginal
      (Root := Fin N) (α := ℕ) μ i []
  have hbatch : HasLaw (fun field i => X i field)
      (Measure.pi (fun _ : Fin N => μ)) P :=
    (iIndepFun_iff_hasLaw_pi_pi hXi).mp hind
  change P.map (fun field i => field i []) =
    Measure.pi (fun _ : Fin N => μ)
  exact hbatch.map_eq

/-- The batch read from a generation-measurably chosen family of roots. -/
noncomputable def selectedRootBatch
    {Root N : ℕ} (chosen : ℕ → RootIndexed.StepField (Fin Root) ℕ ℝ →
      Fin N → Fin Root × TreeNode ℕ) (n : ℕ)
    (field : RootIndexed.StepField (Fin Root) ℕ ℝ) : Fin N → Step ℕ ℝ :=
  rootStepBatch (RootIndexed.selectedSubtreeStepFieldVector
    (chosen n) field)

/-- A selected root batch is measurable at the end of the generation whose
roots it uses. -/
theorem measurable_selectedRootBatch_at_succ
    {Root N : ℕ}
    [MeasurableSingletonClass (Fin Root × TreeNode ℕ)]
    [Countable (Fin Root × TreeNode ℕ)]
    (chosen : ℕ → RootIndexed.StepField (Fin Root) ℕ ℝ →
      Fin N → Fin Root × TreeNode ℕ)
    (hcount : ∀ n, (Set.range (chosen n)).Countable)
    (hfiber : ∀ n roots, MeasurableSet[
      RootIndexed.stepFiltration (Root := Fin Root) (α := ℕ) (X := ℝ) n]
      {field | chosen n field = roots})
    (hdepth : ∀ n field i, (chosen n field i).2.length = n) :
    ∀ n, Measurable[
      RootIndexed.stepFiltration (Root := Fin Root) (α := ℕ) (X := ℝ) (n + 1)]
      (selectedRootBatch chosen n) := by
  intro n
  let F := RootIndexed.stepFiltration (Root := Fin Root) (α := ℕ) (X := ℝ)
  letI : MeasurableSpace (RootIndexed.StepField (Fin Root) ℕ ℝ) := F (n + 1)
  have hcoordinate (i : Fin N) : Measurable[F (n + 1)]
      (fun field : RootIndexed.StepField (Fin Root) ℕ ℝ =>
        (selectedRootBatch chosen n field) i) := by
    have hpreimage (t : Set (Step ℕ ℝ)) (ht : MeasurableSet t) :
        MeasurableSet[F (n + 1)]
          {field | (selectedRootBatch chosen n field) i ∈ t} := by
      let S : Set (Fin N → Fin Root × TreeNode ℕ) := Set.range (chosen n)
      let _ : Countable S := Set.countable_coe_iff.mpr (hcount n)
      have hset : {field | (selectedRootBatch chosen n field) i ∈ t} =
          ⋃ roots : S, {field | chosen n field = roots.1} ∩
            {field | field (roots.1 i).1 (roots.1 i).2 ∈ t} := by
        ext field
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
        constructor
        · intro h
          exact ⟨⟨chosen n field, Set.mem_range_self field⟩, rfl, by
            simpa [selectedRootBatch, rootStepBatch,
              RootIndexed.selectedSubtreeStepFieldVector,
              RootIndexed.subtreeStepFieldVector] using h⟩
        · rintro ⟨roots, hroots, hvalue⟩
          simpa [selectedRootBatch, rootStepBatch, hroots,
            RootIndexed.selectedSubtreeStepFieldVector,
            RootIndexed.subtreeStepFieldVector] using hvalue
      rw [hset]
      apply MeasurableSet.iUnion
      intro roots
      apply MeasurableSet.inter
      · exact (F.mono (Nat.le_succ n)) _ (hfiber n roots.1)
      · have hlen : (roots.1 i).2.length < n + 1 := by
          obtain ⟨field, hfield⟩ := roots.2
          rw [← hfield]
          exact Nat.lt_succ_of_le (Nat.le_of_eq (hdepth n field i))
        exact (RootIndexed.step_measurable
          (X := ℝ) (roots.1 i).1 (roots.1 i).2 hlen) ht
    exact hpreimage
  apply measurable_pi_iff.mpr
  exact hcoordinate

/-- At each generation, the batch read from an adapted injective family of
same-generation roots has the product law and is independent of the exposed
past. -/
theorem selectedRootBatch_independent_and_law
    {Root N : ℕ}
    [MeasurableSingletonClass (Fin Root × TreeNode ℕ)]
    [MeasurableSingletonClass (Fin N → Fin Root × TreeNode ℕ)]
    [Countable (Fin Root × TreeNode ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (chosen : ℕ → RootIndexed.StepField (Fin Root) ℕ ℝ →
      Fin N → Fin Root × TreeNode ℕ)
    (hcount : ∀ n, (Set.range (chosen n)).Countable)
    (hfiber : ∀ n roots, MeasurableSet[
      RootIndexed.stepFiltration (Root := Fin Root) (α := ℕ) (X := ℝ) n]
      {field | chosen n field = roots})
    (hdepth : ∀ n field i, (chosen n field i).2.length = n)
    (hinj : ∀ n field, Function.Injective (chosen n field)) :
    ∀ n,
      Indep (RootIndexed.stepFiltration (Root := Fin Root) (α := ℕ) (X := ℝ) n)
        (MeasurableSpace.comap (selectedRootBatch chosen n) inferInstance)
        (RootIndexed.stepFieldLaw (Root := Fin Root) μ) ∧
      (RootIndexed.stepFieldLaw (Root := Fin Root) μ).map
        (selectedRootBatch chosen n) = Measure.pi (fun _ : Fin N => μ) := by
  intro n
  let fresh := RootIndexed.selectedSubtreeStepFieldVector (chosen n)
  let P := RootIndexed.stepFieldLaw (Root := Fin Root) μ
  have hfreshInd := RootIndexed.selectedSubtreeStepFieldVector_independent
    μ (chosen n) (hcount n) (hfiber n) (hdepth n) (hinj n)
  have hfreshMeas : Measurable fresh :=
    RootIndexed.selectedSubtreeStepFieldVector_measurable
      (chosen n) (hcount n) (hfiber n)
  have heval : Measurable (rootStepBatch (N := N)) := measurable_rootStepBatch
  have hevalComap :
      MeasurableSpace.comap (selectedRootBatch chosen n) inferInstance ≤
        MeasurableSpace.comap fresh inferInstance := by
    rw [show selectedRootBatch chosen n = rootStepBatch ∘ fresh by rfl]
    exact (heval.comp (Measurable.of_comap_le le_rfl)).comap_le
  have hlawFresh := RootIndexed.selectedSubtreeStepFieldVector_law
    μ (chosen n) (hcount n) (hfiber n) (hdepth n) (hinj n)
  constructor
  · rw [show selectedRootBatch chosen n = rootStepBatch ∘ fresh by rfl]
    exact indep_of_indep_of_le_right hfreshInd hevalComap
  · rw [show selectedRootBatch chosen n = rootStepBatch ∘ fresh by rfl,
      ← Measure.map_map heval hfreshMeas, hlawFresh,
      stepFieldLaw_map_rootStepBatch μ]

/-- Successive selected-root batches are jointly i.i.d.  Each batch is
chosen from the already exposed generation; the next generation's subtree
factorization makes it independent of all earlier batches. -/
theorem selectedRootBatch_iIndepFun
    {Root N : ℕ}
    [MeasurableSingletonClass (Fin Root × TreeNode ℕ)]
    [MeasurableSingletonClass (Fin N → Fin Root × TreeNode ℕ)]
    [Countable (Fin Root × TreeNode ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (chosen : ℕ → RootIndexed.StepField (Fin Root) ℕ ℝ →
      Fin N → Fin Root × TreeNode ℕ)
    (hcount : ∀ n, (Set.range (chosen n)).Countable)
    (hfiber : ∀ n roots, MeasurableSet[
      RootIndexed.stepFiltration (Root := Fin Root) (α := ℕ) (X := ℝ) n]
      {field | chosen n field = roots})
    (hdepth : ∀ n field i, (chosen n field i).2.length = n)
    (hinj : ∀ n field, Function.Injective (chosen n field)) :
    iIndepFun (selectedRootBatch chosen ·)
      (RootIndexed.stepFieldLaw (Root := Fin Root) μ) := by
  classical
  let P := RootIndexed.stepFieldLaw (Root := Fin Root) μ
  let F := RootIndexed.stepFiltration (Root := Fin Root) (α := ℕ) (X := ℝ)
  have hprefix : ∀ k,
      iIndepFun (fun i : Fin k => selectedRootBatch chosen i.1) P := by
    intro k
    induction k with
    | zero => exact iIndepFun.of_subsingleton
    | succ k ih =>
      apply iIndepFun.finSucc
      · intro i
        have hbatch := measurable_selectedRootBatch_at_succ
          chosen hcount hfiber hdepth i.1
        have hambient : Measurable (selectedRootBatch chosen i.1) :=
          hbatch.mono (F.le (i.1 + 1)) le_rfl
        exact ⟨selectedRootBatch chosen i.1, hambient, ae_eq_refl _⟩
      · simpa using ih
      · let past : RootIndexed.StepField (Fin Root) ℕ ℝ → Fin k → Fin N → Step ℕ ℝ :=
          fun field i => selectedRootBatch chosen i.1 field
        have hpast : Measurable[F k] past := by
          apply (@measurable_pi_iff
            (RootIndexed.StepField (Fin Root) ℕ ℝ) (Fin k)
            (fun _ => Fin N → Step ℕ ℝ) (F k)
            (fun _ => inferInstance) past).2
          intro i
          have hbatch := measurable_selectedRootBatch_at_succ
            chosen hcount hfiber hdepth i.1
          have hle : i.1 + 1 ≤ k := by omega
          exact hbatch.mono (F.mono hle) le_rfl
        have hind := (selectedRootBatch_independent_and_law
          μ chosen hcount hfiber hdepth hinj k).1
        have hlast : IndepFun past (selectedRootBatch chosen k) P :=
          (IndepFun_iff_Indep past (selectedRootBatch chosen k) P).2
            (indep_of_indep_of_le_left hind hpast.comap_le)
        simpa [past] using hlast
  rw [iIndepFun_iff_finset]
  intro s
  let k := s.sup id + 1
  have hbound : ∀ i : s, i.1 < k := by
    intro i
    dsimp [k]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun x : ℕ => x) i.2)
  let embed : s → Fin k := fun i => ⟨i.1, hbound i⟩
  have hembed : Function.Injective embed := by
    intro i j hij
    apply Subtype.ext
    exact congrArg Fin.val hij
  have hsmall := hprefix k
  have hsmall' := hsmall.precomp hembed
  have heq : (fun i : s => selectedRootBatch chosen i.1) =
      fun i => (fun j : Fin k => selectedRootBatch chosen j.1) (embed i) := by
    funext i
    rfl
  change iIndepFun (fun i : s => selectedRootBatch chosen i.1) P
  rw [heq]
  exact hsmall'

end ProbabilityTheory.BranchingRandomWalk.RootIndexed

end
