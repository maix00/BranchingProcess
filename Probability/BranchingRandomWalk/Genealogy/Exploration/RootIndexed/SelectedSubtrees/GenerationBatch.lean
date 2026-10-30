/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Measurability
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.RootBatch
public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily
public import Probability.Independence.FiniteFamily

/-!
# One-step batches sampled at selected roots

A generation-measurably chosen injective finite family of particles at depth
`n` exposes a fresh root-indexed field. Reading the root step of each fresh
subtree gives one independent batch with the original one-step law. The root
type, finite batch index, child-label type, and mark type remain arbitrary.
## Public declarations

* `selectedRootBatch` applies the root-step batch observation from
  `Genealogy/RootIndexed/Law/RootBatch.lean` to subtrees selected from
  generation `n`; `measurable_selectedRootBatch_at_succ` shows it is
  observable at generation `n + 1` for arbitrary root and mark types.
* `selectedRootBatch_independent_and_law` gives the selected offspring batch
  the product law and its independence from generation-`n` observations;
  `selectedRootBatch_iIndepFun` packages the batches across generations as an
  independent family of random variables.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.RootIndexed

open Combinatorics.UlamHarris
open Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed

/-- The batch read from a generation-measurably chosen family of roots. -/
def selectedRootBatch
    {Root κ α X : Type*}
    (chosen : ℕ → RootIndexed.StepField Root α X →
      κ → Root × TreeNode α) (n : ℕ)
    (field : RootIndexed.StepField Root α X) : κ → Step α X :=
  rootStepBatch (Root := κ) (α := α) (X := X)
    (RootIndexed.selectedSubtreeStepFieldVector
    (chosen n) field)

set_option linter.style.haveILetI false in
/-- A selected root batch is measurable at the end of the generation whose
roots it uses. -/
theorem measurable_selectedRootBatch_at_succ
    {Root κ α X : Type*} [MeasurableSpace X]
    (chosen : ℕ → RootIndexed.StepField Root α X →
      κ → Root × TreeNode α)
    (hcount : ∀ n, (Set.range (chosen n)).Countable)
    (hfiber : ∀ n roots, MeasurableSet[
      RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n]
      {field | chosen n field = roots})
    (hdepth : ∀ n field i, (chosen n field i).2.length = n) :
    ∀ n, Measurable[
      RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) (n + 1)]
      (selectedRootBatch chosen n) := by
  intro n
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  letI : MeasurableSpace (RootIndexed.StepField Root α X) := F (n + 1)
  have hcoordinate (i : κ) : Measurable[F (n + 1)]
      (fun field : RootIndexed.StepField Root α X =>
        (selectedRootBatch chosen n field) i) := by
    have hpreimage (t : Set (Step α X)) (ht : MeasurableSet t) :
        MeasurableSet[F (n + 1)]
          {field | (selectedRootBatch chosen n field) i ∈ t} := by
      let S : Set (κ → Root × TreeNode α) := Set.range (chosen n)
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
          (X := X) (roots.1 i).1 (roots.1 i).2 hlen) ht
    exact hpreimage
  apply measurable_pi_iff.mpr
  exact hcoordinate

/-- At each generation, the batch read from an adapted injective family of
same-generation roots has the product law and is independent of the exposed
past. -/
theorem selectedRootBatch_independent_and_law
    {Root κ α X : Type*} [Fintype κ] [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (chosen : ℕ → RootIndexed.StepField Root α X →
      κ → Root × TreeNode α)
    (hcount : ∀ n, (Set.range (chosen n)).Countable)
    (hfiber : ∀ n roots, MeasurableSet[
      RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n]
      {field | chosen n field = roots})
    (hdepth : ∀ n field i, (chosen n field i).2.length = n)
    (hinj : ∀ n field, Function.Injective (chosen n field)) :
    ∀ n,
      Indep (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n)
        (MeasurableSpace.comap (selectedRootBatch chosen n) inferInstance)
        (RootIndexed.stepFieldLaw (Root := Root) μ) ∧
      (RootIndexed.stepFieldLaw (Root := Root) μ).map
        (selectedRootBatch chosen n) = Measure.pi (fun _ : κ => μ) := by
  intro n
  let fresh := RootIndexed.selectedSubtreeStepFieldVector (chosen n)
  let P := RootIndexed.stepFieldLaw (Root := Root) μ
  have hfreshInd := RootIndexed.selectedSubtreeStepFieldVector_independent
    μ (chosen n) (hcount n) (hfiber n) (hdepth n) (hinj n)
  have hfreshMeas : Measurable fresh :=
    RootIndexed.selectedSubtreeStepFieldVector_measurable
      (chosen n) (hcount n) (hfiber n)
  have heval : Measurable
      (rootStepBatch (Root := κ) (α := α) (X := X)) := measurable_rootStepBatch
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
    simp [Measure.infinitePi_eq_pi]

/-- Successive selected-root batches are jointly i.i.d.  Each batch is
chosen from the already exposed generation; the next generation's subtree
factorization makes it independent of all earlier batches. -/
theorem selectedRootBatch_iIndepFun
    {Root κ α X : Type*} [Fintype κ] [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (chosen : ℕ → RootIndexed.StepField Root α X →
      κ → Root × TreeNode α)
    (hcount : ∀ n, (Set.range (chosen n)).Countable)
    (hfiber : ∀ n roots, MeasurableSet[
      RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n]
      {field | chosen n field = roots})
    (hdepth : ∀ n field i, (chosen n field i).2.length = n)
    (hinj : ∀ n field, Function.Injective (chosen n field)) :
    iIndepFun (selectedRootBatch chosen ·)
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  classical
  let P := RootIndexed.stepFieldLaw (Root := Root) μ
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
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
      · let past : RootIndexed.StepField Root α X → Fin k → κ → Step α X :=
          fun field i => selectedRootBatch chosen i.1 field
        have hpast : Measurable[F k] past := by
          apply (@measurable_pi_iff
            (RootIndexed.StepField Root α X) (Fin k)
            (fun _ => κ → Step α X) (F k)
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
