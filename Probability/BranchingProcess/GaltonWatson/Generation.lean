/-
Copyright (c) 2026 WANG Yiyang.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Combinatorics.BranchingWalk.Basic.GenerationSize
public import Probability.BranchingProcess.Offspring.Count
public import Probability.BranchingProcess.GaltonWatson.Law
public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.DomainFlow

/-!
# Galton--Watson generation sizes

Generation sizes reuse the `ℕ∞`-valued observation on presampled branching
configurations, so infinite populations remain representable.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.GaltonWatson

open MeasureTheory
open scoped ENNReal

private theorem surviveAlong_measurableSet_under_law {ι : Type*}
    (v u : Combinatorics.UlamHarris.TreeNode ι) :
    MeasurableSet {β : Combinatorics.Branching.Process ι |
      Combinatorics.Branching.surviveAlong (β.step PUnit.unit) v u} := by
  have hpair : Measurable
      (fun β : Combinatorics.Branching.Process ι => (β.step, β.initial)) :=
    Measurable.of_comap_le le_rfl
  have hstep : Measurable
      (fun β : Combinatorics.Branching.Process ι => β.step PUnit.unit) :=
    (measurable_pi_apply PUnit.unit).comp (measurable_fst.comp hpair)
  induction u generalizing v with
  | nil =>
      have hset : {β : Combinatorics.Branching.Process ι |
          Combinatorics.Branching.surviveAlong (β.step PUnit.unit) v []} = Set.univ := by
        ext β
        simp [Combinatorics.Branching.surviveAlong]
      rw [hset]
      exact MeasurableSet.univ
  | cons i u ih =>
      have hset : {β : Combinatorics.Branching.Process ι |
          Combinatorics.Branching.surviveAlong (β.step PUnit.unit) v (i :: u)} =
          {β | Combinatorics.Branching.survive (β.step PUnit.unit v) i} ∩
            {β | Combinatorics.Branching.surviveAlong
              (β.step PUnit.unit) (v ++ [i]) u} := by
        ext β
        exact Combinatorics.Branching.surviveAlong_cons _ _ _ _
      rw [hset]
      apply MeasurableSet.inter
      · exact (Combinatorics.Branching.survive_measurableSet i).preimage
          ((measurable_pi_apply v).comp hstep)
      · exact ih (v ++ [i])

/-- The step field below a fixed child address. -/
def childSubtreeField {ι : Type*}
    (field : Combinatorics.Branching.StepField ι PUnit.{1}) (i : ι) :
    Combinatorics.Branching.StepField ι PUnit.{1} :=
  fun u => field (i :: u)

/-- The family of all first-generation descendant fields. -/
def childSubtreeVector {ι : Type*}
    (field : Combinatorics.Branching.StepField ι PUnit.{1}) :
    ι → Combinatorics.Branching.StepField ι PUnit.{1} :=
  fun i => childSubtreeField field i

theorem childSubtreeVector_measurable {ι : Type*} :
    Measurable (childSubtreeVector (ι := ι)) := by
  apply measurable_pi_iff.mpr
  intro i
  exact ProbabilityTheory.BranchingRandomWalk.subtreeStepField_measurable [i]

private theorem childSubtreeVector_measurable_future {ι : Type*} :
    Measurable[ProbabilityTheory.BranchingRandomWalk.stepFutureSpace
      (α := ι) (X := PUnit.{1}) 1]
      (childSubtreeVector (ι := ι)) := by
  refine (@measurable_pi_iff
    (Combinatorics.Branching.StepField ι PUnit.{1}) ι
    (fun _ => Combinatorics.Branching.StepField ι PUnit.{1})
    (ProbabilityTheory.BranchingRandomWalk.stepFutureSpace
      (α := ι) (X := PUnit.{1}) 1)
    (fun _ => inferInstance) (childSubtreeVector (ι := ι))).2 ?_
  intro i
  refine (@measurable_pi_iff
    (Combinatorics.Branching.StepField ι PUnit.{1})
    (Combinatorics.UlamHarris.TreeNode ι)
    (fun _ => Combinatorics.Branching.Step ι PUnit.{1})
    (ProbabilityTheory.BranchingRandomWalk.stepFutureSpace
      (α := ι) (X := PUnit.{1}) 1)
    (fun _ => inferInstance)
    (childSubtreeField (ι := ι) · i)).2 ?_
  intro u
  have hcoord : Measurable[ProbabilityTheory.BranchingRandomWalk.stepCoordinateSpace
      (X := PUnit.{1}) ([i] ++ u)]
      (fun field : Combinatorics.Branching.StepField ι PUnit.{1} => field ([i] ++ u)) :=
    Measurable.of_comap_le le_rfl
  have hle : ProbabilityTheory.BranchingRandomWalk.stepCoordinateSpace
      (X := PUnit.{1}) ([i] ++ u) ≤
      ProbabilityTheory.BranchingRandomWalk.stepFutureSpace
        (α := ι) (X := PUnit.{1}) 1 := by
    exact le_iSup_of_le ([i] ++ u)
      (le_iSup_of_le (by simp : 1 ≤ ([i] ++ u).length) le_rfl)
  exact hcoord.mono hle le_rfl

/-- The vector of child descendant fields has the law of an independent family
of copies of the offspring field. -/
theorem childSubtreeVector_law {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) :
    Measure.map (childSubtreeVector (ι := ι))
      (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})) =
        Measure.infinitePi (fun _ : ι =>
          (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1}))) := by
  let ν : Measure (Combinatorics.Branching.Step ι PUnit.{1}) := μ
  have hflat := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Combinatorics.UlamHarris.TreeNode ι => ν)
    (f := fun p : ι × Combinatorics.UlamHarris.TreeNode ι => p.1 :: p.2)
    (by
      intro p q hpq
      injection hpq with hhead htail
      exact Prod.ext hhead htail)
  have hcurry := Measure.infinitePi_map_curry
    (μ := fun (_ : ι) (_ : Combinatorics.UlamHarris.TreeNode ι) => ν)
  rw [ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.fieldLaw_toMeasure]
  change Measure.map
      (fun field : Combinatorics.Branching.StepField ι PUnit.{1} =>
        fun i u => field (i :: u))
      (Measure.infinitePi (fun _ : Combinatorics.UlamHarris.TreeNode ι => ν)) =
        Measure.infinitePi (fun _ : ι =>
          Measure.infinitePi (fun _ : Combinatorics.UlamHarris.TreeNode ι => ν))
  rw [← hcurry, ← hflat]
  rw [Measure.map_map]
  · rfl
  · exact (MeasurableEquiv.curry ι (Combinatorics.UlamHarris.TreeNode ι)
      (Combinatorics.Branching.Step ι PUnit.{1})).measurable
  · apply measurable_pi_iff.mpr
    intro p
    exact measurable_pi_apply (p.1 :: p.2)

/-- The root configuration and the complete family of child descendant fields
are independent under the presampled Galton--Watson law. -/
theorem fieldLaw_root_childSubtrees_jointLaw {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) :
    Measure.map
      (fun field : Combinatorics.Branching.StepField ι PUnit.{1} =>
        (field [], childSubtreeVector field))
      (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})) =
        (μ : Measure (Combinatorics.Branching.Step ι PUnit.{1})).prod
          (Measure.infinitePi fun _ : ι =>
            (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1}))) := by
  let ν : Measure (Combinatorics.Branching.Step ι PUnit.{1}) := μ
  have hrootPast : Measurable[ProbabilityTheory.BranchingRandomWalk.generationFiltration
      (M := Combinatorics.Branching.Step ι PUnit.{1}) 1]
      (fun field : Combinatorics.Branching.StepField ι PUnit.{1} => field []) :=
    ProbabilityTheory.BranchingRandomWalk.mark_measurable_of_depth_lt [] 1 (by simp)
  have hroot : Measurable (fun field : Combinatorics.Branching.StepField ι PUnit.{1} =>
      field []) := measurable_pi_apply []
  have hvector : Measurable (childSubtreeVector (ι := ι)) :=
    childSubtreeVector_measurable
  have hindPast : Indep
      (ProbabilityTheory.BranchingRandomWalk.generationFiltration
        (M := Combinatorics.Branching.Step ι PUnit.{1}) 1)
      (ProbabilityTheory.BranchingRandomWalk.stepFutureSpace
        (α := ι) (X := PUnit.{1}) 1)
      (ProbabilityTheory.BranchingRandomWalk.stepFieldLaw ν) :=
    ProbabilityTheory.BranchingRandomWalk.generation_stepFuture_independent ν 1
  have hindPastVector : Indep
      (ProbabilityTheory.BranchingRandomWalk.generationFiltration
        (M := Combinatorics.Branching.Step ι PUnit.{1}) 1)
      (MeasurableSpace.comap (childSubtreeVector (ι := ι)) inferInstance)
      (ProbabilityTheory.BranchingRandomWalk.stepFieldLaw ν) :=
    ProbabilityTheory.indep_of_indep_of_le_right hindPast
      childSubtreeVector_measurable_future.comap_le
  have hindPastRoot : Indep
      (MeasurableSpace.comap
        (fun field : Combinatorics.Branching.StepField ι PUnit.{1} => field []) inferInstance)
      (MeasurableSpace.comap (childSubtreeVector (ι := ι)) inferInstance)
      (ProbabilityTheory.BranchingRandomWalk.stepFieldLaw ν) :=
    ProbabilityTheory.indep_of_indep_of_le_left hindPastVector hrootPast.comap_le
  have hind : IndepFun
      (fun field : Combinatorics.Branching.StepField ι PUnit.{1} => field [])
      (childSubtreeVector (ι := ι))
      (ProbabilityTheory.BranchingRandomWalk.stepFieldLaw ν) := by
    rw [IndepFun_iff_Indep]
    exact hindPastRoot
  rw [ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.fieldLaw_toMeasure]
  change Measure.map
      (fun field : Combinatorics.Branching.StepField ι PUnit.{1} =>
        (field [], childSubtreeVector field))
      (ProbabilityTheory.BranchingRandomWalk.stepFieldLaw ν) = _
  rw [hind.map_prod_eq_prod_map_map hroot.aemeasurable hvector.aemeasurable,
    ProbabilityTheory.BranchingRandomWalk.stepFieldLaw_coordinate ν []]
  congr 1
  simpa [ProbabilityTheory.BranchingRandomWalk.stepFieldLaw, ν,
    ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.fieldLaw_toMeasure]
    using childSubtreeVector_law μ

/-- The next generation is the disjoint union of the descendant generations
rooted at the children of the initial particle. This is a deterministic
identity for the actual presampled tree, with no branching or moment
assumption. -/
theorem generationSize_succ_eq_sum_childSubtree {ι : Type*} [Finite ι]
    (field : Combinatorics.Branching.StepField ι PUnit.{1}) (n : ℕ) :
    letI : Fintype {i : ι // Combinatorics.Branching.survive (field []) i} :=
      Fintype.ofFinite _
    (Combinatorics.Branching.branchingOfStepField field).generationSize (n + 1) =
      ∑ i : {i : ι // Combinatorics.Branching.survive (field []) i},
        (Combinatorics.Branching.branchingOfStepField
          (childSubtreeField field i.1)).generationSize n := by
  classical
  let β := Combinatorics.Branching.branchingOfStepField field
  let I := {i : ι // Combinatorics.Branching.survive (field []) i}
  let Q := {p : Combinatorics.UlamHarris.RootIndexed.TreeNode PUnit.{1} ι //
    p ∈ Combinatorics.Branching.survivingParticlesAt β (n + 1)}
  let R (i : I) := {p : Combinatorics.UlamHarris.RootIndexed.TreeNode PUnit.{1} ι //
    p ∈ Combinatorics.Branching.survivingParticlesAt
      (Combinatorics.Branching.branchingOfStepField
        (childSubtreeField field i.1)) n}
  letI : Fintype I := Fintype.ofFinite I
  letI : Fintype Q :=
    (Combinatorics.Branching.RootIndexed.BranchingWalk.generationSlice_finite β (n + 1)).fintype
  letI : ∀ i : I, Fintype (R i) := fun i =>
    (Combinatorics.Branching.RootIndexed.BranchingWalk.generationSlice_finite
      (Combinatorics.Branching.branchingOfStepField
        (childSubtreeField field i.1)) n).fintype
  let forward : (Σ i : I, R i) → Q := fun z => by
      rcases z with ⟨⟨i, hi⟩, ⟨⟨r, u⟩, hu⟩⟩
      cases r
      have hu' := (Combinatorics.Branching.mem_survivingParticlesAt_iff
        (Combinatorics.Branching.branchingOfStepField
          (childSubtreeField field i)) n (PUnit.unit, u)).mp hu
      have hpath : Combinatorics.Branching.surviveAlong field [] (i :: u) := by
        rw [Combinatorics.Branching.surviveAlong_cons]
        refine ⟨hi, ?_⟩
        exact (Combinatorics.Branching.surviveAlong_rebase field [i] [] u).mp
          ((Combinatorics.Branching.mem_survivingParticles_iff_surviveAlong
            (Combinatorics.Branching.branchingOfStepField
              (childSubtreeField field i)) PUnit.unit u).mp hu'.1)
      have hlen : u.length = n := by
        simpa [Combinatorics.UlamHarris.generation] using hu'.2
      refine ⟨(PUnit.unit, i :: u), ?_⟩
      rw [Combinatorics.Branching.mem_survivingParticlesAt_iff,
        Combinatorics.Branching.mem_survivingParticles_iff_surviveAlong]
      exact ⟨hpath, by simp [Combinatorics.UlamHarris.generation, hlen]⟩
  let backward : Q → (Σ i : I, R i) := fun q => by
      rcases q with ⟨⟨r, u⟩, hq⟩
      cases r
      have hlen : u.length = n + 1 := by
        simpa [Combinatorics.UlamHarris.generation] using hq.2
      have hidx : 0 < u.length := by omega
      have hne : u ≠ [] := List.ne_nil_of_length_pos hidx
      let i := u.head hne
      let v := u.tail
      have huv : u = i :: v := by
        dsimp [i, v]
        exact (List.cons_head_tail hne).symm
      have hsurvive : Combinatorics.Branching.surviveAlong field [] u :=
        (Combinatorics.Branching.mem_survivingParticles_iff_surviveAlong β PUnit.unit u).mp hq.1
      have hparts := (Combinatorics.Branching.surviveAlong_cons field [] i v).mp
        (huv ▸ hsurvive)
      refine ⟨⟨i, hparts.1⟩, ⟨(PUnit.unit, v), ?_⟩⟩
      rw [Combinatorics.Branching.mem_survivingParticlesAt_iff,
        Combinatorics.Branching.mem_survivingParticles_iff_surviveAlong]
      constructor
      · exact (Combinatorics.Branching.surviveAlong_rebase field [i] [] v).mpr hparts.2
      · simp [Combinatorics.UlamHarris.generation, huv] at hlen ⊢
        omega
  have hleft : Function.LeftInverse backward forward := by
    rintro ⟨⟨i, hi⟩, ⟨⟨r, u⟩, hu⟩⟩
    cases r
    let z : Σ i : I, R i := ⟨⟨i, hi⟩, ⟨(PUnit.unit, u), hu⟩⟩
    have hbase : (backward (forward z)).1 = z.1 := by
      dsimp [backward, forward]
      apply Subtype.ext
      rfl
    change backward (forward z) = z
    refine Sigma.ext hbase ?_
    have hval : (backward (forward z)).2.val = z.2.val := by
      dsimp [backward, forward]
      rfl
    have hcast : hbase ▸ (backward (forward z)).2 = z.2 := by
      apply Subtype.ext
      exact hval
    exact (eqRec_heq hbase (backward (forward z)).2).symm.trans
      (heq_of_eq hcast)
  have hright : Function.RightInverse backward forward := by
    intro q
    rcases q with ⟨⟨r, u⟩, hq⟩
    cases r
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hlen : u.length = n + 1 := by
        simpa [Combinatorics.UlamHarris.generation] using hq.2
      exact List.cons_head_tail (List.ne_nil_of_length_pos (by omega))
  let e : (Σ i : I, R i) ≃ Q := Equiv.ofBijective forward ⟨
    hleft.injective, hright.surjective⟩
  have hgen : β.generationSize (n + 1) = (Fintype.card Q : ℕ∞) := by
    unfold Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize
    rw [← Set.coe_fintypeCard (Combinatorics.Branching.survivingParticlesAt β (n + 1))]
  have hsub (i : I) :
      (Combinatorics.Branching.branchingOfStepField
        (childSubtreeField field i.1)).generationSize n = (Fintype.card (R i) : ℕ∞) := by
    unfold Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize
    rw [← Set.coe_fintypeCard
      (Combinatorics.Branching.survivingParticlesAt
        (Combinatorics.Branching.branchingOfStepField
          (childSubtreeField field i.1)) n)]
  calc
    β.generationSize (n + 1) = (Fintype.card Q : ℕ∞) := hgen
    _ = (Fintype.card (Σ i : I, R i) : ℕ∞) := by
      exact_mod_cast Fintype.card_congr e.symm
    _ = ∑ i : I, (Fintype.card (R i) : ℕ∞) := by simp [Fintype.card_sigma]
    _ = ∑ i : I,
        (Combinatorics.Branching.branchingOfStepField
          (childSubtreeField field i.1)).generationSize n := by
      simp_rw [← hsub]

/-- The same recursion written over the fixed slot type, with absent children
contributing zero. This fixed index set is useful when integrating against the
offspring field law. -/
theorem generationSize_succ_eq_sum_childSubtreeSlots {ι : Type*} [Fintype ι]
    (field : Combinatorics.Branching.StepField ι PUnit.{1})
    [DecidablePred (fun i => Combinatorics.Branching.survive (field []) i)] (n : ℕ) :
    (Combinatorics.Branching.branchingOfStepField field).generationSize (n + 1) =
      ∑ i : ι, if Combinatorics.Branching.survive (field []) i then
        (Combinatorics.Branching.branchingOfStepField
          (childSubtreeField field i)).generationSize n else 0 := by
  classical
  rw [generationSize_succ_eq_sum_childSubtree]
  let P : ι → Prop := fun i => Combinatorics.Branching.survive (field []) i
  letI : Fintype {i : ι // P i} := Fintype.ofFinite _
  let G : ι → ℕ∞ := fun i =>
    (Combinatorics.Branching.branchingOfStepField
      (childSubtreeField field i)).generationSize n
  let F : ι → ℕ∞ := fun i => if P i then G i else 0
  change (∑ i : {i // P i}, G i.1) = ∑ i : ι, F i
  have huniv : Finset.univ = Finset.subtype P (Finset.univ : Finset ι) := by
    ext i
    simp
  rw [show (∑ i : {i // P i}, G i.1) =
      ∑ i ∈ (Finset.univ : Finset {i // P i}), G i.1 by rfl]
  rw [huniv, Finset.sum_subtype_eq_sum_filter, Finset.sum_filter]


/-- Every fixed generation count is a measurable observation under the
presampled Galton--Watson configuration law. -/
theorem generationSize_measurable {ι : Type*} [Countable ι] (n : ℕ) :
    Measurable (fun β : Combinatorics.Branching.Process ι => β.generationSize n) := by
  unfold Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize
  apply measurable_encard.comp
  rw [measurable_set_iff]
  intro p
  rcases p with ⟨r, u⟩
  cases r
  have hset : MeasurableSet {β : Combinatorics.Branching.Process ι |
      (PUnit.unit, u) ∈ Combinatorics.Branching.survivingParticlesAt β n} := by
    by_cases hlen : u.length = n
    · have heq : {β : Combinatorics.Branching.Process ι |
          (PUnit.unit, u) ∈ Combinatorics.Branching.survivingParticlesAt β n} =
          {β | Combinatorics.Branching.surviveAlong (β.step PUnit.unit) [] u} := by
        ext β
        change ((PUnit.unit, u) ∈ Combinatorics.Branching.survivingParticles β ∧
            u.length = n) ↔
          Combinatorics.Branching.surviveAlong (β.step PUnit.unit) [] u
        rw [Combinatorics.Branching.mem_survivingParticles_iff_surviveAlong]
        simp [hlen]
      rw [heq]
      exact surviveAlong_measurableSet_under_law [] u
    · have heq : {β : Combinatorics.Branching.Process ι |
          (PUnit.unit, u) ∈ Combinatorics.Branching.survivingParticlesAt β n} = ∅ := by
        ext β
        simp [Combinatorics.Branching.survivingParticlesAt,
          Combinatorics.UlamHarris.generation, hlen]
      rw [heq]
      exact MeasurableSet.empty
  have hevent : ((fun β : Combinatorics.Branching.Process ι =>
      (PUnit.unit, u) ∈ Combinatorics.Branching.survivingParticlesAt β n) ⁻¹'
        ({True} : Set Prop)) =
      {β | (PUnit.unit, u) ∈ Combinatorics.Branching.survivingParticlesAt β n} := by
    ext β
    simp
  exact measurable_to_prop (hevent ▸ hset)

/-- The first-generation size under the presampled Galton--Watson law has the
offspring-count law of the one-step configuration. This includes zero and
infinite offspring counts. -/
theorem generationSize_one_law {ι : Type*} [Countable ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) :
    (law μ).map (fun β : Combinatorics.Branching.Process ι =>
      β.generationSize 1) = μ.childCountLaw := by
  have hpair : Measurable
      (fun β : Combinatorics.Branching.Process ι => (β.step, β.initial)) :=
    Measurable.of_comap_le le_rfl
  have hstepField : Measurable
      (fun β : Combinatorics.Branching.Process ι => β.step PUnit.unit) :=
    (measurable_pi_apply PUnit.unit).comp (measurable_fst.comp hpair)
  have hstep : Measurable
      (fun β : Combinatorics.Branching.Process ι =>
        (β.step PUnit.unit) ([] : Combinatorics.UlamHarris.TreeNode ι)) :=
    (measurable_pi_apply ([] : Combinatorics.UlamHarris.TreeNode ι)).comp hstepField
  have hgeneration : Measurable
      (fun β : Combinatorics.Branching.Process ι => β.generationSize 1) := by
    have hcountStep : Measurable
        (Combinatorics.Branching.Step.childCount :
          Combinatorics.Branching.Step ι PUnit.{1} → ℕ∞) :=
      Combinatorics.Branching.Step.childCount_measurable
    have hcount : Measurable
        (fun β : Combinatorics.Branching.Process ι =>
          Combinatorics.Branching.Step.childCount
            ((β.step PUnit.unit) ([] : Combinatorics.UlamHarris.TreeNode ι))) :=
      hcountStep.comp hstep
    have heq : (fun β : Combinatorics.Branching.Process ι =>
        β.generationSize 1) = fun β =>
          Combinatorics.Branching.Step.childCount
            ((β.step PUnit.unit) ([] : Combinatorics.UlamHarris.TreeNode ι)) := by
      funext β
      exact Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize_one_eq_childCount β
    rw [heq]
    exact hcount
  have hfield : Measurable
      (Combinatorics.Branching.branchingOfStepField (α := ι)) :=
    Combinatorics.Branching.measurable_branchingOfStepField
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, law,
    ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.childCountLaw_toMeasure]
  rw [Measure.map_map hgeneration hfield]
  have hcompose :
      (fun β : Combinatorics.Branching.Process ι => β.generationSize 1) ∘
        Combinatorics.Branching.branchingOfStepField =
      (fun field : Combinatorics.Branching.StepField ι PUnit.{1} =>
        Combinatorics.Branching.Step.childCount (field ([] :
          Combinatorics.UlamHarris.TreeNode ι))) := by
    funext field
    exact Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize_one_eq_childCount
      (Combinatorics.Branching.branchingOfStepField field)
  have hchildCount : Measurable
      (Combinatorics.Branching.Step.childCount :
        Combinatorics.Branching.Step ι PUnit.{1} → ℕ∞) :=
    Combinatorics.Branching.Step.childCount_measurable
  have heval : Measurable
      (fun field : Combinatorics.Branching.StepField ι PUnit.{1} =>
        field ([] : Combinatorics.UlamHarris.TreeNode ι)) :=
    measurable_pi_apply ([] : Combinatorics.UlamHarris.TreeNode ι)
  rw [hcompose]
  calc
    _ = (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})).map
      (Combinatorics.Branching.Step.childCount ∘
          (fun field : Combinatorics.Branching.StepField ι PUnit.{1} =>
            field ([] : Combinatorics.UlamHarris.TreeNode ι))) := by
      congr 1
    _ = ((μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})).map
          (fun field : Combinatorics.Branching.StepField ι PUnit.{1} =>
            field ([] : Combinatorics.UlamHarris.TreeNode ι))).map
          Combinatorics.Branching.Step.childCount :=
      (Measure.map_map hchildCount heval).symm
    _ = ((μ : Measure (Combinatorics.Branching.Step ι PUnit.{1})).map
          Combinatorics.Branching.Step.childCount) := by
      rw [ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.fieldLaw_coordinate
        μ ([] : Combinatorics.UlamHarris.TreeNode ι)]

/-- The first-generation mean under the actual presampled Galton--Watson law
is the offspring mean. The equality is valid as an extended nonnegative
integral, so no integrability assumption is hidden in this identity. -/
theorem lintegral_generationSize_one_eq_expectedChildCount {ι : Type*}
    [Countable ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) :
    ∫⁻ (β : Combinatorics.Branching.Process ι),
      (β.generationSize 1 : ℝ≥0∞)
        ∂(law μ : Measure (Combinatorics.Branching.Process ι)) =
        μ.expectedChildCount := by
  have hcast : Measurable (fun n : ℕ∞ => (n : ℝ≥0∞)) := by
    fun_prop
  have hmap :
      Measure.map (fun β : Combinatorics.Branching.Process ι =>
        β.generationSize 1) (law μ : Measure (Combinatorics.Branching.Process ι)) =
          (μ.childCountLaw : Measure ℕ∞) :=
    congrArg (fun ν : ProbabilityMeasure ℕ∞ => (ν : Measure ℕ∞))
      (generationSize_one_law μ)
  rw [← lintegral_map hcast (generationSize_measurable 1), hmap]
  rfl

end ProbabilityTheory.BranchingProcess.GaltonWatson

end
