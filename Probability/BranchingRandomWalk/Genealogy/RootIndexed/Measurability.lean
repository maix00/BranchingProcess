import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Filtration
import Combinatorics.BranchingStep.Position.Increment
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Positions

/-!
# Measurability of realized nodes and positions, root by root

Realization along a remaining path, the accumulated mark of a fixed address,
and the position of a generation-measurably selected address are all
observable at the generation that reveals the path. The proofs are the
single-root inductions of `BranchingStep/Position/Measurability.lean`, carrying the
current address along so each step only needs the step at one fixed address of
one fixed root. The mark type and its additive structure are parameters, so
nothing here is specific to `ℝ`.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory



/-- Realization along a remaining path, root by root. Same induction as in the
single-root case; the address is carried along so each step only needs the
step at one fixed address of one fixed root. -/
theorem rootIndexedStepPresentAlong_measurableSet {m : ℕ} {X : Type*}
    [MeasurableSpace X] (i : Fin m)
    (v p : 𝕍) (n : ℕ) (hn : v.length + p.length ≤ n) :
    MeasurableSet[multiRootStepFiltration (m := m) (X := X) n]
      {ω : FiniteRootStepField m X |
        presentAlong (ω i) v p} := by
  induction p generalizing v with
  | nil =>
      have hset : {ω : FiniteRootStepField m X |
          presentAlong (ω i) v []} = Set.univ := by
        ext ω
        simp
      rw [hset]
      exact MeasurableSet.univ
  | cons j p ih =>
      have hlen : (v ++ [j]).length = v.length + 1 := by simp
      have hlen' : (j :: p).length = p.length + 1 := by simp
      have hset : {ω : FiniteRootStepField m X |
          presentAlong (ω i) v (j :: p)} =
          {ω : FiniteRootStepField m X |
            present (ω i v) j} ∩
            {ω : FiniteRootStepField m X |
              presentAlong (ω i) (v ++ [j]) p} := by
        ext ω
        simp [presentAlong]
      rw [hset]
      refine MeasurableSet.inter ?_ ?_
      · exact (multiRootStep_measurable (X := X) i v (by omega))
          (present_measurableSet (X := X) j)
      · exact ih (v := v ++ [j]) (by omega)

theorem rootIndexedRealizedNode_measurableSet
    {m : ℕ} {X : Type*} [MeasurableSpace X] (i : Fin m) (u : 𝕍) :
    MeasurableSet[multiRootStepFiltration (m := m) (X := X) u.length]
      {ω : FiniteRootStepField m X | rootIndexedRealizedNode ω i u} := by
  change MeasurableSet[multiRootStepFiltration (m := m) (X := X) u.length]
    {ω : FiniteRootStepField m X |
      presentAlong (ω i) [] u}
  exact rootIndexedStepPresentAlong_measurableSet (X := X) i [] u u.length (by simp)

/-- The accumulated mark of one root is observable at the generation reached
by its address. -/
theorem rootIndexedAccumulate_measurable
    {m : ℕ} {X : Type*} [MeasurableSpace X] [AddCommMonoid X] [MeasurableAdd₂ X]
    (i : Fin m) (v p : 𝕍) (n : ℕ) (hn : v.length + p.length ≤ n) :
    Measurable[multiRootStepFiltration (m := m) (X := X) n]
      (fun ω : FiniteRootStepField m X =>
        accumulate (ω i) v p) := by
  induction p generalizing v with
  | nil => exact measurable_const
  | cons j p ih =>
      have hlen : (v ++ [j]).length = v.length + 1 := by simp
      have hlen' : (j :: p).length = p.length + 1 := by simp
      have hstep : Measurable[multiRootStepFiltration (m := m) (X := X) n]
          (fun ω : FiniteRootStepField m X =>
            step (ω i v) j) :=
        (step_measurable (X := X) j).comp
          (multiRootStep_measurable (X := X) i v (by omega))
      have hrec : Measurable[multiRootStepFiltration (m := m) (X := X) n]
          (fun ω : FiniteRootStepField m X =>
            accumulate (ω i) (v ++ [j]) p) :=
        ih (v := v ++ [j]) (by omega)
      change Measurable[multiRootStepFiltration (m := m) (X := X) n]
        ((fun ω : FiniteRootStepField m X =>
            step (ω i v) j) +
          fun ω => accumulate (ω i) (v ++ [j]) p)
      exact hstep.add hrec

theorem rootIndexedStepPosition_measurable
    {m : ℕ} {X : Type*} [MeasurableSpace X] [AddCommMonoid X] [MeasurableAdd₂ X]
    (initial : Fin m → X) (i : Fin m) (u : 𝕍) :
    Measurable[multiRootStepFiltration (m := m) (X := X) u.length]
      (fun ω : FiniteRootStepField m X =>
        rootIndexedStepPosition initial ω i u) := by
  change Measurable[multiRootStepFiltration (m := m) (X := X) u.length]
    ((fun _ : FiniteRootStepField m X => initial i) +
      fun ω => accumulate (ω i) [] u)
  exact (measurable_const : Measurable[
      multiRootStepFiltration (m := m) (X := X) u.length]
      (fun _ : FiniteRootStepField m X => initial i)).add
    (rootIndexedAccumulate_measurable (X := X) i [] u u.length
      (by simp))

/-- Position of a fixed root-indexed address once the observed generation
matches its depth, and zero before that. -/
def multiRootPositionAtGeneration
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (initial : Fin m → X) (n : ℕ)
    (i : Fin m) (u : 𝕍) (ω : FiniteRootStepField m X) : X :=
  if u.length = n then rootIndexedStepPosition initial ω i u else 0

theorem multiRootPositionAtGeneration_measurable
    {m : ℕ} {X : Type*} [MeasurableSpace X] [AddCommMonoid X] [MeasurableAdd₂ X]
    (initial : Fin m → X) (n : ℕ) (i : Fin m) (u : 𝕍) :
    Measurable[multiRootStepFiltration (m := m) (X := X) n]
      (multiRootPositionAtGeneration initial n i u) := by
  change Measurable[multiRootStepFiltration (m := m) (X := X) n]
    (fun ω => if u.length = n then
      rootIndexedStepPosition initial ω i u else 0)
  by_cases hu : u.length = n
  · subst n
    simpa using rootIndexedStepPosition_measurable (X := X) initial i u
  · simp only [hu, ite_false]
    exact measurable_const

set_option linter.style.haveILetI false in
theorem selectedMultiRootAbsolutePosition_measurable
    {m : ℕ} {X : Type*} [MeasurableSpace X] [AddCommMonoid X] [MeasurableAdd₂ X]
    (initial : Fin m → X) (n : ℕ) (i : Fin m)
    (chosen : FiniteRootStepField m X → 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := X) n] chosen)
    (hdepth : ∀ ω, (chosen ω).length = n) :
    Measurable[multiRootStepFiltration (m := m) (X := X) n]
      (fun ω => rootIndexedStepPosition initial ω i (chosen ω)) := by
  letI : MeasurableSpace (FiniteRootStepField m X) :=
    multiRootStepFiltration (m := m) (X := X) n
  have hjoint : Measurable
      (fun p : 𝕍 × FiniteRootStepField m X =>
        multiRootPositionAtGeneration initial n i p.1 p.2) :=
    measurable_from_prod_countable_right
      (multiRootPositionAtGeneration_measurable (X := X) initial n i)
  have h := hjoint.comp (hchosen.prodMk measurable_id)
  convert h using 1
  funext ω
  simp [multiRootPositionAtGeneration, hdepth ω]

theorem selectedMultiRootRealizedNode_measurableSet
    {m : ℕ} {X : Type*} [MeasurableSpace X] (n : ℕ) (i : Fin m)
    (chosen : FiniteRootStepField m X → 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := X) n] chosen)
    (hdepth : ∀ ω, (chosen ω).length = n) :
    MeasurableSet[multiRootStepFiltration (m := m) (X := X) n]
      {ω | rootIndexedRealizedNode ω i (chosen ω)} := by
  have hset : {ω : FiniteRootStepField m X |
      rootIndexedRealizedNode ω i (chosen ω)} =
      ⋃ u : 𝕍,
        {ω : FiniteRootStepField m X | chosen ω = u} ∩
          {ω | rootIndexedRealizedNode ω i u} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨chosen ω, rfl, h⟩
    · rintro ⟨u, hu, hreal⟩
      simpa [hu] using hreal
  rw [hset]
  apply MeasurableSet.iUnion
  intro u
  by_cases hu : u.length = n
  · subst n
    exact (hchosen (measurableSet_singleton u)).inter
      (rootIndexedRealizedNode_measurableSet (X := X) i u)
  · have hempty :
        {ω : FiniteRootStepField m X | chosen ω = u} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro heq
      exact hu (heq ▸ hdepth ω)
    simp [hempty]

end ProbabilityTheory.BranchingRandomWalk
