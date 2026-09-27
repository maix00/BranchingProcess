import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Filtration
import Combinatorics.BranchingWalk.Step.Basic
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Positions

/-!
# Measurability of realized nodes and positions, root by root

Realization along a remaining path, the displacement of a fixed address,
and the position of a generation-measurably selected address are all
observable at the generation that reveals the path. The proofs are the
single-root inductions of the deterministic branching-walk position lemmas, carrying the
current address along so each step only needs the step at one fixed address of
one fixed root. The mark type and its additive structure are parameters, so
nothing here is specific to `ℝ`.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



/-- Realization along a remaining path, root by root. Same induction as in the
single-root case; the address is carried along so each step only needs the
step at one fixed address of one fixed root. -/
theorem RootIndexed.stepPresentAlong_measurableSet {m : ℕ} {X : Type*}
    [MeasurableSpace X] (i : Fin m)
    (v p : 𝕍) (n : ℕ) (hn : v.length + p.length ≤ n) :
    MeasurableSet[multiRootStepFiltration (m := m) (X := X) n]
      {ω : FiniteRootStepField m ℕ X |
        surviveAlong (ω i) v p} := by
  induction p generalizing v with
  | nil =>
      have hset : {ω : FiniteRootStepField m ℕ X |
          surviveAlong (ω i) v []} = Set.univ := by
        ext ω
        constructor
        · intro _
          trivial
        · intro _
          exact surviveAlong_nil (ω i) v
      rw [hset]
      exact MeasurableSet.univ
  | cons j p ih =>
      have hlen : (v ++ [j]).length = v.length + 1 := by simp
      have hlen' : (j :: p).length = p.length + 1 := by simp
      have hset : {ω : FiniteRootStepField m ℕ X |
          surviveAlong (ω i) v (j :: p)} =
          {ω : FiniteRootStepField m ℕ X |
            survive (ω i v) j} ∩
            {ω : FiniteRootStepField m ℕ X |
              surviveAlong (ω i) (v ++ [j]) p} := by
        ext ω
        simp [surviveAlong]
      rw [hset]
      refine MeasurableSet.inter ?_ ?_
      · exact (multiRootStep_measurable (X := X) i v (by omega))
          (survive_measurableSet (X := X) j)
      · exact ih (v := v ++ [j]) (by omega)

theorem RootIndexed.surviveAlong_measurableSet
    {m : ℕ} {X : Type*} [MeasurableSpace X] (i : Fin m) (u : 𝕍) :
    MeasurableSet[multiRootStepFiltration (m := m) (X := X) u.length]
      {ω : FiniteRootStepField m ℕ X | surviveAlong (ω i) [] u} := by
  exact RootIndexed.stepPresentAlong_measurableSet (X := X) i [] u u.length (by simp)

/-- A mapped displacement is observable at the generation reached by its
address. The mark space and additive position space are independent. -/
theorem RootIndexed.displace_measurable
    {m : ℕ} {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    (d : Mark → Position) (hd : Measurable d)
    (i : Fin m) (v p : 𝕍) (n : ℕ) (hn : v.length + p.length ≤ n) :
    Measurable[multiRootStepFiltration (m := m) (X := Mark) n]
      (fun ω : FiniteRootStepField m ℕ Mark =>
        Combinatorics.Branching.displaceWith d (ω i) v p) := by
  induction p generalizing v with
  | nil => exact measurable_const
  | cons j p ih =>
      have hlen : (v ++ [j]).length = v.length + 1 := by simp
      have hlen' : (j :: p).length = p.length + 1 := by simp
      have hstep : Measurable[multiRootStepFiltration (m := m) (X := Mark) n]
          (fun ω : FiniteRootStepField m ℕ Mark =>
            value' ((ω i v).map d) j) :=
        (value'_measurable (X := Position) j).comp
          ((Step.map_measurable hd).comp
            (multiRootStep_measurable (X := Mark) i v (by omega)))
      have hrec : Measurable[multiRootStepFiltration (m := m) (X := Mark) n]
          (fun ω : FiniteRootStepField m ℕ Mark =>
            Combinatorics.Branching.displaceWith d (ω i) (v ++ [j]) p) :=
        ih (v := v ++ [j]) (by omega)
      change Measurable[multiRootStepFiltration (m := m) (X := Mark) n]
        ((fun ω : FiniteRootStepField m ℕ Mark =>
            value' ((ω i v).map d) j) +
          fun ω => Combinatorics.Branching.displaceWith d (ω i) (v ++ [j]) p)
      exact hstep.add hrec

theorem RootIndexed.position_measurable
    {m : ℕ} {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    (initial : Fin m → Position) (d : Mark → Position) (hd : Measurable d)
    (i : Fin m) (u : 𝕍) :
    Measurable[multiRootStepFiltration (m := m) (X := Mark) u.length]
      (fun ω : FiniteRootStepField m ℕ Mark =>
        RootIndexed.position initial d ω i u) := by
  change Measurable[multiRootStepFiltration (m := m) (X := Mark) u.length]
    ((fun _ : FiniteRootStepField m ℕ Mark => initial i) +
      fun ω => Combinatorics.Branching.displaceWith d (ω i) [] u)
  exact (measurable_const : Measurable[
      multiRootStepFiltration (m := m) (X := Mark) u.length]
      (fun _ : FiniteRootStepField m ℕ Mark => initial i)).add
    (RootIndexed.displace_measurable d hd i [] u u.length (by simp))

def multiRootPositionAtGeneration
    {m : ℕ} {Mark Position : Type*} [AddCommMonoid Position]
    (initial : Fin m → Position) (d : Mark → Position) (n : ℕ)
    (i : Fin m) (u : 𝕍) (ω : FiniteRootStepField m ℕ Mark) : Position :=
  if u.length = n then RootIndexed.position initial d ω i u else 0

theorem multiRootPositionAtGeneration_measurable
    {m : ℕ} {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    (initial : Fin m → Position) (d : Mark → Position) (hd : Measurable d)
    (n : ℕ) (i : Fin m) (u : 𝕍) :
    Measurable[multiRootStepFiltration (m := m) (X := Mark) n]
      (multiRootPositionAtGeneration initial d n i u) := by
  change Measurable[multiRootStepFiltration (m := m) (X := Mark) n]
    (fun ω => if u.length = n then RootIndexed.position initial d ω i u else 0)
  by_cases hu : u.length = n
  · subst n
    simpa using RootIndexed.position_measurable initial d hd i u
  · simp only [hu, ite_false]
    exact measurable_const

set_option linter.style.haveILetI false in
theorem selectedMultiRootAbsolutePosition_measurable
    {m : ℕ} {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    (initial : Fin m → Position) (d : Mark → Position) (hd : Measurable d)
    (n : ℕ) (i : Fin m)
    (chosen : FiniteRootStepField m ℕ Mark → 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := Mark) n] chosen)
    (hdepth : ∀ ω, (chosen ω).length = n) :
    Measurable[multiRootStepFiltration (m := m) (X := Mark) n]
      (fun ω => RootIndexed.position initial d ω i (chosen ω)) := by
  letI : MeasurableSpace (FiniteRootStepField m ℕ Mark) :=
    multiRootStepFiltration (m := m) (X := Mark) n
  have hjoint : Measurable
      (fun p : 𝕍 × FiniteRootStepField m ℕ Mark =>
        multiRootPositionAtGeneration initial d n i p.1 p.2) :=
    measurable_from_prod_countable_right
      (multiRootPositionAtGeneration_measurable initial d hd n i)
  have h := hjoint.comp (hchosen.prodMk measurable_id)
  convert h using 1
  funext ω
  simp [multiRootPositionAtGeneration, hdepth ω]

theorem selectedMultiRootRealizedNode_measurableSet
    {m : ℕ} {X : Type*} [MeasurableSpace X] (n : ℕ) (i : Fin m)
    (chosen : FiniteRootStepField m ℕ X → 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := X) n] chosen)
    (hdepth : ∀ ω, (chosen ω).length = n) :
    MeasurableSet[multiRootStepFiltration (m := m) (X := X) n]
      {ω | surviveAlong (ω i) [] (chosen ω)} := by
  have hset : {ω : FiniteRootStepField m ℕ X |
      surviveAlong (ω i) [] (chosen ω)} =
      ⋃ u : 𝕍,
        {ω : FiniteRootStepField m ℕ X | chosen ω = u} ∩
          {ω | surviveAlong (ω i) [] u} := by
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
      (RootIndexed.surviveAlong_measurableSet (X := X) i u)
  · have hempty :
        {ω : FiniteRootStepField m ℕ X | chosen ω = u} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro heq
      exact hu (heq ▸ hdepth ω)
    simp [hempty]

end ProbabilityTheory.BranchingRandomWalk
