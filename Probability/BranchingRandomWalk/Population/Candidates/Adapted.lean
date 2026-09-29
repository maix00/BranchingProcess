module

public import Probability.BranchingRandomWalk.Population.Candidates.MultiRoot

/-!
# Causal candidate update for a random finite parent population

The parent address set is countable. Partition by its value and apply the
fixed-parent measurability theorem on each cell. This avoids unfolding the
finite-set update as a product-valued measurable map. The mark type is a
parameter.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



variable {X : Type*} [MeasurableSpace X]

theorem multiRootCandidatesAtGeneration_of_adapted {m : ℕ}
    (N n : ℕ)
    (parents : FiniteRootStepField m ℕ X → Finset (RootAddress m ℕ))
    (hparents : Measurable[multiRootStepFiltration (m := m) (X := X) n] parents) :
    Measurable[multiRootStepFiltration (m := m) (X := X) (n + 1)]
      (fun ω => multiRootCandidatesAtGeneration N n (parents ω) ω) := by
  let F := multiRootStepFiltration (m := m) (X := X) (n + 1)
  have hparents' : Measurable[F] parents :=
    hparents.mono (multiRootStepFiltration (m := m) (X := X) |>.mono (Nat.le_succ n)) le_rfl
  have hsingle (t : Finset (RootAddress m ℕ)) :
      MeasurableSet[F]
        {ω : FiniteRootStepField m ℕ X |
          multiRootCandidatesAtGeneration N n (parents ω) ω = t} := by
    have hcell :
        {ω : FiniteRootStepField m ℕ X |
          multiRootCandidatesAtGeneration N n (parents ω) ω = t} =
          ⋃ s : Finset (RootAddress m ℕ),
            {ω | parents ω = s} ∩
              {ω | multiRootCandidatesAtGeneration N n s ω = t} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro h
        exact ⟨parents ω, rfl, h⟩
      · rintro ⟨s, hs, ht⟩
        simpa [hs] using ht
    rw [hcell]
    apply MeasurableSet.iUnion
    intro s
    exact (hparents' (measurableSet_singleton s)).inter
      ((multiRootCandidatesAtGeneration_fixed_measurable N n s)
        (measurableSet_singleton t))
  intro U hU
  have hpre :
      (fun ω : FiniteRootStepField m ℕ X =>
        multiRootCandidatesAtGeneration N n (parents ω) ω) ⁻¹' U =
        ⋃ t : U,
          {ω : FiniteRootStepField m ℕ X |
            multiRootCandidatesAtGeneration N n (parents ω) ω = t.1} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨⟨_, h⟩, rfl⟩
    · rintro ⟨⟨t, ht⟩, heq⟩
      exact heq ▸ ht
  rw [hpre]
  exact MeasurableSet.iUnion (fun t => hsingle t.1)

end ProbabilityTheory.BranchingRandomWalk
