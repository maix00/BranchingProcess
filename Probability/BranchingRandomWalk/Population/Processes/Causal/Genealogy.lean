import Probability.BranchingRandomWalk.Population.Processes.Causal

/-!
# Genealogy of causal finite populations

Every retained particle descends from a retained generation-zero root along
genuine surviving edges of the underlying pre-sampled field.  These facts are
purely genealogical: they require no countability, probability law, position
space, or ordering.
-/

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed.CausalFinitePopulation

open Combinatorics.UlamHarris Combinatorics.Branching

variable {Ω Root α X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    {ℱ : ℕ → MeasurableSpace Ω}
    {stepField : Ω → RootIndexed.StepField Root α X}

/-- A retained particle has its root in the initial population and its address
is realized by the underlying pre-sampled field. -/
theorem initial_mem_and_surviveAlong
    (P : RootIndexed.CausalFinitePopulation Ω Root α X ℱ stepField) :
    ∀ {n : ℕ} {ω : Ω} {p : RootIndexed.TreeNode Root α},
      p ∈ P n ω →
        (p.1, []) ∈ P 0 ω ∧ surviveAlong (stepField ω p.1) [] p.2 := by
  intro n
  induction n with
  | zero =>
      intro ω p hp
      have hnil : p.2 = [] := by simpa using P.depth 0 ω p hp
      have hp_eq : p = (p.1, []) := Prod.ext rfl hnil
      rw [hp_eq] at hp ⊢
      exact ⟨hp, surviveAlong_nil _ _⟩
  | succ n ih =>
      intro ω q hq
      have hchild := P.successor n ω hq
      obtain ⟨p, hp, i, hi, rfl⟩ :=
        Combinatorics.Branching.Selection.Coupling.mem_offspringAddressSet.mp
          hchild
      have hparent := ih hp
      exact ⟨hparent.1,
        (surviveAlong_root_append_singleton_iff (stepField ω p.1) p.2 i).2
          ⟨hparent.2, hi⟩⟩

theorem initial_mem_of_mem
    (P : RootIndexed.CausalFinitePopulation Ω Root α X ℱ stepField)
    {n : ℕ} {ω : Ω} {p : RootIndexed.TreeNode Root α} (hp : p ∈ P n ω) :
    (p.1, []) ∈ P 0 ω :=
  (P.initial_mem_and_surviveAlong hp).1

theorem surviveAlong_of_mem
    (P : RootIndexed.CausalFinitePopulation Ω Root α X ℱ stepField)
    {n : ℕ} {ω : Ω} {p : RootIndexed.TreeNode Root α} (hp : p ∈ P n ω) :
    surviveAlong (stepField ω p.1) [] p.2 :=
  (P.initial_mem_and_surviveAlong hp).2

/-- The parent of every retained positive-generation particle was retained in
the preceding generation. -/
theorem parent_mem_of_mem_succ
    (P : RootIndexed.CausalFinitePopulation Ω Root α X ℱ stepField)
    {n : ℕ} {ω : Ω} {q : RootIndexed.TreeNode Root α}
    (hq : q ∈ P (n + 1) ω) :
    parent q ∈ P n ω := by
  have hchild := P.successor n ω hq
  obtain ⟨p, hp, i, hi, rfl⟩ :=
    Combinatorics.Branching.Selection.Coupling.mem_offspringAddressSet.mp
      hchild
  simpa [Combinatorics.Branching.Selection.Coupling.childAddress] using hp

end RootIndexed.CausalFinitePopulation
end ProbabilityTheory.BranchingRandomWalk
