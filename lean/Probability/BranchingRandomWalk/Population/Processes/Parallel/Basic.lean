import Probability.BranchingRandomWalk.Tree.Filtration
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Adapted unions of finitely many population processes

A finite family of candidate populations may be evolved concurrently.  If
each candidate population and the set of candidates enabled at generation
`n` are measurable at generation `n`, their union is measurable there too.
This is the causal interface needed when dormant genealogical branches are
kept in the state instead of being resumed retrospectively.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris

/-- The union of the populations whose indices are enabled at time `n`. -/
def parallelPopulation
    {Ω I V : Type*} [DecidableEq I] [DecidableEq V]
    (enabled : ℕ → Ω → Finset I)
    (candidate : I → ℕ → Ω → Finset V)
    (n : ℕ) (ω : Ω) : Finset V :=
  (enabled n ω).biUnion fun i => candidate i n ω

theorem mem_parallelPopulation_iff
    {Ω I V : Type*} [DecidableEq I] [DecidableEq V]
    (enabled : ℕ → Ω → Finset I)
    (candidate : I → ℕ → Ω → Finset V)
    (n : ℕ) (ω : Ω) (v : V) :
    v ∈ parallelPopulation enabled candidate n ω ↔
      ∃ i ∈ enabled n ω, v ∈ candidate i n ω := by
  simp [parallelPopulation]

/-- Adapted activation and adapted candidate populations give an adapted
concurrent union.  The state and particle types are countable, as they are for
finite sets of Ulam--Harris addresses. -/
theorem parallelPopulation_adapted
    {M I V : Type*} [MeasurableSpace M]
    [Fintype I] [Countable V] [DecidableEq I] [DecidableEq V]
    (enabled : ℕ → Mark ℕ M → Finset I)
    (candidate : I → ℕ → Mark ℕ M → Finset V)
    (henabled : ∀ n,
      Measurable[generationFiltration (M := M) n] (enabled n))
    (hcandidate : ∀ i n,
      Measurable[generationFiltration (M := M) n] (candidate i n)) :
    ∀ n, Measurable[generationFiltration (M := M) n]
      (parallelPopulation enabled candidate n) := by
  intro n
  have hall : Measurable[generationFiltration (M := M) n]
      (fun ω i => candidate i n ω) := by
    apply (@measurable_pi_iff (Mark ℕ M) I (fun _ => Finset V)
      (generationFiltration (M := M) n) (fun _ => inferInstance)
      (fun ω i => candidate i n ω)).2
    exact fun i => hcandidate i n
  have hpair : Measurable[generationFiltration (M := M) n]
      (fun ω => (enabled n ω, fun i => candidate i n ω)) :=
    (henabled n).prodMk hall
  have hcombine : Measurable
      (fun p : Finset I × (I → Finset V) =>
        p.1.biUnion p.2) :=
    measurable_of_countable _
  exact hcombine.comp hpair

/-- The concurrent population has at most the sum of the candidate sizes. -/
theorem parallelPopulation_card_le_sum
    {Ω I V : Type*} [DecidableEq I] [DecidableEq V]
    (enabled : ℕ → Ω → Finset I)
    (candidate : I → ℕ → Ω → Finset V)
    (n : ℕ) (ω : Ω) :
    (parallelPopulation enabled candidate n ω).card ≤
      ∑ i ∈ enabled n ω, (candidate i n ω).card := by
  exact Finset.card_biUnion_le

/-- A uniform per-candidate cap gives the product cap for the union. -/
theorem parallelPopulation_card_le_card_mul
    {Ω I V : Type*} [DecidableEq I] [DecidableEq V]
    (enabled : ℕ → Ω → Finset I)
    (candidate : I → ℕ → Ω → Finset V)
    (C n : ℕ) (ω : Ω)
    (hcap : ∀ i ∈ enabled n ω, (candidate i n ω).card ≤ C) :
    (parallelPopulation enabled candidate n ω).card ≤
      (enabled n ω).card * C := by
  exact Finset.card_biUnion_le_card_mul _ _ C hcap

end ProbabilityTheory.BranchingRandomWalk
