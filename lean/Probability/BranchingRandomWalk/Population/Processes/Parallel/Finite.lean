module

public import Probability.BranchingRandomWalk.Population.Processes.Parallel.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite realizations of parallel population processes

This file supplies the finite-state implementation used by capacity-limited
population processes. Finiteness belongs to this implementation and to its
cardinality estimates, rather than to the basic parallel-union concept.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris

/-- Finite implementation of a parallel population. -/
def finiteParallelPopulation
    {Ω I V : Type*} [DecidableEq I] [DecidableEq V]
    (enabled : ℕ → Ω → Finset I)
    (candidate : I → ℕ → Ω → Finset V)
    (n : ℕ) (ω : Ω) : Finset V :=
  (enabled n ω).biUnion fun i => candidate i n ω

theorem mem_finiteParallelPopulation_iff
    {Ω I V : Type*} [DecidableEq I] [DecidableEq V]
    (enabled : ℕ → Ω → Finset I)
    (candidate : I → ℕ → Ω → Finset V)
    (n : ℕ) (ω : Ω) (v : V) :
    v ∈ finiteParallelPopulation enabled candidate n ω ↔
      ∃ i ∈ enabled n ω, v ∈ candidate i n ω := by
  simp [finiteParallelPopulation]

/-- The finite implementation realizes the general set-valued parallel
population after coercion. -/
theorem coe_finiteParallelPopulation
    {Ω I V : Type*} [DecidableEq I] [DecidableEq V]
    (enabled : ℕ → Ω → Finset I)
    (candidate : I → ℕ → Ω → Finset V)
    (n : ℕ) (ω : Ω) :
    (↑(finiteParallelPopulation enabled candidate n ω) : Set V) =
      parallelPopulation
        (fun n ω => ↑(enabled n ω))
        (fun i n ω => ↑(candidate i n ω)) n ω := by
  ext v
  simp [mem_finiteParallelPopulation_iff, mem_parallelPopulation_iff]

/-- A fixed finite union of adapted candidate populations is adapted. No
countability assumption is imposed on either the candidate indices or the
ambient particle-label type. -/
theorem fixedFiniteParallelPopulation_measurable
    {Ω I V : Type*} {m : MeasurableSpace Ω}
    [DecidableEq I] [DecidableEq V]
    (F : Filtration ℕ m)
    (s : Finset I)
    (candidate : I → ℕ → Ω → Finset V)
    (hcandidate : ∀ i n,
      Measurable[F n] (candidate i n))
    (n : ℕ) :
    Measurable[F n]
      (fun ω => s.biUnion fun i => candidate i n ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.biUnion_insert]
      have hunion : Measurable
          (fun p : Finset V × Finset V => p.1 ∪ p.2) := by
        rw [measurable_finset_iff]
        intro v
        simpa only [Finset.mem_union, Function.comp_apply] using
          (((measurable_finset_mem v).comp measurable_fst).or
            ((measurable_finset_mem v).comp measurable_snd))
      exact hunion.comp ((hcandidate i n).prodMk ih)

/-- The finite implementation is adapted when the fibres of its enabled set
are measurable and its actual range is countable. The ambient index type can
be arbitrary. -/
theorem finiteParallelPopulation_adapted
    {Ω I V : Type*} {m : MeasurableSpace Ω}
    [DecidableEq I] [DecidableEq V]
    (F : Filtration ℕ m)
    (enabled : ℕ → Ω → Finset I)
    (candidate : I → ℕ → Ω → Finset V)
    (henabled : ∀ n s,
      MeasurableSet[F n] {ω | enabled n ω = s})
    (henabledRange : ∀ n, (Set.range (enabled n)).Countable)
    (hcandidate : ∀ i n,
      Measurable[F n] (candidate i n)) :
    ∀ n, Measurable[F n]
      (finiteParallelPopulation enabled candidate n) := by
  intro n
  let S : Set (Finset I) := Set.range (enabled n)
  let _ : Countable S := Set.countable_coe_iff.mpr (henabledRange n)
  intro t ht
  have hpreimage :
      finiteParallelPopulation enabled candidate n ⁻¹' t =
        ⋃ s : S, {ω | enabled n ω = s.1} ∩
          {ω | s.1.biUnion (fun i => candidate i n ω) ∈ t} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro hω
      exact ⟨⟨enabled n ω, Set.mem_range_self ω⟩, rfl,
        by simpa [finiteParallelPopulation] using hω⟩
    · rintro ⟨s, hs, htω⟩
      simpa [finiteParallelPopulation, hs] using htω
  rw [hpreimage]
  apply MeasurableSet.iUnion
  intro s
  exact (henabled n s.1).inter
    ((fixedFiniteParallelPopulation_measurable F s.1 candidate hcandidate n) ht)

/-- The finite concurrent population has at most the sum of the candidate
sizes. -/
theorem finiteParallelPopulation_card_le_sum
    {Ω I V : Type*} [DecidableEq I] [DecidableEq V]
    (enabled : ℕ → Ω → Finset I)
    (candidate : I → ℕ → Ω → Finset V)
    (n : ℕ) (ω : Ω) :
    (finiteParallelPopulation enabled candidate n ω).card ≤
      ∑ i ∈ enabled n ω, (candidate i n ω).card := by
  exact Finset.card_biUnion_le

/-- A uniform per-candidate cap gives the product cap for the finite union. -/
theorem finiteParallelPopulation_card_le_card_mul
    {Ω I V : Type*} [DecidableEq I] [DecidableEq V]
    (enabled : ℕ → Ω → Finset I)
    (candidate : I → ℕ → Ω → Finset V)
    (C n : ℕ) (ω : Ω)
    (hcap : ∀ i ∈ enabled n ω, (candidate i n ω).card ≤ C) :
    (finiteParallelPopulation enabled candidate n ω).card ≤
      (enabled n ω).card * C := by
  exact Finset.card_biUnion_le_card_mul _ _ C hcap

end ProbabilityTheory.BranchingRandomWalk
