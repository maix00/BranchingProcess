import Probability.BranchingRandomWalk.Tree.Filtration
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Adapted unions of locally finite population processes

A family of candidate populations may be evolved concurrently, with only a
finite set enabled at each generation.  If each candidate population and the
fibres of the enabled set are measurable at generation `n`, and only
countably many enabled sets can occur, their union is measurable there too.
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

/-- A finite union of adapted candidate populations is adapted.  No
countability assumption is imposed on the candidate index type. -/
theorem fixedParallelPopulation_measurable
    {M I V : Type*} [MeasurableSpace M]
    [Countable V] [DecidableEq I] [DecidableEq V]
    (s : Finset I)
    (candidate : I → ℕ → Mark ℕ M → Finset V)
    (hcandidate : ∀ i n,
      Measurable[generationFiltration (M := M) n] (candidate i n))
    (n : ℕ) :
    Measurable[generationFiltration (M := M) n]
      (fun ω => s.biUnion fun i => candidate i n ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      simp only [Finset.biUnion_insert]
      have hunion : Measurable
          (fun p : Finset V × Finset V => p.1 ∪ p.2) :=
        measurable_of_countable _
      exact hunion.comp ((hcandidate i n).prodMk ih)

/-- Adapted activation and adapted candidate populations give an adapted
concurrent union.  Countability is required only of the enabled sets that can
actually occur, rather than of the entire candidate index type. -/
theorem parallelPopulation_adapted
    {M I V : Type*} [MeasurableSpace M]
    [Countable V] [DecidableEq I] [DecidableEq V]
    (enabled : ℕ → Mark ℕ M → Finset I)
    (candidate : I → ℕ → Mark ℕ M → Finset V)
    (henabled : ∀ n s,
      MeasurableSet[generationFiltration (M := M) n]
        {ω | enabled n ω = s})
    (henabledRange : ∀ n, (Set.range (enabled n)).Countable)
    (hcandidate : ∀ i n,
      Measurable[generationFiltration (M := M) n] (candidate i n)) :
    ∀ n, Measurable[generationFiltration (M := M) n]
      (parallelPopulation enabled candidate n) := by
  intro n
  let S : Set (Finset I) := Set.range (enabled n)
  let _ : Countable S := Set.countable_coe_iff.mpr (henabledRange n)
  intro t ht
  have hpreimage :
      parallelPopulation enabled candidate n ⁻¹' t =
        ⋃ s : S, {ω | enabled n ω = s.1} ∩
          {ω | s.1.biUnion (fun i => candidate i n ω) ∈ t} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro hω
      exact ⟨⟨enabled n ω, Set.mem_range_self ω⟩, rfl,
        by simpa [parallelPopulation] using hω⟩
    · rintro ⟨s, hs, htω⟩
      simpa [parallelPopulation, hs] using htω
  rw [hpreimage]
  apply MeasurableSet.iUnion
  intro s
  exact (henabled n s.1).inter
    ((fixedParallelPopulation_measurable s.1 candidate hcandidate n) ht)

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
