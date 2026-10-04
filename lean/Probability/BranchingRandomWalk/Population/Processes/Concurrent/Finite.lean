/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Processes.Concurrent.Basic
public import Probability.BranchingRandomWalk.Population.Processes.Parallel.Finite

/-!
# Finite realization of concurrent started populations

This is the finite-particle implementation of `Concurrent.component` and
`Concurrent.population`.  Finiteness belongs to the representation used by a
capacity-limited process; it is absent from the underlying concurrent-set
construction.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Concurrent.Finite

/-- Finite-particle realization of one process started at an observable
random generation. -/
def component
    {Ω I V : Type*} [DecidableEq V]
    (start : I → Ω → WithTop ℕ)
    (candidate : I → ℕ → ℕ → Ω → Finset V)
    (i : I) (n : ℕ) (ω : Ω) : Finset V :=
  (Finset.range (n + 1)).biUnion fun k =>
    if start i ω = k then candidate i k (n - k) ω else ∅

theorem component_eq_of_start
    {Ω I V : Type*} [DecidableEq V]
    (start : I → Ω → WithTop ℕ)
    (candidate : I → ℕ → ℕ → Ω → Finset V)
    (i : I) {n k : ℕ} (ω : Ω) (hk : k ≤ n)
    (hstart : start i ω = k) :
    component start candidate i n ω = candidate i k (n - k) ω := by
  classical
  ext v
  simp only [component, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, hv⟩
    by_cases hsj : start i ω = (j : WithTop ℕ)
    · simp only [hsj, ↓reduceIte] at hv
      have hjk : j = k := WithTop.coe_injective (hsj.symm.trans hstart)
      simpa [hjk] using hv
    · simp [hsj] at hv
  · intro hv
    exact ⟨k, Nat.lt_succ_iff.mpr hk, by simpa [hstart]⟩

theorem component_eq_empty_of_lt
    {Ω I V : Type*} [DecidableEq V]
    (start : I → Ω → WithTop ℕ)
    (candidate : I → ℕ → ℕ → Ω → Finset V)
    (i : I) {n : ℕ} (ω : Ω)
    (hstart : (n : WithTop ℕ) < start i ω) :
    component start candidate i n ω = ∅ := by
  classical
  ext v
  simp only [component, Finset.mem_biUnion, Finset.mem_range,
    Finset.notMem_empty, iff_false]
  rintro ⟨k, hk, hv⟩
  by_cases hs : start i ω = (k : WithTop ℕ)
  · simp only [hs, ↓reduceIte] at hv
    exact (not_lt_of_ge (hs ▸ WithTop.coe_le_coe.mpr
      (Nat.lt_succ_iff.mp hk))) hstart
  · simp [hs] at hv

/-- Coercion of the finite realization recovers the abstract set-valued
component. -/
theorem coe_component
    {Ω I V : Type*} [DecidableEq V]
    (start : I → Ω → WithTop ℕ)
    (candidate : I → ℕ → ℕ → Ω → Finset V)
    (i : I) (n : ℕ) (ω : Ω) :
    (↑(component start candidate i n ω) : Set V) =
      Concurrent.component start
        (fun i k age ω => ↑(candidate i k age ω)) i n ω := by
  ext v
  simp only [component, Concurrent.mem_component_iff,
    Finset.mem_biUnion, Finset.mem_range, Finset.mem_coe]
  constructor
  · rintro ⟨k, hk, hv⟩
    by_cases hs : start i ω = (k : WithTop ℕ)
    · exact ⟨k, Nat.lt_succ_iff.mp hk, hs, by simpa [hs] using hv⟩
    · simp [hs] at hv
  · rintro ⟨k, hk, hs, hv⟩
    exact ⟨k, Nat.lt_succ_iff.mpr hk, by simpa [hs]⟩

/-- A stopping-time start preserves adaptation for finite-particle
candidates.  Measurability is proved through individual membership events,
so the ambient particle-label type need not be countable. -/
theorem component_adapted
    {Ω I V : Type*} {m : MeasurableSpace Ω}
    [DecidableEq V]
    (F : Filtration ℕ m)
    (start : I → Ω → WithTop ℕ)
    (hstart : ∀ i, IsStoppingTime F (start i))
    (candidate : I → ℕ → ℕ → Ω → Finset V)
    (hcandidate : ∀ i k age, Measurable[F (k + age)]
      (candidate i k age)) :
    ∀ i n, Measurable[F n] (component start candidate i n) := by
  intro i n
  let pieces : Ω → Fin (n + 1) → Finset V := fun ω k =>
    if start i ω = k.val then candidate i k.val (n - k.val) ω else ∅
  have hpieces : Measurable[F n] pieces := by
    apply (@measurable_pi_iff Ω (Fin (n + 1)) (fun _ => Finset V)
      (F n) (fun _ => inferInstance) pieces).2
    intro k
    have hk : k.val ≤ n := Nat.le_of_lt_succ k.isLt
    have hevent : MeasurableSet[F n] {ω | start i ω = k.val} :=
      (F.mono hk) _ ((hstart i).measurableSet_eq k.val)
    have hcand : Measurable[F n]
        (candidate i k.val (n - k.val)) := by
      have h := hcandidate i k.val (n - k.val)
      rw [Nat.add_sub_of_le hk] at h
      exact h
    exact hcand.ite hevent measurable_const
  have hcombine : Measurable
      (fun p : Fin (n + 1) → Finset V => Finset.univ.biUnion p) := by
    classical
    induction (Finset.univ : Finset (Fin (n + 1))) using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih =>
        simp only [Finset.biUnion_insert]
        have hunion : Measurable
            (fun q : Finset V × Finset V => q.1 ∪ q.2) := by
          rw [measurable_finset_iff]
          intro v
          simpa only [Finset.mem_union, Function.comp_apply] using
            (((measurable_finset_mem v).comp measurable_fst).or
              ((measurable_finset_mem v).comp measurable_snd))
        exact hunion.comp ((measurable_pi_apply k).prodMk ih)
  have hresult := hcombine.comp hpieces
  convert hresult using 1
  funext ω
  ext v
  simp only [pieces, component, Function.comp_apply, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, hv⟩
    exact ⟨⟨k, hk⟩, hv⟩
  · rintro ⟨k, hv⟩
    exact ⟨k.val, k.isLt, hv⟩

/-- Finite set of enabled concurrent components. -/
def population
    {Ω I V : Type*} [DecidableEq I] [DecidableEq V]
    (enabled : ℕ → Ω → Finset I)
    (start : I → Ω → WithTop ℕ)
    (candidate : I → ℕ → ℕ → Ω → Finset V)
    (n : ℕ) (ω : Ω) : Finset V :=
  (enabled n ω).biUnion fun i => component start candidate i n ω

theorem mem_population_iff
    {Ω I V : Type*} [DecidableEq I] [DecidableEq V]
    (enabled : ℕ → Ω → Finset I)
    (start : I → Ω → WithTop ℕ)
    (candidate : I → ℕ → ℕ → Ω → Finset V)
    (n : ℕ) (ω : Ω) (v : V) :
    v ∈ population enabled start candidate n ω ↔
      ∃ i ∈ enabled n ω, v ∈ component start candidate i n ω := by
  simp [population]

/-- Coercion of the finite enabled realization recovers the abstract
set-valued concurrent population. -/
theorem coe_population
    {Ω I V : Type*} [DecidableEq I] [DecidableEq V]
    (enabled : ℕ → Ω → Finset I)
    (start : I → Ω → WithTop ℕ)
    (candidate : I → ℕ → ℕ → Ω → Finset V)
    (n : ℕ) (ω : Ω) :
    (↑(population enabled start candidate n ω) : Set V) =
      Concurrent.population (fun n ω => ↑(enabled n ω)) start
        (fun i k age ω => ↑(candidate i k age ω)) n ω := by
  ext v
  simp only [Finset.mem_coe, mem_population_iff,
    Concurrent.mem_population_iff]
  constructor
  · rintro ⟨i, hi, hv⟩
    have hv' : v ∈ Concurrent.component start
        (fun i k age ω => ↑(candidate i k age ω)) i n ω := by
      rw [← coe_component start candidate i n ω]
      exact hv
    exact ⟨i, hi,
      (Concurrent.mem_component_iff start
        (fun i k age ω => ↑(candidate i k age ω)) i n ω v).mp hv'⟩
  · rintro ⟨i, hi, hv⟩
    refine ⟨i, hi, ?_⟩
    have hv' : v ∈ Concurrent.component start
        (fun i k age ω => ↑(candidate i k age ω)) i n ω :=
      (Concurrent.mem_component_iff start
        (fun i k age ω => ↑(candidate i k age ω)) i n ω v).mpr hv
    rw [← coe_component start candidate i n ω] at hv'
    exact hv'

/-- Adaptation of the finite enabled realization.  The ambient candidate
index type can be arbitrary; only the actual range of each enabled set is
required to be countable. -/
theorem population_adapted
    {Ω I V : Type*} {m : MeasurableSpace Ω}
    [DecidableEq I] [DecidableEq V]
    (F : Filtration ℕ m)
    (enabled : ℕ → Ω → Finset I)
    (start : I → Ω → WithTop ℕ)
    (candidate : I → ℕ → ℕ → Ω → Finset V)
    (henabled : ∀ n s, MeasurableSet[F n] {ω | enabled n ω = s})
    (henabledRange : ∀ n, (Set.range (enabled n)).Countable)
    (hcomponent : ∀ i n,
      Measurable[F n] (component start candidate i n)) :
    ∀ n, Measurable[F n] (population enabled start candidate n) := by
  exact finiteParallelPopulation_adapted F enabled
    (fun i n => component start candidate i n)
    henabled henabledRange hcomponent

theorem population_card_le_sum
    {Ω I V : Type*} [DecidableEq I] [DecidableEq V]
    (enabled : ℕ → Ω → Finset I)
    (start : I → Ω → WithTop ℕ)
    (candidate : I → ℕ → ℕ → Ω → Finset V)
    (n : ℕ) (ω : Ω) :
    (population enabled start candidate n ω).card ≤
      ∑ i ∈ enabled n ω, (component start candidate i n ω).card :=
  Finset.card_biUnion_le

end ProbabilityTheory.BranchingRandomWalk.Concurrent.Finite
