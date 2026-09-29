module

public import Probability.BranchingRandomWalk.Population.Processes.Parallel.Basic
public import Probability.BranchingRandomWalk.Timing.Stopping

/-!
# Concurrent populations started at observable times

A candidate process may start at a different observable generation for every
index.  All candidates are defined on the same probability space before any
success or failure is observed.  `component` embeds one age-indexed candidate
into global time, while `population` takes the union of all simultaneously
active components.

The definitions impose no cardinality condition on candidate indices or
particles.  The measurability theorems expose precisely the needed union-map
hypotheses.  Countable, locally finite, and finite-capacity realizations may
discharge those hypotheses separately.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Concurrent

/-- Candidate `i`, read at age `n - k` when its observable start time is `k`.
It is empty if the candidate has not started by generation `n`. -/
def component
    {Ω I V : Type*}
    (start : I → Ω → WithTop ℕ)
    (candidate : I → ℕ → ℕ → Ω → Set V)
    (i : I) (n : ℕ) (ω : Ω) : Set V :=
  ⋃ k ∈ Finset.range (n + 1),
    if start i ω = k then candidate i k (n - k) ω else ∅

/-- Union of the enabled candidate processes at generation `n`.  An enabled
candidate that has not yet started contributes the empty set. -/
def population
    {Ω I V : Type*}
    (enabled : ℕ → Ω → Set I)
    (start : I → Ω → WithTop ℕ)
    (candidate : I → ℕ → ℕ → Ω → Set V)
    (n : ℕ) (ω : Ω) : Set V :=
  ⋃ i ∈ enabled n ω, component start candidate i n ω

theorem mem_component_iff
    {Ω I V : Type*}
    (start : I → Ω → WithTop ℕ)
    (candidate : I → ℕ → ℕ → Ω → Set V)
    (i : I) (n : ℕ) (ω : Ω) (v : V) :
    v ∈ component start candidate i n ω ↔
      ∃ k ≤ n, start i ω = k ∧ v ∈ candidate i k (n - k) ω := by
  simp only [component, Set.mem_iUnion, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, hv⟩
    by_cases hs : start i ω = (k : WithTop ℕ)
    · exact ⟨k, Nat.lt_succ_iff.mp hk, hs, by simpa [hs] using hv⟩
    · simp [hs] at hv
  · rintro ⟨k, hk, hs, hv⟩
    exact ⟨k, Nat.lt_succ_iff.mpr hk, by simpa [hs]⟩

theorem mem_population_iff
    {Ω I V : Type*}
    (enabled : ℕ → Ω → Set I)
    (start : I → Ω → WithTop ℕ)
    (candidate : I → ℕ → ℕ → Ω → Set V)
    (n : ℕ) (ω : Ω) (v : V) :
    v ∈ population enabled start candidate n ω ↔
      ∃ i ∈ enabled n ω, ∃ k, k ≤ n ∧ start i ω = k ∧
        v ∈ candidate i k (n - k) ω := by
  simp only [population, Set.mem_iUnion, mem_component_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, h⟩

theorem component_eq_of_start
    {Ω I V : Type*}
    (start : I → Ω → WithTop ℕ)
    (candidate : I → ℕ → ℕ → Ω → Set V)
    (i : I) {n k : ℕ} (ω : Ω) (hk : k ≤ n)
    (hstart : start i ω = k) :
    component start candidate i n ω = candidate i k (n - k) ω := by
  ext v
  rw [mem_component_iff]
  constructor
  · rintro ⟨j, hj, hsj, hv⟩
    have hjk : j = k := WithTop.coe_injective (hsj.symm.trans hstart)
    simpa [hjk] using hv
  · intro hv
    exact ⟨k, hk, hstart, hv⟩

theorem component_eq_empty_of_lt
    {Ω I V : Type*}
    (start : I → Ω → WithTop ℕ)
    (candidate : I → ℕ → ℕ → Ω → Set V)
    (i : I) {n : ℕ} (ω : Ω)
    (hstart : (n : WithTop ℕ) < start i ω) :
    component start candidate i n ω = ∅ := by
  ext v
  rw [mem_component_iff]
  simp only [Set.notMem_empty, iff_false]
  rintro ⟨k, hk, hs, _⟩
  exact (not_lt_of_ge (hs ▸ WithTop.coe_le_coe.mpr hk)) hstart

/-- Starting one deterministic-start family at a stopping time preserves
adaptation whenever finite union of set-valued coordinates is measurable in
the chosen hyperspace.  This formulation does not require the particle type
to be countable. -/
theorem component_adapted
    {Ω I V : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℕ m)
    (start : I → Ω → WithTop ℕ)
    (hstart : ∀ i, IsStoppingTime F (start i))
    (candidate : I → ℕ → ℕ → Ω → Set V)
    (hcandidate : ∀ i k age, Measurable[F (k + age)]
      (candidate i k age))
    (hunion : ∀ n, Measurable
      (fun p : Fin (n + 1) → Set V => ⋃ k, p k)) :
    ∀ i n, Measurable[F n] (component start candidate i n) := by
  intro i n
  let pieces : Ω → Fin (n + 1) → Set V := fun ω k =>
    if start i ω = k.val then candidate i k.val (n - k.val) ω else ∅
  have hpieces : Measurable[F n] pieces := by
    apply (@measurable_pi_iff Ω (Fin (n + 1)) (fun _ => Set V)
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
  have hresult := (hunion n).comp hpieces
  convert hresult using 1
  funext ω
  ext v
  simp only [pieces, component, Function.comp_apply, Set.mem_iUnion, Finset.mem_range,
    Set.mem_ite_empty_right]
  constructor
  · rintro ⟨k, hk, hs, hv⟩
    exact ⟨⟨k, hk⟩, hs, hv⟩
  · rintro ⟨k, hs, hv⟩
    exact ⟨k.val, k.isLt, hs, hv⟩

/-- The concurrent union is adapted whenever the union over candidate
indices is measurable.  Candidate and particle types remain unrestricted. -/
theorem population_adapted
    {Ω I V : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℕ m)
    (enabled : ℕ → Ω → Set I)
    (start : I → Ω → WithTop ℕ)
    (candidate : I → ℕ → ℕ → Ω → Set V)
    (henabled : ∀ n, Measurable[F n] (enabled n))
    (hcomponent : ∀ i n,
      Measurable[F n] (component start candidate i n))
    (hunion : Measurable
      (fun p : Set I × (I → Set V) => ⋃ i ∈ p.1, p.2 i)) :
    ∀ n, Measurable[F n] (population enabled start candidate n) :=
  parallelPopulation_adapted (fun n => F n) enabled
    (fun i n => component start candidate i n)
    henabled hcomponent hunion

end ProbabilityTheory.BranchingRandomWalk.Concurrent
