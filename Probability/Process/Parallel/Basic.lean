/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Process.Filtration

/-!
# Parallel population processes

## Public declarations

- `ProbabilityTheory.Process.Parallel.parallelPopulation`: defines
  \(P_t(\omega)=\bigcup_{i\in E_t(\omega)}C_i(t,\omega)\) for an enabled
  index set \(E_t\) and candidate populations \(C_i\).
- `ProbabilityTheory.Process.Parallel.mem_parallelPopulation_iff`:
  membership is equivalent to \(\exists i\in E_t(\omega),\ v\in C_i(t,\omega)\).
- `ProbabilityTheory.Process.Parallel.parallelPopulation_adapted`:
  if enabled-index and candidate maps are adapted and the union map on the
  chosen measurable set spaces is measurable, then their parallel union is
  adapted; no cardinality bound is required.

The basic construction takes arbitrary set-valued candidate populations and
an arbitrary set of enabled indices. No finiteness or countability is built
into the definition. Measurability is stated using the exact structural
condition it needs: the union map on the chosen measurable hyperspaces must be
measurable. Concrete finite and countable realizations can establish that
condition separately.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.Process.Parallel

/-- The union of the candidate populations enabled at time `t`. -/
def parallelPopulation
    {Time Ω I V : Type*}
    (enabled : Time → Ω → Set I)
    (candidate : I → Time → Ω → Set V)
    (t : Time) (ω : Ω) : Set V :=
  ⋃ i ∈ enabled t ω, candidate i t ω

theorem mem_parallelPopulation_iff
    {Time Ω I V : Type*}
    (enabled : Time → Ω → Set I)
    (candidate : I → Time → Ω → Set V)
    (t : Time) (ω : Ω) (v : V) :
    v ∈ parallelPopulation enabled candidate t ω ↔
      ∃ i ∈ enabled t ω, v ∈ candidate i t ω := by
  simp [parallelPopulation]

/-- Parallel union preserves adaptation whenever union is measurable on the
chosen measurable structures on sets. This theorem places no cardinality
restriction on the index or particle types. -/
theorem parallelPopulation_adapted
    {Time Ω I V : Type*}
    (ℱ : Time → MeasurableSpace Ω)
    (enabled : Time → Ω → Set I)
    (candidate : I → Time → Ω → Set V)
    (henabled : ∀ t, @Measurable Ω (Set I) (ℱ t) inferInstance (enabled t))
    (hcandidate : ∀ i t,
      @Measurable Ω (Set V) (ℱ t) inferInstance (candidate i t))
    (hunion : Measurable
      (fun p : Set I × (I → Set V) => ⋃ i ∈ p.1, p.2 i)) :
    ∀ t, @Measurable Ω (Set V) (ℱ t) inferInstance
      (parallelPopulation enabled candidate t) := by
  intro t
  let _ : MeasurableSpace Ω := ℱ t
  have hall : Measurable (fun ω i => candidate i t ω) := by
    rw [measurable_pi_iff]
    exact fun i => hcandidate i t
  exact hunion.comp ((henabled t).prodMk hall)

end ProbabilityTheory.Process.Parallel
