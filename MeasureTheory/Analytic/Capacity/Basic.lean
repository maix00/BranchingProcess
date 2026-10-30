/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import MeasureTheory.Analytic.Paving.Basic

/-!
# Capacity and capacitable sets

## Public declarations

- `Capacity p` is a monotone set function $m:\mathcal P(X)\to[0,\infty]$
  with $m(\bigcup_n A_n)=\sup_n m(A_n)$ on increasing sequences and
  $m(\bigcap_n A_n)=\inf_n m(A_n)$ on decreasing sequences from $p$.
  `Capacity.capacityOf_eq_coe`, `Capacity.mono`, `capacity_iUnion`, and
  `capacity_iInter` expose these properties.
- `measureCapacity` and `measureCapacity_apply` identify a finite measure
  $\mu$ with the capacity $A\mapsto\mu(A)$.
- `IsCapacitable` defines approximation from below by sets in
  `countableInfClosure p`; `isCapacitable_of_mem` states that every member of
  $p$ is capacitable.
-/

@[expose] public section

open Filter
open MeasureTheory
open MeasureTheory.Analytic
open scoped ENNReal NNReal Topology MeasureTheory

namespace MeasureTheory.Analytic.Paving

variable {𝓧 𝓚 : Type*} {x y : 𝓧} {p : Set (Set 𝓧)} {q : Set (Set 𝓚)}
  {s t : Set 𝓧} {f : ℕ → Set 𝓧}


/-- A capacity is a set function that is monotone, continuous from above for decreasing sequences
of sets satisfying `p`, and continuous from below for increasing sequences of sets.

Any finite measure defines a capacity, but capacities have only the monotonicity properties of
measures. The notable difference is that a capacity is not additive. -/
structure Capacity (p : Set (Set 𝓧)) where
  /-- The set function associated with a capacity. -/
  capacityOf : Set 𝓧 → ℝ≥0∞
  mono' (s t : Set 𝓧) (hst : s ⊆ t) : capacityOf s ≤ capacityOf t
  capacityOf_iUnion : ∀ (f : ℕ → Set 𝓧), Monotone f → capacityOf (⋃ n, f n) = ⨆ n, capacityOf (f n)
  capacityOf_iInter : ∀ (f : ℕ → Set 𝓧), Antitone f → (∀ n, f n ∈ p) →
    capacityOf (⋂ n, f n) = ⨅ n, capacityOf (f n)

variable {m : Capacity p}

namespace Capacity

instance : FunLike (Capacity p) (Set 𝓧) ℝ≥0∞ where
  coe m := m.capacityOf
  coe_injective | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

@[simp] lemma capacityOf_eq_coe (m : Capacity p) : m.capacityOf = m := rfl

lemma mono (m : Capacity p) {s t : Set 𝓧} (hst : s ⊆ t) : m s ≤ m t := m.mono' s t hst

end Capacity

lemma capacity_iUnion (hf : Monotone f) :
    m (⋃ n, f n) = ⨆ n, m (f n) := m.capacityOf_iUnion f hf

lemma capacity_iInter (hf : Antitone f) (hp : ∀ n, f n ∈ p) :
    m (⋂ n, f n) = ⨅ n, m (f n) := m.capacityOf_iInter f hf hp

/-- The capacity defined by a finite measure. -/
def measureCapacity {m𝓧 : MeasurableSpace 𝓧} (μ : Measure 𝓧) [IsFiniteMeasure μ] :
    Capacity {s : Set 𝓧 | MeasurableSet s} where
  capacityOf s := μ s
  mono' s t hst := μ.mono hst
  capacityOf_iUnion f hf := hf.measure_iUnion
  capacityOf_iInter f hf hp := hf.measure_iInter (fun i ↦ (hp i).nullMeasurableSet) ⟨0, by simp⟩

@[simp]
lemma measureCapacity_apply {m𝓧 : MeasurableSpace 𝓧} (μ : Measure 𝓧) [IsFiniteMeasure μ]
    (s : Set 𝓧) :
    (measureCapacity μ) s = μ s := rfl

def IsCapacitable (m : Capacity p) (s : Set 𝓧) : Prop :=
  ∀ a, a < m s → ∃ t, t ∈ countableInfClosure p ∧ t ⊆ s ∧ a ≤ m t

lemma isCapacitable_of_mem (hs : s ∈ p) : IsCapacitable m s :=
  fun a ha ↦ ⟨s, subset_countableInfClosure hs, by simp, ha.le⟩

end MeasureTheory.Analytic.Paving

end
