/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.FiniteCausal
public import Probability.BranchingRandomWalk.Selection.Causal

/-!
# Population processes selected by causal rules

A causal rule is applied to a random candidate population at each time.
The resulting retained population uses the same pre-sampled environment; no
extra probability space or independent random seed is required.  Its
measurability follows by composition with the rule's joint measurability.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection

variable {Time Ω ι : Type*} [MeasurableSpace ι]
    {ℱ : Time → MeasurableSpace Ω}

namespace CausalSelectMechanism

/-- The set-valued population retained by a causal general selection rule. -/
def population (R : CausalSelectMechanism Time Ω ι ℱ)
    (candidates : Time → Ω → Set ι) (t : Time) (ω : Ω) : Set ι :=
  R.select t ω (candidates t ω)

theorem population_subset (R : CausalSelectMechanism Time Ω ι ℱ)
    (candidates : Time → Ω → Set ι) (t : Time) (ω : Ω) :
    R.population candidates t ω ⊆ candidates t ω :=
  R.select_subset t ω _

/-- Selection preserves adaptation to the domain flow without a finiteness or
countability premise on the candidate population. -/
theorem measurable_population (R : CausalSelectMechanism Time Ω ι ℱ)
    (candidates : Time → Ω → Set ι)
    (hcandidates : ∀ t,
      @Measurable Ω (Set ι) (ℱ t) inferInstance (candidates t)) :
    ∀ t, @Measurable Ω (Set ι) (ℱ t) inferInstance
      (R.population candidates t) := by
  intro t
  exact R.measurable_select t (candidates t) (hcandidates t)

end CausalSelectMechanism

namespace CausalNSelection

/-- The finite retained population produced from an arbitrary candidate set. -/
def population {N : ℕ} (R : CausalNSelection Time Ω ι N ℱ)
    (candidates : Time → Ω → Set ι) (t : Time) (ω : Ω) : Finset ι :=
  R.select t ω (candidates t ω)

theorem population_subset {N : ℕ} (R : CausalNSelection Time Ω ι N ℱ)
    (candidates : Time → Ω → Set ι) (t : Time) (ω : Ω) :
    ∀ q ∈ R.population candidates t ω, q ∈ candidates t ω := by
  intro q hq
  exact R.select_subset t ω (candidates t ω) q hq

theorem measurable_population {N : ℕ}
    (R : CausalNSelection Time Ω ι N ℱ)
    (candidates : Time → Ω → Set ι)
    (hcandidates : ∀ t,
      @Measurable Ω (Set ι) (ℱ t) inferInstance (candidates t)) :
    ∀ t, @Measurable Ω (Finset ι) (ℱ t) inferInstance
      (R.population candidates t) := by
  intro t
  exact R.measurable_select t (candidates t) (hcandidates t)

end CausalNSelection

namespace CausalFiniteMechanism

/-- The population retained from a time-indexed random candidate population. -/
def population (R : CausalFiniteMechanism Time Ω ι ℱ)
    (candidates : Time → Ω → Finset ι) (t : Time) (ω : Ω) : Finset ι :=
  R.select t ω (candidates t ω)

theorem population_subset (R : CausalFiniteMechanism Time Ω ι ℱ)
    (candidates : Time → Ω → Finset ι) (t : Time) (ω : Ω) :
    R.population candidates t ω ⊆ candidates t ω :=
  R.select_subset t ω _

/-- Adapted candidates remain adapted after a causal selection rule. -/
theorem measurable_population (R : CausalFiniteMechanism Time Ω ι ℱ)
    (candidates : Time → Ω → Finset ι)
    (hcandidates : ∀ t,
      @Measurable Ω (Finset ι) (ℱ t) inferInstance (candidates t)) :
    ∀ t, @Measurable Ω (Finset ι) (ℱ t) inferInstance
      (R.population candidates t) := by
  intro t
  exact R.measurable_select t (candidates t) (hcandidates t)

end CausalFiniteMechanism

namespace CausalFiniteNSelection

/-- The population process selected by a causal exact-`N` rule. -/
def population {N : ℕ} (R : CausalFiniteNSelection Time Ω ι N ℱ)
    (candidates : Time → Ω → Finset ι) (t : Time) (ω : Ω) : Finset ι :=
  R.select t ω (candidates t ω)

theorem population_subset {N : ℕ} (R : CausalFiniteNSelection Time Ω ι N ℱ)
    (candidates : Time → Ω → Finset ι) (t : Time) (ω : Ω) :
    R.population candidates t ω ⊆ candidates t ω :=
  R.select_subset t ω _

@[simp] theorem population_card {N : ℕ}
    (R : CausalFiniteNSelection Time Ω ι N ℱ)
    (candidates : Time → Ω → Finset ι) (t : Time) (ω : Ω) :
    (R.population candidates t ω).card = min N (candidates t ω).card :=
  R.select_card t ω _

theorem measurable_population {N : ℕ}
    (R : CausalFiniteNSelection Time Ω ι N ℱ)
    (candidates : Time → Ω → Finset ι)
    (hcandidates : ∀ t,
      @Measurable Ω (Finset ι) (ℱ t) inferInstance (candidates t)) :
    ∀ t, @Measurable Ω (Finset ι) (ℱ t) inferInstance
      (R.population candidates t) := by
  intro t
  exact R.measurable_select t (candidates t) (hcandidates t)

end CausalFiniteNSelection

end ProbabilityTheory.BranchingRandomWalk.Selection
