import Probability.BranchingRandomWalk.Selection.Mechanism

/-!
# Population processes selected by causal rules

A causal rule is applied to a random finite candidate population at each time.
The resulting retained population uses the same pre-sampled environment; no
extra probability space or independent random seed is required.  Its
measurability follows by composition with the rule's joint measurability.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection

variable {Time Ω ι : Type*} [MeasurableSpace ι]
    {ℱ : Time → MeasurableSpace Ω}

namespace CausalSelectMechanism

/-- The population retained from a time-indexed random candidate population. -/
def population (R : CausalSelectMechanism Time Ω ι ℱ)
    (candidates : Time → Ω → Finset ι) (t : Time) (ω : Ω) : Finset ι :=
  R.select t ω (candidates t ω)

theorem population_subset (R : CausalSelectMechanism Time Ω ι ℱ)
    (candidates : Time → Ω → Finset ι) (t : Time) (ω : Ω) :
    R.population candidates t ω ⊆ candidates t ω :=
  R.select_subset t ω _

/-- Adapted candidates remain adapted after a causal selection rule. -/
theorem measurable_population (R : CausalSelectMechanism Time Ω ι ℱ)
    (candidates : Time → Ω → Finset ι)
    (hcandidates : ∀ t,
      @Measurable Ω (Finset ι) (ℱ t) inferInstance (candidates t)) :
    ∀ t, @Measurable Ω (Finset ι) (ℱ t) inferInstance
      (R.population candidates t) := by
  intro t
  exact R.measurable_select t (candidates t) (hcandidates t)

end CausalSelectMechanism

namespace CausalNSelection

/-- The population process selected by a causal exact-`N` rule. -/
def population {N : ℕ} (R : CausalNSelection Time Ω ι N ℱ)
    (candidates : Time → Ω → Finset ι) (t : Time) (ω : Ω) : Finset ι :=
  R.select t ω (candidates t ω)

theorem population_subset {N : ℕ} (R : CausalNSelection Time Ω ι N ℱ)
    (candidates : Time → Ω → Finset ι) (t : Time) (ω : Ω) :
    R.population candidates t ω ⊆ candidates t ω :=
  R.select_subset t ω _

@[simp] theorem population_card {N : ℕ}
    (R : CausalNSelection Time Ω ι N ℱ)
    (candidates : Time → Ω → Finset ι) (t : Time) (ω : Ω) :
    (R.population candidates t ω).card = min N (candidates t ω).card :=
  R.select_card t ω _

theorem measurable_population {N : ℕ}
    (R : CausalNSelection Time Ω ι N ℱ)
    (candidates : Time → Ω → Finset ι)
    (hcandidates : ∀ t,
      @Measurable Ω (Finset ι) (ℱ t) inferInstance (candidates t)) :
    ∀ t, @Measurable Ω (Finset ι) (ℱ t) inferInstance
      (R.population candidates t) := by
  intro t
  exact R.measurable_select t (candidates t) (hcandidates t)

end CausalNSelection

end ProbabilityTheory.BranchingRandomWalk.Selection
