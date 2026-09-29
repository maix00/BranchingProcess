module

public import Probability.BranchingRandomWalk.Selection.Finite

/-!
# Causal finite-input selection mechanisms

Domain-flow adaptations of finite candidate selection, including the capacity-
`N` interface.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection

open Combinatorics.Branching.Selection

/-- A causal time-dependent selection rule. At each time, the random rule is
measurable for exactly the information domain available at that time. -/
structure CausalFiniteMechanism (Time Ω ι : Type*)
    [MeasurableSpace ι] (ℱ : Time → MeasurableSpace Ω) where
  rule : ∀ t, @RandomFiniteMechanism Ω ι (ℱ t) inferInstance

namespace CausalFiniteMechanism

variable {Time Ω ι : Type*} [MeasurableSpace ι]
    {ℱ : Time → MeasurableSpace Ω}

/-- The retained candidates at time `t`. -/
def select (R : CausalFiniteMechanism Time Ω ι ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) : Finset ι :=
  @RandomFiniteMechanism.select Ω ι (ℱ t) inferInstance (R.rule t) ω s

theorem select_subset (R : CausalFiniteMechanism Time Ω ι ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) : R.select t ω s ⊆ s :=
  @RandomFiniteMechanism.subset Ω ι (ℱ t) inferInstance (R.rule t) ω s

/-- A causal rule sends an observable candidate population to an observable
retained population in the same information domain. -/
theorem measurable_select (R : CausalFiniteMechanism Time Ω ι ℱ)
    (t : Time) (candidates : Ω → Finset ι)
    (hcandidates : @Measurable Ω (Finset ι) (ℱ t) inferInstance candidates) :
    @Measurable Ω (Finset ι) (ℱ t) inferInstance
      (fun ω => R.select t ω (candidates ω)) :=
  by
    let _ : MeasurableSpace Ω := ℱ t
    exact (R.rule t).measurable_apply candidates hcandidates

/-- A fixed deterministic mechanism is causal for every information domain. -/
def ofDeterministic (M : FiniteMechanism ι) (hM : Measurable M.select) :
  CausalFiniteMechanism Time Ω ι ℱ where
  rule t := @RandomFiniteMechanism.ofDeterministic Ω ι (ℱ t) _ M hM

end CausalFiniteMechanism

/-- A causal random selection rule with the uniform population cap `N`. -/
structure CausalFiniteNSelection (Time Ω ι : Type*) (N : ℕ)
    [MeasurableSpace ι] (ℱ : Time → MeasurableSpace Ω) where
  rule : ∀ t, @RandomFiniteNSelection Ω ι N (ℱ t) inferInstance

namespace CausalFiniteNSelection

variable {Time Ω ι : Type*} {N : ℕ} [MeasurableSpace ι]
    {ℱ : Time → MeasurableSpace Ω}

def select (R : CausalFiniteNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) : Finset ι :=
  @RandomFiniteMechanism.select Ω ι (ℱ t) inferInstance
    (@RandomFiniteNSelection.toRandomFiniteMechanism Ω ι N (ℱ t) inferInstance
      (R.rule t)) ω s

theorem select_subset (R : CausalFiniteNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) : R.select t ω s ⊆ s :=
  @RandomFiniteMechanism.subset Ω ι (ℱ t) inferInstance
    (@RandomFiniteNSelection.toRandomFiniteMechanism Ω ι N (ℱ t) inferInstance
      (R.rule t)) ω s

theorem select_card_le (R : CausalFiniteNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) :
    (R.select t ω s).card ≤ N :=
  @RandomFiniteNSelection.select_card_le Ω ι N (ℱ t) inferInstance (R.rule t) ω s

@[simp] theorem select_card (R : CausalFiniteNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) :
    (R.select t ω s).card = min N s.card :=
  @RandomFiniteNSelection.card_eq Ω ι N (ℱ t) inferInstance (R.rule t) ω s

theorem select_eq_self_of_card_le (R : CausalFiniteNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) (h : s.card ≤ N) :
    R.select t ω s = s :=
  @RandomFiniteNSelection.select_eq_self_of_card_le Ω ι N (ℱ t) inferInstance
    (R.rule t) ω s h

theorem measurable_select (R : CausalFiniteNSelection Time Ω ι N ℱ)
    (t : Time) (candidates : Ω → Finset ι)
    (hcandidates : @Measurable Ω (Finset ι) (ℱ t) inferInstance candidates) :
    @Measurable Ω (Finset ι) (ℱ t) inferInstance
      (fun ω => R.select t ω (candidates ω)) := by
  let _ : MeasurableSpace Ω := ℱ t
  simpa [select] using
    (@RandomFiniteNSelection.toRandomFiniteMechanism Ω ι N (ℱ t) inferInstance
      (R.rule t)).measurable_apply candidates hcandidates

/-- A deterministic `NSelection` is causal for every information domain. -/
def ofDeterministic (M : FiniteNSelection ι N) (hM : Measurable M.select) :
    CausalFiniteNSelection Time Ω ι N ℱ where
  rule t := @RandomFiniteNSelection.ofDeterministic Ω ι N (ℱ t) _ M hM

end CausalFiniteNSelection

end ProbabilityTheory.BranchingRandomWalk.Selection

end
