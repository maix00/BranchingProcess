/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.Random

/-!
# Causal selection mechanisms

Domain-flow adaptations of arbitrary-set selection rules.  Each rule is measurable
for exactly the information domain available at its time.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection

open Combinatorics.Branching.Selection

/-- A time-indexed arbitrary-set selection rule adapted to the domain flow. -/
structure CausalSelectMechanism (Time Ω ι : Type*)
    [MeasurableSpace ι] (ℱ : Time → MeasurableSpace Ω) where
  rule : ∀ t, @RandomSelectMechanism Ω ι (ℱ t) inferInstance

namespace CausalSelectMechanism

variable {Time Ω ι : Type*} [MeasurableSpace ι]
    {ℱ : Time → MeasurableSpace Ω}

def select (R : CausalSelectMechanism Time Ω ι ℱ)
    (t : Time) (ω : Ω) (s : Set ι) : Set ι :=
  @RandomSelectMechanism.select Ω ι (ℱ t) inferInstance (R.rule t) ω s

theorem select_subset (R : CausalSelectMechanism Time Ω ι ℱ)
    (t : Time) (ω : Ω) (s : Set ι) : R.select t ω s ⊆ s :=
  @RandomSelectMechanism.subset Ω ι (ℱ t) inferInstance (R.rule t) ω s

theorem measurable_select (R : CausalSelectMechanism Time Ω ι ℱ)
    (t : Time) (candidates : Ω → Set ι)
    (hcandidates : @Measurable Ω (Set ι) (ℱ t) inferInstance candidates) :
    @Measurable Ω (Set ι) (ℱ t) inferInstance
      (fun ω => R.select t ω (candidates ω)) := by
  let _ : MeasurableSpace Ω := ℱ t
  exact (R.rule t).measurable_apply candidates hcandidates

def ofDeterministic (M : Mechanism ι) (hM : Measurable M.select) :
    CausalSelectMechanism Time Ω ι ℱ where
  rule t := @RandomSelectMechanism.ofDeterministic Ω ι (ℱ t) _ M hM

end CausalSelectMechanism

/-- A time-indexed capacity selection on arbitrary candidate sets. -/
structure CausalNSelection (Time Ω ι : Type*) (N : ℕ)
    [MeasurableSpace ι] (ℱ : Time → MeasurableSpace Ω) where
  rule : ∀ t, @RandomNSelection Ω ι N (ℱ t) inferInstance

namespace CausalNSelection

variable {Time Ω ι : Type*} {N : ℕ} [MeasurableSpace ι]
    {ℱ : Time → MeasurableSpace Ω}

def select (R : CausalNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Set ι) : Finset ι :=
  @RandomNSelection.select Ω ι N (ℱ t) inferInstance (R.rule t) ω s

theorem select_subset (R : CausalNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Set ι) :
    ∀ q ∈ R.select t ω s, q ∈ s :=
  @RandomNSelection.subset Ω ι N (ℱ t) inferInstance (R.rule t) ω s

theorem select_card_le (R : CausalNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Set ι) : (R.select t ω s).card ≤ N :=
  @RandomNSelection.select_card_le Ω ι N (ℱ t) inferInstance
    (R.rule t) ω s

theorem measurable_select (R : CausalNSelection Time Ω ι N ℱ)
    (t : Time) (candidates : Ω → Set ι)
    (hcandidates : @Measurable Ω (Set ι) (ℱ t) inferInstance candidates) :
    @Measurable Ω (Finset ι) (ℱ t) inferInstance
      (fun ω => R.select t ω (candidates ω)) := by
  let _ : MeasurableSpace Ω := ℱ t
  exact (R.rule t).measurable_select.comp (measurable_id.prodMk hcandidates)

def ofDeterministic (M : NSelection ι N) (hM : Measurable M.select) :
    CausalNSelection Time Ω ι N ℱ where
  rule t := @RandomNSelection.ofDeterministic Ω ι N (ℱ t) _ M hM

end CausalNSelection

end ProbabilityTheory.BranchingRandomWalk.Selection

end
