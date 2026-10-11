/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.FiniteCausal
public import Probability.BranchingRandomWalk.Selection.NSelection.ByValue

/-!
# Value-based random finite selections

Measurable value rankings induce random finite selection rules. The
first-`N` comparison machinery is reused from the deterministic `NSelection`
API, while the resulting mechanisms stay in the general `Selection` layer.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection

open Combinatorics.Branching.Selection.NSelection

variable {Ω ι Value : Type*} [MeasurableSpace Ω]

namespace RandomFiniteNSelection

/-- The genuinely random dynamic leftmost rule.  Its ordering may depend on
the environment; observability is expressed by measurable pairwise key
comparisons. -/
noncomputable def leftmostBy
    [MeasurableSpace ι] [Countable ι] [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : Ω → ι → Value)
    (hkey : ∀ p q : ι, Measurable fun ω =>
      valueKey (value ω) q < valueKey (value ω) p) :
    RandomFiniteNSelection Ω ι N where
  select ω := selectFirstNBy N (value ω)
  subset ω := selectFirstNBy_subset N (value ω)
  measurable_select := by
    apply NSelection.measurable_selectFirstNBy_of_countable N
      (fun z p => value z.1 p) Prod.snd
      measurable_snd
    intro p q
    exact (hkey p q).comp measurable_fst
  card_eq ω := card_selectFirstNBy N (value ω)

@[simp] theorem leftmostBy_select
    [MeasurableSpace ι] [Countable ι] [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : Ω → ι → Value)
    (hkey : ∀ p q : ι, Measurable fun ω =>
      valueKey (value ω) q < valueKey (value ω) p)
    (ω : Ω) (s : Finset ι) :
    (leftmostBy N value hkey).select ω s =
      selectFirstNBy N (value ω) s :=
  rfl

end RandomFiniteNSelection

namespace CausalFiniteNSelection

/-- Time-dependent dynamic leftmost selection is causal when its pairwise
spatial comparisons are observable in the domain available at each time. -/
noncomputable def leftmostBy
    [MeasurableSpace ι] [Countable ι] [LinearOrder ι] [LinearOrder Value]
    {Time : Type*} {ℱ : Time → MeasurableSpace Ω}
    (N : ℕ) (value : Time → Ω → ι → Value)
    (hkey : ∀ t p q, @Measurable Ω Prop (ℱ t) inferInstance fun ω =>
      valueKey (value t ω) q < valueKey (value t ω) p) :
    CausalFiniteNSelection Time Ω ι N ℱ where
  rule t := @RandomFiniteNSelection.leftmostBy Ω ι Value (ℱ t) _ _ _ _
    N (value t) (hkey t)

/-- Causal dynamic leftmost selection constructed directly from measurable
particle values.  This is the interface used by a position process after
composition with its ordered observation `Position → Value`. -/
noncomputable def leftmostByOfMeasurableValue
    [MeasurableSpace ι] [Countable ι] [LinearOrder ι]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [LinearOrder Value]
    [SecondCountableTopology Value] [OrderClosedTopology Value]
    [MeasurableEq Value]
    {Time : Type*} {ℱ : Time → MeasurableSpace Ω}
    (N : ℕ) (value : Time → Ω → ι → Value)
    (hvalue : ∀ t p, @Measurable Ω Value (ℱ t) inferInstance
      fun ω => value t ω p) :
    CausalFiniteNSelection Time Ω ι N ℱ :=
  leftmostBy N value fun t p q =>
    @NSelection.measurable_valueKey_lt Ω ι Value (ℱ t) _ _ _ _ _ _ _ _
      (value t) (hvalue t) p q

omit [MeasurableSpace Ω] in
@[simp] theorem leftmostBy_select
    [MeasurableSpace ι] [Countable ι] [LinearOrder ι] [LinearOrder Value]
    {Time : Type*} {ℱ : Time → MeasurableSpace Ω}
    (N : ℕ) (value : Time → Ω → ι → Value)
    (hkey : ∀ t p q, @Measurable Ω Prop (ℱ t) inferInstance fun ω =>
      valueKey (value t ω) q < valueKey (value t ω) p)
    (t : Time) (ω : Ω) (s : Finset ι) :
    (leftmostBy N value hkey).select t ω s =
      selectFirstNBy N (value t ω) s :=
  rfl

omit [MeasurableSpace Ω] in
@[simp] theorem leftmostByOfMeasurableValue_select
    [MeasurableSpace ι] [Countable ι] [LinearOrder ι]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [LinearOrder Value]
    [SecondCountableTopology Value] [OrderClosedTopology Value]
    [MeasurableEq Value]
    {Time : Type*} {ℱ : Time → MeasurableSpace Ω}
    (N : ℕ) (value : Time → Ω → ι → Value)
    (hvalue : ∀ t p, @Measurable Ω Value (ℱ t) inferInstance
      fun ω => value t ω p)
    (t : Time) (ω : Ω) (s : Finset ι) :
    (leftmostByOfMeasurableValue N value hvalue).select t ω s =
      selectFirstNBy N (value t ω) s :=
  rfl

end CausalFiniteNSelection


end ProbabilityTheory.BranchingRandomWalk.Selection
