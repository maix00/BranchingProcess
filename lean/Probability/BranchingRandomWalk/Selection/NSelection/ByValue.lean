import Combinatorics.BranchingWalk.Selection.NSelection.ByValue
import Mathlib.MeasureTheory.MeasurableSpace.NCard
import Probability.BranchingRandomWalk.Selection.Mechanism

/-!
# Measurability of dynamic value selection

The selected finite set is measurable once the candidate set is measurable
and every pairwise comparison of dynamic keys is an observable event.  This
keeps the result abstract in the ordered observation type: concrete real or
integer valued positions discharge the comparison hypothesis using their
usual measurable order.
-/

namespace ProbabilityTheory.BranchingRandomWalk.Selection

open Combinatorics.Branching.Selection.NSelection

variable {Ω ι Value : Type*} [MeasurableSpace Ω]

namespace NSelection

/-- Dynamic leftmost selection of a random finite candidate population is
measurable.  Countability is required only for the particle-label space used
to encode finite sets, not by the deterministic selection theorem. -/
theorem measurable_selectFirstNBy
    [Countable ι] [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : Ω → ι → Value) (candidates : Ω → Finset ι)
    (hcandidates : Measurable candidates)
    (hkey : ∀ p q : ι, Measurable fun ω =>
      valueKey (value ω) q < valueKey (value ω) p) :
    Measurable fun ω => selectFirstNBy N (value ω) (candidates ω) := by
  rw [measurable_finset_iff]
  intro p
  simp_rw [mem_selectFirstNBy_iff_card_lt]
  apply (measurable_finset_mem p).comp hcandidates |>.and
  let below : Ω → Set ι := fun ω =>
    {q | q ∈ candidates ω ∧
      valueKey (value ω) q < valueKey (value ω) p}
  have hbelow : Measurable below := by
    rw [measurable_set_iff]
    intro q
    exact ((measurable_finset_mem q).comp hcandidates).and (hkey p q)
  have hncard : Measurable fun ω => (below ω).ncard :=
    measurable_ncard.comp hbelow
  have heq : ∀ ω,
      ((candidates ω).filter fun q =>
        valueKey (value ω) q < valueKey (value ω) p).card =
        (below ω).ncard := by
    intro ω
    rw [← Set.ncard_coe_finset]
    congr 1
    ext q
    simp [below]
  have hcard : Measurable fun ω =>
      ((candidates ω).filter fun q =>
        valueKey (value ω) q < valueKey (value ω) p).card := by
    convert hncard using 1
    funext ω
    exact heq ω
  exact (measurable_of_countable (fun k : ℕ => k < N)).comp hcard

/-- Measurable particle values have measurable lexicographic comparison keys.
The value is compared first; the label order only resolves equal values. -/
theorem measurable_valueKey_lt
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [LinearOrder Value]
    [SecondCountableTopology Value] [OrderClosedTopology Value]
    [MeasurableEq Value] [LinearOrder ι]
    (value : Ω → ι → Value)
    (hvalue : ∀ p, Measurable fun ω => value ω p)
    (p q : ι) :
    Measurable fun ω => valueKey (value ω) q < valueKey (value ω) p := by
  have hq := hvalue q
  have hp := hvalue p
  simpa [valueKey, Prod.Lex.lt_iff] using
    (hq.lt hp).or ((hq.eq hp).and (measurable_const : Measurable fun _ : Ω => q < p))

end NSelection namespace RandomFiniteNSelection

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
    apply NSelection.measurable_selectFirstNBy N (fun z p => value z.1 p) Prod.snd
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
