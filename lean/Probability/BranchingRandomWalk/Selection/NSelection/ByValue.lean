module

public import Combinatorics.BranchingWalk.Selection.NSelection.ByValue
public import Mathlib.MeasureTheory.MeasurableSpace.NCard
public import Probability.BranchingRandomWalk.Selection.Mechanism

/-!
# Measurability of dynamic value selection

The selected finite set is measurable once the candidate set is measurable
and every pairwise comparison of dynamic keys is an observable event.  This
keeps the result abstract in the ordered observation type: concrete real or
integer valued positions discharge the comparison hypothesis using their
usual measurable order.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection

open Combinatorics.Branching.Selection.NSelection

variable {Ω ι Value : Type*} [MeasurableSpace Ω]

namespace NSelection

/-- Selection from one fixed finite candidate set is measurable whenever all
pairwise key comparisons are measurable. No countability assumption is made
on the ambient label type. -/
theorem measurable_selectFirstNBy_fixed
    [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : Ω → ι → Value) (s : Finset ι)
    (hkey : ∀ p q : ι, Measurable fun ω =>
      valueKey (value ω) q < valueKey (value ω) p) :
    Measurable fun ω => selectFirstNBy N (value ω) s := by
  rw [measurable_finset_iff]
  intro p
  simp_rw [mem_selectFirstNBy_iff_card_lt]
  by_cases hp : p ∈ s
  · simp only [hp, true_and]
    have hcard : Measurable fun ω =>
        (s.filter fun q =>
          valueKey (value ω) q < valueKey (value ω) p).card := by
      have hsum : Measurable fun ω =>
          ∑ q ∈ s, if valueKey (value ω) q < valueKey (value ω) p
            then 1 else 0 := by
        apply Finset.measurable_sum
        intro q hq
        apply measurable_const.ite _ measurable_const
        simpa using (hkey p q) (measurableSet_singleton True)
      convert hsum using 1
      funext ω
      simp
    exact (measurable_of_countable (fun k : ℕ => k < N)).comp hcard
  · simp [hp]

/-- Dynamic selection is measurable when the random finite candidate set has
measurable fibres and countable actual range. The ambient label type itself
may be uncountable. -/
theorem measurable_selectFirstNBy
    [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : Ω → ι → Value) (candidates : Ω → Finset ι)
    (hcandidateFiber : ∀ s, MeasurableSet {ω | candidates ω = s})
    (hcandidateRange : (Set.range candidates).Countable)
    (hkey : ∀ p q : ι, Measurable fun ω =>
      valueKey (value ω) q < valueKey (value ω) p) :
    Measurable fun ω => selectFirstNBy N (value ω) (candidates ω) := by
  let S : Set (Finset ι) := Set.range candidates
  let _ : Countable S := Set.countable_coe_iff.mpr hcandidateRange
  rw [measurable_finset_iff]
  intro p
  have hpreimage :
      {ω | p ∈ selectFirstNBy N (value ω) (candidates ω)} =
        ⋃ s : S, {ω | candidates ω = s.1} ∩
          {ω | p ∈ selectFirstNBy N (value ω) s.1} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hω
      exact ⟨⟨candidates ω, Set.mem_range_self ω⟩, rfl, hω⟩
    · rintro ⟨s, hs, hp⟩
      simpa [hs] using hp
  apply measurableSet_setOfPred.mp
  rw [hpreimage]
  apply MeasurableSet.iUnion
  intro s
  apply (hcandidateFiber s.1).inter
  simpa using ((measurable_finset_mem p).comp
    (measurable_selectFirstNBy_fixed N value s.1 hkey))
      (measurableSet_singleton True)

/-- Convenience form when the whole label type is countable and the candidate
map is measurable. -/
theorem measurable_selectFirstNBy_of_countable
    [Countable ι] [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : Ω → ι → Value) (candidates : Ω → Finset ι)
    (hcandidates : Measurable candidates)
    (hkey : ∀ p q : ι, Measurable fun ω =>
      valueKey (value ω) q < valueKey (value ω) p) :
    Measurable fun ω => selectFirstNBy N (value ω) (candidates ω) := by
  apply measurable_selectFirstNBy N value candidates
  · exact fun s => hcandidates (measurableSet_singleton s)
  · exact Set.to_countable _
  · exact hkey

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
