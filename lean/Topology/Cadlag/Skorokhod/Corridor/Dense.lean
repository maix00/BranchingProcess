module

public import Topology.Cadlag.Skorokhod.Oscillation.Dense

/-!
# Strict corridors from rational coordinates

A positive uniform margin on rational times, including the terminal time,
extends to every time of a càdlàg path. The margin is essential: rational
pointwise strict inequalities alone do not control an unattained left limit.
-/

@[expose] public section

namespace Skorokhod

open Filter Set
open scoped Topology

/-- A closed spatial interval bound on a dense time set extends to all times
for a càdlàg path when the dense set contains the final time. -/
theorem closedCorridor_on_dense
    {T : Type*} [LinearOrder T] [TopologicalSpace T] [OrderTopology T]
    [DenselyOrdered T] [FirstCountableTopology T] [OrderTop T]
    {D : Set T} (hD : Dense D) (htop : ⊤ ∈ D)
    (path : T → ℝ) (hpath : IsCadlag path) {lower upper : ℝ}
    (hDpath : ∀ t ∈ D, lower ≤ path t ∧ path t ≤ upper) :
    ∀ t, lower ≤ path t ∧ path t ≤ upper := by
  intro t
  by_cases ht : t = ⊤
  · exact ht ▸ hDpath ⊤ htop
  · have httop : t < ⊤ := lt_of_le_of_ne le_top ht
    obtain ⟨u, _, huD, huTendsto⟩ :=
      hD.exists_seq_strictAnti_tendsto_of_lt httop
    have hwithin : Tendsto u atTop (𝓝[Set.Ioi t] t) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨huTendsto, Filter.Eventually.of_forall fun n => (huD n).1.1⟩
    have hvalue : Tendsto (fun n => path (u n)) atTop (𝓝 (path t)) :=
      (hpath.isRightContinuous t).tendsto.comp hwithin
    constructor
    · exact isClosed_Ici.mem_of_tendsto hvalue
        (Filter.Eventually.of_forall fun n => (hDpath (u n) (huD n).2).1)
    · exact isClosed_Iic.mem_of_tendsto hvalue
        (Filter.Eventually.of_forall fun n => (hDpath (u n) (huD n).2).2)

/-- A uniform rational-coordinate corridor, with an explicit positive
margin. -/
def rationalCorridorWithMargin (lower upper : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  {f | ∃ margin > 0, ∀ q : RationalunitInterval,
    lower + margin ≤ f (rationalunitIntervalCoe q) ∧
      f (rationalunitIntervalCoe q) ≤ upper - margin}

/-- Countable-coordinate strict corridor with a rational uniform margin. -/
def rationalCoordinateCorridorWithMargin (lower upper : ℝ) :
    Set (RationalunitInterval → ℝ) :=
  {x | ∃ margin : ℚ, 0 < (margin : ℝ) ∧
    ∀ q : RationalunitInterval,
      lower + margin ≤ x q ∧ x q ≤ upper - margin}

theorem measurableSet_rationalCoordinateCorridorWithMargin
    (lower upper : ℝ) :
    MeasurableSet (rationalCoordinateCorridorWithMargin lower upper) := by
  classical
  have hmargin (margin : ℚ) : MeasurableSet
      {x : RationalunitInterval → ℝ |
        ∀ q, lower + (margin : ℝ) ≤ x q ∧
          x q ≤ upper - (margin : ℝ)} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun q =>
      (measurableSet_le measurable_const (measurable_pi_apply q)).inter
        (measurableSet_le (measurable_pi_apply q) measurable_const)
  rw [show rationalCoordinateCorridorWithMargin lower upper =
      ⋃ margin : ℚ,
        if 0 < (margin : ℝ) then
          {x : RationalunitInterval → ℝ |
            ∀ q, lower + (margin : ℝ) ≤ x q ∧
              x q ≤ upper - (margin : ℝ)}
        else ∅ by
      ext x
      simp [rationalCoordinateCorridorWithMargin]]
  exact MeasurableSet.iUnion fun margin => by
    split_ifs
    · exact hmargin margin
    · exact MeasurableSet.empty

/-- A uniform rational corridor with a terminal endpoint window. -/
def rationalCoordinateCorridorReturnWithMargin
    (lower upper coreLower coreUpper : ℝ) :
    Set (RationalunitInterval → ℝ) :=
  rationalCoordinateCorridorWithMargin lower upper ∩
    {x | x ⊤ ∈ Set.Ioo coreLower coreUpper}

theorem measurableSet_rationalCoordinateCorridorReturnWithMargin
    (lower upper coreLower coreUpper : ℝ) :
    MeasurableSet (rationalCoordinateCorridorReturnWithMargin
      lower upper coreLower coreUpper) :=
  (measurableSet_rationalCoordinateCorridorWithMargin lower upper).inter
    (measurableSet_Ioo.preimage (measurable_pi_apply ⊤))

/-- Rational and full-path positive-margin corridor events coincide. -/
theorem rationalCorridorWithMargin_eq (lower upper : ℝ) :
    rationalCorridorWithMargin lower upper = rangeInOpenInterval lower upper := by
  have hD : Dense (Set.range rationalunitIntervalCoe) :=
    denseRange_rationalunitIntervalCoe
  have htop : (⊤ : unitInterval) ∈ Set.range rationalunitIntervalCoe := by
    refine ⟨⟨1, by norm_num⟩, ?_⟩
    apply Subtype.ext
    simp [rationalunitIntervalCoe]
  ext f
  constructor
  · rintro ⟨margin, hmargin, hbound⟩
    refine ⟨margin, hmargin, ?_⟩
    apply closedCorridor_on_dense hD htop f f.isCadlag_toFun
    intro t ht
    obtain ⟨q, rfl⟩ := ht
    exact hbound q
  · rintro ⟨margin, hmargin, hbound⟩
    exact ⟨margin, hmargin, fun q => hbound _⟩

/-- On càdlàg paths, the countable-coordinate event is exactly the full
strict corridor event. -/
theorem mem_rationalCoordinateCorridorWithMargin_iff
    (f : CadlagPath unitInterval ℝ) (lower upper : ℝ) :
    (fun q => f (rationalunitIntervalCoe q)) ∈
        rationalCoordinateCorridorWithMargin lower upper ↔
      f ∈ rangeInOpenInterval lower upper := by
  rw [← rationalCorridorWithMargin_eq]
  constructor
  · rintro ⟨margin, hmargin, hbound⟩
    exact ⟨(margin : ℝ), hmargin, hbound⟩
  · rintro ⟨margin, hmargin, hbound⟩
    obtain ⟨q, hq0, hqmargin⟩ := exists_rat_btwn hmargin
    refine ⟨q, hq0, ?_⟩
    intro t
    have ht := hbound t
    constructor <;> linarith

end Skorokhod

end
