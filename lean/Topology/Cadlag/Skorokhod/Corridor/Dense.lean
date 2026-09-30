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

end Skorokhod

end
