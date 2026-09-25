import ThesisSpeed.Probability.PointProcess.Representation
import Mathlib.Data.EReal.Basic

/-!
# Canonical enumeration directly from a counting measure

The `n`th location is defined from the cumulative counting function
`R ↦ ν (-∞, R]`. Rational thresholds make the construction countable and
therefore measurable in the Giry measurable space of measures. Multiplicity
is retained because ranks use the inequalities `n + 1 ≤ ν (-∞, R]`.
-/

open MeasureTheory
open scoped ENNReal

namespace ThesisSpeed

/-- A rational candidate upper bound for the atom of rank `n`. -/
noncomputable def rankedAtomCandidate (n : ℕ) (q : ℚ)
    (ν : Measure ℝ) : EReal :=
  if (n + 1 : ENNReal) ≤ ν (Set.Iic (q : ℝ)) then
    ((q : ℝ) : EReal)
  else ⊤

theorem rankedAtomCandidate_measurable (n : ℕ) (q : ℚ) :
    Measurable (rankedAtomCandidate n q) := by
  unfold rankedAtomCandidate
  have hcount : Measurable (fun ν : Measure ℝ => ν (Set.Iic (q : ℝ))) :=
    Measure.measurable_coe measurableSet_Iic
  have hset : MeasurableSet
      {ν : Measure ℝ | (n + 1 : ENNReal) ≤ ν (Set.Iic (q : ℝ))} :=
    measurableSet_le measurable_const hcount
  exact measurable_const.ite hset measurable_const

/-- Extended-real rank location. It is `⊤` when the measure has at most `n`
atoms in total. -/
noncomputable def rankedAtomEReal (n : ℕ) (ν : Measure ℝ) : EReal :=
  ⨅ q : ℚ, rankedAtomCandidate n q ν

theorem rankedAtomEReal_measurable (n : ℕ) :
    Measurable (rankedAtomEReal n) := by
  unfold rankedAtomEReal
  exact Measurable.iInf (rankedAtomCandidate_measurable n)

/-- Real-valued displacement used in the optional slot. Its value is
irrelevant when the corresponding presence flag is nonpositive. -/
noncomputable def rankedAtom (n : ℕ) (ν : Measure ℝ) : ℝ :=
  (rankedAtomEReal n ν).toReal

theorem rankedAtom_measurable (n : ℕ) :
    Measurable (rankedAtom n) :=
  (rankedAtomEReal_measurable n).ereal_toReal

/-- Whether the counting measure contains an atom of rank `n`. -/
def rankedAtomPresent (n : ℕ) (ν : Measure ℝ) : Prop :=
  (n + 1 : ENNReal) ≤ ν Set.univ

theorem measurableSet_rankedAtomPresent (n : ℕ) :
    MeasurableSet {ν : Measure ℝ | rankedAtomPresent n ν} := by
  exact measurableSet_le measurable_const
    (Measure.measurable_coe MeasurableSet.univ)

/-- Canonical optional-slot mark extracted from a measure. -/
noncomputable def measureToOffspringMark (ν : Measure ℝ) : OffspringMark :=
  by
    classical
    exact fun n =>
      (if rankedAtomPresent n ν then 1 else 0, rankedAtom n ν)

theorem measureToOffspringMark_measurable :
    Measurable measureToOffspringMark := by
  rw [measurable_pi_iff]
  intro n
  apply Measurable.prodMk
  · exact measurable_const.ite
      (measurableSet_rankedAtomPresent n) measurable_const
  · exact rankedAtom_measurable n

theorem measureToOffspringMark_childPresent (ν : Measure ℝ) (n : ℕ) :
    measureToOffspringMark ν ∈ childPresent n ↔ rankedAtomPresent n ν := by
  classical
  by_cases h : rankedAtomPresent n ν <;>
    simp [measureToOffspringMark, childPresent, h]

theorem rankedAtomPresent_mono {ν : Measure ℝ} {i j : ℕ}
    (hij : i ≤ j) (hj : rankedAtomPresent j ν) :
    rankedAtomPresent i ν := by
  unfold rankedAtomPresent at *
  have hcast : (i + 1 : ENNReal) ≤ (j + 1 : ENNReal) := by
    exact_mod_cast Nat.succ_le_succ hij
  exact hcast.trans hj

theorem measureToOffspringMark_slotsInitial (ν : Measure ℝ) :
    measureToOffspringMark ν ∈ optionalSlotsInitial := by
  intro i hi
  rw [measureToOffspringMark_childPresent] at hi ⊢
  exact rankedAtomPresent_mono (Nat.le_succ i) hi

theorem rankedAtomCandidate_mono (ν : Measure ℝ) (n : ℕ) (q : ℚ) :
    rankedAtomCandidate n q ν ≤ rankedAtomCandidate (n + 1) q ν := by
  classical
  by_cases hhigh : (n + 1 + 1 : ENNReal) ≤ ν (Set.Iic (q : ℝ))
  · have hcast : (n + 1 : ENNReal) ≤ (n + 1 + 1 : ENNReal) := by
      exact_mod_cast (by omega : n + 1 ≤ n + 1 + 1)
    have hlow := hcast.trans hhigh
    simp [rankedAtomCandidate, hhigh, hlow]
  · simp [rankedAtomCandidate, hhigh]

theorem rankedAtomEReal_mono (ν : Measure ℝ) (n : ℕ) :
    rankedAtomEReal n ν ≤ rankedAtomEReal (n + 1) ν := by
  unfold rankedAtomEReal
  exact iInf_mono (fun q => rankedAtomCandidate_mono ν n q)

private theorem counting_value_nat {ν : Measure ℝ}
    (hcount : IsCountingMeasure ν) (hlocal : IsLeftLocallyFinite ν)
    (R : ℝ) : ∃ k : ℕ, ν (Set.Iic R) = k := by
  rcases hcount (Set.Iic R) measurableSet_Iic with htop | hnat
  · exact False.elim (hlocal R htop)
  · exact hnat

/-- If rank `n` exists, some rational left half-line already contains at
least `n+1` atoms. Integer-valuedness is essential at this step. -/
theorem exists_rational_rank_bound {ν : Measure ℝ}
    (hcount : IsCountingMeasure ν) (hlocal : IsLeftLocallyFinite ν)
    (n : ℕ) (hpresent : rankedAtomPresent n ν) :
    ∃ q : ℚ, (n + 1 : ENNReal) ≤ ν (Set.Iic (q : ℝ)) := by
  by_contra hnone
  push Not at hnone
  let s : Set ℝ := Set.range (fun q : ℚ => (q : ℝ))
  have hsc : s.Countable := Set.countable_range _
  have hcofinal : ∀ x : ℝ, ∃ y ∈ s, x ≤ y := by
    intro x
    obtain ⟨q, hq⟩ := exists_rat_gt x
    exact ⟨(q : ℝ), ⟨q, rfl⟩, hq.le⟩
  have hdir : DirectedOn (· ≤ ·) s := by
    rintro x ⟨qx, rfl⟩ y ⟨qy, rfl⟩
    refine ⟨((max qx qy : ℚ) : ℝ), ⟨max qx qy, rfl⟩, ?_, ?_⟩
    · exact Rat.cast_le.mpr (le_max_left qx qy)
    · exact Rat.cast_le.mpr (le_max_right qx qy)
  have hbound : ∀ x ∈ s, ν (Set.Iic x) ≤ (n : ENNReal) := by
    rintro x ⟨q, rfl⟩
    obtain ⟨k, hk⟩ := counting_value_nat hcount hlocal (q : ℝ)
    rw [hk]
    have hkn : k ≤ n := by
      by_contra hnk
      have hsucc : n + 1 ≤ k := by omega
      have hcast : (n + 1 : ENNReal) ≤ (k : ENNReal) := by
        exact_mod_cast hsucc
      exact (not_le_of_gt (hnone q)) (by simpa [hk] using hcast)
    exact_mod_cast hkn
  have htotal : ν Set.univ ≤ (n : ENNReal) := by
    rw [← biSup_measure_Iic hsc hcofinal hdir]
    exact iSup₂_le hbound
  have hstrict : (n : ENNReal) < (n + 1 : ENNReal) := by
    exact_mod_cast (Nat.lt_succ_self n)
  exact (not_lt_of_ge (hpresent.trans htotal)) hstrict

theorem rankedAtomEReal_ne_top {ν : Measure ℝ}
    (hcount : IsCountingMeasure ν) (hlocal : IsLeftLocallyFinite ν)
    (n : ℕ) (hpresent : rankedAtomPresent n ν) :
    rankedAtomEReal n ν ≠ ⊤ := by
  obtain ⟨q, hq⟩ := exists_rational_rank_bound hcount hlocal n hpresent
  have hcand : rankedAtomCandidate n q ν = ((q : ℝ) : EReal) := by
    simp [rankedAtomCandidate, hq]
  have hle : rankedAtomEReal n ν ≤ ((q : ℝ) : EReal) := by
    unfold rankedAtomEReal
    exact (iInf_le (fun r : ℚ => rankedAtomCandidate n r ν) q).trans_eq hcand
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hle

/-- Applying the canonical enumeration to a measurable random measure remains
measurable. -/
theorem measureToOffspringMark_comp_measurable
    {Ω : Type*} [MeasurableSpace Ω] (Ξ : OffspringPointProcess Ω) :
    Measurable (fun ω => measureToOffspringMark (Ξ ω)) :=
  measureToOffspringMark_measurable.comp Ξ.measurable_toMeasure

end ThesisSpeed
