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
open Filter
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

/-- Left local finiteness and integer-valuedness force the cumulative count
to vanish sufficiently far to the left. -/
theorem exists_rational_Iic_measure_zero {ν : Measure ℝ}
    (hcount : IsCountingMeasure ν) (hlocal : IsLeftLocallyFinite ν) :
    ∃ q : ℚ, ν (Set.Iic (q : ℝ)) = 0 := by
  let s : ℕ → Set ℝ := fun n => Set.Iic (-(n : ℝ))
  have hs : ∀ n, NullMeasurableSet (s n) ν := fun _ =>
    measurableSet_Iic.nullMeasurableSet
  have hanti : Antitone s := by
    intro i j hij
    exact Set.Iic_subset_Iic.mpr (by
      have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      linarith)
  have hinter : ⋂ n, s n = (∅ : Set ℝ) := by
    ext x
    constructor
    · intro hall
      obtain ⟨n, hn⟩ := exists_nat_gt (-x)
      have hnreal : -x < (n : ℝ) := by exact_mod_cast hn
      have hn' : -(n : ℝ) < x := by linarith
      have halln : x ∈ s n := Set.mem_iInter.mp hall n
      change x ≤ -(n : ℝ) at halln
      exact False.elim ((not_le_of_gt hn') halln)
    · simp
  have hfinite : ∃ n, ν (s n) ≠ ∞ := by
    refine ⟨0, ?_⟩
    simpa [s] using hlocal 0
  have htend : Tendsto (fun n => ν (s n)) atTop (nhds 0) := by
    have h := tendsto_measure_iInter_atTop hs hanti hfinite
    simpa [Function.comp_def, hinter] using h
  have hevent : ∀ᶠ n in atTop, ν (s n) < 1 :=
    (tendsto_order.1 htend).2 1 (by norm_num)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hevent)
  obtain ⟨k, hk⟩ := counting_value_nat hcount hlocal (-(N : ℝ))
  have hklt : (k : ENNReal) < 1 := by
    rw [← hk]
    exact hN N le_rfl
  have hkzero : k = 0 := by
    have : k < 1 := by exact_mod_cast hklt
    omega
  refine ⟨-(N : ℚ), ?_⟩
  convert hk using 1 <;> simp [hkzero]

theorem rankedAtomEReal_ne_bot {ν : Measure ℝ}
    (hcount : IsCountingMeasure ν) (hlocal : IsLeftLocallyFinite ν)
    (n : ℕ) : rankedAtomEReal n ν ≠ ⊥ := by
  obtain ⟨q₀, hq₀⟩ := exists_rational_Iic_measure_zero hcount hlocal
  have hlower : ((q₀ : ℝ) : EReal) ≤ rankedAtomEReal n ν := by
    unfold rankedAtomEReal
    apply le_iInf
    intro q
    unfold rankedAtomCandidate
    split_ifs with hq
    · have hnot : ¬q ≤ q₀ := by
        intro hle
        have hsubset : Set.Iic (q : ℝ) ⊆ Set.Iic (q₀ : ℝ) :=
          Set.Iic_subset_Iic.mpr (Rat.cast_le.mpr hle)
        have hzero : ν (Set.Iic (q : ℝ)) = 0 :=
          measure_mono_null hsubset hq₀
        rw [hzero] at hq
        simp at hq
      exact_mod_cast (le_of_not_ge hnot)
    · exact le_top
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlower

theorem rankedAtom_mono_of_present {ν : Measure ℝ}
    (hcount : IsCountingMeasure ν) (hlocal : IsLeftLocallyFinite ν)
    (n : ℕ) (hpresent : rankedAtomPresent (n + 1) ν) :
    rankedAtom n ν ≤ rankedAtom (n + 1) ν := by
  apply EReal.toReal_le_toReal (rankedAtomEReal_mono ν n)
  · exact rankedAtomEReal_ne_bot hcount hlocal n
  · exact rankedAtomEReal_ne_top hcount hlocal (n + 1) hpresent

theorem rankedAtom_le_of_le_of_present {ν : Measure ℝ}
    (hcount : IsCountingMeasure ν) (hlocal : IsLeftLocallyFinite ν)
    {i j : ℕ} (hij : i ≤ j) (hpresent : rankedAtomPresent j ν) :
    rankedAtom i ν ≤ rankedAtom j ν := by
  induction j with
  | zero =>
      have : i = 0 := Nat.eq_zero_of_le_zero hij
      subst i
      exact le_rfl
  | succ j ih =>
      by_cases heq : i = j + 1
      · subst i
        exact le_rfl
      · have hij' : i ≤ j := by omega
        have hpj : rankedAtomPresent j ν :=
          rankedAtomPresent_mono (Nat.le_succ j) hpresent
        exact (ih hij' hpj).trans
          (rankedAtom_mono_of_present hcount hlocal j hpresent)

theorem measureToOffspringMark_ordered (ν : Measure ℝ)
    (hcount : IsCountingMeasure ν) (hlocal : IsLeftLocallyFinite ν) :
    measureToOffspringMark ν ∈ orderedOffspring := by
  refine ⟨⟨?_, measureToOffspringMark_slotsInitial ν⟩, ?_⟩
  · intro i hi
    rw [measureToOffspringMark_childPresent] at hi
    have hzero : rankedAtomPresent 0 ν :=
      rankedAtomPresent_mono (Nat.zero_le i) hi
    constructor
    · exact (measureToOffspringMark_childPresent ν 0).2 hzero
    · change rankedAtom 0 ν ≤ rankedAtom i ν
      exact rankedAtom_le_of_le_of_present hcount hlocal
        (Nat.zero_le i) hi
  · intro i hi
    rw [measureToOffspringMark_childPresent] at hi
    change rankedAtom i ν ≤ rankedAtom (i + 1) ν
    exact rankedAtom_mono_of_present hcount hlocal i hi

theorem rankedAtomPresent_zero_iff_ne_zero (ν : Measure ℝ)
    (hcount : IsCountingMeasure ν) :
    rankedAtomPresent 0 ν ↔ ν ≠ 0 := by
  rw [← Measure.measure_univ_pos]
  unfold rankedAtomPresent
  constructor
  · intro h
    exact lt_of_lt_of_le (by norm_num) h
  · intro hpos
    rcases hcount Set.univ MeasurableSet.univ with htop | ⟨k, hk⟩
    · rw [htop]
      exact le_top
    · rw [hk] at hpos ⊢
      have hkpos : 0 < k := by exact_mod_cast hpos
      have : 1 ≤ k := hkpos
      exact_mod_cast this

theorem measureToOffspringMark_nonempty_iff (ν : Measure ℝ)
    (hcount : IsCountingMeasure ν) :
    measureToOffspringMark ν ∈ offspringNonempty ↔ ν ≠ 0 := by
  constructor
  · rintro ⟨i, hi⟩
    rw [measureToOffspringMark_childPresent] at hi
    exact (rankedAtomPresent_zero_iff_ne_zero ν hcount).1
      (rankedAtomPresent_mono (Nat.zero_le i) hi)
  · intro hne
    exact ⟨0, (measureToOffspringMark_childPresent ν 0).2
      ((rankedAtomPresent_zero_iff_ne_zero ν hcount).2 hne)⟩

/-- The canonical measurable ordered mark attached to an abstract offspring
point process. The remaining reconstruction theorem identifies its Dirac sum
with the original measure. -/
noncomputable def canonicalOffspringMark
    {Ω : Type*} [MeasurableSpace Ω] (Ξ : OffspringPointProcess Ω) :
    Ω → OffspringMark :=
  fun ω => measureToOffspringMark (Ξ ω)

theorem canonicalOffspringMark_measurable
    {Ω : Type*} [MeasurableSpace Ω] (Ξ : OffspringPointProcess Ω) :
    Measurable (canonicalOffspringMark Ξ) :=
  measureToOffspringMark_measurable.comp Ξ.measurable_toMeasure

theorem canonicalOffspringMark_ordered
    {Ω : Type*} [MeasurableSpace Ω] (Ξ : OffspringPointProcess Ω)
    (ω : Ω) : canonicalOffspringMark Ξ ω ∈ orderedOffspring :=
  measureToOffspringMark_ordered (Ξ ω) (Ξ.counting ω)
    (Ξ.leftLocallyFinite ω)

theorem canonicalOffspringMark_nonempty_iff
    {Ω : Type*} [MeasurableSpace Ω] (Ξ : OffspringPointProcess Ω)
    (ω : Ω) :
    canonicalOffspringMark Ξ ω ∈ offspringNonempty ↔ Ξ ω ≠ 0 :=
  measureToOffspringMark_nonempty_iff (Ξ ω) (Ξ.counting ω)

/-- Cumulative mass of the reconstructed Dirac sum is the number of present
ranks whose canonical location is at most `R`. This reduces reconstruction to
the rank/CDF equivalence. -/
noncomputable def rankedIicCountTerm (ν : Measure ℝ) (R : ℝ)
    (n : ℕ) : ENNReal := by
  classical
  exact if rankedAtomPresent n ν ∧ rankedAtom n ν ≤ R then 1 else 0

theorem offspringPointMeasure_measureToOffspringMark_Iic
    (ν : Measure ℝ) (R : ℝ) :
    offspringPointMeasure (measureToOffspringMark ν) (Set.Iic R) =
      ∑' n : ℕ, rankedIicCountTerm ν R n := by
  rw [offspringPointMeasure_apply _ _ measurableSet_Iic]
  congr 1
  funext n
  classical
  by_cases hp : rankedAtomPresent n ν <;>
    by_cases hr : rankedAtom n ν ≤ R <;>
      simp [measureToOffspringMark_childPresent, childRealized,
        childDisplacement, measureToOffspringMark, rankedIicCountTerm,
        hp, hr]

/-- Applying the canonical enumeration to a measurable random measure remains
measurable. -/
theorem measureToOffspringMark_comp_measurable
    {Ω : Type*} [MeasurableSpace Ω] (Ξ : OffspringPointProcess Ω) :
    Measurable (fun ω => measureToOffspringMark (Ξ ω)) :=
  measureToOffspringMark_measurable.comp Ξ.measurable_toMeasure

end ThesisSpeed
