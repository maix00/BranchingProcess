import Probability.BranchingRandomWalk.PointProcess.Representation.RankedAtomLocation
import MeasureTheory.BranchingWalk.Ordered

/-!
# Order and nonemptiness of the canonical ranked slots

An increasing counting measure gives an increasing ranked slot sequence, the
rank/CDF equivalence characterizes presence, and the reconstructed slot is
present exactly when present atoms remain.
-/

open MeasureTheory
open Filter
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingWalk MeasureTheory

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

/-- The canonical rank is below `R` exactly when the cumulative counting
measure contains at least `n+1` atoms. -/
theorem rankedAtom_present_and_le_iff {ν : Measure ℝ}
    (hcount : IsCountingMeasure ν) (hlocal : IsLeftLocallyFinite ν)
    (n : ℕ) (R : ℝ) :
    rankedAtomPresent n ν ∧ rankedAtom n ν ≤ R ↔
      (n + 1 : ENNReal) ≤ ν (Set.Iic R) := by
  constructor
  · rintro ⟨hpresent, hrank⟩
    by_contra hnot
    obtain ⟨q, hRq, hsame⟩ :=
      exists_rational_right_same_Iic hcount hlocal R
    have hqnot : ¬(n + 1 : ENNReal) ≤ ν (Set.Iic (q : ℝ)) := by
      rwa [hsame]
    have hlower : ((q : ℝ) : EReal) ≤ rankedAtomEReal n ν := by
      unfold rankedAtomEReal
      apply le_iInf
      intro r
      unfold rankedAtomCandidate
      split_ifs with hr
      · have hnotrq : ¬r ≤ q := by
          intro hrq
          have hmono : ν (Set.Iic (r : ℝ)) ≤ ν (Set.Iic (q : ℝ)) :=
            measure_mono (Set.Iic_subset_Iic.mpr (Rat.cast_le.mpr hrq))
          exact hqnot (hr.trans hmono)
        exact_mod_cast (le_of_not_ge hnotrq)
      · exact le_top
    have htop := rankedAtomEReal_ne_top hcount hlocal n hpresent
    have hbot := rankedAtomEReal_ne_bot hcount hlocal n
    have hqrank : (q : ℝ) ≤ rankedAtom n ν := by
      have hcoe : ((rankedAtom n ν : ℝ) : EReal) =
          rankedAtomEReal n ν := EReal.coe_toReal htop hbot
      rw [← hcoe] at hlower
      exact_mod_cast hlower
    exact (not_lt_of_ge (hqrank.trans hrank)) hRq
  · intro hcountR
    have hpresent : rankedAtomPresent n ν :=
      hcountR.trans (measure_mono (Set.subset_univ _))
    refine ⟨hpresent, ?_⟩
    by_contra hnot
    have hRrank : R < rankedAtom n ν := lt_of_not_ge hnot
    obtain ⟨q, hRq, hqrank⟩ := exists_rat_btwn hRrank
    have hcountq : (n + 1 : ENNReal) ≤ ν (Set.Iic (q : ℝ)) :=
      hcountR.trans (measure_mono (Set.Iic_subset_Iic.mpr hRq.le))
    have hcand : rankedAtomCandidate n q ν = ((q : ℝ) : EReal) := by
      simp [rankedAtomCandidate, hcountq]
    have hinf : rankedAtomEReal n ν ≤ ((q : ℝ) : EReal) := by
      exact (iInf_le (fun r : ℚ => rankedAtomCandidate n r ν) q).trans_eq hcand
    have htop := rankedAtomEReal_ne_top hcount hlocal n hpresent
    have hbot := rankedAtomEReal_ne_bot hcount hlocal n
    have hrankq : rankedAtom n ν ≤ (q : ℝ) := by
      have hcoe : ((rankedAtom n ν : ℝ) : EReal) =
          rankedAtomEReal n ν := EReal.coe_toReal htop hbot
      rw [← hcoe] at hinf
      exact_mod_cast hinf
    exact (not_lt_of_ge hrankq) hqrank

theorem measureToStep_ordered (ν : Measure ℝ)
    (hcount : IsCountingMeasure ν) (hlocal : IsLeftLocallyFinite ν) :
    measureToStep ν ∈ orderedSteps := by
  refine ⟨measureToStep_presencePrefix ν, ?_⟩
  intro i j x y hij hx hy
  have hpres_j : present (measureToStep ν) j := ⟨y, hy⟩
  have hrank_j : rankedAtomPresent j ν :=
    (measureToStep_present ν j).1 hpres_j
  have hle : rankedAtom i ν ≤ rankedAtom j ν :=
    rankedAtom_le_of_le_of_present hcount hlocal (le_of_lt hij) hrank_j
  rw [measureToStep_eq_some ν hx,
    measureToStep_eq_some ν hy]
  exact hle

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

theorem measureToStep_nonempty_iff (ν : Measure ℝ)
    (hcount : IsCountingMeasure ν) :
    measureToStep ν ∈ nonemptySupport ↔ ν ≠ 0 := by
  constructor
  · rintro ⟨i, hi⟩
    rw [measureToStep_present] at hi
    exact (rankedAtomPresent_zero_iff_ne_zero ν hcount).1
      (rankedAtomPresent_mono (Nat.zero_le i) hi)
  · intro hne
    exact ⟨0, (measureToStep_present ν 0).2
      ((rankedAtomPresent_zero_iff_ne_zero ν hcount).2 hne)⟩

end ProbabilityTheory.BranchingRandomWalk
