import Probability.BranchingRandomWalk.PointProcess.Representation.RankedAtom

/-!
# Rank location of a counting measure

Monotonicity of the rational candidate bounds and the location lemmas that
make each rank a genuine extended-real supremum: local finiteness and
integer-valuedness supply the rational thresholds below and above each rank.
-/

open MeasureTheory
open Filter
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingWalk MeasureTheory

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

/-- An integer-valued measure that is finite on left half-lines takes natural
number values there. Shared with the reconstruction module. -/
theorem counting_value_nat {ν : Measure ℝ}
    (hcount : IsCountingMeasure ν) (hlocal : IsLeftLocallyFinite ν)
    (R : ℝ) : ∃ k : ℕ, ν (Set.Iic R) = k := by
  rcases hcount (Set.Iic R) measurableSet_Iic with htop | hnat
  · exact False.elim (hlocal.apply R htop)
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
    simpa [s] using hlocal.apply 0
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

/-- Integer-valued local finiteness makes the cumulative count locally
constant immediately to the right of every threshold. -/
theorem exists_rational_right_same_Iic {ν : Measure ℝ}
    (hcount : IsCountingMeasure ν) (hlocal : IsLeftLocallyFinite ν)
    (R : ℝ) :
    ∃ q : ℚ, R < (q : ℝ) ∧ ν (Set.Iic (q : ℝ)) = ν (Set.Iic R) := by
  obtain ⟨k, hk⟩ := counting_value_nat hcount hlocal R
  let b : ℕ → ℝ := fun n => R + 1 / ((n : ℝ) + 1)
  let s : ℕ → Set ℝ := fun n => Set.Iic (b n)
  have hbpos : ∀ n, R < b n := by
    intro n
    simp only [b, lt_add_iff_pos_right]
    positivity
  have hanti : Antitone s := by
    intro i j hij
    apply Set.Iic_subset_Iic.mpr
    change R + 1 / ((j : ℝ) + 1) ≤ R + 1 / ((i : ℝ) + 1)
    gcongr
  have hinter : ⋂ n, s n = Set.Iic R := by
    ext x
    constructor
    · intro hall
      change x ≤ R
      by_contra hx
      have hRx : 0 < x - R := sub_pos.mpr (lt_of_not_ge hx)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hRx
      have halln : x ∈ s n := Set.mem_iInter.mp hall n
      change x ≤ R + 1 / ((n : ℝ) + 1) at halln
      linarith
    · intro hx
      apply Set.mem_iInter.mpr
      intro n
      exact (Set.mem_Iic.mp hx).trans (hbpos n).le
  have hs : ∀ n, NullMeasurableSet (s n) ν := fun _ =>
    measurableSet_Iic.nullMeasurableSet
  have hfinite : ∃ n, ν (s n) ≠ ∞ := by
    exact ⟨0, hlocal.apply (b 0)⟩
  have htend : Tendsto (fun n => ν (s n)) atTop
      (nhds (ν (Set.Iic R))) := by
    have h := tendsto_measure_iInter_atTop hs hanti hfinite
    simpa [Function.comp_def, hinter] using h
  have hevent : ∀ᶠ n in atTop, ν (s n) < (k + 1 : ℕ) := by
    have hlim : Tendsto (fun n => ν (s n)) atTop (nhds (k : ENNReal)) := by
      simpa [hk] using htend
    have h := (tendsto_order.1 hlim).2 ((k : ENNReal) + 1) (by
      exact_mod_cast Nat.lt_succ_self k)
    simpa using h
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  obtain ⟨l, hl⟩ := counting_value_nat hcount hlocal (b N)
  have hkl : k ≤ l := by
    have hmono : ν (Set.Iic R) ≤ ν (s N) :=
      measure_mono (Set.Iic_subset_Iic.mpr (hbpos N).le)
    rw [hk, hl] at hmono
    exact_mod_cast hmono
  have hlk : l < k + 1 := by
    have := hN N le_rfl
    rw [hl] at this
    exact_mod_cast this
  have hleq : l = k := by omega
  obtain ⟨q, hRq, hqb⟩ := exists_rat_btwn (hbpos N)
  refine ⟨q, hRq, ?_⟩
  apply le_antisymm
  · calc
      ν (Set.Iic (q : ℝ)) ≤ ν (s N) :=
        measure_mono (Set.Iic_subset_Iic.mpr hqb.le)
      _ = ν (Set.Iic R) := by rw [hl, hk, hleq]
  · exact measure_mono (Set.Iic_subset_Iic.mpr hRq.le)

end ProbabilityTheory.BranchingRandomWalk
