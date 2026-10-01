module

public import Topology.Cadlag.Skorokhod.SmallDeviation.PathSets

/-!
# Finite corridor cover of an oscillation tube

The range event in Mogulskii's comparison is covered by finitely many
translated corridors. The argument uses the supremum of the complete path;
the finite grid is only a cover of its possible location.
-/

@[expose] public section

namespace Skorokhod

/-- A path starting at zero whose oscillation is less than two fits in one
of finitely many corridors with half-width `1 + 2 / k`. -/
theorem rangeTubeStartingAtZero_subset_iUnion_corridors
    (k : ℕ) (hk : 0 < k) :
    rangeTubeStartingAtZero 1 ⊆
      ⋃ j ∈ Finset.range (2 * k + 1),
        corridorStartingAtZero
          (((j : ℝ) / k - 1) - (1 + 2 / k))
          (((j : ℝ) / k - 1) + (1 + 2 / k)) := by
  intro f hf
  obtain ⟨hzero, margin, hmargin, hosc⟩ := hf
  let U : ℝ := sSup (Set.range f)
  have hupper : ∀ t, f t ≤ 2 - margin := by
    intro t
    have h := hosc t ⊥
    rw [hzero, sub_zero, abs_le] at h
    linarith [h.2]
  have hbounded : BddAbove (Set.range f) := ⟨2 - margin, by
    rintro y ⟨t, rfl⟩
    exact hupper t⟩
  have hnonempty : (Set.range f).Nonempty := ⟨f ⊥, ⟨⊥, rfl⟩⟩
  have hUpos : 0 ≤ U := by
    rw [← hzero]
    exact le_csSup hbounded ⟨⊥, rfl⟩
  have hUtop : U ≤ 2 - margin :=
    csSup_le hnonempty (by rintro y ⟨t, rfl⟩; exact hupper t)
  have hU : ∀ t, f t ≤ U := fun t => le_csSup hbounded ⟨t, rfl⟩
  have hUlower : ∀ t, U - (2 - margin) ≤ f t := by
    intro t
    have hbdd : ∀ s, f s ≤ f t + (2 - margin) := by
      intro s
      have h := hosc s t
      have hs := (abs_le.mp h).2
      linarith
    have hsup : U ≤ f t + (2 - margin) := by
      apply csSup_le hnonempty
      rintro y ⟨s, rfl⟩
      exact hbdd s
    linarith
  let j : ℕ := ⌊(k : ℝ) * U⌋₊
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hnonneg : 0 ≤ (k : ℝ) * U := mul_nonneg hkreal.le hUpos
  have hjlow : (j : ℝ) ≤ (k : ℝ) * U := Nat.floor_le hnonneg
  have hjhigh : (k : ℝ) * U < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hjbound : j < 2 * k + 1 := by
    have hcast : (j : ℝ) < (2 * k + 1 : ℕ) := by
      push_cast
      nlinarith [hUtop, mul_pos hkreal hmargin]
    exact_mod_cast hcast
  simp only [Set.mem_iUnion]
  refine ⟨j, Finset.mem_range.mpr hjbound, ?_⟩
  let m : ℝ := min (margin / 2) (1 / (2 * (k : ℝ)))
  have hm : 0 < m := lt_min (half_pos hmargin) (one_div_pos.mpr (by positivity))
  have hmMargin : m ≤ margin / 2 := min_le_left _ _
  have hmGrid : m ≤ 1 / (2 * (k : ℝ)) := min_le_right _ _
  have hmGrid' : m ≤ 1 / (k : ℝ) := by
    have hhalf : 1 / (2 * (k : ℝ)) = (1 / (k : ℝ)) / 2 := by ring
    rw [hhalf] at hmGrid
    have hpos : 0 ≤ 1 / (k : ℝ) := (one_div_pos.mpr hkreal).le
    linarith
  refine ⟨hzero, m, hm, ?_⟩
  intro t
  have hl := hUlower t
  have hu := hU t
  have hgridLow : (j : ℝ) / k ≤ U := (div_le_iff₀ hkreal).2 (by simpa [mul_comm] using hjlow)
  have hgridHigh : U < (j : ℝ) / k + 1 / k := by
    have h : U < ((j : ℝ) + 1) / k :=
      (lt_div_iff₀ hkreal).2 (by nlinarith [hjhigh])
    convert h using 1
    ring
  have htwo : 2 / (k : ℝ) = 2 * (1 / (k : ℝ)) := by ring
  constructor
  · rw [htwo]
    nlinarith [hmGrid', hgridLow, hl, one_div_pos.mpr hkreal]
  · rw [htwo]
    nlinarith [hmGrid', hgridHigh, hu, one_div_pos.mpr hkreal]

/-- The same finite cover after any spatial scaling. -/
theorem scaledRangeTube_subset_iUnion_scaledCorridors
    (a : ℝ) (k : ℕ) (hk : 0 < k) :
    scaleSet a (rangeTubeStartingAtZero 1) ⊆
      ⋃ j ∈ Finset.range (2 * k + 1),
        scaleSet a (corridorStartingAtZero
          (((j : ℝ) / k - 1) - (1 + 2 / k))
          (((j : ℝ) / k - 1) + (1 + 2 / k))) := by
  have h := Set.image_mono (f := scalePath a)
    (rangeTubeStartingAtZero_subset_iUnion_corridors k hk)
  simpa only [scaleSet, Set.image_iUnion] using h

end Skorokhod

end
