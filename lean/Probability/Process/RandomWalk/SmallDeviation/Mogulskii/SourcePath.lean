/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Skorokhod.Corridor
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal
public import Probability.Sequence.IID.Law
public import MeasureTheory.MeasurableSpace.CadlagPath.TerminalLeft
public import Topology.Cadlag.TerminalLeft

/-!
# Source endpoint convention for the normalized walk path

The path used in the source paper is the right-continuous normalized step path
on times strictly below `1`, with its terminal value replaced by the left
limit. Its range therefore records the partial sums through time `n - 1`.
This file proves that encoding and its exact finite-corridor event identity.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace ProbabilityTheory.RandomWalk

open Skorokhod

/-- The normalized step path with the source paper's terminal convention:
the value at time `1` is the left limit of the usual right-continuous step
path. -/
noncomputable def sourceNormalizedStepCadlagPathIcc (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) : CadlagPath unitInterval ℝ :=
  terminalLeftPath (normalizedStepCadlagPathIcc scale n increment)

/-- The source-convention random-walk path is Borel measurable as a map from
the increment sequence space into Skorokhod path space. -/
theorem measurable_sourceNormalizedStepCadlagPathIcc (scale : ℕ → ℝ) (n : ℕ) :
    Measurable (sourceNormalizedStepCadlagPathIcc scale n :
      (ℕ → ℝ) → CadlagPath unitInterval ℝ) := by
  exact MeasureTheory.CadlagPath.measurable_terminalLeftPath.comp
    (measurable_normalizedStepCadlagPathIcc scale n)

/-- The source-convention path formed from an arbitrary independent sequence
with common increment law `ν` has the pushforward path law induced by the
canonical i.i.d. sequence law. -/
theorem hasLaw_sourceNormalizedStepCadlagPathIcc_of_iid
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ν : Measure ℝ}
    {coordinate : ℕ → Ω → ℝ}
    (hindep : iIndepFun coordinate P)
    (hmeasurable : ∀ k, Measurable (coordinate k))
    (hlaw : ∀ k, HasLaw (coordinate k) ν P)
    (scale : ℕ → ℝ) (n : ℕ) :
    HasLaw
      (fun ω => sourceNormalizedStepCadlagPathIcc scale n
        (fun k => coordinate k ω))
      ((iidSequenceLaw ν).map (sourceNormalizedStepCadlagPathIcc scale n)) P := by
  have hsequence : HasLaw (fun ω k => coordinate k ω) (iidSequenceLaw ν) P :=
    hindep.hasLaw_iidSequenceLaw hmeasurable hlaw
  have hpath : HasLaw (sourceNormalizedStepCadlagPathIcc scale n)
      ((iidSequenceLaw ν).map (sourceNormalizedStepCadlagPathIcc scale n))
      (iidSequenceLaw ν) :=
    hasLaw_map (measurable_sourceNormalizedStepCadlagPathIcc scale n).aemeasurable
  exact hpath.comp hsequence

/-- Probabilities of measurable source-path events agree under any i.i.d.
realization and the canonical increment law. The measurability hypothesis on
`G` is required for this exact measure equality. -/
theorem measure_sourceNormalizedStepCadlagPathIcc_preimage_eq_of_iid
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ν : Measure ℝ}
    {coordinate : ℕ → Ω → ℝ}
    (hindep : iIndepFun coordinate P)
    (hmeasurable : ∀ k, Measurable (coordinate k))
    (hlaw : ∀ k, HasLaw (coordinate k) ν P)
    (scale : ℕ → ℝ) (n : ℕ)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : MeasurableSet G) :
    P {ω | sourceNormalizedStepCadlagPathIcc scale n
        (fun k => coordinate k ω) ∈ G} =
      iidSequenceLaw ν {increment |
        sourceNormalizedStepCadlagPathIcc scale n increment ∈ G} := by
  calc
    P {ω | sourceNormalizedStepCadlagPathIcc scale n
        (fun k => coordinate k ω) ∈ G} =
        ((iidSequenceLaw ν).map (sourceNormalizedStepCadlagPathIcc scale n)) G :=
      (hasLaw_sourceNormalizedStepCadlagPathIcc_of_iid
        hindep hmeasurable hlaw scale n).measure_eq hG
    _ = iidSequenceLaw ν {increment |
        sourceNormalizedStepCadlagPathIcc scale n increment ∈ G} :=
      Measure.map_apply
        (measurable_sourceNormalizedStepCadlagPathIcc scale n) hG

@[simp]
theorem sourceNormalizedStepCadlagPathIcc_apply_of_ne_top
    (scale : ℕ → ℝ) (n : ℕ) (increment : ℕ → ℝ)
    {t : unitInterval} (ht : t ≠ ⊤) :
    sourceNormalizedStepCadlagPathIcc scale n increment t =
      normalizedStepPath scale n increment (t : ℝ) := by
  simp [sourceNormalizedStepCadlagPathIcc, ht]

/-- The source-convention path ends at the normalized `(n - 1)`-step sum.
The hypothesis `0 < n` ensures that the left side of time `1` is nonempty. -/
theorem sourceNormalizedStepCadlagPathIcc_apply_top
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (increment : ℕ → ℝ) :
    sourceNormalizedStepCadlagPathIcc scale n increment ⊤ =
      (scale n)⁻¹ * AdditivePath.displacement (n - 1) increment := by
  have hbotTop : (⊥ : unitInterval) < ⊤ := by
    norm_num [unitInterval]
  have harg_cont : Continuous (fun t : unitInterval =>
      (n : ℝ) * (t : ℝ)) :=
    continuous_subtype_val.const_mul (n : ℝ)
  have hfilter : 𝓝[<] (⊤ : unitInterval) ≤ 𝓝 (⊤ : unitInterval) :=
    nhdsWithin_le_nhds
  have harg_nhds : Tendsto (fun t : unitInterval =>
      (n : ℝ) * (t : ℝ)) (𝓝[<] ⊤) (𝓝 (n : ℝ)) :=
    by
      simpa [unitInterval] using
        (harg_cont.continuousAt.tendsto).mono_left hfilter
  have harg : Tendsto (fun t : unitInterval =>
      (n : ℝ) * (t : ℝ)) (𝓝[<] ⊤) (𝓝[<] (n : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨harg_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    have httop : t < (⊤ : unitInterval) := by simpa using ht
    have htval : (t : ℝ) < 1 := by
      by_contra hnot
      have hval : (t : ℝ) = 1 := le_antisymm t.property.2 (le_of_not_gt hnot)
      exact (ne_of_lt httop) (Subtype.ext hval)
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    change (n : ℝ) * (t : ℝ) < (n : ℝ)
    nlinarith [mul_lt_mul_of_pos_left htval hnreal]
  have hfloorInt : Tendsto (fun t : unitInterval =>
      ⌊(n : ℝ) * (t : ℝ)⌋) (𝓝[<] ⊤) (𝓝 ((n : ℤ) - 1)) := by
    simpa using (tendsto_floor_left_pure_sub_one (n : ℤ)).comp harg
  have hfloorNat : Tendsto (fun t : unitInterval =>
      ⌊(n : ℝ) * (t : ℝ)⌋₊) (𝓝[<] ⊤) (𝓝 (n - 1)) := by
    change Tendsto (fun t : unitInterval =>
      Int.toNat (⌊(n : ℝ) * (t : ℝ)⌋ : ℤ)) (𝓝[<] ⊤) (𝓝 (n - 1))
    have htoNat : Continuous (Int.toNat : ℤ → ℕ) := continuous_of_discreteTopology
    have h := htoNat.continuousAt.tendsto.comp hfloorInt
    have hnat : Int.toNat ((n : ℤ) - 1) = n - 1 := by omega
    rw [hnat] at h
    exact h
  have hsum : Tendsto (fun t : unitInterval =>
      AdditivePath.displacement (⌊(n : ℝ) * (t : ℝ)⌋₊) increment)
      (𝓝[<] ⊤) (𝓝 (AdditivePath.displacement (n - 1) increment)) := by
    have hdiscrete : Continuous
        (fun k : ℕ => AdditivePath.displacement k increment) :=
      continuous_of_discreteTopology
    exact hdiscrete.continuousAt.tendsto.comp hfloorNat
  have hpath : Tendsto (fun t : unitInterval =>
      normalizedStepPath scale n increment (t : ℝ))
      (𝓝[<] ⊤)
      (𝓝 ((scale n)⁻¹ * AdditivePath.displacement (n - 1) increment)) := by
    change Tendsto (fun t : unitInterval =>
      (scale n)⁻¹ * AdditivePath.displacement
        (⌊(n : ℝ) * (t : ℝ)⌋₊) increment) _ _
    exact (continuous_const.mul continuous_id).continuousAt.tendsto.comp hsum
  have hleft : Function.leftLim (fun t : unitInterval =>
      normalizedStepPath scale n increment (t : ℝ)) ⊤ =
      (scale n)⁻¹ * AdditivePath.displacement (n - 1) increment :=
    leftLim_eq_of_tendsto
      (h := nhdsLT_neBot_of_exists_lt ⟨⊥, hbotTop⟩) hpath
  rw [sourceNormalizedStepCadlagPathIcc, terminalLeftPath_apply_top]
  simpa only [normalizedStepCadlagPathIcc_apply] using hleft

/-- The range of the source-convention path is precisely the set of normalized
partial sums `S₀, …, S_(n-1)`. -/
theorem sourceNormalizedStepCadlagPathIcc_range_eq_scaledDisplacement
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (increment : ℕ → ℝ) :
    Set.range (sourceNormalizedStepCadlagPathIcc scale n increment) =
      Set.range (fun k : Fin n =>
        (scale n)⁻¹ * AdditivePath.displacement (k : ℕ) increment) := by
  apply Set.Subset.antisymm
  · rintro y ⟨t, rfl⟩
    by_cases ht : t = ⊤
    · subst t
      rw [sourceNormalizedStepCadlagPathIcc_apply_top scale hn]
      exact ⟨⟨n - 1, by omega⟩, rfl⟩
    · have httop : t < (⊤ : unitInterval) := (lt_top_iff_ne_top).2 ht
      have htval : (t : ℝ) < 1 := by
        by_contra hnot
        have hval : (t : ℝ) = 1 := le_antisymm t.property.2 (le_of_not_gt hnot)
        exact ht (Subtype.ext hval)
      have hmul : 0 ≤ (n : ℝ) * (t : ℝ) :=
        mul_nonneg (Nat.cast_nonneg n) t.property.1
      have hmulTop : (n : ℝ) * (t : ℝ) < (n : ℝ) := by
        calc
          (n : ℝ) * (t : ℝ) < (n : ℝ) * 1 :=
            mul_lt_mul_of_pos_left htval (by exact_mod_cast hn)
          _ = (n : ℝ) := by ring
      let k : ℕ := ⌊(n : ℝ) * (t : ℝ)⌋₊
      have hk : k < n := by
        dsimp [k]
        exact (Nat.floor_lt hmul).2 hmulTop
      refine ⟨⟨k, hk⟩, ?_⟩
      rw [sourceNormalizedStepCadlagPathIcc_apply_of_ne_top scale n increment ht]
      simp [normalizedStepPath, k]
  · rintro y ⟨k, rfl⟩
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    let t : unitInterval :=
      ⟨(k : ℝ) / n, ⟨div_nonneg (Nat.cast_nonneg _) hnreal.le,
        (div_le_one hnreal).2 (by exact_mod_cast k.isLt.le)⟩⟩
    have htval : (t : ℝ) = (k : ℝ) / n := rfl
    have htlt : (t : ℝ) < 1 := by
      rw [htval]
      exact (div_lt_one hnreal).2 (by exact_mod_cast k.isLt)
    have htne : t ≠ ⊤ := by
      intro h
      have hval : (t : ℝ) = 1 := by
        simpa [unitInterval] using congrArg (fun s : unitInterval => (s : ℝ)) h
      linarith
    refine ⟨t, ?_⟩
    rw [sourceNormalizedStepCadlagPathIcc_apply_of_ne_top scale n increment htne,
      htval]
    exact normalizedStepPath_grid scale hn increment

private theorem normalizedStepCadlagPathIcc_range_eq_scaledDisplacement
    (scale : ℝ) {n : ℕ} (hn : 0 < n) (increment : ℕ → ℝ) :
    Set.range (normalizedStepCadlagPathIcc (fun _ => scale) n increment) =
      Set.range (fun k : Fin (n + 1) =>
        scale⁻¹ * AdditivePath.displacement (k : ℕ) increment) := by
  apply Set.Subset.antisymm
  · rintro y ⟨t, rfl⟩
    obtain ⟨k, hk⟩ :=
      exists_normalizedStepCadlagPathIcc_eq_scaledDisplacement
        (fun _ => scale) n increment t
    refine ⟨k, ?_⟩
    exact hk.symm
  · rintro y ⟨k, rfl⟩
    by_cases hk : (k : ℕ) = n
    · refine ⟨⊤, ?_⟩
      have htop : normalizedStepCadlagPathIcc (fun _ => scale) n increment ⊤ =
          scale⁻¹ * AdditivePath.displacement n increment := by
        simp [normalizedStepCadlagPathIcc_apply]
      rw [htop]
      exact congrArg (fun j : ℕ => scale⁻¹ * AdditivePath.displacement j increment)
        hk.symm
    · have hklt : (k : ℕ) < n := by omega
      let t : unitInterval :=
        ⟨(k : ℝ) / n, ⟨div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hn.le),
          (div_le_one (by exact_mod_cast hn)).2 (by exact_mod_cast hklt.le)⟩⟩
      have htval : (t : ℝ) = (k : ℝ) / n := rfl
      have htlt : (t : ℝ) < 1 := by
        rw [htval]
        exact (div_lt_one (by exact_mod_cast hn)).2 (by exact_mod_cast hklt)
      have htne : t ≠ ⊤ := by
        intro h
        have hval : (t : ℝ) = 1 := by
          simpa [unitInterval] using congrArg (fun s : unitInterval => (s : ℝ)) h
        linarith
      refine ⟨t, ?_⟩
      rw [normalizedStepCadlagPathIcc_apply, htval,
        normalizedStepPath_grid (fun _ => scale) hn increment]

private theorem mem_rangeInOpenInterval_iff_of_range_eq
    {f g : CadlagPath unitInterval ℝ} {lower upper : ℝ}
    (hrange : Set.range f = Set.range g) :
    f ∈ Skorokhod.rangeInOpenInterval lower upper ↔
      g ∈ Skorokhod.rangeInOpenInterval lower upper := by
  rw [Skorokhod.mem_rangeInOpenInterval_iff,
    Skorokhod.mem_rangeInOpenInterval_iff]
  constructor
  · rintro ⟨margin, hmargin, hpath⟩
    refine ⟨margin, hmargin, fun t => ?_⟩
    have hvalue : g t ∈ Set.range f := by
      rw [hrange]
      exact ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := hvalue
    simpa [hs] using hpath s
  · rintro ⟨margin, hmargin, hpath⟩
    refine ⟨margin, hmargin, fun t => ?_⟩
    have hvalue : f t ∈ Set.range g := by
      rw [← hrange]
      exact ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := hvalue
    simpa [hs] using hpath s

/-- The source-convention path's strict Skorokhod corridor event is exactly
the strict horizontal tube over its first `n - 1` partial sums. The shortened
horizon is essential: the terminal value is `S_(n-1)`, not `S_n`. -/
theorem sourceNormalizedStepCadlagPathIcc_mem_rangeInOpenInterval_iff
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (hscale : 0 < scale n)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) (increment : ℕ → ℝ) :
    sourceNormalizedStepCadlagPathIcc scale n increment ∈
        Skorokhod.rangeInOpenInterval (-a) (1 - a) ↔
      InOpenHorizontalTube a (scale n) (n - 1) increment := by
  by_cases hnOne : n = 1
  · subst n
    have hrange := sourceNormalizedStepCadlagPathIcc_range_eq_scaledDisplacement
      scale (n := 1) (by norm_num) increment
    have hzero : ∀ t : unitInterval,
        sourceNormalizedStepCadlagPathIcc scale 1 increment t = 0 := by
      intro t
      have hvalue : sourceNormalizedStepCadlagPathIcc scale 1 increment t ∈
          Set.range (fun k : Fin 1 =>
            (scale 1)⁻¹ * AdditivePath.displacement (k : ℕ) increment) := by
        rw [← hrange]
        exact ⟨t, rfl⟩
      obtain ⟨k, hk⟩ := hvalue
      have hkval : (k : ℕ) = 0 := by omega
      simpa [hkval, AdditivePath.displacement_zero] using hk.symm
    constructor
    · intro _
      simp [InOpenHorizontalTube]
    · intro _
      let δ : ℝ := min a (1 - a) / 2
      have hmargin_pos : 0 < δ := by
        dsimp [δ]
        apply div_pos
        · exact lt_min ha (sub_pos.mpr haOne)
        · norm_num
      refine ⟨δ, hmargin_pos, fun t => ?_⟩
      rw [hzero t]
      have hleft : δ ≤ a := by
        dsimp [δ]
        have h := min_le_left a (1 - a)
        linarith
      have hright : δ ≤ 1 - a := by
        dsimp [δ]
        have h := min_le_right a (1 - a)
        linarith
      constructor <;> linarith
  · have htwo : 2 ≤ n := by omega
    have hshortPos : 0 < n - 1 := by omega
    have hlen : n - 1 + 1 = n := Nat.sub_add_cancel hn
    let shortPath : CadlagPath unitInterval ℝ :=
      normalizedStepCadlagPathIcc (fun _ => scale n) (n - 1) increment
    have hsourceRange := sourceNormalizedStepCadlagPathIcc_range_eq_scaledDisplacement
      scale hn increment
    have hshortRange := normalizedStepCadlagPathIcc_range_eq_scaledDisplacement
      (scale n) hshortPos increment
    have hrange :
        Set.range (sourceNormalizedStepCadlagPathIcc scale n increment) =
          Set.range shortPath := by
      dsimp [shortPath]
      rw [hsourceRange, hshortRange, hlen]
    have hevent := mem_rangeInOpenInterval_iff_of_range_eq
      (lower := -a) (upper := 1 - a) hrange
    have hshortEvent : shortPath ∈ Skorokhod.rangeInOpenInterval (-a) (1 - a) ↔
        InOpenHorizontalTube a (scale n) (n - 1) increment := by
      simpa [shortPath] using
        (normalizedStepCadlagPathIcc_mem_rangeInOpenInterval_iff
          (fun _ => scale n) hshortPos (by simpa using hscale) ha haOne increment)
    exact hevent.trans hshortEvent

end ProbabilityTheory.RandomWalk

end
