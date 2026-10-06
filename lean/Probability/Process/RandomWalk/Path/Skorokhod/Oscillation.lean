/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.UniformGrid
public import Probability.Process.RandomWalk.Path.Cadlag
public import Probability.Process.RandomWalk.Path.Block.Law.FirstCrossing
public import Topology.Cadlag.Skorokhod.Oscillation.Partition.Finite
public import Topology.Cadlag.Skorokhod.Oscillation.Partition.Measurability
public import Topology.Cadlag.Skorokhod.Oscillation.DoubleExcursion

/-!
# Oscillation partitions for finite random-walk paths

The deterministic normalized step path has no within-cell oscillation on its
own time grid. For each fixed step count, this gives a common positive mesh
for every choice of increments; the mesh may shrink with the step count.
-/

@[expose] public section

open Skorokhod

namespace ProbabilityTheory.RandomWalk

/-- The points of the uniform partition used by an `n`-step path. -/
noncomputable def normalizedStepGridPoints (n : ℕ) (hn : 0 < n)
    (j : Fin (n + 1)) : unitInterval := by
  let grid := UniformGrid.unit (K := ℝ) n hn
  refine ⟨grid.point j, ?_⟩
  change 0 ≤ grid.point j ∧ grid.point j ≤ 1
  simpa [grid, UniformGrid.unit, Set.mem_Icc] using (grid.point_mem_Icc j)

@[simp]
private theorem normalizedStepGridPoints_coe (n : ℕ) (hn : 0 < n)
    (j : Fin (n + 1)) :
    (normalizedStepGridPoints n hn j : ℝ) = (j : ℝ) / n := by
  simp [normalizedStepGridPoints, UniformGrid.point, UniformGrid.unit]

theorem normalizedStepGridPoints_first (n : ℕ) (hn : 0 < n) :
    normalizedStepGridPoints n hn ⟨0, by omega⟩ = ⊥ := by
  apply Subtype.ext
  simp [normalizedStepGridPoints, UniformGrid.point, UniformGrid.unit]

theorem normalizedStepGridPoints_last (n : ℕ) (hn : 0 < n) :
    normalizedStepGridPoints n hn ⟨n, by omega⟩ = ⊤ := by
  apply Subtype.ext
  simp [normalizedStepGridPoints, UniformGrid.point, UniformGrid.unit,
    Nat.cast_ne_zero.mpr hn.ne']

theorem normalizedStepGridPoints_strictMono (n : ℕ) (hn : 0 < n) :
    StrictMono (normalizedStepGridPoints n hn) := by
  intro i j hij
  apply Subtype.mk_lt_mk.mpr
  simpa [normalizedStepGridPoints] using
    (UniformGrid.strictMono_point
      (grid := UniformGrid.unit n hn) (by simp [UniformGrid.unit]) hij)

/-- The finite partition whose cells are the steps of an `n`-step path. -/
noncomputable def normalizedStepOscillationPartition (n : ℕ)
    (hn : 0 < n) : OscillationPartition :=
  OscillationPartition.ofFinitePoints hn (normalizedStepGridPoints n hn)
    (normalizedStepGridPoints_first n hn)
    (normalizedStepGridPoints_last n hn)
    (normalizedStepGridPoints_strictMono n hn)

/-- On a nonterminal time, the cell index in the step partition is the
integer part of the rescaled time. -/
private theorem natFloor_mul_eq_stepPartitionIndex (n : ℕ) (hn : 0 < n)
    (t : unitInterval) (ht : t ≠ ⊤) :
    ⌊(n : ℝ) * t⌋₊ =
      ((normalizedStepOscillationPartition n hn).index t).val := by
  let partition := normalizedStepOscillationPartition n hn
  have hi : (partition.index t).val < n := by
    exact (partition.index t).is_lt
  let i : Fin n := ⟨(partition.index t).val, hi⟩
  have hindex : partition.index t = i := by
    apply Fin.ext
    rfl
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hleftPoint :
      (partition.points i.castSucc : ℝ) = (i.val : ℝ) / n := by
    change (normalizedStepGridPoints n hn i.castSucc : ℝ) = _
    rw [normalizedStepGridPoints_coe]
    simp
  have hlowerPoint : (i.val : ℝ) / n ≤ t := by
    have hlower := partition.index_lower t
    rw [hindex] at hlower
    have hlowerReal :
        (partition.points i.castSucc : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast hlower
    rw [hleftPoint] at hlowerReal
    exact hlowerReal
  have hlow : (i.val : ℝ) ≤ (n : ℝ) * t := by
    have hmul := (div_le_iff₀ hnReal).mp hlowerPoint
    nlinarith [hmul]
  have hhigh : (n : ℝ) * t < (i.val : ℝ) + 1 := by
    have hupperIndex := partition.index_upper t
    rw [hindex] at hupperIndex
    rcases hupperIndex with hupper | hlast
    · have hnextPoint :
          (partition.points i.succ : ℝ) = ((i.val : ℝ) + 1) / n := by
        change (normalizedStepGridPoints n hn i.succ : ℝ) = _
        rw [normalizedStepGridPoints_coe]
        simp
      have hupperPoint : t < ((i.val : ℝ) + 1) / n := by
        rw [← hnextPoint]
        have hupperReal : (t : ℝ) < (partition.points i.succ : ℝ) := by
          exact_mod_cast hupper
        exact hupperReal
      have hmul := (lt_div_iff₀ hnReal).mp hupperPoint
      nlinarith [hmul]
    · have htlt : (t : ℝ) < 1 := by
        by_contra hnot
        have heq : (t : ℝ) = 1 := le_antisymm t.property.2
          (le_of_not_gt hnot)
        apply ht
        exact Subtype.ext heq
      have hlastN : i.val + 1 = n := by
        exact hlast
      have hlastReal : (i.val : ℝ) + 1 = n := by exact_mod_cast hlastN
      nlinarith [htlt, hnReal]
  apply (Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg n) t.property.1)).2
  exact ⟨hlow, hhigh⟩

/-- Every `n`-step normalized path is constant on the cells of its uniform
step partition, away from the terminal value. -/
theorem normalizedStepCadlagPathIcc_oscillationBoundedOnStepPartition
    (scale : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (increment : ℕ → ℝ) :
    OscillationBoundedOnPartition (normalizedStepOscillationPartition n hn)
      (normalizedStepCadlagPathIcc scale n increment) 0 := by
  intro s t hs ht hindex
  have hsFloor := natFloor_mul_eq_stepPartitionIndex n hn s hs
  have htFloor := natFloor_mul_eq_stepPartitionIndex n hn t ht
  have hfloor : (⌊(n : ℝ) * s⌋₊ : ℕ) = ⌊(n : ℝ) * t⌋₊ := by
    calc
      _ = ((normalizedStepOscillationPartition n hn).index s).val := hsFloor
      _ = ((normalizedStepOscillationPartition n hn).index t).val :=
        congrArg Fin.val hindex
      _ = _ := htFloor.symm
  simp [normalizedStepCadlagPathIcc_apply, normalizedStepPath, hfloor]

/-- For each fixed step count, all normalized step paths admit a common
positive-gap partition with zero cell oscillation. The gap depends only on
the step count, so this absorbs any finite prefix in an asymptotic tightness
argument. -/
theorem exists_pos_uniform_admitsOscillationPartition_normalizedStepPath
    (scale : ℕ → ℝ) (n : ℕ) (hn : 0 < n) {maximumOscillation : ℝ}
    (hoscillation : 0 < maximumOscillation) :
    ∃ minimumGap > 0, ∀ increment : ℕ → ℝ,
      normalizedStepCadlagPathIcc scale n increment ∈
        admitsOscillationPartition minimumGap maximumOscillation := by
  let partition := normalizedStepOscillationPartition n hn
  refine ⟨partition.mesh / 2, half_pos partition.mesh_pos, fun increment => ?_⟩
  change ∃ p : OscillationPartition,
    partition.mesh / 2 < p.mesh ∧
      ∃ bound < maximumOscillation,
        OscillationBoundedOnPartition p
          (normalizedStepCadlagPathIcc scale n increment) bound
  refine ⟨partition, by dsimp [partition]; linarith [partition.mesh_pos],
    0, hoscillation, ?_⟩
  exact normalizedStepCadlagPathIcc_oscillationBoundedOnStepPartition
    scale n hn increment

private theorem exists_pos_uniform_admitsOscillationPartition_normalizedStepPath_zero
    (scale : ℕ → ℝ) {maximumOscillation : ℝ}
    (hoscillation : 0 < maximumOscillation) :
    ∃ minimumGap > 0, ∀ increment : ℕ → ℝ,
      normalizedStepCadlagPathIcc scale 0 increment ∈
        admitsOscillationPartition minimumGap maximumOscillation := by
  let partition := normalizedStepOscillationPartition 1 (by omega)
  refine ⟨partition.mesh / 2, half_pos partition.mesh_pos, fun increment => ?_⟩
  have hzero (t : unitInterval) :
      normalizedStepCadlagPathIcc scale 0 increment t = 0 := by
    simp [normalizedStepCadlagPathIcc_apply, normalizedStepPath]
  have hosc : OscillationBoundedOnPartition partition
      (normalizedStepCadlagPathIcc scale 0 increment) 0 := by
    intro s t hs ht hindex
    change dist (normalizedStepCadlagPathIcc scale 0 increment s)
      (normalizedStepCadlagPathIcc scale 0 increment t) ≤ 0
    rw [hzero s, hzero t]
    simp
  change ∃ p : OscillationPartition,
    partition.mesh / 2 < p.mesh ∧
      ∃ bound < maximumOscillation,
        OscillationBoundedOnPartition p
          (normalizedStepCadlagPathIcc scale 0 increment) bound
  exact ⟨partition, by dsimp [partition]; linarith [partition.mesh_pos],
    0, hoscillation, hosc⟩

/-- A finite prefix of normalized step-path laws admits a common positive
partition gap at any prescribed positive oscillation tolerance. This is the
deterministic finite-prefix input for asymptotic multiscale tightness. -/
theorem exists_pos_uniform_admitsOscillationPartition_normalizedStepPath_prefix
    (scale : ℕ → ℝ) (N : ℕ) {maximumOscillation : ℝ}
    (hoscillation : 0 < maximumOscillation) :
    ∃ minimumGap > 0, ∀ n < N, ∀ increment : ℕ → ℝ,
      normalizedStepCadlagPathIcc scale n increment ∈
        admitsOscillationPartition minimumGap maximumOscillation := by
  induction N with
  | zero =>
      exact ⟨1, by norm_num, by simp⟩
  | succ N ih =>
      obtain ⟨oldGap, holdGap, hold⟩ := ih
      have huniform : ∃ newGap > 0, ∀ increment : ℕ → ℝ,
          normalizedStepCadlagPathIcc scale N increment ∈
            admitsOscillationPartition newGap maximumOscillation := by
        by_cases hN : N = 0
        · subst N
          exact exists_pos_uniform_admitsOscillationPartition_normalizedStepPath_zero
            scale hoscillation
        · exact exists_pos_uniform_admitsOscillationPartition_normalizedStepPath
            scale N (Nat.pos_of_ne_zero hN) hoscillation
      obtain ⟨newGap, hnewGap, hnew⟩ := huniform
      refine ⟨min oldGap newGap, lt_min holdGap hnewGap, ?_⟩
      intro n hn increment
      by_cases hnN : n < N
      · obtain ⟨partition, hmesh, bound, hbound, hosc⟩ := hold n hnN increment
        refine ⟨partition, lt_of_le_of_lt (min_le_left _ _) hmesh,
          bound, hbound, hosc⟩
      · have hnEq : n = N := by omega
        subst n
        obtain ⟨partition, hmesh, bound, hbound, hosc⟩ := hnew increment
        exact ⟨partition, lt_of_le_of_lt (min_le_right _ _) hmesh,
          bound, hbound, hosc⟩

private theorem existsNatAnchorForWindow {n width i l : ℕ}
    (hwidth : 0 < width) (hi : i < n) (hil : i ≤ l)
    (hspan : l - i ≤ width) :
    ∃ j : ℕ, j < n / width + 1 ∧ j * width ≤ i ∧
      i < j * width + width ∧ l < j * width + 2 * width := by
  let j := i / width
  have hmod : i % width < width := Nat.mod_lt i hwidth
  have hdecomp : i % width + j * width = i := by
    dsimp [j]
    simpa [Nat.mul_comm] using Nat.mod_add_div i width
  have hdiv : j ≤ n / width := by
    dsimp [j]
    exact Nat.div_le_div_right hi.le
  refine ⟨j, by omega, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

private theorem displacement_natAdd_eq_sub (increment : ℕ → ℝ)
    {start finish : ℕ} (hstart : start ≤ finish) :
    AdditivePath.displacement (finish - start)
        (fun k => increment (start + k)) =
      AdditivePath.displacement finish increment -
        AdditivePath.displacement start increment := by
  have hsplit := AdditivePath.displacement_add start (finish - start) increment
  have hend : start + (finish - start) = finish := by omega
  rw [hend] at hsplit
  rw [hsplit]
  ring

/-- Distance between two values of a normalized step path, expressed as the
scaled absolute difference of the corresponding partial sums. -/
theorem normalizedStepCadlagPathIcc_dist_eq
    (scale : ℕ → ℝ) (n : ℕ) (hscale : 0 < scale n)
    (increment : ℕ → ℝ) (s t : unitInterval) :
    dist (normalizedStepCadlagPathIcc scale n increment s)
        (normalizedStepCadlagPathIcc scale n increment t) =
      (scale n)⁻¹ *
        |AdditivePath.displacement ⌊(n : ℝ) * s⌋₊ increment -
          AdditivePath.displacement ⌊(n : ℝ) * t⌋₊ increment| := by
  rw [normalizedStepCadlagPathIcc_apply, normalizedStepPath,
    normalizedStepCadlagPathIcc_apply, normalizedStepPath, Real.dist_eq,
    ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hscale)]

/-- A strict excursion of the normalized path yields the corresponding raw
partial-sum excursion after multiplying by the positive spatial scale. -/
theorem normalizedStepCadlagPathIcc_dist_lt_implies_raw
    (scale : ℕ → ℝ) (n : ℕ) (hscale : 0 < scale n)
    (increment : ℕ → ℝ) (ε : ℝ) (s t : unitInterval)
    (hdist : ε < dist (normalizedStepCadlagPathIcc scale n increment s)
      (normalizedStepCadlagPathIcc scale n increment t)) :
    ε * scale n ≤
      |AdditivePath.displacement ⌊(n : ℝ) * s⌋₊ increment -
        AdditivePath.displacement ⌊(n : ℝ) * t⌋₊ increment| := by
  rw [normalizedStepCadlagPathIcc_dist_eq scale n hscale increment s t] at hdist
  have hdiv : ε <
      |AdditivePath.displacement ⌊(n : ℝ) * s⌋₊ increment -
        AdditivePath.displacement ⌊(n : ℝ) * t⌋₊ increment| / scale n := by
    simpa [div_eq_mul_inv, mul_comm] using hdist
  exact le_of_lt ((lt_div_iff₀ hscale).mp hdiv)

/-- If a normalized random-walk path violates Billingsley's double-excursion
bound on a time interval shorter than `δ`, then two ordered large block
excursions occur in one member of the deterministic grid of windows of
length `width`. The window starts are integer multiples of `width`; this is
the path-to-increment bridge used by the probabilistic block estimates. -/
theorem normalizedStepCadlagPathIcc_not_hasDoubleExcursionBound_subset_windowGrid
    (scale : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hscale : 0 < scale n)
    (δ ε : ℝ)
    (width : ℕ) (hwidth : 0 < width)
    (hwidthLower : (n : ℝ) * δ ≤ width)
    (increment : ℕ → ℝ)
    (hbad : ¬ Skorokhod.HasDoubleExcursionBound
      (normalizedStepCadlagPathIcc scale n increment) δ ε) :
    increment ∈ ⋃ j : Fin (n / width + 1),
      twoOrderedBlockExcursions (j.val * width) (2 * width)
        (ε * scale n) := by
  classical
  have hbad' := hbad
  simp only [Skorokhod.HasDoubleExcursionBound, not_forall, not_le] at hbad'
  rcases hbad' with ⟨s, t, u, hst, htu, huTop, hsu, x, y, z, w,
    hsx, hxy, hyt, htz, hzw, hwu, hmin⟩
  have hfirst : ε < dist
      (normalizedStepCadlagPathIcc scale n increment x)
      (normalizedStepCadlagPathIcc scale n increment y) := by
    exact lt_of_lt_of_le hmin (min_le_left _ _)
  have hsecond : ε < dist
      (normalizedStepCadlagPathIcc scale n increment z)
      (normalizedStepCadlagPathIcc scale n increment w) := by
    exact lt_of_lt_of_le hmin (min_le_right _ _)
  have hsuVal : (s : ℝ) < (u : ℝ) := by
    exact_mod_cast lt_trans hst htu
  have hsuReal : (u : ℝ) - (s : ℝ) < δ := by
    have hdist : |(s : ℝ) - (u : ℝ)| < δ := by
      simpa [Subtype.dist_eq, Real.dist_eq] using hsu
    rw [abs_of_nonpos (sub_nonpos.mpr hsuVal.le)] at hdist
    linarith
  have hxw : (x : ℝ) ≤ (w : ℝ) := by
    have hxw' : x ≤ w := le_trans hxy (le_trans hyt (le_trans htz hzw))
    exact_mod_cast hxw'
  have htimespan : (w : ℝ) - (x : ℝ) < δ := by
    have hsx' : (s : ℝ) ≤ (x : ℝ) := by exact_mod_cast hsx
    have hwu' : (w : ℝ) ≤ (u : ℝ) := by exact_mod_cast hwu
    linarith
  let i : ℕ := ⌊(n : ℝ) * (x : ℝ)⌋₊
  let j : ℕ := ⌊(n : ℝ) * (y : ℝ)⌋₊
  let k : ℕ := ⌊(n : ℝ) * (z : ℝ)⌋₊
  let l : ℕ := ⌊(n : ℝ) * (w : ℝ)⌋₊
  have htimeWidth : (n : ℝ) * ((w : ℝ) - (x : ℝ)) < width := by
    have hmul : (n : ℝ) * ((w : ℝ) - (x : ℝ)) <
        (n : ℝ) * δ := by gcongr
    exact lt_of_lt_of_le hmul hwidthLower
  have htimeWidth' : (n : ℝ) * (w : ℝ) - (n : ℝ) * (x : ℝ) < width := by
    nlinarith [htimeWidth]
  have hiNonneg : 0 ≤ (n : ℝ) * (x : ℝ) :=
    mul_nonneg (Nat.cast_nonneg n) x.property.1
  have hlNonneg : 0 ≤ (n : ℝ) * (w : ℝ) :=
    mul_nonneg (Nat.cast_nonneg n) w.property.1
  have hiFloorUpper : (n : ℝ) * (x : ℝ) < (i : ℝ) + 1 := by
    simpa [i] using Nat.lt_floor_add_one ((n : ℝ) * (x : ℝ))
  have hlFloorLower : (l : ℝ) ≤ (n : ℝ) * (w : ℝ) := by
    simpa [l] using Nat.floor_le hlNonneg
  have hspanNat : l - i ≤ width := by
    have hspanReal : (l : ℝ) < (i : ℝ) + (width : ℝ) + 1 := by
      dsimp [i] at hiFloorUpper
      dsimp [l] at hlFloorLower
      linarith
    have hspanCast : l < i + width + 1 := by exact_mod_cast hspanReal
    omega
  have hfloorOrder : i ≤ l := by
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_left hxw (Nat.cast_nonneg n)
  have hlLtN : l < n := by
    have hwne : w ≠ ⊤ := by
      intro h
      subst w
      exact huTop (le_antisymm hwu le_top).symm
    have hwltOne : (w : ℝ) < 1 := by
      by_contra hnot
      have heq : (w : ℝ) = 1 := le_antisymm w.property.2
        (le_of_not_gt hnot)
      exact hwne (Subtype.ext heq)
    have hlReal : (l : ℝ) ≤ (n : ℝ) * (w : ℝ) := hlFloorLower
    have hmulPos : 0 < (n : ℝ) * (1 - (w : ℝ)) :=
      mul_pos (by exact_mod_cast hn) (by linarith)
    have hltReal : (l : ℝ) < n := by nlinarith [hlReal, hmulPos]
    exact_mod_cast hltReal
  have hiLtN : i < n := lt_of_le_of_lt hfloorOrder hlLtN
  have hindices : i ≤ j ∧ j ≤ k ∧ k ≤ l := by
    refine ⟨?_, ?_, ?_⟩
    · apply Nat.floor_mono
      exact mul_le_mul_of_nonneg_left (show (x : ℝ) ≤ (y : ℝ) by exact_mod_cast hxy)
        (Nat.cast_nonneg n)
    · apply Nat.floor_mono
      exact mul_le_mul_of_nonneg_left (show (y : ℝ) ≤ (z : ℝ) by
        exact_mod_cast le_trans hyt htz) (Nat.cast_nonneg n)
    · apply Nat.floor_mono
      exact mul_le_mul_of_nonneg_left (show (z : ℝ) ≤ (w : ℝ) by exact_mod_cast hzw)
        (Nat.cast_nonneg n)
  obtain ⟨anchor, hanchorLt, hanchorLe, hiUpper, hlUpper⟩ :=
    existsNatAnchorForWindow hwidth hiLtN hfloorOrder hspanNat
  let localI := i - anchor * width
  let localJ := j - anchor * width
  let localK := k - anchor * width
  let localL := l - anchor * width
  have hlocalOrder : localI ≤ localJ ∧ localJ ≤ localK ∧
      localK ≤ localL ∧ localL ≤ 2 * width := by
    dsimp [localI, localJ, localK, localL]
    omega
  let anchorIndex : Fin (n / width + 1) := ⟨anchor, hanchorLt⟩
  have hvalueDist (a b : unitInterval) (ia ib : ℕ)
      (hia : ia = ⌊(n : ℝ) * (a : ℝ)⌋₊)
      (hib : ib = ⌊(n : ℝ) * (b : ℝ)⌋₊) :
      ε < dist (normalizedStepCadlagPathIcc scale n increment a)
          (normalizedStepCadlagPathIcc scale n increment b) →
        ε * scale n ≤
          |AdditivePath.displacement ib increment -
            AdditivePath.displacement ia increment| := by
    intro hdist
    rw [normalizedStepCadlagPathIcc_dist_eq scale n hscale increment a b,
      ← hia, ← hib] at hdist
    have hdiv : ε <
        |AdditivePath.displacement ib increment -
          AdditivePath.displacement ia increment| / scale n := by
      simpa [div_eq_mul_inv, mul_comm, abs_sub_comm] using hdist
    exact (le_of_lt ((lt_div_iff₀ hscale).mp hdiv))
  have hrawFirst := hvalueDist x y i j rfl rfl hfirst
  have hrawSecond := hvalueDist z w k l rfl rfl hsecond
  have hshiftI := displacement_natAdd_eq_sub increment
    (show anchor * width ≤ i by omega)
  have hshiftJ := displacement_natAdd_eq_sub increment
    (show anchor * width ≤ j by omega)
  have hshiftK := displacement_natAdd_eq_sub increment
    (show anchor * width ≤ k by omega)
  have hshiftL := displacement_natAdd_eq_sub increment
    (show anchor * width ≤ l by omega)
  have hrawLocalFirst : ε * scale n ≤
      |AdditivePath.displacement localJ
          (fun m => increment (anchor * width + m)) -
        AdditivePath.displacement localI
          (fun m => increment (anchor * width + m))| := by
    rw [hshiftJ, hshiftI]
    have habs :
        |(AdditivePath.displacement j increment -
            AdditivePath.displacement (anchor * width) increment) -
          (AdditivePath.displacement i increment -
            AdditivePath.displacement (anchor * width) increment)| =
          |AdditivePath.displacement j increment -
            AdditivePath.displacement i increment| := by congr 1; ring
    rw [habs]
    exact hrawFirst
  have hrawLocalSecond : ε * scale n ≤
      |AdditivePath.displacement localL
          (fun m => increment (anchor * width + m)) -
        AdditivePath.displacement localK
          (fun m => increment (anchor * width + m))| := by
    rw [hshiftL, hshiftK]
    have habs :
        |(AdditivePath.displacement l increment -
            AdditivePath.displacement (anchor * width) increment) -
          (AdditivePath.displacement k increment -
            AdditivePath.displacement (anchor * width) increment)| =
          |AdditivePath.displacement l increment -
            AdditivePath.displacement k increment| := by congr 1; ring
    rw [habs]
    exact hrawSecond
  have hlocalEvent :
      (fun m => increment (anchor * width + m)) ∈
        twoOrderedPrefixExcursions (2 * width) (ε * scale n) := by
    refine ⟨localI, localJ, localK, localL,
      hlocalOrder.1, hlocalOrder.2.1, hlocalOrder.2.2.1,
      hlocalOrder.2.2.2, hrawLocalFirst, hrawLocalSecond⟩
  have hgridEvent : increment ∈
      twoOrderedBlockExcursions (anchor * width) (2 * width)
        (ε * scale n) := hlocalEvent
  exact Set.mem_iUnion.mpr ⟨anchorIndex, by simpa [anchorIndex] using hgridEvent⟩

private theorem split_abs_sub_at_half {a x y : ℝ}
    (hlarge : 2 * a ≤ |x - y|) : a ≤ |x| ∨ a ≤ |y| := by
  by_contra h
  push Not at h
  have htriangle : |x - y| ≤ |x| + |y| := by
    rw [abs_sub_le_iff]
    constructor <;> nlinarith [le_abs_self x, neg_le_abs x,
      le_abs_self y, neg_le_abs y]
  linarith

/-- Failure of endpoint oscillation control for a normalized step path is
contained in the union of a first-window and a last-window prefix excursion.
The endpoint windows are handled in the general càdlàg layer; this theorem
only translates them to the underlying increments. -/
theorem normalizedStepCadlagPathIcc_not_hasEndpointOscillationBound_subset_boundaryBlocks
    (scale : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hscale : 0 < scale n)
    (δ ε : ℝ) (hε : 0 < ε) (width : ℕ)
    (hwidthLower : (n : ℝ) * δ ≤ width)
    (increment : ℕ → ℝ)
    (hbad : ¬ Skorokhod.HasEndpointOscillationBound
      (normalizedStepCadlagPathIcc scale n increment) δ ε) :
    increment ∈ blockPrefixExceedance 0 width (ε * scale n / 2) ∪
      blockPrefixExceedance (n - width) width (ε * scale n / 2) := by
  classical
  have hbad' := hbad
  simp only [Skorokhod.HasEndpointOscillationBound, not_and_or] at hbad'
  have hthreshold : 0 < ε * scale n / 2 := by positivity
  rcases hbad' with hleft | hright
  · push Not at hleft
    rcases hleft with ⟨s, t, hs, ht, hdist⟩
    let i : ℕ := ⌊(n : ℝ) * s⌋₊
    let j : ℕ := ⌊(n : ℝ) * t⌋₊
    have hraw := normalizedStepCadlagPathIcc_dist_lt_implies_raw
      scale n hscale increment ε s t hdist
    have hlarge : 2 * (ε * scale n / 2) ≤
        |AdditivePath.displacement i increment -
          AdditivePath.displacement j increment| := by
      nlinarith [hraw]
    have hsplit := split_abs_sub_at_half hlarge
    have htimeI : (n : ℝ) * s < width := by
      have hmul : (n : ℝ) * s < (n : ℝ) * δ := by gcongr
      exact lt_of_lt_of_le hmul hwidthLower
    have htimeJ : (n : ℝ) * t < width := by
      have hmul : (n : ℝ) * t < (n : ℝ) * δ := by gcongr
      exact lt_of_lt_of_le hmul hwidthLower
    have hiLt : i < width := by
      have hiReal : (i : ℝ) ≤ (n : ℝ) * s := by
        dsimp [i]
        exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) s.property.1)
      have : (i : ℝ) < width := lt_of_le_of_lt hiReal htimeI
      exact_mod_cast this
    have hjLt : j < width := by
      have hjReal : (j : ℝ) ≤ (n : ℝ) * t := by
        dsimp [j]
        exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) t.property.1)
      have : (j : ℝ) < width := lt_of_le_of_lt hjReal htimeJ
      exact_mod_cast this
    rcases hsplit with hi | hj
    · exact Or.inl <| blockPrefixExceedance_of_displacementDifference
        increment (start := 0) (finish := i) (length := width)
        hthreshold (by omega) (by omega) (by simpa [i, AdditivePath.displacement_zero] using hi)
    · exact Or.inl <| blockPrefixExceedance_of_displacementDifference
        increment (start := 0) (finish := j) (length := width)
        hthreshold (by omega) (by omega) (by simpa [j, AdditivePath.displacement_zero] using hj)
  · push Not at hright
    rcases hright with ⟨s, t, hsne, htne, hs, ht, hdist⟩
    let anchor : ℕ := n - width
    let i : ℕ := ⌊(n : ℝ) * s⌋₊
    let j : ℕ := ⌊(n : ℝ) * t⌋₊
    have hraw := normalizedStepCadlagPathIcc_dist_lt_implies_raw
      scale n hscale increment ε s t hdist
    have hiNonneg : 0 ≤ (n : ℝ) * s := mul_nonneg (Nat.cast_nonneg n) s.property.1
    have hjNonneg : 0 ≤ (n : ℝ) * t := mul_nonneg (Nat.cast_nonneg n) t.property.1
    have hanchorReal : (anchor : ℝ) ≤ (n : ℝ) * s := by
      by_cases hwidthn : width ≤ n
      · have hcast : (anchor : ℝ) = (n : ℝ) - width := by
          simp [anchor, Nat.cast_sub hwidthn]
        rw [hcast]
        have hmul : (n : ℝ) * (1 - δ) < (n : ℝ) * s := by gcongr
        nlinarith [hwidthLower]
      · have hzero : anchor = 0 := by
          have hle : n ≤ width := by omega
          simp [anchor, Nat.sub_eq_zero_of_le hle]
        simpa [hzero] using hiNonneg
    have hiAnchor : anchor ≤ i := by
      rw [Nat.le_floor_iff hiNonneg]
      exact hanchorReal
    have hjanchorReal : (anchor : ℝ) ≤ (n : ℝ) * t := by
      by_cases hwidthn : width ≤ n
      · have hcast : (anchor : ℝ) = (n : ℝ) - width := by
          simp [anchor, Nat.cast_sub hwidthn]
        rw [hcast]
        have hmul : (n : ℝ) * (1 - δ) < (n : ℝ) * t := by gcongr
        nlinarith [hwidthLower]
      · have hzero : anchor = 0 := by
          have hle : n ≤ width := by omega
          simp [anchor, Nat.sub_eq_zero_of_le hle]
        simpa [hzero] using hjNonneg
    have hjAnchor : anchor ≤ j := by
      rw [Nat.le_floor_iff hjNonneg]
      exact hjanchorReal
    have hiLeN : i ≤ n := by
      have htime : (n : ℝ) * s ≤ (n : ℝ) := by
        calc
          (n : ℝ) * s ≤ (n : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left s.property.2 (Nat.cast_nonneg n)
          _ = (n : ℝ) := by ring
      exact Nat.floor_le_of_le htime
    have hjLeN : j ≤ n := by
      have htime : (n : ℝ) * t ≤ (n : ℝ) := by
        calc
          (n : ℝ) * t ≤ (n : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left t.property.2 (Nat.cast_nonneg n)
          _ = (n : ℝ) := by ring
      exact Nat.floor_le_of_le htime
    have hilength : i - anchor ≤ width := by
      dsimp [anchor]
      omega
    have hjlength : j - anchor ≤ width := by
      dsimp [anchor]
      omega
    have hlarge : 2 * (ε * scale n / 2) ≤
        |(AdditivePath.displacement i increment -
            AdditivePath.displacement anchor increment) -
          (AdditivePath.displacement j increment -
            AdditivePath.displacement anchor increment)| := by
      have hiden :
          (AdditivePath.displacement i increment -
              AdditivePath.displacement anchor increment) -
            (AdditivePath.displacement j increment -
              AdditivePath.displacement anchor increment) =
            AdditivePath.displacement i increment - AdditivePath.displacement j increment := by
        ring
      rw [hiden]
      nlinarith [hraw]
    rcases split_abs_sub_at_half hlarge with hi | hj
    · exact Or.inr <| blockPrefixExceedance_of_displacementDifference
        increment (start := anchor) (finish := i) (length := width)
        hthreshold (by omega) hilength hi
    · exact Or.inr <| blockPrefixExceedance_of_displacementDifference
        increment (start := anchor) (finish := j) (length := width)
        hthreshold (by omega) hjlength hj

end ProbabilityTheory.RandomWalk

end
