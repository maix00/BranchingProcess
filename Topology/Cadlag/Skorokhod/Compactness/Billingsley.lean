/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Compactness.Approximation
public import Topology.Cadlag.Skorokhod.EDistance.Logarithmic.Completeness
public import Topology.Cadlag.Skorokhod.EDistance.Logarithmic.TopologyComparison

/-!
# Relative compactness for càdlàg paths with compact range

Uniform oscillation partitions and containment in a common compact state
space imply relative compactness in the Skorokhod `J₁` topology. The proof
uses Billingsley's complete path metric and therefore does not assume that
the ambient state space is complete.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace Skorokhod

/-- Forgetting that paths take values in a subtype preserves their `J₁`
distance. -/
theorem j1EDist_forgetRange {E : Type*} [MetricSpace E] {range : Set E}
    (f g : CadlagPath unitInterval range) :
    j1EDist f.forgetRange g.forgetRange = j1EDist f g := by
  have huniform (u v : CadlagPath unitInterval range) :
      uniformEDist u.forgetRange v.forgetRange = uniformEDist u v := by
    rw [uniformEDist_eq_edist, uniformEDist_eq_edist,
      UniformFun.edist_def, UniformFun.edist_def]
    apply iSup_congr
    intro t
    simp [CadlagPath.forgetRange_apply, Subtype.edist_eq]
  have hcost (change : TimeChange) :
    j1Cost f.forgetRange g.forgetRange change = j1Cost f g change := by
    unfold j1Cost
    have hact (u : CadlagPath unitInterval range) :
        (change.act u).forgetRange = change.act u.forgetRange := by
      ext t
      rfl
    rw [← hact f, huniform]
  unfold j1EDist
  exact iInf_congr hcost

/-- Forgetting a compact state-range subtype is an isometry on càdlàg path
spaces with the `J₁` metric. -/
theorem isometry_forgetRange {E : Type*} [MetricSpace E] {range : Set E} :
    Isometry (fun f : CadlagPath unitInterval range => f.forgetRange) := by
  intro f g
  change edist f.forgetRange g.forgetRange = edist f g
  simp only [edist_cadlagPath_eq_j1EDist, j1EDist_forgetRange]

set_option linter.style.haveILetI false in
/-- A path family satisfying the compact-range oscillation criterion has a
compact superset in the `J₁` path space. -/
theorem exists_isCompact_superset_of_uniform_admitsOscillationPartition
    {E : Type*} [MetricSpace E] {K : Set (CadlagPath unitInterval E)}
    (hrange : ∃ range : Set E, IsCompact range ∧
      ∀ path ∈ K, ∀ t, path t ∈ range)
    (hpartitions : ∀ tolerance > 0, ∃ gap > 0, ∀ path ∈ K,
      ∃ partition : OscillationPartition, gap < partition.mesh ∧
        ∃ oscillation < tolerance,
          OscillationBoundedOnPartition partition path oscillation) :
    ∃ C : Set (CadlagPath unitInterval E), IsCompact C ∧ K ⊆ C := by
  classical
  obtain ⟨range, hrangeCompact, hrange⟩ := hrange
  haveI : CompactSpace range := isCompact_iff_compactSpace.mp hrangeCompact
  haveI : CompleteSpace range := completeSpace_coe_iff_isComplete.mpr
    hrangeCompact.isComplete
  let lift : {p : CadlagPath unitInterval E // p ∈ K} →
      CadlagPath unitInterval range := fun p =>
        p.1.restrictRange range (hrange p.1 p.2) hrangeCompact.isClosed
  let lifted : Set (CadlagPath unitInterval range) := Set.range lift
  have hliftPartitions : ∀ tolerance > 0, ∃ gap > 0, ∀ p ∈ lifted,
      ∃ partition : OscillationPartition, gap < partition.mesh ∧
        ∃ oscillation < tolerance,
          OscillationBoundedOnPartition partition p oscillation := by
    intro tolerance htolerance
    obtain ⟨gap, hgap, hpartitions⟩ := hpartitions tolerance htolerance
    refine ⟨gap, hgap, ?_⟩
    intro p hp
    obtain ⟨original, horiginal, rfl⟩ := hp
    obtain ⟨partition, hmesh, oscillation, hoscillation, hosc⟩ :=
      hpartitions original.1 original.2
    refine ⟨partition, hmesh, oscillation, hoscillation, ?_⟩
    intro s t hs ht hsame
    have h := hosc s t hs ht hsame
    simpa [lift, CadlagPath.restrictRange, Subtype.dist_eq] using h
  have hliftRange : ∃ C : Set range, IsCompact C ∧
      ∀ p ∈ lifted, ∀ t, p t ∈ C := by
    refine ⟨Set.univ, isCompact_univ, ?_⟩
    intro p hp t
    simp
  let image : Set (BillingsleyPath range) :=
    (fun p : CadlagPath unitInterval range => (⟨p⟩ : BillingsleyPath range)) '' lifted
  have himageTotal : TotallyBounded image := by
    have hcontinuous : Continuous (fun p : CadlagPath unitInterval range =>
        (⟨p⟩ : BillingsleyPath range)) := continuous_toBillingsleyPath
    have hcompactApproximants (gap : ℝ) (rangeSet : Set range)
        (hrangeSet : IsCompact rangeSet) (hgap : 0 < gap) (maxCells : ℕ) :
        IsCompact ((fun p : CadlagPath unitInterval range =>
          (⟨p⟩ : BillingsleyPath range)) ''
            compactRangeMovingPartitionStepPathFamily gap rangeSet hgap maxCells) :=
      (isCompact_compactRangeMovingPartitionStepPathFamily gap rangeSet
        hrangeSet hgap maxCells).image hcontinuous
    rw [Metric.totallyBounded_iff]
    intro ε hε
    let radius := ε / 3
    have hradius : 0 < radius := by dsimp [radius]; linarith
    obtain ⟨gap, hgap, hparts⟩ := hliftPartitions radius hradius
    let rangeSet : Set range := Set.univ
    let maxCells := ⌊1 / gap⌋₊
    let approximants := compactRangeMovingPartitionStepPathFamily
      gap rangeSet hgap maxCells
    let approximantsB : Set (BillingsleyPath range) :=
      (fun p : CadlagPath unitInterval range => (⟨p⟩ : BillingsleyPath range)) ''
        approximants
    have hcompact : IsCompact approximantsB := by
      apply hcompactApproximants gap rangeSet isCompact_univ hgap maxCells
    have htotally : TotallyBounded approximantsB := hcompact.totallyBounded
    obtain ⟨centers, hcentersFinite, hcover⟩ :=
      (Metric.totallyBounded_iff.mp htotally) radius hradius
    refine ⟨centers, hcentersFinite, ?_⟩
    intro p hp
    obtain ⟨path, hpath, rfl⟩ := hp
    obtain ⟨partition, hmesh, oscillation, hoscillation, hosc⟩ :=
      hparts path hpath
    have hsizeGap : (partition.size : ℝ) * gap ≤ 1 := by
      calc
        (partition.size : ℝ) * gap ≤ partition.size * partition.mesh :=
          mul_le_mul_of_nonneg_left (le_of_lt hmesh) (Nat.cast_nonneg _)
        _ ≤ 1 := partition.size_mul_mesh_le_one
    have hsizeDiv : (partition.size : ℝ) ≤ 1 / gap :=
      (le_div_iff₀ hgap).2 hsizeGap
    have hsize : partition.size ≤ maxCells := by
      dsimp [maxCells]
      exact Nat.le_floor hsizeDiv
    have happ : partition.stepApproximation path ∈ approximants :=
      partition.stepApproximation_mem_compactRangeMovingPartitionStepPathFamily
        path rangeSet hgap hmesh (by intro t; trivial) hsize
    have hoscNonneg : 0 ≤ oscillation := by
      have hself := hosc ⊥ ⊥ (ne_of_lt bot_lt_top) (ne_of_lt bot_lt_top) rfl
      simpa using hself
    have hstepEdist : edist (⟨path⟩ : BillingsleyPath range)
        (⟨partition.stepApproximation path⟩ : BillingsleyPath range) ≤
          ENNReal.ofReal oscillation := by
      change billingsleyEDist path (partition.stepApproximation path) ≤ _
      calc
        billingsleyEDist path (partition.stepApproximation path) ≤
            billingsleyCost path (partition.stepApproximation path) TimeChange.refl :=
          billingsleyEDist_le_cost _ _ _
        _ = uniformEDist path (partition.stepApproximation path) := by
          simp [billingsleyCost]
        _ ≤ ENNReal.ofReal oscillation :=
          partition.uniformEDist_stepApproximation_le path hosc
    have hstepDist : dist (⟨path⟩ : BillingsleyPath range)
        (⟨partition.stepApproximation path⟩ : BillingsleyPath range) ≤ oscillation := by
      calc
        dist _ _ = (edist _ _).toReal := by rw [dist_edist]
        _ ≤ (ENNReal.ofReal oscillation).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hstepEdist
        _ = oscillation := ENNReal.toReal_ofReal hoscNonneg
    have happB : (⟨partition.stepApproximation path⟩ : BillingsleyPath range) ∈
        approximantsB := ⟨partition.stepApproximation path, happ, rfl⟩
    rcases Set.mem_iUnion.mp (hcover happB) with ⟨center, hcenterCover⟩
    rcases Set.mem_iUnion.mp hcenterCover with ⟨hcenter, hcenterBall⟩
    have hcenterDist : dist (⟨partition.stepApproximation path⟩ :
        BillingsleyPath range) center < radius := Metric.mem_ball.mp hcenterBall
    refine Set.mem_iUnion.mpr ⟨center, Set.mem_iUnion.mpr ⟨hcenter, ?_⟩⟩
    rw [Metric.mem_ball]
    calc
      dist (⟨path⟩ : BillingsleyPath range) center ≤
          dist (⟨path⟩ : BillingsleyPath range)
              (⟨partition.stepApproximation path⟩ : BillingsleyPath range) +
            dist (⟨partition.stepApproximation path⟩ : BillingsleyPath range) center :=
        dist_triangle _ _ _
      _ < radius + radius := add_lt_add_of_le_of_lt
        (hstepDist.trans hoscillation.le) hcenterDist
      _ < ε := by dsimp [radius]; linarith
  have hcompactClosure : IsCompact (closure image) :=
    isCompact_iff_totallyBounded_isComplete.mpr
      ⟨himageTotal.closure, isClosed_closure.isComplete⟩
  let back : BillingsleyPath range → CadlagPath unitInterval range :=
    fun p => p.toCadlagPath
  have hbackContinuous : Continuous back :=
    (billingsleyPathHomeomorph (E := range)).symm.continuous
  let forget : CadlagPath unitInterval range → CadlagPath unitInterval E :=
    fun p => p.forgetRange
  have hforgetContinuous : Continuous forget := isometry_forgetRange.continuous
  let compact : Set (CadlagPath unitInterval E) :=
    (forget ∘ back) '' closure image
  have hcompact : IsCompact compact :=
    hcompactClosure.image (hforgetContinuous.comp hbackContinuous)
  refine ⟨compact, hcompact, ?_⟩
  intro original horiginal
  have hlift : lift ⟨original, horiginal⟩ ∈ lifted := ⟨⟨original, horiginal⟩, rfl⟩
  have himage : (⟨lift ⟨original, horiginal⟩⟩ : BillingsleyPath range) ∈ image :=
    ⟨lift ⟨original, horiginal⟩, hlift, rfl⟩
  have hclosure : (⟨lift ⟨original, horiginal⟩⟩ : BillingsleyPath range) ∈ closure image :=
    subset_closure himage
  refine ⟨⟨lift ⟨original, horiginal⟩⟩, hclosure, ?_⟩
  ext t
  rfl

end Skorokhod

end
