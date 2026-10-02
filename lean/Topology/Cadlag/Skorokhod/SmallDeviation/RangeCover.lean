module

public import Topology.Cadlag.Skorokhod.SmallDeviation.PathSets
public import Order.Bounds.RangeCover

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
  have hosc' : ∀ s t : unitInterval,
      |f.toFun s - f.toFun t| ≤ 2 - margin := by
    simpa [Skorokhod.OscillationBounded] using hosc
  have hgeneral : Order.Bounds.UnitRangeTube (⊥ : unitInterval) f :=
    ⟨hzero, margin, hmargin, hosc'⟩
  obtain ⟨j, hj, margin', hmarg', hcorr⟩ :=
    Order.Bounds.unitRangeTube_exists_corridor (⊥ : unitInterval) f k hk hgeneral
  simp only [Set.mem_iUnion]
  refine ⟨j, hj, ?_⟩
  exact ⟨hzero, margin', hmarg', hcorr⟩

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
