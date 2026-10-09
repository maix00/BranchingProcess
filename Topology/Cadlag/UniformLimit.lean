/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Topology.Order.Cadlag

/-!
# Uniform limits of càdlàg functions

Uniform limits of càdlàg functions remain càdlàg when the state space is
complete. The proof treats right continuity directly and obtains left limits
as limits of the uniformly Cauchy sequence of the approximants' left limits.
-/

@[expose] public section

open Filter Set
open scoped Topology

variable {X E : Type*} [Preorder X] [TopologicalSpace X] [MetricSpace E]
  [CompleteSpace E]

/-- A pointwise-uniform limit of càdlàg functions into a complete metric space
is càdlàg. -/
theorem IsCadlag.tendstoUniformly {F : ℕ → X → E} {f : X → E}
    (hF : ∀ n, IsCadlag (F n))
    (huniform : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, dist (F n x) (f x) < ε) :
    IsCadlag f := by
  refine ⟨?_, ?_⟩
  · intro x
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hthird : 0 < ε / 3 := by positivity
    obtain ⟨N, hN⟩ := huniform (ε / 3) hthird
    have hFn : ∀ᶠ y in nhdsWithin x (Set.Ioi x),
        dist (F N y) (F N x) < ε / 3 :=
      (Metric.tendsto_nhds.mp ((hF N).isRightContinuous x).tendsto)
        (ε / 3) hthird
    have hbase : dist (F N x) (f x) < ε / 3 := hN N le_rfl x
    filter_upwards [hFn] with y hy
    have htriangle : dist (f y) (f x) ≤
        dist (f y) (F N y) + dist (F N y) (F N x) + dist (F N x) (f x) := by
      calc
        dist (f y) (f x) ≤ dist (f y) (F N y) + dist (F N y) (f x) :=
          dist_triangle _ _ _
        _ ≤ dist (f y) (F N y) +
            (dist (F N y) (F N x) + dist (F N x) (f x)) :=
          add_le_add_right (dist_triangle _ _ _) _
        _ = dist (f y) (F N y) + dist (F N y) (F N x) +
            dist (F N x) (f x) := by abel
    have hclose : dist (f y) (F N y) < ε / 3 := by
      simpa [dist_comm] using hN N le_rfl y
    linarith
  · intro x
    rcases eq_or_neBot (nhdsWithin x (Set.Iio x)) with hbot | hnebot
    · refine ⟨f x, ?_⟩
      rw [hbot]
      exact Filter.tendsto_bot
    · let L : ℕ → E := fun n => Classical.choose ((hF n).tendsto_nhdsLT x)
      have hL (n : ℕ) : Tendsto (F n) (nhdsWithin x (Set.Iio x)) (𝓝 (L n)) :=
        Classical.choose_spec ((hF n).tendsto_nhdsLT x)
      let : NeBot (nhdsWithin x (Set.Iio x)) := hnebot
      have hLcauchy : CauchySeq L := by
        rw [Metric.cauchySeq_iff]
        intro ε hε
        have hthird : 0 < ε / 3 := by positivity
        obtain ⟨N, hN⟩ := huniform (ε / 3) hthird
        refine ⟨N, ?_⟩
        intro m hm n hn
        have hclose (y : X) : dist (F m y) (F n y) ≤ 2 * (ε / 3) := by
          calc
            dist (F m y) (F n y) ≤
                dist (F m y) (f y) + dist (f y) (F n y) := dist_triangle _ _ _
            _ ≤ ε / 3 + ε / 3 :=
              add_le_add (le_of_lt (hN m hm y))
                (le_of_lt (by simpa [dist_comm] using hN n hn y))
            _ = 2 * (ε / 3) := by ring
        have hpair : Tendsto (fun y => (F m y, F n y))
            (nhdsWithin x (Set.Iio x)) (𝓝 (L m, L n)) :=
          (hL m).prodMk_nhds (hL n)
        have hdist : Tendsto (fun y => dist (F m y) (F n y))
            (nhdsWithin x (Set.Iio x)) (𝓝 (dist (L m) (L n))) :=
          (continuous_dist.tendsto (L m, L n)).comp hpair
        have hbound : ∀ᶠ y in nhdsWithin x (Set.Iio x),
            dist (F m y) (F n y) ∈ Set.Iic (2 * (ε / 3)) :=
          Filter.Eventually.of_forall fun y => hclose y
        have hlimit : dist (L m) (L n) ≤ 2 * (ε / 3) :=
          isClosed_Iic.mem_of_tendsto hdist hbound
        linarith
      obtain ⟨l, hLlim⟩ := cauchySeq_tendsto_of_complete hLcauchy
      refine ⟨l, ?_⟩
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      have hthird : 0 < ε / 3 := by positivity
      obtain ⟨N, hN⟩ := huniform (ε / 3) hthird
      have hLnear : ∀ᶠ n in atTop, dist (L n) l < ε / 3 :=
        Metric.tendsto_nhds.mp hLlim (ε / 3) hthird
      obtain ⟨M, hM⟩ := (Filter.eventually_atTop.1 hLnear)
      let n := max N M
      have hnN : n ≥ N := le_max_left _ _
      have hnM : n ≥ M := le_max_right _ _
      have hLn : dist (L n) l < ε / 3 := hM n hnM
      have hFn : ∀ᶠ y in nhdsWithin x (Set.Iio x),
          dist (F n y) (L n) < ε / 3 :=
        Metric.tendsto_nhds.mp (hL n) (ε / 3) hthird
      have huniformN (y : X) : dist (F n y) (f y) < ε / 3 := hN n hnN y
      filter_upwards [hFn] with y hy
      calc
        dist (f y) l ≤ dist (f y) (F n y) + dist (F n y) l := dist_triangle _ _ _
        _ ≤ dist (f y) (F n y) +
            (dist (F n y) (L n) + dist (L n) l) :=
          add_le_add_right (dist_triangle (F n y) (L n) l)
            (dist (f y) (F n y))
        _ < ε := by
          have hclose : dist (f y) (F n y) < ε / 3 := by
            simpa [dist_comm] using huniformN y
          linarith
