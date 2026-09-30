module

public import Topology.Cadlag.Skorokhod.Oscillation
public import Mathlib.Topology.Order.IsLUB

/-!
# Oscillation bounds on dense sets

For càdlàg paths, a range bound can be checked on a dense set of times that
contains the terminal endpoint. This reduces path-range events to countably
many coordinates once a countable dense time set is chosen.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace Skorokhod

/-- For a càdlàg real path, an oscillation bound on a dense time set that
contains the terminal endpoint holds at every time. -/
theorem oscillationBounded_on_dense
    {T : Type*} [LinearOrder T] [TopologicalSpace T] [OrderTopology T]
    [DenselyOrdered T] [FirstCountableTopology T] [OrderTop T]
    {D : Set T} (hD : Dense D) (htop : ⊤ ∈ D)
    (path : T → ℝ) (hpath : IsCadlag path) {bound : ℝ}
    (hDpath : ∀ s ∈ D, ∀ t ∈ D, |path s - path t| ≤ bound) :
    ∀ s t, |path s - path t| ≤ bound := by
  have happrox (x : T) :
      ∃ u : ℕ → T, (∀ n, u n ∈ D) ∧
        Tendsto (fun n => path (u n)) atTop (𝓝 (path x)) := by
    by_cases hx : x = ⊤
    · subst x
      exact ⟨fun _ => ⊤, fun _ => htop, tendsto_const_nhds⟩
    · have hxtop : x < ⊤ := lt_of_le_of_ne le_top hx
      obtain ⟨u, _, humem, hulim⟩ :=
        hD.exists_seq_strictAnti_tendsto_of_lt hxtop
      have hwithin : Tendsto u atTop (𝓝[Set.Ioi x] x) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨hulim, Filter.Eventually.of_forall fun n => (humem n).1.1⟩
      refine ⟨u, fun n => (humem n).2, ?_⟩
      exact (hpath.isRightContinuous x).tendsto.comp hwithin
  intro s t
  obtain ⟨us, husD, hus⟩ := happrox s
  obtain ⟨ut, hutD, hut⟩ := happrox t
  have hdiff : Tendsto (fun n => path (us n) - path (ut n)) atTop
      (𝓝 (path s - path t)) := hus.sub hut
  have hosc : Tendsto (fun n => |path (us n) - path (ut n)|) atTop
      (𝓝 |path s - path t|) :=
    (continuous_abs.tendsto _).comp hdiff
  have hbounded : ∀ᶠ n in atTop,
      |path (us n) - path (ut n)| ∈ Set.Iic bound :=
    Filter.Eventually.of_forall fun n => hDpath (us n) (husD n) (ut n) (hutD n)
  exact isClosed_Iic.mem_of_tendsto hosc hbounded

end Skorokhod

end
