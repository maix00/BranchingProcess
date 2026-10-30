/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Topology
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
import all Topology.Cadlag.Skorokhod.EDistance.Logarithmic.Completion.Completeness
import all Topology.Cadlag.Skorokhod.EDistance.Logarithmic.Comparison
import all Topology.Cadlag.Skorokhod.Path.Lemmas.Separable

/-!
# Separability of Skorokhod path space

## Public declarations

- `Skorokhod.exists_countable_dense_set_cadlagPath`: for a separable metric
  state space $E$, the Skorokhod space $D([0,1],E)$ has a countable dense set.
- `Skorokhod.instSeparableSpaceCadlagPath`: if the metric state space $E$ is
  separable, then the space $D([0,1],E)$ with the $J_1$ topology is separable.
- `Skorokhod.instIsCompletelyMetrizableSpaceCadlagPath`: this path space is
  completely metrizable when the state space is a metric space.
-/

@[expose] public section

namespace Skorokhod

/-- A separable metric state space gives a countable dense family of
càdlàg paths in the Skorokhod `J₁` topology. -/
theorem exists_countable_dense_set_cadlagPath {E : Type*} [MetricSpace E]
    [TopologicalSpace.SeparableSpace E] :
    ∃ s : Set (CadlagPath unitInterval E), s.Countable ∧ Dense s := by
  exact ⟨denseStepPathFamily (E := E), countable_denseStepPathFamily,
    dense_denseStepPathFamily⟩

noncomputable instance instSeparableSpaceCadlagPath {E : Type*} [MetricSpace E]
    [TopologicalSpace.SeparableSpace E] :
    TopologicalSpace.SeparableSpace (CadlagPath unitInterval E) := by
  obtain ⟨s, hsCountable, hsDense⟩ :=
    exists_countable_dense_set_cadlagPath (E := E)
  exact ⟨⟨s, hsCountable, hsDense⟩⟩

set_option linter.style.haveILetI false in
/-- The Skorokhod `J₁` space of càdlàg paths is completely metrizable when the
state space is complete. The proof transfers complete metrizability from
Billingsley's logarithmic path metric through `billingsleyPathHomeomorph`,
which identifies the two path topologies; see Patrick Billingsley,
*Convergence of Probability Measures*, 1st ed., Wiley, 1968, Chapter 3, §14,
Theorem 14.1, p. 114. -/
noncomputable instance instIsCompletelyMetrizableSpaceCadlagPath
    {E : Type*} [MetricSpace E] [CompleteSpace E] :
    TopologicalSpace.IsCompletelyMetrizableSpace (CadlagPath unitInterval E) := by
  let e := billingsleyPathHomeomorph (E := E)
  haveI : TopologicalSpace.IsCompletelyMetrizableSpace (BillingsleyPath E) := inferInstance
  exact Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace e.isClosedEmbedding

end Skorokhod

end
