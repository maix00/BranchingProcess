/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Topology.Cadlag.Basic

/-!
# Terminal left-limit modification of càdlàg paths

## Public declarations

- `Skorokhod.terminalLeftPath`: for any topological state space `E`, changes
  a càdlàg path's value at `⊤` to its left limit there and leaves its other
  values fixed.
- `Skorokhod.terminalLeftPath_apply_top` and
  `Skorokhod.terminalLeftPath_apply_of_ne_top`: give the terminal and
  nonterminal values of this modification.
- `Skorokhod.IsTerminalLeftPath` and `Skorokhod.terminalLeftPathSpace` define
  the endpoint convention `path ⊤ = leftLim path ⊤` and its path space `D₀`
  for each topological state space `E`.
- `Skorokhod.terminalLeftPath_mem_space`: for a T₂ state space, every
  càdlàg path maps into `D₀`.
- `Skorokhod.terminalLeftPath_eq_self_of_mem_space`: the modification fixes
  each path already in `D₀`.
- `Skorokhod.terminalLeftPath_idempotent`: for a T₂ state space, applying
  the modification twice equals applying it once.

On the compact unit interval, replacing the value of a càdlàg path at the top
endpoint by its left limit gives the endpoint convention used by left-continuous
path encodings. The construction applies to paths valued in any topological
space; the Borel measurability result for real-valued paths is stated in
`MeasureTheory.MeasurableSpace.CadlagPath.TerminalLeft`.

The terminal endpoint convention is the one used for $D(0,1)$ in Theorem 3,
Section 4, p. 764 of A. A. Mogul'skii, “Small deviations in the sample
function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755–765; see also the English translation, “Small Deviations in a Space of
Trajectories,” *Theory of Probability and Its Applications* 19(4) (1975),
726–736, DOI [10.1137/1119081](https://doi.org/10.1137/1119081).
-/

@[expose] public section

open Filter
open scoped Topology

namespace Skorokhod

variable {E : Type*} [TopologicalSpace E]

/-- Replace a càdlàg path's terminal value by its left limit. -/
noncomputable def terminalLeftPath
    (path : CadlagPath unitInterval E) : CadlagPath unitInterval E :=
  ⟨(fun t => if t = ⊤ then Function.leftLim (fun s : unitInterval => path s) ⊤
      else path t),
    path.isCadlag_toFun.updateTop
      (Function.leftLim (fun s : unitInterval => path s) ⊤)⟩

@[simp]
theorem terminalLeftPath_apply_top (path : CadlagPath unitInterval E) :
    terminalLeftPath path ⊤ = Function.leftLim (fun s : unitInterval => path s) ⊤ := by
  simp [terminalLeftPath]

@[simp]
theorem terminalLeftPath_apply_of_ne_top (path : CadlagPath unitInterval E)
    {t : unitInterval} (ht : t ≠ ⊤) :
    terminalLeftPath path t = path t := by
  simp [terminalLeftPath, ht]

/-- The endpoint convention of the source path space `D₀`: a càdlàg path's
  terminal value agrees with its left limit. -/
def IsTerminalLeftPath (path : CadlagPath unitInterval E) : Prop :=
  path ⊤ = Function.leftLim (fun s : unitInterval => path s) ⊤

/-- The source path space `D₀`, viewed as a subset of the full càdlàg path
space on the closed unit interval. -/
def terminalLeftPathSpace : Set (CadlagPath unitInterval E) :=
  {path | IsTerminalLeftPath path}

/-- Replacing a càdlàg path's terminal value by its left limit lands in `D₀`.
The left limit itself is unchanged because the modification only affects the
terminal point. -/
theorem terminalLeftPath_mem_space [T2Space E]
    (path : CadlagPath unitInterval E) :
    terminalLeftPath path ∈ terminalLeftPathSpace := by
  change terminalLeftPath path ⊤ =
    Function.leftLim (fun s : unitInterval => terminalLeftPath path s) ⊤
  rw [terminalLeftPath_apply_top]
  let hbotTop : (⊥ : unitInterval) < ⊤ := by
    norm_num [unitInterval]
  have hleft : Tendsto (fun s : unitInterval => path s)
      (𝓝[<] (⊤ : unitInterval))
      (𝓝 (Function.leftLim (fun s : unitInterval => path s) ⊤)) :=
    path.isCadlag_toFun.tendsto_nhdsLT_leftLim ⊤
  have hmodified : Tendsto (fun s : unitInterval => terminalLeftPath path s)
      (𝓝[<] (⊤ : unitInterval))
      (𝓝 (Function.leftLim (fun s : unitInterval => path s) ⊤)) := by
    apply hleft.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hslt : s < (⊤ : unitInterval) := by simpa using hs
    exact (terminalLeftPath_apply_of_ne_top path (ne_of_lt hslt)).symm
  have hleft_eq := leftLim_eq_of_tendsto
    (h := nhdsLT_neBot_of_exists_lt ⟨⊥, hbotTop⟩) hmodified
  exact hleft_eq.symm

/-- The terminal-left modification is the identity on the source path space
`D₀`. -/
theorem terminalLeftPath_eq_self_of_mem_space
    (path : CadlagPath unitInterval E)
    (hpath : path ∈ terminalLeftPathSpace) :
    terminalLeftPath path = path := by
  apply CadlagPath.ext
  intro t
  by_cases ht : t = ⊤
  · subst t
    change path ⊤ = Function.leftLim (fun s : unitInterval => path s) ⊤ at hpath
    simpa using hpath.symm
  · simp [terminalLeftPath, ht]

/-- For a T₂ state space, applying the terminal-left modification twice has
the same effect as applying it once. -/
theorem terminalLeftPath_idempotent [T2Space E]
    (path : CadlagPath unitInterval E) :
    terminalLeftPath (terminalLeftPath path) = terminalLeftPath path :=
  terminalLeftPath_eq_self_of_mem_space _ (terminalLeftPath_mem_space path)

end Skorokhod

end
