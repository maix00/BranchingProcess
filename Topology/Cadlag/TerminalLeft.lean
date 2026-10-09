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

On the compact unit interval, replacing the value of a càdlàg path at the top
endpoint by its left limit gives the endpoint convention used by left-continuous
path encodings. The resulting paths form the source path space `D₀`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Skorokhod

/-- Replace the value of a real càdlàg path at the terminal time `1` by its
left limit there. -/
noncomputable def terminalLeftPath
    (path : CadlagPath unitInterval ℝ) : CadlagPath unitInterval ℝ :=
  ⟨(fun t => if t = ⊤ then Function.leftLim (fun s : unitInterval => path s) ⊤
      else path t),
    path.isCadlag_toFun.updateTop
      (Function.leftLim (fun s : unitInterval => path s) ⊤)⟩

@[simp]
theorem terminalLeftPath_apply_top (path : CadlagPath unitInterval ℝ) :
    terminalLeftPath path ⊤ = Function.leftLim (fun s : unitInterval => path s) ⊤ := by
  simp [terminalLeftPath]

@[simp]
theorem terminalLeftPath_apply_of_ne_top (path : CadlagPath unitInterval ℝ)
    {t : unitInterval} (ht : t ≠ ⊤) :
    terminalLeftPath path t = path t := by
  simp [terminalLeftPath, ht]

/-- The endpoint convention of the source path space `D₀`: a càdlàg path's
terminal value agrees with its left limit at `1`. -/
def IsTerminalLeftPath (path : CadlagPath unitInterval ℝ) : Prop :=
  path ⊤ = Function.leftLim (fun s : unitInterval => path s) ⊤

/-- The source path space `D₀`, viewed as a subset of the full càdlàg path
space on the closed unit interval. -/
def terminalLeftPathSpace : Set (CadlagPath unitInterval ℝ) :=
  {path | IsTerminalLeftPath path}

/-- Replacing a càdlàg path's terminal value by its left limit lands in `D₀`.
The left limit itself is unchanged because the modification only affects the
terminal point. -/
theorem terminalLeftPath_mem_space (path : CadlagPath unitInterval ℝ) :
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
    (path : CadlagPath unitInterval ℝ)
    (hpath : path ∈ terminalLeftPathSpace) :
    terminalLeftPath path = path := by
  apply CadlagPath.ext
  intro t
  by_cases ht : t = ⊤
  · subst t
    change path ⊤ = Function.leftLim (fun s : unitInterval => path s) ⊤ at hpath
    simpa using hpath.symm
  · simp [terminalLeftPath, ht]

/-- Applying the terminal-left modification twice has the same effect as
applying it once. -/
theorem terminalLeftPath_idempotent (path : CadlagPath unitInterval ℝ) :
    terminalLeftPath (terminalLeftPath path) = terminalLeftPath path :=
  terminalLeftPath_eq_self_of_mem_space _ (terminalLeftPath_mem_space path)

end Skorokhod

end
