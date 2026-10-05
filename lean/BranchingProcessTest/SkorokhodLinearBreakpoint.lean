/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Topology.Cadlag.Skorokhod.TimeChange.Breakpoint

#print axioms Skorokhod.TimeChange.linearBreakpoint
#print axioms Skorokhod.TimeChange.linearBreakpoint_distortion_le_abs

example (target source : ℝ) (htarget : 0 < target) (htarget_one : target < 1)
    (hsource : 0 < source) (hsource_one : source < 1) :
    Skorokhod.TimeChange.linearBreakpoint target source htarget htarget_one
      hsource hsource_one ⊥ = ⊥ := by
  simp

example (target source : ℝ) (htarget : 0 < target) (htarget_one : target < 1)
    (hsource : 0 < source) (hsource_one : source < 1) :
    Skorokhod.TimeChange.linearBreakpoint target source htarget htarget_one
      hsource hsource_one ⊤ = ⊤ := by
  simp

example (target source : ℝ) (htarget : 0 < target) (htarget_one : target < 1)
    (hsource : 0 < source) (hsource_one : source < 1) :
    Skorokhod.TimeChange.linearBreakpoint target source htarget htarget_one
      hsource hsource_one ⟨source, ⟨hsource.le, hsource_one.le⟩⟩ =
      ⟨target, ⟨htarget.le, htarget_one.le⟩⟩ :=
  Skorokhod.TimeChange.linearBreakpoint_apply_source target source
    htarget htarget_one hsource hsource_one
