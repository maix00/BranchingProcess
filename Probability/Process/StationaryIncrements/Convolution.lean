/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Probability.Process.StationaryIncrements.Basic

/-!
# Convolution of stationary independent increment laws

## Public declarations

- `ProbabilityTheory.HasStationaryIncrements.map_add_eq_conv_of_indepIncrements`:
  for a zero-start process with stationary and independent increments,
  $\operatorname{Law}(X_{s+t})=\operatorname{Law}(X_s)*\operatorname{Law}(X_t)$.
  The result is stated for measurable additive-group-valued processes and
  ordered additive time monoids; it requires no path regularity.
-/

open MeasureTheory
open scoped MeasureTheory

@[expose] public section

namespace ProbabilityTheory.HasStationaryIncrements

variable {Ω Time E : Type*} [MeasurableSpace Ω]
  [Preorder Time] [AddMonoid Time]
  [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableSub₂ E]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Time → Ω → E}

/-- A zero-start process with stationary and independent increments has
convolution-semigroup one-time laws. The coordinate measurability hypothesis
ensures the process marginals and the interval-increment law are well-defined
pushforward measures. -/
theorem map_add_eq_conv_of_indepIncrements
    (hstationary : HasStationaryIncrements X P)
    (hindep : HasIndepIncrements X P)
    (hstart : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hmeas : ∀ t, AEMeasurable (fun ω => X t ω) P)
    {s t : Time} (hs : 0 ≤ s) (hst : s ≤ s + t) :
    P.map (fun ω => X (s + t) ω) =
      (P.map fun ω => X s ω) ∗ (P.map fun ω => X t ω) := by
  let increment : Ω → E := fun ω => X (s + t) ω - X s ω
  have h_indep : (fun ω => X s ω) ⟂ᵢ[P] increment :=
    hindep.indepFun_eval_sub (r := 0) (s := s) (t := s + t) hs hst hstart
  have h_increment_law : IdentDistrib increment (fun ω => X t ω) P P :=
    hstationary.identDistrib_increment_of_ae_start hstart s t
  have h_increment_meas : AEMeasurable increment P := by
    exact (hmeas (s + t)).sub (hmeas s)
  have h_sum : (fun ω => X s ω + increment ω) =ᵐ[P]
      fun ω => X (s + t) ω := by
    filter_upwards [] with ω
    dsimp [increment]
    abel
  calc
    P.map (fun ω => X (s + t) ω) =
        P.map (fun ω => X s ω + increment ω) :=
      (Measure.map_congr h_sum).symm
    _ = (P.map fun ω => X s ω) ∗ (P.map increment) :=
      h_indep.map_add_eq_map_conv_map₀ (hmeas s) h_increment_meas
    _ = (P.map fun ω => X s ω) ∗ (P.map fun ω => X t ω) := by
      rw [h_increment_law.map_eq]

end ProbabilityTheory.HasStationaryIncrements

end
