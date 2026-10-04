/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Analysis.Fourier.CosineTauberian.Inversion
public import Probability.Distributions.CharacteristicFunction.Tauberian.Kernel.Basic

/-!
# Compatibility names for cosine Tauberian Fourier inversion

The profile and its Fourier identities are owned by the analysis layer. This
module preserves the former probability namespace for downstream applications.
-/

@[expose] public section

namespace ProbabilityTheory

export Analysis.Fourier.CosineTauberian
  (cosineTauberianProfile
    continuous_cosineTauberianProfile
    cosineTauberianProfile_gap_eq_cappedCubic
    integral_cosineTauberianKernel_cos
    integral_Ioi_cosineTauberianKernel_cos
    integral_Ioi_one_sub_cos_mul_cosineTauberianKernel)

end ProbabilityTheory

end
