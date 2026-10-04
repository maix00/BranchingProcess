/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Analysis.Fourier.CosineTauberian.Kernel

/-!
# Compatibility names for the cosine Tauberian kernel

The kernel is owned by the analysis layer. This module preserves the former
probability namespace for downstream characteristic-function applications.
-/

@[expose] public section

namespace ProbabilityTheory

export Analysis.Fourier.CosineTauberian
  (cosineTauberianKernel
    continuous_cosineTauberianKernel
    abs_cosineTauberianKernel_le
    cosineTauberianKernel_eq_quotient
    abs_cosineTauberianKernel_le_tail
    integrableOn_rpow_mul_abs_cosineTauberianKernel
    integrableOn_cosineTauberianKernel)

end ProbabilityTheory

end
