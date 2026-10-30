# External Lean dependencies

`Mathlib/` is a Git submodule pinned to
[`maix00/mathlib4`](https://github.com/maix00/mathlib4), commit
`380f2aafb622cb2c1c93dac545b6389083c68c51`. Lake uses this local
checkout, so upstreamable changes can be developed in the fork and proposed
to [`leanprover-community/mathlib4`](https://github.com/leanprover-community/mathlib4)
without changing the dependency layout.

`BrownianMotion/` is a Git submodule pinned to
[`maix00/brownian-motion`](https://github.com/maix00/brownian-motion),
commit `d6d901b6df592a543b7edf221f92d2ee6760d18d` on the
`codex/mathlib-435-continuity` branch. That fork descends from
[`RemyDegenne/brownian-motion`](https://github.com/RemyDegenne/brownian-motion),
commit `0d5b6eb928e616d3b1f774ad7d233c167d9f42c9`.

The fork adjusts its Kolmogorov–Chentsov continuity modules for this
repository's pinned Mathlib revision. Lake uses this tracked checkout as a
local package through `lakefile.toml`. Clone with submodules, or run
`git submodule update --init --recursive` before building.

The full upstream package includes modules beyond the current import graph.
Those modules have not all been adapted to Mathlib 4.35.
