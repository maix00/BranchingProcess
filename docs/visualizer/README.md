# BranchingProcess Lab

This directory is a static, manifest-driven visual documentation prototype for
the Lean library. It keeps three layers separate:

- `manifest.json` selects the definitions and theorems shown by the site.
- `app.js` renders the selected declarations and runs seeded browser demos.
- `scripts/check-visualizer-manifest.mjs` asks the pinned Lean project to
  `#check` every selected declaration before a Pages build.

The browser demos are executable illustrations. They are not substitutes for
measure-theoretic proofs or for the open asymptotic theorems recorded in the
formalization checklist.

## Local preview

From the Lean package directory (`lean/` in this repository and the repository
root in the standalone package):

```sh
node scripts/check-visualizer-manifest.mjs
python3 -m http.server 4173 --directory docs/visualizer
```

Open <http://localhost:4173>. Query parameters can select a surface directly:

```text
?page=library&object=walk-position
?page=simulation&demo=corridor&object=m2-energy
```

To add another page entry, add an object to `manifest.json`, include its exact
Lean name and module, then optionally attach it to a demo's `objects` list.
The library index, inspector, dependency list, and source link are generated
from the same entry.
