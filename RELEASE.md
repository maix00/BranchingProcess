# Standalone Lean library release

The Lean library is published from the `lean/` subtree of the canonical
repository.  The standalone repository is
`https://github.com/maix00/BranchingProcess.git`; its `main` branch is the
published subtree, not the LaTeX thesis checkout.

## Release checklist

Run these commands from the canonical checkout on `master`:

```sh
cd lean
lake build
cd ..
git diff --check
git status --short --untracked-files=all
./scripts/update-branchingprocess-subtree.sh --push
```

The last command refuses a dirty worktree and creates a subtree commit with
`git subtree split --prefix=lean`. It pushes that commit to a temporary
preflight branch on the standalone repository, waits for the `Lake build`
workflow to pass on that exact commit, then makes an ordinary fast-forward
push to `main` and removes the temporary branch. A failed or missing workflow
prevents publication, and a divergent remote is reported as an error instead
of being overwritten. Publishing requires an authenticated GitHub CLI (`gh`)
session with permission to push branches and read workflow results.

The remote and target branch can be changed explicitly when needed:

```sh
BRANCHINGPROCESS_REMOTE=branchingprocess \
BRANCHINGPROCESS_BRANCH=main \
./scripts/update-branchingprocess-subtree.sh --push
```

Do not release uncommitted files.  The Lake package version and exact
dependency revisions are recorded in `lakefile.toml`, `lake-manifest.json`,
and `lean-toolchain`; a release is valid only after the pinned `lake build`
and GitHub preflight workflow pass.
