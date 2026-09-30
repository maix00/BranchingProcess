#!/bin/sh
set -eu

# Rebuild the local publish branch from the canonical lean/ subtree.
# Pass --push to publish the resulting fast-forward to the standalone remote.
root=$(git rev-parse --show-toplevel)
cd "$root"
branch=$(git symbolic-ref --quiet --short HEAD || true)
if [ "$branch" != master ]; then
  printf 'Skipping subtree refresh on %s\n' "${branch:-detached HEAD}"
  exit 0
fi
push=0
if [ "${1:-}" = "--push" ]; then
  push=1
elif [ "${1:-}" != "" ]; then
  printf 'Usage: %s [--push]\n' "$0" >&2
  exit 2
fi
if [ "$push" -eq 1 ] && [ -n "$(git status --porcelain --untracked-files=all)" ]; then
  printf 'Refusing to publish with uncommitted changes; commit or remove them first.\n' >&2
  exit 1
fi
commit=$(git subtree split --prefix=lean)
git branch -f branchingprocess-publish "$commit" >/dev/null
printf 'Updated branchingprocess-publish to %s\n' "$commit"
if [ "$push" -eq 1 ]; then
  remote=${BRANCHINGPROCESS_REMOTE:-branchingprocess}
  target=${BRANCHINGPROCESS_BRANCH:-main}
  git push "$remote" "$commit:refs/heads/$target"
fi
