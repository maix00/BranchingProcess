#!/bin/sh
set -eu

# Rebuild the local publish branch from the canonical lean/ subtree.
# This intentionally does not push anywhere.
root=$(git rev-parse --show-toplevel)
cd "$root"
branch=$(git symbolic-ref --quiet --short HEAD || true)
if [ "$branch" != master ]; then
  printf 'Skipping subtree refresh on %s\n' "${branch:-detached HEAD}"
  exit 0
fi
commit=$(git subtree split --prefix=lean)
git branch -f branchingprocess-publish "$commit" >/dev/null
printf 'Updated branchingprocess-publish to %s\n' "$commit"
