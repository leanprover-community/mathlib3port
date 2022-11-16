#!/usr/bin/env bash

echo Updates to the latest revision in the lean3port repo
echo and creates a bump commit.

set -ex

lake print-paths
pushd lean_packages/lean3port
git fetch origin
git checkout origin/master
cp lean-toolchain ../..
lean3port_rev=$(git rev-parse HEAD)
tag=$(sed '/^def tag /!d;s/.*"\(.*\)"$/\1/' lakefile.lean)
popd

# We specify a suffix for `-i` for macos compatibility.
sed -i.bak '
  /^def tag / s/"\(.*\)"$/"'$tag'"/;
  /^require lean3port / s/@"\([^"]*\)"$/@"'$lean3port_rev'"/
' lakefile.lean
rm lakefile.lean.bak
rm -f lean_packages/manifest.json
lake update

rm -rf Mathbin
curl -qsSL https://github.com/leanprover-community/mathport/releases/download/$tag/mathlib3-synport.tar.gz \
  | tar xz

lake print-paths
cp build/lib/upstream-rev .
upstream_rev=$(cat upstream-rev)
sed -i 's|\(.* mathlib commit:\).*|\1 '"[\`$upstream_rev\`](https://github.com/leanprover-community/mathlib/commit/$upstream_rev)|" README.md

git add Mathbin upstream-rev README.md
git commit -am "bump to $tag

mathlib commit https://github.com/leanprover-community/mathlib/commit/$upstream_rev"
