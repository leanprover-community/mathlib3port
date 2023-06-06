#!/usr/bin/env bash

echo Updates to the latest revision in the lean3port repo
echo and creates a bump commit.

set -ex

lake resolve-deps
pushd lake-packages/lean3port
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
lake update

rm -rf Mathbin Archive Counterexamples
for lib in mathlib3 archive counterexamples; do
  curl -qsSL https://github.com/leanprover-community/mathport/releases/download/$tag/$lib-synport.tar.gz \
    | tar xz
done

lake print-paths
cp build/lib/upstream-rev .
upstream_rev=$(cat upstream-rev)
sed -i 's|\(.* mathlib commit:\).*|\1 '"[\`$upstream_rev\`](https://github.com/leanprover-community/mathlib/commit/$upstream_rev)|" README.md

git add Mathbin Archive Counterexamples upstream-rev README.md lake-manifest.json
git commit -am "bump to $tag

mathlib commit https://github.com/leanprover-community/mathlib/commit/$upstream_rev" || true that
