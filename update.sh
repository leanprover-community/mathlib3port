#!/usr/bin/env bash

echo Updates to the latest revision in the lean3port repo
echo and creates a bump commit.

set -ex

pushd lean_packages/lean3port
git fetch origin
git checkout origin/master
cp lean-toolchain ../..
lean3port_rev=$(git rev-parse HEAD)
tag=$(sed '/^def tag /!d;s/.*"\(.*\)"$/\1/' lakefile.lean)
popd

sed -i '
  /^def tag / s/"\(.*\)"$/"'$tag'"/;
  /^require lean3port / s/@"\([^"]*\)"$/@"'$lean3port_rev'"/
' lakefile.lean
lake update

rm -rf Mathbin
curl -qsSL https://github.com/leanprover-community/mathport/releases/download/$tag/mathlib3-synport.tar.gz \
  | tar xz

git add Mathbin
git commit -am "bump to $tag"
