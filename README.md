You should use this repository to inspect the Lean 4 files that `mathport` has generated from mathlib3.
Please run `lake build` first, to download a copy of the generated `.olean` files.
After that, you should be able to open any of the `.lean` files under the `Mathbin` directory.
These will use binported `.olean`s for the imports, and there is a synported `.lean` file for each file in mathlib3.
Please expect *many* errors at this stage.

Although the `Mathbin` directory is committed in the repository,
at this stage you should not attempt to make any changes on the master branch.

If you delete the `Mathbin` directory,
then running `lake build` will download a new copy from the `mathport` release page.
(It's probably safest to delete `mathlib3-synport.tar.gz*`, and probably `lean_packages`, too...
This requires further automation.)

It's fine, however, to make branches containing "by-hand" edits,
if you want to be able to link to diffs when reporting issues in `mathport`.