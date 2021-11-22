You should use this repository to inspect the Lean 4 files that `mathport` has generated from mathlib3.
After running `lake build`, you should be able to open `.lean` files from the `Mathbin` directory in VS Code.
Please expect *many* errors at this stage.

Although the `Mathbin` directory is committed in the repository,
at this stage you should not attempt to make any changes on the master branch.
If you delete the `Mathbin` directory,
then running `lake build` will download a new copy from the `mathport` release page.

It's fine, however, to make branches containing "by-hand" edits,
if you want to be able to link to diffs when reporting issues in `mathport`.