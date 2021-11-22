
/-!
# Reserved notation

This file is imported by `logic.basic` and `logic.relator` to place it at the top of the
import graph.

We place all of `mathlib`'s reserved notation in this file so that users will know not to
use them as e.g. variable names without needing to import the specific file where they
are defined.

-/


-- error in Tactic.ReservedNotation: ././Mathport/Syntax/Translate/Basic.lean:264:9: unsupported: advanced prec syntax
reserve prefix `#where`:max

