/-
This file imports many useful tactics ("the kitchen sink").

You can use `import tactic` at the beginning of your file to get everything.
(Although you may want to strip things down when you're polishing.)

Because this file imports some complicated tactics, it has many transitive dependencies
(which of course may not use `import tactic`, and must import selectively).

As (non-exhaustive) examples, these includes things like:
* algebra.group_power
* algebra.order.ring
* data.rat
* data.nat.prime
* data.list.perm
* data.set.lattice
* data.equiv.encodable.basic
* order.complete_lattice
-/
import Tactic.Basic
import Tactic.Abel
import Tactic.RingExp
import Tactic.NoncommRing
import Mathbin.Tactic.Linarith.Default
import Mathbin.Tactic.Omega.Default
import Tactic.Tfae
import Tactic.ApplyFun
import Tactic.IntervalCases
import Tactic.ReassocAxiom
import Tactic.Slice
import Tactic.SubtypeInstance
import Tactic.DeriveFintype
import Tactic.Group
import Tactic.CancelDenoms
import Tactic.Zify
import Tactic.Transport
import Tactic.UnfoldCases
import Tactic.FieldSimp
import Tactic.LinearCombination
import Tactic.Polyrith
import Tactic.ExpandExists

#align_import tactic.default from "leanprover-community/mathlib"@"f9153b8a79eb28d07341706ddb18c02593eeb72a"

-- ensure basic tactics are available
-- ensure basic tactics are available
-- most likely useful only for category_theory
-- most likely useful only for category_theory
