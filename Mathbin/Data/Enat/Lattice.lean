/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Data.Nat.Lattice
import Mathbin.Data.Enat.Basic

#align_import data.enat.lattice from "leanprover-community/mathlib"@"fac369018417f980cec5fcdafc766a69f88d8cfe"

/-!
# Extended natural numbers form a complete linear order

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This instance is not in `data.enat.basic` to avoid dependency on `finset`s.
-/


deriving instance CompleteLinearOrder for ENat

