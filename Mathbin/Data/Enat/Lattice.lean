/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module data.enat.lattice
! leanprover-community/mathlib commit 11bb0c9152e5d14278fb0ac5e0be6d50e2c8fa05
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Lattice
import Mathbin.Data.Enat.Basic

/-!
# Extended natural numbers form a complete linear order

This instance is not in `data.enat.basic` to avoid dependency on `finset`s.
-/


deriving instance CompleteLinearOrder for Enat

