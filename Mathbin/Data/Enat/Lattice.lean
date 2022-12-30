/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module data.enat.lattice
! leanprover-community/mathlib commit 09597669f02422ed388036273d8848119699c22f
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

