/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module control.equiv_functor.instances
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.Control.EquivFunctor

/-!
# `equiv_functor` instances

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We derive some `equiv_functor` instances, to enable `equiv_rw` to rewrite under these functions.
-/


open Equiv

#print EquivFunctorUnique /-
instance EquivFunctorUnique : EquivFunctor Unique where map α β e := Equiv.uniqueCongr e
#align equiv_functor_unique EquivFunctorUnique
-/

#print EquivFunctorPerm /-
instance EquivFunctorPerm : EquivFunctor Perm where map α β e p := (e.symm.trans p).trans e
#align equiv_functor_perm EquivFunctorPerm
-/

#print EquivFunctorFinset /-
-- There is a classical instance of `is_lawful_functor finset` available,
-- but we provide this computable alternative separately.
instance EquivFunctorFinset : EquivFunctor Finset where map α β e s := s.map e.toEmbedding
#align equiv_functor_finset EquivFunctorFinset
-/

#print EquivFunctorFintype /-
instance EquivFunctorFintype : EquivFunctor Fintype
    where map α β e s := Fintype.ofBijective e e.bijective
#align equiv_functor_fintype EquivFunctorFintype
-/

