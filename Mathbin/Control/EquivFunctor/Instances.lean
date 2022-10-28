/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.Control.EquivFunctor

/-!
# `equiv_functor` instances

We derive some `equiv_functor` instances, to enable `equiv_rw` to rewrite under these functions.
-/


open Equiv

instance equivFunctorUnique : EquivFunctor Unique where map α β e := Equiv.uniqueCongr e

instance equivFunctorPerm : EquivFunctor Perm where map α β e p := (e.symm.trans p).trans e

-- There is a classical instance of `is_lawful_functor finset` available,
-- but we provide this computable alternative separately.
instance equivFunctorFinset : EquivFunctor Finset where map α β e s := s.map e.toEmbedding

instance equivFunctorFintype : EquivFunctor Fintype where map α β e s := Fintype.ofBijective e e.bijective

