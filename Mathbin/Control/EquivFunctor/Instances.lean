import Mathbin.Data.Fintype.Basic
import Mathbin.Control.EquivFunctor

/-!
# `equiv_functor` instances

We derive some `equiv_functor` instances, to enable `equiv_rw` to rewrite under these functions.
-/


open Equivₓ

-- failed to format: format: uncaught backtrack exception
instance equivFunctorUnique : EquivFunctor Unique where map α β e := Equivₓ.uniqueCongr e

-- failed to format: format: uncaught backtrack exception
instance equivFunctorPerm : EquivFunctor perm where map α β e p := ( e.symm.trans p ) . trans e

-- failed to format: format: uncaught backtrack exception
instance equivFunctorFinset : EquivFunctor Finset where map α β e s := s.map e.to_embedding

-- failed to format: format: uncaught backtrack exception
instance equivFunctorFintype : EquivFunctor Fintype where map α β e s := by exact Fintype.ofBijective e e.bijective

