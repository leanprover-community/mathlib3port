import Mathbin.Data.Fintype.Basic
import Mathbin.Control.EquivFunctor

/-!
# `equiv_functor` instances

We derive some `equiv_functor` instances, to enable `equiv_rw` to rewrite under these functions.
-/


open Equivₓ

instance equivFunctorUnique : EquivFunctor Unique where
  map := fun α β e => Equivₓ.uniqueCongr e

instance equivFunctorPerm : EquivFunctor perm where
  map := fun α β e p => (e.symm.trans p).trans e

instance equivFunctorFinset : EquivFunctor Finset where
  map := fun α β e s => s.map e.to_embedding

instance equivFunctorFintype : EquivFunctor Fintype where
  map := fun α β e s => Fintype.ofBijective e e.bijective

