import Mathbin.Data.Fintype.Basic 
import Mathbin.Control.EquivFunctor

/-!
# `equiv_functor` instances

We derive some `equiv_functor` instances, to enable `equiv_rw` to rewrite under these functions.
-/


open Equiv

instance equivFunctorUnique : EquivFunctor Unique :=
  { map := fun α β e => Equiv.uniqueCongr e }

instance equivFunctorPerm : EquivFunctor perm :=
  { map := fun α β e p => (e.symm.trans p).trans e }

instance equivFunctorFinset : EquivFunctor Finset :=
  { map := fun α β e s => s.map e.to_embedding }

instance equivFunctorFintype : EquivFunctor Fintype :=
  { map :=
      fun α β e s =>
        by 
          exactI Fintype.ofBijective e e.bijective }

