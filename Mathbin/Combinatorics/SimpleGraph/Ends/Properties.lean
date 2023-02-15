/-
Copyright (c) 2022 Anand Rao, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao, Rémi Bottinelli

! This file was ported from Lean 3 source module combinatorics.simple_graph.ends.properties
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.SimpleGraph.Ends.Defs

/-!
# Properties of the ends of graphs

This file is meant to contain results about the ends of (locally finite connected) graphs.

-/


variable {V : Type} (G : SimpleGraph V)

namespace SimpleGraph

instance [Finite V] : IsEmpty G.end :=
  ⟨by
    rintro ⟨s, _⟩
    cases nonempty_fintype V
    obtain ⟨v, h⟩ := (s <| Opposite.op Finset.univ).Nonempty
    exact
      set.disjoint_iff.mp (s _).disjoint_right
        ⟨by simp only [Opposite.unop_op, Finset.coe_univ], h⟩⟩

end SimpleGraph

