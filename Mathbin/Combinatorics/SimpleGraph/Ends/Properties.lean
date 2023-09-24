/-
Copyright (c) 2022 Anand Rao, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao, Rémi Bottinelli
-/
import Combinatorics.SimpleGraph.Ends.Defs

#align_import combinatorics.simple_graph.ends.properties from "leanprover-community/mathlib"@"50251fd6309cca5ca2e747882ffecd2729f38c5d"

/-!
# Properties of the ends of graphs

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

