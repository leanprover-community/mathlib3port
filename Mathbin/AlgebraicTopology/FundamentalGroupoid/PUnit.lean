/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import CategoryTheory.PUnit
import AlgebraicTopology.FundamentalGroupoid.Basic

#align_import algebraic_topology.fundamental_groupoid.punit from "leanprover-community/mathlib"@"33c67ae661dd8988516ff7f247b0be3018cdd952"

/-!
# Fundamental groupoid of punit

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The fundamental groupoid of punit is naturally isomorphic to `category_theory.discrete punit`
-/


noncomputable section

open CategoryTheory

universe u v

namespace Path

instance : Subsingleton (Path PUnit.unit PUnit.unit) :=
  ⟨fun x y => by ext⟩

end Path

namespace FundamentalGroupoid

instance {x y : FundamentalGroupoid PUnit} : Subsingleton (x ⟶ y) :=
  by
  convert_to Subsingleton (Path.Homotopic.Quotient PUnit.unit PUnit.unit)
  · congr <;> apply PUnit.eq_punit
  apply Quotient.subsingleton

#print FundamentalGroupoid.punitEquivDiscretePUnit /-
/-- Equivalence of groupoids between fundamental groupoid of punit and punit -/
def punitEquivDiscretePUnit : FundamentalGroupoid PUnit.{u + 1} ≌ Discrete PUnit.{v + 1} :=
  Equivalence.mk (Functor.star _) ((CategoryTheory.Functor.const _).obj PUnit.unit)
    (NatIso.ofComponents (fun _ => eqToIso (by decide)) fun _ _ _ => by decide)
    (Functor.punitExt _ _)
#align fundamental_groupoid.punit_equiv_discrete_punit FundamentalGroupoid.punitEquivDiscretePUnit
-/

end FundamentalGroupoid

