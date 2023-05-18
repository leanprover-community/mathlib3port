/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala

! This file was ported from Lean 3 source module algebraic_topology.fundamental_groupoid.punit
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Punit
import Mathbin.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Fundamental groupoid of punit

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

/- warning: fundamental_groupoid.punit_equiv_discrete_punit -> FundamentalGroupoid.punitEquivDiscretePunit is a dubious translation:
lean 3 declaration is
  CategoryTheory.Equivalence.{u1, u2, u1, u2} (FundamentalGroupoid.{u1} PUnit.{succ u1}) (CategoryTheory.Groupoid.toCategory.{u1, u1} (FundamentalGroupoid.{u1} PUnit.{succ u1}) (FundamentalGroupoid.CategoryTheory.groupoid.{u1} PUnit.{succ u1} PUnit.topologicalSpace.{u1})) (CategoryTheory.Discrete.{u2} PUnit.{succ u2}) (CategoryTheory.discreteCategory.{u2} PUnit.{succ u2})
but is expected to have type
  CategoryTheory.Equivalence.{u1, u2, u1, u2} (FundamentalGroupoid.{u1} PUnit.{succ u1}) (CategoryTheory.Discrete.{u2} PUnit.{succ u2}) (CategoryTheory.Groupoid.toCategory.{u1, u1} (FundamentalGroupoid.{u1} PUnit.{succ u1}) (FundamentalGroupoid.instGroupoidFundamentalGroupoid.{u1} PUnit.{succ u1} instTopologicalSpacePUnit.{u1})) (CategoryTheory.discreteCategory.{u2} PUnit.{succ u2})
Case conversion may be inaccurate. Consider using '#align fundamental_groupoid.punit_equiv_discrete_punit FundamentalGroupoid.punitEquivDiscretePunitₓ'. -/
/-- Equivalence of groupoids between fundamental groupoid of punit and punit -/
def punitEquivDiscretePunit : FundamentalGroupoid PUnit.{u + 1} ≌ Discrete PUnit.{v + 1} :=
  Equivalence.mk (Functor.star _) ((CategoryTheory.Functor.const _).obj PUnit.unit)
    (NatIso.ofComponents (fun _ => eqToIso (by decide)) fun _ _ _ => by decide)
    (Functor.pUnitExt _ _)
#align fundamental_groupoid.punit_equiv_discrete_punit FundamentalGroupoid.punitEquivDiscretePunit

end FundamentalGroupoid

