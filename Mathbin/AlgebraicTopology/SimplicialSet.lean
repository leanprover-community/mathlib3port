/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz

! This file was ported from Lean 3 source module algebraic_topology.simplicial_set
! leanprover-community/mathlib commit f2b757fc5c341d88741b9c4630b1e8ba973c5726
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.SimplicialObject
import Mathbin.AlgebraicTopology.TopologicalSimplex
import Mathbin.CategoryTheory.Limits.Presheaf
import Mathbin.CategoryTheory.Limits.Types
import Mathbin.CategoryTheory.Yoneda
import Mathbin.Topology.Category.Top.Limits.Basic

/-!
A simplicial set is just a simplicial object in `Type`,
i.e. a `Type`-valued presheaf on the simplex category.

(One might be tempted to call these "simplicial types" when working in type-theoretic foundations,
but this would be unnecessarily confusing given the existing notion of a simplicial type in
homotopy type theory.)

We define the standard simplices `Δ[n]` as simplicial sets,
and their boundaries `∂Δ[n]` and horns `Λ[n, i]`.
(The notations are available via `open_locale simplicial`.)

## Future work

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

There isn't yet a complete API for simplices, boundaries, and horns.
As an example, we should have a function that constructs
from a non-surjective order preserving function `fin n → fin n`
a morphism `Δ[n] ⟶ ∂Δ[n]`.
-/


universe v u

open CategoryTheory CategoryTheory.Limits

open Simplicial

#print SSet /-
/-- The category of simplicial sets.
This is the category of contravariant functors from
`simplex_category` to `Type u`. -/
def SSet : Type (u + 1) :=
  SimplicialObject (Type u)deriving LargeCategory, Limits.HasLimits, Limits.HasColimits
#align sSet SSet
-/

namespace SSet

#print SSet.standardSimplex /-
/-- The `n`-th standard simplex `Δ[n]` associated with a nonempty finite linear order `n`
is the Yoneda embedding of `n`. -/
def standardSimplex : SimplexCategory ⥤ SSet :=
  yoneda
#align sSet.standard_simplex SSet.standardSimplex
-/

-- mathport name: standard_simplex
scoped[Simplicial] notation "Δ[" n "]" => SSet.standardSimplex.obj (SimplexCategory.mk n)

instance : Inhabited SSet :=
  ⟨Δ[0]⟩

section

/- warning: sSet.as_order_hom -> SSet.asOrderHom is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {m : Opposite.{1} SimplexCategory}, (CategoryTheory.Functor.obj.{0, 0, 0, 1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) Type CategoryTheory.types.{0} (CategoryTheory.Functor.obj.{0, 0, 0, 1} SimplexCategory SimplexCategory.smallCategory SSet.{0} SSet.largeCategory.{0} SSet.standardSimplex (SimplexCategory.mk n)) m) -> (OrderHom.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory m)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory m)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory m)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (SimplexCategory.len (SimplexCategory.mk n)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (SimplexCategory.len (SimplexCategory.mk n)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall {n : Nat} {m : Opposite.{1} SimplexCategory}, (Prefunctor.obj.{1, 1, 0, 1} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) Type (CategoryTheory.CategoryStruct.toQuiver.{0, 1} Type (CategoryTheory.Category.toCategoryStruct.{0, 1} Type CategoryTheory.types.{0})) (CategoryTheory.Functor.toPrefunctor.{0, 0, 0, 1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) Type CategoryTheory.types.{0} (Prefunctor.obj.{1, 1, 0, 1} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) SSet.{0} (CategoryTheory.CategoryStruct.toQuiver.{0, 1} SSet.{0} (CategoryTheory.Category.toCategoryStruct.{0, 1} SSet.{0} SSet.largeCategory.{0})) (CategoryTheory.Functor.toPrefunctor.{0, 0, 0, 1} SimplexCategory SimplexCategory.smallCategory SSet.{0} SSet.largeCategory.{0} SSet.standardSimplex) (SimplexCategory.mk n))) m) -> (OrderHom.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory m)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory m)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instPartialOrderFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (SimplexCategory.len (Opposite.unop.{1} SimplexCategory m)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instPartialOrderFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))
Case conversion may be inaccurate. Consider using '#align sSet.as_order_hom SSet.asOrderHomₓ'. -/
/-- The `m`-simplices of the `n`-th standard simplex are
the monotone maps from `fin (m+1)` to `fin (n+1)`. -/
def asOrderHom {n} {m} (α : Δ[n].obj m) : OrderHom (Fin (m.unop.len + 1)) (Fin (n + 1)) :=
  α.toOrderHom
#align sSet.as_order_hom SSet.asOrderHom

end

#print SSet.boundary /-
/-- The boundary `∂Δ[n]` of the `n`-th standard simplex consists of
all `m`-simplices of `standard_simplex n` that are not surjective
(when viewed as monotone function `m → n`). -/
def boundary (n : ℕ) : SSet
    where
  obj m := { α : Δ[n].obj m // ¬Function.Surjective (asOrderHom α) }
  map m₁ m₂ f α :=
    ⟨f.unop ≫ (α : Δ[n].obj m₁), by intro h; apply α.property; exact Function.Surjective.of_comp h⟩
#align sSet.boundary SSet.boundary
-/

-- mathport name: sSet.boundary
scoped[Simplicial] notation "∂Δ[" n "]" => SSet.boundary n

/- warning: sSet.boundary_inclusion -> SSet.boundaryInclusion is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Quiver.Hom.{1, 1} SSet.{0} (CategoryTheory.CategoryStruct.toQuiver.{0, 1} SSet.{0} (CategoryTheory.Category.toCategoryStruct.{0, 1} SSet.{0} SSet.largeCategory.{0})) (SSet.boundary n) (CategoryTheory.Functor.obj.{0, 0, 0, 1} SimplexCategory SimplexCategory.smallCategory SSet.{0} SSet.largeCategory.{0} SSet.standardSimplex (SimplexCategory.mk n))
but is expected to have type
  forall (n : Nat), Quiver.Hom.{1, 1} SSet.{0} (CategoryTheory.CategoryStruct.toQuiver.{0, 1} SSet.{0} (CategoryTheory.Category.toCategoryStruct.{0, 1} SSet.{0} SSet.largeCategory.{0})) (SSet.boundary n) (Prefunctor.obj.{1, 1, 0, 1} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) SSet.{0} (CategoryTheory.CategoryStruct.toQuiver.{0, 1} SSet.{0} (CategoryTheory.Category.toCategoryStruct.{0, 1} SSet.{0} SSet.largeCategory.{0})) (CategoryTheory.Functor.toPrefunctor.{0, 0, 0, 1} SimplexCategory SimplexCategory.smallCategory SSet.{0} SSet.largeCategory.{0} SSet.standardSimplex) (SimplexCategory.mk n))
Case conversion may be inaccurate. Consider using '#align sSet.boundary_inclusion SSet.boundaryInclusionₓ'. -/
/-- The inclusion of the boundary of the `n`-th standard simplex into that standard simplex. -/
def boundaryInclusion (n : ℕ) : ∂Δ[n] ⟶ Δ[n] where app m (α : { α : Δ[n].obj m // _ }) := α
#align sSet.boundary_inclusion SSet.boundaryInclusion

#print SSet.horn /-
/-- `horn n i` (or `Λ[n, i]`) is the `i`-th horn of the `n`-th standard simplex, where `i : n`.
It consists of all `m`-simplices `α` of `Δ[n]`
for which the union of `{i}` and the range of `α` is not all of `n`
(when viewing `α` as monotone function `m → n`). -/
def horn (n : ℕ) (i : Fin (n + 1)) : SSet
    where
  obj m := { α : Δ[n].obj m // Set.range (asOrderHom α) ∪ {i} ≠ Set.univ }
  map m₁ m₂ f α :=
    ⟨f.unop ≫ (α : Δ[n].obj m₁), by
      intro h; apply α.property
      rw [Set.eq_univ_iff_forall] at h⊢; intro j
      apply Or.imp _ id (h j)
      intro hj
      exact Set.range_comp_subset_range _ _ hj⟩
#align sSet.horn SSet.horn
-/

-- mathport name: sSet.horn
scoped[Simplicial] notation "Λ[" n ", " i "]" => SSet.horn (n : ℕ) i

/- warning: sSet.horn_inclusion -> SSet.hornInclusion is a dubious translation:
lean 3 declaration is
  forall (n : Nat) (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), Quiver.Hom.{1, 1} SSet.{0} (CategoryTheory.CategoryStruct.toQuiver.{0, 1} SSet.{0} (CategoryTheory.Category.toCategoryStruct.{0, 1} SSet.{0} SSet.largeCategory.{0})) (SSet.horn n i) (CategoryTheory.Functor.obj.{0, 0, 0, 1} SimplexCategory SimplexCategory.smallCategory SSet.{0} SSet.largeCategory.{0} SSet.standardSimplex (SimplexCategory.mk n))
but is expected to have type
  forall (n : Nat) (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), Quiver.Hom.{1, 1} SSet.{0} (CategoryTheory.CategoryStruct.toQuiver.{0, 1} SSet.{0} (CategoryTheory.Category.toCategoryStruct.{0, 1} SSet.{0} SSet.largeCategory.{0})) (SSet.horn n i) (Prefunctor.obj.{1, 1, 0, 1} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) SSet.{0} (CategoryTheory.CategoryStruct.toQuiver.{0, 1} SSet.{0} (CategoryTheory.Category.toCategoryStruct.{0, 1} SSet.{0} SSet.largeCategory.{0})) (CategoryTheory.Functor.toPrefunctor.{0, 0, 0, 1} SimplexCategory SimplexCategory.smallCategory SSet.{0} SSet.largeCategory.{0} SSet.standardSimplex) (SimplexCategory.mk n))
Case conversion may be inaccurate. Consider using '#align sSet.horn_inclusion SSet.hornInclusionₓ'. -/
/-- The inclusion of the `i`-th horn of the `n`-th standard simplex into that standard simplex. -/
def hornInclusion (n : ℕ) (i : Fin (n + 1)) : Λ[n, i] ⟶ Δ[n]
    where app m (α : { α : Δ[n].obj m // _ }) := α
#align sSet.horn_inclusion SSet.hornInclusion

section Examples

open Simplicial

#print SSet.S1 /-
/-- The simplicial circle. -/
noncomputable def S1 : SSet :=
  Limits.colimit <|
    Limits.parallelPair (standardSimplex.map <| SimplexCategory.δ 0 : Δ[0] ⟶ Δ[1])
      (standardSimplex.map <| SimplexCategory.δ 1)
#align sSet.S1 SSet.S1
-/

end Examples

#print SSet.Truncated /-
/-- Truncated simplicial sets. -/
def Truncated (n : ℕ) :=
  SimplicialObject.Truncated (Type u) n deriving LargeCategory, Limits.HasLimits, Limits.HasColimits
#align sSet.truncated SSet.Truncated
-/

#print SSet.sk /-
/-- The skeleton functor on simplicial sets. -/
def sk (n : ℕ) : SSet ⥤ SSet.Truncated n :=
  SimplicialObject.sk n
#align sSet.sk SSet.sk
-/

instance {n} : Inhabited (SSet.Truncated n) :=
  ⟨(sk n).obj <| Δ[0]⟩

#print SSet.Augmented /-
/-- The category of augmented simplicial sets, as a particular case of
augmented simplicial objects. -/
abbrev Augmented :=
  SimplicialObject.Augmented (Type u)
#align sSet.augmented SSet.Augmented
-/

namespace Augmented

#print SSet.Augmented.standardSimplex /-
/-- The functor which sends `[n]` to the simplicial set `Δ[n]` equipped by
the obvious augmentation towards the terminal object of the category of sets. -/
@[simps]
noncomputable def standardSimplex : SimplexCategory ⥤ SSet.Augmented
    where
  obj Δ :=
    { left := SSet.standardSimplex.obj Δ
      right := terminal _
      Hom := { app := fun Δ' => terminal.from _ } }
  map Δ₁ Δ₂ θ :=
    { left := SSet.standardSimplex.map θ
      right := terminal.from _ }
#align sSet.augmented.standard_simplex SSet.Augmented.standardSimplex
-/

end Augmented

end SSet

#print TopCat.toSSet /-
/-- The functor associating the singular simplicial set to a topological space. -/
def TopCat.toSSet : TopCat ⥤ SSet :=
  ColimitAdj.restrictedYoneda SimplexCategory.toTop
#align Top.to_sSet TopCat.toSSet
-/

#print SSet.toTop /-
/-- The geometric realization functor. -/
noncomputable def SSet.toTop : SSet ⥤ TopCat :=
  ColimitAdj.extendAlongYoneda SimplexCategory.toTop
#align sSet.to_Top SSet.toTop
-/

#print sSetTopAdj /-
/-- Geometric realization is left adjoint to the singular simplicial set construction. -/
noncomputable def sSetTopAdj : SSet.toTop ⊣ TopCat.toSSet :=
  ColimitAdj.yonedaAdjunction _
#align sSet_Top_adj sSetTopAdj
-/

#print SSet.toTopSimplex /-
/-- The geometric realization of the representable simplicial sets agree
  with the usual topological simplices. -/
noncomputable def SSet.toTopSimplex :
    (yoneda : SimplexCategory ⥤ _) ⋙ SSet.toTop ≅ SimplexCategory.toTop :=
  ColimitAdj.isExtensionAlongYoneda _
#align sSet.to_Top_simplex SSet.toTopSimplex
-/

