/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.category.Ring.adjunctions
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.RingCat.Basic
import Mathbin.Data.MvPolynomial.CommRing

/-!
Multivariable polynomials on a type is the left adjoint of the
forgetful functor from commutative rings to types.
-/


noncomputable section

universe u

open MvPolynomial

open CategoryTheory

namespace CommRingCat

open Classical

/-- The free functor `Type u ⥤ CommRing` sending a type `X` to the multivariable (commutative)
polynomials with variables `x : X`.
-/
def free : Type u ⥤ CommRingCat.{u}
    where
  obj α := of (MvPolynomial α ℤ)
  map X Y f := (↑(rename f : _ →ₐ[ℤ] _) : MvPolynomial X ℤ →+* MvPolynomial Y ℤ)
  -- TODO these next two fields can be done by `tidy`, but the calls in `dsimp` and `simp` it
  -- generates are too slow.
  map_id' X := RingHom.ext <| rename_id
  map_comp' X Y Z f g := RingHom.ext fun p => (rename_rename f g p).symm
#align CommRing.free CommRingCat.free

@[simp]
theorem free_obj_coe {α : Type u} : (free.obj α : Type u) = MvPolynomial α ℤ :=
  rfl
#align CommRing.free_obj_coe CommRingCat.free_obj_coe

@[simp]
theorem free_map_coe {α β : Type u} {f : α → β} : ⇑(free.map f) = rename f :=
  rfl
#align CommRing.free_map_coe CommRingCat.free_map_coe

/-- The free-forgetful adjunction for commutative rings.
-/
def adj : free ⊣ forget CommRingCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X R => homEquiv
      hom_equiv_naturality_left_symm' := fun _ _ Y f g =>
        RingHom.ext fun x => eval₂_cast_comp f (Int.castRingHom Y) g x }
#align CommRing.adj CommRingCat.adj

instance : IsRightAdjoint (forget CommRingCat.{u}) :=
  ⟨_, adj⟩

end CommRingCat

