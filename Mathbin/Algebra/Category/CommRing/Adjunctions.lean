import Mathbin.Algebra.Category.CommRing.Basic 
import Mathbin.Data.MvPolynomial.CommRing

/-!
Multivariable polynomials on a type is the left adjoint of the
forgetful functor from commutative rings to types.
-/


noncomputable theory

universe u

open MvPolynomial

open CategoryTheory

namespace CommRingₓₓ

open_locale Classical

/--
The free functor `Type u ⥤ CommRing` sending a type `X` to the multivariable (commutative)
polynomials with variables `x : X`.
-/
def free : Type u ⥤ CommRingₓₓ.{u} :=
  { obj := fun α => of (MvPolynomial α ℤ),
    map := fun X Y f => («expr↑ » (rename f : _ →ₐ[ℤ] _) : MvPolynomial X ℤ →+* MvPolynomial Y ℤ),
    map_id' := fun X => RingHom.ext$ rename_id,
    map_comp' := fun X Y Z f g => RingHom.ext$ fun p => (rename_rename f g p).symm }

@[simp]
theorem free_obj_coe {α : Type u} : (free.obj α : Type u) = MvPolynomial α ℤ :=
  rfl

@[simp]
theorem free_map_coe {α β : Type u} {f : α → β} : «expr⇑ » (free.map f) = rename f :=
  rfl

/--
The free-forgetful adjunction for commutative rings.
-/
def adj : free ⊣ forget CommRingₓₓ.{u} :=
  adjunction.mk_of_hom_equiv
    { homEquiv := fun X R => hom_equiv,
      hom_equiv_naturality_left_symm' :=
        fun _ _ Y f g => RingHom.ext$ fun x => eval₂_cast_comp f (Int.castRingHom Y) g x }

instance  : is_right_adjoint (forget CommRingₓₓ.{u}) :=
  ⟨_, adj⟩

end CommRingₓₓ

