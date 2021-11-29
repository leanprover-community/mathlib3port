import Mathbin.Algebra.Group.Pi 
import Mathbin.Algebra.Category.Group.Preadditive 
import Mathbin.CategoryTheory.Limits.Shapes.Biproducts 
import Mathbin.Algebra.Category.Group.Limits

/-!
# The category of abelian groups has finite biproducts
-/


open CategoryTheory

open CategoryTheory.Limits

open_locale BigOperators

universe u

namespace AddCommGroupₓₓ

/--
Construct limit data for a binary product in `AddCommGroup`, using `AddCommGroup.of (G × H)`.
-/
def binary_product_limit_cone (G H : AddCommGroupₓₓ.{u}) : limits.limit_cone (pair G H) :=
  { Cone :=
      { x := AddCommGroupₓₓ.of (G × H),
        π := { app := fun j => walking_pair.cases_on j (AddMonoidHom.fst G H) (AddMonoidHom.snd G H) } },
    IsLimit :=
      { lift := fun s => AddMonoidHom.prod (s.π.app walking_pair.left) (s.π.app walking_pair.right),
        fac' :=
          by 
            rintro s (⟨⟩ | ⟨⟩) <;>
              ·
                ext x 
                simp ,
        uniq' :=
          fun s m w =>
            by 
              ext <;> [rw [←w walking_pair.left], rw [←w walking_pair.right]] <;> rfl } }

instance has_binary_product (G H : AddCommGroupₓₓ.{u}) : has_binary_product G H :=
  has_limit.mk (binary_product_limit_cone G H)

instance  (G H : AddCommGroupₓₓ.{u}) : has_binary_biproduct G H :=
  has_binary_biproduct.of_has_binary_product _ _

/--
We verify that the biproduct in AddCommGroup is isomorphic to
the cartesian product of the underlying types:
-/
noncomputable def biprod_iso_prod (G H : AddCommGroupₓₓ.{u}) : (G ⊞ H : AddCommGroupₓₓ) ≅ AddCommGroupₓₓ.of (G × H) :=
  is_limit.cone_point_unique_up_to_iso (binary_biproduct.is_limit G H) (binary_product_limit_cone G H).IsLimit

example  (G H : AddCommGroupₓₓ.{u}) : has_colimit (pair G H) :=
  by 
    infer_instance

variable{J : Type u}(F : discrete J ⥤ AddCommGroupₓₓ.{u})

namespace HasLimit

/--
The map from an arbitrary cone over a indexed family of abelian groups
to the cartesian product of those groups.
-/
def lift (s : cone F) : s.X ⟶ AddCommGroupₓₓ.of (∀ j, F.obj j) :=
  { toFun := fun x j => s.π.app j x,
    map_zero' :=
      by 
        ext 
        simp ,
    map_add' :=
      fun x y =>
        by 
          ext 
          simp  }

@[simp]
theorem lift_apply (s : cone F) (x : s.X) (j : J) : (lift F s) x j = s.π.app j x :=
  rfl

-- error in Algebra.Category.Group.Biproducts: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/--
Construct limit data for a product in `AddCommGroup`, using `AddCommGroup.of (Π j, F.obj j)`.
-/ def product_limit_cone : limits.limit_cone F :=
{ cone := { X := AddCommGroup.of (∀ j, F.obj j),
    π := discrete.nat_trans (λ j, pi.eval_add_monoid_hom (λ j, F.obj j) j) },
  is_limit := { lift := lift F,
    fac' := λ s j, by { ext [] [] [],
      simp [] [] [] [] [] [] },
    uniq' := λ s m w, begin
      ext [] [ident x, ident j] [],
      dsimp ["only"] ["[", expr has_limit.lift, "]"] [] [],
      simp [] [] ["only"] ["[", expr add_monoid_hom.coe_mk, "]"] [] [],
      exact [expr congr_arg (λ f : «expr ⟶ »(s.X, F.obj j), (f : s.X → F.obj j) x) (w j)]
    end } }

end HasLimit

section 

open HasLimit

variable[DecidableEq J][Fintype J]

instance  (f : J → AddCommGroupₓₓ.{u}) : has_biproduct f :=
  has_biproduct.of_has_product _

/--
We verify that the biproduct we've just defined is isomorphic to the AddCommGroup structure
on the dependent function type
-/
noncomputable def biproduct_iso_pi (f : J → AddCommGroupₓₓ.{u}) :
  (⨁ f : AddCommGroupₓₓ) ≅ AddCommGroupₓₓ.of (∀ j, f j) :=
  is_limit.cone_point_unique_up_to_iso (biproduct.is_limit f) (product_limit_cone (discrete.functor f)).IsLimit

end 

instance  : has_finite_biproducts AddCommGroupₓₓ :=
  ⟨fun J _ _ =>
      by 
        exact
          { HasBiproduct :=
              fun f =>
                by 
                  infer_instance }⟩

end AddCommGroupₓₓ

