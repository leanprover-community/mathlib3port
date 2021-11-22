import Mathbin.Algebra.Category.Mon.Basic 
import Mathbin.CategoryTheory.Monoidal.CommMon_ 
import Mathbin.CategoryTheory.Monoidal.Types

/-!
# `Mon_ (Type u) ≌ Mon.{u}`

The category of internal monoid objects in `Type`
is equivalent to the category of "native" bundled monoids.

Moreover, this equivalence is compatible with the forgetful functors to `Type`.
-/


universe v u

open CategoryTheory

namespace monTypeEquivalenceMon

instance Mon_monoid (A : Mon_ (Type u)) : Monoidₓ A.X :=
  { one := A.one PUnit.unit, mul := fun x y => A.mul (x, y),
    one_mul :=
      fun x =>
        by 
          convert congr_funₓ A.one_mul (PUnit.unit, x),
    mul_one :=
      fun x =>
        by 
          convert congr_funₓ A.mul_one (x, PUnit.unit),
    mul_assoc :=
      fun x y z =>
        by 
          convert congr_funₓ A.mul_assoc ((x, y), z) }

/--
Converting a monoid object in `Type` to a bundled monoid.
-/
def Functor : Mon_ (Type u) ⥤ Mon.{u} :=
  { obj := fun A => ⟨A.X⟩,
    map :=
      fun A B f =>
        { toFun := f.hom, map_one' := congr_funₓ f.one_hom PUnit.unit,
          map_mul' := fun x y => congr_funₓ f.mul_hom (x, y) } }

/--
Converting a bundled monoid to a monoid object in `Type`.
-/
def inverse : Mon.{u} ⥤ Mon_ (Type u) :=
  { obj :=
      fun A =>
        { x := A, one := fun _ => 1, mul := fun p => p.1*p.2,
          mul_assoc' :=
            by 
              ext ⟨⟨x, y⟩, z⟩
              simp [mul_assocₓ] },
    map := fun A B f => { Hom := f } }

end monTypeEquivalenceMon

open monTypeEquivalenceMon

/--
The category of internal monoid objects in `Type`
is equivalent to the category of "native" bundled monoids.
-/
def monTypeEquivalenceMon : Mon_ (Type u) ≌ Mon.{u} :=
  { Functor := Functor, inverse := inverse,
    unitIso :=
      nat_iso.of_components (fun A => { Hom := { Hom := 𝟙 _ }, inv := { Hom := 𝟙 _ } })
        (by 
          tidy),
    counitIso :=
      nat_iso.of_components
        (fun A =>
          { Hom := { toFun := id, map_one' := rfl, map_mul' := fun x y => rfl },
            inv := { toFun := id, map_one' := rfl, map_mul' := fun x y => rfl } })
        (by 
          tidy) }

/--
The equivalence `Mon_ (Type u) ≌ Mon.{u}`
is naturally compatible with the forgetful functors to `Type u`.
-/
def monTypeEquivalenceMonForget : MonTypeEquivalenceMon.functor ⋙ forget Mon ≅ Mon_.forget (Type u) :=
  nat_iso.of_components (fun A => iso.refl _)
    (by 
      tidy)

instance monTypeInhabited : Inhabited (Mon_ (Type u)) :=
  ⟨MonTypeEquivalenceMon.inverse.obj (Mon.of PUnit)⟩

namespace commMonTypeEquivalenceCommMon

instance CommMon_comm_monoid (A : CommMon_ (Type u)) : CommMonoidₓ A.X :=
  { MonTypeEquivalenceMon.monMonoid A.to_Mon_ with
    mul_comm :=
      fun x y =>
        by 
          convert congr_funₓ A.mul_comm (y, x) }

/--
Converting a commutative monoid object in `Type` to a bundled commutative monoid.
-/
def Functor : CommMon_ (Type u) ⥤ CommMon.{u} :=
  { obj := fun A => ⟨A.X⟩, map := fun A B f => MonTypeEquivalenceMon.functor.map f }

/--
Converting a bundled commutative monoid to a commutative monoid object in `Type`.
-/
def inverse : CommMon.{u} ⥤ CommMon_ (Type u) :=
  { obj :=
      fun A =>
        { MonTypeEquivalenceMon.inverse.obj ((forget₂ CommMon Mon).obj A) with
          mul_comm' :=
            by 
              ext ⟨x, y⟩
              exact CommMonoidₓ.mul_comm y x },
    map := fun A B f => MonTypeEquivalenceMon.inverse.map f }

end commMonTypeEquivalenceCommMon

open commMonTypeEquivalenceCommMon

/--
The category of internal commutative monoid objects in `Type`
is equivalent to the category of "native" bundled commutative monoids.
-/
def commMonTypeEquivalenceCommMon : CommMon_ (Type u) ≌ CommMon.{u} :=
  { Functor := Functor, inverse := inverse,
    unitIso :=
      nat_iso.of_components (fun A => { Hom := { Hom := 𝟙 _ }, inv := { Hom := 𝟙 _ } })
        (by 
          tidy),
    counitIso :=
      nat_iso.of_components
        (fun A =>
          { Hom := { toFun := id, map_one' := rfl, map_mul' := fun x y => rfl },
            inv := { toFun := id, map_one' := rfl, map_mul' := fun x y => rfl } })
        (by 
          tidy) }

/--
The equivalences `Mon_ (Type u) ≌ Mon.{u}` and `CommMon_ (Type u) ≌ CommMon.{u}`
are naturally compatible with the forgetful functors to `Mon` and `Mon_ (Type u)`.
-/
def commMonTypeEquivalenceCommMonForget :
  CommMonTypeEquivalenceCommMon.functor ⋙ forget₂ CommMon Mon ≅
    CommMon_.forget₂Mon_ (Type u) ⋙ MonTypeEquivalenceMon.functor :=
  nat_iso.of_components (fun A => iso.refl _)
    (by 
      tidy)

instance commMonTypeInhabited : Inhabited (CommMon_ (Type u)) :=
  ⟨CommMonTypeEquivalenceCommMon.inverse.obj (CommMon.of PUnit)⟩

