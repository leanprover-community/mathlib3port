import Mathbin.CategoryTheory.NaturalIsomorphism 
import Mathbin.CategoryTheory.Equivalence 
import Mathbin.CategoryTheory.EqToHom

/-!
# Quotient category

Constructs the quotient of a category by an arbitrary family of relations on its hom-sets,
by introducing a type synonym for the objects, and identifying homs as necessary.

This is analogous to 'the quotient of a group by the normal closure of a subset', rather
than 'the quotient of a group by a normal subgroup'. When taking the quotient by a congruence
relation, `functor_map_eq_iff` says that no unnecessary identifications have been made.
-/


-- error in CategoryTheory.Quotient: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler inhabited
/-- A `hom_rel` on `C` consists of a relation on every hom-set. -/
@[derive #[expr inhabited]]
def hom_rel (C) [quiver C] :=
∀ {{X Y : C}}, «expr ⟶ »(X, Y) → «expr ⟶ »(X, Y) → exprProp()

namespace CategoryTheory

variable{C : Type _}[category C](r : HomRel C)

include r

/-- A `hom_rel` is a congruence when it's an equivalence on every hom-set, and it can be composed
from left and right. -/
class congruence : Prop where 
  IsEquiv : ∀ {X Y}, IsEquiv _ (@r X Y)
  compLeft : ∀ {X Y Z} f : X ⟶ Y {g g' : Y ⟶ Z}, r g g' → r (f ≫ g) (f ≫ g')
  compRight : ∀ {X Y Z} {f f' : X ⟶ Y} g : Y ⟶ Z, r f f' → r (f ≫ g) (f' ≫ g)

attribute [instance] congruence.is_equiv

/-- A type synonym for `C`, thought of as the objects of the quotient category. -/
@[ext]
structure Quotientₓ where 
  as : C

instance  [Inhabited C] : Inhabited (Quotientₓ r) :=
  ⟨{ as := default C }⟩

namespace Quotientₓ

/-- Generates the closure of a family of relations w.r.t. composition from left and right. -/
inductive comp_closure ⦃s t : C⦄ : (s ⟶ t) → (s ⟶ t) → Prop
  | intro {a b} (f : s ⟶ a) (m₁ m₂ : a ⟶ b) (g : b ⟶ t) (h : r m₁ m₂) : comp_closure (f ≫ m₁ ≫ g) (f ≫ m₂ ≫ g)

theorem comp_left {a b c : C} (f : a ⟶ b) : ∀ g₁ g₂ : b ⟶ c h : comp_closure r g₁ g₂, comp_closure r (f ≫ g₁) (f ≫ g₂)
| _, _, ⟨x, m₁, m₂, y, h⟩ =>
  by 
    simpa using comp_closure.intro (f ≫ x) m₁ m₂ y h

theorem comp_right {a b c : C} (g : b ⟶ c) : ∀ f₁ f₂ : a ⟶ b h : comp_closure r f₁ f₂, comp_closure r (f₁ ≫ g) (f₂ ≫ g)
| _, _, ⟨x, m₁, m₂, y, h⟩ =>
  by 
    simpa using comp_closure.intro x m₁ m₂ (y ≫ g) h

/-- Hom-sets of the quotient category. -/
def hom (s t : Quotientₓ r) :=
  Quot$ @comp_closure C _ r s.as t.as

instance  (a : Quotientₓ r) : Inhabited (hom r a a) :=
  ⟨Quot.mk _ (𝟙 a.as)⟩

/-- Composition in the quotient category. -/
def comp ⦃a b c : Quotientₓ r⦄ : hom r a b → hom r b c → hom r a c :=
  fun hf hg =>
    Quot.liftOn hf
      (fun f => Quot.liftOn hg (fun g => Quot.mk _ (f ≫ g)) fun g₁ g₂ h => Quot.sound$ comp_left r f g₁ g₂ h)
      fun f₁ f₂ h => Quot.induction_on hg$ fun g => Quot.sound$ comp_right r g f₁ f₂ h

@[simp]
theorem comp_mk {a b c : Quotientₓ r} (f : a.as ⟶ b.as) (g : b.as ⟶ c.as) :
  comp r (Quot.mk _ f) (Quot.mk _ g) = Quot.mk _ (f ≫ g) :=
  rfl

instance category : category (Quotientₓ r) :=
  { Hom := hom r, id := fun a => Quot.mk _ (𝟙 a.as), comp := comp r }

/-- The functor from a category to its quotient. -/
@[simps]
def Functor : C ⥤ Quotientₓ r :=
  { obj := fun a => { as := a }, map := fun _ _ f => Quot.mk _ f }

noncomputable instance  : full (Functor r) :=
  { Preimage := fun X Y f => Quot.out f }

instance  : ess_surj (Functor r) :=
  { mem_ess_image :=
      fun Y =>
        ⟨Y.as,
          ⟨eq_to_iso
              (by 
                ext 
                rfl)⟩⟩ }

protected theorem induction {P : ∀ {a b : Quotientₓ r}, (a ⟶ b) → Prop}
  (h : ∀ {x y : C} f : x ⟶ y, P ((Functor r).map f)) : ∀ {a b : Quotientₓ r} f : a ⟶ b, P f :=
  by 
    rintro ⟨x⟩ ⟨y⟩ ⟨f⟩
    exact h f

protected theorem sound {a b : C} {f₁ f₂ : a ⟶ b} (h : r f₁ f₂) : (Functor r).map f₁ = (Functor r).map f₂ :=
  by 
    simpa using Quot.sound (comp_closure.intro (𝟙 a) f₁ f₂ (𝟙 b) h)

theorem functor_map_eq_iff [congruence r] {X Y : C} (f f' : X ⟶ Y) : (Functor r).map f = (Functor r).map f' ↔ r f f' :=
  by 
    split 
    ·
      erw [Quot.eq]
      intro h 
      induction' h with m m' hm
      ·
        cases hm 
        apply congruence.comp_left 
        apply congruence.comp_right 
        assumption
      ·
        apply refl
      ·
        apply symm 
        assumption
      ·
        apply trans <;> assumption
    ·
      apply Quotientₓ.sound

variable{D : Type _}[category D](F : C ⥤ D)(H : ∀ x y : C f₁ f₂ : x ⟶ y, r f₁ f₂ → F.map f₁ = F.map f₂)

include H

/-- The induced functor on the quotient category. -/
@[simps]
def lift : Quotientₓ r ⥤ D :=
  { obj := fun a => F.obj a.as,
    map :=
      fun a b hf =>
        Quot.liftOn hf (fun f => F.map f)
          (by 
            rintro _ _ ⟨_, _, _, _, _, _, h⟩
            simp [H _ _ _ _ h]),
    map_id' := fun a => F.map_id a.as,
    map_comp' :=
      by 
        rintro a b c ⟨f⟩ ⟨g⟩
        exact F.map_comp f g }

/-- The original functor factors through the induced functor. -/
def lift.is_lift : Functor r ⋙ lift r F H ≅ F :=
  nat_iso.of_components (fun X => iso.refl _)
    (by 
      tidy)

@[simp]
theorem lift.is_lift_hom (X : C) : (lift.is_lift r F H).Hom.app X = 𝟙 (F.obj X) :=
  rfl

@[simp]
theorem lift.is_lift_inv (X : C) : (lift.is_lift r F H).inv.app X = 𝟙 (F.obj X) :=
  rfl

theorem lift_map_functor_map {X Y : C} (f : X ⟶ Y) : (lift r F H).map ((Functor r).map f) = F.map f :=
  by 
    rw [←nat_iso.naturality_1 (lift.is_lift r F H)]
    dsimp 
    simp 

end Quotientₓ

end CategoryTheory

