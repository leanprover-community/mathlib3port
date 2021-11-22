import Mathbin.CategoryTheory.FunctorCategory 
import Mathbin.CategoryTheory.FullyFaithful 
import Mathbin.CategoryTheory.ReflectsIsomorphisms

namespace CategoryTheory

open Category

universe v₁ u₁

variable(C : Type u₁)[category.{v₁} C]

/--
The data of a monad on C consists of an endofunctor T together with natural transformations
η : 𝟭 C ⟶ T and μ : T ⋙ T ⟶ T satisfying three equations:
- T μ_X ≫ μ_X = μ_(TX) ≫ μ_X (associativity)
- η_(TX) ≫ μ_X = 1_X (left unit)
- Tη_X ≫ μ_X = 1_X (right unit)
-/
structure Monadₓ extends C ⥤ C where 
  η'{} : 𝟭 _ ⟶ to_functor 
  μ'{} : to_functor ⋙ to_functor ⟶ to_functor 
  assoc' : ∀ X, to_functor.map (nat_trans.app μ' X) ≫ μ'.app _ = μ'.app _ ≫ μ'.app _ :=  by 
  runTac 
    obviously 
  left_unit' : ∀ X : C, η'.app (to_functor.obj X) ≫ μ'.app _ = 𝟙 _ :=  by 
  runTac 
    obviously 
  right_unit' : ∀ X : C, to_functor.map (η'.app X) ≫ μ'.app _ = 𝟙 _ :=  by 
  runTac 
    obviously

/--
The data of a comonad on C consists of an endofunctor G together with natural transformations
ε : G ⟶ 𝟭 C and δ : G ⟶ G ⋙ G satisfying three equations:
- δ_X ≫ G δ_X = δ_X ≫ δ_(GX) (coassociativity)
- δ_X ≫ ε_(GX) = 1_X (left counit)
- δ_X ≫ G ε_X = 1_X (right counit)
-/
structure comonad extends C ⥤ C where 
  ε'{} : to_functor ⟶ 𝟭 _ 
  δ'{} : to_functor ⟶ to_functor ⋙ to_functor 
  coassoc' : ∀ X, nat_trans.app δ' _ ≫ to_functor.map (δ'.app X) = δ'.app _ ≫ δ'.app _ :=  by 
  runTac 
    obviously 
  left_counit' : ∀ X : C, δ'.app X ≫ ε'.app (to_functor.obj X) = 𝟙 _ :=  by 
  runTac 
    obviously 
  right_counit' : ∀ X : C, δ'.app X ≫ to_functor.map (ε'.app X) = 𝟙 _ :=  by 
  runTac 
    obviously

variable{C}(T : Monadₓ C)(G : comonad C)

instance coe_monad : Coe (Monadₓ C) (C ⥤ C) :=
  ⟨fun T => T.to_functor⟩

instance coe_comonad : Coe (comonad C) (C ⥤ C) :=
  ⟨fun G => G.to_functor⟩

@[simp]
theorem monad_to_functor_eq_coe : T.to_functor = T :=
  rfl

@[simp]
theorem comonad_to_functor_eq_coe : G.to_functor = G :=
  rfl

/-- The unit for the monad `T`. -/
def monad.η : 𝟭 _ ⟶ (T : C ⥤ C) :=
  T.η'

/-- The multiplication for the monad `T`. -/
def monad.μ : (T : C ⥤ C) ⋙ (T : C ⥤ C) ⟶ T :=
  T.μ'

/-- The counit for the comonad `G`. -/
def comonad.ε : (G : C ⥤ C) ⟶ 𝟭 _ :=
  G.ε'

/-- The comultiplication for the comonad `G`. -/
def comonad.δ : (G : C ⥤ C) ⟶ (G : C ⥤ C) ⋙ G :=
  G.δ'

/-- A custom simps projection for the functor part of a monad, as a coercion. -/
def monad.simps.coe :=
  (T : C ⥤ C)

/-- A custom simps projection for the unit of a monad, in simp normal form. -/
def monad.simps.η : 𝟭 _ ⟶ (T : C ⥤ C) :=
  T.η

/-- A custom simps projection for the multiplication of a monad, in simp normal form. -/
def monad.simps.μ : (T : C ⥤ C) ⋙ (T : C ⥤ C) ⟶ (T : C ⥤ C) :=
  T.μ

/-- A custom simps projection for the functor part of a comonad, as a coercion. -/
def comonad.simps.coe :=
  (G : C ⥤ C)

/-- A custom simps projection for the counit of a comonad, in simp normal form. -/
def comonad.simps.ε : (G : C ⥤ C) ⟶ 𝟭 _ :=
  G.ε

/-- A custom simps projection for the comultiplication of a comonad, in simp normal form. -/
def comonad.simps.δ : (G : C ⥤ C) ⟶ (G : C ⥤ C) ⋙ (G : C ⥤ C) :=
  G.δ

initialize_simps_projections category_theory.monad (toFunctor → coe, η' → η, μ' → μ)

initialize_simps_projections category_theory.comonad (toFunctor → coe, ε' → ε, δ' → δ)

@[reassoc]
theorem monad.assoc (T : Monadₓ C) (X : C) : (T : C ⥤ C).map (T.μ.app X) ≫ T.μ.app _ = T.μ.app _ ≫ T.μ.app _ :=
  T.assoc' X

@[simp, reassoc]
theorem monad.left_unit (T : Monadₓ C) (X : C) : T.η.app ((T : C ⥤ C).obj X) ≫ T.μ.app X = 𝟙 ((T : C ⥤ C).obj X) :=
  T.left_unit' X

@[simp, reassoc]
theorem monad.right_unit (T : Monadₓ C) (X : C) : (T : C ⥤ C).map (T.η.app X) ≫ T.μ.app X = 𝟙 ((T : C ⥤ C).obj X) :=
  T.right_unit' X

@[reassoc]
theorem comonad.coassoc (G : comonad C) (X : C) : G.δ.app _ ≫ (G : C ⥤ C).map (G.δ.app X) = G.δ.app _ ≫ G.δ.app _ :=
  G.coassoc' X

@[simp, reassoc]
theorem comonad.left_counit (G : comonad C) (X : C) : G.δ.app X ≫ G.ε.app ((G : C ⥤ C).obj X) = 𝟙 ((G : C ⥤ C).obj X) :=
  G.left_counit' X

@[simp, reassoc]
theorem comonad.right_counit (G : comonad C) (X : C) :
  G.δ.app X ≫ (G : C ⥤ C).map (G.ε.app X) = 𝟙 ((G : C ⥤ C).obj X) :=
  G.right_counit' X

/-- A morphism of monads is a natural transformation compatible with η and μ. -/
@[ext]
structure monad_hom(T₁ T₂ : Monadₓ C) extends nat_trans (T₁ : C ⥤ C) T₂ where 
  app_η' : ∀ X, T₁.η.app X ≫ app X = T₂.η.app X :=  by 
  runTac 
    obviously 
  app_μ' : ∀ X, T₁.μ.app X ≫ app X = ((T₁ : C ⥤ C).map (app X) ≫ app _) ≫ T₂.μ.app X :=  by 
  runTac 
    obviously

/-- A morphism of comonads is a natural transformation compatible with ε and δ. -/
@[ext]
structure comonad_hom(M N : comonad C) extends nat_trans (M : C ⥤ C) N where 
  app_ε' : ∀ X, app X ≫ N.ε.app X = M.ε.app X :=  by 
  runTac 
    obviously 
  app_δ' : ∀ X, app X ≫ N.δ.app X = M.δ.app X ≫ app _ ≫ (N : C ⥤ C).map (app X) :=  by 
  runTac 
    obviously

restate_axiom monad_hom.app_η'

restate_axiom monad_hom.app_μ'

attribute [simp, reassoc] monad_hom.app_η monad_hom.app_μ

restate_axiom comonad_hom.app_ε'

restate_axiom comonad_hom.app_δ'

attribute [simp, reassoc] comonad_hom.app_ε comonad_hom.app_δ

instance  : category (Monadₓ C) :=
  { Hom := monad_hom, id := fun M => { toNatTrans := 𝟙 (M : C ⥤ C) },
    comp := fun _ _ _ f g => { toNatTrans := { app := fun X => f.app X ≫ g.app X } } }

instance  : category (comonad C) :=
  { Hom := comonad_hom, id := fun M => { toNatTrans := 𝟙 (M : C ⥤ C) },
    comp := fun M N L f g => { toNatTrans := { app := fun X => f.app X ≫ g.app X } } }

instance  {T : Monadₓ C} : Inhabited (monad_hom T T) :=
  ⟨𝟙 T⟩

@[simp]
theorem monad_hom.id_to_nat_trans (T : Monadₓ C) : (𝟙 T : T ⟶ T).toNatTrans = 𝟙 (T : C ⥤ C) :=
  rfl

@[simp]
theorem monad_hom.comp_to_nat_trans {T₁ T₂ T₃ : Monadₓ C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
  (f ≫ g).toNatTrans = ((f.to_nat_trans : _ ⟶ (T₂ : C ⥤ C)) ≫ g.to_nat_trans : (T₁ : C ⥤ C) ⟶ T₃) :=
  rfl

instance  {G : comonad C} : Inhabited (comonad_hom G G) :=
  ⟨𝟙 G⟩

@[simp]
theorem comonad_hom.id_to_nat_trans (T : comonad C) : (𝟙 T : T ⟶ T).toNatTrans = 𝟙 (T : C ⥤ C) :=
  rfl

@[simp]
theorem comp_to_nat_trans {T₁ T₂ T₃ : comonad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
  (f ≫ g).toNatTrans = ((f.to_nat_trans : _ ⟶ (T₂ : C ⥤ C)) ≫ g.to_nat_trans : (T₁ : C ⥤ C) ⟶ T₃) :=
  rfl

/-- Construct a monad isomorphism from a natural isomorphism of functors where the forward
direction is a monad morphism. -/
@[simps]
def monad_iso.mk {M N : Monadₓ C} (f : (M : C ⥤ C) ≅ N) f_η f_μ : M ≅ N :=
  { Hom := { toNatTrans := f.hom, app_η' := f_η, app_μ' := f_μ },
    inv :=
      { toNatTrans := f.inv,
        app_η' :=
          fun X =>
            by 
              simp [←f_η],
        app_μ' :=
          fun X =>
            by 
              rw [←nat_iso.cancel_nat_iso_hom_right f]
              simp only [nat_trans.naturality, iso.inv_hom_id_app, assoc, comp_id, f_μ, nat_trans.naturality_assoc,
                iso.inv_hom_id_app_assoc, ←functor.map_comp_assoc]
              simp  } }

/-- Construct a comonad isomorphism from a natural isomorphism of functors where the forward
direction is a comonad morphism. -/
@[simps]
def comonad_iso.mk {M N : comonad C} (f : (M : C ⥤ C) ≅ N) f_ε f_δ : M ≅ N :=
  { Hom := { toNatTrans := f.hom, app_ε' := f_ε, app_δ' := f_δ },
    inv :=
      { toNatTrans := f.inv,
        app_ε' :=
          fun X =>
            by 
              simp [←f_ε],
        app_δ' :=
          fun X =>
            by 
              rw [←nat_iso.cancel_nat_iso_hom_left f]
              simp only [reassoc_of (f_δ X), iso.hom_inv_id_app_assoc, nat_trans.naturality_assoc]
              rw [←functor.map_comp, iso.hom_inv_id_app, Functor.map_id]
              apply (comp_id _).symm } }

variable(C)

/--
The forgetful functor from the category of monads to the category of endofunctors.
-/
@[simps]
def monad_to_functor : Monadₓ C ⥤ C ⥤ C :=
  { obj := fun T => T, map := fun M N f => f.to_nat_trans }

instance  : faithful (monad_to_functor C) :=
  {  }

@[simp]
theorem monad_to_functor_map_iso_monad_iso_mk {M N : Monadₓ C} (f : (M : C ⥤ C) ≅ N) f_η f_μ :
  (monad_to_functor _).mapIso (monad_iso.mk f f_η f_μ) = f :=
  by 
    ext 
    rfl

instance  : reflects_isomorphisms (monad_to_functor C) :=
  { reflects :=
      fun M N f i =>
        by 
          resetI 
          convert is_iso.of_iso (monad_iso.mk (as_iso ((monad_to_functor C).map f)) f.app_η f.app_μ)
          ext <;> rfl }

/--
The forgetful functor from the category of comonads to the category of endofunctors.
-/
@[simps]
def comonad_to_functor : comonad C ⥤ C ⥤ C :=
  { obj := fun G => G, map := fun M N f => f.to_nat_trans }

instance  : faithful (comonad_to_functor C) :=
  {  }

@[simp]
theorem comonad_to_functor_map_iso_comonad_iso_mk {M N : comonad C} (f : (M : C ⥤ C) ≅ N) f_ε f_δ :
  (comonad_to_functor _).mapIso (comonad_iso.mk f f_ε f_δ) = f :=
  by 
    ext 
    rfl

instance  : reflects_isomorphisms (comonad_to_functor C) :=
  { reflects :=
      fun M N f i =>
        by 
          resetI 
          convert is_iso.of_iso (comonad_iso.mk (as_iso ((comonad_to_functor C).map f)) f.app_ε f.app_δ)
          ext <;> rfl }

variable{C}

/--
An isomorphism of monads gives a natural isomorphism of the underlying functors.
-/
@[simps (config := { rhsMd := semireducible })]
def monad_iso.to_nat_iso {M N : Monadₓ C} (h : M ≅ N) : (M : C ⥤ C) ≅ N :=
  (monad_to_functor C).mapIso h

/--
An isomorphism of comonads gives a natural isomorphism of the underlying functors.
-/
@[simps (config := { rhsMd := semireducible })]
def comonad_iso.to_nat_iso {M N : comonad C} (h : M ≅ N) : (M : C ⥤ C) ≅ N :=
  (comonad_to_functor C).mapIso h

variable(C)

namespace Monadₓ

/-- The identity monad. -/
@[simps]
def id : Monadₓ C :=
  { toFunctor := 𝟭 C, η' := 𝟙 (𝟭 C), μ' := 𝟙 (𝟭 C) }

instance  : Inhabited (Monadₓ C) :=
  ⟨monad.id C⟩

end Monadₓ

namespace Comonad

/-- The identity comonad. -/
@[simps]
def id : comonad C :=
  { toFunctor := 𝟭 _, ε' := 𝟙 (𝟭 C), δ' := 𝟙 (𝟭 C) }

instance  : Inhabited (comonad C) :=
  ⟨comonad.id C⟩

end Comonad

end CategoryTheory

