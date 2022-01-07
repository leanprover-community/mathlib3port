import Mathbin.CategoryTheory.Equivalence

/-!
# Adjunctions between functors

`F ⊣ G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.

We provide various useful constructors:
* `mk_of_hom_equiv`
* `mk_of_unit_counit`
* `left_adjoint_of_equiv` / `right_adjoint_of equiv`
  construct a left/right adjoint of a given functor given the action on objects and
  the relevant equivalence of morphism spaces.
* `adjunction_of_equiv_left` / `adjunction_of_equiv_right` witness that these constructions
  give adjunctions.

There are also typeclasses `is_left_adjoint` / `is_right_adjoint`, carrying data witnessing
that a given functor is a left or right adjoint.
Given `[is_left_adjoint F]`, a right adjoint of `F` can be constructed as `right_adjoint F`.

`adjunction.comp` composes adjunctions.

`to_equivalence` upgrades an adjunction to an equivalence,
given witnesses that the unit and counit are pointwise isomorphisms.
Conversely `equivalence.to_adjunction` recovers the underlying adjunction from an equivalence.
-/


namespace CategoryTheory

open Category

universe v₁ v₂ v₃ u₁ u₂ u₃

attribute [local elabWithoutExpectedType] whisker_left whisker_right

variable {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

/-- `F ⊣ G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.

To construct an `adjunction` between two functors, it's often easier to instead use the
constructors `mk_of_hom_equiv` or `mk_of_unit_counit`. To construct a left adjoint,
there are also constructors `left_adjoint_of_equiv` and `adjunction_of_equiv_left` (as
well as their duals) which can be simpler in practice.

Uniqueness of adjoints is shown in `category_theory.adjunction.opposites`.

See https://stacks.math.columbia.edu/tag/0037.
-/
structure adjunction (F : C ⥤ D) (G : D ⥤ C) where
  homEquiv : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
  Unit : 𝟭 C ⟶ F.comp G
  counit : G.comp F ⟶ 𝟭 D
  hom_equiv_unit' : ∀ {X Y f}, (hom_equiv X Y) f = (Unit : _ ⟶ _).app X ≫ G.map f := by
    run_tac
      obviously
  hom_equiv_counit' : ∀ {X Y g}, (hom_equiv X Y).symm g = F.map g ≫ counit.app Y := by
    run_tac
      obviously

infixl:15 " ⊣ " => adjunction

/-- A class giving a chosen right adjoint to the functor `left`. -/
class is_left_adjoint (left : C ⥤ D) where
  right : D ⥤ C
  adj : left ⊣ right

/-- A class giving a chosen left adjoint to the functor `right`. -/
class is_right_adjoint (right : D ⥤ C) where
  left : C ⥤ D
  adj : left ⊣ right

/-- Extract the left adjoint from the instance giving the chosen adjoint. -/
def left_adjoint (R : D ⥤ C) [is_right_adjoint R] : C ⥤ D :=
  is_right_adjoint.left R

/-- Extract the right adjoint from the instance giving the chosen adjoint. -/
def right_adjoint (L : C ⥤ D) [is_left_adjoint L] : D ⥤ C :=
  is_left_adjoint.right L

/-- The adjunction associated to a functor known to be a left adjoint. -/
def adjunction.of_left_adjoint (left : C ⥤ D) [is_left_adjoint left] : adjunction left (right_adjoint left) :=
  is_left_adjoint.adj

/-- The adjunction associated to a functor known to be a right adjoint. -/
def adjunction.of_right_adjoint (right : C ⥤ D) [is_right_adjoint right] : adjunction (left_adjoint right) right :=
  is_right_adjoint.adj

namespace Adjunction

restate_axiom hom_equiv_unit'

restate_axiom hom_equiv_counit'

attribute [simp] hom_equiv_unit hom_equiv_counit

section

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X' X : C} {Y Y' : D}

theorem hom_equiv_id (X : C) : adj.hom_equiv X _ (𝟙 _) = adj.unit.app X := by
  simp

theorem hom_equiv_symm_id (X : D) : (adj.hom_equiv _ X).symm (𝟙 _) = adj.counit.app X := by
  simp

@[simp]
theorem hom_equiv_naturality_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) :
    (adj.hom_equiv X' Y).symm (f ≫ g) = F.map f ≫ (adj.hom_equiv X Y).symm g := by
  rw [hom_equiv_counit, F.map_comp, assoc, adj.hom_equiv_counit.symm]

@[simp]
theorem hom_equiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    (adj.hom_equiv X' Y) (F.map f ≫ g) = f ≫ (adj.hom_equiv X Y) g := by
  rw [← Equivₓ.eq_symm_apply] <;> simp [-hom_equiv_unit]

@[simp]
theorem hom_equiv_naturality_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') :
    (adj.hom_equiv X Y') (f ≫ g) = (adj.hom_equiv X Y) f ≫ G.map g := by
  rw [hom_equiv_unit, G.map_comp, ← assoc, ← hom_equiv_unit]

@[simp]
theorem hom_equiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
    (adj.hom_equiv X Y').symm (f ≫ G.map g) = (adj.hom_equiv X Y).symm f ≫ g := by
  rw [Equivₓ.symm_apply_eq] <;> simp [-hom_equiv_counit]

@[simp]
theorem left_triangle : whisker_right adj.unit F ≫ whisker_left F adj.counit = nat_trans.id _ := by
  ext
  dsimp
  erw [← adj.hom_equiv_counit, Equivₓ.symm_apply_eq, adj.hom_equiv_unit]
  simp

@[simp]
theorem right_triangle : whisker_left G adj.unit ≫ whisker_right adj.counit G = nat_trans.id _ := by
  ext
  dsimp
  erw [← adj.hom_equiv_unit, ← Equivₓ.eq_symm_apply, adj.hom_equiv_counit]
  simp

@[simp, reassoc]
theorem left_triangle_components : F.map (adj.unit.app X) ≫ adj.counit.app (F.obj X) = 𝟙 (F.obj X) :=
  congr_argₓ (fun t : nat_trans _ (𝟭 C ⋙ F) => t.app X) adj.left_triangle

@[simp, reassoc]
theorem right_triangle_components {Y : D} : adj.unit.app (G.obj Y) ≫ G.map (adj.counit.app Y) = 𝟙 (G.obj Y) :=
  congr_argₓ (fun t : nat_trans _ (G ⋙ 𝟭 C) => t.app Y) adj.right_triangle

@[simp, reassoc]
theorem counit_naturality {X Y : D} (f : X ⟶ Y) : F.map (G.map f) ≫ adj.counit.app Y = adj.counit.app X ≫ f :=
  adj.counit.naturality f

@[simp, reassoc]
theorem unit_naturality {X Y : C} (f : X ⟶ Y) : adj.unit.app X ≫ G.map (F.map f) = f ≫ adj.unit.app Y :=
  (adj.unit.naturality f).symm

theorem hom_equiv_apply_eq {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    adj.hom_equiv A B f = g ↔ f = (adj.hom_equiv A B).symm g :=
  ⟨fun h => by
    cases h
    simp , fun h => by
    cases h
    simp ⟩

theorem eq_hom_equiv_apply {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    g = adj.hom_equiv A B f ↔ (adj.hom_equiv A B).symm g = f :=
  ⟨fun h => by
    cases h
    simp , fun h => by
    cases h
    simp ⟩

end

end Adjunction

namespace Adjunction

/-- This is an auxiliary data structure useful for constructing adjunctions.
See `adjunction.mk_of_hom_equiv`.
This structure won't typically be used anywhere else.
-/
@[nolint has_inhabited_instance]
structure core_hom_equiv (F : C ⥤ D) (G : D ⥤ C) where
  homEquiv : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
  hom_equiv_naturality_left_symm' :
    ∀ {X' X Y} f : X' ⟶ X g : X ⟶ G.obj Y, (hom_equiv X' Y).symm (f ≫ g) = F.map f ≫ (hom_equiv X Y).symm g := by
    run_tac
      obviously
  hom_equiv_naturality_right' :
    ∀ {X Y Y'} f : F.obj X ⟶ Y g : Y ⟶ Y', (hom_equiv X Y') (f ≫ g) = (hom_equiv X Y) f ≫ G.map g := by
    run_tac
      obviously

namespace CoreHomEquiv

restate_axiom hom_equiv_naturality_left_symm'

restate_axiom hom_equiv_naturality_right'

attribute [simp] hom_equiv_naturality_left_symm hom_equiv_naturality_right

variable {F : C ⥤ D} {G : D ⥤ C} (adj : core_hom_equiv F G) {X' X : C} {Y Y' : D}

@[simp]
theorem hom_equiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    (adj.hom_equiv X' Y) (F.map f ≫ g) = f ≫ (adj.hom_equiv X Y) g := by
  rw [← Equivₓ.eq_symm_apply] <;> simp

@[simp]
theorem hom_equiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
    (adj.hom_equiv X Y').symm (f ≫ G.map g) = (adj.hom_equiv X Y).symm f ≫ g := by
  rw [Equivₓ.symm_apply_eq] <;> simp

end CoreHomEquiv

/-- This is an auxiliary data structure useful for constructing adjunctions.
See `adjunction.mk_of_unit_counit`.
This structure won't typically be used anywhere else.
-/
@[nolint has_inhabited_instance]
structure core_unit_counit (F : C ⥤ D) (G : D ⥤ C) where
  Unit : 𝟭 C ⟶ F.comp G
  counit : G.comp F ⟶ 𝟭 D
  left_triangle' :
    whisker_right Unit F ≫ (functor.associator F G F).Hom ≫ whisker_left F counit = nat_trans.id (𝟭 C ⋙ F) := by
    run_tac
      obviously
  right_triangle' :
    whisker_left G Unit ≫ (functor.associator G F G).inv ≫ whisker_right counit G = nat_trans.id (G ⋙ 𝟭 C) := by
    run_tac
      obviously

namespace CoreUnitCounit

restate_axiom left_triangle'

restate_axiom right_triangle'

attribute [simp] left_triangle right_triangle

end CoreUnitCounit

variable {F : C ⥤ D} {G : D ⥤ C}

/-- Construct an adjunction between `F` and `G` out of a natural bijection between each
`F.obj X ⟶ Y` and `X ⟶ G.obj Y`. -/
@[simps]
def mk_of_hom_equiv (adj : core_hom_equiv F G) : F ⊣ G :=
  { adj with
    Unit :=
      { app := fun X => (adj.hom_equiv X (F.obj X)) (𝟙 (F.obj X)),
        naturality' := by
          intros
          erw [← adj.hom_equiv_naturality_left, ← adj.hom_equiv_naturality_right]
          dsimp
          simp },
    counit :=
      { app := fun Y => (adj.hom_equiv _ _).invFun (𝟙 (G.obj Y)),
        naturality' := by
          intros
          erw [← adj.hom_equiv_naturality_left_symm, ← adj.hom_equiv_naturality_right_symm]
          dsimp
          simp },
    hom_equiv_unit' := fun X Y f => by
      erw [← adj.hom_equiv_naturality_right] <;> simp ,
    hom_equiv_counit' := fun X Y f => by
      erw [← adj.hom_equiv_naturality_left_symm] <;> simp }

/-- Construct an adjunction between functors `F` and `G` given a unit and counit for the adjunction
satisfying the triangle identities. -/
@[simps]
def mk_of_unit_counit (adj : core_unit_counit F G) : F ⊣ G :=
  { adj with
    homEquiv := fun X Y =>
      { toFun := fun f => adj.unit.app X ≫ G.map f, invFun := fun g => F.map g ≫ adj.counit.app Y,
        left_inv := fun f => by
          change F.map (_ ≫ _) ≫ _ = _
          rw [F.map_comp, assoc, ← functor.comp_map, adj.counit.naturality, ← assoc]
          convert id_comp f
          have t := congr_argₓ (fun t : nat_trans _ _ => t.app _) adj.left_triangle
          dsimp  at t
          simp only [id_comp] at t
          exact t,
        right_inv := fun g => by
          change _ ≫ G.map (_ ≫ _) = _
          rw [G.map_comp, ← assoc, ← functor.comp_map, ← adj.unit.naturality, assoc]
          convert comp_id g
          have t := congr_argₓ (fun t : nat_trans _ _ => t.app _) adj.right_triangle
          dsimp  at t
          simp only [id_comp] at t
          exact t } }

/-- The adjunction between the identity functor on a category and itself. -/
def id : 𝟭 C ⊣ 𝟭 C where
  homEquiv := fun X Y => Equivₓ.refl _
  Unit := 𝟙 _
  counit := 𝟙 _

instance : Inhabited (adjunction (𝟭 C) (𝟭 C)) :=
  ⟨id⟩

/-- If F and G are naturally isomorphic functors, establish an equivalence of hom-sets. -/
@[simps]
def equiv_homset_left_of_nat_iso {F F' : C ⥤ D} (iso : F ≅ F') {X : C} {Y : D} : (F.obj X ⟶ Y) ≃ (F'.obj X ⟶ Y) where
  toFun := fun f => iso.inv.app _ ≫ f
  invFun := fun g => iso.hom.app _ ≫ g
  left_inv := fun f => by
    simp
  right_inv := fun g => by
    simp

/-- If G and H are naturally isomorphic functors, establish an equivalence of hom-sets. -/
@[simps]
def equiv_homset_right_of_nat_iso {G G' : D ⥤ C} (iso : G ≅ G') {X : C} {Y : D} : (X ⟶ G.obj Y) ≃ (X ⟶ G'.obj Y) where
  toFun := fun f => f ≫ iso.hom.app _
  invFun := fun g => g ≫ iso.inv.app _
  left_inv := fun f => by
    simp
  right_inv := fun g => by
    simp

/-- Transport an adjunction along an natural isomorphism on the left. -/
def of_nat_iso_left {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) : G ⊣ H :=
  adjunction.mk_of_hom_equiv
    { homEquiv := fun X Y => (equiv_homset_left_of_nat_iso iso.symm).trans (adj.hom_equiv X Y) }

/-- Transport an adjunction along an natural isomorphism on the right. -/
def of_nat_iso_right {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) : F ⊣ H :=
  adjunction.mk_of_hom_equiv { homEquiv := fun X Y => (adj.hom_equiv X Y).trans (equiv_homset_right_of_nat_iso iso) }

/-- Transport being a right adjoint along a natural isomorphism. -/
def right_adjoint_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [r : is_right_adjoint F] : is_right_adjoint G where
  left := r.left
  adj := of_nat_iso_right r.adj h

/-- Transport being a left adjoint along a natural isomorphism. -/
def left_adjoint_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [r : is_left_adjoint F] : is_left_adjoint G where
  right := r.right
  adj := of_nat_iso_left r.adj h

section

variable {E : Type u₃} [ℰ : category.{v₃} E] (H : D ⥤ E) (I : E ⥤ D)

/-- Composition of adjunctions.

See https://stacks.math.columbia.edu/tag/0DV0.
-/
def comp (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) : F ⋙ H ⊣ I ⋙ G where
  homEquiv := fun X Z => Equivₓ.trans (adj₂.hom_equiv _ _) (adj₁.hom_equiv _ _)
  Unit := adj₁.unit ≫ (whisker_left F $ whisker_right adj₂.unit G) ≫ (functor.associator _ _ _).inv
  counit := (functor.associator _ _ _).Hom ≫ (whisker_left I $ whisker_right adj₁.counit H) ≫ adj₂.counit

/-- If `F` and `G` are left adjoints then `F ⋙ G` is a left adjoint too. -/
instance left_adjoint_of_comp {E : Type u₃} [ℰ : category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E) [Fl : is_left_adjoint F]
    [Gl : is_left_adjoint G] : is_left_adjoint (F ⋙ G) where
  right := Gl.right ⋙ Fl.right
  adj := comp _ _ Fl.adj Gl.adj

/-- If `F` and `G` are right adjoints then `F ⋙ G` is a right adjoint too. -/
instance right_adjoint_of_comp {E : Type u₃} [ℰ : category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E} [Fr : is_right_adjoint F]
    [Gr : is_right_adjoint G] : is_right_adjoint (F ⋙ G) where
  left := Gr.left ⋙ Fr.left
  adj := comp _ _ Gr.adj Fr.adj

end

section ConstructLeft

variable {F_obj : C → D} {G}

variable (e : ∀ X Y, (F_obj X ⟶ Y) ≃ (X ⟶ G.obj Y))

variable (he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g)

include he

private theorem he' {X Y Y'} f g : (e X Y').symm (f ≫ G.map g) = (e X Y).symm f ≫ g := by
  intros <;> rw [Equivₓ.symm_apply_eq, he] <;> simp

/-- Construct a left adjoint functor to `G`, given the functor's value on objects `F_obj` and
a bijection `e` between `F_obj X ⟶ Y` and `X ⟶ G.obj Y` satisfying a naturality law
`he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g`.
Dual to `right_adjoint_of_equiv`. -/
@[simps]
def left_adjoint_of_equiv : C ⥤ D where
  obj := F_obj
  map := fun X X' f => (e X (F_obj X')).symm (f ≫ e X' (F_obj X') (𝟙 _))
  map_comp' := fun X X' X'' f f' => by
    rw [Equivₓ.symm_apply_eq, he, Equivₓ.apply_symm_apply]
    conv => rhs rw [assoc, ← he, id_comp, Equivₓ.apply_symm_apply]
    simp

/-- Show that the functor given by `left_adjoint_of_equiv` is indeed left adjoint to `G`. Dual
to `adjunction_of_equiv_right`. -/
@[simps]
def adjunction_of_equiv_left : left_adjoint_of_equiv e he ⊣ G :=
  mk_of_hom_equiv
    { homEquiv := e,
      hom_equiv_naturality_left_symm' := by
        intros
        erw [← he' e he, ← Equivₓ.apply_eq_iff_eq]
        simp [(he _ _ _ _ _).symm] }

end ConstructLeft

section ConstructRight

variable {F} {G_obj : D → C}

variable (e : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G_obj Y))

variable (he : ∀ X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g)

include he

private theorem he' {X' X Y} f g : F.map f ≫ (e X Y).symm g = (e X' Y).symm (f ≫ g) := by
  intros <;> rw [Equivₓ.eq_symm_apply, he] <;> simp

/-- Construct a right adjoint functor to `F`, given the functor's value on objects `G_obj` and
a bijection `e` between `F.obj X ⟶ Y` and `X ⟶ G_obj Y` satisfying a naturality law
`he : ∀ X Y Y' g h, e X' Y (F.map f ≫ g) = f ≫ e X Y g`.
Dual to `left_adjoint_of_equiv`. -/
@[simps]
def right_adjoint_of_equiv : D ⥤ C where
  obj := G_obj
  map := fun Y Y' g => (e (G_obj Y) Y') ((e (G_obj Y) Y).symm (𝟙 _) ≫ g)
  map_comp' := fun Y Y' Y'' g g' => by
    rw [← Equivₓ.eq_symm_apply, ← he' e he, Equivₓ.symm_apply_apply]
    conv => rhs rw [← assoc, he' e he, comp_id, Equivₓ.symm_apply_apply]
    simp

/-- Show that the functor given by `right_adjoint_of_equiv` is indeed right adjoint to `F`. Dual
to `adjunction_of_equiv_left`. -/
@[simps]
def adjunction_of_equiv_right : F ⊣ right_adjoint_of_equiv e he :=
  mk_of_hom_equiv
    { homEquiv := e,
      hom_equiv_naturality_left_symm' := by
        intros <;> rw [Equivₓ.symm_apply_eq, he] <;> simp ,
      hom_equiv_naturality_right' := by
        intro X Y Y' g h
        erw [← he, Equivₓ.apply_eq_iff_eq, ← assoc, he' e he, comp_id, Equivₓ.symm_apply_apply] }

end ConstructRight

/-- If the unit and counit of a given adjunction are (pointwise) isomorphisms, then we can upgrade the
adjunction to an equivalence.
-/
@[simps]
noncomputable def to_equivalence (adj : F ⊣ G) [∀ X, is_iso (adj.unit.app X)] [∀ Y, is_iso (adj.counit.app Y)] :
    C ≌ D where
  Functor := F
  inverse := G
  unitIso :=
    nat_iso.of_components (fun X => as_iso (adj.unit.app X))
      (by
        simp )
  counitIso :=
    nat_iso.of_components (fun Y => as_iso (adj.counit.app Y))
      (by
        simp )

/-- If the unit and counit for the adjunction corresponding to a right adjoint functor are (pointwise)
isomorphisms, then the functor is an equivalence of categories.
-/
@[simps]
noncomputable def is_right_adjoint_to_is_equivalence [is_right_adjoint G]
    [∀ X, is_iso ((adjunction.of_right_adjoint G).Unit.app X)]
    [∀ Y, is_iso ((adjunction.of_right_adjoint G).counit.app Y)] : is_equivalence G :=
  is_equivalence.of_equivalence_inverse (adjunction.of_right_adjoint G).toEquivalence

end Adjunction

open Adjunction

namespace Equivalenceₓ

/-- The adjunction given by an equivalence of categories. (To obtain the opposite adjunction,
simply use `e.symm.to_adjunction`. -/
def to_adjunction (e : C ≌ D) : e.functor ⊣ e.inverse :=
  mk_of_unit_counit
    ⟨e.unit, e.counit, by
      ext
      dsimp
      simp only [id_comp]
      exact e.functor_unit_comp _, by
      ext
      dsimp
      simp only [id_comp]
      exact e.unit_inverse_comp _⟩

end Equivalenceₓ

namespace Functor

/-- An equivalence `E` is left adjoint to its inverse. -/
def adjunction (E : C ⥤ D) [is_equivalence E] : E ⊣ E.inv :=
  E.as_equivalence.toAdjunction

/-- If `F` is an equivalence, it's a left adjoint. -/
instance (priority := 10) left_adjoint_of_equivalence {F : C ⥤ D} [is_equivalence F] : is_left_adjoint F where
  right := _
  adj := functor.adjunction F

@[simp]
theorem right_adjoint_of_is_equivalence {F : C ⥤ D} [is_equivalence F] : right_adjoint F = inv F :=
  rfl

/-- If `F` is an equivalence, it's a right adjoint. -/
instance (priority := 10) right_adjoint_of_equivalence {F : C ⥤ D} [is_equivalence F] : is_right_adjoint F where
  left := _
  adj := functor.adjunction F.inv

@[simp]
theorem left_adjoint_of_is_equivalence {F : C ⥤ D} [is_equivalence F] : left_adjoint F = inv F :=
  rfl

end Functor

end CategoryTheory

