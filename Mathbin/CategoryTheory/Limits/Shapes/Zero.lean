import Mathbin.CategoryTheory.Limits.Shapes.Products
import Mathbin.CategoryTheory.Limits.Shapes.Images
import Mathbin.CategoryTheory.IsomorphismClasses

/-!
# Zero morphisms and zero objects

A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. (Notice this is extra
structure, not merely a property.)

A category "has a zero object" if it has an object which is both initial and terminal. Having a
zero object provides zero morphisms, as the unique morphisms factoring through the zero object.

## References

* https://en.wikipedia.org/wiki/Zero_morphism
* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Category

namespace CategoryTheory.Limits

variable (C : Type u) [category.{v} C]

/-- A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. -/
class has_zero_morphisms where
  [HasZero : ∀ X Y : C, Zero (X ⟶ Y)]
  comp_zero' : ∀ {X Y : C} f : X ⟶ Y Z : C, f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) := by
    run_tac
      obviously
  zero_comp' : ∀ X : C {Y Z : C} f : Y ⟶ Z, (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) := by
    run_tac
      obviously

attribute [instance] has_zero_morphisms.has_zero

restate_axiom has_zero_morphisms.comp_zero'

restate_axiom has_zero_morphisms.zero_comp'

variable {C}

@[simp]
theorem comp_zero [has_zero_morphisms C] {X Y : C} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) :=
  has_zero_morphisms.comp_zero f Z

@[simp]
theorem zero_comp [has_zero_morphisms C] {X : C} {Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) :=
  has_zero_morphisms.zero_comp X f

instance has_zero_morphisms_pempty : has_zero_morphisms (discrete Pempty) where
  HasZero := by
    tidy

instance has_zero_morphisms_punit : has_zero_morphisms (discrete PUnit) where
  HasZero := by
    tidy

namespace HasZeroMorphisms

variable {C}

/-- This lemma will be immediately superseded by `ext`, below. -/
private theorem ext_aux (I J : has_zero_morphisms C)
    (w : ∀ X Y : C, (@has_zero_morphisms.has_zero _ _ I X Y).zero = (@has_zero_morphisms.has_zero _ _ J X Y).zero) :
    I = J := by
  cases' I
  cases' J
  congr
  · ext X Y
    exact w X Y
    
  · apply proof_irrel_heq
    
  · apply proof_irrel_heq
    

/-- If you're tempted to use this lemma "in the wild", you should probably
carefully consider whether you've made a mistake in allowing two
instances of `has_zero_morphisms` to exist at all.

See, particularly, the note on `zero_morphisms_of_zero_object` below.
-/
theorem ext (I J : has_zero_morphisms C) : I = J := by
  apply ext_aux
  intro X Y
  rw [← @has_zero_morphisms.comp_zero _ _ I X X (@has_zero_morphisms.has_zero _ _ J X X).zero]
  rw [@has_zero_morphisms.zero_comp _ _ J]

instance : Subsingleton (has_zero_morphisms C) :=
  ⟨ext⟩

end HasZeroMorphisms

open Opposite HasZeroMorphisms

instance has_zero_morphisms_opposite [has_zero_morphisms C] : has_zero_morphisms (Cᵒᵖ) where
  HasZero := fun X Y => ⟨(0 : unop Y ⟶ unop X).op⟩
  comp_zero' := fun X Y f Z => congr_argₓ Quiver.Hom.op (has_zero_morphisms.zero_comp (unop Z) f.unop)
  zero_comp' := fun X Y Z f => congr_argₓ Quiver.Hom.op (has_zero_morphisms.comp_zero f.unop (unop X))

section

variable {C} [has_zero_morphisms C]

theorem zero_of_comp_mono {X Y Z : C} {f : X ⟶ Y} (g : Y ⟶ Z) [mono g] (h : f ≫ g = 0) : f = 0 := by
  rw [← zero_comp, cancel_mono] at h
  exact h

theorem zero_of_epi_comp {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} [epi f] (h : f ≫ g = 0) : g = 0 := by
  rw [← comp_zero, cancel_epi] at h
  exact h

theorem eq_zero_of_image_eq_zero {X Y : C} {f : X ⟶ Y} [has_image f] (w : image.ι f = 0) : f = 0 := by
  rw [← image.fac f, w, has_zero_morphisms.comp_zero]

theorem nonzero_image_of_nonzero {X Y : C} {f : X ⟶ Y} [has_image f] (w : f ≠ 0) : image.ι f ≠ 0 := fun h =>
  w (eq_zero_of_image_eq_zero h)

end

section

universe v' u'

variable (D : Type u') [category.{v'} D]

variable [has_zero_morphisms D]

instance : has_zero_morphisms (C ⥤ D) where
  HasZero := fun F G => ⟨{ app := fun X => 0 }⟩

@[simp]
theorem zero_app (F G : C ⥤ D) (j : C) : (0 : F ⟶ G).app j = 0 :=
  rfl

variable [has_zero_morphisms C]

theorem equivalence_preserves_zero_morphisms (F : C ≌ D) (X Y : C) :
    F.functor.map (0 : X ⟶ Y) = (0 : F.functor.obj X ⟶ F.functor.obj Y) :=
  have t : F.functor.map (0 : X ⟶ Y) = F.functor.map (0 : X ⟶ Y) ≫ (0 : F.functor.obj Y ⟶ F.functor.obj Y) := by
    apply faithful.map_injective F.inverse
    rw [functor.map_comp, equivalence.inv_fun_map]
    dsimp
    rw [zero_comp, comp_zero, zero_comp]
  t.trans
    (by
      simp )

@[simp]
theorem is_equivalence_preserves_zero_morphisms (F : C ⥤ D) [is_equivalence F] (X Y : C) : F.map (0 : X ⟶ Y) = 0 := by
  rw [← functor.as_equivalence_functor F, equivalence_preserves_zero_morphisms]

end

variable (C)

/-- A category "has a zero object" if it has an object which is both initial and terminal. -/
class has_zero_object where
  zero : C
  uniqueTo : ∀ X : C, Unique (zero ⟶ X)
  uniqueFrom : ∀ X : C, Unique (X ⟶ zero)

instance has_zero_object_punit : has_zero_object (discrete PUnit) where
  zero := PUnit.unit
  uniqueTo := by
    tidy
  uniqueFrom := by
    tidy

variable {C}

namespace HasZeroObject

variable [has_zero_object C]

/-- Construct a `has_zero C` for a category with a zero object.
This can not be a global instance as it will trigger for every `has_zero C` typeclass search.
-/
protected def Zero : Zero C where
  zero := has_zero_object.zero

localized [ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.hasZero

localized [ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.uniqueTo

localized [ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.uniqueFrom

@[ext]
theorem to_zero_ext {X : C} (f g : X ⟶ 0) : f = g := by
  rw [(has_zero_object.unique_from X).uniq f, (has_zero_object.unique_from X).uniq g]

@[ext]
theorem from_zero_ext {X : C} (f g : 0 ⟶ X) : f = g := by
  rw [(has_zero_object.unique_to X).uniq f, (has_zero_object.unique_to X).uniq g]

instance (X : C) : Subsingleton (X ≅ 0) := by
  tidy

instance {X : C} (f : 0 ⟶ X) : mono f where
  right_cancellation := fun Z g h w => by
    ext

instance {X : C} (f : X ⟶ 0) : epi f where
  left_cancellation := fun Z g h w => by
    ext

/-- A category with a zero object has zero morphisms.

    It is rarely a good idea to use this. Many categories that have a zero object have zero
    morphisms for some other reason, for example from additivity. Library code that uses
    `zero_morphisms_of_zero_object` will then be incompatible with these categories because
    the `has_zero_morphisms` instances will not be definitionally equal. For this reason library
    code should generally ask for an instance of `has_zero_morphisms` separately, even if it already
    asks for an instance of `has_zero_objects`. -/
def zero_morphisms_of_zero_object : has_zero_morphisms C where
  HasZero := fun X Y => { zero := (default : X ⟶ 0) ≫ default }
  zero_comp' := fun X Y Z f => by
    dunfold Zero.zero
    rw [category.assoc]
    congr
  comp_zero' := fun X Y Z f => by
    dunfold Zero.zero
    rw [← category.assoc]
    congr

/-- A zero object is in particular initial. -/
def zero_is_initial : is_initial (0 : C) :=
  is_initial.of_unique 0

/-- A zero object is in particular terminal. -/
def zero_is_terminal : is_terminal (0 : C) :=
  is_terminal.of_unique 0

/-- A zero object is in particular initial. -/
instance (priority := 10) has_initial : has_initial C :=
  has_initial_of_unique 0

/-- A zero object is in particular terminal. -/
instance (priority := 10) has_terminal : has_terminal C :=
  has_terminal_of_unique 0

instance (priority := 100) has_strict_initial : initial_mono_class C :=
  initial_mono_class.of_is_initial zero_is_initial fun X => CategoryTheory.Mono _

open_locale ZeroObject

instance {B : Type _} [category B] [has_zero_morphisms C] : has_zero_object (B ⥤ C) where
  zero := { obj := fun X => 0, map := fun X Y f => 0 }
  uniqueTo := fun F =>
    ⟨⟨{ app := fun X => 0 }⟩, by
      tidy⟩
  uniqueFrom := fun F =>
    ⟨⟨{ app := fun X => 0 }⟩, by
      tidy⟩

@[simp]
theorem functor.zero_obj {B : Type _} [category B] [has_zero_morphisms C] (X : B) : (0 : B ⥤ C).obj X = 0 :=
  rfl

@[simp]
theorem functor.zero_map {B : Type _} [category B] [has_zero_morphisms C] {X Y : B} (f : X ⟶ Y) :
    (0 : B ⥤ C).map f = 0 :=
  rfl

end HasZeroObject

section

variable [has_zero_object C] [has_zero_morphisms C]

open_locale ZeroObject

@[simp]
theorem id_zero : 𝟙 (0 : C) = (0 : 0 ⟶ 0) := by
  ext

/-- An arrow ending in the zero object is zero -/
theorem zero_of_to_zero {X : C} (f : X ⟶ 0) : f = 0 := by
  ext

theorem zero_of_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : f = 0 := by
  have h : f = f ≫ i.hom ≫ 𝟙 0 ≫ i.inv := by
    simp only [iso.hom_inv_id, id_comp, comp_id]
  simpa using h

/-- An arrow starting at the zero object is zero -/
theorem zero_of_from_zero {X : C} (f : 0 ⟶ X) : f = 0 := by
  ext

theorem zero_of_source_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : f = 0 := by
  have h : f = i.hom ≫ 𝟙 0 ≫ i.inv ≫ f := by
    simp only [iso.hom_inv_id_assoc, id_comp, comp_id]
  simpa using h

theorem zero_of_source_iso_zero' {X Y : C} (f : X ⟶ Y) (i : is_isomorphic X 0) : f = 0 :=
  zero_of_source_iso_zero f (Nonempty.some i)

theorem zero_of_target_iso_zero' {X Y : C} (f : X ⟶ Y) (i : is_isomorphic Y 0) : f = 0 :=
  zero_of_target_iso_zero f (Nonempty.some i)

theorem mono_of_source_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : mono f :=
  ⟨fun Z g h w => by
    rw [zero_of_target_iso_zero g i, zero_of_target_iso_zero h i]⟩

theorem epi_of_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : epi f :=
  ⟨fun Z g h w => by
    rw [zero_of_source_iso_zero g i, zero_of_source_iso_zero h i]⟩

/-- An object `X` has `𝟙 X = 0` if and only if it is isomorphic to the zero object.

Because `X ≅ 0` contains data (even if a subsingleton), we express this `↔` as an `≃`.
-/
def id_zero_equiv_iso_zero (X : C) : 𝟙 X = 0 ≃ (X ≅ 0) where
  toFun := fun h => { Hom := 0, inv := 0 }
  invFun := fun i => zero_of_target_iso_zero (𝟙 X) i
  left_inv := by
    tidy
  right_inv := by
    tidy

@[simp]
theorem id_zero_equiv_iso_zero_apply_hom (X : C) (h : 𝟙 X = 0) : ((id_zero_equiv_iso_zero X) h).Hom = 0 :=
  rfl

@[simp]
theorem id_zero_equiv_iso_zero_apply_inv (X : C) (h : 𝟙 X = 0) : ((id_zero_equiv_iso_zero X) h).inv = 0 :=
  rfl

/-- If `0 : X ⟶ Y` is an monomorphism, then `X ≅ 0`. -/
@[simps]
def iso_zero_of_mono_zero {X Y : C} (h : mono (0 : X ⟶ Y)) : X ≅ 0 where
  Hom := 0
  inv := 0
  hom_inv_id' :=
    (cancel_mono (0 : X ⟶ Y)).mp
      (by
        simp )

/-- If `0 : X ⟶ Y` is an epimorphism, then `Y ≅ 0`. -/
@[simps]
def iso_zero_of_epi_zero {X Y : C} (h : epi (0 : X ⟶ Y)) : Y ≅ 0 where
  Hom := 0
  inv := 0
  hom_inv_id' :=
    (cancel_epi (0 : X ⟶ Y)).mp
      (by
        simp )

/-- If an object `X` is isomorphic to 0, there's no need to use choice to construct
an explicit isomorphism: the zero morphism suffices. -/
def iso_of_is_isomorphic_zero {X : C} (P : is_isomorphic X 0) : X ≅ 0 where
  Hom := 0
  inv := 0
  hom_inv_id' := by
    cases' P
    rw [← P.hom_inv_id]
    rw [← category.id_comp P.inv]
    simp
  inv_hom_id' := by
    simp

end

section IsIso

variable [has_zero_morphisms C]

/-- A zero morphism `0 : X ⟶ Y` is an isomorphism if and only if
the identities on both `X` and `Y` are zero.
-/
@[simps]
def is_iso_zero_equiv (X Y : C) : is_iso (0 : X ⟶ Y) ≃ 𝟙 X = 0 ∧ 𝟙 Y = 0 where
  toFun := by
    intros i
    rw [← is_iso.hom_inv_id (0 : X ⟶ Y)]
    rw [← is_iso.inv_hom_id (0 : X ⟶ Y)]
    simp
  invFun := fun h =>
    ⟨⟨(0 : Y ⟶ X), by
        tidy⟩⟩
  left_inv := by
    tidy
  right_inv := by
    tidy

/-- A zero morphism `0 : X ⟶ X` is an isomorphism if and only if
the identity on `X` is zero.
-/
def is_iso_zero_self_equiv (X : C) : is_iso (0 : X ⟶ X) ≃ 𝟙 X = 0 := by
  simpa using is_iso_zero_equiv X X

variable [has_zero_object C]

open_locale ZeroObject

/-- A zero morphism `0 : X ⟶ Y` is an isomorphism if and only if
`X` and `Y` are isomorphic to the zero object.
-/
def is_iso_zero_equiv_iso_zero (X Y : C) : is_iso (0 : X ⟶ Y) ≃ (X ≅ 0) × (Y ≅ 0) := by
  refine' (is_iso_zero_equiv X Y).trans _
  symm
  fconstructor
  · rintro ⟨eX, eY⟩
    fconstructor
    exact (id_zero_equiv_iso_zero X).symm eX
    exact (id_zero_equiv_iso_zero Y).symm eY
    
  · rintro ⟨hX, hY⟩
    fconstructor
    exact (id_zero_equiv_iso_zero X) hX
    exact (id_zero_equiv_iso_zero Y) hY
    
  · tidy
    
  · tidy
    

theorem is_iso_of_source_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) (j : Y ≅ 0) : is_iso f := by
  rw [zero_of_source_iso_zero f i]
  exact (is_iso_zero_equiv_iso_zero _ _).invFun ⟨i, j⟩

/-- A zero morphism `0 : X ⟶ X` is an isomorphism if and only if
`X` is isomorphic to the zero object.
-/
def is_iso_zero_self_equiv_iso_zero (X : C) : is_iso (0 : X ⟶ X) ≃ (X ≅ 0) :=
  (is_iso_zero_equiv_iso_zero X X).trans subsingletonProdSelfEquiv

end IsIso

/-- If there are zero morphisms, any initial object is a zero object. -/
def has_zero_object_of_has_initial_object [has_zero_morphisms C] [has_initial C] : has_zero_object C where
  zero := ⊥_ C
  uniqueTo := fun X =>
    ⟨⟨0⟩, by
      tidy⟩
  uniqueFrom := fun X =>
    ⟨⟨0⟩, fun f =>
      calc
        f = f ≫ 𝟙 _ := (category.comp_id _).symm
        _ = f ≫ 0 := by
          congr
        _ = 0 := has_zero_morphisms.comp_zero _ _
        ⟩

/-- If there are zero morphisms, any terminal object is a zero object. -/
def has_zero_object_of_has_terminal_object [has_zero_morphisms C] [has_terminal C] : has_zero_object C where
  zero := ⊤_ C
  uniqueFrom := fun X =>
    ⟨⟨0⟩, by
      tidy⟩
  uniqueTo := fun X =>
    ⟨⟨0⟩, fun f =>
      calc
        f = 𝟙 _ ≫ f := (category.id_comp _).symm
        _ = 0 ≫ f := by
          congr
        _ = 0 := zero_comp
        ⟩

section Image

variable [has_zero_morphisms C]

theorem image_ι_comp_eq_zero {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [has_image f] [epi (factor_thru_image f)]
    (h : f ≫ g = 0) : image.ι f ≫ g = 0 :=
  zero_of_epi_comp (factor_thru_image f) <| by
    simp [h]

theorem comp_factor_thru_image_eq_zero {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [has_image g] (h : f ≫ g = 0) :
    f ≫ factor_thru_image g = 0 :=
  zero_of_comp_mono (image.ι g) <| by
    simp [h]

variable [has_zero_object C]

open_locale ZeroObject

/-- The zero morphism has a `mono_factorisation` through the zero object.
-/
@[simps]
def mono_factorisation_zero (X Y : C) : mono_factorisation (0 : X ⟶ Y) where
  i := 0
  m := 0
  e := 0

/-- The factorisation through the zero object is an image factorisation.
-/
def image_factorisation_zero (X Y : C) : image_factorisation (0 : X ⟶ Y) where
  f := mono_factorisation_zero X Y
  IsImage := { lift := fun F' => 0 }

instance has_image_zero {X Y : C} : has_image (0 : X ⟶ Y) :=
  has_image.mk <| image_factorisation_zero _ _

/-- The image of a zero morphism is the zero object. -/
def image_zero {X Y : C} : image (0 : X ⟶ Y) ≅ 0 :=
  is_image.iso_ext (image.is_image (0 : X ⟶ Y)) (image_factorisation_zero X Y).IsImage

/-- The image of a morphism which is equal to zero is the zero object. -/
def image_zero' {X Y : C} {f : X ⟶ Y} (h : f = 0) [has_image f] : image f ≅ 0 :=
  image.eq_to_iso h ≪≫ image_zero

@[simp]
theorem image.ι_zero {X Y : C} [has_image (0 : X ⟶ Y)] : image.ι (0 : X ⟶ Y) = 0 := by
  rw [← image.lift_fac (mono_factorisation_zero X Y)]
  simp

/-- If we know `f = 0`,
it requires a little work to conclude `image.ι f = 0`,
because `f = g` only implies `image f ≅ image g`.
-/
@[simp]
theorem image.ι_zero' [has_equalizers C] {X Y : C} {f : X ⟶ Y} (h : f = 0) [has_image f] : image.ι f = 0 := by
  rw [image.eq_fac h]
  simp

end Image

/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
instance split_mono_sigma_ι {β : Type v} [DecidableEq β] [has_zero_morphisms C] (f : β → C)
    [has_colimit (discrete.functor f)] (b : β) : split_mono (sigma.ι f b) where
  retraction := sigma.desc fun b' => if h : b' = b then eq_to_hom (congr_argₓ f h) else 0

/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
instance split_epi_pi_π {β : Type v} [DecidableEq β] [has_zero_morphisms C] (f : β → C) [has_limit (discrete.functor f)]
    (b : β) : split_epi (pi.π f b) where
  section_ := pi.lift fun b' => if h : b = b' then eq_to_hom (congr_argₓ f h) else 0

/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
instance split_mono_coprod_inl [has_zero_morphisms C] {X Y : C} [has_colimit (pair X Y)] :
    split_mono (coprod.inl : X ⟶ X ⨿ Y) where
  retraction := coprod.desc (𝟙 X) 0

/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
instance split_mono_coprod_inr [has_zero_morphisms C] {X Y : C} [has_colimit (pair X Y)] :
    split_mono (coprod.inr : Y ⟶ X ⨿ Y) where
  retraction := coprod.desc 0 (𝟙 Y)

/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
instance split_epi_prod_fst [has_zero_morphisms C] {X Y : C} [has_limit (pair X Y)] :
    split_epi (Prod.fst : X ⨯ Y ⟶ X) where
  section_ := prod.lift (𝟙 X) 0

/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
instance split_epi_prod_snd [has_zero_morphisms C] {X Y : C} [has_limit (pair X Y)] :
    split_epi (Prod.snd : X ⨯ Y ⟶ Y) where
  section_ := prod.lift 0 (𝟙 Y)

end CategoryTheory.Limits

