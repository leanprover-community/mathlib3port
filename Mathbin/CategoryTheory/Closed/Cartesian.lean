import Mathbin.CategoryTheory.EpiMono
import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathbin.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Adjunction.Limits
import Mathbin.CategoryTheory.Adjunction.Mates
import Mathbin.CategoryTheory.Closed.Monoidal

/-!
# Cartesian closed categories

Given a category with finite products, the cartesian monoidal structure is provided by the local
instance `monoidal_of_has_finite_products`.

We define exponentiable objects to be closed objects with respect to this monoidal structure,
i.e. `(X × -)` is a left adjoint.

We say a category is cartesian closed if every object is exponentiable
(equivalently, that the category equipped with the cartesian monoidal structure is closed monoidal).

Show that exponential forms a difunctor and define the exponential comparison morphisms.

## TODO
Some of the results here are true more generally for closed objects and
for closed monoidal categories, and these could be generalised.
-/


universe v u u₂

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

attribute [local instance] monoidal_of_has_finite_products

/-- An object `X` is *exponentiable* if `(X × -)` is a left adjoint.
We define this as being `closed` in the cartesian monoidal structure.
-/
abbrev exponentiable {C : Type u} [category.{v} C] [has_finite_products C] (X : C) :=
  closed X

/-- If `X` and `Y` are exponentiable then `X ⨯ Y` is.
This isn't an instance because it's not usually how we want to construct exponentials, we'll usually
prove all objects are exponential uniformly.
-/
def binary_product_exponentiable {C : Type u} [category.{v} C] [has_finite_products C] {X Y : C} (hX : exponentiable X)
    (hY : exponentiable Y) : exponentiable (X ⨯ Y) where
  isAdj := by
    have := hX.is_adj
    have := hY.is_adj
    exact adjunction.left_adjoint_of_nat_iso (monoidal_category.tensor_left_tensor _ _).symm

/-- The terminal object is always exponentiable.
This isn't an instance because most of the time we'll prove cartesian closed for all objects
at once, rather than just for this one.
-/
def terminal_exponentiable {C : Type u} [category.{v} C] [has_finite_products C] : exponentiable (⊤_ C) :=
  unit_closed

/-- A category `C` is cartesian closed if it has finite products and every object is exponentiable.
We define this as `monoidal_closed` with respect to the cartesian monoidal structure.
-/
abbrev cartesian_closed (C : Type u) [category.{v} C] [has_finite_products C] :=
  monoidal_closed C

variable {C : Type u} [category.{v} C] (A B : C) {X X' Y Y' Z : C}

section Exp

variable [has_finite_products C] [exponentiable A]

/-- This is (-)^A. -/
def exp : C ⥤ C :=
  (@closed.is_adj _ _ _ A _).right

/-- The adjunction between A ⨯ - and (-)^A. -/
def exp.adjunction : prod.functor.obj A ⊣ exp A :=
  closed.is_adj.adj

/-- The evaluation natural transformation. -/
def ev : exp A ⋙ prod.functor.obj A ⟶ 𝟭 C :=
  (exp.adjunction A).counit

/-- The coevaluation natural transformation. -/
def coev : 𝟭 C ⟶ prod.functor.obj A ⋙ exp A :=
  (exp.adjunction A).Unit

@[simp]
theorem exp_adjunction_counit : (exp.adjunction A).counit = ev A :=
  rfl

@[simp]
theorem exp_adjunction_unit : (exp.adjunction A).Unit = coev A :=
  rfl

@[simp, reassoc]
theorem ev_naturality {X Y : C} (f : X ⟶ Y) : limits.prod.map (𝟙 A) ((exp A).map f) ≫ (ev A).app Y = (ev A).app X ≫ f :=
  (ev A).naturality f

@[simp, reassoc]
theorem coev_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (coev A).app Y = (coev A).app X ≫ (exp A).map (limits.prod.map (𝟙 A) f) :=
  (coev A).naturality f

notation:20 A " ⟹ " B:19 => (exp A).obj B

notation:30 B " ^^ " A:30 => (exp A).obj B

@[simp, reassoc]
theorem ev_coev : limits.prod.map (𝟙 A) ((coev A).app B) ≫ (ev A).app (A ⨯ B) = 𝟙 (A ⨯ B) :=
  adjunction.left_triangle_components (exp.adjunction A)

@[simp, reassoc]
theorem coev_ev : (coev A).app (A ⟹ B) ≫ (exp A).map ((ev A).app B) = 𝟙 (A ⟹ B) :=
  adjunction.right_triangle_components (exp.adjunction A)

instance : preserves_colimits (prod.functor.obj A) :=
  (exp.adjunction A).leftAdjointPreservesColimits

end Exp

variable {A}

namespace CartesianClosed

variable [has_finite_products C] [exponentiable A]

/-- Currying in a cartesian closed category. -/
def curry : (A ⨯ Y ⟶ X) → (Y ⟶ A ⟹ X) :=
  (exp.adjunction A).homEquiv _ _

/-- Uncurrying in a cartesian closed category. -/
def uncurry : (Y ⟶ A ⟹ X) → (A ⨯ Y ⟶ X) :=
  ((exp.adjunction A).homEquiv _ _).symm

@[simp]
theorem hom_equiv_apply_eq (f : A ⨯ Y ⟶ X) : (exp.adjunction A).homEquiv _ _ f = curry f :=
  rfl

@[simp]
theorem hom_equiv_symm_apply_eq (f : Y ⟶ A ⟹ X) : ((exp.adjunction A).homEquiv _ _).symm f = uncurry f :=
  rfl

@[reassoc]
theorem curry_natural_left (f : X ⟶ X') (g : A ⨯ X' ⟶ Y) : curry (limits.prod.map (𝟙 _) f ≫ g) = f ≫ curry g :=
  adjunction.hom_equiv_naturality_left _ _ _

@[reassoc]
theorem curry_natural_right (f : A ⨯ X ⟶ Y) (g : Y ⟶ Y') : curry (f ≫ g) = curry f ≫ (exp _).map g :=
  adjunction.hom_equiv_naturality_right _ _ _

@[reassoc]
theorem uncurry_natural_right (f : X ⟶ A ⟹ Y) (g : Y ⟶ Y') : uncurry (f ≫ (exp _).map g) = uncurry f ≫ g :=
  adjunction.hom_equiv_naturality_right_symm _ _ _

@[reassoc]
theorem uncurry_natural_left (f : X ⟶ X') (g : X' ⟶ A ⟹ Y) : uncurry (f ≫ g) = limits.prod.map (𝟙 _) f ≫ uncurry g :=
  adjunction.hom_equiv_naturality_left_symm _ _ _

@[simp]
theorem uncurry_curry (f : A ⨯ X ⟶ Y) : uncurry (curry f) = f :=
  (closed.is_adj.adj.homEquiv _ _).left_inv f

@[simp]
theorem curry_uncurry (f : X ⟶ A ⟹ Y) : curry (uncurry f) = f :=
  (closed.is_adj.adj.homEquiv _ _).right_inv f

theorem curry_eq_iff (f : A ⨯ Y ⟶ X) (g : Y ⟶ A ⟹ X) : curry f = g ↔ f = uncurry g :=
  adjunction.hom_equiv_apply_eq _ f g

theorem eq_curry_iff (f : A ⨯ Y ⟶ X) (g : Y ⟶ A ⟹ X) : g = curry f ↔ uncurry g = f :=
  adjunction.eq_hom_equiv_apply _ f g

theorem uncurry_eq (g : Y ⟶ A ⟹ X) : uncurry g = limits.prod.map (𝟙 A) g ≫ (ev A).app X :=
  adjunction.hom_equiv_counit _

theorem curry_eq (g : A ⨯ Y ⟶ X) : curry g = (coev A).app Y ≫ (exp A).map g :=
  adjunction.hom_equiv_unit _

theorem uncurry_id_eq_ev (A X : C) [exponentiable A] : uncurry (𝟙 (A ⟹ X)) = (ev A).app X := by
  rw [uncurry_eq, prod.map_id_id, id_comp]

theorem curry_id_eq_coev (A X : C) [exponentiable A] : curry (𝟙 _) = (coev A).app X := by
  rw [curry_eq, (exp A).map_id (A ⨯ _)]
  apply comp_id

theorem curry_injective : Function.Injective (curry : (A ⨯ Y ⟶ X) → (Y ⟶ A ⟹ X)) :=
  (closed.is_adj.adj.homEquiv _ _).Injective

theorem uncurry_injective : Function.Injective (uncurry : (Y ⟶ A ⟹ X) → (A ⨯ Y ⟶ X)) :=
  (closed.is_adj.adj.homEquiv _ _).symm.Injective

end CartesianClosed

open CartesianClosed

variable [has_finite_products C] [exponentiable A]

/-- Show that the exponential of the terminal object is isomorphic to itself, i.e. `X^1 ≅ X`.

The typeclass argument is explicit: any instance can be used.
-/
def exp_terminal_iso_self [exponentiable (⊤_ C)] : (⊤_ C) ⟹ X ≅ X :=
  yoneda.ext ((⊤_ C) ⟹ X) X (fun Y f => (prod.left_unitor Y).inv ≫ cartesian_closed.uncurry f)
    (fun Y f => cartesian_closed.curry ((prod.left_unitor Y).Hom ≫ f))
    (fun Z g => by
      rw [curry_eq_iff, iso.hom_inv_id_assoc])
    (fun Z g => by
      simp )
    fun Z W f g => by
    rw [uncurry_natural_left, prod.left_unitor_inv_naturality_assoc f]

/-- The internal element which points at the given morphism. -/
def internalize_hom (f : A ⟶ Y) : ⊤_ C ⟶ A ⟹ Y :=
  cartesian_closed.curry (limits.prod.fst ≫ f)

section Pre

variable {B}

/-- Pre-compose an internal hom with an external hom. -/
def pre (f : B ⟶ A) [exponentiable B] : exp A ⟶ exp B :=
  transfer_nat_trans_self (exp.adjunction _) (exp.adjunction _) (prod.functor.map f)

theorem prod_map_pre_app_comp_ev (f : B ⟶ A) [exponentiable B] (X : C) :
    limits.prod.map (𝟙 B) ((pre f).app X) ≫ (ev B).app X = limits.prod.map f (𝟙 (A ⟹ X)) ≫ (ev A).app X :=
  transfer_nat_trans_self_counit _ _ (prod.functor.map f) X

theorem uncurry_pre (f : B ⟶ A) [exponentiable B] (X : C) :
    cartesian_closed.uncurry ((pre f).app X) = limits.prod.map f (𝟙 _) ≫ (ev A).app X := by
  rw [uncurry_eq, prod_map_pre_app_comp_ev]

theorem coev_app_comp_pre_app (f : B ⟶ A) [exponentiable B] :
    (coev A).app X ≫ (pre f).app (A ⨯ X) = (coev B).app X ≫ (exp B).map (limits.prod.map f (𝟙 _)) :=
  unit_transfer_nat_trans_self _ _ (prod.functor.map f) X

@[simp]
theorem pre_id (A : C) [exponentiable A] : pre (𝟙 A) = 𝟙 _ := by
  simp [pre]

@[simp]
theorem pre_map {A₁ A₂ A₃ : C} [exponentiable A₁] [exponentiable A₂] [exponentiable A₃] (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    pre (f ≫ g) = pre g ≫ pre f := by
  rw [pre, pre, pre, transfer_nat_trans_self_comp, prod.functor.map_comp]

end Pre

/-- The internal hom functor given by the cartesian closed structure. -/
def internal_hom [cartesian_closed C] : Cᵒᵖ ⥤ C ⥤ C where
  obj := fun X => exp X.unop
  map := fun X Y f => pre f.unop

/-- If an initial object `I` exists in a CCC, then `A ⨯ I ≅ I`. -/
@[simps]
def zero_mul {I : C} (t : is_initial I) : A ⨯ I ≅ I where
  Hom := limits.prod.snd
  inv := t.to _
  hom_inv_id' := by
    have : (limits.prod.snd : A ⨯ I ⟶ I) = cartesian_closed.uncurry (t.to _)
    rw [← curry_eq_iff]
    apply t.hom_ext
    rw [this, ← uncurry_natural_right, ← eq_curry_iff]
    apply t.hom_ext
  inv_hom_id' := t.hom_ext _ _

/-- If an initial object `0` exists in a CCC, then `0 ⨯ A ≅ 0`. -/
def mul_zero {I : C} (t : is_initial I) : I ⨯ A ≅ I :=
  limits.prod.braiding _ _ ≪≫ zero_mul t

/-- If an initial object `0` exists in a CCC then `0^B ≅ 1` for any `B`. -/
def pow_zeroₓ {I : C} (t : is_initial I) [cartesian_closed C] : I ⟹ B ≅ ⊤_ C where
  Hom := default _
  inv := cartesian_closed.curry ((mul_zero t).Hom ≫ t.to _)
  hom_inv_id' := by
    rw [← curry_natural_left, curry_eq_iff, ← cancel_epi (mul_zero t).inv]
    · apply t.hom_ext
      
    · infer_instance
      
    · infer_instance
      

/-- In a CCC with binary coproducts, the distribution morphism is an isomorphism. -/
def prod_coprod_distrib [has_binary_coproducts C] [cartesian_closed C] (X Y Z : C) : (Z ⨯ X) ⨿ Z ⨯ Y ≅ Z ⨯ X ⨿ Y where
  Hom := coprod.desc (limits.prod.map (𝟙 _) coprod.inl) (limits.prod.map (𝟙 _) coprod.inr)
  inv := cartesian_closed.uncurry (coprod.desc (cartesian_closed.curry coprod.inl) (cartesian_closed.curry coprod.inr))
  hom_inv_id' := by
    apply coprod.hom_ext
    rw [coprod.inl_desc_assoc, comp_id, ← uncurry_natural_left, coprod.inl_desc, uncurry_curry]
    rw [coprod.inr_desc_assoc, comp_id, ← uncurry_natural_left, coprod.inr_desc, uncurry_curry]
  inv_hom_id' := by
    rw [← uncurry_natural_right, ← eq_curry_iff]
    apply coprod.hom_ext
    rw [coprod.inl_desc_assoc, ← curry_natural_right, coprod.inl_desc, ← curry_natural_left, comp_id]
    rw [coprod.inr_desc_assoc, ← curry_natural_right, coprod.inr_desc, ← curry_natural_left, comp_id]

/-- If an initial object `I` exists in a CCC then it is a strict initial object,
i.e. any morphism to `I` is an iso.
This actually shows a slightly stronger version: any morphism to an initial object from an
exponentiable object is an isomorphism.
-/
theorem strict_initial {I : C} (t : is_initial I) (f : A ⟶ I) : is_iso f := by
  have : mono (limits.prod.lift (𝟙 A) f ≫ (zero_mul t).Hom) := mono_comp _ _
  rw [zero_mul_hom, prod.lift_snd] at _inst
  have : split_epi f := ⟨t.to _, t.hom_ext _ _⟩
  apply is_iso_of_mono_of_split_epi

instance to_initial_is_iso [has_initial C] (f : A ⟶ ⊥_ C) : is_iso f :=
  strict_initial initial_is_initial _

/-- If an initial object `0` exists in a CCC then every morphism from it is monic. -/
theorem initial_mono {I : C} (B : C) (t : is_initial I) [cartesian_closed C] : mono (t.to B) :=
  ⟨fun B g h _ => by
    have := strict_initial t g
    have := strict_initial t h
    exact eq_of_inv_eq_inv (t.hom_ext _ _)⟩

instance initial.mono_to [has_initial C] (B : C) [cartesian_closed C] : mono (initial.to B) :=
  initial_mono B initial_is_initial

variable {D : Type u₂} [category.{v} D]

section Functor

variable [has_finite_products D]

/-- Transport the property of being cartesian closed across an equivalence of categories.

Note we didn't require any coherence between the choice of finite products here, since we transport
along the `prod_comparison` isomorphism.
-/
def cartesian_closed_of_equiv (e : C ≌ D) [h : cartesian_closed C] : cartesian_closed D where
  closed := fun X =>
    { isAdj := by
        have q : exponentiable (e.inverse.obj X) := inferInstance
        have : is_left_adjoint (prod.functor.obj (e.inverse.obj X)) := q.is_adj
        have : e.functor ⋙ prod.functor.obj X ⋙ e.inverse ≅ prod.functor.obj (e.inverse.obj X)
        apply nat_iso.of_components _ _
        intro Y
        · apply as_iso (prod_comparison e.inverse X (e.functor.obj Y)) ≪≫ _
          apply prod.map_iso (iso.refl _) (e.unit_iso.app Y).symm
          
        · intro Y Z g
          dsimp [prod_comparison]
          simp [prod.comp_lift, ← e.inverse.map_comp, ← e.inverse.map_comp_assoc]
          dsimp
          simp
          
        · have : is_left_adjoint (e.functor ⋙ prod.functor.obj X ⋙ e.inverse) :=
            adjunction.left_adjoint_of_nat_iso this.symm
          have : is_left_adjoint (e.inverse ⋙ e.functor ⋙ prod.functor.obj X ⋙ e.inverse) :=
            adjunction.left_adjoint_of_comp e.inverse _
          have : (e.inverse ⋙ e.functor ⋙ prod.functor.obj X ⋙ e.inverse) ⋙ e.functor ≅ prod.functor.obj X := by
            apply iso_whisker_right e.counit_iso (prod.functor.obj X ⋙ e.inverse ⋙ e.functor) ≪≫ _
            change prod.functor.obj X ⋙ e.inverse ⋙ e.functor ≅ prod.functor.obj X
            apply iso_whisker_left (prod.functor.obj X) e.counit_iso
          skip
          apply adjunction.left_adjoint_of_nat_iso this
           }

end Functor

end CategoryTheory

