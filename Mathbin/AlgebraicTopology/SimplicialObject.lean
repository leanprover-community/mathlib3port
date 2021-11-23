import Mathbin.AlgebraicTopology.SimplexCategory 
import Mathbin.CategoryTheory.Arrow 
import Mathbin.CategoryTheory.Limits.FunctorCategory 
import Mathbin.CategoryTheory.Opposites

/-!
# Simplicial objects in a category.

A simplicial object in a category `C` is a `C`-valued presheaf on `simplex_category`.
(Similarly a cosimplicial object is functor `simplex_category ⥤ C`.)

Use the notation `X _[n]` in the `simplicial` locale to obtain the `n`-th term of a
(co)simplicial object `X`, where `n` is a natural number.

-/


open Opposite

open CategoryTheory

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable(C : Type u)[category.{v} C]

-- error in AlgebraicTopology.SimplicialObject: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler category
/-- The category of simplicial objects valued in a category `C`.
This is the category of contravariant functors from `simplex_category` to `C`. -/
@[derive #[expr category], nolint #[ident has_inhabited_instance]]
def simplicial_object :=
«expr ⥤ »(«expr ᵒᵖ»(simplex_category.{v}), C)

namespace SimplicialObject

localized [Simplicial]
  notation:1000 X "_[" n "]" => (X : CategoryTheory.SimplicialObject _).obj (Opposite.op (SimplexCategory.mk n))

instance  {J : Type v} [small_category J] [has_limits_of_shape J C] : has_limits_of_shape J (simplicial_object C) :=
  by 
    dsimp [simplicial_object]
    infer_instance

instance  [has_limits C] : has_limits (simplicial_object C) :=
  ⟨inferInstance⟩

instance  {J : Type v} [small_category J] [has_colimits_of_shape J C] : has_colimits_of_shape J (simplicial_object C) :=
  by 
    dsimp [simplicial_object]
    infer_instance

instance  [has_colimits C] : has_colimits (simplicial_object C) :=
  ⟨inferInstance⟩

variable{C}(X : simplicial_object C)

/-- Face maps for a simplicial object. -/
def δ {n} (i : Finₓ (n+2)) : X _[n+1] ⟶ X _[n] :=
  X.map (SimplexCategory.δ i).op

/-- Degeneracy maps for a simplicial object. -/
def σ {n} (i : Finₓ (n+1)) : X _[n] ⟶ X _[n+1] :=
  X.map (SimplexCategory.σ i).op

/-- Isomorphisms from identities in ℕ. -/
def eq_to_iso {n m : ℕ} (h : n = m) : X _[n] ≅ X _[m] :=
  X.map_iso
    (eq_to_iso
      (by 
        rw [h]))

@[simp]
theorem eq_to_iso_refl {n : ℕ} (h : n = n) : X.eq_to_iso h = iso.refl _ :=
  by 
    ext 
    simp [eq_to_iso]

/-- The generic case of the first simplicial identity -/
theorem δ_comp_δ {n} {i j : Finₓ (n+2)} (H : i ≤ j) : X.δ j.succ ≫ X.δ i = X.δ i.cast_succ ≫ X.δ j :=
  by 
    dsimp [δ]
    simp only [←X.map_comp, ←op_comp, SimplexCategory.δ_comp_δ H]

/-- The special case of the first simplicial identity -/
theorem δ_comp_δ_self {n} {i : Finₓ (n+2)} : X.δ i.cast_succ ≫ X.δ i = X.δ i.succ ≫ X.δ i :=
  by 
    dsimp [δ]
    simp only [←X.map_comp, ←op_comp, SimplexCategory.δ_comp_δ_self]

/-- The second simplicial identity -/
theorem δ_comp_σ_of_le {n} {i : Finₓ (n+2)} {j : Finₓ (n+1)} (H : i ≤ j.cast_succ) :
  X.σ j.succ ≫ X.δ i.cast_succ = X.δ i ≫ X.σ j :=
  by 
    dsimp [δ, σ]
    simp only [←X.map_comp, ←op_comp, SimplexCategory.δ_comp_σ_of_le H]

/-- The first part of the third simplicial identity -/
theorem δ_comp_σ_self {n} {i : Finₓ (n+1)} : X.σ i ≫ X.δ i.cast_succ = 𝟙 _ :=
  by 
    dsimp [δ, σ]
    simp only [←X.map_comp, ←op_comp, SimplexCategory.δ_comp_σ_self, op_id, X.map_id]

/-- The second part of the third simplicial identity -/
theorem δ_comp_σ_succ {n} {i : Finₓ (n+1)} : X.σ i ≫ X.δ i.succ = 𝟙 _ :=
  by 
    dsimp [δ, σ]
    simp only [←X.map_comp, ←op_comp, SimplexCategory.δ_comp_σ_succ, op_id, X.map_id]

/-- The fourth simplicial identity -/
theorem δ_comp_σ_of_gt {n} {i : Finₓ (n+2)} {j : Finₓ (n+1)} (H : j.cast_succ < i) :
  X.σ j.cast_succ ≫ X.δ i.succ = X.δ i ≫ X.σ j :=
  by 
    dsimp [δ, σ]
    simp only [←X.map_comp, ←op_comp, SimplexCategory.δ_comp_σ_of_gt H]

/-- The fifth simplicial identity -/
theorem σ_comp_σ {n} {i j : Finₓ (n+1)} (H : i ≤ j) : X.σ j ≫ X.σ i.cast_succ = X.σ i ≫ X.σ j.succ :=
  by 
    dsimp [δ, σ]
    simp only [←X.map_comp, ←op_comp, SimplexCategory.σ_comp_σ H]

variable(C)

/-- Functor composition induces a functor on simplicial objects. -/
@[simps]
def whiskering (D : Type _) [category.{v} D] : (C ⥤ D) ⥤ simplicial_object C ⥤ simplicial_object D :=
  whiskering_right _ _ _

-- error in AlgebraicTopology.SimplicialObject: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler category
/-- Truncated simplicial objects. -/
@[derive #[expr category], nolint #[ident has_inhabited_instance]]
def truncated (n : exprℕ()) :=
«expr ⥤ »(«expr ᵒᵖ»(simplex_category.truncated.{v} n), C)

variable{C}

namespace Truncated

instance  {n} {J : Type v} [small_category J] [has_limits_of_shape J C] :
  has_limits_of_shape J (simplicial_object.truncated C n) :=
  by 
    dsimp [truncated]
    infer_instance

instance  {n} [has_limits C] : has_limits (simplicial_object.truncated C n) :=
  ⟨inferInstance⟩

instance  {n} {J : Type v} [small_category J] [has_colimits_of_shape J C] :
  has_colimits_of_shape J (simplicial_object.truncated C n) :=
  by 
    dsimp [truncated]
    infer_instance

instance  {n} [has_colimits C] : has_colimits (simplicial_object.truncated C n) :=
  ⟨inferInstance⟩

variable(C)

/-- Functor composition induces a functor on truncated simplicial objects. -/
@[simps]
def whiskering {n} (D : Type _) [category.{v} D] : (C ⥤ D) ⥤ truncated C n ⥤ truncated D n :=
  whiskering_right _ _ _

variable{C}

end Truncated

section Skeleton

/-- The skeleton functor from simplicial objects to truncated simplicial objects. -/
def sk (n : ℕ) : simplicial_object C ⥤ simplicial_object.truncated C n :=
  (whiskering_left _ _ _).obj SimplexCategory.Truncated.inclusion.op

end Skeleton

variable(C)

/-- The constant simplicial object is the constant functor. -/
abbrev const : C ⥤ simplicial_object C :=
  CategoryTheory.Functor.const _

-- error in AlgebraicTopology.SimplicialObject: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler category
/-- The category of augmented simplicial objects, defined as a comma category. -/
@[derive #[expr category], nolint #[ident has_inhabited_instance]]
def augmented :=
comma («expr𝟭»() (simplicial_object C)) (const C)

variable{C}

namespace Augmented

/-- Drop the augmentation. -/
@[simps]
def drop : augmented C ⥤ simplicial_object C :=
  comma.fst _ _

/-- The point of the augmentation. -/
@[simps]
def point : augmented C ⥤ C :=
  comma.snd _ _

/-- The functor from augmented objects to arrows. -/
@[simps]
def to_arrow : augmented C ⥤ arrow C :=
  { obj := fun X => { left := drop.obj X _[0], right := point.obj X, Hom := X.hom.app _ },
    map :=
      fun X Y η =>
        { left := (drop.map η).app _, right := point.map η,
          w' :=
            by 
              dsimp 
              rw [←nat_trans.comp_app]
              erw [η.w]
              rfl } }

variable(C)

/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simp]
def whiskering_obj (D : Type _) [category.{v} D] (F : C ⥤ D) : augmented C ⥤ augmented D :=
  { obj :=
      fun X =>
        { left := ((whiskering _ _).obj F).obj (drop.obj X), right := F.obj (point.obj X),
          Hom := whisker_right X.hom F ≫ (functor.const_comp _ _ _).Hom },
    map :=
      fun X Y η =>
        { left := whisker_right η.left _, right := F.map η.right,
          w' :=
            by 
              ext 
              dsimp 
              erw [category.comp_id, category.comp_id, ←F.map_comp, ←F.map_comp, ←nat_trans.comp_app, η.w]
              rfl } }

/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simps]
def whiskering (D : Type _) [category.{v} D] : (C ⥤ D) ⥤ augmented C ⥤ augmented D :=
  { obj := whiskering_obj _ _, map := fun X Y η => { app := fun A => { left := whisker_left _ η, right := η.app _ } } }

variable{C}

end Augmented

open_locale Simplicial

/-- Aaugment a simplicial object with an object. -/
@[simps]
def augment (X : simplicial_object C) (X₀ : C) (f : X _[0] ⟶ X₀)
  (w : ∀ i : SimplexCategory g₁ g₂ : [0] ⟶ i, X.map g₁.op ≫ f = X.map g₂.op ≫ f) : simplicial_object.augmented C :=
  { left := X, right := X₀,
    Hom :=
      { app := fun i => X.map (SimplexCategory.const i.unop 0).op ≫ f,
        naturality' :=
          by 
            intro i j g 
            dsimp 
            rw [←g.op_unop]
            simpa only [←X.map_comp, ←category.assoc, category.comp_id, ←op_comp] using w _ _ _ } }

@[simp]
theorem augment_hom_zero (X : simplicial_object C) (X₀ : C) (f : X _[0] ⟶ X₀) w :
  (X.augment X₀ f w).Hom.app (op [0]) = f :=
  by 
    dsimp 
    erw [SimplexCategory.hom_zero_zero ([0].const 0), X.map_id, category.id_comp]

end SimplicialObject

-- error in AlgebraicTopology.SimplicialObject: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler category
/-- Cosimplicial objects. -/
@[derive #[expr category], nolint #[ident has_inhabited_instance]]
def cosimplicial_object :=
«expr ⥤ »(simplex_category.{v}, C)

namespace CosimplicialObject

localized [Simplicial]
  notation:1000 X "_[" n "]" => (X : CategoryTheory.CosimplicialObject _).obj (SimplexCategory.mk n)

instance  {J : Type v} [small_category J] [has_limits_of_shape J C] : has_limits_of_shape J (cosimplicial_object C) :=
  by 
    dsimp [cosimplicial_object]
    infer_instance

instance  [has_limits C] : has_limits (cosimplicial_object C) :=
  ⟨inferInstance⟩

instance  {J : Type v} [small_category J] [has_colimits_of_shape J C] :
  has_colimits_of_shape J (cosimplicial_object C) :=
  by 
    dsimp [cosimplicial_object]
    infer_instance

instance  [has_colimits C] : has_colimits (cosimplicial_object C) :=
  ⟨inferInstance⟩

variable{C}(X : cosimplicial_object C)

/-- Coface maps for a cosimplicial object. -/
def δ {n} (i : Finₓ (n+2)) : X _[n] ⟶ X _[n+1] :=
  X.map (SimplexCategory.δ i)

/-- Codegeneracy maps for a cosimplicial object. -/
def σ {n} (i : Finₓ (n+1)) : X _[n+1] ⟶ X _[n] :=
  X.map (SimplexCategory.σ i)

/-- Isomorphisms from identities in ℕ. -/
def eq_to_iso {n m : ℕ} (h : n = m) : X _[n] ≅ X _[m] :=
  X.map_iso
    (eq_to_iso
      (by 
        rw [h]))

@[simp]
theorem eq_to_iso_refl {n : ℕ} (h : n = n) : X.eq_to_iso h = iso.refl _ :=
  by 
    ext 
    simp [eq_to_iso]

/-- The generic case of the first cosimplicial identity -/
theorem δ_comp_δ {n} {i j : Finₓ (n+2)} (H : i ≤ j) : X.δ i ≫ X.δ j.succ = X.δ j ≫ X.δ i.cast_succ :=
  by 
    dsimp [δ]
    simp only [←X.map_comp, SimplexCategory.δ_comp_δ H]

/-- The special case of the first cosimplicial identity -/
theorem δ_comp_δ_self {n} {i : Finₓ (n+2)} : X.δ i ≫ X.δ i.cast_succ = X.δ i ≫ X.δ i.succ :=
  by 
    dsimp [δ]
    simp only [←X.map_comp, SimplexCategory.δ_comp_δ_self]

/-- The second cosimplicial identity -/
theorem δ_comp_σ_of_le {n} {i : Finₓ (n+2)} {j : Finₓ (n+1)} (H : i ≤ j.cast_succ) :
  X.δ i.cast_succ ≫ X.σ j.succ = X.σ j ≫ X.δ i :=
  by 
    dsimp [δ, σ]
    simp only [←X.map_comp, SimplexCategory.δ_comp_σ_of_le H]

/-- The first part of the third cosimplicial identity -/
theorem δ_comp_σ_self {n} {i : Finₓ (n+1)} : X.δ i.cast_succ ≫ X.σ i = 𝟙 _ :=
  by 
    dsimp [δ, σ]
    simp only [←X.map_comp, SimplexCategory.δ_comp_σ_self, X.map_id]

/-- The second part of the third cosimplicial identity -/
theorem δ_comp_σ_succ {n} {i : Finₓ (n+1)} : X.δ i.succ ≫ X.σ i = 𝟙 _ :=
  by 
    dsimp [δ, σ]
    simp only [←X.map_comp, SimplexCategory.δ_comp_σ_succ, X.map_id]

/-- The fourth cosimplicial identity -/
theorem δ_comp_σ_of_gt {n} {i : Finₓ (n+2)} {j : Finₓ (n+1)} (H : j.cast_succ < i) :
  X.δ i.succ ≫ X.σ j.cast_succ = X.σ j ≫ X.δ i :=
  by 
    dsimp [δ, σ]
    simp only [←X.map_comp, SimplexCategory.δ_comp_σ_of_gt H]

/-- The fifth cosimplicial identity -/
theorem σ_comp_σ {n} {i j : Finₓ (n+1)} (H : i ≤ j) : X.σ i.cast_succ ≫ X.σ j = X.σ j.succ ≫ X.σ i :=
  by 
    dsimp [δ, σ]
    simp only [←X.map_comp, SimplexCategory.σ_comp_σ H]

variable(C)

/-- Functor composition induces a functor on cosimplicial objects. -/
@[simps]
def whiskering (D : Type _) [category.{v} D] : (C ⥤ D) ⥤ cosimplicial_object C ⥤ cosimplicial_object D :=
  whiskering_right _ _ _

-- error in AlgebraicTopology.SimplicialObject: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler category
/-- Truncated cosimplicial objects. -/
@[derive #[expr category], nolint #[ident has_inhabited_instance]]
def truncated (n : exprℕ()) :=
«expr ⥤ »(simplex_category.truncated.{v} n, C)

variable{C}

namespace Truncated

instance  {n} {J : Type v} [small_category J] [has_limits_of_shape J C] :
  has_limits_of_shape J (cosimplicial_object.truncated C n) :=
  by 
    dsimp [truncated]
    infer_instance

instance  {n} [has_limits C] : has_limits (cosimplicial_object.truncated C n) :=
  ⟨inferInstance⟩

instance  {n} {J : Type v} [small_category J] [has_colimits_of_shape J C] :
  has_colimits_of_shape J (cosimplicial_object.truncated C n) :=
  by 
    dsimp [truncated]
    infer_instance

instance  {n} [has_colimits C] : has_colimits (cosimplicial_object.truncated C n) :=
  ⟨inferInstance⟩

variable(C)

/-- Functor composition induces a functor on truncated cosimplicial objects. -/
@[simps]
def whiskering {n} (D : Type _) [category.{v} D] : (C ⥤ D) ⥤ truncated C n ⥤ truncated D n :=
  whiskering_right _ _ _

variable{C}

end Truncated

section Skeleton

/-- The skeleton functor from cosimplicial objects to truncated cosimplicial objects. -/
def sk (n : ℕ) : cosimplicial_object C ⥤ cosimplicial_object.truncated C n :=
  (whiskering_left _ _ _).obj SimplexCategory.Truncated.inclusion

end Skeleton

variable(C)

/-- The constant cosimplicial object. -/
abbrev const : C ⥤ cosimplicial_object C :=
  CategoryTheory.Functor.const _

-- error in AlgebraicTopology.SimplicialObject: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler category
/-- Augmented cosimplicial objects. -/
@[derive #[expr category], nolint #[ident has_inhabited_instance]]
def augmented :=
comma (const C) («expr𝟭»() (cosimplicial_object C))

variable{C}

namespace Augmented

/-- Drop the augmentation. -/
@[simps]
def drop : augmented C ⥤ cosimplicial_object C :=
  comma.snd _ _

/-- The point of the augmentation. -/
@[simps]
def point : augmented C ⥤ C :=
  comma.fst _ _

/-- The functor from augmented objects to arrows. -/
@[simps]
def to_arrow : augmented C ⥤ arrow C :=
  { obj := fun X => { left := point.obj X, right := drop.obj X _[0], Hom := X.hom.app _ },
    map :=
      fun X Y η =>
        { left := point.map η, right := (drop.map η).app _,
          w' :=
            by 
              dsimp 
              rw [←nat_trans.comp_app]
              erw [←η.w]
              rfl } }

variable(C)

/-- Functor composition induces a functor on augmented cosimplicial objects. -/
@[simp]
def whiskering_obj (D : Type _) [category.{v} D] (F : C ⥤ D) : augmented C ⥤ augmented D :=
  { obj :=
      fun X =>
        { left := F.obj (point.obj X), right := ((whiskering _ _).obj F).obj (drop.obj X),
          Hom := (functor.const_comp _ _ _).inv ≫ whisker_right X.hom F },
    map :=
      fun X Y η =>
        { left := F.map η.left, right := whisker_right η.right _,
          w' :=
            by 
              ext 
              dsimp 
              erw [category.id_comp, category.id_comp, ←F.map_comp, ←F.map_comp, ←nat_trans.comp_app, ←η.w]
              rfl } }

/-- Functor composition induces a functor on augmented cosimplicial objects. -/
@[simps]
def whiskering (D : Type _) [category.{v} D] : (C ⥤ D) ⥤ augmented C ⥤ augmented D :=
  { obj := whiskering_obj _ _, map := fun X Y η => { app := fun A => { left := η.app _, right := whisker_left _ η } } }

variable{C}

end Augmented

open_locale Simplicial

/-- Augment a cosimplicial object with an object. -/
@[simps]
def augment (X : cosimplicial_object C) (X₀ : C) (f : X₀ ⟶ X.obj [0])
  (w : ∀ i : SimplexCategory g₁ g₂ : [0] ⟶ i, f ≫ X.map g₁ = f ≫ X.map g₂) : cosimplicial_object.augmented C :=
  { left := X₀, right := X,
    Hom :=
      { app := fun i => f ≫ X.map (SimplexCategory.const i 0),
        naturality' :=
          by 
            intro i j g 
            dsimp 
            simpa [←X.map_comp] using w _ _ _ } }

@[simp]
theorem augment_hom_zero (X : cosimplicial_object C) (X₀ : C) (f : X₀ ⟶ X.obj [0]) w :
  (X.augment X₀ f w).Hom.app [0] = f :=
  by 
    dsimp 
    rw [SimplexCategory.hom_zero_zero ([0].const 0), X.map_id, category.comp_id]

end CosimplicialObject

/-- The anti-equivalence between simplicial objects and cosimplicial objects. -/
@[simps]
def simplicial_cosimplicial_equiv : «expr ᵒᵖ» (simplicial_object C) ≌ cosimplicial_object («expr ᵒᵖ» C) :=
  functor.left_op_right_op_equiv _ _

variable{C}

/-- Construct an augmented cosimplicial object in the opposite
category from an augmented simplicial object. -/
@[simps]
def simplicial_object.augmented.right_op (X : simplicial_object.augmented C) :
  cosimplicial_object.augmented («expr ᵒᵖ» C) :=
  { left := Opposite.op X.right, right := X.left.right_op, Hom := X.hom.right_op }

/-- Construct an augmented simplicial object from an augmented cosimplicial
object in the opposite category. -/
@[simps]
def cosimplicial_object.augmented.left_op (X : cosimplicial_object.augmented («expr ᵒᵖ» C)) :
  simplicial_object.augmented C :=
  { left := X.right.left_op, right := X.left.unop, Hom := X.hom.left_op }

/-- Converting an augmented simplicial object to an augmented cosimplicial
object and back is isomorphic to the given object. -/
@[simps]
def simplicial_object.augmented.right_op_left_op_iso (X : simplicial_object.augmented C) : X.right_op.left_op ≅ X :=
  comma.iso_mk X.left.right_op_left_op_iso
    (eq_to_iso$
      by 
        simp )
    (by 
      tidy)

/-- Converting an augmented cosimplicial object to an augmented simplicial
object and back is isomorphic to the given object. -/
@[simps]
def cosimplicial_object.augmented.left_op_right_op_iso (X : cosimplicial_object.augmented («expr ᵒᵖ» C)) :
  X.left_op.right_op ≅ X :=
  comma.iso_mk
    (eq_to_iso$
      by 
        simp )
    X.right.left_op_right_op_iso
    (by 
      tidy)

variable(C)

/-- A functorial version of `simplicial_object.augmented.right_op`. -/
@[simps]
def simplicial_to_cosimplicial_augmented :
  «expr ᵒᵖ» (simplicial_object.augmented C) ⥤ cosimplicial_object.augmented («expr ᵒᵖ» C) :=
  { obj := fun X => X.unop.right_op,
    map :=
      fun X Y f =>
        { left := f.unop.right.op, right := f.unop.left.right_op,
          w' :=
            by 
              ext x 
              dsimp 
              simpRw [←op_comp]
              congr 1 
              exact (congr_app f.unop.w (op x)).symm } }

/-- A functorial version of `cosimplicial_object.augmented.left_op`. -/
@[simps]
def cosimplicial_to_simplicial_augmented :
  cosimplicial_object.augmented («expr ᵒᵖ» C) ⥤ «expr ᵒᵖ» (simplicial_object.augmented C) :=
  { obj := fun X => Opposite.op X.left_op,
    map :=
      fun X Y f =>
        Quiver.Hom.op$
          { left := f.right.left_op, right := f.left.unop,
            w' :=
              by 
                ext x 
                dsimp 
                simpRw [←unop_comp]
                congr 1 
                exact (congr_app f.w x.unop).symm } }

/-- The contravariant categorical equivalence between augmented simplicial
objects and augmented cosimplicial objects in the opposite category. -/
@[simps]
def simplicial_cosimplicial_augmented_equiv :
  «expr ᵒᵖ» (simplicial_object.augmented C) ≌ cosimplicial_object.augmented («expr ᵒᵖ» C) :=
  { Functor := simplicial_to_cosimplicial_augmented _, inverse := cosimplicial_to_simplicial_augmented _,
    unitIso :=
      nat_iso.of_components (fun X => X.unop.right_op_left_op_iso.op)
        (by 
          intro X Y f 
          dsimp 
          rw
            [show f = f.unop.op by 
              simp ]
          simpRw [←op_comp]
          congr 1
          tidy),
    counitIso :=
      nat_iso.of_components (fun X => X.left_op_right_op_iso)
        (by 
          tidy) }

end CategoryTheory

