import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Preadditive.Default

/-!
# Biproducts and binary biproducts

We introduce the notion of (finite) biproducts and binary biproducts.

These are slightly unusual relative to the other shapes in the library,
as they are simultaneously limits and colimits.
(Zero objects are similar; they are "biterminal".)

We treat first the case of a general category with zero morphisms,
and subsequently the case of a preadditive category.

In a category with zero morphisms, we model the (binary) biproduct of `P Q : C`
using a `binary_bicone`, which has a cone point `X`,
and morphisms `fst : X ⟶ P`, `snd : X ⟶ Q`, `inl : P ⟶ X` and `inr : X ⟶ Q`,
such that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`.
Such a `binary_bicone` is a biproduct if the cone is a limit cone, and the cocone is a colimit
cocone.

In a preadditive category,
* any `binary_biproduct` satisfies `total : fst ≫ inl + snd ≫ inr = 𝟙 X`
* any `binary_product` is a `binary_biproduct`
* any `binary_coproduct` is a `binary_biproduct`

For biproducts indexed by a `fintype J`, a `bicone` again consists of a cone point `X`
and morphisms `π j : X ⟶ F j` and `ι j : F j ⟶ X` for each `j`,
such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.

In a preadditive category,
* any `biproduct` satisfies `total : ∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`
* any `product` is a `biproduct`
* any `coproduct` is a `biproduct`

## Notation
As `⊕` is already taken for the sum of types, we introduce the notation `X ⊞ Y` for
a binary biproduct. We introduce `⨁ f` for the indexed biproduct.
-/


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Functor

namespace CategoryTheory.Limits

variable {J : Type v} [DecidableEq J]

variable {C : Type u} [category.{v} C] [has_zero_morphisms C]

/-- 
A `c : bicone F` is:
* an object `c.X` and
* morphisms `π j : X ⟶ F j` and `ι j : F j ⟶ X` for each `j`,
* such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.
-/
@[nolint has_inhabited_instance]
structure bicone (F : J → C) where
  x : C
  π : ∀ j, X ⟶ F j
  ι : ∀ j, F j ⟶ X
  ι_π : ∀ j j', ι j ≫ π j' = if h : j = j' then eq_to_hom (congr_argₓ F h) else 0

@[simp]
theorem bicone_ι_π_self {F : J → C} (B : bicone F) (j : J) : B.ι j ≫ B.π j = 𝟙 (F j) := by
  simpa using B.ι_π j j

@[simp]
theorem bicone_ι_π_ne {F : J → C} (B : bicone F) {j j' : J} (h : j ≠ j') : B.ι j ≫ B.π j' = 0 := by
  simpa [h] using B.ι_π j j'

variable {F : J → C}

namespace Bicone

/--  Extract the cone from a bicone. -/
@[simps]
def to_cone (B : bicone F) : cone (discrete.functor F) :=
  { x := B.X, π := { app := fun j => B.π j } }

/--  Extract the cocone from a bicone. -/
@[simps]
def to_cocone (B : bicone F) : cocone (discrete.functor F) :=
  { x := B.X, ι := { app := fun j => B.ι j } }

end Bicone

/-- 
A bicone over `F : J → C`, which is both a limit cone and a colimit cocone.
-/
@[nolint has_inhabited_instance]
structure limit_bicone (F : J → C) where
  Bicone : bicone F
  IsLimit : is_limit bicone.to_cone
  IsColimit : is_colimit bicone.to_cocone

/-- 
`has_biproduct F` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `F`.
-/
class has_biproduct (F : J → C) : Prop where mk' ::
  exists_biproduct : Nonempty (limit_bicone F)

theorem has_biproduct.mk {F : J → C} (d : limit_bicone F) : has_biproduct F :=
  ⟨Nonempty.intro d⟩

/--  Use the axiom of choice to extract explicit `biproduct_data F` from `has_biproduct F`. -/
def get_biproduct_data (F : J → C) [has_biproduct F] : limit_bicone F :=
  Classical.choice has_biproduct.exists_biproduct

/--  A bicone for `F` which is both a limit cone and a colimit cocone. -/
def biproduct.bicone (F : J → C) [has_biproduct F] : bicone F :=
  (get_biproduct_data F).Bicone

/--  `biproduct.bicone F` is a limit cone. -/
def biproduct.is_limit (F : J → C) [has_biproduct F] : is_limit (biproduct.bicone F).toCone :=
  (get_biproduct_data F).IsLimit

/--  `biproduct.bicone F` is a colimit cocone. -/
def biproduct.is_colimit (F : J → C) [has_biproduct F] : is_colimit (biproduct.bicone F).toCocone :=
  (get_biproduct_data F).IsColimit

instance (priority := 100) has_product_of_has_biproduct [has_biproduct F] : has_limit (discrete.functor F) :=
  has_limit.mk { Cone := (biproduct.bicone F).toCone, IsLimit := biproduct.is_limit F }

instance (priority := 100) has_coproduct_of_has_biproduct [has_biproduct F] : has_colimit (discrete.functor F) :=
  has_colimit.mk { Cocone := (biproduct.bicone F).toCocone, IsColimit := biproduct.is_colimit F }

variable (J C)

/-- 
`C` has biproducts of shape `J` if we have
a limit and a colimit, with the same cone points,
of every function `F : J → C`.
-/
class has_biproducts_of_shape : Prop where
  HasBiproduct : ∀ F : J → C, has_biproduct F

attribute [instance] has_biproducts_of_shape.has_biproduct

/--  `has_finite_biproducts C` represents a choice of biproduct for every family of objects in `C`
indexed by a finite type with decidable equality. -/
class has_finite_biproducts : Prop where
  HasBiproductsOfShape : ∀ J : Type v [DecidableEq J] [Fintype J], has_biproducts_of_shape J C

attribute [instance] has_finite_biproducts.has_biproducts_of_shape

-- failed to format: format: uncaught backtrack exception
instance
  ( priority := 100 )
  has_finite_products_of_has_finite_biproducts
  [ has_finite_biproducts C ] : has_finite_products C
  where out J _ _ := ⟨ fun F => by exact has_limit_of_iso discrete.nat_iso_functor.symm ⟩

-- failed to format: format: uncaught backtrack exception
instance
  ( priority := 100 )
  has_finite_coproducts_of_has_finite_biproducts
  [ has_finite_biproducts C ] : has_finite_coproducts C
  where out J _ _ := ⟨ fun F => by exact has_colimit_of_iso discrete.nat_iso_functor ⟩

variable {J C}

/-- 
The isomorphism between the specified limit and the specified colimit for
a functor with a bilimit.
-/
def biproduct_iso (F : J → C) [has_biproduct F] : limits.pi_obj F ≅ limits.sigma_obj F :=
  (is_limit.cone_point_unique_up_to_iso (limit.is_limit _) (biproduct.is_limit F)).trans $
    is_colimit.cocone_point_unique_up_to_iso (biproduct.is_colimit F) (colimit.is_colimit _)

end CategoryTheory.Limits

namespace CategoryTheory.Limits

variable {J : Type v} [DecidableEq J]

variable {C : Type u} [category.{v} C] [has_zero_morphisms C]

/--  `biproduct f` computes the biproduct of a family of elements `f`. (It is defined as an
   abbreviation for `limit (discrete.functor f)`, so for most facts about `biproduct f`, you will
   just use general facts about limits and colimits.) -/
abbrev biproduct (f : J → C) [has_biproduct f] : C :=
  (biproduct.bicone f).x

notation "⨁ " f:20 => biproduct f

/--  The projection onto a summand of a biproduct. -/
abbrev biproduct.π (f : J → C) [has_biproduct f] (b : J) : ⨁ f ⟶ f b :=
  (biproduct.bicone f).π b

@[simp]
theorem biproduct.bicone_π (f : J → C) [has_biproduct f] (b : J) : (biproduct.bicone f).π b = biproduct.π f b :=
  rfl

/--  The inclusion into a summand of a biproduct. -/
abbrev biproduct.ι (f : J → C) [has_biproduct f] (b : J) : f b ⟶ ⨁ f :=
  (biproduct.bicone f).ι b

@[simp]
theorem biproduct.bicone_ι (f : J → C) [has_biproduct f] (b : J) : (biproduct.bicone f).ι b = biproduct.ι f b :=
  rfl

@[reassoc]
theorem biproduct.ι_π (f : J → C) [has_biproduct f] (j j' : J) :
    biproduct.ι f j ≫ biproduct.π f j' = if h : j = j' then eq_to_hom (congr_argₓ f h) else 0 :=
  (biproduct.bicone f).ι_π j j'

@[simp, reassoc]
theorem biproduct.ι_π_self (f : J → C) [has_biproduct f] (j : J) : biproduct.ι f j ≫ biproduct.π f j = 𝟙 _ := by
  simp [biproduct.ι_π]

@[simp, reassoc]
theorem biproduct.ι_π_ne (f : J → C) [has_biproduct f] {j j' : J} (h : j ≠ j') :
    biproduct.ι f j ≫ biproduct.π f j' = 0 := by
  simp [biproduct.ι_π, h]

/--  Given a collection of maps into the summands, we obtain a map into the biproduct. -/
abbrev biproduct.lift {f : J → C} [has_biproduct f] {P : C} (p : ∀ b, P ⟶ f b) : P ⟶ ⨁ f :=
  (biproduct.is_limit f).lift (fan.mk P p)

/--  Given a collection of maps out of the summands, we obtain a map out of the biproduct. -/
abbrev biproduct.desc {f : J → C} [has_biproduct f] {P : C} (p : ∀ b, f b ⟶ P) : ⨁ f ⟶ P :=
  (biproduct.is_colimit f).desc (cofan.mk P p)

@[simp, reassoc]
theorem biproduct.lift_π {f : J → C} [has_biproduct f] {P : C} (p : ∀ b, P ⟶ f b) (j : J) :
    biproduct.lift p ≫ biproduct.π f j = p j :=
  (biproduct.is_limit f).fac _ _

@[simp, reassoc]
theorem biproduct.ι_desc {f : J → C} [has_biproduct f] {P : C} (p : ∀ b, f b ⟶ P) (j : J) :
    biproduct.ι f j ≫ biproduct.desc p = p j :=
  (biproduct.is_colimit f).fac _ _

/--  Given a collection of maps between corresponding summands of a pair of biproducts
indexed by the same type, we obtain a map between the biproducts. -/
abbrev biproduct.map [Fintype J] {f g : J → C} [has_finite_biproducts C] (p : ∀ b, f b ⟶ g b) : ⨁ f ⟶ ⨁ g :=
  is_limit.map (biproduct.bicone f).toCone (biproduct.is_limit g) (discrete.nat_trans p)

/--  An alternative to `biproduct.map` constructed via colimits.
This construction only exists in order to show it is equal to `biproduct.map`. -/
abbrev biproduct.map' [Fintype J] {f g : J → C} [has_finite_biproducts C] (p : ∀ b, f b ⟶ g b) : ⨁ f ⟶ ⨁ g :=
  is_colimit.map (biproduct.is_colimit f) (biproduct.bicone g).toCocone (discrete.nat_trans p)

@[ext]
theorem biproduct.hom_ext {f : J → C} [has_biproduct f] {Z : C} (g h : Z ⟶ ⨁ f)
    (w : ∀ j, g ≫ biproduct.π f j = h ≫ biproduct.π f j) : g = h :=
  (biproduct.is_limit f).hom_ext w

@[ext]
theorem biproduct.hom_ext' {f : J → C} [has_biproduct f] {Z : C} (g h : ⨁ f ⟶ Z)
    (w : ∀ j, biproduct.ι f j ≫ g = biproduct.ι f j ≫ h) : g = h :=
  (biproduct.is_colimit f).hom_ext w

theorem biproduct.map_eq_map' [Fintype J] {f g : J → C} [has_finite_biproducts C] (p : ∀ b, f b ⟶ g b) :
    biproduct.map p = biproduct.map' p := by
  ext j j'
  simp only [discrete.nat_trans_app, limits.is_colimit.ι_map, limits.is_limit.map_π, category.assoc, ←
    bicone.to_cone_π_app, ← biproduct.bicone_π, ← bicone.to_cocone_ι_app, ← biproduct.bicone_ι]
  simp only [biproduct.bicone_ι, biproduct.bicone_π, bicone.to_cocone_ι_app, bicone.to_cone_π_app]
  rw [biproduct.ι_π_assoc, biproduct.ι_π]
  split_ifs
  ·
    subst h
    rw [eq_to_hom_refl, category.id_comp]
    erw [category.comp_id]
  ·
    simp

@[simp, reassoc]
theorem biproduct.map_π [Fintype J] {f g : J → C} [has_finite_biproducts C] (p : ∀ j, f j ⟶ g j) (j : J) :
    biproduct.map p ≫ biproduct.π g j = biproduct.π f j ≫ p j :=
  limits.is_limit.map_π _ _ _ _

@[simp, reassoc]
theorem biproduct.ι_map [Fintype J] {f g : J → C} [has_finite_biproducts C] (p : ∀ j, f j ⟶ g j) (j : J) :
    biproduct.ι f j ≫ biproduct.map p = p j ≫ biproduct.ι g j := by
  rw [biproduct.map_eq_map']
  convert limits.is_colimit.ι_map _ _ _ _ <;> rfl

@[simp, reassoc]
theorem biproduct.map_desc [Fintype J] {f g : J → C} [has_finite_biproducts C] (p : ∀ j, f j ⟶ g j) {P : C}
    (k : ∀ j, g j ⟶ P) : biproduct.map p ≫ biproduct.desc k = biproduct.desc fun j => p j ≫ k j := by
  ext
  simp

@[simp, reassoc]
theorem biproduct.lift_map [Fintype J] {f g : J → C} [has_finite_biproducts C] {P : C} (k : ∀ j, P ⟶ f j)
    (p : ∀ j, f j ⟶ g j) : biproduct.lift k ≫ biproduct.map p = biproduct.lift fun j => k j ≫ p j := by
  ext
  simp

/--  Given a collection of isomorphisms between corresponding summands of a pair of biproducts
indexed by the same type, we obtain an isomorphism between the biproducts. -/
@[simps]
def biproduct.map_iso [Fintype J] {f g : J → C} [has_finite_biproducts C] (p : ∀ b, f b ≅ g b) : ⨁ f ≅ ⨁ g :=
  { Hom := biproduct.map fun b => (p b).Hom, inv := biproduct.map fun b => (p b).inv }

section

variable [Fintype J] {K : Type v} [Fintype K] [DecidableEq K] {f : J → C} {g : K → C} [has_finite_biproducts C]

/-- 
Convert a (dependently typed) matrix to a morphism of biproducts.
-/
def biproduct.matrix (m : ∀ j k, f j ⟶ g k) : ⨁ f ⟶ ⨁ g :=
  biproduct.desc fun j => biproduct.lift fun k => m j k

@[simp, reassoc]
theorem biproduct.matrix_π (m : ∀ j k, f j ⟶ g k) (k : K) :
    biproduct.matrix m ≫ biproduct.π g k = biproduct.desc fun j => m j k := by
  ext
  simp [biproduct.matrix]

@[simp, reassoc]
theorem biproduct.ι_matrix (m : ∀ j k, f j ⟶ g k) (j : J) :
    biproduct.ι f j ≫ biproduct.matrix m = biproduct.lift fun k => m j k := by
  ext
  simp [biproduct.matrix]

/-- 
Extract the matrix components from a morphism of biproducts.
-/
def biproduct.components (m : ⨁ f ⟶ ⨁ g) (j : J) (k : K) : f j ⟶ g k :=
  biproduct.ι f j ≫ m ≫ biproduct.π g k

@[simp]
theorem biproduct.matrix_components (m : ∀ j k, f j ⟶ g k) (j : J) (k : K) :
    biproduct.components (biproduct.matrix m) j k = m j k := by
  simp [biproduct.components]

@[simp]
theorem biproduct.components_matrix (m : ⨁ f ⟶ ⨁ g) : (biproduct.matrix fun j k => biproduct.components m j k) = m := by
  ext
  simp [biproduct.components]

/--  Morphisms between direct sums are matrices. -/
@[simps]
def biproduct.matrix_equiv : (⨁ f ⟶ ⨁ g) ≃ ∀ j k, f j ⟶ g k :=
  { toFun := biproduct.components, invFun := biproduct.matrix, left_inv := biproduct.components_matrix,
    right_inv := fun m => by
      ext
      apply biproduct.matrix_components }

end

instance biproduct.ι_mono (f : J → C) [has_biproduct f] (b : J) : split_mono (biproduct.ι f b) where
  retraction :=
    biproduct.desc $ fun b' => if h : b' = b then eq_to_hom (congr_argₓ f h) else biproduct.ι f b' ≫ biproduct.π f b

instance biproduct.π_epi (f : J → C) [has_biproduct f] (b : J) : split_epi (biproduct.π f b) where
  section_ :=
    biproduct.lift $ fun b' => if h : b = b' then eq_to_hom (congr_argₓ f h) else biproduct.ι f b ≫ biproduct.π f b'

variable {C}

/-- 
A binary bicone for a pair of objects `P Q : C` consists of the cone point `X`,
maps from `X` to both `P` and `Q`, and maps from both `P` and `Q` to `X`,
so that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`
-/
@[nolint has_inhabited_instance]
structure binary_bicone (P Q : C) where
  x : C
  fst : X ⟶ P
  snd : X ⟶ Q
  inl : P ⟶ X
  inr : Q ⟶ X
  inl_fst' : inl ≫ fst = 𝟙 P := by
    run_tac
      obviously
  inl_snd' : inl ≫ snd = 0 := by
    run_tac
      obviously
  inr_fst' : inr ≫ fst = 0 := by
    run_tac
      obviously
  inr_snd' : inr ≫ snd = 𝟙 Q := by
    run_tac
      obviously

restate_axiom binary_bicone.inl_fst'

restate_axiom binary_bicone.inl_snd'

restate_axiom binary_bicone.inr_fst'

restate_axiom binary_bicone.inr_snd'

attribute [simp, reassoc] binary_bicone.inl_fst binary_bicone.inl_snd binary_bicone.inr_fst binary_bicone.inr_snd

namespace BinaryBicone

variable {P Q : C}

/--  Extract the cone from a binary bicone. -/
def to_cone (c : binary_bicone P Q) : cone (pair P Q) :=
  binary_fan.mk c.fst c.snd

@[simp]
theorem to_cone_X (c : binary_bicone P Q) : c.to_cone.X = c.X :=
  rfl

@[simp]
theorem to_cone_π_app_left (c : binary_bicone P Q) : c.to_cone.π.app walking_pair.left = c.fst :=
  rfl

@[simp]
theorem to_cone_π_app_right (c : binary_bicone P Q) : c.to_cone.π.app walking_pair.right = c.snd :=
  rfl

/--  Extract the cocone from a binary bicone. -/
def to_cocone (c : binary_bicone P Q) : cocone (pair P Q) :=
  binary_cofan.mk c.inl c.inr

@[simp]
theorem to_cocone_X (c : binary_bicone P Q) : c.to_cocone.X = c.X :=
  rfl

@[simp]
theorem to_cocone_ι_app_left (c : binary_bicone P Q) : c.to_cocone.ι.app walking_pair.left = c.inl :=
  rfl

@[simp]
theorem to_cocone_ι_app_right (c : binary_bicone P Q) : c.to_cocone.ι.app walking_pair.right = c.inr :=
  rfl

end BinaryBicone

namespace Bicone

/--  Convert a `bicone` over a function on `walking_pair` to a binary_bicone. -/
@[simps]
def to_binary_bicone {X Y : C} (b : bicone (pair X Y).obj) : binary_bicone X Y :=
  { x := b.X, fst := b.π walking_pair.left, snd := b.π walking_pair.right, inl := b.ι walking_pair.left,
    inr := b.ι walking_pair.right,
    inl_fst' := by
      simp [bicone.ι_π]
      rfl,
    inr_fst' := by
      simp [bicone.ι_π],
    inl_snd' := by
      simp [bicone.ι_π],
    inr_snd' := by
      simp [bicone.ι_π]
      rfl }

/-- 
If the cone obtained from a bicone over `pair X Y` is a limit cone,
so is the cone obtained by converting that bicone to a binary_bicone, then to a cone.
-/
def to_binary_bicone_is_limit {X Y : C} {b : bicone (pair X Y).obj} (c : is_limit b.to_cone) :
    is_limit b.to_binary_bicone.to_cone :=
  { lift := fun s => c.lift s,
    fac' := fun s j => by
      cases j <;> erw [c.fac],
    uniq' := fun s m w => by
      apply c.uniq s
      rintro (⟨⟩ | ⟨⟩)
      exact w walking_pair.left
      exact w walking_pair.right }

/-- 
If the cocone obtained from a bicone over `pair X Y` is a colimit cocone,
so is the cocone obtained by converting that bicone to a binary_bicone, then to a cocone.
-/
def to_binary_bicone_is_colimit {X Y : C} {b : bicone (pair X Y).obj} (c : is_colimit b.to_cocone) :
    is_colimit b.to_binary_bicone.to_cocone :=
  { desc := fun s => c.desc s,
    fac' := fun s j => by
      cases j <;> erw [c.fac],
    uniq' := fun s m w => by
      apply c.uniq s
      rintro (⟨⟩ | ⟨⟩)
      exact w walking_pair.left
      exact w walking_pair.right }

end Bicone

/-- 
A bicone over `P Q : C`, which is both a limit cone and a colimit cocone.
-/
@[nolint has_inhabited_instance]
structure binary_biproduct_data (P Q : C) where
  Bicone : binary_bicone P Q
  IsLimit : is_limit bicone.to_cone
  IsColimit : is_colimit bicone.to_cocone

/-- 
`has_binary_biproduct P Q` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`.
-/
class has_binary_biproduct (P Q : C) : Prop where mk' ::
  exists_binary_biproduct : Nonempty (binary_biproduct_data P Q)

theorem has_binary_biproduct.mk {P Q : C} (d : binary_biproduct_data P Q) : has_binary_biproduct P Q :=
  ⟨Nonempty.intro d⟩

/-- 
Use the axiom of choice to extract explicit `binary_biproduct_data F` from `has_binary_biproduct F`.
-/
def get_binary_biproduct_data (P Q : C) [has_binary_biproduct P Q] : binary_biproduct_data P Q :=
  Classical.choice has_binary_biproduct.exists_binary_biproduct

/--  A bicone for `P Q ` which is both a limit cone and a colimit cocone. -/
def binary_biproduct.bicone (P Q : C) [has_binary_biproduct P Q] : binary_bicone P Q :=
  (get_binary_biproduct_data P Q).Bicone

/--  `binary_biproduct.bicone P Q` is a limit cone. -/
def binary_biproduct.is_limit (P Q : C) [has_binary_biproduct P Q] : is_limit (binary_biproduct.bicone P Q).toCone :=
  (get_binary_biproduct_data P Q).IsLimit

/--  `binary_biproduct.bicone P Q` is a colimit cocone. -/
def binary_biproduct.is_colimit (P Q : C) [has_binary_biproduct P Q] :
    is_colimit (binary_biproduct.bicone P Q).toCocone :=
  (get_binary_biproduct_data P Q).IsColimit

section

variable (C)

/-- 
`has_binary_biproducts C` represents the existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`, for every `P Q : C`.
-/
class has_binary_biproducts : Prop where
  HasBinaryBiproduct : ∀ P Q : C, has_binary_biproduct P Q

attribute [instance] has_binary_biproducts.has_binary_biproduct

/-- 
A category with finite biproducts has binary biproducts.

This is not an instance as typically in concrete categories there will be
an alternative construction with nicer definitional properties.
-/
theorem has_binary_biproducts_of_finite_biproducts [has_finite_biproducts C] : has_binary_biproducts C :=
  { HasBinaryBiproduct := fun P Q =>
      has_binary_biproduct.mk
        { Bicone := (biproduct.bicone (pair P Q).obj).toBinaryBicone,
          IsLimit := bicone.to_binary_bicone_is_limit (biproduct.is_limit _),
          IsColimit := bicone.to_binary_bicone_is_colimit (biproduct.is_colimit _) } }

end

variable {P Q : C}

instance has_binary_biproduct.has_limit_pair [has_binary_biproduct P Q] : has_limit (pair P Q) :=
  has_limit.mk ⟨_, binary_biproduct.is_limit P Q⟩

instance has_binary_biproduct.has_colimit_pair [has_binary_biproduct P Q] : has_colimit (pair P Q) :=
  has_colimit.mk ⟨_, binary_biproduct.is_colimit P Q⟩

-- failed to format: format: uncaught backtrack exception
instance
  ( priority := 100 )
  has_binary_products_of_has_binary_biproducts
  [ has_binary_biproducts C ] : has_binary_products C
  where HasLimit F := has_limit_of_iso ( diagram_iso_pair F ) . symm

-- failed to format: format: uncaught backtrack exception
instance
  ( priority := 100 )
  has_binary_coproducts_of_has_binary_biproducts
  [ has_binary_biproducts C ] : has_binary_coproducts C
  where HasColimit F := has_colimit_of_iso ( diagram_iso_pair F )

/-- 
The isomorphism between the specified binary product and the specified binary coproduct for
a pair for a binary biproduct.
-/
def biprod_iso (X Y : C) [has_binary_biproduct X Y] : limits.prod X Y ≅ limits.coprod X Y :=
  (is_limit.cone_point_unique_up_to_iso (limit.is_limit _) (binary_biproduct.is_limit X Y)).trans $
    is_colimit.cocone_point_unique_up_to_iso (binary_biproduct.is_colimit X Y) (colimit.is_colimit _)

/--  An arbitrary choice of biproduct of a pair of objects. -/
abbrev biprod (X Y : C) [has_binary_biproduct X Y] :=
  (binary_biproduct.bicone X Y).x

notation:20 X " ⊞ " Y:20 => biprod X Y

/--  The projection onto the first summand of a binary biproduct. -/
abbrev biprod.fst {X Y : C} [has_binary_biproduct X Y] : X ⊞ Y ⟶ X :=
  (binary_biproduct.bicone X Y).fst

/--  The projection onto the second summand of a binary biproduct. -/
abbrev biprod.snd {X Y : C} [has_binary_biproduct X Y] : X ⊞ Y ⟶ Y :=
  (binary_biproduct.bicone X Y).snd

/--  The inclusion into the first summand of a binary biproduct. -/
abbrev biprod.inl {X Y : C} [has_binary_biproduct X Y] : X ⟶ X ⊞ Y :=
  (binary_biproduct.bicone X Y).inl

/--  The inclusion into the second summand of a binary biproduct. -/
abbrev biprod.inr {X Y : C} [has_binary_biproduct X Y] : Y ⟶ X ⊞ Y :=
  (binary_biproduct.bicone X Y).inr

section

variable {X Y : C} [has_binary_biproduct X Y]

@[simp]
theorem binary_biproduct.bicone_fst : (binary_biproduct.bicone X Y).fst = biprod.fst :=
  rfl

@[simp]
theorem binary_biproduct.bicone_snd : (binary_biproduct.bicone X Y).snd = biprod.snd :=
  rfl

@[simp]
theorem binary_biproduct.bicone_inl : (binary_biproduct.bicone X Y).inl = biprod.inl :=
  rfl

@[simp]
theorem binary_biproduct.bicone_inr : (binary_biproduct.bicone X Y).inr = biprod.inr :=
  rfl

end

@[simp, reassoc]
theorem biprod.inl_fst {X Y : C} [has_binary_biproduct X Y] :
    (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 𝟙 X :=
  (binary_biproduct.bicone X Y).inl_fst

@[simp, reassoc]
theorem biprod.inl_snd {X Y : C} [has_binary_biproduct X Y] : (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 0 :=
  (binary_biproduct.bicone X Y).inl_snd

@[simp, reassoc]
theorem biprod.inr_fst {X Y : C} [has_binary_biproduct X Y] : (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 0 :=
  (binary_biproduct.bicone X Y).inr_fst

@[simp, reassoc]
theorem biprod.inr_snd {X Y : C} [has_binary_biproduct X Y] :
    (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 𝟙 Y :=
  (binary_biproduct.bicone X Y).inr_snd

/--  Given a pair of maps into the summands of a binary biproduct,
we obtain a map into the binary biproduct. -/
abbrev biprod.lift {W X Y : C} [has_binary_biproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ⊞ Y :=
  (binary_biproduct.is_limit X Y).lift (binary_fan.mk f g)

/--  Given a pair of maps out of the summands of a binary biproduct,
we obtain a map out of the binary biproduct. -/
abbrev biprod.desc {W X Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) : X ⊞ Y ⟶ W :=
  (binary_biproduct.is_colimit X Y).desc (binary_cofan.mk f g)

@[simp, reassoc]
theorem biprod.lift_fst {W X Y : C} [has_binary_biproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift f g ≫ biprod.fst = f :=
  (binary_biproduct.is_limit X Y).fac _ walking_pair.left

@[simp, reassoc]
theorem biprod.lift_snd {W X Y : C} [has_binary_biproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift f g ≫ biprod.snd = g :=
  (binary_biproduct.is_limit X Y).fac _ walking_pair.right

@[simp, reassoc]
theorem biprod.inl_desc {W X Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    biprod.inl ≫ biprod.desc f g = f :=
  (binary_biproduct.is_colimit X Y).fac _ walking_pair.left

@[simp, reassoc]
theorem biprod.inr_desc {W X Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    biprod.inr ≫ biprod.desc f g = g :=
  (binary_biproduct.is_colimit X Y).fac _ walking_pair.right

instance biprod.mono_lift_of_mono_left {W X Y : C} [has_binary_biproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) [mono f] :
    mono (biprod.lift f g) :=
  mono_of_mono_fac $ biprod.lift_fst _ _

instance biprod.mono_lift_of_mono_right {W X Y : C} [has_binary_biproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) [mono g] :
    mono (biprod.lift f g) :=
  mono_of_mono_fac $ biprod.lift_snd _ _

instance biprod.epi_desc_of_epi_left {W X Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) [epi f] :
    epi (biprod.desc f g) :=
  epi_of_epi_fac $ biprod.inl_desc _ _

instance biprod.epi_desc_of_epi_right {W X Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) [epi g] :
    epi (biprod.desc f g) :=
  epi_of_epi_fac $ biprod.inr_desc _ _

/--  Given a pair of maps between the summands of a pair of binary biproducts,
we obtain a map between the binary biproducts. -/
abbrev biprod.map {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    W ⊞ X ⟶ Y ⊞ Z :=
  is_limit.map (binary_biproduct.bicone W X).toCone (binary_biproduct.is_limit Y Z)
    (@map_pair _ _ (pair W X) (pair Y Z) f g)

/--  An alternative to `biprod.map` constructed via colimits.
This construction only exists in order to show it is equal to `biprod.map`. -/
abbrev biprod.map' {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    W ⊞ X ⟶ Y ⊞ Z :=
  is_colimit.map (binary_biproduct.is_colimit W X) (binary_biproduct.bicone Y Z).toCocone
    (@map_pair _ _ (pair W X) (pair Y Z) f g)

@[ext]
theorem biprod.hom_ext {X Y Z : C} [has_binary_biproduct X Y] (f g : Z ⟶ X ⊞ Y) (h₀ : f ≫ biprod.fst = g ≫ biprod.fst)
    (h₁ : f ≫ biprod.snd = g ≫ biprod.snd) : f = g :=
  binary_fan.is_limit.hom_ext (binary_biproduct.is_limit X Y) h₀ h₁

@[ext]
theorem biprod.hom_ext' {X Y Z : C} [has_binary_biproduct X Y] (f g : X ⊞ Y ⟶ Z) (h₀ : biprod.inl ≫ f = biprod.inl ≫ g)
    (h₁ : biprod.inr ≫ f = biprod.inr ≫ g) : f = g :=
  binary_cofan.is_colimit.hom_ext (binary_biproduct.is_colimit X Y) h₀ h₁

theorem biprod.map_eq_map' {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    biprod.map f g = biprod.map' f g := by
  ext
  ·
    simp only [map_pair_left, is_colimit.ι_map, is_limit.map_π, biprod.inl_fst_assoc, category.assoc, ←
      binary_bicone.to_cone_π_app_left, ← binary_biproduct.bicone_fst, ← binary_bicone.to_cocone_ι_app_left, ←
      binary_biproduct.bicone_inl]
    simp
  ·
    simp only [map_pair_left, is_colimit.ι_map, is_limit.map_π, zero_comp, biprod.inl_snd_assoc, category.assoc, ←
      binary_bicone.to_cone_π_app_right, ← binary_biproduct.bicone_snd, ← binary_bicone.to_cocone_ι_app_left, ←
      binary_biproduct.bicone_inl]
    simp
  ·
    simp only [map_pair_right, biprod.inr_fst_assoc, is_colimit.ι_map, is_limit.map_π, zero_comp, category.assoc, ←
      binary_bicone.to_cone_π_app_left, ← binary_biproduct.bicone_fst, ← binary_bicone.to_cocone_ι_app_right, ←
      binary_biproduct.bicone_inr]
    simp
  ·
    simp only [map_pair_right, is_colimit.ι_map, is_limit.map_π, biprod.inr_snd_assoc, category.assoc, ←
      binary_bicone.to_cone_π_app_right, ← binary_biproduct.bicone_snd, ← binary_bicone.to_cocone_ι_app_right, ←
      binary_biproduct.bicone_inr]
    simp

instance biprod.inl_mono {X Y : C} [has_binary_biproduct X Y] : split_mono (biprod.inl : X ⟶ X ⊞ Y) where
  retraction := biprod.desc (𝟙 X) (biprod.inr ≫ biprod.fst)

instance biprod.inr_mono {X Y : C} [has_binary_biproduct X Y] : split_mono (biprod.inr : Y ⟶ X ⊞ Y) where
  retraction := biprod.desc (biprod.inl ≫ biprod.snd) (𝟙 Y)

instance biprod.fst_epi {X Y : C} [has_binary_biproduct X Y] : split_epi (biprod.fst : X ⊞ Y ⟶ X) where
  section_ := biprod.lift (𝟙 X) (biprod.inl ≫ biprod.snd)

instance biprod.snd_epi {X Y : C} [has_binary_biproduct X Y] : split_epi (biprod.snd : X ⊞ Y ⟶ Y) where
  section_ := biprod.lift (biprod.inr ≫ biprod.fst) (𝟙 Y)

@[simp, reassoc]
theorem biprod.map_fst {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    biprod.map f g ≫ biprod.fst = biprod.fst ≫ f :=
  is_limit.map_π _ _ _ walking_pair.left

@[simp, reassoc]
theorem biprod.map_snd {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    biprod.map f g ≫ biprod.snd = biprod.snd ≫ g :=
  is_limit.map_π _ _ _ walking_pair.right

@[simp, reassoc]
theorem biprod.inl_map {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    biprod.inl ≫ biprod.map f g = f ≫ biprod.inl := by
  rw [biprod.map_eq_map']
  exact is_colimit.ι_map (binary_biproduct.is_colimit W X) _ _ walking_pair.left

@[simp, reassoc]
theorem biprod.inr_map {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    biprod.inr ≫ biprod.map f g = g ≫ biprod.inr := by
  rw [biprod.map_eq_map']
  exact is_colimit.ι_map (binary_biproduct.is_colimit W X) _ _ walking_pair.right

/--  Given a pair of isomorphisms between the summands of a pair of binary biproducts,
we obtain an isomorphism between the binary biproducts. -/
@[simps]
def biprod.map_iso {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z] (f : W ≅ Y) (g : X ≅ Z) :
    W ⊞ X ≅ Y ⊞ Z :=
  { Hom := biprod.map f.hom g.hom, inv := biprod.map f.inv g.inv }

section

variable [has_binary_biproducts C]

/--  The braiding isomorphism which swaps a binary biproduct. -/
@[simps]
def biprod.braiding (P Q : C) : P ⊞ Q ≅ Q ⊞ P :=
  { Hom := biprod.lift biprod.snd biprod.fst, inv := biprod.lift biprod.snd biprod.fst }

/-- 
An alternative formula for the braiding isomorphism which swaps a binary biproduct,
using the fact that the biproduct is a coproduct.
-/
@[simps]
def biprod.braiding' (P Q : C) : P ⊞ Q ≅ Q ⊞ P :=
  { Hom := biprod.desc biprod.inr biprod.inl, inv := biprod.desc biprod.inr biprod.inl }

theorem biprod.braiding'_eq_braiding {P Q : C} : biprod.braiding' P Q = biprod.braiding P Q := by
  tidy

/--  The braiding isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
theorem biprod.braid_natural {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W) :
    biprod.map f g ≫ (biprod.braiding _ _).Hom = (biprod.braiding _ _).Hom ≫ biprod.map g f := by
  tidy

@[reassoc]
theorem biprod.braiding_map_braiding {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) :
    (biprod.braiding X W).Hom ≫ biprod.map f g ≫ (biprod.braiding Y Z).Hom = biprod.map g f := by
  tidy

@[simp, reassoc]
theorem biprod.symmetry' (P Q : C) :
    biprod.lift biprod.snd biprod.fst ≫ biprod.lift biprod.snd biprod.fst = 𝟙 (P ⊞ Q) := by
  tidy

/--  The braiding isomorphism is symmetric. -/
@[reassoc]
theorem biprod.symmetry (P Q : C) : (biprod.braiding P Q).Hom ≫ (biprod.braiding Q P).Hom = 𝟙 _ := by
  simp

end

end CategoryTheory.Limits

namespace CategoryTheory.Limits

section Preadditive

variable {C : Type u} [category.{v} C] [preadditive C]

variable {J : Type v} [DecidableEq J] [Fintype J]

open CategoryTheory.Preadditive

open_locale BigOperators

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "\nIn a preadditive category, we can construct a biproduct for `f : J → C` from\nany bicone `b` for `f` satisfying `total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X`.\n\n(That is, such a bicone is a limit cone and a colimit cocone.)\n-/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `has_biproduct_of_total [])
  (Command.declSig
   [(Term.implicitBinder "{" [`f] [":" (Term.arrow `J "→" `C)] "}")
    (Term.explicitBinder "(" [`b] [":" (Term.app `bicone [`f])] [] ")")
    (Term.explicitBinder
     "("
     [`total]
     [":"
      («term_=_»
       (Algebra.BigOperators.Basic.«term∑_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `J]))
        ", "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `b.π [`j]) " ≫ " (Term.app `b.ι [`j])))
       "="
       (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`b.X]))]
     []
     ")")]
   (Term.typeSpec ":" (Term.app `has_biproduct [`f])))
  (Command.declValSimple
   ":="
   (Term.app
    `has_biproduct.mk
    [(Term.structInst
      "{"
      []
      [(group (Term.structInstField (Term.structInstLVal `Bicone []) ":=" `b) [","])
       (group
        (Term.structInstField
         (Term.structInstLVal `IsLimit [])
         ":="
         (Term.structInst
          "{"
          []
          [(group
            (Term.structInstField
             (Term.structInstLVal `lift [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`s] [])]
               "=>"
               (Algebra.BigOperators.Basic.«term∑_,_»
                "∑"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
                ", "
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 (Term.app `s.π.app [`j])
                 " ≫ "
                 (Term.app `b.ι [`j]))))))
            [","])
           (group
            (Term.structInstField
             (Term.structInstLVal `uniq' [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`s `m `h] [])]
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.tacticErw__
                     "erw"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule ["←"] (Term.app `category.comp_id [`m]))
                       ","
                       (Tactic.rwRule ["←"] `Total)
                       ","
                       (Tactic.rwRule [] `comp_sum)]
                      "]")
                     [])
                    [])
                   (group (Tactic.apply "apply" (Term.app `Finset.sum_congr [`rfl])) [])
                   (group (Tactic.intro "intro" [`j `m]) [])
                   (group
                    (Tactic.tacticErw__
                     "erw"
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `reassoc_of [(Term.app `h [`j])]))] "]")
                     [])
                    [])]))))))
            [","])
           (group
            (Term.structInstField
             (Term.structInstLVal `fac' [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`s `j] [])]
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.simp
                     "simp"
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `sum_comp)
                       ","
                       (Tactic.simpLemma [] [] `category.assoc)
                       ","
                       (Tactic.simpLemma [] [] `bicone.to_cone_π_app)
                       ","
                       (Tactic.simpLemma [] [] `b.ι_π)
                       ","
                       (Tactic.simpLemma [] [] `comp_dite)]
                      "]"]
                     [])
                    [])
                   (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
                   (group (Tactic.simp "simp" [] [] [] []) [])]))))))
            [])]
          (Term.optEllipsis [])
          []
          "}"))
        [","])
       (group
        (Term.structInstField
         (Term.structInstLVal `IsColimit [])
         ":="
         (Term.structInst
          "{"
          []
          [(group
            (Term.structInstField
             (Term.structInstLVal `desc [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`s] [])]
               "=>"
               (Algebra.BigOperators.Basic.«term∑_,_»
                "∑"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
                ", "
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 (Term.app `b.π [`j])
                 " ≫ "
                 (Term.app `s.ι.app [`j]))))))
            [","])
           (group
            (Term.structInstField
             (Term.structInstLVal `uniq' [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`s `m `h] [])]
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.tacticErw__
                     "erw"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule ["←"] (Term.app `category.id_comp [`m]))
                       ","
                       (Tactic.rwRule ["←"] `Total)
                       ","
                       (Tactic.rwRule [] `sum_comp)]
                      "]")
                     [])
                    [])
                   (group (Tactic.apply "apply" (Term.app `Finset.sum_congr [`rfl])) [])
                   (group (Tactic.intro "intro" [`j `m]) [])
                   (group
                    (Tactic.tacticErw__
                     "erw"
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc) "," (Tactic.rwRule [] `h)] "]")
                     [])
                    [])]))))))
            [","])
           (group
            (Term.structInstField
             (Term.structInstLVal `fac' [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`s `j] [])]
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.simp
                     "simp"
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `comp_sum)
                       ","
                       (Tactic.simpLemma [] ["←"] `category.assoc)
                       ","
                       (Tactic.simpLemma [] [] `bicone.to_cocone_ι_app)
                       ","
                       (Tactic.simpLemma [] [] `b.ι_π)
                       ","
                       (Tactic.simpLemma [] [] `dite_comp)]
                      "]"]
                     [])
                    [])
                   (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
                   (group (Tactic.simp "simp" [] [] [] []) [])]))))))
            [])]
          (Term.optEllipsis [])
          []
          "}"))
        [])]
      (Term.optEllipsis [])
      []
      "}")])
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `has_biproduct.mk
   [(Term.structInst
     "{"
     []
     [(group (Term.structInstField (Term.structInstLVal `Bicone []) ":=" `b) [","])
      (group
       (Term.structInstField
        (Term.structInstLVal `IsLimit [])
        ":="
        (Term.structInst
         "{"
         []
         [(group
           (Term.structInstField
            (Term.structInstLVal `lift [])
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`s] [])]
              "=>"
              (Algebra.BigOperators.Basic.«term∑_,_»
               "∑"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
               ", "
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app `s.π.app [`j])
                " ≫ "
                (Term.app `b.ι [`j]))))))
           [","])
          (group
           (Term.structInstField
            (Term.structInstLVal `uniq' [])
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`s `m `h] [])]
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.tacticErw__
                    "erw"
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule ["←"] (Term.app `category.comp_id [`m]))
                      ","
                      (Tactic.rwRule ["←"] `Total)
                      ","
                      (Tactic.rwRule [] `comp_sum)]
                     "]")
                    [])
                   [])
                  (group (Tactic.apply "apply" (Term.app `Finset.sum_congr [`rfl])) [])
                  (group (Tactic.intro "intro" [`j `m]) [])
                  (group
                   (Tactic.tacticErw__
                    "erw"
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `reassoc_of [(Term.app `h [`j])]))] "]")
                    [])
                   [])]))))))
           [","])
          (group
           (Term.structInstField
            (Term.structInstLVal `fac' [])
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`s `j] [])]
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.simp
                    "simp"
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `sum_comp)
                      ","
                      (Tactic.simpLemma [] [] `category.assoc)
                      ","
                      (Tactic.simpLemma [] [] `bicone.to_cone_π_app)
                      ","
                      (Tactic.simpLemma [] [] `b.ι_π)
                      ","
                      (Tactic.simpLemma [] [] `comp_dite)]
                     "]"]
                    [])
                   [])
                  (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
                  (group (Tactic.simp "simp" [] [] [] []) [])]))))))
           [])]
         (Term.optEllipsis [])
         []
         "}"))
       [","])
      (group
       (Term.structInstField
        (Term.structInstLVal `IsColimit [])
        ":="
        (Term.structInst
         "{"
         []
         [(group
           (Term.structInstField
            (Term.structInstLVal `desc [])
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`s] [])]
              "=>"
              (Algebra.BigOperators.Basic.«term∑_,_»
               "∑"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
               ", "
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app `b.π [`j])
                " ≫ "
                (Term.app `s.ι.app [`j]))))))
           [","])
          (group
           (Term.structInstField
            (Term.structInstLVal `uniq' [])
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`s `m `h] [])]
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.tacticErw__
                    "erw"
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule ["←"] (Term.app `category.id_comp [`m]))
                      ","
                      (Tactic.rwRule ["←"] `Total)
                      ","
                      (Tactic.rwRule [] `sum_comp)]
                     "]")
                    [])
                   [])
                  (group (Tactic.apply "apply" (Term.app `Finset.sum_congr [`rfl])) [])
                  (group (Tactic.intro "intro" [`j `m]) [])
                  (group
                   (Tactic.tacticErw__
                    "erw"
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc) "," (Tactic.rwRule [] `h)] "]")
                    [])
                   [])]))))))
           [","])
          (group
           (Term.structInstField
            (Term.structInstLVal `fac' [])
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`s `j] [])]
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.simp
                    "simp"
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `comp_sum)
                      ","
                      (Tactic.simpLemma [] ["←"] `category.assoc)
                      ","
                      (Tactic.simpLemma [] [] `bicone.to_cocone_ι_app)
                      ","
                      (Tactic.simpLemma [] [] `b.ι_π)
                      ","
                      (Tactic.simpLemma [] [] `dite_comp)]
                     "]"]
                    [])
                   [])
                  (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
                  (group (Tactic.simp "simp" [] [] [] []) [])]))))))
           [])]
         (Term.optEllipsis [])
         []
         "}"))
       [])]
     (Term.optEllipsis [])
     []
     "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.structInst
   "{"
   []
   [(group (Term.structInstField (Term.structInstLVal `Bicone []) ":=" `b) [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `IsLimit [])
      ":="
      (Term.structInst
       "{"
       []
       [(group
         (Term.structInstField
          (Term.structInstLVal `lift [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`s] [])]
            "=>"
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
             ", "
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app `s.π.app [`j])
              " ≫ "
              (Term.app `b.ι [`j]))))))
         [","])
        (group
         (Term.structInstField
          (Term.structInstLVal `uniq' [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`s `m `h] [])]
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.tacticErw__
                  "erw"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule ["←"] (Term.app `category.comp_id [`m]))
                    ","
                    (Tactic.rwRule ["←"] `Total)
                    ","
                    (Tactic.rwRule [] `comp_sum)]
                   "]")
                  [])
                 [])
                (group (Tactic.apply "apply" (Term.app `Finset.sum_congr [`rfl])) [])
                (group (Tactic.intro "intro" [`j `m]) [])
                (group
                 (Tactic.tacticErw__
                  "erw"
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `reassoc_of [(Term.app `h [`j])]))] "]")
                  [])
                 [])]))))))
         [","])
        (group
         (Term.structInstField
          (Term.structInstLVal `fac' [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`s `j] [])]
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.simp
                  "simp"
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `sum_comp)
                    ","
                    (Tactic.simpLemma [] [] `category.assoc)
                    ","
                    (Tactic.simpLemma [] [] `bicone.to_cone_π_app)
                    ","
                    (Tactic.simpLemma [] [] `b.ι_π)
                    ","
                    (Tactic.simpLemma [] [] `comp_dite)]
                   "]"]
                  [])
                 [])
                (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
                (group (Tactic.simp "simp" [] [] [] []) [])]))))))
         [])]
       (Term.optEllipsis [])
       []
       "}"))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `IsColimit [])
      ":="
      (Term.structInst
       "{"
       []
       [(group
         (Term.structInstField
          (Term.structInstLVal `desc [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`s] [])]
            "=>"
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
             ", "
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app `b.π [`j])
              " ≫ "
              (Term.app `s.ι.app [`j]))))))
         [","])
        (group
         (Term.structInstField
          (Term.structInstLVal `uniq' [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`s `m `h] [])]
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.tacticErw__
                  "erw"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule ["←"] (Term.app `category.id_comp [`m]))
                    ","
                    (Tactic.rwRule ["←"] `Total)
                    ","
                    (Tactic.rwRule [] `sum_comp)]
                   "]")
                  [])
                 [])
                (group (Tactic.apply "apply" (Term.app `Finset.sum_congr [`rfl])) [])
                (group (Tactic.intro "intro" [`j `m]) [])
                (group
                 (Tactic.tacticErw__
                  "erw"
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc) "," (Tactic.rwRule [] `h)] "]")
                  [])
                 [])]))))))
         [","])
        (group
         (Term.structInstField
          (Term.structInstLVal `fac' [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`s `j] [])]
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.simp
                  "simp"
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `comp_sum)
                    ","
                    (Tactic.simpLemma [] ["←"] `category.assoc)
                    ","
                    (Tactic.simpLemma [] [] `bicone.to_cocone_ι_app)
                    ","
                    (Tactic.simpLemma [] [] `b.ι_π)
                    ","
                    (Tactic.simpLemma [] [] `dite_comp)]
                   "]"]
                  [])
                 [])
                (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
                (group (Tactic.simp "simp" [] [] [] []) [])]))))))
         [])]
       (Term.optEllipsis [])
       []
       "}"))
     [])]
   (Term.optEllipsis [])
   []
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.structInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.optEllipsis', expected 'Lean.Parser.Term.optEllipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.structInst
   "{"
   []
   [(group
     (Term.structInstField
      (Term.structInstLVal `desc [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`s] [])]
        "=>"
        (Algebra.BigOperators.Basic.«term∑_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
         ", "
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app `b.π [`j])
          " ≫ "
          (Term.app `s.ι.app [`j]))))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `uniq' [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`s `m `h] [])]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.tacticErw__
              "erw"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule ["←"] (Term.app `category.id_comp [`m]))
                ","
                (Tactic.rwRule ["←"] `Total)
                ","
                (Tactic.rwRule [] `sum_comp)]
               "]")
              [])
             [])
            (group (Tactic.apply "apply" (Term.app `Finset.sum_congr [`rfl])) [])
            (group (Tactic.intro "intro" [`j `m]) [])
            (group
             (Tactic.tacticErw__
              "erw"
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc) "," (Tactic.rwRule [] `h)] "]")
              [])
             [])]))))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `fac' [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`s `j] [])]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `comp_sum)
                ","
                (Tactic.simpLemma [] ["←"] `category.assoc)
                ","
                (Tactic.simpLemma [] [] `bicone.to_cocone_ι_app)
                ","
                (Tactic.simpLemma [] [] `b.ι_π)
                ","
                (Tactic.simpLemma [] [] `dite_comp)]
               "]"]
              [])
             [])
            (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
            (group (Tactic.simp "simp" [] [] [] []) [])]))))))
     [])]
   (Term.optEllipsis [])
   []
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.structInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.optEllipsis', expected 'Lean.Parser.Term.optEllipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`s `j] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.simp
          "simp"
          []
          ["only"]
          ["["
           [(Tactic.simpLemma [] [] `comp_sum)
            ","
            (Tactic.simpLemma [] ["←"] `category.assoc)
            ","
            (Tactic.simpLemma [] [] `bicone.to_cocone_ι_app)
            ","
            (Tactic.simpLemma [] [] `b.ι_π)
            ","
            (Tactic.simpLemma [] [] `dite_comp)]
           "]"]
          [])
         [])
        (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
        (group (Tactic.simp "simp" [] [] [] []) [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `comp_sum)
          ","
          (Tactic.simpLemma [] ["←"] `category.assoc)
          ","
          (Tactic.simpLemma [] [] `bicone.to_cocone_ι_app)
          ","
          (Tactic.simpLemma [] [] `b.ι_π)
          ","
          (Tactic.simpLemma [] [] `dite_comp)]
         "]"]
        [])
       [])
      (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
      (group (Tactic.simp "simp" [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `comp_sum)
     ","
     (Tactic.simpLemma [] ["←"] `category.assoc)
     ","
     (Tactic.simpLemma [] [] `bicone.to_cocone_ι_app)
     ","
     (Tactic.simpLemma [] [] `b.ι_π)
     ","
     (Tactic.simpLemma [] [] `dite_comp)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dite_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b.ι_π
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `bicone.to_cocone_ι_app
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `category.assoc
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comp_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`s `m `h] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.tacticErw__
          "erw"
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule ["←"] (Term.app `category.id_comp [`m]))
            ","
            (Tactic.rwRule ["←"] `Total)
            ","
            (Tactic.rwRule [] `sum_comp)]
           "]")
          [])
         [])
        (group (Tactic.apply "apply" (Term.app `Finset.sum_congr [`rfl])) [])
        (group (Tactic.intro "intro" [`j `m]) [])
        (group
         (Tactic.tacticErw__
          "erw"
          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc) "," (Tactic.rwRule [] `h)] "]")
          [])
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticErw__
        "erw"
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] (Term.app `category.id_comp [`m]))
          ","
          (Tactic.rwRule ["←"] `Total)
          ","
          (Tactic.rwRule [] `sum_comp)]
         "]")
        [])
       [])
      (group (Tactic.apply "apply" (Term.app `Finset.sum_congr [`rfl])) [])
      (group (Tactic.intro "intro" [`j `m]) [])
      (group
       (Tactic.tacticErw__
        "erw"
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc) "," (Tactic.rwRule [] `h)] "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticErw__
   "erw"
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc) "," (Tactic.rwRule [] `h)] "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticErw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `category.assoc
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`j `m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" (Term.app `Finset.sum_congr [`rfl]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset.sum_congr [`rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.sum_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticErw__
   "erw"
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule ["←"] (Term.app `category.id_comp [`m]))
     ","
     (Tactic.rwRule ["←"] `Total)
     ","
     (Tactic.rwRule [] `sum_comp)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticErw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sum_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Total
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `category.id_comp [`m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `category.id_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`s] [])]
    "=>"
    (Algebra.BigOperators.Basic.«term∑_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
     ", "
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `b.π [`j]) " ≫ " (Term.app `s.ι.app [`j])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
   ", "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `b.π [`j]) " ≫ " (Term.app `s.ι.app [`j])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `b.π [`j]) " ≫ " (Term.app `s.ι.app [`j]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `s.ι.app [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `s.ι.app
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `b.π [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `b.π
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    In a preadditive category, we can construct a biproduct for `f : J → C` from
    any bicone `b` for `f` satisfying `total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X`.
    
    (That is, such a bicone is a limit cone and a colimit cocone.)
    -/
  theorem
    has_biproduct_of_total
    { f : J → C } ( b : bicone f ) ( total : ∑ j : J , b.π j ≫ b.ι j = 𝟙 b.X ) : has_biproduct f
    :=
      has_biproduct.mk
        {
          Bicone := b ,
            IsLimit
                :=
                {
                  lift := fun s => ∑ j , s.π.app j ≫ b.ι j ,
                    uniq'
                        :=
                        fun
                          s m h
                            =>
                            by
                              erw [ ← category.comp_id m , ← Total , comp_sum ]
                                apply Finset.sum_congr rfl
                                intro j m
                                erw [ reassoc_of h j ]
                      ,
                    fac'
                      :=
                      fun
                        s j
                          =>
                          by
                            simp only [ sum_comp , category.assoc , bicone.to_cone_π_app , b.ι_π , comp_dite ]
                              dsimp
                              simp
                  }
              ,
            IsColimit
              :=
              {
                desc := fun s => ∑ j , b.π j ≫ s.ι.app j ,
                  uniq'
                      :=
                      fun
                        s m h
                          =>
                          by
                            erw [ ← category.id_comp m , ← Total , sum_comp ]
                              apply Finset.sum_congr rfl
                              intro j m
                              erw [ category.assoc , h ]
                    ,
                  fac'
                    :=
                    fun
                      s j
                        =>
                        by
                          simp only [ comp_sum , ← category.assoc , bicone.to_cocone_ι_app , b.ι_π , dite_comp ]
                            dsimp
                            simp
                }
          }

/--  In a preadditive category, if the product over `f : J → C` exists,
    then the biproduct over `f` exists. -/
theorem has_biproduct.of_has_product (f : J → C) [has_product f] : has_biproduct f :=
  has_biproduct_of_total
    { x := pi_obj f, π := limits.pi.π f,
      ι := fun j => pi.lift fun j' => if h : j = j' then eq_to_hom (congr_argₓ f h) else 0,
      ι_π := fun j j' => by
        simp }
    (by
      ext
      simp [sum_comp, comp_dite])

/--  In a preadditive category, if the coproduct over `f : J → C` exists,
    then the biproduct over `f` exists. -/
theorem has_biproduct.of_has_coproduct (f : J → C) [has_coproduct f] : has_biproduct f :=
  has_biproduct_of_total
    { x := sigma_obj f, π := fun j => sigma.desc fun j' => if h : j' = j then eq_to_hom (congr_argₓ f h) else 0,
      ι := limits.sigma.ι f,
      ι_π := fun j j' => by
        simp }
    (by
      ext
      simp only [comp_sum, limits.colimit.ι_desc_assoc, eq_self_iff_true, limits.colimit.ι_desc, category.comp_id]
      dsimp
      simp only [dite_comp, Finset.sum_dite_eq, Finset.mem_univ, if_true, category.id_comp, eq_to_hom_refl, zero_comp])

/--  A preadditive category with finite products has finite biproducts. -/
theorem has_finite_biproducts.of_has_finite_products [has_finite_products C] : has_finite_biproducts C :=
  ⟨fun J _ _ =>
    { HasBiproduct := fun F => by
        exact has_biproduct.of_has_product _ }⟩

/--  A preadditive category with finite coproducts has finite biproducts. -/
theorem has_finite_biproducts.of_has_finite_coproducts [has_finite_coproducts C] : has_finite_biproducts C :=
  ⟨fun J _ _ =>
    { HasBiproduct := fun F => by
        exact has_biproduct.of_has_coproduct _ }⟩

section

variable {f : J → C} [has_biproduct f]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "\nIn any preadditive category, any biproduct satsifies\n`∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`\n-/")]
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `biproduct.total [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_=_»
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `J]))
      ", "
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `biproduct.π [`f `j])
       " ≫ "
       (Term.app `biproduct.ι [`f `j])))
     "="
     (Term.app
      (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
      [(CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term⨁_» "⨁ " `f)]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `j) (Tactic.rcasesPat.one `j')] []) [])
       (group
        (Tactic.simp
         "simp"
         []
         []
         ["["
          [(Tactic.simpLemma [] [] `comp_sum)
           ","
           (Tactic.simpLemma [] [] `sum_comp)
           ","
           (Tactic.simpLemma [] [] `biproduct.ι_π)
           ","
           (Tactic.simpLemma [] [] `comp_dite)
           ","
           (Tactic.simpLemma [] [] `dite_comp)]
          "]"]
         [])
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `j) (Tactic.rcasesPat.one `j')] []) [])
      (group
       (Tactic.simp
        "simp"
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `comp_sum)
          ","
          (Tactic.simpLemma [] [] `sum_comp)
          ","
          (Tactic.simpLemma [] [] `biproduct.ι_π)
          ","
          (Tactic.simpLemma [] [] `comp_dite)
          ","
          (Tactic.simpLemma [] [] `dite_comp)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   []
   ["["
    [(Tactic.simpLemma [] [] `comp_sum)
     ","
     (Tactic.simpLemma [] [] `sum_comp)
     ","
     (Tactic.simpLemma [] [] `biproduct.ι_π)
     ","
     (Tactic.simpLemma [] [] `comp_dite)
     ","
     (Tactic.simpLemma [] [] `dite_comp)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dite_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comp_dite
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `biproduct.ι_π
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sum_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comp_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [(Tactic.rcasesPat.one `j) (Tactic.rcasesPat.one `j')] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `J]))
    ", "
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     (Term.app `biproduct.π [`f `j])
     " ≫ "
     (Term.app `biproduct.ι [`f `j])))
   "="
   (Term.app
    (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
    [(CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term⨁_» "⨁ " `f)]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
   [(CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term⨁_» "⨁ " `f)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term⨁_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term⨁_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term⨁_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term⨁_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term⨁_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term⨁_» "⨁ " `f)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term⨁_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 20 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 20, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term⨁_» "⨁ " `f) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term𝟙»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `J]))
   ", "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
    (Term.app `biproduct.π [`f `j])
    " ≫ "
    (Term.app `biproduct.ι [`f `j])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   (Term.app `biproduct.π [`f `j])
   " ≫ "
   (Term.app `biproduct.ι [`f `j]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `biproduct.ι [`f `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `biproduct.ι
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `biproduct.π [`f `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `biproduct.π
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      In any preadditive category, any biproduct satsifies
      `∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`
      -/
    @[ simp ]
  theorem
    biproduct.total
    : ∑ j : J , biproduct.π f j ≫ biproduct.ι f j = 𝟙 ⨁ f
    := by ext j j' simp [ comp_sum , sum_comp , biproduct.ι_π , comp_dite , dite_comp ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `biproduct.lift_eq [])
  (Command.declSig
   [(Term.implicitBinder "{" [`T] [":" `C] "}")
    (Term.implicitBinder
     "{"
     [`g]
     [":"
      (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Combinatorics.Quiver.«term_⟶_» `T " ⟶ " (Term.app `f [`j])))]
     "}")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `biproduct.lift [`g])
     "="
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
      ", "
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `g [`j])
       " ≫ "
       (Term.app `biproduct.ι [`f `j]))))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `j)] []) [])
       (group
        (Tactic.simp
         "simp"
         []
         []
         ["["
          [(Tactic.simpLemma [] [] `sum_comp)
           ","
           (Tactic.simpLemma [] [] `biproduct.ι_π)
           ","
           (Tactic.simpLemma [] [] `comp_dite)]
          "]"]
         [])
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `j)] []) [])
      (group
       (Tactic.simp
        "simp"
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `sum_comp)
          ","
          (Tactic.simpLemma [] [] `biproduct.ι_π)
          ","
          (Tactic.simpLemma [] [] `comp_dite)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   []
   ["["
    [(Tactic.simpLemma [] [] `sum_comp)
     ","
     (Tactic.simpLemma [] [] `biproduct.ι_π)
     ","
     (Tactic.simpLemma [] [] `comp_dite)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comp_dite
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `biproduct.ι_π
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sum_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [(Tactic.rcasesPat.one `j)] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app `biproduct.lift [`g])
   "="
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
    ", "
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `g [`j]) " ≫ " (Term.app `biproduct.ι [`f `j]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
   ", "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `g [`j]) " ≫ " (Term.app `biproduct.ι [`f `j])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `g [`j]) " ≫ " (Term.app `biproduct.ι [`f `j]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `biproduct.ι [`f `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `biproduct.ι
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `g [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  biproduct.lift_eq
  { T : C } { g : ∀ j , T ⟶ f j } : biproduct.lift g = ∑ j , g j ≫ biproduct.ι f j
  := by ext j simp [ sum_comp , biproduct.ι_π , comp_dite ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `biproduct.desc_eq [])
  (Command.declSig
   [(Term.implicitBinder "{" [`T] [":" `C] "}")
    (Term.implicitBinder
     "{"
     [`g]
     [":"
      (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Combinatorics.Quiver.«term_⟶_» (Term.app `f [`j]) " ⟶ " `T))]
     "}")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `biproduct.desc [`g])
     "="
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
      ", "
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `biproduct.π [`f `j])
       " ≫ "
       (Term.app `g [`j]))))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `j)] []) [])
       (group
        (Tactic.simp
         "simp"
         []
         []
         ["["
          [(Tactic.simpLemma [] [] `comp_sum)
           ","
           (Tactic.simpLemma [] [] `biproduct.ι_π_assoc)
           ","
           (Tactic.simpLemma [] [] `dite_comp)]
          "]"]
         [])
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `j)] []) [])
      (group
       (Tactic.simp
        "simp"
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `comp_sum)
          ","
          (Tactic.simpLemma [] [] `biproduct.ι_π_assoc)
          ","
          (Tactic.simpLemma [] [] `dite_comp)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   []
   ["["
    [(Tactic.simpLemma [] [] `comp_sum)
     ","
     (Tactic.simpLemma [] [] `biproduct.ι_π_assoc)
     ","
     (Tactic.simpLemma [] [] `dite_comp)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dite_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `biproduct.ι_π_assoc
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comp_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [(Tactic.rcasesPat.one `j)] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app `biproduct.desc [`g])
   "="
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
    ", "
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `biproduct.π [`f `j]) " ≫ " (Term.app `g [`j]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
   ", "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `biproduct.π [`f `j]) " ≫ " (Term.app `g [`j])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `biproduct.π [`f `j]) " ≫ " (Term.app `g [`j]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `g [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `biproduct.π [`f `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `biproduct.π
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  biproduct.desc_eq
  { T : C } { g : ∀ j , f j ⟶ T } : biproduct.desc g = ∑ j , biproduct.π f j ≫ g j
  := by ext j simp [ comp_sum , biproduct.ι_π_assoc , dite_comp ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes
    "@["
    [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))
     ","
     (Term.attrInstance (Term.attrKind []) (Attr.reassoc "reassoc" []))]
    "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `biproduct.lift_desc [])
  (Command.declSig
   [(Term.implicitBinder "{" [`T `U] [":" `C] "}")
    (Term.implicitBinder
     "{"
     [`g]
     [":"
      (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Combinatorics.Quiver.«term_⟶_» `T " ⟶ " (Term.app `f [`j])))]
     "}")
    (Term.implicitBinder
     "{"
     [`h]
     [":"
      (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Combinatorics.Quiver.«term_⟶_» (Term.app `f [`j]) " ⟶ " `U))]
     "}")]
   (Term.typeSpec
    ":"
    («term_=_»
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.app `biproduct.lift [`g])
      " ≫ "
      (Term.app `biproduct.desc [`h]))
     "="
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `J]))
      ", "
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `g [`j]) " ≫ " (Term.app `h [`j]))))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.simp
         "simp"
         []
         []
         ["["
          [(Tactic.simpLemma [] [] `biproduct.lift_eq)
           ","
           (Tactic.simpLemma [] [] `biproduct.desc_eq)
           ","
           (Tactic.simpLemma [] [] `comp_sum)
           ","
           (Tactic.simpLemma [] [] `sum_comp)
           ","
           (Tactic.simpLemma [] [] `biproduct.ι_π_assoc)
           ","
           (Tactic.simpLemma [] [] `comp_dite)
           ","
           (Tactic.simpLemma [] [] `dite_comp)]
          "]"]
         [])
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `biproduct.lift_eq)
          ","
          (Tactic.simpLemma [] [] `biproduct.desc_eq)
          ","
          (Tactic.simpLemma [] [] `comp_sum)
          ","
          (Tactic.simpLemma [] [] `sum_comp)
          ","
          (Tactic.simpLemma [] [] `biproduct.ι_π_assoc)
          ","
          (Tactic.simpLemma [] [] `comp_dite)
          ","
          (Tactic.simpLemma [] [] `dite_comp)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   []
   ["["
    [(Tactic.simpLemma [] [] `biproduct.lift_eq)
     ","
     (Tactic.simpLemma [] [] `biproduct.desc_eq)
     ","
     (Tactic.simpLemma [] [] `comp_sum)
     ","
     (Tactic.simpLemma [] [] `sum_comp)
     ","
     (Tactic.simpLemma [] [] `biproduct.ι_π_assoc)
     ","
     (Tactic.simpLemma [] [] `comp_dite)
     ","
     (Tactic.simpLemma [] [] `dite_comp)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dite_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comp_dite
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `biproduct.ι_π_assoc
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sum_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comp_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `biproduct.desc_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `biproduct.lift_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
    (Term.app `biproduct.lift [`g])
    " ≫ "
    (Term.app `biproduct.desc [`h]))
   "="
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `J]))
    ", "
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `g [`j]) " ≫ " (Term.app `h [`j]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `J]))
   ", "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `g [`j]) " ≫ " (Term.app `h [`j])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `g [`j]) " ≫ " (Term.app `h [`j]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `h [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `g [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp , reassoc ]
  theorem
    biproduct.lift_desc
    { T U : C } { g : ∀ j , T ⟶ f j } { h : ∀ j , f j ⟶ U } : biproduct.lift g ≫ biproduct.desc h = ∑ j : J , g j ≫ h j
    :=
      by
        simp
          [ biproduct.lift_eq , biproduct.desc_eq , comp_sum , sum_comp , biproduct.ι_π_assoc , comp_dite , dite_comp ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `biproduct.map_eq [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `has_finite_biproducts [`C]) "]")
    (Term.implicitBinder "{" [`f `g] [":" (Term.arrow `J "→" `C)] "}")
    (Term.implicitBinder
     "{"
     [`h]
     [":"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`j] [])]
       ","
       (Combinatorics.Quiver.«term_⟶_» (Term.app `f [`j]) " ⟶ " (Term.app `g [`j])))]
     "}")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `biproduct.map [`h])
     "="
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `J]))
      ", "
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `biproduct.π [`f `j])
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `h [`j])
        " ≫ "
        (Term.app `biproduct.ι [`g `j])))))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.ext "ext" [] []) [])
       (group
        (Tactic.simp
         "simp"
         []
         []
         ["["
          [(Tactic.simpLemma [] [] `biproduct.ι_π)
           ","
           (Tactic.simpLemma [] [] `biproduct.ι_π_assoc)
           ","
           (Tactic.simpLemma [] [] `comp_sum)
           ","
           (Tactic.simpLemma [] [] `sum_comp)
           ","
           (Tactic.simpLemma [] [] `comp_dite)
           ","
           (Tactic.simpLemma [] [] `dite_comp)]
          "]"]
         [])
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.ext "ext" [] []) [])
      (group
       (Tactic.simp
        "simp"
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `biproduct.ι_π)
          ","
          (Tactic.simpLemma [] [] `biproduct.ι_π_assoc)
          ","
          (Tactic.simpLemma [] [] `comp_sum)
          ","
          (Tactic.simpLemma [] [] `sum_comp)
          ","
          (Tactic.simpLemma [] [] `comp_dite)
          ","
          (Tactic.simpLemma [] [] `dite_comp)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   []
   ["["
    [(Tactic.simpLemma [] [] `biproduct.ι_π)
     ","
     (Tactic.simpLemma [] [] `biproduct.ι_π_assoc)
     ","
     (Tactic.simpLemma [] [] `comp_sum)
     ","
     (Tactic.simpLemma [] [] `sum_comp)
     ","
     (Tactic.simpLemma [] [] `comp_dite)
     ","
     (Tactic.simpLemma [] [] `dite_comp)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dite_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comp_dite
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sum_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comp_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `biproduct.ι_π_assoc
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `biproduct.ι_π
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app `biproduct.map [`h])
   "="
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `J]))
    ", "
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
     (Term.app `biproduct.π [`f `j])
     " ≫ "
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.app `h [`j])
      " ≫ "
      (Term.app `biproduct.ι [`g `j])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" `J]))
   ", "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
    (Term.app `biproduct.π [`f `j])
    " ≫ "
    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `h [`j]) " ≫ " (Term.app `biproduct.ι [`g `j]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
   (Term.app `biproduct.π [`f `j])
   " ≫ "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `h [`j]) " ≫ " (Term.app `biproduct.ι [`g `j])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `h [`j]) " ≫ " (Term.app `biproduct.ι [`g `j]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `biproduct.ι [`g `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `biproduct.ι
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `h [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `biproduct.π [`f `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `biproduct.π
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  biproduct.map_eq
  [ has_finite_biproducts C ] { f g : J → C } { h : ∀ j , f j ⟶ g j }
    : biproduct.map h = ∑ j : J , biproduct.π f j ≫ h j ≫ biproduct.ι g j
  := by ext simp [ biproduct.ι_π , biproduct.ι_π_assoc , comp_sum , sum_comp , comp_dite , dite_comp ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes
    "@["
    [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))
     ","
     (Term.attrInstance (Term.attrKind []) (Attr.reassoc "reassoc" []))]
    "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `biproduct.matrix_desc [])
  (Command.declSig
   [(Term.implicitBinder "{" [`K] [":" (Term.type "Type" [`v])] "}")
    (Term.instBinder "[" [] (Term.app `Fintype [`K]) "]")
    (Term.instBinder "[" [] (Term.app `DecidableEq [`K]) "]")
    (Term.instBinder "[" [] (Term.app `has_finite_biproducts [`C]) "]")
    (Term.implicitBinder "{" [`f] [":" (Term.arrow `J "→" `C)] "}")
    (Term.implicitBinder "{" [`g] [":" (Term.arrow `K "→" `C)] "}")
    (Term.explicitBinder
     "("
     [`m]
     [":"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`j `k] [])]
       ","
       (Combinatorics.Quiver.«term_⟶_» (Term.app `f [`j]) " ⟶ " (Term.app `g [`k])))]
     []
     ")")
    (Term.implicitBinder "{" [`P] [] "}")
    (Term.explicitBinder
     "("
     [`x]
     [":"
      (Term.forall "∀" [(Term.simpleBinder [`k] [])] "," (Combinatorics.Quiver.«term_⟶_» (Term.app `g [`k]) " ⟶ " `P))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.app `biproduct.matrix [`m])
      " ≫ "
      (Term.app `biproduct.desc [`x]))
     "="
     (Term.app
      `biproduct.desc
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`j] [])]
         "=>"
         (Algebra.BigOperators.Basic.«term∑_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
          ", "
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app `m [`j `k])
           " ≫ "
           (Term.app `x [`k])))))]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented [(group (Tactic.ext "ext" [] []) []) (group (Tactic.simp "simp" [] [] [] []) [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented [(group (Tactic.ext "ext" [] []) []) (group (Tactic.simp "simp" [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
    (Term.app `biproduct.matrix [`m])
    " ≫ "
    (Term.app `biproduct.desc [`x]))
   "="
   (Term.app
    `biproduct.desc
    [(Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`j] [])]
       "=>"
       (Algebra.BigOperators.Basic.«term∑_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
        ", "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `m [`j `k]) " ≫ " (Term.app `x [`k])))))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `biproduct.desc
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`j] [])]
      "=>"
      (Algebra.BigOperators.Basic.«term∑_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
       ", "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `m [`j `k]) " ≫ " (Term.app `x [`k])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`j] [])]
    "=>"
    (Algebra.BigOperators.Basic.«term∑_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
     ", "
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `m [`j `k]) " ≫ " (Term.app `x [`k])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
   ", "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `m [`j `k]) " ≫ " (Term.app `x [`k])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `m [`j `k]) " ≫ " (Term.app `x [`k]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `x [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `m [`j `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp , reassoc ]
  theorem
    biproduct.matrix_desc
    { K : Type v }
        [ Fintype K ]
        [ DecidableEq K ]
        [ has_finite_biproducts C ]
        { f : J → C }
        { g : K → C }
        ( m : ∀ j k , f j ⟶ g k )
        { P }
        ( x : ∀ k , g k ⟶ P )
      : biproduct.matrix m ≫ biproduct.desc x = biproduct.desc fun j => ∑ k , m j k ≫ x k
    := by ext simp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes
    "@["
    [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))
     ","
     (Term.attrInstance (Term.attrKind []) (Attr.reassoc "reassoc" []))]
    "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `biproduct.lift_matrix [])
  (Command.declSig
   [(Term.implicitBinder "{" [`K] [":" (Term.type "Type" [`v])] "}")
    (Term.instBinder "[" [] (Term.app `Fintype [`K]) "]")
    (Term.instBinder "[" [] (Term.app `DecidableEq [`K]) "]")
    (Term.instBinder "[" [] (Term.app `has_finite_biproducts [`C]) "]")
    (Term.implicitBinder "{" [`f] [":" (Term.arrow `J "→" `C)] "}")
    (Term.implicitBinder "{" [`g] [":" (Term.arrow `K "→" `C)] "}")
    (Term.implicitBinder "{" [`P] [] "}")
    (Term.explicitBinder
     "("
     [`x]
     [":"
      (Term.forall "∀" [(Term.simpleBinder [`j] [])] "," (Combinatorics.Quiver.«term_⟶_» `P " ⟶ " (Term.app `f [`j])))]
     []
     ")")
    (Term.explicitBinder
     "("
     [`m]
     [":"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`j `k] [])]
       ","
       (Combinatorics.Quiver.«term_⟶_» (Term.app `f [`j]) " ⟶ " (Term.app `g [`k])))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.app `biproduct.lift [`x])
      " ≫ "
      (Term.app `biproduct.matrix [`m]))
     "="
     (Term.app
      `biproduct.lift
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`k] [])]
         "=>"
         (Algebra.BigOperators.Basic.«term∑_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
          ", "
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app `x [`j])
           " ≫ "
           (Term.app `m [`j `k])))))]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented [(group (Tactic.ext "ext" [] []) []) (group (Tactic.simp "simp" [] [] [] []) [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented [(group (Tactic.ext "ext" [] []) []) (group (Tactic.simp "simp" [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
    (Term.app `biproduct.lift [`x])
    " ≫ "
    (Term.app `biproduct.matrix [`m]))
   "="
   (Term.app
    `biproduct.lift
    [(Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`k] [])]
       "=>"
       (Algebra.BigOperators.Basic.«term∑_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
        ", "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `x [`j]) " ≫ " (Term.app `m [`j `k])))))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `biproduct.lift
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`k] [])]
      "=>"
      (Algebra.BigOperators.Basic.«term∑_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
       ", "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `x [`j]) " ≫ " (Term.app `m [`j `k])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`k] [])]
    "=>"
    (Algebra.BigOperators.Basic.«term∑_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
     ", "
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `x [`j]) " ≫ " (Term.app `m [`j `k])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
   ", "
   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `x [`j]) " ≫ " (Term.app `m [`j `k])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.app `x [`j]) " ≫ " (Term.app `m [`j `k]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `m [`j `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app `x [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp , reassoc ]
  theorem
    biproduct.lift_matrix
    { K : Type v }
        [ Fintype K ]
        [ DecidableEq K ]
        [ has_finite_biproducts C ]
        { f : J → C }
        { g : K → C }
        { P }
        ( x : ∀ j , P ⟶ f j )
        ( m : ∀ j k , f j ⟶ g k )
      : biproduct.lift x ≫ biproduct.matrix m = biproduct.lift fun k => ∑ j , x j ≫ m j k
    := by ext simp

@[reassoc]
theorem biproduct.matrix_map {K : Type v} [Fintype K] [DecidableEq K] [has_finite_biproducts C] {f : J → C} {g : K → C}
    {h : K → C} (m : ∀ j k, f j ⟶ g k) (n : ∀ k, g k ⟶ h k) :
    biproduct.matrix m ≫ biproduct.map n = biproduct.matrix fun j k => m j k ≫ n k := by
  ext
  simp

@[reassoc]
theorem biproduct.map_matrix {K : Type v} [Fintype K] [DecidableEq K] [has_finite_biproducts C] {f : J → C} {g : J → C}
    {h : K → C} (m : ∀ k, f k ⟶ g k) (n : ∀ j k, g j ⟶ h k) :
    biproduct.map m ≫ biproduct.matrix n = biproduct.matrix fun j k => m j ≫ n j k := by
  ext
  simp

end

/-- 
In a preadditive category, we can construct a binary biproduct for `X Y : C` from
any binary bicone `b` satisfying `total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
theorem has_binary_biproduct_of_total {X Y : C} (b : binary_bicone X Y)
    (total : ((b.fst ≫ b.inl)+b.snd ≫ b.inr) = 𝟙 b.X) : has_binary_biproduct X Y :=
  has_binary_biproduct.mk
    { Bicone := b,
      IsLimit :=
        { lift := fun s => (binary_fan.fst s ≫ b.inl)+binary_fan.snd s ≫ b.inr,
          uniq' := fun s m h => by
            erw [← category.comp_id m, ← Total, comp_add, reassoc_of (h walking_pair.left),
              reassoc_of (h walking_pair.right)],
          fac' := fun s j => by
            cases j <;> simp },
      IsColimit :=
        { desc := fun s => (b.fst ≫ binary_cofan.inl s)+b.snd ≫ binary_cofan.inr s,
          uniq' := fun s m h => by
            erw [← category.id_comp m, ← Total, add_comp, category.assoc, category.assoc, h walking_pair.left,
              h walking_pair.right],
          fac' := fun s j => by
            cases j <;> simp } }

/--  In a preadditive category, if the product of `X` and `Y` exists, then the
    binary biproduct of `X` and `Y` exists. -/
theorem has_binary_biproduct.of_has_binary_product (X Y : C) [has_binary_product X Y] : has_binary_biproduct X Y :=
  has_binary_biproduct_of_total
    { x := X ⨯ Y, fst := CategoryTheory.Limits.prod.fst, snd := CategoryTheory.Limits.prod.snd,
      inl := prod.lift (𝟙 X) 0, inr := prod.lift 0 (𝟙 Y) }
    (by
      ext <;> simp [add_comp])

/--  In a preadditive category, if all binary products exist, then all binary biproducts exist. -/
theorem has_binary_biproducts.of_has_binary_products [has_binary_products C] : has_binary_biproducts C :=
  { HasBinaryBiproduct := fun X Y => has_binary_biproduct.of_has_binary_product X Y }

/--  In a preadditive category, if the coproduct of `X` and `Y` exists, then the
    binary biproduct of `X` and `Y` exists. -/
theorem has_binary_biproduct.of_has_binary_coproduct (X Y : C) [has_binary_coproduct X Y] : has_binary_biproduct X Y :=
  has_binary_biproduct_of_total
    { x := X ⨿ Y, fst := coprod.desc (𝟙 X) 0, snd := coprod.desc 0 (𝟙 Y), inl := CategoryTheory.Limits.coprod.inl,
      inr := CategoryTheory.Limits.coprod.inr }
    (by
      ext <;> simp [add_comp])

/--  In a preadditive category, if all binary coproducts exist, then all binary biproducts exist. -/
theorem has_binary_biproducts.of_has_binary_coproducts [has_binary_coproducts C] : has_binary_biproducts C :=
  { HasBinaryBiproduct := fun X Y => has_binary_biproduct.of_has_binary_coproduct X Y }

section

variable {X Y : C} [has_binary_biproduct X Y]

/-- 
In any preadditive category, any binary biproduct satsifies
`biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y)`.
-/
@[simp]
theorem biprod.total : ((biprod.fst ≫ biprod.inl)+biprod.snd ≫ biprod.inr) = 𝟙 (X ⊞ Y) := by
  ext <;> simp [add_comp]

theorem biprod.lift_eq {T : C} {f : T ⟶ X} {g : T ⟶ Y} : biprod.lift f g = (f ≫ biprod.inl)+g ≫ biprod.inr := by
  ext <;> simp [add_comp]

theorem biprod.desc_eq {T : C} {f : X ⟶ T} {g : Y ⟶ T} : biprod.desc f g = (biprod.fst ≫ f)+biprod.snd ≫ g := by
  ext <;> simp [add_comp]

@[simp, reassoc]
theorem biprod.lift_desc {T U : C} {f : T ⟶ X} {g : T ⟶ Y} {h : X ⟶ U} {i : Y ⟶ U} :
    biprod.lift f g ≫ biprod.desc h i = (f ≫ h)+g ≫ i := by
  simp [biprod.lift_eq, biprod.desc_eq]

theorem biprod.map_eq [has_binary_biproducts C] {W X Y Z : C} {f : W ⟶ Y} {g : X ⟶ Z} :
    biprod.map f g = (biprod.fst ≫ f ≫ biprod.inl)+biprod.snd ≫ g ≫ biprod.inr := by
  apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp

end

end Preadditive

end CategoryTheory.Limits

