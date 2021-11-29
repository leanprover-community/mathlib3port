import Mathbin.CategoryTheory.Limits.Shapes.Products 
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers 
import Mathbin.CategoryTheory.Limits.ConeCategory 
import Mathbin.CategoryTheory.Adjunction.Default

/-!

# Multi-(co)equalizers

A *multiequalizer* is an equalizer of two morphisms between two products.
Since both products and equalizers are limits, such an object is again a limit.
This file provides the diagram whose limit is indeed such an object.
In fact, it is well-known that any limit can be obtained as a multiequalizer.
The dual construction (multicoequalizers) is also provided.

## Projects

Prove that a multiequalizer can be identified with
an equalizer between products (and analogously for multicoequalizers).

Prove that the limit of any diagram is a multiequalizer (and similarly for colimits).

-/


namespace CategoryTheory.Limits

open CategoryTheory

universe v u

/-- The type underlying the multiequalizer diagram. -/
@[nolint unused_arguments]
inductive walking_multicospan {L R : Type v} (fst snd : R → L) : Type v
  | left : L → walking_multicospan
  | right : R → walking_multicospan

/-- The type underlying the multiecoqualizer diagram. -/
@[nolint unused_arguments]
inductive walking_multispan {L R : Type v} (fst snd : L → R) : Type v
  | left : L → walking_multispan
  | right : R → walking_multispan

namespace WalkingMulticospan

variable {L R : Type v} {fst snd : R → L}

instance [Inhabited L] : Inhabited (walking_multicospan fst snd) :=
  ⟨left (default _)⟩

/-- Morphisms for `walking_multicospan`. -/
inductive hom : ∀ a b : walking_multicospan fst snd, Type v
  | id A : hom A A
  | fst b : hom (left (fst b)) (right b)
  | snd b : hom (left (snd b)) (right b)

instance {a : walking_multicospan fst snd} : Inhabited (hom a a) :=
  ⟨hom.id _⟩

/-- Composition of morphisms for `walking_multicospan`. -/
def hom.comp : ∀ {A B C : walking_multicospan fst snd} f : hom A B g : hom B C, hom A C
| _, _, _, hom.id X, f => f
| _, _, _, hom.fst b, hom.id X => hom.fst b
| _, _, _, hom.snd b, hom.id X => hom.snd b

instance : small_category (walking_multicospan fst snd) :=
  { Hom := hom, id := hom.id, comp := fun X Y Z => hom.comp,
    id_comp' :=
      by 
        rintro (_ | _) (_ | _) (_ | _ | _)
        tidy,
    comp_id' :=
      by 
        rintro (_ | _) (_ | _) (_ | _ | _)
        tidy,
    assoc' :=
      by 
        rintro (_ | _) (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) (_ | _ | _)
        tidy }

end WalkingMulticospan

namespace WalkingMultispan

variable {L R : Type v} {fst snd : L → R}

instance [Inhabited L] : Inhabited (walking_multispan fst snd) :=
  ⟨left (default _)⟩

/-- Morphisms for `walking_multispan`. -/
inductive hom : ∀ a b : walking_multispan fst snd, Type v
  | id A : hom A A
  | fst a : hom (left a) (right (fst a))
  | snd a : hom (left a) (right (snd a))

instance {a : walking_multispan fst snd} : Inhabited (hom a a) :=
  ⟨hom.id _⟩

/-- Composition of morphisms for `walking_multispan`. -/
def hom.comp : ∀ {A B C : walking_multispan fst snd} f : hom A B g : hom B C, hom A C
| _, _, _, hom.id X, f => f
| _, _, _, hom.fst a, hom.id X => hom.fst a
| _, _, _, hom.snd a, hom.id X => hom.snd a

instance : small_category (walking_multispan fst snd) :=
  { Hom := hom, id := hom.id, comp := fun X Y Z => hom.comp,
    id_comp' :=
      by 
        rintro (_ | _) (_ | _) (_ | _ | _)
        tidy,
    comp_id' :=
      by 
        rintro (_ | _) (_ | _) (_ | _ | _)
        tidy,
    assoc' :=
      by 
        rintro (_ | _) (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) (_ | _ | _)
        tidy }

end WalkingMultispan

/-- This is a structure encapsulating the data necessary to define a `multicospan`. -/
@[nolint has_inhabited_instance]
structure multicospan_index (C : Type u) [category.{v} C] where 
  (L R : Type v)
  (fstTo sndTo : R → L)
  left : L → C 
  right : R → C 
  fst : ∀ b, left (fst_to b) ⟶ right b 
  snd : ∀ b, left (snd_to b) ⟶ right b

/-- This is a structure encapsulating the data necessary to define a `multispan`. -/
@[nolint has_inhabited_instance]
structure multispan_index (C : Type u) [category.{v} C] where 
  (L R : Type v)
  (fstFrom sndFrom : L → R)
  left : L → C 
  right : R → C 
  fst : ∀ a, left a ⟶ right (fst_from a)
  snd : ∀ a, left a ⟶ right (snd_from a)

namespace MulticospanIndex

variable {C : Type u} [category.{v} C] (I : multicospan_index C)

/-- The multicospan associated to `I : multicospan_index`. -/
def multicospan : walking_multicospan I.fst_to I.snd_to ⥤ C :=
  { obj :=
      fun x =>
        match x with 
        | walking_multicospan.left a => I.left a
        | walking_multicospan.right b => I.right b,
    map :=
      fun x y f =>
        match x, y, f with 
        | _, _, walking_multicospan.hom.id x => 𝟙 _
        | _, _, walking_multicospan.hom.fst b => I.fst _
        | _, _, walking_multicospan.hom.snd b => I.snd _,
    map_id' :=
      by 
        rintro (_ | _)
        tidy,
    map_comp' :=
      by 
        rintro (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _)
        tidy }

@[simp]
theorem multicospan_obj_left a : I.multicospan.obj (walking_multicospan.left a) = I.left a :=
  rfl

@[simp]
theorem multicospan_obj_right b : I.multicospan.obj (walking_multicospan.right b) = I.right b :=
  rfl

@[simp]
theorem multicospan_map_fst b : I.multicospan.map (walking_multicospan.hom.fst b) = I.fst b :=
  rfl

@[simp]
theorem multicospan_map_snd b : I.multicospan.map (walking_multicospan.hom.snd b) = I.snd b :=
  rfl

variable [has_product I.left] [has_product I.right]

/-- The induced map `∏ I.left ⟶ ∏ I.right` via `I.fst`. -/
noncomputable def fst_pi_map : ∏ I.left ⟶ ∏ I.right :=
  pi.lift fun b => pi.π I.left (I.fst_to b) ≫ I.fst b

/-- The induced map `∏ I.left ⟶ ∏ I.right` via `I.snd`. -/
noncomputable def snd_pi_map : ∏ I.left ⟶ ∏ I.right :=
  pi.lift fun b => pi.π I.left (I.snd_to b) ≫ I.snd b

@[simp, reassoc]
theorem fst_pi_map_π b : I.fst_pi_map ≫ pi.π I.right b = pi.π I.left _ ≫ I.fst b :=
  by 
    simp [fst_pi_map]

@[simp, reassoc]
theorem snd_pi_map_π b : I.snd_pi_map ≫ pi.π I.right b = pi.π I.left _ ≫ I.snd b :=
  by 
    simp [snd_pi_map]

/--
Taking the multiequalizer over the multicospan index is equivalent to taking the equalizer over
the two morphsims `∏ I.left ⇉ ∏ I.right`. This is the diagram of the latter.
-/
@[simps]
protected noncomputable def parallel_pair_diagram :=
  parallel_pair I.fst_pi_map I.snd_pi_map

end MulticospanIndex

namespace MultispanIndex

variable {C : Type u} [category.{v} C] (I : multispan_index C)

/-- The multispan associated to `I : multispan_index`. -/
def multispan : walking_multispan I.fst_from I.snd_from ⥤ C :=
  { obj :=
      fun x =>
        match x with 
        | walking_multispan.left a => I.left a
        | walking_multispan.right b => I.right b,
    map :=
      fun x y f =>
        match x, y, f with 
        | _, _, walking_multispan.hom.id x => 𝟙 _
        | _, _, walking_multispan.hom.fst b => I.fst _
        | _, _, walking_multispan.hom.snd b => I.snd _,
    map_id' :=
      by 
        rintro (_ | _)
        tidy,
    map_comp' :=
      by 
        rintro (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _)
        tidy }

@[simp]
theorem multispan_obj_left a : I.multispan.obj (walking_multispan.left a) = I.left a :=
  rfl

@[simp]
theorem multispan_obj_right b : I.multispan.obj (walking_multispan.right b) = I.right b :=
  rfl

@[simp]
theorem multispan_map_fst a : I.multispan.map (walking_multispan.hom.fst a) = I.fst a :=
  rfl

@[simp]
theorem multispan_map_snd a : I.multispan.map (walking_multispan.hom.snd a) = I.snd a :=
  rfl

variable [has_coproduct I.left] [has_coproduct I.right]

/-- The induced map `∐ I.left ⟶ ∐ I.right` via `I.fst`. -/
noncomputable def fst_sigma_map : ∐ I.left ⟶ ∐ I.right :=
  sigma.desc fun b => I.fst b ≫ sigma.ι _ (I.fst_from b)

/-- The induced map `∐ I.left ⟶ ∐ I.right` via `I.snd`. -/
noncomputable def snd_sigma_map : ∐ I.left ⟶ ∐ I.right :=
  sigma.desc fun b => I.snd b ≫ sigma.ι _ (I.snd_from b)

@[simp, reassoc]
theorem ι_fst_sigma_map b : sigma.ι I.left b ≫ I.fst_sigma_map = I.fst b ≫ sigma.ι I.right _ :=
  by 
    simp [fst_sigma_map]

@[simp, reassoc]
theorem ι_snd_sigma_map b : sigma.ι I.left b ≫ I.snd_sigma_map = I.snd b ≫ sigma.ι I.right _ :=
  by 
    simp [snd_sigma_map]

/--
Taking the multicoequalizer over the multispan index is equivalent to taking the coequalizer over
the two morphsims `∐ I.left ⇉ ∐ I.right`. This is the diagram of the latter.
-/
protected noncomputable abbrev parallel_pair_diagram :=
  parallel_pair I.fst_sigma_map I.snd_sigma_map

end MultispanIndex

variable {C : Type u} [category.{v} C]

/-- A multifork is a cone over a multicospan. -/
@[nolint has_inhabited_instance]
abbrev multifork (I : multicospan_index C) :=
  cone I.multicospan

/-- A multicofork is a cocone over a multispan. -/
@[nolint has_inhabited_instance]
abbrev multicofork (I : multispan_index C) :=
  cocone I.multispan

namespace Multifork

variable {I : multicospan_index C} (K : multifork I)

/-- The maps from the cone point of a multifork to the objects on the left. -/
def ι (a : I.L) : K.X ⟶ I.left a :=
  K.π.app (walking_multicospan.left _)

@[simp]
theorem ι_eq_app_left a : K.ι a = K.π.app (walking_multicospan.left _) :=
  rfl

@[simp]
theorem app_left_fst b :
  K.π.app (walking_multicospan.left (I.fst_to b)) ≫ I.fst b = K.π.app (walking_multicospan.right b) :=
  by 
    rw [←K.w (walking_multicospan.hom.fst b)]
    rfl

@[simp]
theorem app_left_snd b :
  K.π.app (walking_multicospan.left (I.snd_to b)) ≫ I.snd b = K.π.app (walking_multicospan.right b) :=
  by 
    rw [←K.w (walking_multicospan.hom.snd b)]
    rfl

/-- Construct a multifork using a collection `ι` of morphisms. -/
@[simps]
def of_ι (I : multicospan_index C) (P : C) (ι : ∀ a, P ⟶ I.left a)
  (w : ∀ b, ι (I.fst_to b) ≫ I.fst b = ι (I.snd_to b) ≫ I.snd b) : multifork I :=
  { x := P,
    π :=
      { app :=
          fun x =>
            match x with 
            | walking_multicospan.left a => ι _
            | walking_multicospan.right b => ι (I.fst_to b) ≫ I.fst b,
        naturality' :=
          by 
            rintro (_ | _) (_ | _) (_ | _ | _)
            any_goals 
              symm 
              dsimp 
              rw [category.id_comp]
              apply category.comp_id
            ·
              dsimp 
              rw [category.id_comp]
              rfl
            ·
              dsimp 
              rw [category.id_comp]
              apply w } }

@[reassoc]
theorem condition b : K.ι (I.fst_to b) ≫ I.fst b = K.ι (I.snd_to b) ≫ I.snd b :=
  by 
    simp 

/-- This definition provides a convenient way to show that a multifork is a limit. -/
@[simps]
def is_limit.mk (lift : ∀ E : multifork I, E.X ⟶ K.X) (fac : ∀ E : multifork I i : I.L, lift E ≫ K.ι i = E.ι i)
  (uniq : ∀ E : multifork I m : E.X ⟶ K.X, (∀ i : I.L, m ≫ K.ι i = E.ι i) → m = lift E) : is_limit K :=
  { lift,
    fac' :=
      by 
        rintro E (a | b)
        ·
          apply fac
        ·
          rw [←E.w (walking_multicospan.hom.fst b), ←K.w (walking_multicospan.hom.fst b), ←category.assoc]
          congr 1
          apply fac,
    uniq' :=
      by 
        rintro E m hm 
        apply uniq 
        intro i 
        apply hm }

variable [has_product I.left] [has_product I.right]

@[simp, reassoc]
theorem pi_condition : pi.lift K.ι ≫ I.fst_pi_map = pi.lift K.ι ≫ I.snd_pi_map :=
  by 
    ext 
    simp 

/-- Given a multifork, we may obtain a fork over `∏ I.left ⇉ ∏ I.right`. -/
@[simps x]
noncomputable def to_pi_fork (K : multifork I) : fork I.fst_pi_map I.snd_pi_map :=
  { x := K.X,
    π :=
      { app :=
          fun x =>
            match x with 
            | walking_parallel_pair.zero => pi.lift K.ι
            | walking_parallel_pair.one => pi.lift K.ι ≫ I.fst_pi_map,
        naturality' :=
          by 
            rintro (_ | _) (_ | _) (_ | _ | _)
            any_goals 
              symm 
              dsimp 
              rw [category.id_comp]
              apply category.comp_id 
            all_goals 
              change 𝟙 _ ≫ _ ≫ _ = pi.lift _ ≫ _ 
              simp  } }

@[simp]
theorem to_pi_fork_π_app_zero : K.to_pi_fork.π.app walking_parallel_pair.zero = pi.lift K.ι :=
  rfl

@[simp]
theorem to_pi_fork_π_app_one : K.to_pi_fork.π.app walking_parallel_pair.one = pi.lift K.ι ≫ I.fst_pi_map :=
  rfl

variable (I)

/-- Given a fork over `∏ I.left ⇉ ∏ I.right`, we may obtain a multifork. -/
@[simps x]
noncomputable def of_pi_fork (c : fork I.fst_pi_map I.snd_pi_map) : multifork I :=
  { x := c.X,
    π :=
      { app :=
          fun x =>
            match x with 
            | walking_multicospan.left a => c.ι ≫ pi.π _ _
            | walking_multicospan.right b => c.ι ≫ I.fst_pi_map ≫ pi.π _ _,
        naturality' :=
          by 
            rintro (_ | _) (_ | _) (_ | _ | _)
            any_goals 
              symm 
              dsimp 
              rw [category.id_comp]
              apply category.comp_id
            ·
              change 𝟙 _ ≫ _ ≫ _ = (_ ≫ _) ≫ _ 
              simp 
            ·
              change 𝟙 _ ≫ _ ≫ _ = (_ ≫ _) ≫ _ 
              rw [c.condition_assoc]
              simp  } }

@[simp]
theorem of_pi_fork_π_app_left (c : fork I.fst_pi_map I.snd_pi_map) a :
  (of_pi_fork I c).π.app (walking_multicospan.left a) = c.ι ≫ pi.π _ _ :=
  rfl

@[simp]
theorem of_pi_fork_π_app_right (c : fork I.fst_pi_map I.snd_pi_map) a :
  (of_pi_fork I c).π.app (walking_multicospan.right a) = c.ι ≫ I.fst_pi_map ≫ pi.π _ _ :=
  rfl

end Multifork

namespace MulticospanIndex

variable (I : multicospan_index C) [has_product I.left] [has_product I.right]

attribute [local tidy] tactic.case_bash

/-- `multifork.to_pi_fork` is functorial. -/
@[simps]
noncomputable def to_pi_fork_functor : multifork I ⥤ fork I.fst_pi_map I.snd_pi_map :=
  { obj := multifork.to_pi_fork, map := fun K₁ K₂ f => { Hom := f.hom } }

/-- `multifork.of_pi_fork` is functorial. -/
@[simps]
noncomputable def of_pi_fork_functor : fork I.fst_pi_map I.snd_pi_map ⥤ multifork I :=
  { obj := multifork.of_pi_fork I,
    map :=
      fun K₁ K₂ f =>
        { Hom := f.hom,
          w' :=
            by 
              rintro (_ | _) <;> simp  } }

/--
The category of multiforks is equivalent to the category of forks over `∏ I.left ⇉ ∏ I.right`.
It then follows from `category_theory.is_limit_of_preserves_cone_terminal` (or `reflects`) that it
preserves and reflects limit cones.
-/
@[simps]
noncomputable def multifork_equiv_pi_fork : multifork I ≌ fork I.fst_pi_map I.snd_pi_map :=
  { Functor := to_pi_fork_functor I, inverse := of_pi_fork_functor I,
    unitIso :=
      nat_iso.of_components
        (fun K =>
          cones.ext (iso.refl _)
            (by 
              rintro (_ | _) <;> dsimp <;> simp ))
        fun K₁ K₂ f =>
          by 
            ext 
            simp ,
    counitIso :=
      nat_iso.of_components
        (fun K =>
          fork.ext (iso.refl _)
            (by 
              ext 
              dsimp 
              simp ))
        fun K₁ K₂ f =>
          by 
            ext 
            simp  }

end MulticospanIndex

namespace Multicofork

variable {I : multispan_index C} (K : multicofork I)

/-- The maps to the cocone point of a multicofork from the objects on the right. -/
def π (b : I.R) : I.right b ⟶ K.X :=
  K.ι.app (walking_multispan.right _)

@[simp]
theorem π_eq_app_right b : K.π b = K.ι.app (walking_multispan.right _) :=
  rfl

@[simp]
theorem fst_app_right a :
  I.fst a ≫ K.ι.app (walking_multispan.right (I.fst_from a)) = K.ι.app (walking_multispan.left a) :=
  by 
    rw [←K.w (walking_multispan.hom.fst a)]
    rfl

@[simp]
theorem snd_app_right a :
  I.snd a ≫ K.ι.app (walking_multispan.right (I.snd_from a)) = K.ι.app (walking_multispan.left a) :=
  by 
    rw [←K.w (walking_multispan.hom.snd a)]
    rfl

/-- Construct a multicofork using a collection `π` of morphisms. -/
@[simps]
def of_π (I : multispan_index C) (P : C) (π : ∀ b, I.right b ⟶ P)
  (w : ∀ a, I.fst a ≫ π (I.fst_from a) = I.snd a ≫ π (I.snd_from a)) : multicofork I :=
  { x := P,
    ι :=
      { app :=
          fun x =>
            match x with 
            | walking_multispan.left a => I.fst a ≫ π _
            | walking_multispan.right b => π _,
        naturality' :=
          by 
            rintro (_ | _) (_ | _) (_ | _ | _)
            any_goals 
              dsimp 
              rw [category.comp_id]
              apply category.id_comp
            ·
              dsimp 
              rw [category.comp_id]
              rfl
            ·
              dsimp 
              rw [category.comp_id]
              apply (w _).symm } }

@[reassoc]
theorem condition a : I.fst a ≫ K.π (I.fst_from a) = I.snd a ≫ K.π (I.snd_from a) :=
  by 
    simp 

/-- This definition provides a convenient way to show that a multicofork is a colimit. -/
@[simps]
def is_colimit.mk (desc : ∀ E : multicofork I, K.X ⟶ E.X) (fac : ∀ E : multicofork I i : I.R, K.π i ≫ desc E = E.π i)
  (uniq : ∀ E : multicofork I m : K.X ⟶ E.X, (∀ i : I.R, K.π i ≫ m = E.π i) → m = desc E) : is_colimit K :=
  { desc,
    fac' :=
      by 
        rintro S (a | b)
        ·
          rw [←K.w (walking_multispan.hom.fst a), ←S.w (walking_multispan.hom.fst a), category.assoc]
          congr 1
          apply fac
        ·
          apply fac,
    uniq' :=
      by 
        intro S m hm 
        apply uniq 
        intro i 
        apply hm }

variable [has_coproduct I.left] [has_coproduct I.right]

@[simp, reassoc]
theorem sigma_condition : I.fst_sigma_map ≫ sigma.desc K.π = I.snd_sigma_map ≫ sigma.desc K.π :=
  by 
    ext 
    simp 

/-- Given a multicofork, we may obtain a cofork over `∐ I.left ⇉ ∐ I.right`. -/
@[simps x]
noncomputable def to_sigma_cofork (K : multicofork I) : cofork I.fst_sigma_map I.snd_sigma_map :=
  { x := K.X,
    ι :=
      { app :=
          fun x =>
            match x with 
            | walking_parallel_pair.zero => I.fst_sigma_map ≫ sigma.desc K.π
            | walking_parallel_pair.one => sigma.desc K.π,
        naturality' :=
          by 
            rintro (_ | _) (_ | _) (_ | _ | _)
            any_goals 
              dsimp 
              rw [category.comp_id]
              apply category.id_comp 
            all_goals 
              change _ ≫ sigma.desc _ = (_ ≫ _) ≫ 𝟙 _ 
              simp  } }

@[simp]
theorem to_sigma_cofork_ι_app_zero :
  K.to_sigma_cofork.ι.app walking_parallel_pair.zero = I.fst_sigma_map ≫ sigma.desc K.π :=
  rfl

@[simp]
theorem to_sigma_cofork_ι_app_one : K.to_sigma_cofork.ι.app walking_parallel_pair.one = sigma.desc K.π :=
  rfl

variable (I)

/-- Given a cofork over `∐ I.left ⇉ ∐ I.right`, we may obtain a multicofork. -/
@[simps x]
noncomputable def of_sigma_cofork (c : cofork I.fst_sigma_map I.snd_sigma_map) : multicofork I :=
  { x := c.X,
    ι :=
      { app :=
          fun x =>
            match x with 
            | walking_multispan.left a => (sigma.ι I.left a : _) ≫ I.fst_sigma_map ≫ c.π
            | walking_multispan.right b => (sigma.ι I.right b : _) ≫ c.π,
        naturality' :=
          by 
            rintro (_ | _) (_ | _) (_ | _ | _)
            any_goals 
              dsimp 
              rw [category.comp_id]
              apply category.id_comp
            ·
              change _ ≫ _ ≫ _ = (_ ≫ _) ≫ _ 
              dsimp 
              simp [←cofork.left_app_one, -cofork.left_app_one]
            ·
              change _ ≫ _ ≫ _ = (_ ≫ _) ≫ 𝟙 _ 
              rw [c.condition]
              dsimp 
              simp [←cofork.right_app_one, -cofork.right_app_one] } }

@[simp]
theorem of_sigma_cofork_ι_app_left (c : cofork I.fst_sigma_map I.snd_sigma_map) a :
  (of_sigma_cofork I c).ι.app (walking_multispan.left a) = (sigma.ι I.left a : _) ≫ I.fst_sigma_map ≫ c.π :=
  rfl

@[simp]
theorem of_sigma_cofork_ι_app_right (c : cofork I.fst_sigma_map I.snd_sigma_map) b :
  (of_sigma_cofork I c).ι.app (walking_multispan.right b) = (sigma.ι I.right b : _) ≫ c.π :=
  rfl

end Multicofork

namespace MultispanIndex

variable (I : multispan_index C) [has_coproduct I.left] [has_coproduct I.right]

attribute [local tidy] tactic.case_bash

/-- `multicofork.to_sigma_cofork` is functorial. -/
@[simps]
noncomputable def to_sigma_cofork_functor : multicofork I ⥤ cofork I.fst_sigma_map I.snd_sigma_map :=
  { obj := multicofork.to_sigma_cofork, map := fun K₁ K₂ f => { Hom := f.hom } }

/-- `multicofork.of_sigma_cofork` is functorial. -/
@[simps]
noncomputable def of_sigma_cofork_functor : cofork I.fst_sigma_map I.snd_sigma_map ⥤ multicofork I :=
  { obj := multicofork.of_sigma_cofork I,
    map :=
      fun K₁ K₂ f =>
        { Hom := f.hom,
          w' :=
            by 
              rintro (_ | _) <;> simp  } }

/--
The category of multicoforks is equivalent to the category of coforks over `∐ I.left ⇉ ∐ I.right`.
It then follows from `category_theory.is_colimit_of_preserves_cocone_initial` (or `reflects`) that
it preserves and reflects colimit cocones.
-/
@[simps]
noncomputable def multicofork_equiv_sigma_cofork : multicofork I ≌ cofork I.fst_sigma_map I.snd_sigma_map :=
  { Functor := to_sigma_cofork_functor I, inverse := of_sigma_cofork_functor I,
    unitIso :=
      nat_iso.of_components
        (fun K =>
          cocones.ext (iso.refl _)
            (by 
              rintro (_ | _) <;> dsimp <;> simp ))
        fun K₁ K₂ f =>
          by 
            ext 
            simp ,
    counitIso :=
      nat_iso.of_components
        (fun K =>
          cofork.ext (iso.refl _)
            (by 
              ext 
              dsimp 
              simp ))
        fun K₁ K₂ f =>
          by 
            ext 
            dsimp 
            simp  }

end MultispanIndex

/-- For `I : multicospan_index C`, we say that it has a multiequalizer if the associated
  multicospan has a limit. -/
abbrev has_multiequalizer (I : multicospan_index C) :=
  has_limit I.multicospan

noncomputable theory

/-- The multiequalizer of `I : multicospan_index C`. -/
abbrev multiequalizer (I : multicospan_index C) [has_multiequalizer I] : C :=
  limit I.multicospan

/-- For `I : multispan_index C`, we say that it has a multicoequalizer if
  the associated multicospan has a limit. -/
abbrev has_multicoequalizer (I : multispan_index C) :=
  has_colimit I.multispan

/-- The multiecoqualizer of `I : multispan_index C`. -/
abbrev multicoequalizer (I : multispan_index C) [has_multicoequalizer I] : C :=
  colimit I.multispan

namespace Multiequalizer

variable (I : multicospan_index C) [has_multiequalizer I]

/-- The canonical map from the multiequalizer to the objects on the left. -/
abbrev ι (a : I.L) : multiequalizer I ⟶ I.left a :=
  limit.π _ (walking_multicospan.left a)

/-- The multifork associated to the multiequalizer. -/
abbrev multifork : multifork I :=
  limit.cone _

@[simp]
theorem multifork_ι a : (multiequalizer.multifork I).ι a = multiequalizer.ι I a :=
  rfl

@[simp]
theorem multifork_π_app_left a :
  (multiequalizer.multifork I).π.app (walking_multicospan.left a) = multiequalizer.ι I a :=
  rfl

@[reassoc]
theorem condition b : multiequalizer.ι I (I.fst_to b) ≫ I.fst b = multiequalizer.ι I (I.snd_to b) ≫ I.snd b :=
  multifork.condition _ _

/-- Construct a morphism to the multiequalizer from its universal property. -/
abbrev lift (W : C) (k : ∀ a, W ⟶ I.left a) (h : ∀ b, k (I.fst_to b) ≫ I.fst b = k (I.snd_to b) ≫ I.snd b) :
  W ⟶ multiequalizer I :=
  limit.lift _ (multifork.of_ι I _ k h)

@[simp, reassoc]
theorem lift_ι (W : C) (k : ∀ a, W ⟶ I.left a) (h : ∀ b, k (I.fst_to b) ≫ I.fst b = k (I.snd_to b) ≫ I.snd b) a :
  multiequalizer.lift I _ k h ≫ multiequalizer.ι I a = k _ :=
  limit.lift_π _ _

@[ext]
theorem hom_ext {W : C} (i j : W ⟶ multiequalizer I) (h : ∀ a, i ≫ multiequalizer.ι I a = j ≫ multiequalizer.ι I a) :
  i = j :=
  limit.hom_ext
    (by 
      rintro (a | b)
      ·
        apply h 
      simpRw [←limit.w I.multicospan (walking_multicospan.hom.fst b), ←category.assoc, h])

variable [has_product I.left] [has_product I.right] [has_equalizer I.fst_pi_map I.snd_pi_map]

/-- The multiequalizer is isomorphic to the equalizer of `∏ I.left ⇉ ∏ I.right`. -/
def iso_equalizer : multiequalizer I ≅ equalizer I.fst_pi_map I.snd_pi_map :=
  limit.iso_limit_cone ⟨_, is_limit.of_preserves_cone_terminal I.multifork_equiv_pi_fork.inverse (limit.is_limit _)⟩

/-- The canonical injection `multiequalizer I ⟶ ∏ I.left`. -/
def ι_pi : multiequalizer I ⟶ ∏ I.left :=
  (iso_equalizer I).Hom ≫ equalizer.ι I.fst_pi_map I.snd_pi_map

@[simp, reassoc]
theorem ι_pi_π a : ι_pi I ≫ pi.π I.left a = ι I a :=
  by 
    rw [ι_pi, category.assoc, ←iso.eq_inv_comp, iso_equalizer]
    simpa

instance : mono (ι_pi I) :=
  @mono_comp _ _ _ _ equalizer.ι_mono

end Multiequalizer

namespace Multicoequalizer

variable (I : multispan_index C) [has_multicoequalizer I]

/-- The canonical map from the multiequalizer to the objects on the left. -/
abbrev π (b : I.R) : I.right b ⟶ multicoequalizer I :=
  colimit.ι I.multispan (walking_multispan.right _)

/-- The multicofork associated to the multicoequalizer. -/
abbrev multicofork : multicofork I :=
  colimit.cocone _

@[simp]
theorem multicofork_π b : (multicoequalizer.multicofork I).π b = multicoequalizer.π I b :=
  rfl

@[simp]
theorem multicofork_ι_app_right b :
  (multicoequalizer.multicofork I).ι.app (walking_multispan.right b) = multicoequalizer.π I b :=
  rfl

@[reassoc]
theorem condition a : I.fst a ≫ multicoequalizer.π I (I.fst_from a) = I.snd a ≫ multicoequalizer.π I (I.snd_from a) :=
  multicofork.condition _ _

/-- Construct a morphism from the multicoequalizer from its universal property. -/
abbrev desc (W : C) (k : ∀ b, I.right b ⟶ W) (h : ∀ a, I.fst a ≫ k (I.fst_from a) = I.snd a ≫ k (I.snd_from a)) :
  multicoequalizer I ⟶ W :=
  colimit.desc _ (multicofork.of_π I _ k h)

@[simp, reassoc]
theorem π_desc (W : C) (k : ∀ b, I.right b ⟶ W) (h : ∀ a, I.fst a ≫ k (I.fst_from a) = I.snd a ≫ k (I.snd_from a)) b :
  multicoequalizer.π I b ≫ multicoequalizer.desc I _ k h = k _ :=
  colimit.ι_desc _ _

@[ext]
theorem hom_ext {W : C} (i j : multicoequalizer I ⟶ W)
  (h : ∀ b, multicoequalizer.π I b ≫ i = multicoequalizer.π I b ≫ j) : i = j :=
  colimit.hom_ext
    (by 
      rintro (a | b)
      ·
        simpRw [←colimit.w I.multispan (walking_multispan.hom.fst a), category.assoc, h]
      ·
        apply h)

variable [has_coproduct I.left] [has_coproduct I.right]

variable [has_coequalizer I.fst_sigma_map I.snd_sigma_map]

/-- The multicoequalizer is isomorphic to the coequalizer of `∐ I.left ⇉ ∐ I.right`. -/
def iso_coequalizer : multicoequalizer I ≅ coequalizer I.fst_sigma_map I.snd_sigma_map :=
  colimit.iso_colimit_cocone
    ⟨_, is_colimit.of_preserves_cocone_initial I.multicofork_equiv_sigma_cofork.inverse (colimit.is_colimit _)⟩

/-- The canonical projection `∐ I.right ⟶ multicoequalizer I`. -/
def sigma_π : ∐ I.right ⟶ multicoequalizer I :=
  coequalizer.π I.fst_sigma_map I.snd_sigma_map ≫ (iso_coequalizer I).inv

@[simp, reassoc]
theorem ι_sigma_π b : sigma.ι I.right b ≫ sigma_π I = π I b :=
  by 
    rw [sigma_π, ←category.assoc, iso.comp_inv_eq, iso_coequalizer]
    simpa

instance : epi (sigma_π I) :=
  @epi_comp _ _ coequalizer.π_epi _ _

end Multicoequalizer

end CategoryTheory.Limits

