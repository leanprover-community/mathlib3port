import Mathbin.CategoryTheory.EpiMono 
import Mathbin.CategoryTheory.Limits.HasLimits

/-!
# Equalizers and coequalizers

This file defines (co)equalizers as special cases of (co)limits.

An equalizer is the categorical generalization of the subobject {a ∈ A | f(a) = g(a)} known
from abelian groups or modules. It is a limit cone over the diagram formed by `f` and `g`.

A coequalizer is the dual concept.

## Main definitions

* `walking_parallel_pair` is the indexing category used for (co)equalizer_diagrams
* `parallel_pair` is a functor from `walking_parallel_pair` to our category `C`.
* a `fork` is a cone over a parallel pair.
  * there is really only one interesting morphism in a fork: the arrow from the vertex of the fork
    to the domain of f and g. It is called `fork.ι`.
* an `equalizer` is now just a `limit (parallel_pair f g)`

Each of these has a dual.

## Main statements

* `equalizer.ι_mono` states that every equalizer map is a monomorphism
* `is_iso_limit_cone_parallel_pair_of_self` states that the identity on the domain of `f` is an
  equalizer of `f` and `f`.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/


noncomputable theory

open CategoryTheory

namespace CategoryTheory.Limits

attribute [local tidy] tactic.case_bash

universe v u u₂

-- error in CategoryTheory.Limits.Shapes.Equalizers: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler decidable_eq
/-- The type of objects for the diagram indexing a (co)equalizer. -/
@[derive #[expr decidable_eq], derive #[expr inhabited]]
inductive walking_parallel_pair : Type v
| zero
| one

open WalkingParallelPair

-- error in CategoryTheory.Limits.Shapes.Equalizers: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler decidable_eq
/-- The type family of morphisms for the diagram indexing a (co)equalizer. -/
@[derive #[expr decidable_eq]]
inductive walking_parallel_pair_hom : walking_parallel_pair → walking_parallel_pair → Type v
| left : walking_parallel_pair_hom zero one
| right : walking_parallel_pair_hom zero one
| id : ∀ X : walking_parallel_pair.{v}, walking_parallel_pair_hom X X

/-- Satisfying the inhabited linter -/
instance  : Inhabited (walking_parallel_pair_hom zero one) :=
  { default := walking_parallel_pair_hom.left }

open WalkingParallelPairHom

/-- Composition of morphisms in the indexing diagram for (co)equalizers. -/
def walking_parallel_pair_hom.comp :
  ∀ X Y Z : walking_parallel_pair f : walking_parallel_pair_hom X Y g : walking_parallel_pair_hom Y Z,
    walking_parallel_pair_hom X Z
| _, _, _, id _, h => h
| _, _, _, left, id one => left
| _, _, _, right, id one => right

instance walking_parallel_pair_hom_category : small_category walking_parallel_pair :=
  { Hom := walking_parallel_pair_hom, id := walking_parallel_pair_hom.id, comp := walking_parallel_pair_hom.comp }

@[simp]
theorem walking_parallel_pair_hom_id (X : walking_parallel_pair) : walking_parallel_pair_hom.id X = 𝟙 X :=
  rfl

variable{C : Type u}[category.{v} C]

variable{X Y : C}

/-- `parallel_pair f g` is the diagram in `C` consisting of the two morphisms `f` and `g` with
    common domain and codomain. -/
def parallel_pair (f g : X ⟶ Y) : walking_parallel_pair.{v} ⥤ C :=
  { obj :=
      fun x =>
        match x with 
        | zero => X
        | one => Y,
    map :=
      fun x y h =>
        match x, y, h with 
        | _, _, id _ => 𝟙 _
        | _, _, left => f
        | _, _, right => g,
    map_comp' :=
      by 
        rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) ⟨⟩ ⟨⟩ <;>
          ·
            unfoldAux 
            simp  <;> rfl }

@[simp]
theorem parallel_pair_obj_zero (f g : X ⟶ Y) : (parallel_pair f g).obj zero = X :=
  rfl

@[simp]
theorem parallel_pair_obj_one (f g : X ⟶ Y) : (parallel_pair f g).obj one = Y :=
  rfl

@[simp]
theorem parallel_pair_map_left (f g : X ⟶ Y) : (parallel_pair f g).map left = f :=
  rfl

@[simp]
theorem parallel_pair_map_right (f g : X ⟶ Y) : (parallel_pair f g).map right = g :=
  rfl

@[simp]
theorem parallel_pair_functor_obj {F : walking_parallel_pair ⥤ C} (j : walking_parallel_pair) :
  (parallel_pair (F.map left) (F.map right)).obj j = F.obj j :=
  by 
    cases j <;> rfl

/-- Every functor indexing a (co)equalizer is naturally isomorphic (actually, equal) to a
    `parallel_pair` -/
@[simps]
def diagram_iso_parallel_pair (F : walking_parallel_pair ⥤ C) : F ≅ parallel_pair (F.map left) (F.map right) :=
  (nat_iso.of_components
      fun j =>
        eq_to_iso$
          by 
            cases j <;> tidy)$
    by 
      tidy

/-- Construct a morphism between parallel pairs. -/
def parallel_pair_hom {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X') (q : Y ⟶ Y') (wf : f ≫ q = p ≫ f')
  (wg : g ≫ q = p ≫ g') : parallel_pair f g ⟶ parallel_pair f' g' :=
  { app :=
      fun j =>
        match j with 
        | zero => p
        | one => q,
    naturality' :=
      by 
        rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) ⟨⟩ <;>
          ·
            unfoldAux 
            simp [wf, wg] }

@[simp]
theorem parallel_pair_hom_app_zero {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X') (q : Y ⟶ Y')
  (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') : (parallel_pair_hom f g f' g' p q wf wg).app zero = p :=
  rfl

@[simp]
theorem parallel_pair_hom_app_one {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X') (q : Y ⟶ Y')
  (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') : (parallel_pair_hom f g f' g' p q wf wg).app one = q :=
  rfl

/-- A fork on `f` and `g` is just a `cone (parallel_pair f g)`. -/
abbrev fork (f g : X ⟶ Y) :=
  cone (parallel_pair f g)

/-- A cofork on `f` and `g` is just a `cocone (parallel_pair f g)`. -/
abbrev cofork (f g : X ⟶ Y) :=
  cocone (parallel_pair f g)

variable{f g : X ⟶ Y}

/-- A fork `t` on the parallel pair `f g : X ⟶ Y` consists of two morphisms `t.π.app zero : t.X ⟶ X`
    and `t.π.app one : t.X ⟶ Y`. Of these, only the first one is interesting, and we give it the
    shorter name `fork.ι t`. -/
abbrev fork.ι (t : fork f g) :=
  t.π.app zero

/-- A cofork `t` on the parallel_pair `f g : X ⟶ Y` consists of two morphisms
    `t.ι.app zero : X ⟶ t.X` and `t.ι.app one : Y ⟶ t.X`. Of these, only the second one is
    interesting, and we give it the shorter name `cofork.π t`. -/
abbrev cofork.π (t : cofork f g) :=
  t.ι.app one

@[simp]
theorem fork.ι_eq_app_zero (t : fork f g) : t.ι = t.π.app zero :=
  rfl

@[simp]
theorem cofork.π_eq_app_one (t : cofork f g) : t.π = t.ι.app one :=
  rfl

@[simp, reassoc]
theorem fork.app_zero_left (s : fork f g) : s.π.app zero ≫ f = s.π.app one :=
  by 
    rw [←s.w left, parallel_pair_map_left]

@[simp, reassoc]
theorem fork.app_zero_right (s : fork f g) : s.π.app zero ≫ g = s.π.app one :=
  by 
    rw [←s.w right, parallel_pair_map_right]

@[simp, reassoc]
theorem cofork.left_app_one (s : cofork f g) : f ≫ s.ι.app one = s.ι.app zero :=
  by 
    rw [←s.w left, parallel_pair_map_left]

@[simp, reassoc]
theorem cofork.right_app_one (s : cofork f g) : g ≫ s.ι.app one = s.ι.app zero :=
  by 
    rw [←s.w right, parallel_pair_map_right]

/-- A fork on `f g : X ⟶ Y` is determined by the morphism `ι : P ⟶ X` satisfying `ι ≫ f = ι ≫ g`.
-/
@[simps]
def fork.of_ι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) : fork f g :=
  { x := P,
    π :=
      { app :=
          fun X =>
            by 
              cases X 
              exact ι 
              exact ι ≫ f,
        naturality' :=
          fun X Y f =>
            by 
              cases X <;> cases Y <;> cases f <;> dsimp <;> simp 
              ·
                dsimp 
                simp 
              ·
                exact w
              ·
                dsimp 
                simp  } }

/-- A cofork on `f g : X ⟶ Y` is determined by the morphism `π : Y ⟶ P` satisfying
    `f ≫ π = g ≫ π`. -/
@[simps]
def cofork.of_π {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) : cofork f g :=
  { x := P,
    ι :=
      { app := fun X => walking_parallel_pair.cases_on X (f ≫ π) π,
        naturality' :=
          fun i j f =>
            by 
              cases f <;> dsimp <;> simp [w] } }

theorem fork.ι_of_ι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) : (fork.of_ι ι w).ι = ι :=
  rfl

theorem cofork.π_of_π {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) : (cofork.of_π π w).π = π :=
  rfl

@[reassoc]
theorem fork.condition (t : fork f g) : t.ι ≫ f = t.ι ≫ g :=
  by 
    rw [t.app_zero_left, t.app_zero_right]

@[reassoc]
theorem cofork.condition (t : cofork f g) : f ≫ t.π = g ≫ t.π :=
  by 
    rw [t.left_app_one, t.right_app_one]

/-- To check whether two maps are equalized by both maps of a fork, it suffices to check it for the
    first map -/
theorem fork.equalizer_ext (s : fork f g) {W : C} {k l : W ⟶ s.X} (h : k ≫ fork.ι s = l ≫ fork.ι s) :
  ∀ j : walking_parallel_pair, k ≫ s.π.app j = l ≫ s.π.app j
| zero => h
| one =>
  by 
    rw [←fork.app_zero_left, reassoc_of h]

/-- To check whether two maps are coequalized by both maps of a cofork, it suffices to check it for
    the second map -/
theorem cofork.coequalizer_ext (s : cofork f g) {W : C} {k l : s.X ⟶ W} (h : cofork.π s ≫ k = cofork.π s ≫ l) :
  ∀ j : walking_parallel_pair, s.ι.app j ≫ k = s.ι.app j ≫ l
| zero =>
  by 
    simp only [←cofork.left_app_one, category.assoc, h]
| one => h

theorem fork.is_limit.hom_ext {s : fork f g} (hs : is_limit s) {W : C} {k l : W ⟶ s.X}
  (h : k ≫ fork.ι s = l ≫ fork.ι s) : k = l :=
  hs.hom_ext$ fork.equalizer_ext _ h

theorem cofork.is_colimit.hom_ext {s : cofork f g} (hs : is_colimit s) {W : C} {k l : s.X ⟶ W}
  (h : cofork.π s ≫ k = cofork.π s ≫ l) : k = l :=
  hs.hom_ext$ cofork.coequalizer_ext _ h

/-- If `s` is a limit fork over `f` and `g`, then a morphism `k : W ⟶ X` satisfying
    `k ≫ f = k ≫ g` induces a morphism `l : W ⟶ s.X` such that `l ≫ fork.ι s = k`. -/
def fork.is_limit.lift' {s : fork f g} (hs : is_limit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
  { l : W ⟶ s.X // l ≫ fork.ι s = k } :=
  ⟨hs.lift$ fork.of_ι _ h, hs.fac _ _⟩

/-- If `s` is a colimit cofork over `f` and `g`, then a morphism `k : Y ⟶ W` satisfying
    `f ≫ k = g ≫ k` induces a morphism `l : s.X ⟶ W` such that `cofork.π s ≫ l = k`. -/
def cofork.is_colimit.desc' {s : cofork f g} (hs : is_colimit s) {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) :
  { l : s.X ⟶ W // cofork.π s ≫ l = k } :=
  ⟨hs.desc$ cofork.of_π _ h, hs.fac _ _⟩

/-- This is a slightly more convenient method to verify that a fork is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def fork.is_limit.mk (t : fork f g) (lift : ∀ s : fork f g, s.X ⟶ t.X)
  (fac : ∀ s : fork f g, lift s ≫ fork.ι t = fork.ι s)
  (uniq : ∀ s : fork f g m : s.X ⟶ t.X w : ∀ j : walking_parallel_pair, m ≫ t.π.app j = s.π.app j, m = lift s) :
  is_limit t :=
  { lift,
    fac' :=
      fun s j =>
        walking_parallel_pair.cases_on j (fac s)$
          by 
            erw [←s.w left, ←t.w left, ←category.assoc, fac] <;> rfl,
    uniq' := uniq }

/-- This is another convenient method to verify that a fork is a limit cone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def fork.is_limit.mk' {X Y : C} {f g : X ⟶ Y} (t : fork f g)
  (create : ∀ s : fork f g, { l // l ≫ t.ι = s.ι ∧ ∀ {m}, m ≫ t.ι = s.ι → m = l }) : is_limit t :=
  fork.is_limit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s m w => (create s).2.2 (w zero)

/-- This is a slightly more convenient method to verify that a cofork is a colimit cocone. It
    only asks for a proof of facts that carry any mathematical content -/
def cofork.is_colimit.mk (t : cofork f g) (desc : ∀ s : cofork f g, t.X ⟶ s.X)
  (fac : ∀ s : cofork f g, cofork.π t ≫ desc s = cofork.π s)
  (uniq : ∀ s : cofork f g m : t.X ⟶ s.X w : ∀ j : walking_parallel_pair, t.ι.app j ≫ m = s.ι.app j, m = desc s) :
  is_colimit t :=
  { desc,
    fac' :=
      fun s j =>
        walking_parallel_pair.cases_on j
          (by 
            erw [←s.w left, ←t.w left, category.assoc, fac] <;> rfl)
          (fac s),
    uniq' := uniq }

/-- This is another convenient method to verify that a fork is a limit cone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def cofork.is_colimit.mk' {X Y : C} {f g : X ⟶ Y} (t : cofork f g)
  (create : ∀ s : cofork f g, { l : t.X ⟶ s.X // t.π ≫ l = s.π ∧ ∀ {m}, t.π ≫ m = s.π → m = l }) : is_colimit t :=
  cofork.is_colimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s m w => (create s).2.2 (w one)

/--
Given a limit cone for the pair `f g : X ⟶ Y`, for any `Z`, morphisms from `Z` to its point are in
bijection with morphisms `h : Z ⟶ X` such that `h ≫ f = h ≫ g`.
Further, this bijection is natural in `Z`: see `fork.is_limit.hom_iso_natural`.
This is a special case of `is_limit.hom_iso'`, often useful to construct adjunctions.
-/
@[simps]
def fork.is_limit.hom_iso {X Y : C} {f g : X ⟶ Y} {t : fork f g} (ht : is_limit t) (Z : C) :
  (Z ⟶ t.X) ≃ { h : Z ⟶ X // h ≫ f = h ≫ g } :=
  { toFun :=
      fun k =>
        ⟨k ≫ t.ι,
          by 
            simp ⟩,
    invFun := fun h => (fork.is_limit.lift' ht _ h.prop).1,
    left_inv := fun k => fork.is_limit.hom_ext ht (fork.is_limit.lift' _ _ _).Prop,
    right_inv := fun h => Subtype.ext (fork.is_limit.lift' ht _ _).Prop }

/-- The bijection of `fork.is_limit.hom_iso` is natural in `Z`. -/
theorem fork.is_limit.hom_iso_natural {X Y : C} {f g : X ⟶ Y} {t : fork f g} (ht : is_limit t) {Z Z' : C} (q : Z' ⟶ Z)
  (k : Z ⟶ t.X) : (fork.is_limit.hom_iso ht _ (q ≫ k) : Z' ⟶ X) = q ≫ (fork.is_limit.hom_iso ht _ k : Z ⟶ X) :=
  category.assoc _ _ _

/--
Given a colimit cocone for the pair `f g : X ⟶ Y`, for any `Z`, morphisms from the cocone point
to `Z` are in bijection with morphisms `h : Y ⟶ Z` such that `f ≫ h = g ≫ h`.
Further, this bijection is natural in `Z`: see `cofork.is_colimit.hom_iso_natural`.
This is a special case of `is_colimit.hom_iso'`, often useful to construct adjunctions.
-/
@[simps]
def cofork.is_colimit.hom_iso {X Y : C} {f g : X ⟶ Y} {t : cofork f g} (ht : is_colimit t) (Z : C) :
  (t.X ⟶ Z) ≃ { h : Y ⟶ Z // f ≫ h = g ≫ h } :=
  { toFun :=
      fun k =>
        ⟨t.π ≫ k,
          by 
            simp ⟩,
    invFun := fun h => (cofork.is_colimit.desc' ht _ h.prop).1,
    left_inv := fun k => cofork.is_colimit.hom_ext ht (cofork.is_colimit.desc' _ _ _).Prop,
    right_inv := fun h => Subtype.ext (cofork.is_colimit.desc' ht _ _).Prop }

/-- The bijection of `cofork.is_colimit.hom_iso` is natural in `Z`. -/
theorem cofork.is_colimit.hom_iso_natural {X Y : C} {f g : X ⟶ Y} {t : cofork f g} {Z Z' : C} (q : Z ⟶ Z')
  (ht : is_colimit t) (k : t.X ⟶ Z) :
  (cofork.is_colimit.hom_iso ht _ (k ≫ q) : Y ⟶ Z') = (cofork.is_colimit.hom_iso ht _ k : Y ⟶ Z) ≫ q :=
  (category.assoc _ _ _).symm

/-- This is a helper construction that can be useful when verifying that a category has all
    equalizers. Given `F : walking_parallel_pair ⥤ C`, which is really the same as
    `parallel_pair (F.map left) (F.map right)`, and a fork on `F.map left` and `F.map right`,
    we get a cone on `F`.

    If you're thinking about using this, have a look at `has_equalizers_of_has_limit_parallel_pair`,
    which you may find to be an easier way of achieving your goal. -/
def cone.of_fork {F : walking_parallel_pair ⥤ C} (t : fork (F.map left) (F.map right)) : cone F :=
  { x := t.X,
    π :=
      { app :=
          fun X =>
            t.π.app X ≫
              eq_to_hom
                (by 
                  tidy),
        naturality' :=
          fun j j' g =>
            by 
              cases j <;> cases j' <;> cases g <;> dsimp <;> simp  } }

/-- This is a helper construction that can be useful when verifying that a category has all
    coequalizers. Given `F : walking_parallel_pair ⥤ C`, which is really the same as
    `parallel_pair (F.map left) (F.map right)`, and a cofork on `F.map left` and `F.map right`,
    we get a cocone on `F`.

    If you're thinking about using this, have a look at
    `has_coequalizers_of_has_colimit_parallel_pair`, which you may find to be an easier way of
    achieving your goal. -/
def cocone.of_cofork {F : walking_parallel_pair ⥤ C} (t : cofork (F.map left) (F.map right)) : cocone F :=
  { x := t.X,
    ι :=
      { app :=
          fun X =>
            eq_to_hom
                (by 
                  tidy) ≫
              t.ι.app X,
        naturality' :=
          fun j j' g =>
            by 
              cases j <;> cases j' <;> cases g <;> dsimp <;> simp  } }

@[simp]
theorem cone.of_fork_π {F : walking_parallel_pair ⥤ C} (t : fork (F.map left) (F.map right)) j :
  (cone.of_fork t).π.app j =
    t.π.app j ≫
      eq_to_hom
        (by 
          tidy) :=
  rfl

@[simp]
theorem cocone.of_cofork_ι {F : walking_parallel_pair ⥤ C} (t : cofork (F.map left) (F.map right)) j :
  (cocone.of_cofork t).ι.app j =
    eq_to_hom
        (by 
          tidy) ≫
      t.ι.app j :=
  rfl

/-- Given `F : walking_parallel_pair ⥤ C`, which is really the same as
    `parallel_pair (F.map left) (F.map right)` and a cone on `F`, we get a fork on
    `F.map left` and `F.map right`. -/
def fork.of_cone {F : walking_parallel_pair ⥤ C} (t : cone F) : fork (F.map left) (F.map right) :=
  { x := t.X,
    π :=
      { app :=
          fun X =>
            t.π.app X ≫
              eq_to_hom
                (by 
                  tidy) } }

/-- Given `F : walking_parallel_pair ⥤ C`, which is really the same as
    `parallel_pair (F.map left) (F.map right)` and a cocone on `F`, we get a cofork on
    `F.map left` and `F.map right`. -/
def cofork.of_cocone {F : walking_parallel_pair ⥤ C} (t : cocone F) : cofork (F.map left) (F.map right) :=
  { x := t.X,
    ι :=
      { app :=
          fun X =>
            eq_to_hom
                (by 
                  tidy) ≫
              t.ι.app X } }

@[simp]
theorem fork.of_cone_π {F : walking_parallel_pair ⥤ C} (t : cone F) j :
  (fork.of_cone t).π.app j =
    t.π.app j ≫
      eq_to_hom
        (by 
          tidy) :=
  rfl

@[simp]
theorem cofork.of_cocone_ι {F : walking_parallel_pair ⥤ C} (t : cocone F) j :
  (cofork.of_cocone t).ι.app j =
    eq_to_hom
        (by 
          tidy) ≫
      t.ι.app j :=
  rfl

/--
Helper function for constructing morphisms between equalizer forks.
-/
@[simps]
def fork.mk_hom {s t : fork f g} (k : s.X ⟶ t.X) (w : k ≫ t.ι = s.ι) : s ⟶ t :=
  { Hom := k,
    w' :=
      by 
        rintro ⟨_ | _⟩
        ·
          exact w
        ·
          simpa using w =≫ f }

/--
To construct an isomorphism between forks,
it suffices to give an isomorphism between the cone points
and check that it commutes with the `ι` morphisms.
-/
@[simps]
def fork.ext {s t : fork f g} (i : s.X ≅ t.X) (w : i.hom ≫ t.ι = s.ι) : s ≅ t :=
  { Hom := fork.mk_hom i.hom w,
    inv :=
      fork.mk_hom i.inv
        (by 
          rw [←w, iso.inv_hom_id_assoc]) }

/--
Helper function for constructing morphisms between coequalizer coforks.
-/
@[simps]
def cofork.mk_hom {s t : cofork f g} (k : s.X ⟶ t.X) (w : s.π ≫ k = t.π) : s ⟶ t :=
  { Hom := k,
    w' :=
      by 
        rintro ⟨_ | _⟩
        simpa using f ≫= w 
        exact w }

/--
To construct an isomorphism between coforks,
it suffices to give an isomorphism between the cocone points
and check that it commutes with the `π` morphisms.
-/
def cofork.ext {s t : cofork f g} (i : s.X ≅ t.X) (w : s.π ≫ i.hom = t.π) : s ≅ t :=
  { Hom := cofork.mk_hom i.hom w,
    inv :=
      cofork.mk_hom i.inv
        (by 
          rw [iso.comp_inv_eq, w]) }

variable(f g)

section 

/--
`has_equalizer f g` represents a particular choice of limiting cone
for the parallel pair of morphisms `f` and `g`.
-/
abbrev has_equalizer :=
  has_limit (parallel_pair f g)

variable[has_equalizer f g]

/-- If an equalizer of `f` and `g` exists, we can access an arbitrary choice of such by
    saying `equalizer f g`. -/
abbrev equalizer : C :=
  limit (parallel_pair f g)

/-- If an equalizer of `f` and `g` exists, we can access the inclusion
    `equalizer f g ⟶ X` by saying `equalizer.ι f g`. -/
abbrev equalizer.ι : equalizer f g ⟶ X :=
  limit.π (parallel_pair f g) zero

/--
An equalizer cone for a parallel pair `f` and `g`.
-/
abbrev equalizer.fork : fork f g :=
  limit.cone (parallel_pair f g)

@[simp]
theorem equalizer.fork_ι : (equalizer.fork f g).ι = equalizer.ι f g :=
  rfl

@[simp]
theorem equalizer.fork_π_app_zero : (equalizer.fork f g).π.app zero = equalizer.ι f g :=
  rfl

@[reassoc]
theorem equalizer.condition : equalizer.ι f g ≫ f = equalizer.ι f g ≫ g :=
  fork.condition$ limit.cone$ parallel_pair f g

/-- The equalizer built from `equalizer.ι f g` is limiting. -/
def equalizer_is_equalizer : is_limit (fork.of_ι (equalizer.ι f g) (equalizer.condition f g)) :=
  is_limit.of_iso_limit (limit.is_limit _)
    (fork.ext (iso.refl _)
      (by 
        tidy))

variable{f g}

/-- A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` factors through the equalizer of `f` and `g`
    via `equalizer.lift : W ⟶ equalizer f g`. -/
abbrev equalizer.lift {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) : W ⟶ equalizer f g :=
  limit.lift (parallel_pair f g) (fork.of_ι k h)

@[simp, reassoc]
theorem equalizer.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) : equalizer.lift k h ≫ equalizer.ι f g = k :=
  limit.lift_π _ _

/-- A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` induces a morphism `l : W ⟶ equalizer f g`
    satisfying `l ≫ equalizer.ι f g = k`. -/
def equalizer.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) : { l : W ⟶ equalizer f g // l ≫ equalizer.ι f g = k } :=
  ⟨equalizer.lift k h, equalizer.lift_ι _ _⟩

/-- Two maps into an equalizer are equal if they are are equal when composed with the equalizer
    map. -/
@[ext]
theorem equalizer.hom_ext {W : C} {k l : W ⟶ equalizer f g} (h : k ≫ equalizer.ι f g = l ≫ equalizer.ι f g) : k = l :=
  fork.is_limit.hom_ext (limit.is_limit _) h

/-- An equalizer morphism is a monomorphism -/
instance equalizer.ι_mono : mono (equalizer.ι f g) :=
  { right_cancellation := fun Z h k w => equalizer.hom_ext w }

end 

section 

variable{f g}

/-- The equalizer morphism in any limit cone is a monomorphism. -/
theorem mono_of_is_limit_parallel_pair {c : cone (parallel_pair f g)} (i : is_limit c) : mono (fork.ι c) :=
  { right_cancellation := fun Z h k w => fork.is_limit.hom_ext i w }

end 

section 

variable{f g}

/-- The identity determines a cone on the equalizer diagram of `f` and `g` if `f = g`. -/
def id_fork (h : f = g) : fork f g :=
  fork.of_ι (𝟙 X)$ h ▸ rfl

/-- The identity on `X` is an equalizer of `(f, g)`, if `f = g`. -/
def is_limit_id_fork (h : f = g) : is_limit (id_fork h) :=
  fork.is_limit.mk _ (fun s => fork.ι s) (fun s => category.comp_id _)
    fun s m h =>
      by 
        convert h zero 
        exact (category.comp_id _).symm

/-- Every equalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
theorem is_iso_limit_cone_parallel_pair_of_eq (h₀ : f = g) {c : cone (parallel_pair f g)} (h : is_limit c) :
  is_iso (c.π.app zero) :=
  is_iso.of_iso$ is_limit.cone_point_unique_up_to_iso h$ is_limit_id_fork h₀

/-- The equalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
theorem equalizer.ι_of_eq [has_equalizer f g] (h : f = g) : is_iso (equalizer.ι f g) :=
  is_iso_limit_cone_parallel_pair_of_eq h$ limit.is_limit _

/-- Every equalizer of `(f, f)` is an isomorphism. -/
theorem is_iso_limit_cone_parallel_pair_of_self {c : cone (parallel_pair f f)} (h : is_limit c) :
  is_iso (c.π.app zero) :=
  is_iso_limit_cone_parallel_pair_of_eq rfl h

/-- An equalizer that is an epimorphism is an isomorphism. -/
theorem is_iso_limit_cone_parallel_pair_of_epi {c : cone (parallel_pair f g)} (h : is_limit c) [epi (c.π.app zero)] :
  is_iso (c.π.app zero) :=
  is_iso_limit_cone_parallel_pair_of_eq ((cancel_epi _).1 (fork.condition c)) h

end 

instance has_equalizer_of_self : has_equalizer f f :=
  has_limit.mk { Cone := id_fork rfl, IsLimit := is_limit_id_fork rfl }

/-- The equalizer inclusion for `(f, f)` is an isomorphism. -/
instance equalizer.ι_of_self : is_iso (equalizer.ι f f) :=
  equalizer.ι_of_eq rfl

/-- The equalizer of a morphism with itself is isomorphic to the source. -/
def equalizer.iso_source_of_self : equalizer f f ≅ X :=
  as_iso (equalizer.ι f f)

@[simp]
theorem equalizer.iso_source_of_self_hom : (equalizer.iso_source_of_self f).Hom = equalizer.ι f f :=
  rfl

@[simp]
theorem equalizer.iso_source_of_self_inv :
  (equalizer.iso_source_of_self f).inv =
    equalizer.lift (𝟙 X)
      (by 
        simp ) :=
  by 
    ext 
    simp [equalizer.iso_source_of_self]

section 

/--
`has_coequalizer f g` represents a particular choice of colimiting cocone
for the parallel pair of morphisms `f` and `g`.
-/
abbrev has_coequalizer :=
  has_colimit (parallel_pair f g)

variable[has_coequalizer f g]

/-- If a coequalizer of `f` and `g` exists, we can access an arbitrary choice of such by
    saying `coequalizer f g`. -/
abbrev coequalizer : C :=
  colimit (parallel_pair f g)

/--  If a coequalizer of `f` and `g` exists, we can access the corresponding projection by
    saying `coequalizer.π f g`. -/
abbrev coequalizer.π : Y ⟶ coequalizer f g :=
  colimit.ι (parallel_pair f g) one

/--
An arbitrary choice of coequalizer cocone for a parallel pair `f` and `g`.
-/
abbrev coequalizer.cofork : cofork f g :=
  colimit.cocone (parallel_pair f g)

@[simp]
theorem coequalizer.cofork_π : (coequalizer.cofork f g).π = coequalizer.π f g :=
  rfl

@[simp]
theorem coequalizer.cofork_ι_app_one : (coequalizer.cofork f g).ι.app one = coequalizer.π f g :=
  rfl

@[reassoc]
theorem coequalizer.condition : f ≫ coequalizer.π f g = g ≫ coequalizer.π f g :=
  cofork.condition$ colimit.cocone$ parallel_pair f g

/-- The cofork built from `coequalizer.π f g` is colimiting. -/
def coequalizer_is_coequalizer : is_colimit (cofork.of_π (coequalizer.π f g) (coequalizer.condition f g)) :=
  is_colimit.of_iso_colimit (colimit.is_colimit _)
    (cofork.ext (iso.refl _)
      (by 
        tidy))

variable{f g}

/-- Any morphism `k : Y ⟶ W` satisfying `f ≫ k = g ≫ k` factors through the coequalizer of `f`
    and `g` via `coequalizer.desc : coequalizer f g ⟶ W`. -/
abbrev coequalizer.desc {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) : coequalizer f g ⟶ W :=
  colimit.desc (parallel_pair f g) (cofork.of_π k h)

@[simp, reassoc]
theorem coequalizer.π_desc {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) : coequalizer.π f g ≫ coequalizer.desc k h = k :=
  colimit.ι_desc _ _

/-- Any morphism `k : Y ⟶ W` satisfying `f ≫ k = g ≫ k` induces a morphism
    `l : coequalizer f g ⟶ W` satisfying `coequalizer.π ≫ g = l`. -/
def coequalizer.desc' {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) :
  { l : coequalizer f g ⟶ W // coequalizer.π f g ≫ l = k } :=
  ⟨coequalizer.desc k h, coequalizer.π_desc _ _⟩

/-- Two maps from a coequalizer are equal if they are equal when composed with the coequalizer
    map -/
@[ext]
theorem coequalizer.hom_ext {W : C} {k l : coequalizer f g ⟶ W} (h : coequalizer.π f g ≫ k = coequalizer.π f g ≫ l) :
  k = l :=
  cofork.is_colimit.hom_ext (colimit.is_colimit _) h

/-- A coequalizer morphism is an epimorphism -/
instance coequalizer.π_epi : epi (coequalizer.π f g) :=
  { left_cancellation := fun Z h k w => coequalizer.hom_ext w }

end 

section 

variable{f g}

/-- The coequalizer morphism in any colimit cocone is an epimorphism. -/
theorem epi_of_is_colimit_parallel_pair {c : cocone (parallel_pair f g)} (i : is_colimit c) : epi (c.ι.app one) :=
  { left_cancellation := fun Z h k w => cofork.is_colimit.hom_ext i w }

end 

section 

variable{f g}

/-- The identity determines a cocone on the coequalizer diagram of `f` and `g`, if `f = g`. -/
def id_cofork (h : f = g) : cofork f g :=
  cofork.of_π (𝟙 Y)$ h ▸ rfl

/-- The identity on `Y` is a coequalizer of `(f, g)`, where `f = g`.  -/
def is_colimit_id_cofork (h : f = g) : is_colimit (id_cofork h) :=
  cofork.is_colimit.mk _ (fun s => cofork.π s) (fun s => category.id_comp _)
    fun s m h =>
      by 
        convert h one 
        exact (category.id_comp _).symm

/-- Every coequalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
theorem is_iso_colimit_cocone_parallel_pair_of_eq (h₀ : f = g) {c : cocone (parallel_pair f g)} (h : is_colimit c) :
  is_iso (c.ι.app one) :=
  is_iso.of_iso$ is_colimit.cocone_point_unique_up_to_iso (is_colimit_id_cofork h₀) h

/-- The coequalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
theorem coequalizer.π_of_eq [has_coequalizer f g] (h : f = g) : is_iso (coequalizer.π f g) :=
  is_iso_colimit_cocone_parallel_pair_of_eq h$ colimit.is_colimit _

/-- Every coequalizer of `(f, f)` is an isomorphism. -/
theorem is_iso_colimit_cocone_parallel_pair_of_self {c : cocone (parallel_pair f f)} (h : is_colimit c) :
  is_iso (c.ι.app one) :=
  is_iso_colimit_cocone_parallel_pair_of_eq rfl h

/-- A coequalizer that is a monomorphism is an isomorphism. -/
theorem is_iso_limit_cocone_parallel_pair_of_epi {c : cocone (parallel_pair f g)} (h : is_colimit c)
  [mono (c.ι.app one)] : is_iso (c.ι.app one) :=
  is_iso_colimit_cocone_parallel_pair_of_eq ((cancel_mono _).1 (cofork.condition c)) h

end 

instance has_coequalizer_of_self : has_coequalizer f f :=
  has_colimit.mk { Cocone := id_cofork rfl, IsColimit := is_colimit_id_cofork rfl }

/-- The coequalizer projection for `(f, f)` is an isomorphism. -/
instance coequalizer.π_of_self : is_iso (coequalizer.π f f) :=
  coequalizer.π_of_eq rfl

/-- The coequalizer of a morphism with itself is isomorphic to the target. -/
def coequalizer.iso_target_of_self : coequalizer f f ≅ Y :=
  (as_iso (coequalizer.π f f)).symm

@[simp]
theorem coequalizer.iso_target_of_self_hom :
  (coequalizer.iso_target_of_self f).Hom =
    coequalizer.desc (𝟙 Y)
      (by 
        simp ) :=
  by 
    ext 
    simp [coequalizer.iso_target_of_self]

@[simp]
theorem coequalizer.iso_target_of_self_inv : (coequalizer.iso_target_of_self f).inv = coequalizer.π f f :=
  rfl

section Comparison

variable{D : Type u₂}[category.{v} D](G : C ⥤ D)

/--
The comparison morphism for the equalizer of `f,g`.
This is an isomorphism iff `G` preserves the equalizer of `f,g`; see
`category_theory/limits/preserves/shapes/equalizers.lean`
-/
def equalizer_comparison [has_equalizer f g] [has_equalizer (G.map f) (G.map g)] :
  G.obj (equalizer f g) ⟶ equalizer (G.map f) (G.map g) :=
  equalizer.lift (G.map (equalizer.ι _ _))
    (by 
      simp only [←G.map_comp, equalizer.condition])

@[simp, reassoc]
theorem equalizer_comparison_comp_π [has_equalizer f g] [has_equalizer (G.map f) (G.map g)] :
  equalizer_comparison f g G ≫ equalizer.ι (G.map f) (G.map g) = G.map (equalizer.ι f g) :=
  equalizer.lift_ι _ _

@[simp, reassoc]
theorem map_lift_equalizer_comparison [has_equalizer f g] [has_equalizer (G.map f) (G.map g)] {Z : C} {h : Z ⟶ X}
  (w : h ≫ f = h ≫ g) :
  G.map (equalizer.lift h w) ≫ equalizer_comparison f g G =
    equalizer.lift (G.map h)
      (by 
        simp only [←G.map_comp, w]) :=
  by 
    ext 
    simp [←G.map_comp]

/-- The comparison morphism for the coequalizer of `f,g`. -/
def coequalizer_comparison [has_coequalizer f g] [has_coequalizer (G.map f) (G.map g)] :
  coequalizer (G.map f) (G.map g) ⟶ G.obj (coequalizer f g) :=
  coequalizer.desc (G.map (coequalizer.π _ _))
    (by 
      simp only [←G.map_comp, coequalizer.condition])

@[simp, reassoc]
theorem ι_comp_coequalizer_comparison [has_coequalizer f g] [has_coequalizer (G.map f) (G.map g)] :
  coequalizer.π _ _ ≫ coequalizer_comparison f g G = G.map (coequalizer.π _ _) :=
  coequalizer.π_desc _ _

@[simp, reassoc]
theorem coequalizer_comparison_map_desc [has_coequalizer f g] [has_coequalizer (G.map f) (G.map g)] {Z : C} {h : Y ⟶ Z}
  (w : f ≫ h = g ≫ h) :
  coequalizer_comparison f g G ≫ G.map (coequalizer.desc h w) =
    coequalizer.desc (G.map h)
      (by 
        simp only [←G.map_comp, w]) :=
  by 
    ext 
    simp [←G.map_comp]

end Comparison

variable(C)

/-- `has_equalizers` represents a choice of equalizer for every pair of morphisms -/
abbrev has_equalizers :=
  has_limits_of_shape walking_parallel_pair C

/-- `has_coequalizers` represents a choice of coequalizer for every pair of morphisms -/
abbrev has_coequalizers :=
  has_colimits_of_shape walking_parallel_pair C

/-- If `C` has all limits of diagrams `parallel_pair f g`, then it has all equalizers -/
theorem has_equalizers_of_has_limit_parallel_pair [∀ {X Y : C} {f g : X ⟶ Y}, has_limit (parallel_pair f g)] :
  has_equalizers C :=
  { HasLimit := fun F => has_limit_of_iso (diagram_iso_parallel_pair F).symm }

/-- If `C` has all colimits of diagrams `parallel_pair f g`, then it has all coequalizers -/
theorem has_coequalizers_of_has_colimit_parallel_pair [∀ {X Y : C} {f g : X ⟶ Y}, has_colimit (parallel_pair f g)] :
  has_coequalizers C :=
  { HasColimit := fun F => has_colimit_of_iso (diagram_iso_parallel_pair F) }

section 

variable{C}[split_mono f]

/--
A split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
Here we build the cone, and show in `split_mono_equalizes` that it is a limit cone.
-/
@[simps (config := { rhsMd := semireducible })]
def cone_of_split_mono : cone (parallel_pair (𝟙 Y) (retraction f ≫ f)) :=
  fork.of_ι f
    (by 
      simp )

/--
A split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
-/
def split_mono_equalizes {X Y : C} (f : X ⟶ Y) [split_mono f] : is_limit (cone_of_split_mono f) :=
  fork.is_limit.mk' _$
    fun s =>
      ⟨s.ι ≫ retraction f,
        by 
          dsimp 
          rw [category.assoc, ←s.condition]
          apply category.comp_id,
        fun m hm =>
          by 
            simp [←hm]⟩

end 

section 

variable{C}[split_epi f]

/--
A split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
Here we build the cocone, and show in `split_epi_coequalizes` that it is a colimit cocone.
-/
@[simps (config := { rhsMd := semireducible })]
def cocone_of_split_epi : cocone (parallel_pair (𝟙 X) (f ≫ section_ f)) :=
  cofork.of_π f
    (by 
      simp )

/--
A split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
-/
def split_epi_coequalizes {X Y : C} (f : X ⟶ Y) [split_epi f] : is_colimit (cocone_of_split_epi f) :=
  cofork.is_colimit.mk' _$
    fun s =>
      ⟨section_ f ≫ s.π,
        by 
          dsimp 
          rw [←category.assoc, ←s.condition, category.id_comp],
        fun m hm =>
          by 
            simp [←hm]⟩

end 

end CategoryTheory.Limits

