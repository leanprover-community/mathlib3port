import Mathbin.CategoryTheory.Limits.Shapes.WidePullbacks 
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Pullbacks

We define a category `walking_cospan` (resp. `walking_span`), which is the index category
for the given data for a pullback (resp. pushout) diagram. Convenience methods `cospan f g`
and `span f g` construct functors from the walking (co)span, hitting the given morphisms.

We define `pullback f g` and `pushout f g` as limits and colimits of such functors.

## References
* [Stacks: Fibre products](https://stacks.math.columbia.edu/tag/001U)
* [Stacks: Pushouts](https://stacks.math.columbia.edu/tag/0025)
-/


noncomputable theory

open CategoryTheory

namespace CategoryTheory.Limits

universe v u u₂

attribute [local tidy] tactic.case_bash

/--
The type of objects for the diagram indexing a pullback, defined as a special case of
`wide_pullback_shape`.
-/
abbrev walking_cospan : Type v :=
  wide_pullback_shape walking_pair

/-- The left point of the walking cospan. -/
@[matchPattern]
abbrev walking_cospan.left : walking_cospan :=
  some walking_pair.left

/-- The right point of the walking cospan. -/
@[matchPattern]
abbrev walking_cospan.right : walking_cospan :=
  some walking_pair.right

/-- The central point of the walking cospan. -/
@[matchPattern]
abbrev walking_cospan.one : walking_cospan :=
  none

/--
The type of objects for the diagram indexing a pushout, defined as a special case of
`wide_pushout_shape`.
-/
abbrev walking_span : Type v :=
  wide_pushout_shape walking_pair

/-- The left point of the walking span. -/
@[matchPattern]
abbrev walking_span.left : walking_span :=
  some walking_pair.left

/-- The right point of the walking span. -/
@[matchPattern]
abbrev walking_span.right : walking_span :=
  some walking_pair.right

/-- The central point of the walking span. -/
@[matchPattern]
abbrev walking_span.zero : walking_span :=
  none

namespace WalkingCospan

/-- The type of arrows for the diagram indexing a pullback. -/
abbrev hom : walking_cospan → walking_cospan → Type v :=
  wide_pullback_shape.hom

/-- The left arrow of the walking cospan. -/
@[matchPattern]
abbrev hom.inl : left ⟶ one :=
  wide_pullback_shape.hom.term _

/-- The right arrow of the walking cospan. -/
@[matchPattern]
abbrev hom.inr : right ⟶ one :=
  wide_pullback_shape.hom.term _

/-- The identity arrows of the walking cospan. -/
@[matchPattern]
abbrev hom.id (X : walking_cospan) : X ⟶ X :=
  wide_pullback_shape.hom.id X

instance (X Y : walking_cospan) : Subsingleton (X ⟶ Y) :=
  by 
    tidy

end WalkingCospan

namespace WalkingSpan

/-- The type of arrows for the diagram indexing a pushout. -/
abbrev hom : walking_span → walking_span → Type v :=
  wide_pushout_shape.hom

/-- The left arrow of the walking span. -/
@[matchPattern]
abbrev hom.fst : zero ⟶ left :=
  wide_pushout_shape.hom.init _

/-- The right arrow of the walking span. -/
@[matchPattern]
abbrev hom.snd : zero ⟶ right :=
  wide_pushout_shape.hom.init _

/-- The identity arrows of the walking span. -/
@[matchPattern]
abbrev hom.id (X : walking_span) : X ⟶ X :=
  wide_pushout_shape.hom.id X

instance (X Y : walking_span) : Subsingleton (X ⟶ Y) :=
  by 
    tidy

end WalkingSpan

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom

variable {C : Type u} [category.{v} C]

/-- `cospan f g` is the functor from the walking cospan hitting `f` and `g`. -/
def cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : walking_cospan ⥤ C :=
  wide_pullback_shape.wide_cospan Z (fun j => walking_pair.cases_on j X Y) fun j => walking_pair.cases_on j f g

/-- `span f g` is the functor from the walking span hitting `f` and `g`. -/
def span {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : walking_span ⥤ C :=
  wide_pushout_shape.wide_span X (fun j => walking_pair.cases_on j Y Z) fun j => walking_pair.cases_on j f g

@[simp]
theorem cospan_left {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj walking_cospan.left = X :=
  rfl

@[simp]
theorem span_left {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj walking_span.left = Y :=
  rfl

@[simp]
theorem cospan_right {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj walking_cospan.right = Y :=
  rfl

@[simp]
theorem span_right {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj walking_span.right = Z :=
  rfl

@[simp]
theorem cospan_one {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj walking_cospan.one = Z :=
  rfl

@[simp]
theorem span_zero {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj walking_span.zero = X :=
  rfl

@[simp]
theorem cospan_map_inl {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).map walking_cospan.hom.inl = f :=
  rfl

@[simp]
theorem span_map_fst {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).map walking_span.hom.fst = f :=
  rfl

@[simp]
theorem cospan_map_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).map walking_cospan.hom.inr = g :=
  rfl

@[simp]
theorem span_map_snd {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).map walking_span.hom.snd = g :=
  rfl

theorem cospan_map_id {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (w : walking_cospan) :
  (cospan f g).map (walking_cospan.hom.id w) = 𝟙 _ :=
  rfl

theorem span_map_id {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (w : walking_span) :
  (span f g).map (walking_span.hom.id w) = 𝟙 _ :=
  rfl

/-- Every diagram indexing an pullback is naturally isomorphic (actually, equal) to a `cospan` -/
@[simps (config := { rhsMd := semireducible })]
def diagram_iso_cospan (F : walking_cospan ⥤ C) : F ≅ cospan (F.map inl) (F.map inr) :=
  nat_iso.of_components
    (fun j =>
      eq_to_iso
        (by 
          tidy))
    (by 
      tidy)

/-- Every diagram indexing a pushout is naturally isomorphic (actually, equal) to a `span` -/
@[simps (config := { rhsMd := semireducible })]
def diagram_iso_span (F : walking_span ⥤ C) : F ≅ span (F.map fst) (F.map snd) :=
  nat_iso.of_components
    (fun j =>
      eq_to_iso
        (by 
          tidy))
    (by 
      tidy)

variable {W X Y Z : C}

/-- A pullback cone is just a cone on the cospan formed by two morphisms `f : X ⟶ Z` and
    `g : Y ⟶ Z`.-/
abbrev pullback_cone (f : X ⟶ Z) (g : Y ⟶ Z) :=
  cone (cospan f g)

namespace PullbackCone

variable {f : X ⟶ Z} {g : Y ⟶ Z}

/-- The first projection of a pullback cone. -/
abbrev fst (t : pullback_cone f g) : t.X ⟶ X :=
  t.π.app walking_cospan.left

/-- The second projection of a pullback cone. -/
abbrev snd (t : pullback_cone f g) : t.X ⟶ Y :=
  t.π.app walking_cospan.right

/-- This is a slightly more convenient method to verify that a pullback cone is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def is_limit_aux (t : pullback_cone f g) (lift : ∀ s : pullback_cone f g, s.X ⟶ t.X)
  (fac_left : ∀ s : pullback_cone f g, lift s ≫ t.fst = s.fst)
  (fac_right : ∀ s : pullback_cone f g, lift s ≫ t.snd = s.snd)
  (uniq : ∀ s : pullback_cone f g m : s.X ⟶ t.X w : ∀ j : walking_cospan, m ≫ t.π.app j = s.π.app j, m = lift s) :
  is_limit t :=
  { lift,
    fac' :=
      fun s j =>
        Option.casesOn j
          (by 
            rw [←s.w inl, ←t.w inl, ←category.assoc]
            congr 
            exact fac_left s)
          fun j' => walking_pair.cases_on j' (fac_left s) (fac_right s),
    uniq' := uniq }

/-- This is another convenient method to verify that a pullback cone is a limit cone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def is_limit_aux' (t : pullback_cone f g)
  (create :
    ∀ s : pullback_cone f g,
      { l // l ≫ t.fst = s.fst ∧ l ≫ t.snd = s.snd ∧ ∀ {m}, m ≫ t.fst = s.fst → m ≫ t.snd = s.snd → m = l }) :
  limits.is_limit t :=
  pullback_cone.is_limit_aux t (fun s => (create s).1) (fun s => (create s).2.1) (fun s => (create s).2.2.1)
    fun s m w => (create s).2.2.2 (w walking_cospan.left) (w walking_cospan.right)

/-- A pullback cone on `f` and `g` is determined by morphisms `fst : W ⟶ X` and `snd : W ⟶ Y`
    such that `fst ≫ f = snd ≫ g`. -/
@[simps]
def mk {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) : pullback_cone f g :=
  { x := W, π := { app := fun j => Option.casesOn j (fst ≫ f) fun j' => walking_pair.cases_on j' fst snd } }

@[simp]
theorem mk_π_app_left {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
  (mk fst snd Eq).π.app walking_cospan.left = fst :=
  rfl

@[simp]
theorem mk_π_app_right {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
  (mk fst snd Eq).π.app walking_cospan.right = snd :=
  rfl

@[simp]
theorem mk_π_app_one {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
  (mk fst snd Eq).π.app walking_cospan.one = fst ≫ f :=
  rfl

@[simp]
theorem mk_fst {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) : (mk fst snd Eq).fst = fst :=
  rfl

@[simp]
theorem mk_snd {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) : (mk fst snd Eq).snd = snd :=
  rfl

@[reassoc]
theorem condition (t : pullback_cone f g) : fst t ≫ f = snd t ≫ g :=
  (t.w inl).trans (t.w inr).symm

/-- To check whether a morphism is equalized by the maps of a pullback cone, it suffices to check
  it for `fst t` and `snd t` -/
theorem equalizer_ext (t : pullback_cone f g) {W : C} {k l : W ⟶ t.X} (h₀ : k ≫ fst t = l ≫ fst t)
  (h₁ : k ≫ snd t = l ≫ snd t) : ∀ j : walking_cospan, k ≫ t.π.app j = l ≫ t.π.app j
| some walking_pair.left => h₀
| some walking_pair.right => h₁
| none =>
  by 
    rw [←t.w inl, reassoc_of h₀]

theorem is_limit.hom_ext {t : pullback_cone f g} (ht : is_limit t) {W : C} {k l : W ⟶ t.X} (h₀ : k ≫ fst t = l ≫ fst t)
  (h₁ : k ≫ snd t = l ≫ snd t) : k = l :=
  ht.hom_ext$ equalizer_ext _ h₀ h₁

theorem mono_snd_of_is_pullback_of_mono {t : pullback_cone f g} (ht : is_limit t) [mono f] : mono t.snd :=
  ⟨fun W h k i =>
      is_limit.hom_ext ht
        (by 
          simp [←cancel_mono f, t.condition, reassoc_of i])
        i⟩

theorem mono_fst_of_is_pullback_of_mono {t : pullback_cone f g} (ht : is_limit t) [mono g] : mono t.fst :=
  ⟨fun W h k i =>
      is_limit.hom_ext ht i
        (by 
          simp [←cancel_mono g, ←t.condition, reassoc_of i])⟩

/-- If `t` is a limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W ⟶ Y` are such that
    `h ≫ f = k ≫ g`, then we have `l : W ⟶ t.X` satisfying `l ≫ fst t = h` and `l ≫ snd t = k`.
    -/
def is_limit.lift' {t : pullback_cone f g} (ht : is_limit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
  { l : W ⟶ t.X // l ≫ fst t = h ∧ l ≫ snd t = k } :=
  ⟨ht.lift$ pullback_cone.mk _ _ w, ht.fac _ _, ht.fac _ _⟩

/--
This is a more convenient formulation to show that a `pullback_cone` constructed using
`pullback_cone.mk` is a limit cone.
-/
def is_limit.mk {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g) (lift : ∀ s : pullback_cone f g, s.X ⟶ W)
  (fac_left : ∀ s : pullback_cone f g, lift s ≫ fst = s.fst) (fac_right : ∀ s : pullback_cone f g, lift s ≫ snd = s.snd)
  (uniq : ∀ s : pullback_cone f g m : s.X ⟶ W w_fst : m ≫ fst = s.fst w_snd : m ≫ snd = s.snd, m = lift s) :
  is_limit (mk fst snd Eq) :=
  is_limit_aux _ lift fac_left fac_right fun s m w => uniq s m (w walking_cospan.left) (w walking_cospan.right)

/-- The flip of a pullback square is a pullback square. -/
def flip_is_limit {W : C} {h : W ⟶ X} {k : W ⟶ Y} {comm : h ≫ f = k ≫ g} (t : is_limit (mk _ _ comm.symm)) :
  is_limit (mk _ _ comm) :=
  is_limit_aux' _$
    fun s =>
      by 
        refine'
          ⟨(is_limit.lift' t _ _ s.condition.symm).1, (is_limit.lift' t _ _ _).2.2, (is_limit.lift' t _ _ _).2.1,
            fun m m₁ m₂ => t.hom_ext _⟩
        apply (mk k h _).equalizer_ext
        ·
          rwa [(is_limit.lift' t _ _ _).2.1]
        ·
          rwa [(is_limit.lift' t _ _ _).2.2]

/--
The pullback cone `(𝟙 X, 𝟙 X)` for the pair `(f, f)` is a limit if `f` is a mono. The converse is
shown in `mono_of_pullback_is_id`.
-/
def is_limit_mk_id_id (f : X ⟶ Y) [mono f] : is_limit (mk (𝟙 X) (𝟙 X) rfl : pullback_cone f f) :=
  is_limit.mk _ (fun s => s.fst) (fun s => category.comp_id _)
    (fun s =>
      by 
        rw [←cancel_mono f, category.comp_id, s.condition])
    fun s m m₁ m₂ =>
      by 
        simpa using m₁

/--
`f` is a mono if the pullback cone `(𝟙 X, 𝟙 X)` is a limit for the pair `(f, f)`. The converse is
given in `pullback_cone.is_id_of_mono`.
-/
theorem mono_of_is_limit_mk_id_id (f : X ⟶ Y) (t : is_limit (mk (𝟙 X) (𝟙 X) rfl : pullback_cone f f)) : mono f :=
  ⟨fun Z g h eq =>
      by 
        rcases pullback_cone.is_limit.lift' t _ _ Eq with ⟨_, rfl, rfl⟩
        rfl⟩

/-- Suppose `f` and `g` are two morphisms with a common codomain and `s` is a limit cone over the
    diagram formed by `f` and `g`. Suppose `f` and `g` both factor through a monomorphism `h` via
    `x` and `y`, respectively.  Then `s` is also a limit cone over the diagram formed by `x` and
    `y`.  -/
def is_limit_of_factors (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Z) [mono h] (x : X ⟶ W) (y : Y ⟶ W) (hxh : x ≫ h = f)
  (hyh : y ≫ h = g) (s : pullback_cone f g) (hs : is_limit s) :
  is_limit
    (pullback_cone.mk _ _
      (show s.fst ≫ x = s.snd ≫ y from
        (cancel_mono h).1$
          by 
            simp only [category.assoc, hxh, hyh, s.condition])) :=
  pullback_cone.is_limit_aux' _$
    fun t =>
      ⟨hs.lift
          (pullback_cone.mk t.fst t.snd$
            by 
              rw [←hxh, ←hyh, reassoc_of t.condition]),
        ⟨hs.fac _ walking_cospan.left, hs.fac _ walking_cospan.right,
          fun r hr hr' =>
            by 
              apply pullback_cone.is_limit.hom_ext hs <;>
                simp only [pullback_cone.mk_fst, pullback_cone.mk_snd] at hr hr'⊢ <;> simp only [hr, hr'] <;> symm 
              exacts[hs.fac _ walking_cospan.left, hs.fac _ walking_cospan.right]⟩⟩

end PullbackCone

/-- A pushout cocone is just a cocone on the span formed by two morphisms `f : X ⟶ Y` and
    `g : X ⟶ Z`.-/
abbrev pushout_cocone (f : X ⟶ Y) (g : X ⟶ Z) :=
  cocone (span f g)

namespace PushoutCocone

variable {f : X ⟶ Y} {g : X ⟶ Z}

/-- The first inclusion of a pushout cocone. -/
abbrev inl (t : pushout_cocone f g) : Y ⟶ t.X :=
  t.ι.app walking_span.left

/-- The second inclusion of a pushout cocone. -/
abbrev inr (t : pushout_cocone f g) : Z ⟶ t.X :=
  t.ι.app walking_span.right

/-- This is a slightly more convenient method to verify that a pushout cocone is a colimit cocone.
    It only asks for a proof of facts that carry any mathematical content -/
def is_colimit_aux (t : pushout_cocone f g) (desc : ∀ s : pushout_cocone f g, t.X ⟶ s.X)
  (fac_left : ∀ s : pushout_cocone f g, t.inl ≫ desc s = s.inl)
  (fac_right : ∀ s : pushout_cocone f g, t.inr ≫ desc s = s.inr)
  (uniq : ∀ s : pushout_cocone f g m : t.X ⟶ s.X w : ∀ j : walking_span, t.ι.app j ≫ m = s.ι.app j, m = desc s) :
  is_colimit t :=
  { desc,
    fac' :=
      fun s j =>
        Option.casesOn j
          (by 
            simp [←s.w fst, ←t.w fst, fac_left s])
          fun j' => walking_pair.cases_on j' (fac_left s) (fac_right s),
    uniq' := uniq }

/-- This is another convenient method to verify that a pushout cocone is a colimit cocone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def is_colimit_aux' (t : pushout_cocone f g)
  (create :
    ∀ s : pushout_cocone f g,
      { l // t.inl ≫ l = s.inl ∧ t.inr ≫ l = s.inr ∧ ∀ {m}, t.inl ≫ m = s.inl → t.inr ≫ m = s.inr → m = l }) :
  is_colimit t :=
  is_colimit_aux t (fun s => (create s).1) (fun s => (create s).2.1) (fun s => (create s).2.2.1)
    fun s m w => (create s).2.2.2 (w walking_cospan.left) (w walking_cospan.right)

/-- A pushout cocone on `f` and `g` is determined by morphisms `inl : Y ⟶ W` and `inr : Z ⟶ W` such
    that `f ≫ inl = g ↠ inr`. -/
@[simps]
def mk {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : pushout_cocone f g :=
  { x := W, ι := { app := fun j => Option.casesOn j (f ≫ inl) fun j' => walking_pair.cases_on j' inl inr } }

@[simp]
theorem mk_ι_app_left {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
  (mk inl inr Eq).ι.app walking_span.left = inl :=
  rfl

@[simp]
theorem mk_ι_app_right {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
  (mk inl inr Eq).ι.app walking_span.right = inr :=
  rfl

@[simp]
theorem mk_ι_app_zero {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
  (mk inl inr Eq).ι.app walking_span.zero = f ≫ inl :=
  rfl

@[simp]
theorem mk_inl {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : (mk inl inr Eq).inl = inl :=
  rfl

@[simp]
theorem mk_inr {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : (mk inl inr Eq).inr = inr :=
  rfl

@[reassoc]
theorem condition (t : pushout_cocone f g) : f ≫ inl t = g ≫ inr t :=
  (t.w fst).trans (t.w snd).symm

/-- To check whether a morphism is coequalized by the maps of a pushout cocone, it suffices to check
  it for `inl t` and `inr t` -/
theorem coequalizer_ext (t : pushout_cocone f g) {W : C} {k l : t.X ⟶ W} (h₀ : inl t ≫ k = inl t ≫ l)
  (h₁ : inr t ≫ k = inr t ≫ l) : ∀ j : walking_span, t.ι.app j ≫ k = t.ι.app j ≫ l
| some walking_pair.left => h₀
| some walking_pair.right => h₁
| none =>
  by 
    rw [←t.w fst, category.assoc, category.assoc, h₀]

theorem is_colimit.hom_ext {t : pushout_cocone f g} (ht : is_colimit t) {W : C} {k l : t.X ⟶ W}
  (h₀ : inl t ≫ k = inl t ≫ l) (h₁ : inr t ≫ k = inr t ≫ l) : k = l :=
  ht.hom_ext$ coequalizer_ext _ h₀ h₁

/-- If `t` is a colimit pushout cocone over `f` and `g` and `h : Y ⟶ W` and `k : Z ⟶ W` are
    morphisms satisfying `f ≫ h = g ≫ k`, then we have a factorization `l : t.X ⟶ W` such that
    `inl t ≫ l = h` and `inr t ≫ l = k`. -/
def is_colimit.desc' {t : pushout_cocone f g} (ht : is_colimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) :
  { l : t.X ⟶ W // inl t ≫ l = h ∧ inr t ≫ l = k } :=
  ⟨ht.desc$ pushout_cocone.mk _ _ w, ht.fac _ _, ht.fac _ _⟩

theorem epi_inr_of_is_pushout_of_epi {t : pushout_cocone f g} (ht : is_colimit t) [epi f] : epi t.inr :=
  ⟨fun W h k i =>
      is_colimit.hom_ext ht
        (by 
          simp [←cancel_epi f, t.condition_assoc, i])
        i⟩

theorem epi_inl_of_is_pushout_of_epi {t : pushout_cocone f g} (ht : is_colimit t) [epi g] : epi t.inl :=
  ⟨fun W h k i =>
      is_colimit.hom_ext ht i
        (by 
          simp [←cancel_epi g, ←t.condition_assoc, i])⟩

/--
This is a more convenient formulation to show that a `pushout_cocone` constructed using
`pushout_cocone.mk` is a colimit cocone.
-/
def is_colimit.mk {W : C} {inl : Y ⟶ W} {inr : Z ⟶ W} (eq : f ≫ inl = g ≫ inr)
  (desc : ∀ s : pushout_cocone f g, W ⟶ s.X) (fac_left : ∀ s : pushout_cocone f g, inl ≫ desc s = s.inl)
  (fac_right : ∀ s : pushout_cocone f g, inr ≫ desc s = s.inr)
  (uniq : ∀ s : pushout_cocone f g m : W ⟶ s.X w_inl : inl ≫ m = s.inl w_inr : inr ≫ m = s.inr, m = desc s) :
  is_colimit (mk inl inr Eq) :=
  is_colimit_aux _ desc fac_left fac_right fun s m w => uniq s m (w walking_cospan.left) (w walking_cospan.right)

/-- The flip of a pushout square is a pushout square. -/
def flip_is_colimit {W : C} {h : Y ⟶ W} {k : Z ⟶ W} {comm : f ≫ h = g ≫ k} (t : is_colimit (mk _ _ comm.symm)) :
  is_colimit (mk _ _ comm) :=
  is_colimit_aux' _$
    fun s =>
      by 
        refine'
          ⟨(is_colimit.desc' t _ _ s.condition.symm).1, (is_colimit.desc' t _ _ _).2.2, (is_colimit.desc' t _ _ _).2.1,
            fun m m₁ m₂ => t.hom_ext _⟩
        apply (mk k h _).coequalizer_ext
        ·
          rwa [(is_colimit.desc' t _ _ _).2.1]
        ·
          rwa [(is_colimit.desc' t _ _ _).2.2]

/--
The pushout cocone `(𝟙 X, 𝟙 X)` for the pair `(f, f)` is a colimit if `f` is an epi. The converse is
shown in `epi_of_is_colimit_mk_id_id`.
-/
def is_colimit_mk_id_id (f : X ⟶ Y) [epi f] : is_colimit (mk (𝟙 Y) (𝟙 Y) rfl : pushout_cocone f f) :=
  is_colimit.mk _ (fun s => s.inl) (fun s => category.id_comp _)
    (fun s =>
      by 
        rw [←cancel_epi f, category.id_comp, s.condition])
    fun s m m₁ m₂ =>
      by 
        simpa using m₁

/--
`f` is an epi if the pushout cocone `(𝟙 X, 𝟙 X)` is a colimit for the pair `(f, f)`.
The converse is given in `pushout_cocone.is_colimit_mk_id_id`.
-/
theorem epi_of_is_colimit_mk_id_id (f : X ⟶ Y) (t : is_colimit (mk (𝟙 Y) (𝟙 Y) rfl : pushout_cocone f f)) : epi f :=
  ⟨fun Z g h eq =>
      by 
        rcases pushout_cocone.is_colimit.desc' t _ _ Eq with ⟨_, rfl, rfl⟩
        rfl⟩

/-- Suppose `f` and `g` are two morphisms with a common domain and `s` is a colimit cocone over the
    diagram formed by `f` and `g`. Suppose `f` and `g` both factor through an epimorphism `h` via
    `x` and `y`, respectively. Then `s` is also a colimit cocone over the diagram formed by `x` and
    `y`.  -/
def is_colimit_of_factors (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) [epi h] (x : W ⟶ Y) (y : W ⟶ Z) (hhx : h ≫ x = f)
  (hhy : h ≫ y = g) (s : pushout_cocone f g) (hs : is_colimit s) :
  is_colimit
    (pushout_cocone.mk _ _
      (show x ≫ s.inl = y ≫ s.inr from
        (cancel_epi h).1$
          by 
            rw [reassoc_of hhx, reassoc_of hhy, s.condition])) :=
  pushout_cocone.is_colimit_aux' _$
    fun t =>
      ⟨hs.desc
          (pushout_cocone.mk t.inl t.inr$
            by 
              rw [←hhx, ←hhy, category.assoc, category.assoc, t.condition]),
        ⟨hs.fac _ walking_span.left, hs.fac _ walking_span.right,
          fun r hr hr' =>
            by 
              apply pushout_cocone.is_colimit.hom_ext hs <;>
                simp only [pushout_cocone.mk_inl, pushout_cocone.mk_inr] at hr hr'⊢ <;> simp only [hr, hr'] <;> symm 
              exacts[hs.fac _ walking_span.left, hs.fac _ walking_span.right]⟩⟩

end PushoutCocone

/-- This is a helper construction that can be useful when verifying that a category has all
    pullbacks. Given `F : walking_cospan ⥤ C`, which is really the same as
    `cospan (F.map inl) (F.map inr)`, and a pullback cone on `F.map inl` and `F.map inr`, we
    get a cone on `F`.

    If you're thinking about using this, have a look at `has_pullbacks_of_has_limit_cospan`,
    which you may find to be an easier way of achieving your goal. -/
@[simps]
def cone.of_pullback_cone {F : walking_cospan ⥤ C} (t : pullback_cone (F.map inl) (F.map inr)) : cone F :=
  { x := t.X, π := t.π ≫ (diagram_iso_cospan F).inv }

/-- This is a helper construction that can be useful when verifying that a category has all
    pushout. Given `F : walking_span ⥤ C`, which is really the same as
    `span (F.map fst) (F.mal snd)`, and a pushout cocone on `F.map fst` and `F.map snd`,
    we get a cocone on `F`.

    If you're thinking about using this, have a look at `has_pushouts_of_has_colimit_span`, which
    you may find to be an easiery way of achieving your goal.  -/
@[simps]
def cocone.of_pushout_cocone {F : walking_span ⥤ C} (t : pushout_cocone (F.map fst) (F.map snd)) : cocone F :=
  { x := t.X, ι := (diagram_iso_span F).Hom ≫ t.ι }

/-- Given `F : walking_cospan ⥤ C`, which is really the same as `cospan (F.map inl) (F.map inr)`,
    and a cone on `F`, we get a pullback cone on `F.map inl` and `F.map inr`. -/
@[simps]
def pullback_cone.of_cone {F : walking_cospan ⥤ C} (t : cone F) : pullback_cone (F.map inl) (F.map inr) :=
  { x := t.X, π := t.π ≫ (diagram_iso_cospan F).Hom }

/-- Given `F : walking_span ⥤ C`, which is really the same as `span (F.map fst) (F.map snd)`,
    and a cocone on `F`, we get a pushout cocone on `F.map fst` and `F.map snd`. -/
@[simps]
def pushout_cocone.of_cocone {F : walking_span ⥤ C} (t : cocone F) : pushout_cocone (F.map fst) (F.map snd) :=
  { x := t.X, ι := (diagram_iso_span F).inv ≫ t.ι }

/--
`has_pullback f g` represents a particular choice of limiting cone
for the pair of morphisms `f : X ⟶ Z` and `g : Y ⟶ Z`.
-/
abbrev has_pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  has_limit (cospan f g)

/--
`has_pushout f g` represents a particular choice of colimiting cocone
for the pair of morphisms `f : X ⟶ Y` and `g : X ⟶ Z`.
-/
abbrev has_pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :=
  has_colimit (span f g)

/-- `pullback f g` computes the pullback of a pair of morphisms with the same target. -/
abbrev pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] :=
  limit (cospan f g)

/-- `pushout f g` computes the pushout of a pair of morphisms with the same source. -/
abbrev pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [has_pushout f g] :=
  colimit (span f g)

/-- The first projection of the pullback of `f` and `g`. -/
abbrev pullback.fst {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] : pullback f g ⟶ X :=
  limit.π (cospan f g) walking_cospan.left

/-- The second projection of the pullback of `f` and `g`. -/
abbrev pullback.snd {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] : pullback f g ⟶ Y :=
  limit.π (cospan f g) walking_cospan.right

/-- The first inclusion into the pushout of `f` and `g`. -/
abbrev pushout.inl {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] : Y ⟶ pushout f g :=
  colimit.ι (span f g) walking_span.left

/-- The second inclusion into the pushout of `f` and `g`. -/
abbrev pushout.inr {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] : Z ⟶ pushout f g :=
  colimit.ι (span f g) walking_span.right

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
    `pullback.lift : W ⟶ pullback f g`. -/
abbrev pullback.lift {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] (h : W ⟶ X) (k : W ⟶ Y)
  (w : h ≫ f = k ≫ g) : W ⟶ pullback f g :=
  limit.lift _ (pullback_cone.mk h k w)

/-- A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induces a morphism
    `pushout.desc : pushout f g ⟶ W`. -/
abbrev pushout.desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
  (w : f ≫ h = g ≫ k) : pushout f g ⟶ W :=
  colimit.desc _ (pushout_cocone.mk h k w)

@[simp, reassoc]
theorem pullback.lift_fst {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] (h : W ⟶ X) (k : W ⟶ Y)
  (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.fst = h :=
  limit.lift_π _ _

@[simp, reassoc]
theorem pullback.lift_snd {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] (h : W ⟶ X) (k : W ⟶ Y)
  (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.snd = k :=
  limit.lift_π _ _

@[simp, reassoc]
theorem pushout.inl_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
  (w : f ≫ h = g ≫ k) : pushout.inl ≫ pushout.desc h k w = h :=
  colimit.ι_desc _ _

@[simp, reassoc]
theorem pushout.inr_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
  (w : f ≫ h = g ≫ k) : pushout.inr ≫ pushout.desc h k w = k :=
  colimit.ι_desc _ _

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
    `l : W ⟶ pullback f g` such that `l ≫ pullback.fst = h` and `l ≫ pullback.snd = k`. -/
def pullback.lift' {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] (h : W ⟶ X) (k : W ⟶ Y)
  (w : h ≫ f = k ≫ g) : { l : W ⟶ pullback f g // l ≫ pullback.fst = h ∧ l ≫ pullback.snd = k } :=
  ⟨pullback.lift h k w, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

/-- A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induces a morphism
    `l : pushout f g ⟶ W` such that `pushout.inl ≫ l = h` and `pushout.inr ≫ l = k`. -/
def pullback.desc' {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) :
  { l : pushout f g ⟶ W // pushout.inl ≫ l = h ∧ pushout.inr ≫ l = k } :=
  ⟨pushout.desc h k w, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _⟩

@[reassoc]
theorem pullback.condition {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] :
  (pullback.fst : pullback f g ⟶ X) ≫ f = pullback.snd ≫ g :=
  pullback_cone.condition _

@[reassoc]
theorem pushout.condition {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] :
  f ≫ (pushout.inl : Y ⟶ pushout f g) = g ≫ pushout.inr :=
  pushout_cocone.condition _

/--
Given such a diagram, then there is a natural morphism `W ×ₛ X ⟶ Y ×ₜ Z`.

    W  ⟶  Y
      ↘      ↘
        S  ⟶  T
      ↗      ↗
    X  ⟶  Z

-/
abbrev pullback.map {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [has_pullback f₁ f₂] (g₁ : Y ⟶ T) (g₂ : Z ⟶ T)
  [has_pullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
  pullback f₁ f₂ ⟶ pullback g₁ g₂ :=
  pullback.lift (pullback.fst ≫ i₁) (pullback.snd ≫ i₂)
    (by 
      simp [←eq₁, ←eq₂, pullback.condition_assoc])

/--
Given such a diagram, then there is a natural morphism `W ⨿ₛ X ⟶ Y ⨿ₜ Z`.

        W  ⟶  Y
      ↗      ↗
    S  ⟶  T
      ↘      ↘
        X  ⟶  Z

-/
abbrev pushout.map {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [has_pushout f₁ f₂] (g₁ : T ⟶ Y) (g₂ : T ⟶ Z)
  [has_pushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁) (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) :
  pushout f₁ f₂ ⟶ pushout g₁ g₂ :=
  pushout.desc (i₁ ≫ pushout.inl) (i₂ ≫ pushout.inr)
    (by 
      simp only [←category.assoc, eq₁, eq₂]
      simp [pushout.condition])

/-- Two morphisms into a pullback are equal if their compositions with the pullback morphisms are
    equal -/
@[ext]
theorem pullback.hom_ext {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] {W : C} {k l : W ⟶ pullback f g}
  (h₀ : k ≫ pullback.fst = l ≫ pullback.fst) (h₁ : k ≫ pullback.snd = l ≫ pullback.snd) : k = l :=
  limit.hom_ext$ pullback_cone.equalizer_ext _ h₀ h₁

/-- The pullback cone built from the pullback projections is a pullback. -/
def pullback_is_pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] :
  is_limit (pullback_cone.mk (pullback.fst : pullback f g ⟶ _) pullback.snd pullback.condition) :=
  pullback_cone.is_limit.mk _ (fun s => pullback.lift s.fst s.snd s.condition)
    (by 
      simp )
    (by 
      simp )
    (by 
      tidy)

/-- The pullback of a monomorphism is a monomorphism -/
instance pullback.fst_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] [mono g] :
  mono (pullback.fst : pullback f g ⟶ X) :=
  pullback_cone.mono_fst_of_is_pullback_of_mono (limit.is_limit _)

/-- The pullback of a monomorphism is a monomorphism -/
instance pullback.snd_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] [mono f] :
  mono (pullback.snd : pullback f g ⟶ Y) :=
  pullback_cone.mono_snd_of_is_pullback_of_mono (limit.is_limit _)

/-- The map `X ×[Z] Y ⟶ X × Y` is mono. -/
instance mono_pullback_to_prod {C : Type _} [category C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g]
  [has_binary_product X Y] : mono (prod.lift pullback.fst pullback.snd : pullback f g ⟶ _) :=
  ⟨fun W i₁ i₂ h =>
      by 
        ext
        ·
          simpa using congr_argₓ (fun f => f ≫ Prod.fst) h
        ·
          simpa using congr_argₓ (fun f => f ≫ Prod.snd) h⟩

/-- Two morphisms out of a pushout are equal if their compositions with the pushout morphisms are
    equal -/
@[ext]
theorem pushout.hom_ext {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] {W : C} {k l : pushout f g ⟶ W}
  (h₀ : pushout.inl ≫ k = pushout.inl ≫ l) (h₁ : pushout.inr ≫ k = pushout.inr ≫ l) : k = l :=
  colimit.hom_ext$ pushout_cocone.coequalizer_ext _ h₀ h₁

/-- The pushout cocone built from the pushout coprojections is a pushout. -/
def pushout_is_pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [has_pushout f g] :
  is_colimit (pushout_cocone.mk (pushout.inl : _ ⟶ pushout f g) pushout.inr pushout.condition) :=
  pushout_cocone.is_colimit.mk _ (fun s => pushout.desc s.inl s.inr s.condition)
    (by 
      simp )
    (by 
      simp )
    (by 
      tidy)

/-- The pushout of an epimorphism is an epimorphism -/
instance pushout.inl_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] [epi g] :
  epi (pushout.inl : Y ⟶ pushout f g) :=
  pushout_cocone.epi_inl_of_is_pushout_of_epi (colimit.is_colimit _)

/-- The pushout of an epimorphism is an epimorphism -/
instance pushout.inr_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] [epi f] :
  epi (pushout.inr : Z ⟶ pushout f g) :=
  pushout_cocone.epi_inr_of_is_pushout_of_epi (colimit.is_colimit _)

/-- The map ` X ⨿ Y ⟶ X ⨿[Z] Y` is epi. -/
instance epi_coprod_to_pushout {C : Type _} [category C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [has_pushout f g]
  [has_binary_coproduct Y Z] : epi (coprod.desc pushout.inl pushout.inr : _ ⟶ pushout f g) :=
  ⟨fun W i₁ i₂ h =>
      by 
        ext
        ·
          simpa using congr_argₓ (fun f => coprod.inl ≫ f) h
        ·
          simpa using congr_argₓ (fun f => coprod.inr ≫ f) h⟩

section 

variable {D : Type u₂} [category.{v} D] (G : C ⥤ D)

/--
The comparison morphism for the pullback of `f,g`.
This is an isomorphism iff `G` preserves the pullback of `f,g`; see
`category_theory/limits/preserves/shapes/pullbacks.lean`
-/
def pullback_comparison (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] [has_pullback (G.map f) (G.map g)] :
  G.obj (pullback f g) ⟶ pullback (G.map f) (G.map g) :=
  pullback.lift (G.map pullback.fst) (G.map pullback.snd)
    (by 
      simp only [←G.map_comp, pullback.condition])

@[simp, reassoc]
theorem pullback_comparison_comp_fst (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] [has_pullback (G.map f) (G.map g)] :
  pullback_comparison G f g ≫ pullback.fst = G.map pullback.fst :=
  pullback.lift_fst _ _ _

@[simp, reassoc]
theorem pullback_comparison_comp_snd (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] [has_pullback (G.map f) (G.map g)] :
  pullback_comparison G f g ≫ pullback.snd = G.map pullback.snd :=
  pullback.lift_snd _ _ _

@[simp, reassoc]
theorem map_lift_pullback_comparison (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] [has_pullback (G.map f) (G.map g)]
  {W : C} {h : W ⟶ X} {k : W ⟶ Y} (w : h ≫ f = k ≫ g) :
  G.map (pullback.lift _ _ w) ≫ pullback_comparison G f g =
    pullback.lift (G.map h) (G.map k)
      (by 
        simp only [←G.map_comp, w]) :=
  by 
    ext <;> simp [←G.map_comp]

end 

section PullbackSymmetry

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z)

/-- Making this a global instance would make the typeclass seach go in an infinite loop. -/
theorem has_pullback_symmetry [has_pullback f g] : has_pullback g f :=
  ⟨⟨⟨pullback_cone.mk _ _ pullback.condition.symm, pullback_cone.flip_is_limit (pullback_is_pullback _ _)⟩⟩⟩

attribute [local instance] has_pullback_symmetry

/-- The isomorphism `X ×[Z] Y ≅ Y ×[Z] X`. -/
def pullback_symmetry [has_pullback f g] : pullback f g ≅ pullback g f :=
  is_limit.cone_point_unique_up_to_iso
    (pullback_cone.flip_is_limit (pullback_is_pullback f g) : is_limit (pullback_cone.mk _ _ pullback.condition.symm))
    (limit.is_limit _)

@[simp, reassoc]
theorem pullback_symmetry_hom_comp_fst [has_pullback f g] : (pullback_symmetry f g).Hom ≫ pullback.fst = pullback.snd :=
  by 
    simp [pullback_symmetry]

@[simp, reassoc]
theorem pullback_symmetry_hom_comp_snd [has_pullback f g] : (pullback_symmetry f g).Hom ≫ pullback.snd = pullback.fst :=
  by 
    simp [pullback_symmetry]

@[simp, reassoc]
theorem pullback_symmetry_inv_comp_fst [has_pullback f g] : (pullback_symmetry f g).inv ≫ pullback.fst = pullback.snd :=
  by 
    simp [iso.inv_comp_eq]

@[simp, reassoc]
theorem pullback_symmetry_inv_comp_snd [has_pullback f g] : (pullback_symmetry f g).inv ≫ pullback.snd = pullback.fst :=
  by 
    simp [iso.inv_comp_eq]

end PullbackSymmetry

section PushoutSymmetry

open WalkingCospan

variable (f : X ⟶ Y) (g : X ⟶ Z)

/-- Making this a global instance would make the typeclass seach go in an infinite loop. -/
theorem has_pushout_symmetry [has_pushout f g] : has_pushout g f :=
  ⟨⟨⟨pushout_cocone.mk _ _ pushout.condition.symm, pushout_cocone.flip_is_colimit (pushout_is_pushout _ _)⟩⟩⟩

attribute [local instance] has_pushout_symmetry

/-- The isomorphism `Y ⨿[X] Z ≅ Z ⨿[X] Y`. -/
def pushout_symmetry [has_pushout f g] : pushout f g ≅ pushout g f :=
  is_colimit.cocone_point_unique_up_to_iso
    (pushout_cocone.flip_is_colimit (pushout_is_pushout f g) :
    is_colimit (pushout_cocone.mk _ _ pushout.condition.symm))
    (colimit.is_colimit _)

@[simp, reassoc]
theorem inl_comp_pushout_symmetry_hom [has_pushout f g] : pushout.inl ≫ (pushout_symmetry f g).Hom = pushout.inr :=
  (colimit.is_colimit (span f g)).comp_cocone_point_unique_up_to_iso_hom
    (pushout_cocone.flip_is_colimit (pushout_is_pushout g f)) _

@[simp, reassoc]
theorem inr_comp_pushout_symmetry_hom [has_pushout f g] : pushout.inr ≫ (pushout_symmetry f g).Hom = pushout.inl :=
  (colimit.is_colimit (span f g)).comp_cocone_point_unique_up_to_iso_hom
    (pushout_cocone.flip_is_colimit (pushout_is_pushout g f)) _

@[simp, reassoc]
theorem inl_comp_pushout_symmetry_inv [has_pushout f g] : pushout.inl ≫ (pushout_symmetry f g).inv = pushout.inr :=
  by 
    simp [iso.comp_inv_eq]

@[simp, reassoc]
theorem inr_comp_pushout_symmetry_inv [has_pushout f g] : pushout.inr ≫ (pushout_symmetry f g).inv = pushout.inl :=
  by 
    simp [iso.comp_inv_eq]

end PushoutSymmetry

section PullbackLeftIso

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z) [is_iso f]

/-- If `f : X ⟶ Z` is iso, then `X ×[Z] Y ≅ Y`. This is the explicit limit cone. -/
def pullback_cone_of_left_iso : pullback_cone f g :=
  pullback_cone.mk (g ≫ inv f) (𝟙 _)$
    by 
      simp 

@[simp]
theorem pullback_cone_of_left_iso_X : (pullback_cone_of_left_iso f g).x = Y :=
  rfl

@[simp]
theorem pullback_cone_of_left_iso_fst : (pullback_cone_of_left_iso f g).fst = g ≫ inv f :=
  rfl

@[simp]
theorem pullback_cone_of_left_iso_snd : (pullback_cone_of_left_iso f g).snd = 𝟙 _ :=
  rfl

@[simp]
theorem pullback_cone_of_left_iso_π_app_none : (pullback_cone_of_left_iso f g).π.app none = g :=
  by 
    delta' pullback_cone_of_left_iso 
    simp 

@[simp]
theorem pullback_cone_of_left_iso_π_app_left : (pullback_cone_of_left_iso f g).π.app left = g ≫ inv f :=
  rfl

@[simp]
theorem pullback_cone_of_left_iso_π_app_right : (pullback_cone_of_left_iso f g).π.app right = 𝟙 _ :=
  rfl

/-- Verify that the constructed limit cone is indeed a limit. -/
def pullback_cone_of_left_iso_is_limit : is_limit (pullback_cone_of_left_iso f g) :=
  pullback_cone.is_limit_aux' _
    fun s =>
      ⟨s.snd,
        by 
          simp [←s.condition_assoc]⟩

theorem has_pullback_of_left_iso : has_pullback f g :=
  ⟨⟨⟨_, pullback_cone_of_left_iso_is_limit f g⟩⟩⟩

attribute [local instance] has_pullback_of_left_iso

instance pullback_snd_iso_of_left_iso : is_iso (pullback.snd : pullback f g ⟶ _) :=
  by 
    refine'
      ⟨⟨pullback.lift (g ≫ inv f) (𝟙 _)
            (by 
              simp ),
          _,
          by 
            simp ⟩⟩
    ext
    ·
      simp [←pullback.condition_assoc]
    ·
      simp [pullback.condition_assoc]

end PullbackLeftIso

section PullbackRightIso

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z) [is_iso g]

/-- If `g : Y ⟶ Z` is iso, then `X ×[Z] Y ≅ X`. This is the explicit limit cone. -/
def pullback_cone_of_right_iso : pullback_cone f g :=
  pullback_cone.mk (𝟙 _) (f ≫ inv g)$
    by 
      simp 

@[simp]
theorem pullback_cone_of_right_iso_X : (pullback_cone_of_right_iso f g).x = X :=
  rfl

@[simp]
theorem pullback_cone_of_right_iso_fst : (pullback_cone_of_right_iso f g).fst = 𝟙 _ :=
  rfl

@[simp]
theorem pullback_cone_of_right_iso_snd : (pullback_cone_of_right_iso f g).snd = f ≫ inv g :=
  rfl

@[simp]
theorem pullback_cone_of_right_iso_π_app_none : (pullback_cone_of_right_iso f g).π.app none = f :=
  category.id_comp _

@[simp]
theorem pullback_cone_of_right_iso_π_app_left : (pullback_cone_of_right_iso f g).π.app left = 𝟙 _ :=
  rfl

@[simp]
theorem pullback_cone_of_right_iso_π_app_right : (pullback_cone_of_right_iso f g).π.app right = f ≫ inv g :=
  rfl

/-- Verify that the constructed limit cone is indeed a limit. -/
def pullback_cone_of_right_iso_is_limit : is_limit (pullback_cone_of_right_iso f g) :=
  pullback_cone.is_limit_aux' _
    fun s =>
      ⟨s.fst,
        by 
          simp [s.condition_assoc]⟩

theorem has_pullback_of_right_iso : has_pullback f g :=
  ⟨⟨⟨_, pullback_cone_of_right_iso_is_limit f g⟩⟩⟩

attribute [local instance] has_pullback_of_right_iso

instance pullback_snd_iso_of_right_iso : is_iso (pullback.fst : pullback f g ⟶ _) :=
  by 
    refine'
      ⟨⟨pullback.lift (𝟙 _) (f ≫ inv g)
            (by 
              simp ),
          _,
          by 
            simp ⟩⟩
    ext
    ·
      simp 
    ·
      simp [pullback.condition_assoc]

end PullbackRightIso

section PushoutLeftIso

open WalkingSpan

variable (f : X ⟶ Y) (g : X ⟶ Z) [is_iso f]

/-- If `f : X ⟶ Y` is iso, then `Y ⨿[X] Z ≅ Z`. This is the explicit colimit cocone. -/
def pushout_cocone_of_left_iso : pushout_cocone f g :=
  pushout_cocone.mk (inv f ≫ g) (𝟙 _)$
    by 
      simp 

@[simp]
theorem pushout_cocone_of_left_iso_X : (pushout_cocone_of_left_iso f g).x = Z :=
  rfl

@[simp]
theorem pushout_cocone_of_left_iso_inl : (pushout_cocone_of_left_iso f g).inl = inv f ≫ g :=
  rfl

@[simp]
theorem pushout_cocone_of_left_iso_inr : (pushout_cocone_of_left_iso f g).inr = 𝟙 _ :=
  rfl

@[simp]
theorem pushout_cocone_of_left_iso_ι_app_none : (pushout_cocone_of_left_iso f g).ι.app none = g :=
  by 
    delta' pushout_cocone_of_left_iso 
    simp 

@[simp]
theorem pushout_cocone_of_left_iso_ι_app_left : (pushout_cocone_of_left_iso f g).ι.app left = inv f ≫ g :=
  rfl

@[simp]
theorem pushout_cocone_of_left_iso_ι_app_right : (pushout_cocone_of_left_iso f g).ι.app right = 𝟙 _ :=
  rfl

/-- Verify that the constructed cocone is indeed a colimit. -/
def pushout_cocone_of_left_iso_is_limit : is_colimit (pushout_cocone_of_left_iso f g) :=
  pushout_cocone.is_colimit_aux' _
    fun s =>
      ⟨s.inr,
        by 
          simp [←s.condition]⟩

theorem has_pushout_of_left_iso : has_pushout f g :=
  ⟨⟨⟨_, pushout_cocone_of_left_iso_is_limit f g⟩⟩⟩

attribute [local instance] has_pushout_of_left_iso

instance pushout_inr_iso_of_left_iso : is_iso (pushout.inr : _ ⟶ pushout f g) :=
  by 
    refine'
      ⟨⟨pushout.desc (inv f ≫ g) (𝟙 _)
            (by 
              simp ),
          by 
            simp ,
          _⟩⟩
    ext
    ·
      simp [←pushout.condition]
    ·
      simp [pushout.condition_assoc]

end PushoutLeftIso

section PushoutRightIso

open WalkingSpan

variable (f : X ⟶ Y) (g : X ⟶ Z) [is_iso g]

/-- If `f : X ⟶ Z` is iso, then `Y ⨿[X] Z ≅ Y`. This is the explicit colimit cocone. -/
def pushout_cocone_of_right_iso : pushout_cocone f g :=
  pushout_cocone.mk (𝟙 _) (inv g ≫ f)$
    by 
      simp 

@[simp]
theorem pushout_cocone_of_right_iso_X : (pushout_cocone_of_right_iso f g).x = Y :=
  rfl

@[simp]
theorem pushout_cocone_of_right_iso_inl : (pushout_cocone_of_right_iso f g).inl = 𝟙 _ :=
  rfl

@[simp]
theorem pushout_cocone_of_right_iso_inr : (pushout_cocone_of_right_iso f g).inr = inv g ≫ f :=
  rfl

@[simp]
theorem pushout_cocone_of_right_iso_ι_app_none : (pushout_cocone_of_right_iso f g).ι.app none = f :=
  by 
    delta' pushout_cocone_of_right_iso 
    simp 

@[simp]
theorem pushout_cocone_of_right_iso_ι_app_left : (pushout_cocone_of_right_iso f g).ι.app left = 𝟙 _ :=
  rfl

@[simp]
theorem pushout_cocone_of_right_iso_ι_app_right : (pushout_cocone_of_right_iso f g).ι.app right = inv g ≫ f :=
  rfl

/-- Verify that the constructed cocone is indeed a colimit. -/
def pushout_cocone_of_right_iso_is_limit : is_colimit (pushout_cocone_of_right_iso f g) :=
  pushout_cocone.is_colimit_aux' _
    fun s =>
      ⟨s.inl,
        by 
          simp [←s.condition]⟩

theorem has_pushout_of_right_iso : has_pushout f g :=
  ⟨⟨⟨_, pushout_cocone_of_right_iso_is_limit f g⟩⟩⟩

attribute [local instance] has_pushout_of_right_iso

instance pushout_inl_iso_of_right_iso : is_iso (pushout.inl : _ ⟶ pushout f g) :=
  by 
    refine'
      ⟨⟨pushout.desc (𝟙 _) (inv g ≫ f)
            (by 
              simp ),
          by 
            simp ,
          _⟩⟩
    ext
    ·
      simp [←pushout.condition]
    ·
      simp [pushout.condition]

end PushoutRightIso

section 

open WalkingCospan

variable (f : X ⟶ Y)

instance has_kernel_pair_of_mono [mono f] : has_pullback f f :=
  ⟨⟨⟨_, pullback_cone.is_limit_mk_id_id f⟩⟩⟩

theorem fst_eq_snd_of_mono_eq [mono f] : (pullback.fst : pullback f f ⟶ _) = pullback.snd :=
  ((pullback_cone.is_limit_mk_id_id f).fac (get_limit_cone (cospan f f)).Cone left).symm.trans
    ((pullback_cone.is_limit_mk_id_id f).fac (get_limit_cone (cospan f f)).Cone right : _)

@[simp]
theorem pullback_symmetry_hom_of_mono_eq [mono f] : (pullback_symmetry f f).Hom = 𝟙 _ :=
  by 
    ext <;> simp [fst_eq_snd_of_mono_eq]

instance fst_iso_of_mono_eq [mono f] : is_iso (pullback.fst : pullback f f ⟶ _) :=
  by 
    refine'
      ⟨⟨pullback.lift (𝟙 _) (𝟙 _)
            (by 
              simp ),
          _,
          by 
            simp ⟩⟩
    ext
    ·
      simp 
    ·
      simp [fst_eq_snd_of_mono_eq]

instance snd_iso_of_mono_eq [mono f] : is_iso (pullback.snd : pullback f f ⟶ _) :=
  by 
    rw [←fst_eq_snd_of_mono_eq]
    infer_instance

end 

section 

open WalkingSpan

variable (f : X ⟶ Y)

instance has_cokernel_pair_of_epi [epi f] : has_pushout f f :=
  ⟨⟨⟨_, pushout_cocone.is_colimit_mk_id_id f⟩⟩⟩

theorem inl_eq_inr_of_epi_eq [epi f] : (pushout.inl : _ ⟶ pushout f f) = pushout.inr :=
  ((pushout_cocone.is_colimit_mk_id_id f).fac (get_colimit_cocone (span f f)).Cocone left).symm.trans
    ((pushout_cocone.is_colimit_mk_id_id f).fac (get_colimit_cocone (span f f)).Cocone right : _)

@[simp]
theorem pullback_symmetry_hom_of_epi_eq [epi f] : (pushout_symmetry f f).Hom = 𝟙 _ :=
  by 
    ext <;> simp [inl_eq_inr_of_epi_eq]

instance inl_iso_of_epi_eq [epi f] : is_iso (pushout.inl : _ ⟶ pushout f f) :=
  by 
    refine'
      ⟨⟨pushout.desc (𝟙 _) (𝟙 _)
            (by 
              simp ),
          by 
            simp ,
          _⟩⟩
    ext
    ·
      simp 
    ·
      simp [inl_eq_inr_of_epi_eq]

instance inr_iso_of_epi_eq [epi f] : is_iso (pushout.inr : _ ⟶ pushout f f) :=
  by 
    rw [←inl_eq_inr_of_epi_eq]
    infer_instance

end 

variable (C)

/--
`has_pullbacks` represents a choice of pullback for every pair of morphisms

See https://stacks.math.columbia.edu/tag/001W.
-/
abbrev has_pullbacks :=
  has_limits_of_shape walking_cospan.{v} C

/-- `has_pushouts` represents a choice of pushout for every pair of morphisms -/
abbrev has_pushouts :=
  has_colimits_of_shape walking_span.{v} C

/-- If `C` has all limits of diagrams `cospan f g`, then it has all pullbacks -/
theorem has_pullbacks_of_has_limit_cospan [∀ {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}, has_limit (cospan f g)] :
  has_pullbacks C :=
  { HasLimit := fun F => has_limit_of_iso (diagram_iso_cospan F).symm }

/-- If `C` has all colimits of diagrams `span f g`, then it has all pushouts -/
theorem has_pushouts_of_has_colimit_span [∀ {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}, has_colimit (span f g)] :
  has_pushouts C :=
  { HasColimit := fun F => has_colimit_of_iso (diagram_iso_span F) }

end CategoryTheory.Limits

