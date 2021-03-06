/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Shapes.Terminal
import Mathbin.CategoryTheory.DiscreteCategory
import Mathbin.CategoryTheory.EpiMono
import Mathbin.CategoryTheory.Over

/-!
# Binary (co)products

We define a category `walking_pair`, which is the index category
for a binary (co)product diagram. A convenience method `pair X Y`
constructs the functor from the walking pair, hitting the given objects.

We define `prod X Y` and `coprod X Y` as limits and colimits of such functors.

Typeclasses `has_binary_products` and `has_binary_coproducts` assert the existence
of (co)limits shaped as walking pairs.

We include lemmas for simplifying equations involving projections and coprojections, and define
braiding and associating isomorphisms, and the product comparison morphism.

## References
* [Stacks: Products of pairs](https://stacks.math.columbia.edu/tag/001R)
* [Stacks: coproducts of pairs](https://stacks.math.columbia.edu/tag/04AN)
-/


noncomputable section

universe v u uā

open CategoryTheory

namespace CategoryTheory.Limits

/-- The type of objects for the diagram indexing a binary (co)product. -/
inductive WalkingPair : Type
  | left
  | right
  deriving DecidableEq, Inhabited

open WalkingPair

/-- The equivalence swapping left and right.
-/
def WalkingPair.swap : walking_pair ā walking_pair where
  toFun := fun j => WalkingPair.recOn j right left
  invFun := fun j => WalkingPair.recOn j right left
  left_inv := fun j => by
    cases j <;> rfl
  right_inv := fun j => by
    cases j <;> rfl

@[simp]
theorem WalkingPair.swap_apply_left : WalkingPair.swap left = right :=
  rfl

@[simp]
theorem WalkingPair.swap_apply_right : WalkingPair.swap right = left :=
  rfl

@[simp]
theorem WalkingPair.swap_symm_apply_tt : WalkingPair.swap.symm left = right :=
  rfl

@[simp]
theorem WalkingPair.swap_symm_apply_ff : WalkingPair.swap.symm right = left :=
  rfl

/-- An equivalence from `walking_pair` to `bool`, sometimes useful when reindexing limits.
-/
def WalkingPair.equivBool : walking_pair ā Bool where
  toFun := fun j => WalkingPair.recOn j true false
  -- to match equiv.sum_equiv_sigma_bool
  invFun := fun b => Bool.recOn b right left
  left_inv := fun j => by
    cases j <;> rfl
  right_inv := fun b => by
    cases b <;> rfl

@[simp]
theorem WalkingPair.equiv_bool_apply_left : WalkingPair.equivBool left = tt :=
  rfl

@[simp]
theorem WalkingPair.equiv_bool_apply_right : WalkingPair.equivBool right = ff :=
  rfl

@[simp]
theorem WalkingPair.equiv_bool_symm_apply_tt : WalkingPair.equivBool.symm true = left :=
  rfl

@[simp]
theorem WalkingPair.equiv_bool_symm_apply_ff : WalkingPair.equivBool.symm false = right :=
  rfl

variable {C : Type u}

/-- The function on the walking pair, sending the two points to `X` and `Y`. -/
def pairFunction (X Y : C) : WalkingPair ā C := fun j => WalkingPair.casesOn j X Y

@[simp]
theorem pair_function_left (X Y : C) : pairFunction X Y left = X :=
  rfl

@[simp]
theorem pair_function_right (X Y : C) : pairFunction X Y right = Y :=
  rfl

variable [Category.{v} C]

/-- The diagram on the walking pair, sending the two points to `X` and `Y`. -/
def pair (X Y : C) : Discrete WalkingPair ā„¤ C :=
  Discrete.functor fun j => WalkingPair.casesOn j X Y

@[simp]
theorem pair_obj_left (X Y : C) : (pair X Y).obj āØleftā© = X :=
  rfl

@[simp]
theorem pair_obj_right (X Y : C) : (pair X Y).obj āØrightā© = Y :=
  rfl

section

variable {F G : Discrete WalkingPair ā„¤ C} (f : F.obj āØleftā© ā¶ G.obj āØleftā©) (g : F.obj āØrightā© ā¶ G.obj āØrightā©)

attribute [local tidy] tactic.discrete_cases

/-- The natural transformation between two functors out of the
 walking pair, specified by its
components. -/
def mapPair : F ā¶ G where app := fun j => Discrete.recOn j fun j => WalkingPair.casesOn j f g

@[simp]
theorem map_pair_left : (mapPair f g).app āØleftā© = f :=
  rfl

@[simp]
theorem map_pair_right : (mapPair f g).app āØrightā© = g :=
  rfl

/-- The natural isomorphism between two functors out of the walking pair, specified by its
components. -/
@[simps]
def mapPairIso (f : F.obj āØleftā© ā G.obj āØleftā©) (g : F.obj āØrightā© ā G.obj āØrightā©) : F ā G :=
  NatIso.ofComponents (fun j => Discrete.recOn j fun j => WalkingPair.casesOn j f g)
    (by
      tidy)

end

/-- Every functor out of the walking pair is naturally isomorphic (actually, equal) to a `pair` -/
@[simps]
def diagramIsoPair (F : Discrete WalkingPair ā„¤ C) : F ā pair (F.obj āØWalkingPair.leftā©) (F.obj āØWalkingPair.rightā©) :=
  mapPairIso (Iso.refl _) (Iso.refl _)

section

variable {D : Type u} [Category.{v} D]

/-- The natural isomorphism between `pair X Y ā F` and `pair (F.obj X) (F.obj Y)`. -/
def pairComp (X Y : C) (F : C ā„¤ D) : pair X Y ā F ā pair (F.obj X) (F.obj Y) :=
  diagramIsoPair _

end

/-- A binary fan is just a cone on a diagram indexing a product. -/
abbrev BinaryFan (X Y : C) :=
  Cone (pair X Y)

/-- The first projection of a binary fan. -/
abbrev BinaryFan.fst {X Y : C} (s : BinaryFan X Y) :=
  s.Ļ.app āØWalkingPair.leftā©

/-- The second projection of a binary fan. -/
abbrev BinaryFan.snd {X Y : C} (s : BinaryFan X Y) :=
  s.Ļ.app āØWalkingPair.rightā©

@[simp]
theorem BinaryFan.Ļ_app_left {X Y : C} (s : BinaryFan X Y) : s.Ļ.app āØWalkingPair.leftā© = s.fst :=
  rfl

@[simp]
theorem BinaryFan.Ļ_app_right {X Y : C} (s : BinaryFan X Y) : s.Ļ.app āØWalkingPair.rightā© = s.snd :=
  rfl

/-- A convenient way to show that a binary fan is a limit. -/
def BinaryFan.IsLimit.mk {X Y : C} (s : BinaryFan X Y) (lift : ā {T : C} (f : T ā¶ X) (g : T ā¶ Y), T ā¶ s.x)
    (hlā : ā {T : C} (f : T ā¶ X) (g : T ā¶ Y), lift f g ā« s.fst = f)
    (hlā : ā {T : C} (f : T ā¶ X) (g : T ā¶ Y), lift f g ā« s.snd = g)
    (uniq : ā {T : C} (f : T ā¶ X) (g : T ā¶ Y) (m : T ā¶ s.x) (hā : m ā« s.fst = f) (hā : m ā« s.snd = g), m = lift f g) :
    IsLimit s :=
  IsLimit.mk (fun t => lift (BinaryFan.fst t) (BinaryFan.snd t))
    (by
      rintro t (rfl | rfl)
      Ā· exact hlā _ _
        
      Ā· exact hlā _ _
        )
    fun t m h => uniq _ _ _ (h āØWalkingPair.leftā©) (h āØWalkingPair.rightā©)

theorem BinaryFan.IsLimit.hom_ext {W X Y : C} {s : BinaryFan X Y} (h : IsLimit s) {f g : W ā¶ s.x}
    (hā : f ā« s.fst = g ā« s.fst) (hā : f ā« s.snd = g ā« s.snd) : f = g :=
  h.hom_ext fun j => Discrete.recOn j fun j => WalkingPair.casesOn j hā hā

/-- A binary cofan is just a cocone on a diagram indexing a coproduct. -/
abbrev BinaryCofan (X Y : C) :=
  Cocone (pair X Y)

/-- The first inclusion of a binary cofan. -/
abbrev BinaryCofan.inl {X Y : C} (s : BinaryCofan X Y) :=
  s.Ī¹.app āØWalkingPair.leftā©

/-- The second inclusion of a binary cofan. -/
abbrev BinaryCofan.inr {X Y : C} (s : BinaryCofan X Y) :=
  s.Ī¹.app āØWalkingPair.rightā©

@[simp]
theorem BinaryCofan.Ī¹_app_left {X Y : C} (s : BinaryCofan X Y) : s.Ī¹.app āØWalkingPair.leftā© = s.inl :=
  rfl

@[simp]
theorem BinaryCofan.Ī¹_app_right {X Y : C} (s : BinaryCofan X Y) : s.Ī¹.app āØWalkingPair.rightā© = s.inr :=
  rfl

/-- A convenient way to show that a binary cofan is a colimit. -/
def BinaryCofan.IsColimit.mk {X Y : C} (s : BinaryCofan X Y) (desc : ā {T : C} (f : X ā¶ T) (g : Y ā¶ T), s.x ā¶ T)
    (hdā : ā {T : C} (f : X ā¶ T) (g : Y ā¶ T), s.inl ā« desc f g = f)
    (hdā : ā {T : C} (f : X ā¶ T) (g : Y ā¶ T), s.inr ā« desc f g = g)
    (uniq : ā {T : C} (f : X ā¶ T) (g : Y ā¶ T) (m : s.x ā¶ T) (hā : s.inl ā« m = f) (hā : s.inr ā« m = g), m = desc f g) :
    IsColimit s :=
  IsColimit.mk (fun t => desc (BinaryCofan.inl t) (BinaryCofan.inr t))
    (by
      rintro t (rfl | rfl)
      Ā· exact hdā _ _
        
      Ā· exact hdā _ _
        )
    fun t m h => uniq _ _ _ (h āØWalkingPair.leftā©) (h āØWalkingPair.rightā©)

theorem BinaryCofan.IsColimit.hom_ext {W X Y : C} {s : BinaryCofan X Y} (h : IsColimit s) {f g : s.x ā¶ W}
    (hā : s.inl ā« f = s.inl ā« g) (hā : s.inr ā« f = s.inr ā« g) : f = g :=
  h.hom_ext fun j => Discrete.recOn j fun j => WalkingPair.casesOn j hā hā

variable {X Y : C}

section

attribute [local tidy] tactic.discrete_cases

/-- A binary fan with vertex `P` consists of the two projections `Ļā : P ā¶ X` and `Ļā : P ā¶ Y`. -/
@[simps x]
def BinaryFan.mk {P : C} (Ļā : P ā¶ X) (Ļā : P ā¶ Y) : BinaryFan X Y where
  x := P
  Ļ := { app := fun j => Discrete.recOn j fun j => WalkingPair.casesOn j Ļā Ļā }

/-- A binary cofan with vertex `P` consists of the two inclusions `Ī¹ā : X ā¶ P` and `Ī¹ā : Y ā¶ P`. -/
@[simps x]
def BinaryCofan.mk {P : C} (Ī¹ā : X ā¶ P) (Ī¹ā : Y ā¶ P) : BinaryCofan X Y where
  x := P
  Ī¹ := { app := fun j => Discrete.recOn j fun j => WalkingPair.casesOn j Ī¹ā Ī¹ā }

end

@[simp]
theorem BinaryFan.mk_fst {P : C} (Ļā : P ā¶ X) (Ļā : P ā¶ Y) : (BinaryFan.mk Ļā Ļā).fst = Ļā :=
  rfl

@[simp]
theorem BinaryFan.mk_snd {P : C} (Ļā : P ā¶ X) (Ļā : P ā¶ Y) : (BinaryFan.mk Ļā Ļā).snd = Ļā :=
  rfl

@[simp]
theorem BinaryCofan.mk_inl {P : C} (Ī¹ā : X ā¶ P) (Ī¹ā : Y ā¶ P) : (BinaryCofan.mk Ī¹ā Ī¹ā).inl = Ī¹ā :=
  rfl

@[simp]
theorem BinaryCofan.mk_inr {P : C} (Ī¹ā : X ā¶ P) (Ī¹ā : Y ā¶ P) : (BinaryCofan.mk Ī¹ā Ī¹ā).inr = Ī¹ā :=
  rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]
/-- Every `binary_fan` is isomorphic to an application of `binary_fan.mk`. -/
def isoBinaryFanMk {X Y : C} (c : BinaryFan X Y) : c ā BinaryFan.mk c.fst c.snd :=
  Cones.ext (Iso.refl _) fun j => by
    trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]" <;>
      cases j <;> tidy

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]
/-- Every `binary_fan` is isomorphic to an application of `binary_fan.mk`. -/
def isoBinaryCofanMk {X Y : C} (c : BinaryCofan X Y) : c ā BinaryCofan.mk c.inl c.inr :=
  Cocones.ext (Iso.refl _) fun j => by
    trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]" <;>
      cases j <;> tidy

/-- If `s` is a limit binary fan over `X` and `Y`, then every pair of morphisms `f : W ā¶ X` and
    `g : W ā¶ Y` induces a morphism `l : W ā¶ s.X` satisfying `l ā« s.fst = f` and `l ā« s.snd = g`.
    -/
@[simps]
def BinaryFan.IsLimit.lift' {W X Y : C} {s : BinaryFan X Y} (h : IsLimit s) (f : W ā¶ X) (g : W ā¶ Y) :
    { l : W ā¶ s.x // l ā« s.fst = f ā§ l ā« s.snd = g } :=
  āØh.lift <| BinaryFan.mk f g, h.fac _ _, h.fac _ _ā©

/-- If `s` is a colimit binary cofan over `X` and `Y`,, then every pair of morphisms `f : X ā¶ W` and
    `g : Y ā¶ W` induces a morphism `l : s.X ā¶ W` satisfying `s.inl ā« l = f` and `s.inr ā« l = g`.
    -/
@[simps]
def BinaryCofan.IsColimit.desc' {W X Y : C} {s : BinaryCofan X Y} (h : IsColimit s) (f : X ā¶ W) (g : Y ā¶ W) :
    { l : s.x ā¶ W // s.inl ā« l = f ā§ s.inr ā« l = g } :=
  āØh.desc <| BinaryCofan.mk f g, h.fac _ _, h.fac _ _ā©

/-- An abbreviation for `has_limit (pair X Y)`. -/
abbrev HasBinaryProduct (X Y : C) :=
  HasLimit (pair X Y)

/-- An abbreviation for `has_colimit (pair X Y)`. -/
abbrev HasBinaryCoproduct (X Y : C) :=
  HasColimit (pair X Y)

/-- If we have a product of `X` and `Y`, we can access it using `prod X Y` or
    `X āØÆ Y`. -/
abbrev prod (X Y : C) [HasBinaryProduct X Y] :=
  limit (pair X Y)

/-- If we have a coproduct of `X` and `Y`, we can access it using `coprod X Y ` or
    `X āØæ Y`. -/
abbrev coprod (X Y : C) [HasBinaryCoproduct X Y] :=
  colimit (pair X Y)

-- mathport name: Ā«expr āØÆ Ā»
notation:20 X " āØÆ " Y:20 => prod X Y

-- mathport name: Ā«expr āØæ Ā»
notation:20 X " āØæ " Y:20 => coprod X Y

/-- The projection map to the first component of the product. -/
abbrev prod.fst {X Y : C} [HasBinaryProduct X Y] : X āØÆ Y ā¶ X :=
  limit.Ļ (pair X Y) āØWalkingPair.leftā©

/-- The projecton map to the second component of the product. -/
abbrev prod.snd {X Y : C} [HasBinaryProduct X Y] : X āØÆ Y ā¶ Y :=
  limit.Ļ (pair X Y) āØWalkingPair.rightā©

/-- The inclusion map from the first component of the coproduct. -/
abbrev coprod.inl {X Y : C} [HasBinaryCoproduct X Y] : X ā¶ X āØæ Y :=
  colimit.Ī¹ (pair X Y) āØWalkingPair.leftā©

/-- The inclusion map from the second component of the coproduct. -/
abbrev coprod.inr {X Y : C} [HasBinaryCoproduct X Y] : Y ā¶ X āØæ Y :=
  colimit.Ī¹ (pair X Y) āØWalkingPair.rightā©

/-- The binary fan constructed from the projection maps is a limit. -/
def prodIsProd (X Y : C) [HasBinaryProduct X Y] : IsLimit (BinaryFan.mk (prod.fst : X āØÆ Y ā¶ X) prod.snd) :=
  (limit.isLimit _).ofIsoLimit
    (Cones.ext (Iso.refl _)
      (by
        rintro (_ | _)
        tidy))

/-- The binary cofan constructed from the coprojection maps is a colimit. -/
def coprodIsCoprod (X Y : C) [HasBinaryCoproduct X Y] :
    IsColimit (BinaryCofan.mk (coprod.inl : X ā¶ X āØæ Y) coprod.inr) :=
  (colimit.isColimit _).ofIsoColimit
    (Cocones.ext (Iso.refl _)
      (by
        rintro (_ | _)
        tidy))

@[ext]
theorem prod.hom_ext {W X Y : C} [HasBinaryProduct X Y] {f g : W ā¶ X āØÆ Y} (hā : f ā« Prod.fst = g ā« Prod.fst)
    (hā : f ā« Prod.snd = g ā« Prod.snd) : f = g :=
  BinaryFan.IsLimit.hom_ext (limit.isLimit _) hā hā

@[ext]
theorem coprod.hom_ext {W X Y : C} [HasBinaryCoproduct X Y] {f g : X āØæ Y ā¶ W} (hā : coprod.inl ā« f = coprod.inl ā« g)
    (hā : coprod.inr ā« f = coprod.inr ā« g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (colimit.isColimit _) hā hā

/-- If the product of `X` and `Y` exists, then every pair of morphisms `f : W ā¶ X` and `g : W ā¶ Y`
    induces a morphism `prod.lift f g : W ā¶ X āØÆ Y`. -/
abbrev prod.lift {W X Y : C} [HasBinaryProduct X Y] (f : W ā¶ X) (g : W ā¶ Y) : W ā¶ X āØÆ Y :=
  limit.lift _ (BinaryFan.mk f g)

/-- diagonal arrow of the binary product in the category `fam I` -/
abbrev diag (X : C) [HasBinaryProduct X X] : X ā¶ X āØÆ X :=
  prod.lift (š _) (š _)

/-- If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ā¶ W` and
    `g : Y ā¶ W` induces a morphism `coprod.desc f g : X āØæ Y ā¶ W`. -/
abbrev coprod.desc {W X Y : C} [HasBinaryCoproduct X Y] (f : X ā¶ W) (g : Y ā¶ W) : X āØæ Y ā¶ W :=
  colimit.desc _ (BinaryCofan.mk f g)

/-- codiagonal arrow of the binary coproduct -/
abbrev codiag (X : C) [HasBinaryCoproduct X X] : X āØæ X ā¶ X :=
  coprod.desc (š _) (š _)

@[simp, reassoc]
theorem prod.lift_fst {W X Y : C} [HasBinaryProduct X Y] (f : W ā¶ X) (g : W ā¶ Y) : prod.lift f g ā« Prod.fst = f :=
  limit.lift_Ļ _ _

@[simp, reassoc]
theorem prod.lift_snd {W X Y : C} [HasBinaryProduct X Y] (f : W ā¶ X) (g : W ā¶ Y) : prod.lift f g ā« Prod.snd = g :=
  limit.lift_Ļ _ _

-- The simp linter says simp can prove the reassoc version of this lemma.
@[reassoc, simp]
theorem coprod.inl_desc {W X Y : C} [HasBinaryCoproduct X Y] (f : X ā¶ W) (g : Y ā¶ W) :
    coprod.inl ā« coprod.desc f g = f :=
  colimit.Ī¹_desc _ _

-- The simp linter says simp can prove the reassoc version of this lemma.
@[reassoc, simp]
theorem coprod.inr_desc {W X Y : C} [HasBinaryCoproduct X Y] (f : X ā¶ W) (g : Y ā¶ W) :
    coprod.inr ā« coprod.desc f g = g :=
  colimit.Ī¹_desc _ _

instance prod.mono_lift_of_mono_left {W X Y : C} [HasBinaryProduct X Y] (f : W ā¶ X) (g : W ā¶ Y) [Mono f] :
    Mono (prod.lift f g) :=
  mono_of_mono_fac <| prod.lift_fst _ _

instance prod.mono_lift_of_mono_right {W X Y : C} [HasBinaryProduct X Y] (f : W ā¶ X) (g : W ā¶ Y) [Mono g] :
    Mono (prod.lift f g) :=
  mono_of_mono_fac <| prod.lift_snd _ _

instance coprod.epi_desc_of_epi_left {W X Y : C} [HasBinaryCoproduct X Y] (f : X ā¶ W) (g : Y ā¶ W) [Epi f] :
    Epi (coprod.desc f g) :=
  epi_of_epi_fac <| coprod.inl_desc _ _

instance coprod.epi_desc_of_epi_right {W X Y : C} [HasBinaryCoproduct X Y] (f : X ā¶ W) (g : Y ā¶ W) [Epi g] :
    Epi (coprod.desc f g) :=
  epi_of_epi_fac <| coprod.inr_desc _ _

/-- If the product of `X` and `Y` exists, then every pair of morphisms `f : W ā¶ X` and `g : W ā¶ Y`
    induces a morphism `l : W ā¶ X āØÆ Y` satisfying `l ā« prod.fst = f` and `l ā« prod.snd = g`. -/
def prod.lift' {W X Y : C} [HasBinaryProduct X Y] (f : W ā¶ X) (g : W ā¶ Y) :
    { l : W ā¶ X āØÆ Y // l ā« Prod.fst = f ā§ l ā« Prod.snd = g } :=
  āØprod.lift f g, prod.lift_fst _ _, prod.lift_snd _ _ā©

/-- If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ā¶ W` and
    `g : Y ā¶ W` induces a morphism `l : X āØæ Y ā¶ W` satisfying `coprod.inl ā« l = f` and
    `coprod.inr ā« l = g`. -/
def coprod.desc' {W X Y : C} [HasBinaryCoproduct X Y] (f : X ā¶ W) (g : Y ā¶ W) :
    { l : X āØæ Y ā¶ W // coprod.inl ā« l = f ā§ coprod.inr ā« l = g } :=
  āØcoprod.desc f g, coprod.inl_desc _ _, coprod.inr_desc _ _ā©

/-- If the products `W āØÆ X` and `Y āØÆ Z` exist, then every pair of morphisms `f : W ā¶ Y` and
    `g : X ā¶ Z` induces a morphism `prod.map f g : W āØÆ X ā¶ Y āØÆ Z`. -/
def prod.map {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ā¶ Y) (g : X ā¶ Z) : W āØÆ X ā¶ Y āØÆ Z :=
  limMap (mapPair f g)

/-- If the coproducts `W āØæ X` and `Y āØæ Z` exist, then every pair of morphisms `f : W ā¶ Y` and
    `g : W ā¶ Z` induces a morphism `coprod.map f g : W āØæ X ā¶ Y āØæ Z`. -/
def coprod.map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ā¶ Y) (g : X ā¶ Z) :
    W āØæ X ā¶ Y āØæ Z :=
  colimMap (mapPair f g)

section ProdLemmas

-- Making the reassoc version of this a simp lemma seems to be more harmful than helpful.
@[reassoc, simp]
theorem prod.comp_lift {V W X Y : C} [HasBinaryProduct X Y] (f : V ā¶ W) (g : W ā¶ X) (h : W ā¶ Y) :
    f ā« prod.lift g h = prod.lift (f ā« g) (f ā« h) := by
  ext <;> simp

theorem prod.comp_diag {X Y : C} [HasBinaryProduct Y Y] (f : X ā¶ Y) : f ā« diag Y = prod.lift f f := by
  simp

@[simp, reassoc]
theorem prod.map_fst {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ā¶ Y) (g : X ā¶ Z) :
    prod.map f g ā« Prod.fst = Prod.fst ā« f :=
  lim_map_Ļ _ _

@[simp, reassoc]
theorem prod.map_snd {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ā¶ Y) (g : X ā¶ Z) :
    prod.map f g ā« Prod.snd = Prod.snd ā« g :=
  lim_map_Ļ _ _

@[simp]
theorem prod.map_id_id {X Y : C} [HasBinaryProduct X Y] : prod.map (š X) (š Y) = š _ := by
  ext <;> simp

@[simp]
theorem prod.lift_fst_snd {X Y : C} [HasBinaryProduct X Y] : prod.lift prod.fst prod.snd = š (X āØÆ Y) := by
  ext <;> simp

@[simp, reassoc]
theorem prod.lift_map {V W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : V ā¶ W) (g : V ā¶ X) (h : W ā¶ Y)
    (k : X ā¶ Z) : prod.lift f g ā« prod.map h k = prod.lift (f ā« h) (g ā« k) := by
  ext <;> simp

@[simp]
theorem prod.lift_fst_comp_snd_comp {W X Y Z : C} [HasBinaryProduct W Y] [HasBinaryProduct X Z] (g : W ā¶ X)
    (g' : Y ā¶ Z) : prod.lift (Prod.fst ā« g) (Prod.snd ā« g') = prod.map g g' := by
  rw [ā prod.lift_map]
  simp

-- We take the right hand side here to be simp normal form, as this way composition lemmas for
-- `f ā« h` and `g ā« k` can fire (eg `id_comp`) , while `map_fst` and `map_snd` can still work just
-- as well.
@[simp, reassoc]
theorem prod.map_map {Aā Aā Aā Bā Bā Bā : C} [HasBinaryProduct Aā Bā] [HasBinaryProduct Aā Bā] [HasBinaryProduct Aā Bā]
    (f : Aā ā¶ Aā) (g : Bā ā¶ Bā) (h : Aā ā¶ Aā) (k : Bā ā¶ Bā) : prod.map f g ā« prod.map h k = prod.map (f ā« h) (g ā« k) :=
  by
  ext <;> simp

-- TODO: is it necessary to weaken the assumption here?
@[reassoc]
theorem prod.map_swap {A B X Y : C} (f : A ā¶ B) (g : X ā¶ Y) [HasLimitsOfShape (Discrete WalkingPair) C] :
    prod.map (š X) f ā« prod.map g (š B) = prod.map g (š A) ā« prod.map (š Y) f := by
  simp

@[reassoc]
theorem prod.map_comp_id {X Y Z W : C} (f : X ā¶ Y) (g : Y ā¶ Z) [HasBinaryProduct X W] [HasBinaryProduct Z W]
    [HasBinaryProduct Y W] : prod.map (f ā« g) (š W) = prod.map f (š W) ā« prod.map g (š W) := by
  simp

@[reassoc]
theorem prod.map_id_comp {X Y Z W : C} (f : X ā¶ Y) (g : Y ā¶ Z) [HasBinaryProduct W X] [HasBinaryProduct W Y]
    [HasBinaryProduct W Z] : prod.map (š W) (f ā« g) = prod.map (š W) f ā« prod.map (š W) g := by
  simp

/-- If the products `W āØÆ X` and `Y āØÆ Z` exist, then every pair of isomorphisms `f : W ā Y` and
    `g : X ā Z` induces an isomorphism `prod.map_iso f g : W āØÆ X ā Y āØÆ Z`. -/
@[simps]
def prod.mapIso {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ā Y) (g : X ā Z) :
    W āØÆ X ā Y āØÆ Z where
  Hom := prod.map f.Hom g.Hom
  inv := prod.map f.inv g.inv

instance is_iso_prod {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ā¶ Y) (g : X ā¶ Z) [IsIso f]
    [IsIso g] : IsIso (prod.map f g) :=
  IsIso.of_iso (prod.mapIso (asIso f) (asIso g))

instance prod.map_mono {C : Type _} [Category C] {W X Y Z : C} (f : W ā¶ Y) (g : X ā¶ Z) [Mono f] [Mono g]
    [HasBinaryProduct W X] [HasBinaryProduct Y Z] : Mono (prod.map f g) :=
  āØfun A iā iā h => by
    ext
    Ā· rw [ā cancel_mono f]
      simpa using congr_arg (fun f => f ā« Prod.fst) h
      
    Ā· rw [ā cancel_mono g]
      simpa using congr_arg (fun f => f ā« Prod.snd) h
      ā©

@[simp, reassoc]
theorem prod.diag_map {X Y : C} (f : X ā¶ Y) [HasBinaryProduct X X] [HasBinaryProduct Y Y] :
    diag X ā« prod.map f f = f ā« diag Y := by
  simp

@[simp, reassoc]
theorem prod.diag_map_fst_snd {X Y : C} [HasBinaryProduct X Y] [HasBinaryProduct (X āØÆ Y) (X āØÆ Y)] :
    diag (X āØÆ Y) ā« prod.map prod.fst prod.snd = š (X āØÆ Y) := by
  simp

@[simp, reassoc]
theorem prod.diag_map_fst_snd_comp [HasLimitsOfShape (Discrete WalkingPair) C] {X X' Y Y' : C} (g : X ā¶ Y)
    (g' : X' ā¶ Y') : diag (X āØÆ X') ā« prod.map (Prod.fst ā« g) (Prod.snd ā« g') = prod.map g g' := by
  simp

instance {X : C} [HasBinaryProduct X X] : SplitMono (diag X) where retraction := prod.fst

end ProdLemmas

section CoprodLemmas

@[simp, reassoc]
theorem coprod.desc_comp {V W X Y : C} [HasBinaryCoproduct X Y] (f : V ā¶ W) (g : X ā¶ V) (h : Y ā¶ V) :
    coprod.desc g h ā« f = coprod.desc (g ā« f) (h ā« f) := by
  ext <;> simp

theorem coprod.diag_comp {X Y : C} [HasBinaryCoproduct X X] (f : X ā¶ Y) : codiag X ā« f = coprod.desc f f := by
  simp

@[simp, reassoc]
theorem coprod.inl_map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ā¶ Y) (g : X ā¶ Z) :
    coprod.inl ā« coprod.map f g = f ā« coprod.inl :=
  Ī¹_colim_map _ _

@[simp, reassoc]
theorem coprod.inr_map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ā¶ Y) (g : X ā¶ Z) :
    coprod.inr ā« coprod.map f g = g ā« coprod.inr :=
  Ī¹_colim_map _ _

@[simp]
theorem coprod.map_id_id {X Y : C} [HasBinaryCoproduct X Y] : coprod.map (š X) (š Y) = š _ := by
  ext <;> simp

@[simp]
theorem coprod.desc_inl_inr {X Y : C} [HasBinaryCoproduct X Y] : coprod.desc coprod.inl coprod.inr = š (X āØæ Y) := by
  ext <;> simp

-- The simp linter says simp can prove the reassoc version of this lemma.
@[reassoc, simp]
theorem coprod.map_desc {S T U V W : C} [HasBinaryCoproduct U W] [HasBinaryCoproduct T V] (f : U ā¶ S) (g : W ā¶ S)
    (h : T ā¶ U) (k : V ā¶ W) : coprod.map h k ā« coprod.desc f g = coprod.desc (h ā« f) (k ā« g) := by
  ext <;> simp

@[simp]
theorem coprod.desc_comp_inl_comp_inr {W X Y Z : C} [HasBinaryCoproduct W Y] [HasBinaryCoproduct X Z] (g : W ā¶ X)
    (g' : Y ā¶ Z) : coprod.desc (g ā« coprod.inl) (g' ā« coprod.inr) = coprod.map g g' := by
  rw [ā coprod.map_desc]
  simp

-- We take the right hand side here to be simp normal form, as this way composition lemmas for
-- `f ā« h` and `g ā« k` can fire (eg `id_comp`) , while `inl_map` and `inr_map` can still work just
-- as well.
@[simp, reassoc]
theorem coprod.map_map {Aā Aā Aā Bā Bā Bā : C} [HasBinaryCoproduct Aā Bā] [HasBinaryCoproduct Aā Bā]
    [HasBinaryCoproduct Aā Bā] (f : Aā ā¶ Aā) (g : Bā ā¶ Bā) (h : Aā ā¶ Aā) (k : Bā ā¶ Bā) :
    coprod.map f g ā« coprod.map h k = coprod.map (f ā« h) (g ā« k) := by
  ext <;> simp

-- I don't think it's a good idea to make any of the following three simp lemmas.
@[reassoc]
theorem coprod.map_swap {A B X Y : C} (f : A ā¶ B) (g : X ā¶ Y) [HasColimitsOfShape (Discrete WalkingPair) C] :
    coprod.map (š X) f ā« coprod.map g (š B) = coprod.map g (š A) ā« coprod.map (š Y) f := by
  simp

@[reassoc]
theorem coprod.map_comp_id {X Y Z W : C} (f : X ā¶ Y) (g : Y ā¶ Z) [HasBinaryCoproduct Z W] [HasBinaryCoproduct Y W]
    [HasBinaryCoproduct X W] : coprod.map (f ā« g) (š W) = coprod.map f (š W) ā« coprod.map g (š W) := by
  simp

@[reassoc]
theorem coprod.map_id_comp {X Y Z W : C} (f : X ā¶ Y) (g : Y ā¶ Z) [HasBinaryCoproduct W X] [HasBinaryCoproduct W Y]
    [HasBinaryCoproduct W Z] : coprod.map (š W) (f ā« g) = coprod.map (š W) f ā« coprod.map (š W) g := by
  simp

/-- If the coproducts `W āØæ X` and `Y āØæ Z` exist, then every pair of isomorphisms `f : W ā Y` and
    `g : W ā Z` induces a isomorphism `coprod.map_iso f g : W āØæ X ā Y āØæ Z`. -/
@[simps]
def coprod.mapIso {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ā Y) (g : X ā Z) :
    W āØæ X ā Y āØæ Z where
  Hom := coprod.map f.Hom g.Hom
  inv := coprod.map f.inv g.inv

instance is_iso_coprod {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ā¶ Y) (g : X ā¶ Z) [IsIso f]
    [IsIso g] : IsIso (coprod.map f g) :=
  IsIso.of_iso (coprod.mapIso (asIso f) (asIso g))

instance coprod.map_epi {C : Type _} [Category C] {W X Y Z : C} (f : W ā¶ Y) (g : X ā¶ Z) [Epi f] [Epi g]
    [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] : Epi (coprod.map f g) :=
  āØfun A iā iā h => by
    ext
    Ā· rw [ā cancel_epi f]
      simpa using congr_arg (fun f => coprod.inl ā« f) h
      
    Ā· rw [ā cancel_epi g]
      simpa using congr_arg (fun f => coprod.inr ā« f) h
      ā©

-- The simp linter says simp can prove the reassoc version of this lemma.
@[reassoc, simp]
theorem coprod.map_codiag {X Y : C} (f : X ā¶ Y) [HasBinaryCoproduct X X] [HasBinaryCoproduct Y Y] :
    coprod.map f f ā« codiag Y = codiag X ā« f := by
  simp

-- The simp linter says simp can prove the reassoc version of this lemma.
@[reassoc, simp]
theorem coprod.map_inl_inr_codiag {X Y : C} [HasBinaryCoproduct X Y] [HasBinaryCoproduct (X āØæ Y) (X āØæ Y)] :
    coprod.map coprod.inl coprod.inr ā« codiag (X āØæ Y) = š (X āØæ Y) := by
  simp

-- The simp linter says simp can prove the reassoc version of this lemma.
@[reassoc, simp]
theorem coprod.map_comp_inl_inr_codiag [HasColimitsOfShape (Discrete WalkingPair) C] {X X' Y Y' : C} (g : X ā¶ Y)
    (g' : X' ā¶ Y') : coprod.map (g ā« coprod.inl) (g' ā« coprod.inr) ā« codiag (Y āØæ Y') = coprod.map g g' := by
  simp

end CoprodLemmas

variable (C)

/-- `has_binary_products` represents a choice of product for every pair of objects.

See <https://stacks.math.columbia.edu/tag/001T>.
-/
abbrev HasBinaryProducts :=
  HasLimitsOfShape (Discrete WalkingPair) C

/-- `has_binary_coproducts` represents a choice of coproduct for every pair of objects.

See <https://stacks.math.columbia.edu/tag/04AP>.
-/
abbrev HasBinaryCoproducts :=
  HasColimitsOfShape (Discrete WalkingPair) C

/-- If `C` has all limits of diagrams `pair X Y`, then it has all binary products -/
theorem has_binary_products_of_has_limit_pair [ā {X Y : C}, HasLimit (pair X Y)] : HasBinaryProducts C :=
  { HasLimit := fun F => has_limit_of_iso (diagramIsoPair F).symm }

/-- If `C` has all colimits of diagrams `pair X Y`, then it has all binary coproducts -/
theorem has_binary_coproducts_of_has_colimit_pair [ā {X Y : C}, HasColimit (pair X Y)] : HasBinaryCoproducts C :=
  { HasColimit := fun F => has_colimit_of_iso (diagramIsoPair F) }

section

variable {C}

/-- The braiding isomorphism which swaps a binary product. -/
@[simps]
def prod.braiding (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] : P āØÆ Q ā Q āØÆ P where
  Hom := prod.lift prod.snd prod.fst
  inv := prod.lift prod.snd prod.fst

/-- The braiding isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
theorem braid_natural [HasBinaryProducts C] {W X Y Z : C} (f : X ā¶ Y) (g : Z ā¶ W) :
    prod.map f g ā« (prod.braiding _ _).Hom = (prod.braiding _ _).Hom ā« prod.map g f := by
  simp

@[reassoc]
theorem prod.symmetry' (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] :
    prod.lift prod.snd prod.fst ā« prod.lift prod.snd prod.fst = š (P āØÆ Q) :=
  (prod.braiding _ _).hom_inv_id

/-- The braiding isomorphism is symmetric. -/
@[reassoc]
theorem prod.symmetry (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] :
    (prod.braiding P Q).Hom ā« (prod.braiding Q P).Hom = š _ :=
  (prod.braiding _ _).hom_inv_id

/-- The associator isomorphism for binary products. -/
@[simps]
def prod.associator [HasBinaryProducts C] (P Q R : C) : (P āØÆ Q) āØÆ R ā P āØÆ Q āØÆ R where
  Hom := prod.lift (Prod.fst ā« Prod.fst) (prod.lift (Prod.fst ā« Prod.snd) prod.snd)
  inv := prod.lift (prod.lift prod.fst (Prod.snd ā« Prod.fst)) (Prod.snd ā« Prod.snd)

@[reassoc]
theorem prod.pentagon [HasBinaryProducts C] (W X Y Z : C) :
    prod.map (prod.associator W X Y).Hom (š Z) ā«
        (prod.associator W (X āØÆ Y) Z).Hom ā« prod.map (š W) (prod.associator X Y Z).Hom =
      (prod.associator (W āØÆ X) Y Z).Hom ā« (prod.associator W X (Y āØÆ Z)).Hom :=
  by
  simp

@[reassoc]
theorem prod.associator_naturality [HasBinaryProducts C] {Xā Xā Xā Yā Yā Yā : C} (fā : Xā ā¶ Yā) (fā : Xā ā¶ Yā)
    (fā : Xā ā¶ Yā) :
    prod.map (prod.map fā fā) fā ā« (prod.associator Yā Yā Yā).Hom =
      (prod.associator Xā Xā Xā).Hom ā« prod.map fā (prod.map fā fā) :=
  by
  simp

variable [HasTerminal C]

/-- The left unitor isomorphism for binary products with the terminal object. -/
@[simps]
def prod.leftUnitor (P : C) [HasBinaryProduct (ā¤_ C) P] : (ā¤_ C) āØÆ P ā P where
  Hom := prod.snd
  inv := prod.lift (terminal.from P) (š _)

/-- The right unitor isomorphism for binary products with the terminal object. -/
@[simps]
def prod.rightUnitor (P : C) [HasBinaryProduct P (ā¤_ C)] : P āØÆ ā¤_ C ā P where
  Hom := prod.fst
  inv := prod.lift (š _) (terminal.from P)

@[reassoc]
theorem prod.left_unitor_hom_naturality [HasBinaryProducts C] (f : X ā¶ Y) :
    prod.map (š _) f ā« (prod.leftUnitor Y).Hom = (prod.leftUnitor X).Hom ā« f :=
  prod.map_snd _ _

@[reassoc]
theorem prod.left_unitor_inv_naturality [HasBinaryProducts C] (f : X ā¶ Y) :
    (prod.leftUnitor X).inv ā« prod.map (š _) f = f ā« (prod.leftUnitor Y).inv := by
  rw [iso.inv_comp_eq, ā category.assoc, iso.eq_comp_inv, prod.left_unitor_hom_naturality]

@[reassoc]
theorem prod.right_unitor_hom_naturality [HasBinaryProducts C] (f : X ā¶ Y) :
    prod.map f (š _) ā« (prod.rightUnitor Y).Hom = (prod.rightUnitor X).Hom ā« f :=
  prod.map_fst _ _

@[reassoc]
theorem prod_right_unitor_inv_naturality [HasBinaryProducts C] (f : X ā¶ Y) :
    (prod.rightUnitor X).inv ā« prod.map f (š _) = f ā« (prod.rightUnitor Y).inv := by
  rw [iso.inv_comp_eq, ā category.assoc, iso.eq_comp_inv, prod.right_unitor_hom_naturality]

theorem prod.triangle [HasBinaryProducts C] (X Y : C) :
    (prod.associator X (ā¤_ C) Y).Hom ā« prod.map (š X) (prod.leftUnitor Y).Hom =
      prod.map (prod.rightUnitor X).Hom (š Y) :=
  by
  tidy

end

section

variable {C} [HasBinaryCoproducts C]

/-- The braiding isomorphism which swaps a binary coproduct. -/
@[simps]
def coprod.braiding (P Q : C) : P āØæ Q ā Q āØæ P where
  Hom := coprod.desc coprod.inr coprod.inl
  inv := coprod.desc coprod.inr coprod.inl

@[reassoc]
theorem coprod.symmetry' (P Q : C) :
    coprod.desc coprod.inr coprod.inl ā« coprod.desc coprod.inr coprod.inl = š (P āØæ Q) :=
  (coprod.braiding _ _).hom_inv_id

/-- The braiding isomorphism is symmetric. -/
theorem coprod.symmetry (P Q : C) : (coprod.braiding P Q).Hom ā« (coprod.braiding Q P).Hom = š _ :=
  coprod.symmetry' _ _

/-- The associator isomorphism for binary coproducts. -/
@[simps]
def coprod.associator (P Q R : C) : (P āØæ Q) āØæ R ā P āØæ Q āØæ R where
  Hom := coprod.desc (coprod.desc coprod.inl (coprod.inl ā« coprod.inr)) (coprod.inr ā« coprod.inr)
  inv := coprod.desc (coprod.inl ā« coprod.inl) (coprod.desc (coprod.inr ā« coprod.inl) coprod.inr)

theorem coprod.pentagon (W X Y Z : C) :
    coprod.map (coprod.associator W X Y).Hom (š Z) ā«
        (coprod.associator W (X āØæ Y) Z).Hom ā« coprod.map (š W) (coprod.associator X Y Z).Hom =
      (coprod.associator (W āØæ X) Y Z).Hom ā« (coprod.associator W X (Y āØæ Z)).Hom :=
  by
  simp

theorem coprod.associator_naturality {Xā Xā Xā Yā Yā Yā : C} (fā : Xā ā¶ Yā) (fā : Xā ā¶ Yā) (fā : Xā ā¶ Yā) :
    coprod.map (coprod.map fā fā) fā ā« (coprod.associator Yā Yā Yā).Hom =
      (coprod.associator Xā Xā Xā).Hom ā« coprod.map fā (coprod.map fā fā) :=
  by
  simp

variable [HasInitial C]

/-- The left unitor isomorphism for binary coproducts with the initial object. -/
@[simps]
def coprod.leftUnitor (P : C) : (ā„_ C) āØæ P ā P where
  Hom := coprod.desc (initial.to P) (š _)
  inv := coprod.inr

/-- The right unitor isomorphism for binary coproducts with the initial object. -/
@[simps]
def coprod.rightUnitor (P : C) : P āØæ ā„_ C ā P where
  Hom := coprod.desc (š _) (initial.to P)
  inv := coprod.inl

theorem coprod.triangle (X Y : C) :
    (coprod.associator X (ā„_ C) Y).Hom ā« coprod.map (š X) (coprod.leftUnitor Y).Hom =
      coprod.map (coprod.rightUnitor X).Hom (š Y) :=
  by
  tidy

end

section ProdFunctor

variable {C} [HasBinaryProducts C]

/-- The binary product functor. -/
@[simps]
def prod.functor : C ā„¤ C ā„¤ C where
  obj := fun X => { obj := fun Y => X āØÆ Y, map := fun Y Z => prod.map (š X) }
  map := fun Y Z f => { app := fun T => prod.map f (š T) }

/-- The product functor can be decomposed. -/
def prod.functorLeftComp (X Y : C) : prod.functor.obj (X āØÆ Y) ā prod.functor.obj Y ā prod.functor.obj X :=
  NatIso.ofComponents (prod.associator _ _)
    (by
      tidy)

end ProdFunctor

section CoprodFunctor

variable {C} [HasBinaryCoproducts C]

/-- The binary coproduct functor. -/
@[simps]
def coprod.functor : C ā„¤ C ā„¤ C where
  obj := fun X => { obj := fun Y => X āØæ Y, map := fun Y Z => coprod.map (š X) }
  map := fun Y Z f => { app := fun T => coprod.map f (š T) }

/-- The coproduct functor can be decomposed. -/
def coprod.functorLeftComp (X Y : C) : coprod.functor.obj (X āØæ Y) ā coprod.functor.obj Y ā coprod.functor.obj X :=
  NatIso.ofComponents (coprod.associator _ _)
    (by
      tidy)

end CoprodFunctor

section ProdComparison

universe w

variable {C} {D : Type uā} [Category.{w} D]

variable (F : C ā„¤ D) {A A' B B' : C}

variable [HasBinaryProduct A B] [HasBinaryProduct A' B']

variable [HasBinaryProduct (F.obj A) (F.obj B)] [HasBinaryProduct (F.obj A') (F.obj B')]

/-- The product comparison morphism.

In `category_theory/limits/preserves` we show this is always an iso iff F preserves binary products.
-/
def prodComparison (F : C ā„¤ D) (A B : C) [HasBinaryProduct A B] [HasBinaryProduct (F.obj A) (F.obj B)] :
    F.obj (A āØÆ B) ā¶ F.obj A āØÆ F.obj B :=
  prod.lift (F.map prod.fst) (F.map prod.snd)

@[simp, reassoc]
theorem prod_comparison_fst : prodComparison F A B ā« Prod.fst = F.map prod.fst :=
  prod.lift_fst _ _

@[simp, reassoc]
theorem prod_comparison_snd : prodComparison F A B ā« Prod.snd = F.map prod.snd :=
  prod.lift_snd _ _

/-- Naturality of the prod_comparison morphism in both arguments. -/
@[reassoc]
theorem prod_comparison_natural (f : A ā¶ A') (g : B ā¶ B') :
    F.map (prod.map f g) ā« prodComparison F A' B' = prodComparison F A B ā« prod.map (F.map f) (F.map g) := by
  rw [prod_comparison, prod_comparison, prod.lift_map, ā F.map_comp, ā F.map_comp, prod.comp_lift, ā F.map_comp,
    Prod.map_fst, ā F.map_comp, Prod.map_sndā]

/-- The product comparison morphism from `F(A āØÆ -)` to `FA āØÆ F-`, whose components are given by
`prod_comparison`.
-/
@[simps]
def prodComparisonNatTrans [HasBinaryProducts C] [HasBinaryProducts D] (F : C ā„¤ D) (A : C) :
    prod.functor.obj A ā F ā¶ F ā prod.functor.obj (F.obj A) where
  app := fun B => prodComparison F A B
  naturality' := fun B B' f => by
    simp [ā prod_comparison_natural]

@[reassoc]
theorem inv_prod_comparison_map_fst [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ā« F.map prod.fst = Prod.fst := by
  simp [ā is_iso.inv_comp_eq]

@[reassoc]
theorem inv_prod_comparison_map_snd [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ā« F.map prod.snd = Prod.snd := by
  simp [ā is_iso.inv_comp_eq]

/-- If the product comparison morphism is an iso, its inverse is natural. -/
@[reassoc]
theorem prod_comparison_inv_natural (f : A ā¶ A') (g : B ā¶ B') [IsIso (prodComparison F A B)]
    [IsIso (prodComparison F A' B')] :
    inv (prodComparison F A B) ā« F.map (prod.map f g) = prod.map (F.map f) (F.map g) ā« inv (prodComparison F A' B') :=
  by
  rw [is_iso.eq_comp_inv, category.assoc, is_iso.inv_comp_eq, prod_comparison_natural]

/-- The natural isomorphism `F(A āØÆ -) ā FA āØÆ F-`, provided each `prod_comparison F A B` is an
isomorphism (as `B` changes).
-/
@[simps (config := { rhsMd := semireducible })]
def prodComparisonNatIso [HasBinaryProducts C] [HasBinaryProducts D] (A : C) [ā B, IsIso (prodComparison F A B)] :
    prod.functor.obj A ā F ā F ā prod.functor.obj (F.obj A) :=
  { @asIso _ _ _ _ _ (NatIso.is_iso_of_is_iso_app āØ_, _ā©) with Hom := prodComparisonNatTrans F A }

end ProdComparison

section CoprodComparison

universe w

variable {C} {D : Type uā} [Category.{w} D]

variable (F : C ā„¤ D) {A A' B B' : C}

variable [HasBinaryCoproduct A B] [HasBinaryCoproduct A' B']

variable [HasBinaryCoproduct (F.obj A) (F.obj B)] [HasBinaryCoproduct (F.obj A') (F.obj B')]

/-- The coproduct comparison morphism.

In `category_theory/limits/preserves` we show
this is always an iso iff F preserves binary coproducts.
-/
def coprodComparison (F : C ā„¤ D) (A B : C) [HasBinaryCoproduct A B] [HasBinaryCoproduct (F.obj A) (F.obj B)] :
    F.obj A āØæ F.obj B ā¶ F.obj (A āØæ B) :=
  coprod.desc (F.map coprod.inl) (F.map coprod.inr)

@[simp, reassoc]
theorem coprod_comparison_inl : coprod.inl ā« coprodComparison F A B = F.map coprod.inl :=
  coprod.inl_desc _ _

@[simp, reassoc]
theorem coprod_comparison_inr : coprod.inr ā« coprodComparison F A B = F.map coprod.inr :=
  coprod.inr_desc _ _

/-- Naturality of the coprod_comparison morphism in both arguments. -/
@[reassoc]
theorem coprod_comparison_natural (f : A ā¶ A') (g : B ā¶ B') :
    coprodComparison F A B ā« F.map (coprod.map f g) = coprod.map (F.map f) (F.map g) ā« coprodComparison F A' B' := by
  rw [coprod_comparison, coprod_comparison, coprod.map_desc, ā F.map_comp, ā F.map_comp, coprod.desc_comp, ā F.map_comp,
    coprod.inl_map, ā F.map_comp, coprod.inr_map]

/-- The coproduct comparison morphism from `FA āØæ F-` to `F(A āØæ -)`, whose components are given by
`coprod_comparison`.
-/
@[simps]
def coprodComparisonNatTrans [HasBinaryCoproducts C] [HasBinaryCoproducts D] (F : C ā„¤ D) (A : C) :
    F ā coprod.functor.obj (F.obj A) ā¶ coprod.functor.obj A ā F where
  app := fun B => coprodComparison F A B
  naturality' := fun B B' f => by
    simp [ā coprod_comparison_natural]

@[reassoc]
theorem map_inl_inv_coprod_comparison [IsIso (coprodComparison F A B)] :
    F.map coprod.inl ā« inv (coprodComparison F A B) = coprod.inl := by
  simp [ā is_iso.inv_comp_eq]

@[reassoc]
theorem map_inr_inv_coprod_comparison [IsIso (coprodComparison F A B)] :
    F.map coprod.inr ā« inv (coprodComparison F A B) = coprod.inr := by
  simp [ā is_iso.inv_comp_eq]

/-- If the coproduct comparison morphism is an iso, its inverse is natural. -/
@[reassoc]
theorem coprod_comparison_inv_natural (f : A ā¶ A') (g : B ā¶ B') [IsIso (coprodComparison F A B)]
    [IsIso (coprodComparison F A' B')] :
    inv (coprodComparison F A B) ā« coprod.map (F.map f) (F.map g) =
      F.map (coprod.map f g) ā« inv (coprodComparison F A' B') :=
  by
  rw [is_iso.eq_comp_inv, category.assoc, is_iso.inv_comp_eq, coprod_comparison_natural]

/-- The natural isomorphism `FA āØæ F- ā F(A āØæ -)`, provided each `coprod_comparison F A B` is an
isomorphism (as `B` changes).
-/
@[simps (config := { rhsMd := semireducible })]
def coprodComparisonNatIso [HasBinaryCoproducts C] [HasBinaryCoproducts D] (A : C)
    [ā B, IsIso (coprodComparison F A B)] : F ā coprod.functor.obj (F.obj A) ā coprod.functor.obj A ā F :=
  { @asIso _ _ _ _ _ (NatIso.is_iso_of_is_iso_app āØ_, _ā©) with Hom := coprodComparisonNatTrans F A }

end CoprodComparison

end CategoryTheory.Limits

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Auxiliary definition for `over.coprod`. -/
@[simps]
def Over.coprodObj [HasBinaryCoproducts C] {A : C} : Over A ā Over A ā„¤ Over A := fun f =>
  { obj := fun g => Over.mk (coprod.desc f.Hom g.Hom), map := fun gā gā k => Over.homMk (coprod.map (š _) k.left) }

/-- A category with binary coproducts has a functorial `sup` operation on over categories. -/
@[simps]
def Over.coprod [HasBinaryCoproducts C] {A : C} : Over A ā„¤ Over A ā„¤ Over A where
  obj := fun f => Over.coprodObj f
  map := fun fā fā k =>
    { app := fun g =>
        Over.homMk (coprod.map k.left (š _))
          (by
            dsimp'
            rw [coprod.map_desc, category.id_comp, over.w k]),
      naturality' := fun f g k => by
        ext <;>
          Ā· dsimp'
            simp
             }
  map_id' := fun X => by
    ext <;>
      Ā· dsimp'
        simp
        
  map_comp' := fun X Y Z f g => by
    ext <;>
      Ā· dsimp'
        simp
        

end CategoryTheory

