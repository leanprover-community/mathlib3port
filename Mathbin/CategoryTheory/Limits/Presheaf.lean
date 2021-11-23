import Mathbin.CategoryTheory.Adjunction.Limits 
import Mathbin.CategoryTheory.Adjunction.Opposites 
import Mathbin.CategoryTheory.Elements 
import Mathbin.CategoryTheory.Limits.FunctorCategory 
import Mathbin.CategoryTheory.Limits.KanExtension 
import Mathbin.CategoryTheory.Limits.Preserves.Limits 
import Mathbin.CategoryTheory.Limits.Shapes.Terminal 
import Mathbin.CategoryTheory.Limits.Types

/-!
# Colimit of representables

This file constructs an adjunction `yoneda_adjunction` between `(Cᵒᵖ ⥤ Type u)` and `ℰ` given a
functor `A : C ⥤ ℰ`, where the right adjoint sends `(E : ℰ)` to `c ↦ (A.obj c ⟶ E)` (provided `ℰ`
has colimits).

This adjunction is used to show that every presheaf is a colimit of representables.

Further, the left adjoint `colimit_adj.extend_along_yoneda : (Cᵒᵖ ⥤ Type u) ⥤ ℰ` satisfies
`yoneda ⋙ L ≅ A`, that is, an extension of `A : C ⥤ ℰ` to `(Cᵒᵖ ⥤ Type u) ⥤ ℰ` through
`yoneda : C ⥤ Cᵒᵖ ⥤ Type u`. It is the left Kan extension of `A` along the yoneda embedding,
sometimes known as the Yoneda extension, as proved in `extend_along_yoneda_iso_Kan`.

`unique_extension_along_yoneda` shows `extend_along_yoneda` is unique amongst cocontinuous functors
with this property, establishing the presheaf category as the free cocompletion of a small category.

## Tags
colimit, representable, presheaf, free cocompletion

## References
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* https://ncatlab.org/nlab/show/Yoneda+extension
-/


namespace CategoryTheory

noncomputable theory

open Category Limits

universe u₁ u₂

variable{C : Type u₁}[small_category C]

variable{ℰ : Type u₂}[category.{u₁} ℰ]

variable(A : C ⥤ ℰ)

namespace ColimitAdj

/--
The functor taking `(E : ℰ) (c : Cᵒᵖ)` to the homset `(A.obj C ⟶ E)`. It is shown in `L_adjunction`
that this functor has a left adjoint (provided `E` has colimits) given by taking colimits over
categories of elements.
In the case where `ℰ = Cᵒᵖ ⥤ Type u` and `A = yoneda`, this functor is isomorphic to the identity.

Defined as in [MM92], Chapter I, Section 5, Theorem 2.
-/
@[simps]
def restricted_yoneda : ℰ ⥤ «expr ᵒᵖ» C ⥤ Type u₁ :=
  yoneda ⋙ (whiskering_left _ _ (Type u₁)).obj (functor.op A)

/--
The functor `restricted_yoneda` is isomorphic to the identity functor when evaluated at the yoneda
embedding.
-/
def restricted_yoneda_yoneda : restricted_yoneda (yoneda : C ⥤ «expr ᵒᵖ» C ⥤ Type u₁) ≅ 𝟭 _ :=
  nat_iso.of_components
    (fun P =>
      nat_iso.of_components (fun X => yoneda_sections_small X.unop _)
        fun X Y f =>
          funext$
            fun x =>
              by 
                dsimp 
                rw [←functor_to_types.naturality _ _ x f (𝟙 _)]
                dsimp 
                simp )
    fun _ _ _ => rfl

/--
(Implementation). The equivalence of homsets which helps construct the left adjoint to
`colimit_adj.restricted_yoneda`.
It is shown in `restrict_yoneda_hom_equiv_natural` that this is a natural bijection.
-/
def restrict_yoneda_hom_equiv (P : «expr ᵒᵖ» C ⥤ Type u₁) (E : ℰ) {c : cocone ((category_of_elements.π P).leftOp ⋙ A)}
  (t : is_colimit c) : (c.X ⟶ E) ≃ (P ⟶ (restricted_yoneda A).obj E) :=
  (t.hom_iso' E).toEquiv.trans
    { toFun :=
        fun k =>
          { app := fun c p => k.1 (Opposite.op ⟨_, p⟩),
            naturality' :=
              fun c c' f =>
                funext$
                  fun p =>
                    (k.2
                        (Quiver.Hom.op ⟨f, rfl⟩ :
                        (Opposite.op ⟨c', P.map f p⟩ : «expr ᵒᵖ» P.elements) ⟶ Opposite.op ⟨c, p⟩)).symm },
      invFun :=
        fun τ =>
          { val := fun p => τ.app p.unop.1 p.unop.2,
            property :=
              fun p p' f =>
                by 
                  simpRw [←f.unop.2]
                  apply (congr_funₓ (τ.naturality f.unop.1) p'.unop.2).symm },
      left_inv :=
        by 
          rintro ⟨k₁, k₂⟩
          ext 
          dsimp 
          congr 1
          simp ,
      right_inv :=
        by 
          rintro ⟨_, _⟩
          rfl }

/--
(Implementation). Show that the bijection in `restrict_yoneda_hom_equiv` is natural (on the right).
-/
theorem restrict_yoneda_hom_equiv_natural (P : «expr ᵒᵖ» C ⥤ Type u₁) (E₁ E₂ : ℰ) (g : E₁ ⟶ E₂) {c : cocone _}
  (t : is_colimit c) (k : c.X ⟶ E₁) :
  restrict_yoneda_hom_equiv A P E₂ t (k ≫ g) = restrict_yoneda_hom_equiv A P E₁ t k ≫ (restricted_yoneda A).map g :=
  by 
    ext _ X p 
    apply (assoc _ _ _).symm

variable[has_colimits ℰ]

/--
The left adjoint to the functor `restricted_yoneda` (shown in `yoneda_adjunction`). It is also an
extension of `A` along the yoneda embedding (shown in `is_extension_along_yoneda`), in particular
it is the left Kan extension of `A` through the yoneda embedding.
-/
def extend_along_yoneda : («expr ᵒᵖ» C ⥤ Type u₁) ⥤ ℰ :=
  adjunction.left_adjoint_of_equiv (fun P E => restrict_yoneda_hom_equiv A P E (colimit.is_colimit _))
    fun P E E' g => restrict_yoneda_hom_equiv_natural A P E E' g _

@[simp]
theorem extend_along_yoneda_obj (P : «expr ᵒᵖ» C ⥤ Type u₁) :
  (extend_along_yoneda A).obj P = colimit ((category_of_elements.π P).leftOp ⋙ A) :=
  rfl

theorem extend_along_yoneda_map {X Y : «expr ᵒᵖ» C ⥤ Type u₁} (f : X ⟶ Y) :
  (extend_along_yoneda A).map f = colimit.pre ((category_of_elements.π Y).leftOp ⋙ A) (category_of_elements.map f).op :=
  by 
    ext J 
    erw [colimit.ι_pre ((category_of_elements.π Y).leftOp ⋙ A) (category_of_elements.map f).op]
    dsimp only [extend_along_yoneda, restrict_yoneda_hom_equiv, is_colimit.hom_iso', is_colimit.hom_iso]
    simpa

/--
Show `extend_along_yoneda` is left adjoint to `restricted_yoneda`.

The construction of [MM92], Chapter I, Section 5, Theorem 2.
-/
def yoneda_adjunction : extend_along_yoneda A ⊣ restricted_yoneda A :=
  adjunction.adjunction_of_equiv_left _ _

/--
The initial object in the category of elements for a representable functor. In `is_initial` it is
shown that this is initial.
-/
def elements.initial (A : C) : (yoneda.obj A).Elements :=
  ⟨Opposite.op A, 𝟙 _⟩

/--
Show that `elements.initial A` is initial in the category of elements for the `yoneda` functor.
-/
def is_initial (A : C) : is_initial (elements.initial A) :=
  { desc := fun s => ⟨s.X.2.op, comp_id _⟩,
    uniq' :=
      fun s m w =>
        by 
          simpRw [←m.2]
          dsimp [elements.initial]
          simp  }

/--
`extend_along_yoneda A` is an extension of `A` to the presheaf category along the yoneda embedding.
`unique_extension_along_yoneda` shows it is unique among functors preserving colimits with this
property (up to isomorphism).

The first part of [MM92], Chapter I, Section 5, Corollary 4.
See Property 1 of https://ncatlab.org/nlab/show/Yoneda+extension#properties.
-/
def is_extension_along_yoneda : (yoneda : C ⥤ «expr ᵒᵖ» C ⥤ Type u₁) ⋙ extend_along_yoneda A ≅ A :=
  nat_iso.of_components
    (fun X =>
      (colimit.is_colimit _).coconePointUniqueUpToIso
        (colimit_of_diagram_terminal (terminal_op_of_initial (is_initial _)) _))
    (by 
      intro X Y f 
      change colimit.desc _ ⟨_, _⟩ ≫ colimit.desc _ _ = colimit.desc _ _ ≫ _ 
      apply colimit.hom_ext 
      intro j 
      rw [colimit.ι_desc_assoc, colimit.ι_desc_assoc]
      change (colimit.ι _ _ ≫ 𝟙 _) ≫ colimit.desc _ _ = _ 
      rw [comp_id, colimit.ι_desc]
      dsimp 
      rw [←A.map_comp]
      congr 1)

/-- See Property 2 of https://ncatlab.org/nlab/show/Yoneda+extension#properties. -/
instance  : preserves_colimits (extend_along_yoneda A) :=
  (yoneda_adjunction A).leftAdjointPreservesColimits

/--
Show that the images of `X` after `extend_along_yoneda` and `Lan yoneda` are indeed isomorphic.
This follows from `category_theory.category_of_elements.costructured_arrow_yoneda_equivalence`.
-/
@[simps]
def extend_along_yoneda_iso_Kan_app X : (extend_along_yoneda A).obj X ≅ ((Lan yoneda : (_ ⥤ ℰ) ⥤ _).obj A).obj X :=
  let eq := category_of_elements.costructured_arrow_yoneda_equivalence X
  { Hom := colimit.pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A X) eq.functor,
    inv := colimit.pre ((category_of_elements.π X).leftOp ⋙ A) eq.inverse,
    hom_inv_id' :=
      by 
        erw [colimit.pre_pre ((category_of_elements.π X).leftOp ⋙ A) eq.inverse]
        trans colimit.pre ((category_of_elements.π X).leftOp ⋙ A) (𝟭 _)
        congr
        ·
          exact congr_argₓ functor.op (category_of_elements.from_to_costructured_arrow_eq X)
        ·
          ext 
          simp only [colimit.ι_pre]
          erw [category.comp_id]
          congr,
    inv_hom_id' :=
      by 
        erw [colimit.pre_pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A X) eq.functor]
        trans colimit.pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A X) (𝟭 _)
        congr
        ·
          exact category_of_elements.to_from_costructured_arrow_eq X
        ·
          ext 
          simp only [colimit.ι_pre]
          erw [category.comp_id]
          congr }

/--
Verify that `extend_along_yoneda` is indeed the left Kan extension along the yoneda embedding.
-/
@[simps]
def extend_along_yoneda_iso_Kan : extend_along_yoneda A ≅ (Lan yoneda : (_ ⥤ ℰ) ⥤ _).obj A :=
  nat_iso.of_components (extend_along_yoneda_iso_Kan_app A)
    (by 
      intro X Y f 
      simp 
      rw [extend_along_yoneda_map]
      erw [colimit.pre_pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A Y) (costructured_arrow.map f)]
      erw
        [colimit.pre_pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A Y)
          (category_of_elements.costructured_arrow_yoneda_equivalence Y).Functor]
      congr 1
      apply category_of_elements.costructured_arrow_yoneda_equivalence_naturality)

end ColimitAdj

open ColimitAdj

/--
Since `extend_along_yoneda A` is adjoint to `restricted_yoneda A`, if we use `A = yoneda`
then `restricted_yoneda A` is isomorphic to the identity, and so `extend_along_yoneda A` is as well.
-/
def extend_along_yoneda_yoneda : extend_along_yoneda (yoneda : C ⥤ _) ≅ 𝟭 _ :=
  Adjunction.natIsoOfRightAdjointNatIso (yoneda_adjunction _) adjunction.id restricted_yoneda_yoneda

/--
A functor to the presheaf category in which everything in the image is representable (witnessed
by the fact that it factors through the yoneda embedding).
`cocone_of_representable` gives a cocone for this functor which is a colimit and has point `P`.
-/
def functor_to_representables (P : «expr ᵒᵖ» C ⥤ Type u₁) : «expr ᵒᵖ» P.elements ⥤ «expr ᵒᵖ» C ⥤ Type u₁ :=
  (category_of_elements.π P).leftOp ⋙ yoneda

/--
This is a cocone with point `P` for the functor `functor_to_representables P`. It is shown in
`colimit_of_representable P` that this cocone is a colimit: that is, we have exhibited an arbitrary
presheaf `P` as a colimit of representables.

The construction of [MM92], Chapter I, Section 5, Corollary 3.
-/
def cocone_of_representable (P : «expr ᵒᵖ» C ⥤ Type u₁) : cocone (functor_to_representables P) :=
  cocone.extend (colimit.cocone _) (extend_along_yoneda_yoneda.Hom.app P)

@[simp]
theorem cocone_of_representable_X (P : «expr ᵒᵖ» C ⥤ Type u₁) : (cocone_of_representable P).x = P :=
  rfl

/-- An explicit formula for the legs of the cocone `cocone_of_representable`. -/
theorem cocone_of_representable_ι_app (P : «expr ᵒᵖ» C ⥤ Type u₁) (j : «expr ᵒᵖ» P.elements) :
  (cocone_of_representable P).ι.app j = (yoneda_sections_small _ _).inv j.unop.2 :=
  colimit.ι_desc _ _

/-- The legs of the cocone `cocone_of_representable` are natural in the choice of presheaf. -/
theorem cocone_of_representable_naturality {P₁ P₂ : «expr ᵒᵖ» C ⥤ Type u₁} (α : P₁ ⟶ P₂) (j : «expr ᵒᵖ» P₁.elements) :
  (cocone_of_representable P₁).ι.app j ≫ α =
    (cocone_of_representable P₂).ι.app ((category_of_elements.map α).op.obj j) :=
  by 
    ext T f 
    simpa [cocone_of_representable_ι_app] using functor_to_types.naturality _ _ α f.op _

/--
The cocone with point `P` given by `the_cocone` is a colimit: that is, we have exhibited an
arbitrary presheaf `P` as a colimit of representables.

The result of [MM92], Chapter I, Section 5, Corollary 3.
-/
def colimit_of_representable (P : «expr ᵒᵖ» C ⥤ Type u₁) : is_colimit (cocone_of_representable P) :=
  by 
    apply is_colimit.of_point_iso (colimit.is_colimit (functor_to_representables P))
    change is_iso (colimit.desc _ (cocone.extend _ _))
    rw [colimit.desc_extend, colimit.desc_cocone]
    infer_instance

-- error in CategoryTheory.Limits.Presheaf: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Given two functors L₁ and L₂ which preserve colimits, if they agree when restricted to the
representable presheaves then they agree everywhere.
-/
def nat_iso_of_nat_iso_on_representables
(L₁ L₂ : «expr ⥤ »(«expr ⥤ »(«expr ᵒᵖ»(C), Type u₁), ℰ))
[preserves_colimits L₁]
[preserves_colimits L₂]
(h : «expr ≅ »(«expr ⋙ »(yoneda, L₁), «expr ⋙ »(yoneda, L₂))) : «expr ≅ »(L₁, L₂) :=
begin
  apply [expr nat_iso.of_components _ _],
  { intro [ident P],
    refine [expr (is_colimit_of_preserves L₁ (colimit_of_representable P)).cocone_points_iso_of_nat_iso (is_colimit_of_preserves L₂ (colimit_of_representable P)) _],
    apply [expr «expr ≪≫ »(functor.associator _ _ _, _)],
    exact [expr iso_whisker_left (category_of_elements.π P).left_op h] },
  { intros [ident P₁, ident P₂, ident f],
    apply [expr (is_colimit_of_preserves L₁ (colimit_of_representable P₁)).hom_ext],
    intro [ident j],
    dsimp ["only"] ["[", expr id.def, ",", expr is_colimit.cocone_points_iso_of_nat_iso_hom, ",", expr iso_whisker_left_hom, "]"] [] [],
    have [] [":", expr «expr = »(«expr ≫ »((L₁.map_cocone (cocone_of_representable P₁)).ι.app j, L₁.map f), (L₁.map_cocone (cocone_of_representable P₂)).ι.app ((category_of_elements.map f).op.obj j))] [],
    { dsimp [] [] [] [],
      rw ["[", "<-", expr L₁.map_comp, ",", expr cocone_of_representable_naturality, "]"] [],
      refl },
    rw ["[", expr reassoc_of this, ",", expr is_colimit.ι_map_assoc, ",", expr is_colimit.ι_map, "]"] [],
    dsimp [] [] [] [],
    rw ["[", "<-", expr L₂.map_comp, ",", expr cocone_of_representable_naturality, "]"] [],
    refl }
end

variable[has_colimits ℰ]

/--
Show that `extend_along_yoneda` is the unique colimit-preserving functor which extends `A` to
the presheaf category.

The second part of [MM92], Chapter I, Section 5, Corollary 4.
See Property 3 of https://ncatlab.org/nlab/show/Yoneda+extension#properties.
-/
def unique_extension_along_yoneda (L : («expr ᵒᵖ» C ⥤ Type u₁) ⥤ ℰ) (hL : yoneda ⋙ L ≅ A) [preserves_colimits L] :
  L ≅ extend_along_yoneda A :=
  nat_iso_of_nat_iso_on_representables _ _ (hL ≪≫ (is_extension_along_yoneda _).symm)

/--
If `L` preserves colimits and `ℰ` has them, then it is a left adjoint. This is a special case of
`is_left_adjoint_of_preserves_colimits` used to prove that.
-/
def is_left_adjoint_of_preserves_colimits_aux (L : («expr ᵒᵖ» C ⥤ Type u₁) ⥤ ℰ) [preserves_colimits L] :
  is_left_adjoint L :=
  { right := restricted_yoneda (yoneda ⋙ L),
    adj := (yoneda_adjunction _).ofNatIsoLeft (unique_extension_along_yoneda _ L (iso.refl _)).symm }

/--
If `L` preserves colimits and `ℰ` has them, then it is a left adjoint. Note this is a (partial)
converse to `left_adjoint_preserves_colimits`.
-/
def is_left_adjoint_of_preserves_colimits (L : (C ⥤ Type u₁) ⥤ ℰ) [preserves_colimits L] : is_left_adjoint L :=
  let e : _ ⥤ Type u₁ ≌ _ ⥤ Type u₁ := (op_op_equivalence C).congr_left 
  let t := is_left_adjoint_of_preserves_colimits_aux (e.functor ⋙ L : _)
  by 
    exact adjunction.left_adjoint_of_nat_iso (e.inv_fun_id_assoc _)

end CategoryTheory

