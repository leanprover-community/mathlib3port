import Mathbin.CategoryTheory.StructuredArrow 
import Mathbin.CategoryTheory.Groupoid 
import Mathbin.CategoryTheory.Punit

/-!
# The category of elements

This file defines the category of elements, also known as (a special case of) the Grothendieck
construction.

Given a functor `F : C ⥤ Type`, an object of `F.elements` is a pair `(X : C, x : F.obj X)`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, so `F.map f` takes `x` to `y`.

## Implementation notes

This construction is equivalent to a special case of a comma construction, so this is mostly just a
more convenient API. We prove the equivalence in
`category_theory.category_of_elements.structured_arrow_equivalence`.

## References
* [Emily Riehl, *Category Theory in Context*, Section 2.4][riehl2017]
* <https://en.wikipedia.org/wiki/Category_of_elements>
* <https://ncatlab.org/nlab/show/category+of+elements>

## Tags
category of elements, Grothendieck construction, comma category
-/


namespace CategoryTheory

universe w v u

variable {C : Type u} [category.{v} C]

/--
The type of objects for the category of elements of a functor `F : C ⥤ Type`
is a pair `(X : C, x : F.obj X)`.
-/
@[nolint has_inhabited_instance]
def functor.elements (F : C ⥤ Type w) :=
  Σc : C, F.obj c

/-- The category structure on `F.elements`, for `F : C ⥤ Type`.
    A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, so `F.map f` takes `x` to `y`.
 -/
instance category_of_elements (F : C ⥤ Type w) : category.{v} F.elements :=
  { Hom := fun p q => { f : p.1 ⟶ q.1 // (F.map f) p.2 = q.2 },
    id :=
      fun p =>
        ⟨𝟙 p.1,
          by 
            runTac 
              obviously⟩,
    comp :=
      fun p q r f g =>
        ⟨f.val ≫ g.val,
          by 
            runTac 
              obviously⟩ }

namespace CategoryOfElements

@[ext]
theorem ext (F : C ⥤ Type w) {x y : F.elements} (f g : x ⟶ y) (w : f.val = g.val) : f = g :=
  Subtype.ext_val w

@[simp]
theorem comp_val {F : C ⥤ Type w} {p q r : F.elements} {f : p ⟶ q} {g : q ⟶ r} : (f ≫ g).val = f.val ≫ g.val :=
  rfl

@[simp]
theorem id_val {F : C ⥤ Type w} {p : F.elements} : (𝟙 p : p ⟶ p).val = 𝟙 p.1 :=
  rfl

end CategoryOfElements

noncomputable instance groupoid_of_elements {G : Type u} [groupoid.{v} G] (F : G ⥤ Type w) : groupoid F.elements :=
  { inv :=
      fun p q f =>
        ⟨inv f.val,
          calc F.map (inv f.val) q.2 = F.map (inv f.val) (F.map f.val p.2) :=
            by 
              rw [f.2]
            _ = (F.map f.val ≫ F.map (inv f.val)) p.2 :=
            by 
              simp 
            _ = p.2 :=
            by 
              rw [←functor.map_comp]
              simp 
            ⟩ }

namespace CategoryOfElements

variable (F : C ⥤ Type w)

/-- The functor out of the category of elements which forgets the element. -/
@[simps]
def π : F.elements ⥤ C :=
  { obj := fun X => X.1, map := fun X Y f => f.val }

/--
A natural transformation between functors induces a functor between the categories of elements.
-/
@[simps]
def map {F₁ F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂) : F₁.elements ⥤ F₂.elements :=
  { obj := fun t => ⟨t.1, α.app t.1 t.2⟩,
    map :=
      fun t₁ t₂ k =>
        ⟨k.1,
          by 
            simpa [←k.2] using (functor_to_types.naturality _ _ α k.1 t₁.2).symm⟩ }

@[simp]
theorem map_π {F₁ F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂) : map α ⋙ π F₂ = π F₁ :=
  rfl

/-- The forward direction of the equivalence `F.elements ≅ (*, F)`. -/
def to_structured_arrow : F.elements ⥤ structured_arrow PUnit F :=
  { obj := fun X => structured_arrow.mk fun _ => X.2,
    map :=
      fun X Y f =>
        structured_arrow.hom_mk f.val
          (by 
            tidy) }

@[simp]
theorem to_structured_arrow_obj X :
  (to_structured_arrow F).obj X = { left := PUnit.unit, right := X.1, Hom := fun _ => X.2 } :=
  rfl

@[simp]
theorem to_comma_map_right {X Y} (f : X ⟶ Y) : ((to_structured_arrow F).map f).right = f.val :=
  rfl

/-- The reverse direction of the equivalence `F.elements ≅ (*, F)`. -/
def from_structured_arrow : structured_arrow PUnit F ⥤ F.elements :=
  { obj := fun X => ⟨X.right, X.hom PUnit.unit⟩, map := fun X Y f => ⟨f.right, congr_funₓ f.w'.symm PUnit.unit⟩ }

@[simp]
theorem from_structured_arrow_obj X : (from_structured_arrow F).obj X = ⟨X.right, X.hom PUnit.unit⟩ :=
  rfl

@[simp]
theorem from_structured_arrow_map {X Y} (f : X ⟶ Y) :
  (from_structured_arrow F).map f = ⟨f.right, congr_funₓ f.w'.symm PUnit.unit⟩ :=
  rfl

/-- The equivalence between the category of elements `F.elements`
    and the comma category `(*, F)`. -/
@[simps]
def structured_arrow_equivalence : F.elements ≌ structured_arrow PUnit F :=
  equivalence.mk (to_structured_arrow F) (from_structured_arrow F)
    (nat_iso.of_components
      (fun X =>
        eq_to_iso
          (by 
            tidy))
      (by 
        tidy))
    (nat_iso.of_components (fun X => { Hom := { right := 𝟙 _ }, inv := { right := 𝟙 _ } })
      (by 
        tidy))

open Opposite

/--
The forward direction of the equivalence `F.elementsᵒᵖ ≅ (yoneda, F)`,
given by `category_theory.yoneda_sections`.
-/
@[simps]
def to_costructured_arrow (F : «expr ᵒᵖ» C ⥤ Type v) : «expr ᵒᵖ» F.elements ⥤ costructured_arrow yoneda F :=
  { obj := fun X => costructured_arrow.mk ((yoneda_sections (unop (unop X).fst) F).inv (Ulift.up (unop X).2)),
    map :=
      fun X Y f =>
        by 
          fapply costructured_arrow.hom_mk 
          exact f.unop.val.unop 
          ext y 
          simp only [costructured_arrow.mk_hom_eq_self, yoneda_map_app, functor_to_types.comp, op_comp,
            yoneda_sections_inv_app, functor_to_types.map_comp_apply, Quiver.Hom.op_unop, Subtype.val_eq_coe]
          congr 
          exact f.unop.2 }

-- error in CategoryTheory.Elements: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The reverse direction of the equivalence `F.elementsᵒᵖ ≅ (yoneda, F)`,
given by `category_theory.yoneda_equiv`.
-/
@[simps #[]]
def from_costructured_arrow
(F : «expr ⥤ »(«expr ᵒᵖ»(C), Type v)) : «expr ⥤ »(«expr ᵒᵖ»(costructured_arrow yoneda F), F.elements) :=
{ obj := λ X, ⟨op (unop X).1, yoneda_equiv.1 (unop X).3⟩,
  map := λ
  X
  Y
  f, ⟨f.unop.1.op, begin
     convert [] [expr (congr_fun ((unop X).hom.naturality f.unop.left.op) («expr𝟙»() _)).symm] [],
     simp [] [] ["only"] ["[", expr equiv.to_fun_as_coe, ",", expr quiver.hom.unop_op, ",", expr yoneda_equiv_apply, ",", expr types_comp_apply, ",", expr category.comp_id, ",", expr yoneda_obj_map, "]"] [] [],
     have [] [":", expr «expr = »(«expr ≫ »(yoneda.map f.unop.left, (unop X).hom), (unop Y).hom)] [],
     { convert [] [expr f.unop.3] [],
       erw [expr category.comp_id] [] },
     erw ["<-", expr this] [],
     simp [] [] ["only"] ["[", expr yoneda_map_app, ",", expr functor_to_types.comp, "]"] [] [],
     erw [expr category.id_comp] []
   end⟩ }

@[simp]
theorem from_costructured_arrow_obj_mk (F : «expr ᵒᵖ» C ⥤ Type v) {X : C} (f : yoneda.obj X ⟶ F) :
  (from_costructured_arrow F).obj (op (costructured_arrow.mk f)) = ⟨op X, yoneda_equiv.1 f⟩ :=
  rfl

-- error in CategoryTheory.Elements: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The unit of the equivalence `F.elementsᵒᵖ ≅ (yoneda, F)` is indeed iso. -/
theorem from_to_costructured_arrow_eq
(F : «expr ⥤ »(«expr ᵒᵖ»(C), Type v)) : «expr = »(«expr ⋙ »((to_costructured_arrow F).right_op, from_costructured_arrow F), «expr𝟭»() _) :=
begin
  apply [expr functor.ext],
  intros [ident X, ident Y, ident f],
  have [] [":", expr ∀
   {a b : F.elements}
   (H : «expr = »(a, b)), «expr = »(«expr↑ »(eq_to_hom H), eq_to_hom (show «expr = »(a.fst, b.fst), by { cases [expr H] [],
       refl }))] [":=", expr λ _ _ H, by { cases [expr H] [], refl }],
  ext [] [] [],
  simp [] [] [] ["[", expr this, "]"] [] [],
  tidy []
end

/-- The counit of the equivalence `F.elementsᵒᵖ ≅ (yoneda, F)` is indeed iso. -/
theorem to_from_costructured_arrow_eq (F : «expr ᵒᵖ» C ⥤ Type v) :
  (from_costructured_arrow F).rightOp ⋙ to_costructured_arrow F = 𝟭 _ :=
  by 
    apply functor.hext
    ·
      intro X 
      cases X 
      cases X_right 
      simp only [functor.id_obj, functor.right_op_obj, to_costructured_arrow_obj, functor.comp_obj,
        costructured_arrow.mk]
      congr 
      ext x f 
      convert congr_funₓ (X_hom.naturality f.op).symm (𝟙 X_left)
      simp only [Quiver.Hom.unop_op, yoneda_obj_map]
      erw [category.comp_id]
    intro X Y f 
    cases X 
    cases Y 
    cases f 
    cases X_right 
    cases Y_right 
    simp [costructured_arrow.hom_mk]
    delta' costructured_arrow.mk 
    congr
    ·
      ext x f 
      convert congr_funₓ (X_hom.naturality f.op).symm (𝟙 X_left)
      simp only [Quiver.Hom.unop_op, CategoryTheory.yoneda_obj_map]
      erw [category.comp_id]
    ·
      ext x f 
      convert congr_funₓ (Y_hom.naturality f.op).symm (𝟙 Y_left)
      simp only [Quiver.Hom.unop_op, CategoryTheory.yoneda_obj_map]
      erw [category.comp_id]
    simp 
    exact proof_irrel_heq _ _

/-- The equivalence `F.elementsᵒᵖ ≅ (yoneda, F)` given by yoneda lemma. -/
@[simps]
def costructured_arrow_yoneda_equivalence (F : «expr ᵒᵖ» C ⥤ Type v) :
  «expr ᵒᵖ» F.elements ≌ costructured_arrow yoneda F :=
  equivalence.mk (to_costructured_arrow F) (from_costructured_arrow F).rightOp
    (nat_iso.op (eq_to_iso (from_to_costructured_arrow_eq F))) (eq_to_iso$ to_from_costructured_arrow_eq F)

-- error in CategoryTheory.Elements: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The equivalence `(-.elements)ᵒᵖ ≅ (yoneda, -)` of is actually a natural isomorphism of functors.
-/
theorem costructured_arrow_yoneda_equivalence_naturality
{F₁ F₂ : «expr ⥤ »(«expr ᵒᵖ»(C), Type v)}
(α : «expr ⟶ »(F₁, F₂)) : «expr = »(«expr ⋙ »((map α).op, to_costructured_arrow F₂), «expr ⋙ »(to_costructured_arrow F₁, costructured_arrow.map α)) :=
begin
  fapply [expr functor.ext],
  { intro [ident X],
    simp [] [] ["only"] ["[", expr costructured_arrow.map_mk, ",", expr to_costructured_arrow_obj, ",", expr functor.op_obj, ",", expr functor.comp_obj, "]"] [] [],
    congr,
    ext [] [ident x, ident f] [],
    simpa [] [] [] [] [] ["using", expr congr_fun (α.naturality f.op).symm (unop X).snd] },
  { intros [ident X, ident Y, ident f],
    ext [] [] [],
    have [] [":", expr ∀
     {F : «expr ⥤ »(«expr ᵒᵖ»(C), Type v)}
     {a b : costructured_arrow yoneda F}
     (H : «expr = »(a, b)), «expr = »(comma_morphism.left (eq_to_hom H), eq_to_hom (show «expr = »(a.left, b.left), by { cases [expr H] [],
         refl }))] [":=", expr λ _ _ _ H, by { cases [expr H] [], refl }],
    simp [] [] [] ["[", expr this, "]"] [] [] }
end

end CategoryOfElements

end CategoryTheory

