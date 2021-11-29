import Mathbin.CategoryTheory.Limits.Shapes.Terminal 
import Mathbin.CategoryTheory.Punit 
import Mathbin.CategoryTheory.StructuredArrow

/-!

# Kan extensions

This file defines the right and left Kan extensions of a functor.
They exist under the assumption that the target category has enough limits
resp. colimits.

The main definitions are `Ran ι` and `Lan ι`, where `ι : S ⥤ L` is a functor.
Namely, `Ran ι` is the right Kan extension, while `Lan ι` is the left Kan extension,
both as functors `(S ⥤ D) ⥤ (L ⥤ D)`.

To access the right resp. left adjunction associated to these, use `Ran.adjunction`
resp. `Lan.adjunction`.

# Projects

A lot of boilerplate could be generalized by defining and working with pseudofunctors.

-/


noncomputable theory

namespace CategoryTheory

open Limits

universe v u₁ u₂ u₃

variable {S : Type v} {L : Type u₂} {D : Type u₃}

variable [category.{v} S] [category.{v} L] [category.{v} D]

variable (ι : S ⥤ L)

namespace Ran

attribute [local simp] structured_arrow.proj

/-- The diagram indexed by `Ran.index ι x` used to define `Ran`. -/
abbrev diagram (F : S ⥤ D) (x : L) : structured_arrow x ι ⥤ D :=
  structured_arrow.proj x ι ⋙ F

variable {ι}

-- error in CategoryTheory.Limits.KanExtension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A cone over `Ran.diagram ι F x` used to define `Ran`. -/
@[simp]
def cone
{F : «expr ⥤ »(S, D)}
{G : «expr ⥤ »(L, D)}
(x : L)
(f : «expr ⟶ »(«expr ⋙ »(ι, G), F)) : cone (diagram ι F x) :=
{ X := G.obj x,
  π := { app := λ i, «expr ≫ »(G.map i.hom, f.app i.right),
    naturality' := begin
      rintro ["⟨", "⟨", ident il, "⟩", ",", ident ir, ",", ident i, "⟩", "⟨", "⟨", ident jl, "⟩", ",", ident jr, ",", ident j, "⟩", "⟨", "⟨", "⟨", ident fl, "⟩", "⟩", ",", ident fr, ",", ident ff, "⟩"],
      dsimp [] [] [] ["at", "*"],
      simp [] [] ["only"] ["[", expr category.id_comp, ",", expr category.assoc, "]"] [] ["at", "*"],
      rw ["[", expr ff, "]"] [],
      have [] [] [":=", expr f.naturality],
      tidy []
    end } }

variable (ι)

/-- An auxiliary definition used to define `Ran`. -/
@[simps]
def loc (F : S ⥤ D) [∀ x, has_limit (diagram ι F x)] : L ⥤ D :=
  { obj := fun x => limit (diagram ι F x),
    map := fun x y f => limit.pre (diagram _ _ _) (structured_arrow.map f : structured_arrow _ ι ⥤ _),
    map_id' :=
      by 
        intro l 
        ext j 
        simp only [category.id_comp, limit.pre_π]
        congr 1
        simp ,
    map_comp' :=
      by 
        intro x y z f g 
        ext j 
        erw [limit.pre_pre, limit.pre_π, limit.pre_π]
        congr 1
        tidy }

/-- An auxiliary definition used to define `Ran` and `Ran.adjunction`. -/
@[simps]
def Equiv (F : S ⥤ D) [∀ x, has_limit (diagram ι F x)] (G : L ⥤ D) :
  (G ⟶ loc ι F) ≃ (((whiskering_left _ _ _).obj ι).obj G ⟶ F) :=
  { toFun :=
      fun f =>
        { app := fun x => f.app _ ≫ limit.π (diagram ι F (ι.obj x)) (structured_arrow.mk (𝟙 _)),
          naturality' :=
            by 
              intro x y ff 
              dsimp only [whiskering_left]
              simp only [functor.comp_map, nat_trans.naturality_assoc, loc_map, category.assoc]
              congr 1 
              erw [limit.pre_π]
              change _ = _ ≫ (diagram ι F (ι.obj x)).map (structured_arrow.hom_mk _ _)
              rw [limit.w]
              tidy },
    invFun :=
      fun f =>
        { app := fun x => limit.lift (diagram ι F x) (cone _ f),
          naturality' :=
            by 
              intro x y ff 
              ext j 
              erw [limit.lift_pre, limit.lift_π, category.assoc, limit.lift_π (cone _ f) j]
              tidy },
    left_inv :=
      by 
        intro x 
        ext k j 
        dsimp only [cone]
        rw [limit.lift_π]
        simp only [nat_trans.naturality_assoc, loc_map]
        erw [limit.pre_π]
        congr 
        cases j 
        tidy,
    right_inv :=
      by 
        tidy }

end Ran

/-- The right Kan extension of a functor. -/
@[simps]
def Ran [∀ X, has_limits_of_shape (structured_arrow X ι) D] : (S ⥤ D) ⥤ L ⥤ D :=
  adjunction.right_adjoint_of_equiv (fun F G => (Ran.equiv ι G F).symm)
    (by 
      tidy)

namespace Ran

variable (D)

/-- The adjunction associated to `Ran`. -/
def adjunction [∀ X, has_limits_of_shape (structured_arrow X ι) D] : (whiskering_left _ _ D).obj ι ⊣ Ran ι :=
  adjunction.adjunction_of_equiv_right _ _

theorem reflective [full ι] [faithful ι] [∀ X, has_limits_of_shape (structured_arrow X ι) D] :
  is_iso (adjunction D ι).counit :=
  by 
    apply nat_iso.is_iso_of_is_iso_app _ 
    intro F 
    apply nat_iso.is_iso_of_is_iso_app _ 
    intro X 
    dsimp [adjunction]
    simp only [category.id_comp]
    exact
      is_iso.of_iso
        ((limit.is_limit _).conePointUniqueUpToIso (limit_of_diagram_initial structured_arrow.mk_id_initial _))

end Ran

namespace Lan

attribute [local simp] costructured_arrow.proj

/-- The diagram indexed by `Ran.index ι x` used to define `Ran`. -/
abbrev diagram (F : S ⥤ D) (x : L) : costructured_arrow ι x ⥤ D :=
  costructured_arrow.proj ι x ⋙ F

variable {ι}

/-- A cocone over `Lan.diagram ι F x` used to define `Lan`. -/
@[simp]
def cocone {F : S ⥤ D} {G : L ⥤ D} (x : L) (f : F ⟶ ι ⋙ G) : cocone (diagram ι F x) :=
  { x := G.obj x,
    ι :=
      { app := fun i => f.app i.left ≫ G.map i.hom,
        naturality' :=
          by 
            rintro ⟨ir, ⟨il⟩, i⟩ ⟨jl, ⟨jr⟩, j⟩ ⟨fl, ⟨⟨fl⟩⟩, ff⟩
            dsimp  at *
            simp only [functor.comp_map, category.comp_id, nat_trans.naturality_assoc]
            rw [←G.map_comp, ff]
            tidy } }

variable (ι)

-- error in CategoryTheory.Limits.KanExtension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An auxiliary definition used to define `Lan`. -/
@[simps #[]]
def loc (F : «expr ⥤ »(S, D)) [I : ∀ x, has_colimit (diagram ι F x)] : «expr ⥤ »(L, D) :=
{ obj := λ x, colimit (diagram ι F x),
  map := λ x y f, colimit.pre (diagram _ _ _) (costructured_arrow.map f : «expr ⥤ »(costructured_arrow ι _, _)),
  map_id' := begin
    intro [ident l],
    ext [] [ident j] [],
    erw ["[", expr colimit.ι_pre, ",", expr category.comp_id, "]"] [],
    congr' [1] [],
    simp [] [] [] [] [] []
  end,
  map_comp' := begin
    intros [ident x, ident y, ident z, ident f, ident g],
    ext [] [ident j] [],
    let [ident ff] [":", expr «expr ⥤ »(costructured_arrow ι _, _)] [":=", expr costructured_arrow.map f],
    let [ident gg] [":", expr «expr ⥤ »(costructured_arrow ι _, _)] [":=", expr costructured_arrow.map g],
    let [ident dd] [] [":=", expr diagram ι F z],
    haveI [] [":", expr has_colimit «expr ⋙ »(ff, «expr ⋙ »(gg, dd))] [":=", expr I _],
    haveI [] [":", expr has_colimit «expr ⋙ »(«expr ⋙ »(ff, gg), dd)] [":=", expr I _],
    haveI [] [":", expr has_colimit «expr ⋙ »(gg, dd)] [":=", expr I _],
    change [expr «expr = »(_, «expr ≫ »(colimit.ι «expr ⋙ »(«expr ⋙ »(ff, gg), dd) j, «expr ≫ »(_, _)))] [] [],
    erw ["[", expr colimit.pre_pre dd gg ff, ",", expr colimit.ι_pre, ",", expr colimit.ι_pre, "]"] [],
    congr' [1] [],
    simp [] [] [] [] [] []
  end }

-- error in CategoryTheory.Limits.KanExtension: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An auxiliary definition used to define `Lan` and `Lan.adjunction`. -/
@[simps #[]]
def equiv
(F : «expr ⥤ »(S, D))
[I : ∀ x, has_colimit (diagram ι F x)]
(G : «expr ⥤ »(L, D)) : «expr ≃ »(«expr ⟶ »(loc ι F, G), «expr ⟶ »(F, ((whiskering_left _ _ _).obj ι).obj G)) :=
{ to_fun := λ
  f, { app := λ
    x, by apply [expr «expr ≫ »(colimit.ι (diagram ι F (ι.obj x)) (costructured_arrow.mk («expr𝟙»() _)), f.app _)],
    naturality' := begin
      intros [ident x, ident y, ident ff],
      dsimp ["only"] ["[", expr whiskering_left, "]"] [] [],
      simp [] [] ["only"] ["[", expr functor.comp_map, ",", expr category.assoc, "]"] [] [],
      rw ["[", "<-", expr f.naturality (ι.map ff), ",", "<-", expr category.assoc, ",", "<-", expr category.assoc, "]"] [],
      let [ident fff] [":", expr «expr ⥤ »(costructured_arrow ι _, _)] [":=", expr costructured_arrow.map (ι.map ff)],
      haveI [] [":", expr has_colimit «expr ⋙ »(fff, diagram ι F (ι.obj y))] [":=", expr I _],
      erw [expr colimit.ι_pre (diagram ι F (ι.obj y)) fff (costructured_arrow.mk («expr𝟙»() _))] [],
      let [ident xx] [":", expr costructured_arrow ι (ι.obj y)] [":=", expr costructured_arrow.mk (ι.map ff)],
      let [ident yy] [":", expr costructured_arrow ι (ι.obj y)] [":=", expr costructured_arrow.mk («expr𝟙»() _)],
      let [ident fff] [":", expr «expr ⟶ »(xx, yy)] [":=", expr costructured_arrow.hom_mk ff (by { simp [] [] ["only"] ["[", expr costructured_arrow.mk_hom_eq_self, "]"] [] [],
          erw [expr category.comp_id] [] })],
      erw [expr colimit.w (diagram ι F (ι.obj y)) fff] [],
      congr,
      simp [] [] [] [] [] []
    end },
  inv_fun := λ
  f, { app := λ x, colimit.desc (diagram ι F x) (cocone _ f),
    naturality' := begin
      intros [ident x, ident y, ident ff],
      ext [] [ident j] [],
      erw ["[", expr colimit.pre_desc, ",", "<-", expr category.assoc, ",", expr colimit.ι_desc, ",", expr colimit.ι_desc, "]"] [],
      tidy []
    end },
  left_inv := begin
    intro [ident x],
    ext [] [ident k, ident j] [],
    rw [expr colimit.ι_desc] [],
    dsimp ["only"] ["[", expr cocone, "]"] [] [],
    rw ["[", expr category.assoc, ",", "<-", expr x.naturality j.hom, ",", "<-", expr category.assoc, "]"] [],
    congr' [1] [],
    change [expr «expr = »(«expr ≫ »(colimit.ι _ _, colimit.pre (diagram ι F k) (costructured_arrow.map _)), _)] [] [],
    rw [expr colimit.ι_pre] [],
    congr,
    cases [expr j] [],
    tidy []
  end,
  right_inv := by tidy [] }

end Lan

/-- The left Kan extension of a functor. -/
@[simps]
def Lan [∀ X, has_colimits_of_shape (costructured_arrow ι X) D] : (S ⥤ D) ⥤ L ⥤ D :=
  adjunction.left_adjoint_of_equiv (fun F G => Lan.equiv ι F G)
    (by 
      tidy)

namespace Lan

variable (D)

/-- The adjunction associated to `Lan`. -/
def adjunction [∀ X, has_colimits_of_shape (costructured_arrow ι X) D] : Lan ι ⊣ (whiskering_left _ _ D).obj ι :=
  adjunction.adjunction_of_equiv_left _ _

theorem coreflective [full ι] [faithful ι] [∀ X, has_colimits_of_shape (costructured_arrow ι X) D] :
  is_iso (adjunction D ι).Unit :=
  by 
    apply nat_iso.is_iso_of_is_iso_app _ 
    intro F 
    apply nat_iso.is_iso_of_is_iso_app _ 
    intro X 
    dsimp [adjunction]
    simp only [category.comp_id]
    exact
      is_iso.of_iso
        ((colimit.is_colimit _).coconePointUniqueUpToIso
            (colimit_of_diagram_terminal costructured_arrow.mk_id_terminal _)).symm

end Lan

end CategoryTheory

