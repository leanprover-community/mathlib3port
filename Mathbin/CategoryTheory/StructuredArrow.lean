import Mathbin.CategoryTheory.Comma 
import Mathbin.CategoryTheory.Punit 
import Mathbin.CategoryTheory.Limits.Shapes.Terminal

/-!
# The category of "structured arrows"

For `T : C ⥤ D`, a `T`-structured arrow with source `S : D`
is just a morphism `S ⟶ T.obj Y`, for some `Y : C`.

These form a category with morphisms `g : Y ⟶ Y'` making the obvious diagram commute.

We prove that `𝟙 (T.obj Y)` is the initial object in `T`-structured objects with source `T.obj Y`.
-/


namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

-- error in CategoryTheory.StructuredArrow: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler category
/--
The category of `T`-structured arrows with domain `S : D` (here `T : C ⥤ D`),
has as its objects `D`-morphisms of the form `S ⟶ T Y`, for some `Y : C`,
and morphisms `C`-morphisms `Y ⟶ Y'` making the obvious triangle commute.
-/
@[derive #[expr category], nolint #[ident has_inhabited_instance]]
def structured_arrow (S : D) (T : «expr ⥤ »(C, D)) :=
comma (functor.from_punit S) T

namespace StructuredArrow

/-- The obvious projection functor from structured arrows. -/
@[simps]
def proj (S : D) (T : C ⥤ D) : structured_arrow S T ⥤ C :=
  comma.snd _ _

variable {S S' S'' : D} {Y Y' : C} {T : C ⥤ D}

/-- Construct a structured arrow from a morphism. -/
def mk (f : S ⟶ T.obj Y) : structured_arrow S T :=
  ⟨⟨⟩, Y, f⟩

@[simp]
theorem mk_left (f : S ⟶ T.obj Y) : (mk f).left = PUnit.unit :=
  rfl

@[simp]
theorem mk_right (f : S ⟶ T.obj Y) : (mk f).right = Y :=
  rfl

@[simp]
theorem mk_hom_eq_self (f : S ⟶ T.obj Y) : (mk f).Hom = f :=
  rfl

-- error in CategoryTheory.StructuredArrow: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp, reassoc #[]]
theorem w {A B : structured_arrow S T} (f : «expr ⟶ »(A, B)) : «expr = »(«expr ≫ »(A.hom, T.map f.right), B.hom) :=
by { have [] [] [":=", expr f.w]; tidy [] }

theorem eq_mk (f : structured_arrow S T) : f = mk f.hom :=
  by 
    cases f 
    congr 
    ext

/--
To construct a morphism of structured arrows,
we need a morphism of the objects underlying the target,
and to check that the triangle commutes.
-/
@[simps]
def hom_mk {f f' : structured_arrow S T} (g : f.right ⟶ f'.right) (w : f.hom ≫ T.map g = f'.hom) : f ⟶ f' :=
  { left :=
      eq_to_hom
        (by 
          ext),
    right := g,
    w' :=
      by 
        dsimp 
        simpa using w.symm }

/--
Given a structured arrow `X ⟶ F(U)`, and an arrow `U ⟶ Y`, we can construct a morphism of
structured arrow given by `(X ⟶ F(U)) ⟶ (X ⟶ F(U) ⟶ F(Y))`.
-/
def hom_mk' {F : C ⥤ D} {X : D} {Y : C} (U : structured_arrow X F) (f : U.right ⟶ Y) : U ⟶ mk (U.hom ≫ F.map f) :=
  { right := f }

/--
To construct an isomorphism of structured arrows,
we need an isomorphism of the objects underlying the target,
and to check that the triangle commutes.
-/
@[simps]
def iso_mk {f f' : structured_arrow S T} (g : f.right ≅ f'.right) (w : f.hom ≫ T.map g.hom = f'.hom) : f ≅ f' :=
  comma.iso_mk
    (eq_to_iso
      (by 
        ext))
    g
    (by 
      simpa using w.symm)

/--
A morphism between source objects `S ⟶ S'`
contravariantly induces a functor between structured arrows,
`structured_arrow S' T ⥤ structured_arrow S T`.

Ideally this would be described as a 2-functor from `D`
(promoted to a 2-category with equations as 2-morphisms)
to `Cat`.
-/
@[simps]
def map (f : S ⟶ S') : structured_arrow S' T ⥤ structured_arrow S T :=
  comma.map_left _ ((Functor.Const _).map f)

@[simp]
theorem map_mk {f : S' ⟶ T.obj Y} (g : S ⟶ S') : (map g).obj (mk f) = mk (g ≫ f) :=
  rfl

@[simp]
theorem map_id {f : structured_arrow S T} : (map (𝟙 S)).obj f = f :=
  by 
    rw [eq_mk f]
    simp 

@[simp]
theorem map_comp {f : S ⟶ S'} {f' : S' ⟶ S''} {h : structured_arrow S'' T} :
  (map (f ≫ f')).obj h = (map f).obj ((map f').obj h) :=
  by 
    rw [eq_mk h]
    simp 

instance proj_reflects_iso : reflects_isomorphisms (proj S T) :=
  { reflects :=
      fun Y Z f t =>
        by 
          exact
            ⟨⟨structured_arrow.hom_mk (inv ((proj S T).map f))
                  (by 
                    simp ),
                by 
                  tidy⟩⟩ }

open CategoryTheory.Limits

/-- The identity structured arrow is initial. -/
def mk_id_initial [full T] [faithful T] : is_initial (mk (𝟙 (T.obj Y))) :=
  { desc :=
      fun c =>
        hom_mk (T.preimage c.X.hom)
          (by 
            dsimp 
            simp ),
    uniq' :=
      fun c m _ =>
        by 
          ext 
          apply T.map_injective 
          simpa only [hom_mk_right, T.image_preimage, ←w m] using (category.id_comp _).symm }

variable {A : Type u₃} [category.{v₃} A] {B : Type u₄} [category.{v₄} B]

/-- The functor `(S, F ⋙ G) ⥤ (S, G)`. -/
@[simps]
def pre (S : D) (F : B ⥤ C) (G : C ⥤ D) : structured_arrow S (F ⋙ G) ⥤ structured_arrow S G :=
  comma.pre_right _ F G

/-- The functor `(S, F) ⥤ (G(S), F ⋙ G)`. -/
@[simps]
def post (S : C) (F : B ⥤ C) (G : C ⥤ D) : structured_arrow S F ⥤ structured_arrow (G.obj S) (F ⋙ G) :=
  { obj := fun X => { right := X.right, Hom := G.map X.hom },
    map :=
      fun X Y f =>
        { right := f.right,
          w' :=
            by 
              simp [functor.comp_map, ←G.map_comp, ←f.w] } }

end StructuredArrow

-- error in CategoryTheory.StructuredArrow: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler category
/--
The category of `S`-costructured arrows with target `T : D` (here `S : C ⥤ D`),
has as its objects `D`-morphisms of the form `S Y ⟶ T`, for some `Y : C`,
and morphisms `C`-morphisms `Y ⟶ Y'` making the obvious triangle commute.
-/
@[derive #[expr category], nolint #[ident has_inhabited_instance]]
def costructured_arrow (S : «expr ⥤ »(C, D)) (T : D) :=
comma S (functor.from_punit T)

namespace CostructuredArrow

/-- The obvious projection functor from costructured arrows. -/
@[simps]
def proj (S : C ⥤ D) (T : D) : costructured_arrow S T ⥤ C :=
  comma.fst _ _

variable {T T' T'' : D} {Y Y' : C} {S : C ⥤ D}

/-- Construct a costructured arrow from a morphism. -/
def mk (f : S.obj Y ⟶ T) : costructured_arrow S T :=
  ⟨Y, ⟨⟩, f⟩

@[simp]
theorem mk_left (f : S.obj Y ⟶ T) : (mk f).left = Y :=
  rfl

@[simp]
theorem mk_right (f : S.obj Y ⟶ T) : (mk f).right = PUnit.unit :=
  rfl

@[simp]
theorem mk_hom_eq_self (f : S.obj Y ⟶ T) : (mk f).Hom = f :=
  rfl

@[simp, reassoc]
theorem w {A B : costructured_arrow S T} (f : A ⟶ B) : S.map f.left ≫ B.hom = A.hom :=
  by 
    tidy

theorem eq_mk (f : costructured_arrow S T) : f = mk f.hom :=
  by 
    cases f 
    congr 
    ext

/--
To construct a morphism of costructured arrows,
we need a morphism of the objects underlying the source,
and to check that the triangle commutes.
-/
@[simps]
def hom_mk {f f' : costructured_arrow S T} (g : f.left ⟶ f'.left) (w : S.map g ≫ f'.hom = f.hom) : f ⟶ f' :=
  { left := g,
    right :=
      eq_to_hom
        (by 
          ext),
    w' :=
      by 
        simpa using w }

/--
To construct an isomorphism of costructured arrows,
we need an isomorphism of the objects underlying the source,
and to check that the triangle commutes.
-/
@[simps]
def iso_mk {f f' : costructured_arrow S T} (g : f.left ≅ f'.left) (w : S.map g.hom ≫ f'.hom = f.hom) : f ≅ f' :=
  comma.iso_mk g
    (eq_to_iso
      (by 
        ext))
    (by 
      simpa using w)

/--
A morphism between target objects `T ⟶ T'`
covariantly induces a functor between costructured arrows,
`costructured_arrow S T ⥤ costructured_arrow S T'`.

Ideally this would be described as a 2-functor from `D`
(promoted to a 2-category with equations as 2-morphisms)
to `Cat`.
-/
@[simps]
def map (f : T ⟶ T') : costructured_arrow S T ⥤ costructured_arrow S T' :=
  comma.map_right _ ((Functor.Const _).map f)

@[simp]
theorem map_mk {f : S.obj Y ⟶ T} (g : T ⟶ T') : (map g).obj (mk f) = mk (f ≫ g) :=
  rfl

@[simp]
theorem map_id {f : costructured_arrow S T} : (map (𝟙 T)).obj f = f :=
  by 
    rw [eq_mk f]
    simp 

@[simp]
theorem map_comp {f : T ⟶ T'} {f' : T' ⟶ T''} {h : costructured_arrow S T} :
  (map (f ≫ f')).obj h = (map f').obj ((map f).obj h) :=
  by 
    rw [eq_mk h]
    simp 

instance proj_reflects_iso : reflects_isomorphisms (proj S T) :=
  { reflects :=
      fun Y Z f t =>
        by 
          exact
            ⟨⟨costructured_arrow.hom_mk (inv ((proj S T).map f))
                  (by 
                    simp ),
                by 
                  tidy⟩⟩ }

open CategoryTheory.Limits

/-- The identity costructured arrow is terminal. -/
def mk_id_terminal [full S] [faithful S] : is_terminal (mk (𝟙 (S.obj Y))) :=
  { lift :=
      fun c =>
        hom_mk (S.preimage c.X.hom)
          (by 
            dsimp 
            simp ),
    uniq' :=
      by 
        rintro c m -
        ext 
        apply S.map_injective 
        simpa only [hom_mk_left, S.image_preimage, ←w m] using (category.comp_id _).symm }

variable {A : Type u₃} [category.{v₃} A] {B : Type u₄} [category.{v₄} B]

/-- The functor `(F ⋙ G, S) ⥤ (G, S)`. -/
@[simps]
def pre (F : B ⥤ C) (G : C ⥤ D) (S : D) : costructured_arrow (F ⋙ G) S ⥤ costructured_arrow G S :=
  comma.pre_left F G _

/-- The functor `(F, S) ⥤ (F ⋙ G, G(S))`. -/
@[simps]
def post (F : B ⥤ C) (G : C ⥤ D) (S : C) : costructured_arrow F S ⥤ costructured_arrow (F ⋙ G) (G.obj S) :=
  { obj := fun X => { left := X.left, Hom := G.map X.hom },
    map :=
      fun X Y f =>
        { left := f.left,
          w' :=
            by 
              simp [functor.comp_map, ←G.map_comp, ←f.w] } }

end CostructuredArrow

open Opposite

namespace StructuredArrow

/--
For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of structured arrows `d ⟶ F.obj c` to the category of costructured arrows
`F.op.obj c ⟶ (op d)`.
-/
@[simps]
def to_costructured_arrow (F : C ⥤ D) (d : D) : «expr ᵒᵖ» (structured_arrow d F) ⥤ costructured_arrow F.op (op d) :=
  { obj := fun X => @costructured_arrow.mk _ _ _ _ _ (op X.unop.right) F.op X.unop.hom.op,
    map :=
      fun X Y f =>
        costructured_arrow.hom_mk f.unop.right.op
          (by 
            dsimp 
            rw [←op_comp, ←f.unop.w, functor.const.obj_map]
            erw [category.id_comp]) }

/--
For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of structured arrows `op d ⟶ F.op.obj c` to the category of costructured arrows
`F.obj c ⟶ d`.
-/
@[simps]
def to_costructured_arrow' (F : C ⥤ D) (d : D) : «expr ᵒᵖ» (structured_arrow (op d) F.op) ⥤ costructured_arrow F d :=
  { obj := fun X => @costructured_arrow.mk _ _ _ _ _ (unop X.unop.right) F X.unop.hom.unop,
    map :=
      fun X Y f =>
        costructured_arrow.hom_mk f.unop.right.unop
          (by 
            dsimp 
            rw [←Quiver.Hom.unop_op (F.map (Quiver.Hom.unop f.unop.right)), ←unop_comp, ←F.op_map, ←f.unop.w,
              functor.const.obj_map]
            erw [category.id_comp]) }

end StructuredArrow

namespace CostructuredArrow

/--
For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of costructured arrows `F.obj c ⟶ d` to the category of structured arrows
`op d ⟶ F.op.obj c`.
-/
@[simps]
def to_structured_arrow (F : C ⥤ D) (d : D) : «expr ᵒᵖ» (costructured_arrow F d) ⥤ structured_arrow (op d) F.op :=
  { obj := fun X => @structured_arrow.mk _ _ _ _ _ (op X.unop.left) F.op X.unop.hom.op,
    map :=
      fun X Y f =>
        structured_arrow.hom_mk f.unop.left.op
          (by 
            dsimp 
            rw [←op_comp, f.unop.w, functor.const.obj_map]
            erw [category.comp_id]) }

/--
For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of costructured arrows `F.op.obj c ⟶ op d` to the category of structured arrows
`d ⟶ F.obj c`.
-/
@[simps]
def to_structured_arrow' (F : C ⥤ D) (d : D) : «expr ᵒᵖ» (costructured_arrow F.op (op d)) ⥤ structured_arrow d F :=
  { obj := fun X => @structured_arrow.mk _ _ _ _ _ (unop X.unop.left) F X.unop.hom.unop,
    map :=
      fun X Y f =>
        structured_arrow.hom_mk f.unop.left.unop
          (by 
            dsimp 
            rw [←Quiver.Hom.unop_op (F.map f.unop.left.unop), ←unop_comp, ←F.op_map, f.unop.w, functor.const.obj_map]
            erw [category.comp_id]) }

end CostructuredArrow

/--
For a functor `F : C ⥤ D` and an object `d : D`, the category of structured arrows `d ⟶ F.obj c`
is contravariantly equivalent to the category of costructured arrows `F.op.obj c ⟶ op d`.
-/
def structured_arrow_op_equivalence (F : C ⥤ D) (d : D) :
  «expr ᵒᵖ» (structured_arrow d F) ≌ costructured_arrow F.op (op d) :=
  equivalence.mk (structured_arrow.to_costructured_arrow F d) (costructured_arrow.to_structured_arrow' F d).rightOp
    (nat_iso.of_components
      (fun X =>
        (@structured_arrow.iso_mk _ _ _ _ _ _ (structured_arrow.mk (unop X).Hom) (unop X) (iso.refl _)
            (by 
              tidy)).op)
      fun X Y f =>
        Quiver.Hom.unop_inj$
          by 
            ext 
            dsimp 
            simp )
    (nat_iso.of_components
      (fun X =>
        @costructured_arrow.iso_mk _ _ _ _ _ _ (costructured_arrow.mk X.hom) X (iso.refl _)
          (by 
            tidy))
      fun X Y f =>
        by 
          ext 
          dsimp 
          simp )

/--
For a functor `F : C ⥤ D` and an object `d : D`, the category of costructured arrows
`F.obj c ⟶ d` is contravariantly equivalent to the category of structured arrows
`op d ⟶ F.op.obj c`.
-/
def costructured_arrow_op_equivalence (F : C ⥤ D) (d : D) :
  «expr ᵒᵖ» (costructured_arrow F d) ≌ structured_arrow (op d) F.op :=
  equivalence.mk (costructured_arrow.to_structured_arrow F d) (structured_arrow.to_costructured_arrow' F d).rightOp
    (nat_iso.of_components
      (fun X =>
        (@costructured_arrow.iso_mk _ _ _ _ _ _ (costructured_arrow.mk (unop X).Hom) (unop X) (iso.refl _)
            (by 
              tidy)).op)
      fun X Y f =>
        Quiver.Hom.unop_inj$
          by 
            ext 
            dsimp 
            simp )
    (nat_iso.of_components
      (fun X =>
        @structured_arrow.iso_mk _ _ _ _ _ _ (structured_arrow.mk X.hom) X (iso.refl _)
          (by 
            tidy))
      fun X Y f =>
        by 
          ext 
          dsimp 
          simp )

end CategoryTheory

