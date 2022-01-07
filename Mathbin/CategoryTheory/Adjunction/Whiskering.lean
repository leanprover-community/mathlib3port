import Mathbin.CategoryTheory.Adjunction.Default
import Mathbin.CategoryTheory.Whiskering

/-!

Given categories `C D E`, functors `F : D ⥤ E` and `G : E ⥤ D` with an adjunction
`F ⊣ G`, we provide the induced adjunction between the functor categories `C ⥤ D` and `C ⥤ E`,
and the functor categories `E ⥤ C` and `D ⥤ C`.

-/


namespace CategoryTheory.Adjunction

open CategoryTheory

variable (C : Type _) {D E : Type _} [category C] [category D] [category E] {F : D ⥤ E} {G : E ⥤ D}

/-- Given an adjunction `F ⊣ G`, this provides the natural adjunction
  `(whiskering_right C _ _).obj F ⊣ (whiskering_right C _ _).obj G`. -/
@[simps unit_app_app counit_app_app]
protected def whisker_right (adj : F ⊣ G) : (whiskering_right C D E).obj F ⊣ (whiskering_right C E D).obj G :=
  mk_of_unit_counit
    { Unit :=
        { app := fun X => (functor.right_unitor _).inv ≫ whisker_left X adj.unit ≫ (functor.associator _ _ _).inv,
          naturality' := by
            intros
            ext
            dsimp
            simp },
      counit :=
        { app := fun X => (functor.associator _ _ _).Hom ≫ whisker_left X adj.counit ≫ (functor.right_unitor _).Hom,
          naturality' := by
            intros
            ext
            dsimp
            simp },
      left_triangle' := by
        ext
        dsimp
        simp ,
      right_triangle' := by
        ext
        dsimp
        simp }

/-- Given an adjunction `F ⊣ G`, this provides the natural adjunction
  `(whiskering_left _ _ C).obj G ⊣ (whiskering_left _ _ C).obj F`. -/
@[simps unit_app_app counit_app_app]
protected def whisker_left (adj : F ⊣ G) : (whiskering_left E D C).obj G ⊣ (whiskering_left D E C).obj F :=
  mk_of_unit_counit
    { Unit :=
        { app := fun X => (functor.left_unitor _).inv ≫ whisker_right adj.unit X ≫ (functor.associator _ _ _).Hom,
          naturality' := by
            intros
            ext
            dsimp
            simp },
      counit :=
        { app := fun X => (functor.associator _ _ _).inv ≫ whisker_right adj.counit X ≫ (functor.left_unitor _).Hom,
          naturality' := by
            intros
            ext
            dsimp
            simp },
      left_triangle' := by
        ext x
        dsimp
        simp only [category.id_comp, category.comp_id, ← x.map_comp]
        simp ,
      right_triangle' := by
        ext x
        dsimp
        simp only [category.id_comp, category.comp_id, ← x.map_comp]
        simp }

end CategoryTheory.Adjunction

