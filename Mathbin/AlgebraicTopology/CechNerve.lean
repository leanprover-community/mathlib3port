import Mathbin.AlgebraicTopology.SimplicialObject 
import Mathbin.CategoryTheory.Limits.Shapes.WidePullbacks 
import Mathbin.CategoryTheory.Arrow

/-!

# The Čech Nerve

This file provides a definition of the Čech nerve associated to an arrow, provided
the base category has the correct wide pullbacks.

Several variants are provided, given `f : arrow C`:
1. `f.cech_nerve` is the Čech nerve, considered as a simplicial object in `C`.
2. `f.augmented_cech_nerve` is the augmented Čech nerve, considered as an
  augmented simplicial object in `C`.
3. `simplicial_object.cech_nerve` and `simplicial_object.augmented_cech_nerve` are
  functorial versions of 1 resp. 2.

-/


open CategoryTheory

open CategoryTheory.Limits

noncomputable theory

universe v u

variable {C : Type u} [category.{v} C]

namespace CategoryTheory.Arrow

variable (f : arrow C)

variable [∀ n : ℕ, has_wide_pullback f.right (fun i : Ulift (Finₓ (n+1)) => f.left) fun i => f.hom]

/-- The Čech nerve associated to an arrow. -/
@[simps]
def cech_nerve : simplicial_object C :=
  { obj := fun n => wide_pullback f.right (fun i : Ulift (Finₓ (n.unop.len+1)) => f.left) fun i => f.hom,
    map :=
      fun m n g =>
        wide_pullback.lift (wide_pullback.base _)
          (fun i => (wide_pullback.π fun i => f.hom)$ Ulift.up$ g.unop.to_preorder_hom i.down)
          (by 
            tidy) }

/-- The augmented Čech nerve associated to an arrow. -/
@[simps]
def augmented_cech_nerve : simplicial_object.augmented C :=
  { left := f.cech_nerve, right := f.right, Hom := { app := fun i => wide_pullback.base _ } }

end CategoryTheory.Arrow

namespace CategoryTheory

namespace SimplicialObject

variable [∀ n : ℕ f : arrow C, has_wide_pullback f.right (fun i : Ulift (Finₓ (n+1)) => f.left) fun i => f.hom]

/-- The Čech nerve construction, as a functor from `arrow C`. -/
@[simps]
def cech_nerve : arrow C ⥤ simplicial_object C :=
  { obj := fun f => f.cech_nerve,
    map :=
      fun f g F =>
        { app :=
            fun n =>
              wide_pullback.lift (wide_pullback.base _ ≫ F.right) (fun i => wide_pullback.π _ i ≫ F.left)
                fun i =>
                  by 
                    simp [←category.assoc] },
    map_id' :=
      by 
        intro i 
        ext 
        tidy,
    map_comp' :=
      by 
        intro f g h F G 
        ext 
        all_goals 
          dsimp 
          simp only [category.assoc, limits.wide_pullback.lift_base, limits.wide_pullback.lift_π,
            limits.limit.lift_π_assoc]
          simpa only [←category.assoc] }

/-- The augmented Čech nerve construction, as a functor from `arrow C`. -/
@[simps]
def augmented_cech_nerve : arrow C ⥤ simplicial_object.augmented C :=
  { obj := fun f => f.augmented_cech_nerve, map := fun f g F => { left := cech_nerve.map F, right := F.right } }

-- error in AlgebraicTopology.CechNerve: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A helper function used in defining the Čech adjunction. -/
@[simps #[]]
def equivalence_right_to_left
(X : simplicial_object.augmented C)
(F : arrow C)
(G : «expr ⟶ »(X, F.augmented_cech_nerve)) : «expr ⟶ »(augmented.to_arrow.obj X, F) :=
{ left := «expr ≫ »(G.left.app _, wide_pullback.π (λ i, F.hom) ⟨0⟩),
  right := G.right,
  w' := begin
    have [] [] [":=", expr G.w],
    apply_fun [expr λ e, e.app «expr $ »(opposite.op, simplex_category.mk 0)] ["at", ident this] [],
    tidy []
  end }

/-- A helper function used in defining the Čech adjunction. -/
@[simps]
def equivalence_left_to_right (X : simplicial_object.augmented C) (F : arrow C) (G : augmented.to_arrow.obj X ⟶ F) :
  X ⟶ F.augmented_cech_nerve :=
  { left :=
      { app :=
          fun x =>
            limits.wide_pullback.lift (X.hom.app _ ≫ G.right)
              (fun i => X.left.map (SimplexCategory.const x.unop i.down).op ≫ G.left)
              (by 
                tidy),
        naturality' :=
          by 
            intro x y f 
            ext
            ·
              dsimp 
              simp only [wide_pullback.lift_π, category.assoc]
              rw [←category.assoc, ←X.left.map_comp]
              rfl
            ·
              dsimp 
              simp only [functor.const.obj_map, nat_trans.naturality_assoc, wide_pullback.lift_base, category.assoc]
              erw [category.id_comp] },
    right := G.right }

-- error in AlgebraicTopology.CechNerve: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A helper function used in defining the Čech adjunction. -/
@[simps #[]]
def cech_nerve_equiv
(X : simplicial_object.augmented C)
(F : arrow C) : «expr ≃ »(«expr ⟶ »(augmented.to_arrow.obj X, F), «expr ⟶ »(X, F.augmented_cech_nerve)) :=
{ to_fun := equivalence_left_to_right _ _,
  inv_fun := equivalence_right_to_left _ _,
  left_inv := begin
    intro [ident A],
    dsimp [] [] [] [],
    ext [] [] [],
    { dsimp [] [] [] [],
      erw [expr wide_pullback.lift_π] [],
      nth_rewrite [1] ["<-", expr category.id_comp A.left] [],
      congr' [1] [],
      convert [] [expr X.left.map_id _] [],
      rw ["<-", expr op_id] [],
      congr' [1] [],
      ext [] ["⟨", ident a, ",", ident ha, "⟩"] [],
      change [expr «expr < »(a, 1)] [] ["at", ident ha],
      change [expr «expr = »(0, a)] [] [],
      linarith [] [] [] },
    { refl }
  end,
  right_inv := begin
    intro [ident A],
    dsimp [] [] [] [],
    ext [] ["_", "⟨", ident j, "⟩"] [],
    { dsimp [] [] [] [],
      simp [] [] ["only"] ["[", expr arrow.cech_nerve_map, ",", expr wide_pullback.lift_π, ",", expr nat_trans.naturality_assoc, "]"] [] [],
      erw [expr wide_pullback.lift_π] [],
      refl },
    { dsimp [] [] [] [],
      erw [expr wide_pullback.lift_base] [],
      have [] [] [":=", expr A.w],
      apply_fun [expr λ e, e.app x] ["at", ident this] [],
      rw [expr nat_trans.comp_app] ["at", ident this],
      erw [expr this] [],
      refl },
    { refl }
  end }

/-- The augmented Čech nerve construction is right adjoint to the `to_arrow` functor. -/
abbrev cech_nerve_adjunction : (augmented.to_arrow : _ ⥤ arrow C) ⊣ augmented_cech_nerve :=
  adjunction.mk_of_hom_equiv { homEquiv := cech_nerve_equiv }

end SimplicialObject

end CategoryTheory

namespace CategoryTheory.Arrow

variable (f : arrow C)

variable [∀ n : ℕ, has_wide_pushout f.left (fun i : Ulift (Finₓ (n+1)) => f.right) fun i => f.hom]

/-- The Čech conerve associated to an arrow. -/
@[simps]
def cech_conerve : cosimplicial_object C :=
  { obj := fun n => wide_pushout f.left (fun i : Ulift (Finₓ (n.len+1)) => f.right) fun i => f.hom,
    map :=
      fun m n g =>
        wide_pushout.desc (wide_pushout.head _)
          (fun i => (wide_pushout.ι fun i => f.hom)$ Ulift.up$ g.to_preorder_hom i.down)
          (by 
            rintro ⟨⟨j⟩⟩
            dsimp 
            rw [wide_pushout.arrow_ι fun i => f.hom]) }

/-- The augmented Čech conerve associated to an arrow. -/
@[simps]
def augmented_cech_conerve : cosimplicial_object.augmented C :=
  { left := f.left, right := f.cech_conerve, Hom := { app := fun i => wide_pushout.head _ } }

end CategoryTheory.Arrow

namespace CategoryTheory

namespace CosimplicialObject

variable [∀ n : ℕ f : arrow C, has_wide_pushout f.left (fun i : Ulift (Finₓ (n+1)) => f.right) fun i => f.hom]

/-- The Čech conerve construction, as a functor from `arrow C`. -/
@[simps]
def cech_conerve : arrow C ⥤ cosimplicial_object C :=
  { obj := fun f => f.cech_conerve,
    map :=
      fun f g F =>
        { app :=
            fun n =>
              wide_pushout.desc (F.left ≫ wide_pushout.head _) (fun i => F.right ≫ wide_pushout.ι _ i)
                fun i =>
                  by 
                    rw [←arrow.w_assoc F, wide_pushout.arrow_ι fun i => g.hom] },
    map_id' :=
      by 
        intro i 
        ext 
        tidy,
    map_comp' :=
      by 
        intro f g h F G 
        ext 
        all_goals 
          dsimp 
          simp only [category.assoc, limits.wide_pushout.head_desc_assoc, limits.wide_pushout.ι_desc_assoc,
            limits.colimit.ι_desc]
          simpa only [←category.assoc] }

/-- The augmented Čech conerve construction, as a functor from `arrow C`. -/
@[simps]
def augmented_cech_conerve : arrow C ⥤ cosimplicial_object.augmented C :=
  { obj := fun f => f.augmented_cech_conerve, map := fun f g F => { left := F.left, right := cech_conerve.map F } }

-- error in AlgebraicTopology.CechNerve: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A helper function used in defining the Čech conerve adjunction. -/
@[simps #[]]
def equivalence_left_to_right
(F : arrow C)
(X : cosimplicial_object.augmented C)
(G : «expr ⟶ »(F.augmented_cech_conerve, X)) : «expr ⟶ »(F, augmented.to_arrow.obj X) :=
{ left := G.left,
  right := («expr ≫ »(wide_pushout.ι (λ i, F.hom) (_root_.ulift.up 0), G.right.app (simplex_category.mk 0)) : _),
  w' := begin
    have [] [] [":=", expr G.w],
    apply_fun [expr λ e, e.app (simplex_category.mk 0)] ["at", ident this] [],
    dsimp [] [] [] ["at", ident this],
    simpa [] [] ["only"] ["[", expr category_theory.functor.id_map, ",", expr augmented.to_arrow_obj_hom, ",", expr wide_pushout.arrow_ι_assoc (λ
      i, F.hom), "]"] [] []
  end }

-- error in AlgebraicTopology.CechNerve: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A helper function used in defining the Čech conerve adjunction. -/
@[simps #[]]
def equivalence_right_to_left
(F : arrow C)
(X : cosimplicial_object.augmented C)
(G : «expr ⟶ »(F, augmented.to_arrow.obj X)) : «expr ⟶ »(F.augmented_cech_conerve, X) :=
{ left := G.left,
  right := { app := λ
    x, limits.wide_pushout.desc «expr ≫ »(G.left, X.hom.app _) (λ
     i, «expr ≫ »(G.right, X.right.map (simplex_category.const x i.down))) (begin
       rintros ["⟨", ident j, "⟩"],
       rw ["<-", expr arrow.w_assoc G] [],
       dsimp [] [] [] [],
       have [ident t] [] [":=", expr X.hom.naturality (x.const j)],
       dsimp [] [] [] ["at", ident t],
       simp [] [] ["only"] ["[", expr category.id_comp, "]"] [] ["at", ident t],
       rw ["<-", expr t] []
     end),
    naturality' := begin
      intros [ident x, ident y, ident f],
      ext [] [] [],
      { dsimp [] [] [] [],
        simp [] [] ["only"] ["[", expr wide_pushout.ι_desc_assoc, ",", expr wide_pushout.ι_desc, "]"] [] [],
        rw ["[", expr category.assoc, ",", "<-", expr X.right.map_comp, "]"] [],
        refl },
      { dsimp [] [] [] [],
        simp [] [] ["only"] ["[", expr functor.const.obj_map, ",", "<-", expr nat_trans.naturality, ",", expr wide_pushout.head_desc_assoc, ",", expr wide_pushout.head_desc, ",", expr category.assoc, "]"] [] [],
        erw [expr category.id_comp] [] }
    end } }

-- error in AlgebraicTopology.CechNerve: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A helper function used in defining the Čech conerve adjunction. -/
@[simps #[]]
def cech_conerve_equiv
(F : arrow C)
(X : cosimplicial_object.augmented C) : «expr ≃ »(«expr ⟶ »(F.augmented_cech_conerve, X), «expr ⟶ »(F, augmented.to_arrow.obj X)) :=
{ to_fun := equivalence_left_to_right _ _,
  inv_fun := equivalence_right_to_left _ _,
  left_inv := begin
    intro [ident A],
    dsimp [] [] [] [],
    ext [] [] [],
    { refl },
    { cases [expr j] [],
      dsimp [] [] [] [],
      simp [] [] ["only"] ["[", expr arrow.cech_conerve_map, ",", expr wide_pushout.ι_desc, ",", expr category.assoc, ",", "<-", expr nat_trans.naturality, ",", expr wide_pushout.ι_desc_assoc, "]"] [] [],
      refl },
    { dsimp [] [] [] [],
      erw [expr wide_pushout.head_desc] [],
      have [] [] [":=", expr A.w],
      apply_fun [expr λ e, e.app x] ["at", ident this] [],
      rw [expr nat_trans.comp_app] ["at", ident this],
      erw [expr this] [],
      refl }
  end,
  right_inv := begin
    intro [ident A],
    dsimp [] [] [] [],
    ext [] [] [],
    { refl },
    { dsimp [] [] [] [],
      erw [expr wide_pushout.ι_desc] [],
      nth_rewrite [1] ["<-", expr category.comp_id A.right] [],
      congr' [1] [],
      convert [] [expr X.right.map_id _] [],
      ext [] ["⟨", ident a, ",", ident ha, "⟩"] [],
      change [expr «expr < »(a, 1)] [] ["at", ident ha],
      change [expr «expr = »(0, a)] [] [],
      linarith [] [] [] }
  end }

/-- The augmented Čech conerve construction is left adjoint to the `to_arrow` functor. -/
abbrev cech_conerve_adjunction : augmented_cech_conerve ⊣ (augmented.to_arrow : _ ⥤ arrow C) :=
  adjunction.mk_of_hom_equiv { homEquiv := cech_conerve_equiv }

end CosimplicialObject

end CategoryTheory

