import Mathbin.CategoryTheory.Opposites

/-!
# Morphisms from equations between objects.

When working categorically, sometimes one encounters an equation `h : X = Y` between objects.

Your initial aversion to this is natural and appropriate:
you're in for some trouble, and if there is another way to approach the problem that won't
rely on this equality, it may be worth pursuing.

You have two options:
1. Use the equality `h` as one normally would in Lean (e.g. using `rw` and `subst`).
   This may immediately cause difficulties, because in category theory everything is dependently
   typed, and equations between objects quickly lead to nasty goals with `eq.rec`.
2. Promote `h` to a morphism using `eq_to_hom h : X ⟶ Y`, or `eq_to_iso h : X ≅ Y`.

This file introduces various `simp` lemmas which in favourable circumstances
result in the various `eq_to_hom` morphisms to drop out at the appropriate moment!
-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite

variable{C : Type u₁}[category.{v₁} C]

/--
An equality `X = Y` gives us a morphism `X ⟶ Y`.

It is typically better to use this, rather than rewriting by the equality then using `𝟙 _`
which usually leads to dependent type theory hell.
-/
def eq_to_hom {X Y : C} (p : X = Y) : X ⟶ Y :=
  by 
    rw [p] <;> exact 𝟙 _

@[simp]
theorem eq_to_hom_refl (X : C) (p : X = X) : eq_to_hom p = 𝟙 X :=
  rfl

@[simp, reassoc]
theorem eq_to_hom_trans {X Y Z : C} (p : X = Y) (q : Y = Z) : eq_to_hom p ≫ eq_to_hom q = eq_to_hom (p.trans q) :=
  by 
    cases p 
    cases q 
    simp 

/--
If we (perhaps unintentionally) perform equational rewriting on
the source object of a morphism,
we can replace the resulting `_.mpr f` term by a composition with an `eq_to_hom`.

It may be advisable to introduce any necessary `eq_to_hom` morphisms manually,
rather than relying on this lemma firing.
-/
@[simp]
theorem congr_arg_mpr_hom_left {X Y Z : C} (p : X = Y) (q : Y ⟶ Z) :
  (congr_argₓ (fun W : C => W ⟶ Z) p).mpr q = eq_to_hom p ≫ q :=
  by 
    cases p 
    simp 

/--
If we (perhaps unintentionally) perform equational rewriting on
the target object of a morphism,
we can replace the resulting `_.mpr f` term by a composition with an `eq_to_hom`.

It may be advisable to introduce any necessary `eq_to_hom` morphisms manually,
rather than relying on this lemma firing.
-/
@[simp]
theorem congr_arg_mpr_hom_right {X Y Z : C} (p : X ⟶ Y) (q : Z = Y) :
  (congr_argₓ (fun W : C => X ⟶ W) q).mpr p = p ≫ eq_to_hom q.symm :=
  by 
    cases q 
    simp 

/--
An equality `X = Y` gives us an isomorphism `X ≅ Y`.

It is typically better to use this, rather than rewriting by the equality then using `iso.refl _`
which usually leads to dependent type theory hell.
-/
def eq_to_iso {X Y : C} (p : X = Y) : X ≅ Y :=
  ⟨eq_to_hom p, eq_to_hom p.symm,
    by 
      simp ,
    by 
      simp ⟩

@[simp]
theorem eq_to_iso.hom {X Y : C} (p : X = Y) : (eq_to_iso p).Hom = eq_to_hom p :=
  rfl

@[simp]
theorem eq_to_iso.inv {X Y : C} (p : X = Y) : (eq_to_iso p).inv = eq_to_hom p.symm :=
  rfl

@[simp]
theorem eq_to_iso_refl {X : C} (p : X = X) : eq_to_iso p = iso.refl X :=
  rfl

@[simp]
theorem eq_to_iso_trans {X Y Z : C} (p : X = Y) (q : Y = Z) : eq_to_iso p ≪≫ eq_to_iso q = eq_to_iso (p.trans q) :=
  by 
    ext <;> simp 

@[simp]
theorem eq_to_hom_op {X Y : C} (h : X = Y) : (eq_to_hom h).op = eq_to_hom (congr_argₓ op h.symm) :=
  by 
    cases h 
    rfl

@[simp]
theorem eq_to_hom_unop {X Y : «expr ᵒᵖ» C} (h : X = Y) : (eq_to_hom h).unop = eq_to_hom (congr_argₓ unop h.symm) :=
  by 
    cases h 
    rfl

instance  {X Y : C} (h : X = Y) : is_iso (eq_to_hom h) :=
  is_iso.of_iso (eq_to_iso h)

@[simp]
theorem inv_eq_to_hom {X Y : C} (h : X = Y) : inv (eq_to_hom h) = eq_to_hom h.symm :=
  by 
    ext 
    simp 

variable{D : Type u₂}[category.{v₂} D]

namespace Functor

-- error in CategoryTheory.EqToHom: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Proving equality between functors. This isn't an extensionality lemma,
  because usually you don't really want to do this. -/
theorem ext
{F G : «expr ⥤ »(C, D)}
(h_obj : ∀ X, «expr = »(F.obj X, G.obj X))
(h_map : ∀
 X
 Y
 f, «expr = »(F.map f, «expr ≫ »(eq_to_hom (h_obj X), «expr ≫ »(G.map f, eq_to_hom (h_obj Y).symm)))) : «expr = »(F, G) :=
begin
  cases [expr F] ["with", ident F_obj, "_", "_", "_"],
  cases [expr G] ["with", ident G_obj, "_", "_", "_"],
  have [] [":", expr «expr = »(F_obj, G_obj)] [],
  by ext [] [ident X] []; apply [expr h_obj],
  subst [expr this],
  congr,
  funext [ident X, ident Y, ident f],
  simpa [] [] [] [] [] ["using", expr h_map X Y f]
end

-- error in CategoryTheory.EqToHom: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Proving equality between functors using heterogeneous equality. -/
theorem hext
{F G : «expr ⥤ »(C, D)}
(h_obj : ∀ X, «expr = »(F.obj X, G.obj X))
(h_map : ∀ (X Y) (f : «expr ⟶ »(X, Y)), «expr == »(F.map f, G.map f)) : «expr = »(F, G) :=
begin
  cases [expr F] ["with", ident F_obj, "_", "_", "_"],
  cases [expr G] ["with", ident G_obj, "_", "_", "_"],
  have [] [":", expr «expr = »(F_obj, G_obj)] [],
  by ext [] [ident X] []; apply [expr h_obj],
  subst [expr this],
  congr,
  funext [ident X, ident Y, ident f],
  exact [expr eq_of_heq (h_map X Y f)]
end

theorem congr_obj {F G : C ⥤ D} (h : F = G) X : F.obj X = G.obj X :=
  by 
    subst h

theorem congr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) :
  F.map f = eq_to_hom (congr_obj h X) ≫ G.map f ≫ eq_to_hom (congr_obj h Y).symm :=
  by 
    subst h <;> simp 

end Functor

@[simp]
theorem eq_to_hom_map (F : C ⥤ D) {X Y : C} (p : X = Y) : F.map (eq_to_hom p) = eq_to_hom (congr_argₓ F.obj p) :=
  by 
    cases p <;> simp 

@[simp]
theorem eq_to_iso_map (F : C ⥤ D) {X Y : C} (p : X = Y) : F.map_iso (eq_to_iso p) = eq_to_iso (congr_argₓ F.obj p) :=
  by 
    ext <;> cases p <;> simp 

@[simp]
theorem eq_to_hom_app {F G : C ⥤ D} (h : F = G) (X : C) :
  (eq_to_hom h : F ⟶ G).app X = eq_to_hom (functor.congr_obj h X) :=
  by 
    subst h <;> rfl

theorem nat_trans.congr {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (h : X = Y) :
  α.app X = F.map (eq_to_hom h) ≫ α.app Y ≫ G.map (eq_to_hom h.symm) :=
  by 
    rw [α.naturality_assoc]
    simp 

theorem eq_conj_eq_to_hom {X Y : C} (f : X ⟶ Y) : f = eq_to_hom rfl ≫ f ≫ eq_to_hom rfl :=
  by 
    simp only [category.id_comp, eq_to_hom_refl, category.comp_id]

end CategoryTheory

