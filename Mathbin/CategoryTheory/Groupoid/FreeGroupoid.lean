/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import Mathbin.CategoryTheory.Category.Basic
import Mathbin.CategoryTheory.Functor.Basic
import Mathbin.CategoryTheory.Groupoid
import Mathbin.Combinatorics.Quiver.Basic
import Mathbin.Combinatorics.Quiver.ConnectedComponent
import Mathbin.Logic.Relation
import Mathbin.Tactic.NthRewrite.Default
import Mathbin.CategoryTheory.PathCategory
import Mathbin.CategoryTheory.Quotient

/-!
# Free groupoid on a quiver

This file defines the free groupoid on a quiver, the lifting of a prefunctor to its unique
extension as a functor from the free groupoid, and proves uniqueness of this extension.

## Main results

Given the type `V` and a quiver instance on `V`:

- `free_groupoid V`: a type synonym for `V`.
- `free_groupoid_groupoid`: the `groupoid` instance on `free_groupoid V`.
- `lift`: the lifting of a prefunctor from `V` to `V'` where `V'` is a groupoid, to a functor.
  `free_groupoid V ⥤ V'`.
- `lift_spec` and `lift_unique`: the proofs that, respectively, `lift` indeed is a lifting
  and is the unique one.

## Implementation notes

The free groupoid is first defined by symmetrifying the quiver, taking the induced path category
and finally quotienting by the reducibility relation.

-/


open Set Classical Function Relation

attribute [local instance] prop_decidable

namespace CategoryTheory

namespace Groupoid

namespace Free

universe u v u' v'

variable {V : Type u} [Quiver.{v + 1} V]

/-- Shorthand for the "forward" arrow corresponding to `f` in `symmetrify V` -/
abbrev Quiver.Hom.toPos {X Y : V} (f : X ⟶ Y) : (Quiver.symmetrifyQuiver V).Hom X Y :=
  Sum.inl f

/-- Shorthand for the "backward" arrow corresponding to `f` in `symmetrify V` -/
abbrev Quiver.Hom.toNeg {X Y : V} (f : X ⟶ Y) : (Quiver.symmetrifyQuiver V).Hom Y X :=
  Sum.inr f

/-- Shorthand for the "forward" arrow corresponding to `f` in `paths $ symmetrify V` -/
abbrev Quiver.Hom.toPosPath {X Y : V} (f : X ⟶ Y) :
    (CategoryTheory.Paths.categoryPaths <| Quiver.Symmetrify V).Hom X Y :=
  f.toPos.toPath

/-- Shorthand for the "forward" arrow corresponding to `f` in `paths $ symmetrify V` -/
abbrev Quiver.Hom.toNegPath {X Y : V} (f : X ⟶ Y) :
    (CategoryTheory.Paths.categoryPaths <| Quiver.Symmetrify V).Hom Y X :=
  f.toNeg.toPath

/-- The "reduction" relation -/
inductive RedStep : HomRel (Paths (Quiver.Symmetrify V))
  | step (X Z : Quiver.Symmetrify V) (f : X ⟶ Z) : red_step (𝟙 X) (f.toPath ≫ (Quiver.reverse f).toPath)

/-- The underlying vertices of the free groupoid -/
def FreeGroupoid (V) [Q : Quiver.{v + 1} V] :=
  Quotient (@RedStep V Q)

instance {V} [Q : Quiver.{v + 1} V] [h : Nonempty V] : Nonempty (FreeGroupoid V) :=
  ⟨⟨h.some⟩⟩

theorem congr_reverse {X Y : paths <| Quiver.Symmetrify V} (p q : X ⟶ Y) :
    Quotient.CompClosure RedStep p q → Quotient.CompClosure RedStep p.reverse q.reverse := by
  rintro ⟨U, W, XW, pp, qq, WY, ⟨_, Z, f⟩⟩
  have :
    quotient.comp_closure red_step (WY.reverse ≫ 𝟙 _ ≫ XW.reverse)
      (WY.reverse ≫ (f.to_path ≫ (Quiver.reverse f).toPath) ≫ XW.reverse) :=
    by
    apply quotient.comp_closure.intro
    apply red_step.step
  simpa only [category_struct.comp, category_struct.id, Quiver.Path.reverseₓ, Quiver.Path.nil_comp,
    Quiver.Path.reverse_comp, Quiver.reverse_reverse, Quiver.Path.reverse_to_path, Quiver.Path.comp_assoc] using this

theorem congr_comp_reverse {X Y : paths <| Quiver.Symmetrify V} (p : X ⟶ Y) :
    Quot.mk (@Quotient.CompClosure _ _ RedStep _ _) (p ≫ p.reverse) =
      Quot.mk (@Quotient.CompClosure _ _ RedStep _ _) (𝟙 X) :=
  by
  apply Quot.eqv_gen_sound
  induction' p with _ _ q f ih
  · apply EqvGen.refl
    
  · simp only [Quiver.Path.reverseₓ]
    fapply EqvGen.trans
    · exact q ≫ q.reverse
      
    · apply EqvGen.symm
      apply EqvGen.rel
      have :
        quotient.comp_closure red_step (q ≫ 𝟙 _ ≫ q.reverse)
          (q ≫ (f.to_path ≫ (Quiver.reverse f).toPath) ≫ q.reverse) :=
        by
        apply quotient.comp_closure.intro
        apply red_step.step
      have that : q.cons f = q.comp f.to_path := by rfl
      rw [that]
      simp only [category.assoc, category.id_comp] at this⊢
      simp only [category_struct.comp, Quiver.Path.comp_assoc] at this⊢
      exact this
      
    · exact ih
      
    

theorem congr_reverse_comp {X Y : paths <| Quiver.Symmetrify V} (p : X ⟶ Y) :
    Quot.mk (@Quotient.CompClosure _ _ RedStep _ _) (p.reverse ≫ p) =
      Quot.mk (@Quotient.CompClosure _ _ RedStep _ _) (𝟙 Y) :=
  by
  nth_rw 1 [← Quiver.Path.reverse_reverse p]
  apply congr_comp_reverse

instance : Category (FreeGroupoid V) :=
  Quotient.category RedStep

/-- The inverse of an arrow in the free groupoid -/
def quotInv {X Y : FreeGroupoid V} (f : X ⟶ Y) : Y ⟶ X :=
  Quot.liftOn f (fun pp => Quot.mk _ <| pp.reverse) fun pp qq con => Quot.sound <| congr_reverse pp qq con

instance : Groupoid (FreeGroupoid V) where
  inv := fun X Y f => quotInv f
  inv_comp' := fun X Y p => (Quot.induction_on p) fun pp => congr_reverse_comp pp
  comp_inv' := fun X Y p => (Quot.induction_on p) fun pp => congr_comp_reverse pp

/-- The inclusion of the quiver on `V` to the underlying quiver on `free_groupoid V`-/
def of : Prefunctor V (FreeGroupoid V) where
  obj := fun X => ⟨X⟩
  map := fun X Y f => Quot.mk _ f.toPosPath

theorem of_eq : of = (Quiver.Symmetrify.of.comp Paths.of).comp (quotient.functor <| @RedStep V _).toPrefunctor := by
  apply Prefunctor.ext
  rotate_left
  · rintro X
    rfl
    
  · rintro X Y f
    rfl
    

section UniversalProperty

variable {V' : Type u'} [Groupoid V'] (φ : Prefunctor V V')

/-- The lift of a prefunctor to a groupoid, to a functor from `free_groupoid V` -/
def lift (φ : Prefunctor V V') : FreeGroupoid V ⥤ V' :=
  Quotient.lift _ (paths.lift <| Quiver.Symmetrify.lift φ)
    (by
      rintro _ _ _ _ ⟨X, Y, f⟩
      simp only [Quiver.Symmetrify.lift_reverse, paths.lift_nil, Quiver.Path.comp_nil, paths.lift_cons,
        paths.lift_to_path]
      symm
      apply groupoid.comp_inv)

theorem lift_spec (φ : Prefunctor V V') : of.comp (lift φ).toPrefunctor = φ := by
  rw [of_eq, Prefunctor.comp_assoc, Prefunctor.comp_assoc, functor.to_prefunctor_comp]
  dsimp [lift]
  rw [quotient.lift_spec, paths.lift_spec, Quiver.Symmetrify.lift_spec]

theorem lift_unique_spec (φ : Prefunctor V V') (Φ : FreeGroupoid V ⥤ V') (hΦ : of.comp Φ.toPrefunctor = φ) :
    Φ = lift φ := by
  apply quotient.lift_spec_unique
  apply paths.lift_spec_unique
  apply Quiver.Symmetrify.lift_spec_unique
  · rw [← functor.to_prefunctor_comp]
    exact hΦ
    
  · rintro X Y f
    simp [← functor.to_prefunctor_comp, Prefunctor.comp_map, paths.of_map, inv_eq_inv]
    change
      Φ.map (inv ((quotient.functor red_step).toPrefunctor.map f.to_path)) =
        inv (Φ.map ((quotient.functor red_step).toPrefunctor.map f.to_path))
    have := functor.map_inv Φ ((quotient.functor red_step).toPrefunctor.map f.to_path)
    convert this <;> simp only [inv_eq_inv]
    

end UniversalProperty

end Free

end Groupoid

end CategoryTheory

