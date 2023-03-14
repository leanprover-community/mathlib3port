/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.limits.constructions.finite_products_of_binary_products
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathbin.Logic.Equiv.Fin

/-!
# Constructing finite products from binary products and terminal.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If a category has binary products and a terminal object then it has finite products.
If a functor preserves binary products and the terminal object then it preserves finite products.

# TODO

Provide the dual results.
Show the analogous results for functors which reflect or create (co)limits.
-/


universe v v' u u'

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory

variable {J : Type v} [SmallCategory J]

variable {C : Type u} [Category.{v} C]

variable {D : Type u'} [Category.{v'} D]

/- warning: category_theory.extend_fan -> CategoryTheory.extendFan is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} C] {n : Nat} {f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> C} (c₁ : CategoryTheory.Limits.Fan.{0, u1, u2} (Fin n) C _inst_2 (fun (i : Fin n) => f (Fin.succ n i))), (CategoryTheory.Limits.BinaryFan.{u1, u2} C _inst_2 (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin n) (fun (i : Fin n) => f (Fin.succ n i))) c₁)) -> (CategoryTheory.Limits.Fan.{0, u1, u2} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) C _inst_2 f)
but is expected to have type
  forall {C : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} C] {n : Nat} {f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> C} (c₁ : CategoryTheory.Limits.Fan.{0, u1, u2} (Fin n) C _inst_2 (fun (i : Fin n) => f (Fin.succ n i))), (CategoryTheory.Limits.BinaryFan.{u1, u2} C _inst_2 (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin n) (fun (i : Fin n) => f (Fin.succ n i))) c₁)) -> (CategoryTheory.Limits.Fan.{0, u1, u2} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) C _inst_2 f)
Case conversion may be inaccurate. Consider using '#align category_theory.extend_fan CategoryTheory.extendFanₓ'. -/
/--
Given `n+1` objects of `C`, a fan for the last `n` with point `c₁.X` and a binary fan on `c₁.X` and
`f 0`, we can build a fan for all `n+1`.

In `extend_fan_is_limit` we show that if the two given fans are limits, then this fan is also a
limit.
-/
@[simps (config := { rhsMd := semireducible })]
def extendFan {n : ℕ} {f : Fin (n + 1) → C} (c₁ : Fan fun i : Fin n => f i.succ)
    (c₂ : BinaryFan (f 0) c₁.pt) : Fan f :=
  Fan.mk c₂.pt
    (by
      refine' Fin.cases _ _
      · apply c₂.fst
      · intro i
        apply c₂.snd ≫ c₁.π.app ⟨i⟩)
#align category_theory.extend_fan CategoryTheory.extendFan

/- warning: category_theory.extend_fan_is_limit -> CategoryTheory.extendFanIsLimit is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} C] {n : Nat} (f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> C) {c₁ : CategoryTheory.Limits.Fan.{0, u1, u2} (Fin n) C _inst_2 (fun (i : Fin n) => f (Fin.succ n i))} {c₂ : CategoryTheory.Limits.BinaryFan.{u1, u2} C _inst_2 (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin n) (fun (i : Fin n) => f (Fin.succ n i))) c₁)}, (CategoryTheory.Limits.IsLimit.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin n) (fun (i : Fin n) => f (Fin.succ n i))) c₁) -> (CategoryTheory.Limits.IsLimit.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_2 (CategoryTheory.Limits.pair.{u1, u2} C _inst_2 (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin n) (fun (i : Fin n) => f (Fin.succ n i))) c₁)) c₂) -> (CategoryTheory.Limits.IsLimit.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (CategoryTheory.discreteCategory.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) f) (CategoryTheory.extendFan.{u1, u2} C _inst_2 n f c₁ c₂))
but is expected to have type
  forall {C : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} C] {n : Nat} (f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> C) {c₁ : CategoryTheory.Limits.Fan.{0, u1, u2} (Fin n) C _inst_2 (fun (i : Fin n) => f (Fin.succ n i))} {c₂ : CategoryTheory.Limits.BinaryFan.{u1, u2} C _inst_2 (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin n) (fun (i : Fin n) => f (Fin.succ n i))) c₁)}, (CategoryTheory.Limits.IsLimit.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin n) (fun (i : Fin n) => f (Fin.succ n i))) c₁) -> (CategoryTheory.Limits.IsLimit.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_2 (CategoryTheory.Limits.pair.{u1, u2} C _inst_2 (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (CategoryTheory.Limits.Cone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin n) (fun (i : Fin n) => f (Fin.succ n i))) c₁)) c₂) -> (CategoryTheory.Limits.IsLimit.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (CategoryTheory.discreteCategory.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) f) (CategoryTheory.extendFan.{u1, u2} C _inst_2 n f c₁ c₂))
Case conversion may be inaccurate. Consider using '#align category_theory.extend_fan_is_limit CategoryTheory.extendFanIsLimitₓ'. -/
/-- Show that if the two given fans in `extend_fan` are limits, then the constructed fan is also a
limit.
-/
def extendFanIsLimit {n : ℕ} (f : Fin (n + 1) → C) {c₁ : Fan fun i : Fin n => f i.succ}
    {c₂ : BinaryFan (f 0) c₁.pt} (t₁ : IsLimit c₁) (t₂ : IsLimit c₂) : IsLimit (extendFan c₁ c₂)
    where
  lift s := by
    apply (binary_fan.is_limit.lift' t₂ (s.π.app ⟨0⟩) _).1
    apply t₁.lift ⟨_, discrete.nat_trans fun ⟨i⟩ => s.π.app ⟨i.succ⟩⟩
  fac := fun s ⟨j⟩ => by
    apply Fin.inductionOn j
    · apply (binary_fan.is_limit.lift' t₂ _ _).2.1
    · rintro i -
      dsimp only [extend_fan_π_app]
      rw [Fin.cases_succ, ← assoc, (binary_fan.is_limit.lift' t₂ _ _).2.2, t₁.fac]
      rfl
  uniq s m w := by
    apply binary_fan.is_limit.hom_ext t₂
    · rw [(binary_fan.is_limit.lift' t₂ _ _).2.1]
      apply w ⟨0⟩
    · rw [(binary_fan.is_limit.lift' t₂ _ _).2.2]
      apply t₁.uniq ⟨_, _⟩
      rintro ⟨j⟩
      rw [assoc]
      dsimp only [discrete.nat_trans_app, extend_fan_is_limit._match_1]
      rw [← w ⟨j.succ⟩]
      dsimp only [extend_fan_π_app]
      rw [Fin.cases_succ]
#align category_theory.extend_fan_is_limit CategoryTheory.extendFanIsLimit

section

variable [HasBinaryProducts C] [HasTerminal C]

/-- If `C` has a terminal object and binary products, then it has a product for objects indexed by
`fin n`.
This is a helper lemma for `has_finite_products_of_has_binary_and_terminal`, which is more general
than this.
-/
private theorem has_product_fin : ∀ (n : ℕ) (f : Fin n → C), HasProduct f
  | 0 => fun f =>
    by
    letI : has_limits_of_shape (discrete (Fin 0)) C :=
      has_limits_of_shape_of_equivalence (Discrete.equivalence.{0} fin_zero_equiv'.symm)
    infer_instance
  | n + 1 => fun f => by
    haveI := has_product_fin n
    apply has_limit.mk ⟨_, extend_fan_is_limit f (limit.is_limit _) (limit.is_limit _)⟩
#align category_theory.has_product_fin category_theory.has_product_fin

#print CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal /-
/-- If `C` has a terminal object and binary products, then it has finite products. -/
theorem hasFiniteProducts_of_has_binary_and_terminal : HasFiniteProducts C :=
  by
  refine' ⟨fun n => ⟨fun K => _⟩⟩
  letI := has_product_fin n fun n => K.obj ⟨n⟩
  let this : (discrete.functor fun n => K.obj ⟨n⟩) ≅ K := discrete.nat_iso fun ⟨i⟩ => iso.refl _
  apply has_limit_of_iso this
#align category_theory.has_finite_products_of_has_binary_and_terminal CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal
-/

end

section Preserves

variable (F : C ⥤ D)

variable [PreservesLimitsOfShape (Discrete WalkingPair) F]

variable [PreservesLimitsOfShape (Discrete.{0} PEmpty) F]

variable [HasFiniteProducts.{v} C]

/- warning: category_theory.preserves_fin_of_preserves_binary_and_terminal -> CategoryTheory.preservesFinOfPreservesBinaryAndTerminalₓ is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_2 D _inst_3) [_inst_4 : CategoryTheory.Limits.PreservesLimitsOfShape.{0, 0, u1, u2, u3, u4} C _inst_2 D _inst_3 (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) F] [_inst_5 : CategoryTheory.Limits.PreservesLimitsOfShape.{0, 0, u1, u2, u3, u4} C _inst_2 D _inst_3 (CategoryTheory.Discrete.{0} PEmpty.{1}) (CategoryTheory.discreteCategory.{0} PEmpty.{1}) F] [_inst_6 : CategoryTheory.Limits.HasFiniteProducts.{u1, u3} C _inst_2] (n : Nat) (f : (Fin n) -> C), CategoryTheory.Limits.PreservesLimit.{0, 0, u1, u2, u3, u4} C _inst_2 D _inst_3 (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) (CategoryTheory.Discrete.functor.{u1, 0, u3} C _inst_2 (Fin n) f) F
but is expected to have type
  forall {C : Type.{u1}} [_inst_2 : CategoryTheory.Category.{u3, u1} C] {D : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u4, u2} D] (F : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_2 D _inst_3) [_inst_4 : CategoryTheory.Limits.PreservesLimitsOfShape.{0, 0, u3, u4, u1, u2} C _inst_2 D _inst_3 (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) F] [_inst_5 : CategoryTheory.Limits.PreservesLimitsOfShape.{0, 0, u3, u4, u1, u2} C _inst_2 D _inst_3 (CategoryTheory.Discrete.{0} PEmpty.{1}) (CategoryTheory.discreteCategory.{0} PEmpty.{1}) F] [_inst_6 : CategoryTheory.Limits.HasFiniteProducts.{u3, u1} C _inst_2] (n : Nat) (f : (Fin n) -> C), CategoryTheory.Limits.PreservesLimit.{0, 0, u3, u4, u1, u2} C _inst_2 D _inst_3 (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) (CategoryTheory.Discrete.functor.{u3, 0, u1} C _inst_2 (Fin n) f) F
Case conversion may be inaccurate. Consider using '#align category_theory.preserves_fin_of_preserves_binary_and_terminal CategoryTheory.preservesFinOfPreservesBinaryAndTerminalₓₓ'. -/
/-- If `F` preserves the terminal object and binary products, then it preserves products indexed by
`fin n` for any `n`.
-/
noncomputable def preservesFinOfPreservesBinaryAndTerminal :
    ∀ (n : ℕ) (f : Fin n → C), PreservesLimit (Discrete.functor f) F
  | 0 => fun f =>
    by
    letI : preserves_limits_of_shape (discrete (Fin 0)) F :=
      preservesLimitsOfShapeOfEquiv.{0, 0} (discrete.equivalence fin_zero_equiv'.symm) _
    infer_instance
  | n + 1 => by
    haveI := preserves_fin_of_preserves_binary_and_terminal n
    intro f
    refine'
      preserves_limit_of_preserves_limit_cone
        (extend_fan_is_limit f (limit.is_limit _) (limit.is_limit _)) _
    apply (is_limit_map_cone_fan_mk_equiv _ _ _).symm _
    let this :=
      extend_fan_is_limit (fun i => F.obj (f i)) (is_limit_of_has_product_of_preserves_limit F _)
        (is_limit_of_has_binary_product_of_preserves_limit F _ _)
    refine' is_limit.of_iso_limit this _
    apply cones.ext _ _
    apply iso.refl _
    rintro ⟨j⟩
    apply Fin.inductionOn j
    · apply (category.id_comp _).symm
    · rintro i -
      dsimp only [extend_fan_π_app, iso.refl_hom, fan.mk_π_app]
      rw [Fin.cases_succ, Fin.cases_succ]
      change F.map _ ≫ _ = 𝟙 _ ≫ _
      rw [id_comp, ← F.map_comp]
      rfl
#align category_theory.preserves_fin_of_preserves_binary_and_terminal CategoryTheory.preservesFinOfPreservesBinaryAndTerminalₓ

#print CategoryTheory.preservesShapeFinOfPreservesBinaryAndTerminal /-
/-- If `F` preserves the terminal object and binary products, then it preserves limits of shape
`discrete (fin n)`.
-/
def preservesShapeFinOfPreservesBinaryAndTerminal (n : ℕ) :
    PreservesLimitsOfShape (Discrete (Fin n)) F
    where PreservesLimit K :=
    by
    let this : (discrete.functor fun n => K.obj ⟨n⟩) ≅ K := discrete.nat_iso fun ⟨i⟩ => iso.refl _
    haveI := preserves_fin_of_preserves_binary_and_terminal F n fun n => K.obj ⟨n⟩
    apply preserves_limit_of_iso_diagram F this
#align category_theory.preserves_shape_fin_of_preserves_binary_and_terminal CategoryTheory.preservesShapeFinOfPreservesBinaryAndTerminal
-/

#print CategoryTheory.preservesFiniteProductsOfPreservesBinaryAndTerminal /-
/-- If `F` preserves the terminal object and binary products then it preserves finite products. -/
def preservesFiniteProductsOfPreservesBinaryAndTerminal (J : Type) [Fintype J] :
    PreservesLimitsOfShape (Discrete J) F := by
  classical
    let e := Fintype.equivFin J
    haveI := preserves_shape_fin_of_preserves_binary_and_terminal F (Fintype.card J)
    apply preservesLimitsOfShapeOfEquiv.{0, 0} (discrete.equivalence e).symm
#align category_theory.preserves_finite_products_of_preserves_binary_and_terminal CategoryTheory.preservesFiniteProductsOfPreservesBinaryAndTerminal
-/

end Preserves

/- warning: category_theory.extend_cofan -> CategoryTheory.extendCofan is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} C] {n : Nat} {f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> C} (c₁ : CategoryTheory.Limits.Cofan.{0, u1, u2} (Fin n) C _inst_2 (fun (i : Fin n) => f (Fin.succ n i))), (CategoryTheory.Limits.BinaryCofan.{u1, u2} C _inst_2 (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin n) (fun (i : Fin n) => f (Fin.succ n i))) c₁)) -> (CategoryTheory.Limits.Cofan.{0, u1, u2} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) C _inst_2 f)
but is expected to have type
  forall {C : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} C] {n : Nat} {f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> C} (c₁ : CategoryTheory.Limits.Cofan.{0, u1, u2} (Fin n) C _inst_2 (fun (i : Fin n) => f (Fin.succ n i))), (CategoryTheory.Limits.BinaryCofan.{u1, u2} C _inst_2 (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin n) (fun (i : Fin n) => f (Fin.succ n i))) c₁)) -> (CategoryTheory.Limits.Cofan.{0, u1, u2} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) C _inst_2 f)
Case conversion may be inaccurate. Consider using '#align category_theory.extend_cofan CategoryTheory.extendCofanₓ'. -/
/-- Given `n+1` objects of `C`, a cofan for the last `n` with point `c₁.X`
and a binary cofan on `c₁.X` and `f 0`, we can build a cofan for all `n+1`.

In `extend_cofan_is_colimit` we show that if the two given cofans are colimits,
then this cofan is also a colimit.
-/
@[simps (config := { rhsMd := semireducible })]
def extendCofan {n : ℕ} {f : Fin (n + 1) → C} (c₁ : Cofan fun i : Fin n => f i.succ)
    (c₂ : BinaryCofan (f 0) c₁.pt) : Cofan f :=
  Cofan.mk c₂.pt
    (by
      refine' Fin.cases _ _
      · apply c₂.inl
      · intro i
        apply c₁.ι.app ⟨i⟩ ≫ c₂.inr)
#align category_theory.extend_cofan CategoryTheory.extendCofan

/- warning: category_theory.extend_cofan_is_colimit -> CategoryTheory.extendCofanIsColimit is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} C] {n : Nat} (f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> C) {c₁ : CategoryTheory.Limits.Cofan.{0, u1, u2} (Fin n) C _inst_2 (fun (i : Fin n) => f (Fin.succ n i))} {c₂ : CategoryTheory.Limits.BinaryCofan.{u1, u2} C _inst_2 (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin n) (fun (i : Fin n) => f (Fin.succ n i))) c₁)}, (CategoryTheory.Limits.IsColimit.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin n) (fun (i : Fin n) => f (Fin.succ n i))) c₁) -> (CategoryTheory.Limits.IsColimit.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_2 (CategoryTheory.Limits.pair.{u1, u2} C _inst_2 (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin n) (fun (i : Fin n) => f (Fin.succ n i))) c₁)) c₂) -> (CategoryTheory.Limits.IsColimit.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (CategoryTheory.discreteCategory.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) f) (CategoryTheory.extendCofan.{u1, u2} C _inst_2 n f c₁ c₂))
but is expected to have type
  forall {C : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} C] {n : Nat} (f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> C) {c₁ : CategoryTheory.Limits.Cofan.{0, u1, u2} (Fin n) C _inst_2 (fun (i : Fin n) => f (Fin.succ n i))} {c₂ : CategoryTheory.Limits.BinaryCofan.{u1, u2} C _inst_2 (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin n) (fun (i : Fin n) => f (Fin.succ n i))) c₁)}, (CategoryTheory.Limits.IsColimit.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin n) (fun (i : Fin n) => f (Fin.succ n i))) c₁) -> (CategoryTheory.Limits.IsColimit.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) C _inst_2 (CategoryTheory.Limits.pair.{u1, u2} C _inst_2 (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (CategoryTheory.Limits.Cocone.pt.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin n) (fun (i : Fin n) => f (Fin.succ n i))) c₁)) c₂) -> (CategoryTheory.Limits.IsColimit.{0, u1, 0, u2} (CategoryTheory.Discrete.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (CategoryTheory.discreteCategory.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) C _inst_2 (CategoryTheory.Discrete.functor.{u1, 0, u2} C _inst_2 (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) f) (CategoryTheory.extendCofan.{u1, u2} C _inst_2 n f c₁ c₂))
Case conversion may be inaccurate. Consider using '#align category_theory.extend_cofan_is_colimit CategoryTheory.extendCofanIsColimitₓ'. -/
/-- Show that if the two given cofans in `extend_cofan` are colimits,
then the constructed cofan is also a colimit.
-/
def extendCofanIsColimit {n : ℕ} (f : Fin (n + 1) → C) {c₁ : Cofan fun i : Fin n => f i.succ}
    {c₂ : BinaryCofan (f 0) c₁.pt} (t₁ : IsColimit c₁) (t₂ : IsColimit c₂) :
    IsColimit (extendCofan c₁ c₂)
    where
  desc s := by
    apply (binary_cofan.is_colimit.desc' t₂ (s.ι.app ⟨0⟩) _).1
    apply t₁.desc ⟨_, discrete.nat_trans fun i => s.ι.app ⟨i.as.succ⟩⟩
  fac s := by
    rintro ⟨j⟩
    apply Fin.inductionOn j
    · apply (binary_cofan.is_colimit.desc' t₂ _ _).2.1
    · rintro i -
      dsimp only [extend_cofan_ι_app]
      rw [Fin.cases_succ, assoc, (binary_cofan.is_colimit.desc' t₂ _ _).2.2, t₁.fac]
      rfl
  uniq s m w := by
    apply binary_cofan.is_colimit.hom_ext t₂
    · rw [(binary_cofan.is_colimit.desc' t₂ _ _).2.1]
      apply w ⟨0⟩
    · rw [(binary_cofan.is_colimit.desc' t₂ _ _).2.2]
      apply t₁.uniq ⟨_, _⟩
      rintro ⟨j⟩
      dsimp only [discrete.nat_trans_app]
      rw [← w ⟨j.succ⟩]
      dsimp only [extend_cofan_ι_app]
      rw [Fin.cases_succ, assoc]
#align category_theory.extend_cofan_is_colimit CategoryTheory.extendCofanIsColimit

section

variable [HasBinaryCoproducts C] [HasInitial C]

/--
If `C` has an initial object and binary coproducts, then it has a coproduct for objects indexed by
`fin n`.
This is a helper lemma for `has_cofinite_products_of_has_binary_and_terminal`, which is more general
than this.
-/
private theorem has_coproduct_fin : ∀ (n : ℕ) (f : Fin n → C), HasCoproduct f
  | 0 => fun f =>
    by
    letI : has_colimits_of_shape (discrete (Fin 0)) C :=
      has_colimits_of_shape_of_equivalence (Discrete.equivalence.{0} fin_zero_equiv'.symm)
    infer_instance
  | n + 1 => fun f => by
    haveI := has_coproduct_fin n
    apply
      has_colimit.mk ⟨_, extend_cofan_is_colimit f (colimit.is_colimit _) (colimit.is_colimit _)⟩
#align category_theory.has_coproduct_fin category_theory.has_coproduct_fin

#print CategoryTheory.hasFiniteCoproducts_of_has_binary_and_initial /-
/-- If `C` has an initial object and binary coproducts, then it has finite coproducts. -/
theorem hasFiniteCoproducts_of_has_binary_and_initial : HasFiniteCoproducts C :=
  by
  refine' ⟨fun n => ⟨fun K => _⟩⟩
  letI := has_coproduct_fin n fun n => K.obj ⟨n⟩
  let this : K ≅ discrete.functor fun n => K.obj ⟨n⟩ := discrete.nat_iso fun ⟨i⟩ => iso.refl _
  apply has_colimit_of_iso this
#align category_theory.has_finite_coproducts_of_has_binary_and_initial CategoryTheory.hasFiniteCoproducts_of_has_binary_and_initial
-/

end

section Preserves

variable (F : C ⥤ D)

variable [PreservesColimitsOfShape (Discrete WalkingPair) F]

variable [PreservesColimitsOfShape (Discrete.{0} PEmpty) F]

variable [HasFiniteCoproducts.{v} C]

/- warning: category_theory.preserves_fin_of_preserves_binary_and_initial -> CategoryTheory.preservesFinOfPreservesBinaryAndInitialₓ is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] (F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_2 D _inst_3) [_inst_4 : CategoryTheory.Limits.PreservesColimitsOfShape.{0, 0, u1, u2, u3, u4} C _inst_2 D _inst_3 (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) F] [_inst_5 : CategoryTheory.Limits.PreservesColimitsOfShape.{0, 0, u1, u2, u3, u4} C _inst_2 D _inst_3 (CategoryTheory.Discrete.{0} PEmpty.{1}) (CategoryTheory.discreteCategory.{0} PEmpty.{1}) F] [_inst_6 : CategoryTheory.Limits.HasFiniteCoproducts.{u1, u3} C _inst_2] (n : Nat) (f : (Fin n) -> C), CategoryTheory.Limits.PreservesColimit.{0, 0, u1, u2, u3, u4} C _inst_2 D _inst_3 (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) (CategoryTheory.Discrete.functor.{u1, 0, u3} C _inst_2 (Fin n) f) F
but is expected to have type
  forall {C : Type.{u1}} [_inst_2 : CategoryTheory.Category.{u3, u1} C] {D : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u4, u2} D] (F : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_2 D _inst_3) [_inst_4 : CategoryTheory.Limits.PreservesColimitsOfShape.{0, 0, u3, u4, u1, u2} C _inst_2 D _inst_3 (CategoryTheory.Discrete.{0} CategoryTheory.Limits.WalkingPair) (CategoryTheory.discreteCategory.{0} CategoryTheory.Limits.WalkingPair) F] [_inst_5 : CategoryTheory.Limits.PreservesColimitsOfShape.{0, 0, u3, u4, u1, u2} C _inst_2 D _inst_3 (CategoryTheory.Discrete.{0} PEmpty.{1}) (CategoryTheory.discreteCategory.{0} PEmpty.{1}) F] [_inst_6 : CategoryTheory.Limits.HasFiniteCoproducts.{u3, u1} C _inst_2] (n : Nat) (f : (Fin n) -> C), CategoryTheory.Limits.PreservesColimit.{0, 0, u3, u4, u1, u2} C _inst_2 D _inst_3 (CategoryTheory.Discrete.{0} (Fin n)) (CategoryTheory.discreteCategory.{0} (Fin n)) (CategoryTheory.Discrete.functor.{u3, 0, u1} C _inst_2 (Fin n) f) F
Case conversion may be inaccurate. Consider using '#align category_theory.preserves_fin_of_preserves_binary_and_initial CategoryTheory.preservesFinOfPreservesBinaryAndInitialₓₓ'. -/
/-- If `F` preserves the initial object and binary coproducts, then it preserves products indexed by
`fin n` for any `n`.
-/
noncomputable def preservesFinOfPreservesBinaryAndInitial :
    ∀ (n : ℕ) (f : Fin n → C), PreservesColimit (Discrete.functor f) F
  | 0 => fun f =>
    by
    letI : preserves_colimits_of_shape (discrete (Fin 0)) F :=
      preservesColimitsOfShapeOfEquiv.{0, 0} (discrete.equivalence fin_zero_equiv'.symm) _
    infer_instance
  | n + 1 => by
    haveI := preserves_fin_of_preserves_binary_and_initial n
    intro f
    refine'
      preserves_colimit_of_preserves_colimit_cocone
        (extend_cofan_is_colimit f (colimit.is_colimit _) (colimit.is_colimit _)) _
    apply (is_colimit_map_cocone_cofan_mk_equiv _ _ _).symm _
    let this :=
      extend_cofan_is_colimit (fun i => F.obj (f i))
        (is_colimit_of_has_coproduct_of_preserves_colimit F _)
        (is_colimit_of_has_binary_coproduct_of_preserves_colimit F _ _)
    refine' is_colimit.of_iso_colimit this _
    apply cocones.ext _ _
    apply iso.refl _
    rintro ⟨j⟩
    apply Fin.inductionOn j
    · apply category.comp_id
    · rintro i -
      dsimp only [extend_cofan_ι_app, iso.refl_hom, cofan.mk_ι_app]
      rw [Fin.cases_succ, Fin.cases_succ]
      erw [comp_id, ← F.map_comp]
      rfl
#align category_theory.preserves_fin_of_preserves_binary_and_initial CategoryTheory.preservesFinOfPreservesBinaryAndInitialₓ

#print CategoryTheory.preservesShapeFinOfPreservesBinaryAndInitial /-
/-- If `F` preserves the initial object and binary coproducts, then it preserves colimits of shape
`discrete (fin n)`.
-/
def preservesShapeFinOfPreservesBinaryAndInitial (n : ℕ) :
    PreservesColimitsOfShape (Discrete (Fin n)) F
    where PreservesColimit K :=
    by
    let this : (discrete.functor fun n => K.obj ⟨n⟩) ≅ K := discrete.nat_iso fun ⟨i⟩ => iso.refl _
    haveI := preserves_fin_of_preserves_binary_and_initial F n fun n => K.obj ⟨n⟩
    apply preserves_colimit_of_iso_diagram F this
#align category_theory.preserves_shape_fin_of_preserves_binary_and_initial CategoryTheory.preservesShapeFinOfPreservesBinaryAndInitial
-/

#print CategoryTheory.preservesFiniteCoproductsOfPreservesBinaryAndInitial /-
/-- If `F` preserves the initial object and binary coproducts then it preserves finite products. -/
def preservesFiniteCoproductsOfPreservesBinaryAndInitial (J : Type) [Fintype J] :
    PreservesColimitsOfShape (Discrete J) F := by
  classical
    let e := Fintype.equivFin J
    haveI := preserves_shape_fin_of_preserves_binary_and_initial F (Fintype.card J)
    apply preservesColimitsOfShapeOfEquiv.{0, 0} (discrete.equivalence e).symm
#align category_theory.preserves_finite_coproducts_of_preserves_binary_and_initial CategoryTheory.preservesFiniteCoproductsOfPreservesBinaryAndInitial
-/

end Preserves

end CategoryTheory

