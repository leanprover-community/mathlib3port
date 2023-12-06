/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Data.Fintype.Order
import Data.Set.Finite
import Order.Category.FinPartOrd
import Order.Category.LinOrd
import CategoryTheory.Limits.Shapes.Images
import CategoryTheory.Limits.Shapes.RegularMono

#align_import order.category.NonemptyFinLinOrd from "leanprover-community/mathlib"@"fa4a805d16a9cd9c96e0f8edeb57dc5a07af1a19"

/-!
# Nonempty finite linear orders

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `NonemptyFinLinOrd`, the category of nonempty finite linear orders with monotone maps.
This is the index category for simplicial objects.

Note: `NonemptyFinLinOrd` is *not* a subcategory of `FinBddDistLat` because its morphisms do not
preserve `⊥` and `⊤`.
-/


universe u v

open CategoryTheory CategoryTheory.Limits

#print NonemptyFiniteLinearOrder /-
/-- A typeclass for nonempty finite linear orders. -/
class NonemptyFiniteLinearOrder (α : Type _) extends Fintype α, LinearOrder α where
  Nonempty : Nonempty α := by infer_instance
#align nonempty_fin_lin_ord NonemptyFiniteLinearOrder
-/

attribute [instance] NonemptyFiniteLinearOrder.nonempty

#print NonemptyFiniteLinearOrder.toBoundedOrder /-
instance (priority := 100) NonemptyFiniteLinearOrder.toBoundedOrder (α : Type _)
    [NonemptyFiniteLinearOrder α] : BoundedOrder α :=
  Fintype.toBoundedOrder α
#align nonempty_fin_lin_ord.to_bounded_order NonemptyFiniteLinearOrder.toBoundedOrder
-/

#print PUnit.nonemptyFiniteLinearOrder /-
instance PUnit.nonemptyFiniteLinearOrder : NonemptyFiniteLinearOrder PUnit where
#align punit.nonempty_fin_lin_ord PUnit.nonemptyFiniteLinearOrder
-/

#print Fin.nonemptyFiniteLinearOrder /-
instance Fin.nonemptyFiniteLinearOrder (n : ℕ) : NonemptyFiniteLinearOrder (Fin (n + 1)) where
#align fin.nonempty_fin_lin_ord Fin.nonemptyFiniteLinearOrder
-/

#print ULift.nonemptyFiniteLinearOrder /-
instance ULift.nonemptyFiniteLinearOrder (α : Type u) [NonemptyFiniteLinearOrder α] :
    NonemptyFiniteLinearOrder (ULift.{v} α) :=
  { LinearOrder.lift' Equiv.ulift (Equiv.injective _) with }
#align ulift.nonempty_fin_lin_ord ULift.nonemptyFiniteLinearOrder
-/

instance (α : Type _) [NonemptyFiniteLinearOrder α] : NonemptyFiniteLinearOrder αᵒᵈ :=
  { OrderDual.fintype α with }

#print NonemptyFinLinOrd /-
/-- The category of nonempty finite linear orders. -/
def NonemptyFinLinOrd :=
  Bundled NonemptyFiniteLinearOrder
#align NonemptyFinLinOrd NonemptyFinLinOrd
-/

namespace NonemptyFinLinOrd

instance : BundledHom.ParentProjection @NonemptyFiniteLinearOrder.toLinearOrder :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for NonemptyFinLinOrd

instance : CoeSort NonemptyFinLinOrd (Type _) :=
  Bundled.hasCoeToSort

#print NonemptyFinLinOrd.of /-
/-- Construct a bundled `NonemptyFinLinOrd` from the underlying type and typeclass. -/
def of (α : Type _) [NonemptyFiniteLinearOrder α] : NonemptyFinLinOrd :=
  Bundled.of α
#align NonemptyFinLinOrd.of NonemptyFinLinOrd.of
-/

#print NonemptyFinLinOrd.coe_of /-
@[simp]
theorem coe_of (α : Type _) [NonemptyFiniteLinearOrder α] : ↥(of α) = α :=
  rfl
#align NonemptyFinLinOrd.coe_of NonemptyFinLinOrd.coe_of
-/

instance : Inhabited NonemptyFinLinOrd :=
  ⟨of PUnit⟩

instance (α : NonemptyFinLinOrd) : NonemptyFiniteLinearOrder α :=
  α.str

#print NonemptyFinLinOrd.hasForgetToLinOrd /-
instance hasForgetToLinOrd : HasForget₂ NonemptyFinLinOrd LinOrd :=
  BundledHom.forget₂ _ _
#align NonemptyFinLinOrd.has_forget_to_LinOrd NonemptyFinLinOrd.hasForgetToLinOrd
-/

#print NonemptyFinLinOrd.hasForgetToFinPartOrd /-
instance hasForgetToFinPartOrd : HasForget₂ NonemptyFinLinOrd FinPartOrd
    where forget₂ :=
    { obj := fun X => FinPartOrd.of X
      map := fun X Y => id }
#align NonemptyFinLinOrd.has_forget_to_FinPartOrd NonemptyFinLinOrd.hasForgetToFinPartOrd
-/

#print NonemptyFinLinOrd.Iso.mk /-
/-- Constructs an equivalence between nonempty finite linear orders from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : NonemptyFinLinOrd.{u}} (e : α ≃o β) : α ≅ β
    where
  hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply x
  inv_hom_id' := by ext; exact e.apply_symm_apply x
#align NonemptyFinLinOrd.iso.mk NonemptyFinLinOrd.Iso.mk
-/

#print NonemptyFinLinOrd.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : NonemptyFinLinOrd ⥤ NonemptyFinLinOrd
    where
  obj X := of Xᵒᵈ
  map X Y := OrderHom.dual
#align NonemptyFinLinOrd.dual NonemptyFinLinOrd.dual
-/

#print NonemptyFinLinOrd.dualEquiv /-
/-- The equivalence between `NonemptyFinLinOrd` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : NonemptyFinLinOrd ≌ NonemptyFinLinOrd :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align NonemptyFinLinOrd.dual_equiv NonemptyFinLinOrd.dualEquiv
-/

#print NonemptyFinLinOrd.mono_iff_injective /-
theorem mono_iff_injective {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B) :
    Mono f ↔ Function.Injective f :=
  by
  refine' ⟨_, concrete_category.mono_of_injective f⟩
  intro
  intro a₁ a₂ h
  let X : NonemptyFinLinOrd.{u} := ⟨ULift (Fin 1)⟩
  let g₁ : X ⟶ A := ⟨fun x => a₁, fun x₁ x₂ h => by rfl⟩
  let g₂ : X ⟶ A := ⟨fun x => a₂, fun x₁ x₂ h => by rfl⟩
  change g₁ (ULift.up (0 : Fin 1)) = g₂ (ULift.up (0 : Fin 1))
  have eq : g₁ ≫ f = g₂ ≫ f := by ext x; exact h
  rw [cancel_mono] at eq 
  rw [Eq]
#align NonemptyFinLinOrd.mono_iff_injective NonemptyFinLinOrd.mono_iff_injective
-/

#print NonemptyFinLinOrd.epi_iff_surjective /-
theorem epi_iff_surjective {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B) :
    Epi f ↔ Function.Surjective f := by
  constructor
  · intro
    by_contra! hf'
    rcases hf' with ⟨m, hm⟩
    let Y : NonemptyFinLinOrd.{u} := ⟨ULift (Fin 2)⟩
    let p₁ : B ⟶ Y :=
      ⟨fun b => if b < m then ULift.up 0 else ULift.up 1, fun x₁ x₂ h =>
        by
        simp only
        split_ifs with h₁ h₂ h₂
        any_goals apply Fin.zero_le'
        · exfalso
          exact h₁ (lt_of_le_of_lt h h₂)
        · rfl⟩
    let p₂ : B ⟶ Y :=
      ⟨fun b => if b ≤ m then ULift.up 0 else ULift.up 1, fun x₁ x₂ h =>
        by
        simp only
        split_ifs with h₁ h₂ h₂
        any_goals apply Fin.zero_le'
        · exfalso
          exact h₁ (h.trans h₂)
        · rfl⟩
    have h : p₁ m = p₂ m := by
      congr
      rw [← cancel_epi f]
      ext a : 2
      simp only [comp_apply, OrderHom.coe_mk]
      split_ifs with h₁ h₂ h₂
      any_goals rfl
      · exfalso; exact h₂ (le_of_lt h₁)
      · exfalso; exact hm a (eq_of_le_of_not_lt h₂ h₁)
    simpa only [OrderHom.coe_mk, lt_self_iff_false, if_false, le_refl, if_true, ULift.up_inj,
      Fin.one_eq_zero_iff, Nat.succ_succ_ne_one] using h
  · intro h
    exact concrete_category.epi_of_surjective f h
#align NonemptyFinLinOrd.epi_iff_surjective NonemptyFinLinOrd.epi_iff_surjective
-/

instance : SplitEpiCategory NonemptyFinLinOrd.{u} :=
  ⟨fun X Y f hf =>
    by
    have H : ∀ y : Y, Nonempty (f ⁻¹' {y}) :=
      by
      rw [epi_iff_surjective] at hf 
      intro y
      exact Nonempty.intro ⟨(hf y).some, (hf y).choose_spec⟩
    let φ : Y → X := fun y => (H y).some.1
    have hφ : ∀ y : Y, f (φ y) = y := fun y => (H y).some.2
    refine' is_split_epi.mk' ⟨⟨φ, _⟩, _⟩; swap
    · ext b
      apply hφ
    · intro a b
      contrapose
      intro h
      simp only [not_le] at h ⊢
      suffices b ≤ a by
        apply lt_of_le_of_ne this
        intro h'
        exfalso
        simpa only [h', lt_self_iff_false] using h
      simpa only [hφ] using f.monotone (le_of_lt h)⟩

instance : HasStrongEpiMonoFactorisations NonemptyFinLinOrd.{u} :=
  ⟨fun X Y f => by
    let I : NonemptyFinLinOrd.{u} := ⟨Set.image (coeFn f) ⊤, ⟨⟩⟩
    let e : X ⟶ I := ⟨fun x => ⟨f x, ⟨x, by tidy⟩⟩, fun x₁ x₂ h => f.monotone h⟩
    let m : I ⟶ Y := ⟨fun y => y, by tidy⟩
    haveI : epi e := by rw [epi_iff_surjective]; tidy
    haveI : strong_epi e := strong_epi_of_epi e
    haveI : mono m := concrete_category.mono_of_injective _ (by tidy)
    exact
      Nonempty.intro
        { i
          m
          e }⟩

end NonemptyFinLinOrd

#print nonemptyFinLinOrd_dual_comp_forget_to_linOrd /-
theorem nonemptyFinLinOrd_dual_comp_forget_to_linOrd :
    NonemptyFinLinOrd.dual ⋙ forget₂ NonemptyFinLinOrd LinOrd =
      forget₂ NonemptyFinLinOrd LinOrd ⋙ LinOrd.dual :=
  rfl
#align NonemptyFinLinOrd_dual_comp_forget_to_LinOrd nonemptyFinLinOrd_dual_comp_forget_to_linOrd
-/

#print nonemptyFinLinOrdDualCompForgetToFinPartOrd /-
/-- The forgetful functor `NonemptyFinLinOrd ⥤ FinPartOrd` and `order_dual` commute. -/
def nonemptyFinLinOrdDualCompForgetToFinPartOrd :
    NonemptyFinLinOrd.dual ⋙ forget₂ NonemptyFinLinOrd FinPartOrd ≅
      forget₂ NonemptyFinLinOrd FinPartOrd ⋙ FinPartOrd.dual
    where
  hom := { app := fun X => OrderHom.id }
  inv := { app := fun X => OrderHom.id }
#align NonemptyFinLinOrd_dual_comp_forget_to_FinPartOrd nonemptyFinLinOrdDualCompForgetToFinPartOrd
-/

