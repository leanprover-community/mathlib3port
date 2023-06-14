/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.hom.lattice
! leanprover-community/mathlib commit 7581030920af3dcb241d1df0e36f6ec8289dd6be
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Hom.Bounded
import Mathbin.Order.SymmDiff

/-!
# Lattice homomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines (bounded) lattice homomorphisms.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `sup_hom`: Maps which preserve `⊔`.
* `inf_hom`: Maps which preserve `⊓`.
* `sup_bot_hom`: Finitary supremum homomorphisms. Maps which preserve `⊔` and `⊥`.
* `inf_top_hom`: Finitary infimum homomorphisms. Maps which preserve `⊓` and `⊤`.
* `lattice_hom`: Lattice homomorphisms. Maps which preserve `⊔` and `⊓`.
* `bounded_lattice_hom`: Bounded lattice homomorphisms. Maps which preserve `⊤`, `⊥`, `⊔` and `⊓`.

## Typeclasses

* `sup_hom_class`
* `inf_hom_class`
* `sup_bot_hom_class`
* `inf_top_hom_class`
* `lattice_hom_class`
* `bounded_lattice_hom_class`

## TODO

Do we need more intersections between `bot_hom`, `top_hom` and lattice homomorphisms?
-/


open Function OrderDual

variable {F ι α β γ δ : Type _}

#print SupHom /-
/-- The type of `⊔`-preserving functions from `α` to `β`. -/
structure SupHom (α β : Type _) [Sup α] [Sup β] where
  toFun : α → β
  map_sup' (a b : α) : to_fun (a ⊔ b) = to_fun a ⊔ to_fun b
#align sup_hom SupHom
-/

#print InfHom /-
/-- The type of `⊓`-preserving functions from `α` to `β`. -/
structure InfHom (α β : Type _) [Inf α] [Inf β] where
  toFun : α → β
  map_inf' (a b : α) : to_fun (a ⊓ b) = to_fun a ⊓ to_fun b
#align inf_hom InfHom
-/

#print SupBotHom /-
/-- The type of finitary supremum-preserving homomorphisms from `α` to `β`. -/
structure SupBotHom (α β : Type _) [Sup α] [Sup β] [Bot α] [Bot β] extends SupHom α β where
  map_bot' : to_fun ⊥ = ⊥
#align sup_bot_hom SupBotHom
-/

#print InfTopHom /-
/-- The type of finitary infimum-preserving homomorphisms from `α` to `β`. -/
structure InfTopHom (α β : Type _) [Inf α] [Inf β] [Top α] [Top β] extends InfHom α β where
  map_top' : to_fun ⊤ = ⊤
#align inf_top_hom InfTopHom
-/

#print LatticeHom /-
/-- The type of lattice homomorphisms from `α` to `β`. -/
structure LatticeHom (α β : Type _) [Lattice α] [Lattice β] extends SupHom α β where
  map_inf' (a b : α) : to_fun (a ⊓ b) = to_fun a ⊓ to_fun b
#align lattice_hom LatticeHom
-/

#print BoundedLatticeHom /-
/-- The type of bounded lattice homomorphisms from `α` to `β`. -/
structure BoundedLatticeHom (α β : Type _) [Lattice α] [Lattice β] [BoundedOrder α]
    [BoundedOrder β] extends LatticeHom α β where
  map_top' : to_fun ⊤ = ⊤
  map_bot' : to_fun ⊥ = ⊥
#align bounded_lattice_hom BoundedLatticeHom
-/

section

#print SupHomClass /-
/-- `sup_hom_class F α β` states that `F` is a type of `⊔`-preserving morphisms.

You should extend this class when you extend `sup_hom`. -/
class SupHomClass (F : Type _) (α β : outParam <| Type _) [Sup α] [Sup β] extends
    FunLike F α fun _ => β where
  map_sup (f : F) (a b : α) : f (a ⊔ b) = f a ⊔ f b
#align sup_hom_class SupHomClass
-/

#print InfHomClass /-
/-- `inf_hom_class F α β` states that `F` is a type of `⊓`-preserving morphisms.

You should extend this class when you extend `inf_hom`. -/
class InfHomClass (F : Type _) (α β : outParam <| Type _) [Inf α] [Inf β] extends
    FunLike F α fun _ => β where
  map_inf (f : F) (a b : α) : f (a ⊓ b) = f a ⊓ f b
#align inf_hom_class InfHomClass
-/

#print SupBotHomClass /-
/-- `sup_bot_hom_class F α β` states that `F` is a type of finitary supremum-preserving morphisms.

You should extend this class when you extend `sup_bot_hom`. -/
class SupBotHomClass (F : Type _) (α β : outParam <| Type _) [Sup α] [Sup β] [Bot α] [Bot β] extends
    SupHomClass F α β where
  map_bot (f : F) : f ⊥ = ⊥
#align sup_bot_hom_class SupBotHomClass
-/

#print InfTopHomClass /-
/-- `inf_top_hom_class F α β` states that `F` is a type of finitary infimum-preserving morphisms.

You should extend this class when you extend `sup_bot_hom`. -/
class InfTopHomClass (F : Type _) (α β : outParam <| Type _) [Inf α] [Inf β] [Top α] [Top β] extends
    InfHomClass F α β where
  map_top (f : F) : f ⊤ = ⊤
#align inf_top_hom_class InfTopHomClass
-/

#print LatticeHomClass /-
/-- `lattice_hom_class F α β` states that `F` is a type of lattice morphisms.

You should extend this class when you extend `lattice_hom`. -/
class LatticeHomClass (F : Type _) (α β : outParam <| Type _) [Lattice α] [Lattice β] extends
    SupHomClass F α β where
  map_inf (f : F) (a b : α) : f (a ⊓ b) = f a ⊓ f b
#align lattice_hom_class LatticeHomClass
-/

#print BoundedLatticeHomClass /-
/-- `bounded_lattice_hom_class F α β` states that `F` is a type of bounded lattice morphisms.

You should extend this class when you extend `bounded_lattice_hom`. -/
class BoundedLatticeHomClass (F : Type _) (α β : outParam <| Type _) [Lattice α] [Lattice β]
    [BoundedOrder α] [BoundedOrder β] extends LatticeHomClass F α β where
  map_top (f : F) : f ⊤ = ⊤
  map_bot (f : F) : f ⊥ = ⊥
#align bounded_lattice_hom_class BoundedLatticeHomClass
-/

end

export SupHomClass (map_sup)

export InfHomClass (map_inf)

attribute [simp] map_top map_bot map_sup map_inf

#print SupHomClass.toOrderHomClass /-
-- See note [lower instance priority]
instance (priority := 100) SupHomClass.toOrderHomClass [SemilatticeSup α] [SemilatticeSup β]
    [SupHomClass F α β] : OrderHomClass F α β :=
  { ‹SupHomClass F α β› with
    map_rel := fun f a b h => by rw [← sup_eq_right, ← map_sup, sup_eq_right.2 h] }
#align sup_hom_class.to_order_hom_class SupHomClass.toOrderHomClass
-/

#print InfHomClass.toOrderHomClass /-
-- See note [lower instance priority]
instance (priority := 100) InfHomClass.toOrderHomClass [SemilatticeInf α] [SemilatticeInf β]
    [InfHomClass F α β] : OrderHomClass F α β :=
  { ‹InfHomClass F α β› with
    map_rel := fun f a b h => by rw [← inf_eq_left, ← map_inf, inf_eq_left.2 h] }
#align inf_hom_class.to_order_hom_class InfHomClass.toOrderHomClass
-/

#print SupBotHomClass.toBotHomClass /-
-- See note [lower instance priority]
instance (priority := 100) SupBotHomClass.toBotHomClass [Sup α] [Sup β] [Bot α] [Bot β]
    [SupBotHomClass F α β] : BotHomClass F α β :=
  { ‹SupBotHomClass F α β› with }
#align sup_bot_hom_class.to_bot_hom_class SupBotHomClass.toBotHomClass
-/

#print InfTopHomClass.toTopHomClass /-
-- See note [lower instance priority]
instance (priority := 100) InfTopHomClass.toTopHomClass [Inf α] [Inf β] [Top α] [Top β]
    [InfTopHomClass F α β] : TopHomClass F α β :=
  { ‹InfTopHomClass F α β› with }
#align inf_top_hom_class.to_top_hom_class InfTopHomClass.toTopHomClass
-/

#print LatticeHomClass.toInfHomClass /-
-- See note [lower instance priority]
instance (priority := 100) LatticeHomClass.toInfHomClass [Lattice α] [Lattice β]
    [LatticeHomClass F α β] : InfHomClass F α β :=
  { ‹LatticeHomClass F α β› with }
#align lattice_hom_class.to_inf_hom_class LatticeHomClass.toInfHomClass
-/

#print BoundedLatticeHomClass.toSupBotHomClass /-
-- See note [lower instance priority]
instance (priority := 100) BoundedLatticeHomClass.toSupBotHomClass [Lattice α] [Lattice β]
    [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] : SupBotHomClass F α β :=
  { ‹BoundedLatticeHomClass F α β› with }
#align bounded_lattice_hom_class.to_sup_bot_hom_class BoundedLatticeHomClass.toSupBotHomClass
-/

#print BoundedLatticeHomClass.toInfTopHomClass /-
-- See note [lower instance priority]
instance (priority := 100) BoundedLatticeHomClass.toInfTopHomClass [Lattice α] [Lattice β]
    [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] : InfTopHomClass F α β :=
  { ‹BoundedLatticeHomClass F α β› with }
#align bounded_lattice_hom_class.to_inf_top_hom_class BoundedLatticeHomClass.toInfTopHomClass
-/

#print BoundedLatticeHomClass.toBoundedOrderHomClass /-
-- See note [lower instance priority]
instance (priority := 100) BoundedLatticeHomClass.toBoundedOrderHomClass [Lattice α] [Lattice β]
    [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] : BoundedOrderHomClass F α β :=
  { show OrderHomClass F α β from inferInstance, ‹BoundedLatticeHomClass F α β› with }
#align bounded_lattice_hom_class.to_bounded_order_hom_class BoundedLatticeHomClass.toBoundedOrderHomClass
-/

#print OrderIsoClass.toSupHomClass /-
-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toSupHomClass [SemilatticeSup α] [SemilatticeSup β]
    [OrderIsoClass F α β] : SupHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_sup := fun f a b =>
      eq_of_forall_ge_iff fun c => by simp only [← le_map_inv_iff, sup_le_iff] }
#align order_iso_class.to_sup_hom_class OrderIsoClass.toSupHomClass
-/

#print OrderIsoClass.toInfHomClass /-
-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toInfHomClass [SemilatticeInf α] [SemilatticeInf β]
    [OrderIsoClass F α β] : InfHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_inf := fun f a b =>
      eq_of_forall_le_iff fun c => by simp only [← map_inv_le_iff, le_inf_iff] }
#align order_iso_class.to_inf_hom_class OrderIsoClass.toInfHomClass
-/

#print OrderIsoClass.toSupBotHomClass /-
-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toSupBotHomClass [SemilatticeSup α] [OrderBot α]
    [SemilatticeSup β] [OrderBot β] [OrderIsoClass F α β] : SupBotHomClass F α β :=
  { OrderIsoClass.toSupHomClass, OrderIsoClass.toBotHomClass with }
#align order_iso_class.to_sup_bot_hom_class OrderIsoClass.toSupBotHomClass
-/

#print OrderIsoClass.toInfTopHomClass /-
-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toInfTopHomClass [SemilatticeInf α] [OrderTop α]
    [SemilatticeInf β] [OrderTop β] [OrderIsoClass F α β] : InfTopHomClass F α β :=
  { OrderIsoClass.toInfHomClass, OrderIsoClass.toTopHomClass with }
#align order_iso_class.to_inf_top_hom_class OrderIsoClass.toInfTopHomClass
-/

#print OrderIsoClass.toLatticeHomClass /-
-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toLatticeHomClass [Lattice α] [Lattice β]
    [OrderIsoClass F α β] : LatticeHomClass F α β :=
  { OrderIsoClass.toSupHomClass, OrderIsoClass.toInfHomClass with }
#align order_iso_class.to_lattice_hom_class OrderIsoClass.toLatticeHomClass
-/

#print OrderIsoClass.toBoundedLatticeHomClass /-
-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toBoundedLatticeHomClass [Lattice α] [Lattice β]
    [BoundedOrder α] [BoundedOrder β] [OrderIsoClass F α β] : BoundedLatticeHomClass F α β :=
  { OrderIsoClass.toLatticeHomClass, OrderIsoClass.toBoundedOrderHomClass with }
#align order_iso_class.to_bounded_lattice_hom_class OrderIsoClass.toBoundedLatticeHomClass
-/

section BoundedLattice

variable [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β] [BoundedLatticeHomClass F α β]
  (f : F) {a b : α}

#print Disjoint.map /-
theorem Disjoint.map (h : Disjoint a b) : Disjoint (f a) (f b) := by
  rw [disjoint_iff, ← map_inf, h.eq_bot, map_bot]
#align disjoint.map Disjoint.map
-/

#print Codisjoint.map /-
theorem Codisjoint.map (h : Codisjoint a b) : Codisjoint (f a) (f b) := by
  rw [codisjoint_iff, ← map_sup, h.eq_top, map_top]
#align codisjoint.map Codisjoint.map
-/

#print IsCompl.map /-
theorem IsCompl.map (h : IsCompl a b) : IsCompl (f a) (f b) :=
  ⟨h.1.map _, h.2.map _⟩
#align is_compl.map IsCompl.map
-/

end BoundedLattice

section BooleanAlgebra

variable [BooleanAlgebra α] [BooleanAlgebra β] [BoundedLatticeHomClass F α β] (f : F)

#print map_compl' /-
/-- Special case of `map_compl` for boolean algebras. -/
theorem map_compl' (a : α) : f (aᶜ) = f aᶜ :=
  (isCompl_compl.map _).compl_eq.symm
#align map_compl' map_compl'
-/

#print map_sdiff' /-
/-- Special case of `map_sdiff` for boolean algebras. -/
theorem map_sdiff' (a b : α) : f (a \ b) = f a \ f b := by
  rw [sdiff_eq, sdiff_eq, map_inf, map_compl']
#align map_sdiff' map_sdiff'
-/

#print map_symm_diff' /-
/-- Special case of `map_symm_diff` for boolean algebras. -/
theorem map_symm_diff' (a b : α) : f (a ∆ b) = f a ∆ f b := by
  rw [symmDiff, symmDiff, map_sup, map_sdiff', map_sdiff']
#align map_symm_diff' map_symm_diff'
-/

end BooleanAlgebra

instance [Sup α] [Sup β] [SupHomClass F α β] : CoeTC F (SupHom α β) :=
  ⟨fun f => ⟨f, map_sup f⟩⟩

instance [Inf α] [Inf β] [InfHomClass F α β] : CoeTC F (InfHom α β) :=
  ⟨fun f => ⟨f, map_inf f⟩⟩

instance [Sup α] [Sup β] [Bot α] [Bot β] [SupBotHomClass F α β] : CoeTC F (SupBotHom α β) :=
  ⟨fun f => ⟨f, map_bot f⟩⟩

instance [Inf α] [Inf β] [Top α] [Top β] [InfTopHomClass F α β] : CoeTC F (InfTopHom α β) :=
  ⟨fun f => ⟨f, map_top f⟩⟩

instance [Lattice α] [Lattice β] [LatticeHomClass F α β] : CoeTC F (LatticeHom α β) :=
  ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f }⟩

instance [Lattice α] [Lattice β] [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] :
    CoeTC F (BoundedLatticeHom α β) :=
  ⟨fun f =>
    { (f : LatticeHom α β) with
      toFun := f
      map_top' := map_top f
      map_bot' := map_bot f }⟩

/-! ### Supremum homomorphisms -/


namespace SupHom

variable [Sup α]

section Sup

variable [Sup β] [Sup γ] [Sup δ]

instance : SupHomClass (SupHom α β) α β
    where
  coe := SupHom.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_sup := SupHom.map_sup'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (SupHom α β) fun _ => α → β :=
  ⟨fun f => f.toFun⟩

#print SupHom.toFun_eq_coe /-
@[simp]
theorem toFun_eq_coe {f : SupHom α β} : f.toFun = (f : α → β) :=
  rfl
#align sup_hom.to_fun_eq_coe SupHom.toFun_eq_coe
-/

#print SupHom.ext /-
@[ext]
theorem ext {f g : SupHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align sup_hom.ext SupHom.ext
-/

#print SupHom.copy /-
/-- Copy of a `sup_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : SupHom α β) (f' : α → β) (h : f' = f) : SupHom α β
    where
  toFun := f'
  map_sup' := h.symm ▸ f.map_sup'
#align sup_hom.copy SupHom.copy
-/

#print SupHom.coe_copy /-
@[simp]
theorem coe_copy (f : SupHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align sup_hom.coe_copy SupHom.coe_copy
-/

#print SupHom.copy_eq /-
theorem copy_eq (f : SupHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align sup_hom.copy_eq SupHom.copy_eq
-/

variable (α)

#print SupHom.id /-
/-- `id` as a `sup_hom`. -/
protected def id : SupHom α α :=
  ⟨id, fun a b => rfl⟩
#align sup_hom.id SupHom.id
-/

instance : Inhabited (SupHom α α) :=
  ⟨SupHom.id α⟩

#print SupHom.coe_id /-
@[simp]
theorem coe_id : ⇑(SupHom.id α) = id :=
  rfl
#align sup_hom.coe_id SupHom.coe_id
-/

variable {α}

#print SupHom.id_apply /-
@[simp]
theorem id_apply (a : α) : SupHom.id α a = a :=
  rfl
#align sup_hom.id_apply SupHom.id_apply
-/

#print SupHom.comp /-
/-- Composition of `sup_hom`s as a `sup_hom`. -/
def comp (f : SupHom β γ) (g : SupHom α β) : SupHom α γ
    where
  toFun := f ∘ g
  map_sup' a b := by rw [comp_apply, map_sup, map_sup]
#align sup_hom.comp SupHom.comp
-/

#print SupHom.coe_comp /-
@[simp]
theorem coe_comp (f : SupHom β γ) (g : SupHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
#align sup_hom.coe_comp SupHom.coe_comp
-/

#print SupHom.comp_apply /-
@[simp]
theorem comp_apply (f : SupHom β γ) (g : SupHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align sup_hom.comp_apply SupHom.comp_apply
-/

#print SupHom.comp_assoc /-
@[simp]
theorem comp_assoc (f : SupHom γ δ) (g : SupHom β γ) (h : SupHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align sup_hom.comp_assoc SupHom.comp_assoc
-/

#print SupHom.comp_id /-
@[simp]
theorem comp_id (f : SupHom α β) : f.comp (SupHom.id α) = f :=
  SupHom.ext fun a => rfl
#align sup_hom.comp_id SupHom.comp_id
-/

#print SupHom.id_comp /-
@[simp]
theorem id_comp (f : SupHom α β) : (SupHom.id β).comp f = f :=
  SupHom.ext fun a => rfl
#align sup_hom.id_comp SupHom.id_comp
-/

#print SupHom.cancel_right /-
theorem cancel_right {g₁ g₂ : SupHom β γ} {f : SupHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => SupHom.ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align sup_hom.cancel_right SupHom.cancel_right
-/

#print SupHom.cancel_left /-
theorem cancel_left {g : SupHom β γ} {f₁ f₂ : SupHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => SupHom.ext fun a => hg <| by rw [← SupHom.comp_apply, h, SupHom.comp_apply],
    congr_arg _⟩
#align sup_hom.cancel_left SupHom.cancel_left
-/

end Sup

variable (α) [SemilatticeSup β]

#print SupHom.const /-
/-- The constant function as a `sup_hom`. -/
def const (b : β) : SupHom α β :=
  ⟨fun _ => b, fun _ _ => sup_idem.symm⟩
#align sup_hom.const SupHom.const
-/

#print SupHom.coe_const /-
@[simp]
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl
#align sup_hom.coe_const SupHom.coe_const
-/

#print SupHom.const_apply /-
@[simp]
theorem const_apply (b : β) (a : α) : const α b a = b :=
  rfl
#align sup_hom.const_apply SupHom.const_apply
-/

variable {α}

instance : Sup (SupHom α β) :=
  ⟨fun f g =>
    ⟨f ⊔ g, fun a b => by rw [Pi.sup_apply, map_sup, map_sup]; exact sup_sup_sup_comm _ _ _ _⟩⟩

instance : SemilatticeSup (SupHom α β) :=
  FunLike.coe_injective.SemilatticeSup _ fun f g => rfl

instance [Bot β] : Bot (SupHom α β) :=
  ⟨SupHom.const α ⊥⟩

instance [Top β] : Top (SupHom α β) :=
  ⟨SupHom.const α ⊤⟩

instance [OrderBot β] : OrderBot (SupHom α β) :=
  OrderBot.lift (coeFn : _ → α → β) (fun _ _ => id) rfl

instance [OrderTop β] : OrderTop (SupHom α β) :=
  OrderTop.lift (coeFn : _ → α → β) (fun _ _ => id) rfl

instance [BoundedOrder β] : BoundedOrder (SupHom α β) :=
  BoundedOrder.lift (coeFn : _ → α → β) (fun _ _ => id) rfl rfl

#print SupHom.coe_sup /-
@[simp]
theorem coe_sup (f g : SupHom α β) : ⇑(f ⊔ g) = f ⊔ g :=
  rfl
#align sup_hom.coe_sup SupHom.coe_sup
-/

#print SupHom.coe_bot /-
@[simp]
theorem coe_bot [Bot β] : ⇑(⊥ : SupHom α β) = ⊥ :=
  rfl
#align sup_hom.coe_bot SupHom.coe_bot
-/

#print SupHom.coe_top /-
@[simp]
theorem coe_top [Top β] : ⇑(⊤ : SupHom α β) = ⊤ :=
  rfl
#align sup_hom.coe_top SupHom.coe_top
-/

#print SupHom.sup_apply /-
@[simp]
theorem sup_apply (f g : SupHom α β) (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl
#align sup_hom.sup_apply SupHom.sup_apply
-/

#print SupHom.bot_apply /-
@[simp]
theorem bot_apply [Bot β] (a : α) : (⊥ : SupHom α β) a = ⊥ :=
  rfl
#align sup_hom.bot_apply SupHom.bot_apply
-/

#print SupHom.top_apply /-
@[simp]
theorem top_apply [Top β] (a : α) : (⊤ : SupHom α β) a = ⊤ :=
  rfl
#align sup_hom.top_apply SupHom.top_apply
-/

end SupHom

/-! ### Infimum homomorphisms -/


namespace InfHom

variable [Inf α]

section Inf

variable [Inf β] [Inf γ] [Inf δ]

instance : InfHomClass (InfHom α β) α β
    where
  coe := InfHom.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_inf := InfHom.map_inf'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (InfHom α β) fun _ => α → β :=
  ⟨fun f => f.toFun⟩

#print InfHom.toFun_eq_coe /-
@[simp]
theorem toFun_eq_coe {f : InfHom α β} : f.toFun = (f : α → β) :=
  rfl
#align inf_hom.to_fun_eq_coe InfHom.toFun_eq_coe
-/

#print InfHom.ext /-
@[ext]
theorem ext {f g : InfHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align inf_hom.ext InfHom.ext
-/

#print InfHom.copy /-
/-- Copy of an `inf_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : InfHom α β) (f' : α → β) (h : f' = f) : InfHom α β
    where
  toFun := f'
  map_inf' := h.symm ▸ f.map_inf'
#align inf_hom.copy InfHom.copy
-/

#print InfHom.coe_copy /-
@[simp]
theorem coe_copy (f : InfHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align inf_hom.coe_copy InfHom.coe_copy
-/

#print InfHom.copy_eq /-
theorem copy_eq (f : InfHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align inf_hom.copy_eq InfHom.copy_eq
-/

variable (α)

#print InfHom.id /-
/-- `id` as an `inf_hom`. -/
protected def id : InfHom α α :=
  ⟨id, fun a b => rfl⟩
#align inf_hom.id InfHom.id
-/

instance : Inhabited (InfHom α α) :=
  ⟨InfHom.id α⟩

#print InfHom.coe_id /-
@[simp]
theorem coe_id : ⇑(InfHom.id α) = id :=
  rfl
#align inf_hom.coe_id InfHom.coe_id
-/

variable {α}

#print InfHom.id_apply /-
@[simp]
theorem id_apply (a : α) : InfHom.id α a = a :=
  rfl
#align inf_hom.id_apply InfHom.id_apply
-/

#print InfHom.comp /-
/-- Composition of `inf_hom`s as an `inf_hom`. -/
def comp (f : InfHom β γ) (g : InfHom α β) : InfHom α γ
    where
  toFun := f ∘ g
  map_inf' a b := by rw [comp_apply, map_inf, map_inf]
#align inf_hom.comp InfHom.comp
-/

#print InfHom.coe_comp /-
@[simp]
theorem coe_comp (f : InfHom β γ) (g : InfHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
#align inf_hom.coe_comp InfHom.coe_comp
-/

#print InfHom.comp_apply /-
@[simp]
theorem comp_apply (f : InfHom β γ) (g : InfHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align inf_hom.comp_apply InfHom.comp_apply
-/

#print InfHom.comp_assoc /-
@[simp]
theorem comp_assoc (f : InfHom γ δ) (g : InfHom β γ) (h : InfHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align inf_hom.comp_assoc InfHom.comp_assoc
-/

#print InfHom.comp_id /-
@[simp]
theorem comp_id (f : InfHom α β) : f.comp (InfHom.id α) = f :=
  InfHom.ext fun a => rfl
#align inf_hom.comp_id InfHom.comp_id
-/

#print InfHom.id_comp /-
@[simp]
theorem id_comp (f : InfHom α β) : (InfHom.id β).comp f = f :=
  InfHom.ext fun a => rfl
#align inf_hom.id_comp InfHom.id_comp
-/

#print InfHom.cancel_right /-
theorem cancel_right {g₁ g₂ : InfHom β γ} {f : InfHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => InfHom.ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align inf_hom.cancel_right InfHom.cancel_right
-/

#print InfHom.cancel_left /-
theorem cancel_left {g : InfHom β γ} {f₁ f₂ : InfHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => InfHom.ext fun a => hg <| by rw [← InfHom.comp_apply, h, InfHom.comp_apply],
    congr_arg _⟩
#align inf_hom.cancel_left InfHom.cancel_left
-/

end Inf

variable (α) [SemilatticeInf β]

#print InfHom.const /-
/-- The constant function as an `inf_hom`. -/
def const (b : β) : InfHom α β :=
  ⟨fun _ => b, fun _ _ => inf_idem.symm⟩
#align inf_hom.const InfHom.const
-/

#print InfHom.coe_const /-
@[simp]
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl
#align inf_hom.coe_const InfHom.coe_const
-/

#print InfHom.const_apply /-
@[simp]
theorem const_apply (b : β) (a : α) : const α b a = b :=
  rfl
#align inf_hom.const_apply InfHom.const_apply
-/

variable {α}

instance : Inf (InfHom α β) :=
  ⟨fun f g =>
    ⟨f ⊓ g, fun a b => by rw [Pi.inf_apply, map_inf, map_inf]; exact inf_inf_inf_comm _ _ _ _⟩⟩

instance : SemilatticeInf (InfHom α β) :=
  FunLike.coe_injective.SemilatticeInf _ fun f g => rfl

instance [Bot β] : Bot (InfHom α β) :=
  ⟨InfHom.const α ⊥⟩

instance [Top β] : Top (InfHom α β) :=
  ⟨InfHom.const α ⊤⟩

instance [OrderBot β] : OrderBot (InfHom α β) :=
  OrderBot.lift (coeFn : _ → α → β) (fun _ _ => id) rfl

instance [OrderTop β] : OrderTop (InfHom α β) :=
  OrderTop.lift (coeFn : _ → α → β) (fun _ _ => id) rfl

instance [BoundedOrder β] : BoundedOrder (InfHom α β) :=
  BoundedOrder.lift (coeFn : _ → α → β) (fun _ _ => id) rfl rfl

#print InfHom.coe_inf /-
@[simp]
theorem coe_inf (f g : InfHom α β) : ⇑(f ⊓ g) = f ⊓ g :=
  rfl
#align inf_hom.coe_inf InfHom.coe_inf
-/

#print InfHom.coe_bot /-
@[simp]
theorem coe_bot [Bot β] : ⇑(⊥ : InfHom α β) = ⊥ :=
  rfl
#align inf_hom.coe_bot InfHom.coe_bot
-/

#print InfHom.coe_top /-
@[simp]
theorem coe_top [Top β] : ⇑(⊤ : InfHom α β) = ⊤ :=
  rfl
#align inf_hom.coe_top InfHom.coe_top
-/

#print InfHom.inf_apply /-
@[simp]
theorem inf_apply (f g : InfHom α β) (a : α) : (f ⊓ g) a = f a ⊓ g a :=
  rfl
#align inf_hom.inf_apply InfHom.inf_apply
-/

#print InfHom.bot_apply /-
@[simp]
theorem bot_apply [Bot β] (a : α) : (⊥ : InfHom α β) a = ⊥ :=
  rfl
#align inf_hom.bot_apply InfHom.bot_apply
-/

#print InfHom.top_apply /-
@[simp]
theorem top_apply [Top β] (a : α) : (⊤ : InfHom α β) a = ⊤ :=
  rfl
#align inf_hom.top_apply InfHom.top_apply
-/

end InfHom

/-! ### Finitary supremum homomorphisms -/


namespace SupBotHom

variable [Sup α] [Bot α]

section Sup

variable [Sup β] [Bot β] [Sup γ] [Bot γ] [Sup δ] [Bot δ]

#print SupBotHom.toBotHom /-
/-- Reinterpret a `sup_bot_hom` as a `bot_hom`. -/
def toBotHom (f : SupBotHom α β) : BotHom α β :=
  { f with }
#align sup_bot_hom.to_bot_hom SupBotHom.toBotHom
-/

instance : SupBotHomClass (SupBotHom α β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr
  map_sup f := f.map_sup'
  map_bot f := f.map_bot'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (SupBotHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

#print SupBotHom.toFun_eq_coe /-
@[simp]
theorem toFun_eq_coe {f : SupBotHom α β} : f.toFun = (f : α → β) :=
  rfl
#align sup_bot_hom.to_fun_eq_coe SupBotHom.toFun_eq_coe
-/

#print SupBotHom.ext /-
@[ext]
theorem ext {f g : SupBotHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align sup_bot_hom.ext SupBotHom.ext
-/

#print SupBotHom.copy /-
/-- Copy of a `sup_bot_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : SupBotHom α β) (f' : α → β) (h : f' = f) : SupBotHom α β :=
  { f.toBotHom.copy f' h with toSupHom := f.toSupHom.copy f' h }
#align sup_bot_hom.copy SupBotHom.copy
-/

#print SupBotHom.coe_copy /-
@[simp]
theorem coe_copy (f : SupBotHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align sup_bot_hom.coe_copy SupBotHom.coe_copy
-/

#print SupBotHom.copy_eq /-
theorem copy_eq (f : SupBotHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align sup_bot_hom.copy_eq SupBotHom.copy_eq
-/

variable (α)

#print SupBotHom.id /-
/-- `id` as a `sup_bot_hom`. -/
@[simps]
protected def id : SupBotHom α α :=
  ⟨SupHom.id α, rfl⟩
#align sup_bot_hom.id SupBotHom.id
-/

instance : Inhabited (SupBotHom α α) :=
  ⟨SupBotHom.id α⟩

#print SupBotHom.coe_id /-
@[simp]
theorem coe_id : ⇑(SupBotHom.id α) = id :=
  rfl
#align sup_bot_hom.coe_id SupBotHom.coe_id
-/

variable {α}

#print SupBotHom.id_apply /-
@[simp]
theorem id_apply (a : α) : SupBotHom.id α a = a :=
  rfl
#align sup_bot_hom.id_apply SupBotHom.id_apply
-/

#print SupBotHom.comp /-
/-- Composition of `sup_bot_hom`s as a `sup_bot_hom`. -/
def comp (f : SupBotHom β γ) (g : SupBotHom α β) : SupBotHom α γ :=
  { f.toSupHom.comp g.toSupHom, f.toBotHom.comp g.toBotHom with }
#align sup_bot_hom.comp SupBotHom.comp
-/

#print SupBotHom.coe_comp /-
@[simp]
theorem coe_comp (f : SupBotHom β γ) (g : SupBotHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
#align sup_bot_hom.coe_comp SupBotHom.coe_comp
-/

#print SupBotHom.comp_apply /-
@[simp]
theorem comp_apply (f : SupBotHom β γ) (g : SupBotHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align sup_bot_hom.comp_apply SupBotHom.comp_apply
-/

#print SupBotHom.comp_assoc /-
@[simp]
theorem comp_assoc (f : SupBotHom γ δ) (g : SupBotHom β γ) (h : SupBotHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align sup_bot_hom.comp_assoc SupBotHom.comp_assoc
-/

#print SupBotHom.comp_id /-
@[simp]
theorem comp_id (f : SupBotHom α β) : f.comp (SupBotHom.id α) = f :=
  ext fun a => rfl
#align sup_bot_hom.comp_id SupBotHom.comp_id
-/

#print SupBotHom.id_comp /-
@[simp]
theorem id_comp (f : SupBotHom α β) : (SupBotHom.id β).comp f = f :=
  ext fun a => rfl
#align sup_bot_hom.id_comp SupBotHom.id_comp
-/

#print SupBotHom.cancel_right /-
theorem cancel_right {g₁ g₂ : SupBotHom β γ} {f : SupBotHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align sup_bot_hom.cancel_right SupBotHom.cancel_right
-/

#print SupBotHom.cancel_left /-
theorem cancel_left {g : SupBotHom β γ} {f₁ f₂ : SupBotHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => SupBotHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align sup_bot_hom.cancel_left SupBotHom.cancel_left
-/

end Sup

variable [SemilatticeSup β] [OrderBot β]

instance : Sup (SupBotHom α β) :=
  ⟨fun f g => { f.toBotHom ⊔ g.toBotHom with toSupHom := f.toSupHom ⊔ g.toSupHom }⟩

instance : SemilatticeSup (SupBotHom α β) :=
  FunLike.coe_injective.SemilatticeSup _ fun f g => rfl

instance : OrderBot (SupBotHom α β) where
  bot := ⟨⊥, rfl⟩
  bot_le f := bot_le

#print SupBotHom.coe_sup /-
@[simp]
theorem coe_sup (f g : SupBotHom α β) : ⇑(f ⊔ g) = f ⊔ g :=
  rfl
#align sup_bot_hom.coe_sup SupBotHom.coe_sup
-/

#print SupBotHom.coe_bot /-
@[simp]
theorem coe_bot : ⇑(⊥ : SupBotHom α β) = ⊥ :=
  rfl
#align sup_bot_hom.coe_bot SupBotHom.coe_bot
-/

#print SupBotHom.sup_apply /-
@[simp]
theorem sup_apply (f g : SupBotHom α β) (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl
#align sup_bot_hom.sup_apply SupBotHom.sup_apply
-/

#print SupBotHom.bot_apply /-
@[simp]
theorem bot_apply (a : α) : (⊥ : SupBotHom α β) a = ⊥ :=
  rfl
#align sup_bot_hom.bot_apply SupBotHom.bot_apply
-/

end SupBotHom

/-! ### Finitary infimum homomorphisms -/


namespace InfTopHom

variable [Inf α] [Top α]

section Inf

variable [Inf β] [Top β] [Inf γ] [Top γ] [Inf δ] [Top δ]

#print InfTopHom.toTopHom /-
/-- Reinterpret an `inf_top_hom` as a `top_hom`. -/
def toTopHom (f : InfTopHom α β) : TopHom α β :=
  { f with }
#align inf_top_hom.to_top_hom InfTopHom.toTopHom
-/

instance : InfTopHomClass (InfTopHom α β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr
  map_inf f := f.map_inf'
  map_top f := f.map_top'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (InfTopHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

#print InfTopHom.toFun_eq_coe /-
@[simp]
theorem toFun_eq_coe {f : InfTopHom α β} : f.toFun = (f : α → β) :=
  rfl
#align inf_top_hom.to_fun_eq_coe InfTopHom.toFun_eq_coe
-/

#print InfTopHom.ext /-
@[ext]
theorem ext {f g : InfTopHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align inf_top_hom.ext InfTopHom.ext
-/

#print InfTopHom.copy /-
/-- Copy of an `inf_top_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : InfTopHom α β) (f' : α → β) (h : f' = f) : InfTopHom α β :=
  { f.toTopHom.copy f' h with toInfHom := f.toInfHom.copy f' h }
#align inf_top_hom.copy InfTopHom.copy
-/

#print InfTopHom.coe_copy /-
@[simp]
theorem coe_copy (f : InfTopHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align inf_top_hom.coe_copy InfTopHom.coe_copy
-/

#print InfTopHom.copy_eq /-
theorem copy_eq (f : InfTopHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align inf_top_hom.copy_eq InfTopHom.copy_eq
-/

variable (α)

#print InfTopHom.id /-
/-- `id` as an `inf_top_hom`. -/
@[simps]
protected def id : InfTopHom α α :=
  ⟨InfHom.id α, rfl⟩
#align inf_top_hom.id InfTopHom.id
-/

instance : Inhabited (InfTopHom α α) :=
  ⟨InfTopHom.id α⟩

#print InfTopHom.coe_id /-
@[simp]
theorem coe_id : ⇑(InfTopHom.id α) = id :=
  rfl
#align inf_top_hom.coe_id InfTopHom.coe_id
-/

variable {α}

#print InfTopHom.id_apply /-
@[simp]
theorem id_apply (a : α) : InfTopHom.id α a = a :=
  rfl
#align inf_top_hom.id_apply InfTopHom.id_apply
-/

#print InfTopHom.comp /-
/-- Composition of `inf_top_hom`s as an `inf_top_hom`. -/
def comp (f : InfTopHom β γ) (g : InfTopHom α β) : InfTopHom α γ :=
  { f.toInfHom.comp g.toInfHom, f.toTopHom.comp g.toTopHom with }
#align inf_top_hom.comp InfTopHom.comp
-/

#print InfTopHom.coe_comp /-
@[simp]
theorem coe_comp (f : InfTopHom β γ) (g : InfTopHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
#align inf_top_hom.coe_comp InfTopHom.coe_comp
-/

#print InfTopHom.comp_apply /-
@[simp]
theorem comp_apply (f : InfTopHom β γ) (g : InfTopHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align inf_top_hom.comp_apply InfTopHom.comp_apply
-/

#print InfTopHom.comp_assoc /-
@[simp]
theorem comp_assoc (f : InfTopHom γ δ) (g : InfTopHom β γ) (h : InfTopHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align inf_top_hom.comp_assoc InfTopHom.comp_assoc
-/

#print InfTopHom.comp_id /-
@[simp]
theorem comp_id (f : InfTopHom α β) : f.comp (InfTopHom.id α) = f :=
  ext fun a => rfl
#align inf_top_hom.comp_id InfTopHom.comp_id
-/

#print InfTopHom.id_comp /-
@[simp]
theorem id_comp (f : InfTopHom α β) : (InfTopHom.id β).comp f = f :=
  ext fun a => rfl
#align inf_top_hom.id_comp InfTopHom.id_comp
-/

#print InfTopHom.cancel_right /-
theorem cancel_right {g₁ g₂ : InfTopHom β γ} {f : InfTopHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align inf_top_hom.cancel_right InfTopHom.cancel_right
-/

#print InfTopHom.cancel_left /-
theorem cancel_left {g : InfTopHom β γ} {f₁ f₂ : InfTopHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => InfTopHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align inf_top_hom.cancel_left InfTopHom.cancel_left
-/

end Inf

variable [SemilatticeInf β] [OrderTop β]

instance : Inf (InfTopHom α β) :=
  ⟨fun f g => { f.toTopHom ⊓ g.toTopHom with toInfHom := f.toInfHom ⊓ g.toInfHom }⟩

instance : SemilatticeInf (InfTopHom α β) :=
  FunLike.coe_injective.SemilatticeInf _ fun f g => rfl

instance : OrderTop (InfTopHom α β) where
  top := ⟨⊤, rfl⟩
  le_top f := le_top

#print InfTopHom.coe_inf /-
@[simp]
theorem coe_inf (f g : InfTopHom α β) : ⇑(f ⊓ g) = f ⊓ g :=
  rfl
#align inf_top_hom.coe_inf InfTopHom.coe_inf
-/

#print InfTopHom.coe_top /-
@[simp]
theorem coe_top : ⇑(⊤ : InfTopHom α β) = ⊤ :=
  rfl
#align inf_top_hom.coe_top InfTopHom.coe_top
-/

#print InfTopHom.inf_apply /-
@[simp]
theorem inf_apply (f g : InfTopHom α β) (a : α) : (f ⊓ g) a = f a ⊓ g a :=
  rfl
#align inf_top_hom.inf_apply InfTopHom.inf_apply
-/

#print InfTopHom.top_apply /-
@[simp]
theorem top_apply (a : α) : (⊤ : InfTopHom α β) a = ⊤ :=
  rfl
#align inf_top_hom.top_apply InfTopHom.top_apply
-/

end InfTopHom

/-! ### Lattice homomorphisms -/


namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ] [Lattice δ]

#print LatticeHom.toInfHom /-
/-- Reinterpret a `lattice_hom` as an `inf_hom`. -/
def toInfHom (f : LatticeHom α β) : InfHom α β :=
  { f with }
#align lattice_hom.to_inf_hom LatticeHom.toInfHom
-/

instance : LatticeHomClass (LatticeHom α β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f <;> obtain ⟨⟨_, _⟩, _⟩ := g <;> congr
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (LatticeHom α β) fun _ => α → β :=
  ⟨fun f => f.toFun⟩

#print LatticeHom.toFun_eq_coe /-
@[simp]
theorem toFun_eq_coe {f : LatticeHom α β} : f.toFun = (f : α → β) :=
  rfl
#align lattice_hom.to_fun_eq_coe LatticeHom.toFun_eq_coe
-/

#print LatticeHom.ext /-
@[ext]
theorem ext {f g : LatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align lattice_hom.ext LatticeHom.ext
-/

#print LatticeHom.copy /-
/-- Copy of a `lattice_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : LatticeHom α β) (f' : α → β) (h : f' = f) : LatticeHom α β :=
  { f.toSupHom.copy f' h, f.toInfHom.copy f' h with }
#align lattice_hom.copy LatticeHom.copy
-/

#print LatticeHom.coe_copy /-
@[simp]
theorem coe_copy (f : LatticeHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align lattice_hom.coe_copy LatticeHom.coe_copy
-/

#print LatticeHom.copy_eq /-
theorem copy_eq (f : LatticeHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align lattice_hom.copy_eq LatticeHom.copy_eq
-/

variable (α)

#print LatticeHom.id /-
/-- `id` as a `lattice_hom`. -/
protected def id : LatticeHom α α where
  toFun := id
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
#align lattice_hom.id LatticeHom.id
-/

instance : Inhabited (LatticeHom α α) :=
  ⟨LatticeHom.id α⟩

#print LatticeHom.coe_id /-
@[simp]
theorem coe_id : ⇑(LatticeHom.id α) = id :=
  rfl
#align lattice_hom.coe_id LatticeHom.coe_id
-/

variable {α}

#print LatticeHom.id_apply /-
@[simp]
theorem id_apply (a : α) : LatticeHom.id α a = a :=
  rfl
#align lattice_hom.id_apply LatticeHom.id_apply
-/

#print LatticeHom.comp /-
/-- Composition of `lattice_hom`s as a `lattice_hom`. -/
def comp (f : LatticeHom β γ) (g : LatticeHom α β) : LatticeHom α γ :=
  { f.toSupHom.comp g.toSupHom, f.toInfHom.comp g.toInfHom with }
#align lattice_hom.comp LatticeHom.comp
-/

#print LatticeHom.coe_comp /-
@[simp]
theorem coe_comp (f : LatticeHom β γ) (g : LatticeHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl
#align lattice_hom.coe_comp LatticeHom.coe_comp
-/

#print LatticeHom.comp_apply /-
@[simp]
theorem comp_apply (f : LatticeHom β γ) (g : LatticeHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align lattice_hom.comp_apply LatticeHom.comp_apply
-/

#print LatticeHom.coe_comp_sup_hom /-
@[simp]
theorem coe_comp_sup_hom (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g : SupHom α γ) = (f : SupHom β γ).comp g :=
  rfl
#align lattice_hom.coe_comp_sup_hom LatticeHom.coe_comp_sup_hom
-/

#print LatticeHom.coe_comp_inf_hom /-
@[simp]
theorem coe_comp_inf_hom (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g : InfHom α γ) = (f : InfHom β γ).comp g :=
  rfl
#align lattice_hom.coe_comp_inf_hom LatticeHom.coe_comp_inf_hom
-/

#print LatticeHom.comp_assoc /-
@[simp]
theorem comp_assoc (f : LatticeHom γ δ) (g : LatticeHom β γ) (h : LatticeHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align lattice_hom.comp_assoc LatticeHom.comp_assoc
-/

#print LatticeHom.comp_id /-
@[simp]
theorem comp_id (f : LatticeHom α β) : f.comp (LatticeHom.id α) = f :=
  LatticeHom.ext fun a => rfl
#align lattice_hom.comp_id LatticeHom.comp_id
-/

#print LatticeHom.id_comp /-
@[simp]
theorem id_comp (f : LatticeHom α β) : (LatticeHom.id β).comp f = f :=
  LatticeHom.ext fun a => rfl
#align lattice_hom.id_comp LatticeHom.id_comp
-/

#print LatticeHom.cancel_right /-
theorem cancel_right {g₁ g₂ : LatticeHom β γ} {f : LatticeHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => LatticeHom.ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align lattice_hom.cancel_right LatticeHom.cancel_right
-/

#print LatticeHom.cancel_left /-
theorem cancel_left {g : LatticeHom β γ} {f₁ f₂ : LatticeHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => LatticeHom.ext fun a => hg <| by rw [← LatticeHom.comp_apply, h, LatticeHom.comp_apply],
    congr_arg _⟩
#align lattice_hom.cancel_left LatticeHom.cancel_left
-/

end LatticeHom

namespace OrderHomClass

variable (α β) [LinearOrder α] [Lattice β] [OrderHomClass F α β]

#print OrderHomClass.toLatticeHomClass /-
/-- An order homomorphism from a linear order is a lattice homomorphism. -/
@[reducible]
def toLatticeHomClass : LatticeHomClass F α β :=
  {
    ‹OrderHomClass F α
        β› with
    map_sup := fun f a b => by
      obtain h | h := le_total a b
      · rw [sup_eq_right.2 h, sup_eq_right.2 (OrderHomClass.mono f h : f a ≤ f b)]
      · rw [sup_eq_left.2 h, sup_eq_left.2 (OrderHomClass.mono f h : f b ≤ f a)]
    map_inf := fun f a b => by
      obtain h | h := le_total a b
      · rw [inf_eq_left.2 h, inf_eq_left.2 (OrderHomClass.mono f h : f a ≤ f b)]
      · rw [inf_eq_right.2 h, inf_eq_right.2 (OrderHomClass.mono f h : f b ≤ f a)] }
#align order_hom_class.to_lattice_hom_class OrderHomClass.toLatticeHomClass
-/

#print OrderHomClass.toLatticeHom /-
/-- Reinterpret an order homomorphism to a linear order as a `lattice_hom`. -/
def toLatticeHom (f : F) : LatticeHom α β :=
  haveI : LatticeHomClass F α β := OrderHomClass.toLatticeHomClass α β
  f
#align order_hom_class.to_lattice_hom OrderHomClass.toLatticeHom
-/

#print OrderHomClass.coe_to_lattice_hom /-
@[simp]
theorem coe_to_lattice_hom (f : F) : ⇑(toLatticeHom α β f) = f :=
  rfl
#align order_hom_class.coe_to_lattice_hom OrderHomClass.coe_to_lattice_hom
-/

#print OrderHomClass.to_lattice_hom_apply /-
@[simp]
theorem to_lattice_hom_apply (f : F) (a : α) : toLatticeHom α β f a = f a :=
  rfl
#align order_hom_class.to_lattice_hom_apply OrderHomClass.to_lattice_hom_apply
-/

end OrderHomClass

/-! ### Bounded lattice homomorphisms -/


namespace BoundedLatticeHom

variable [Lattice α] [Lattice β] [Lattice γ] [Lattice δ] [BoundedOrder α] [BoundedOrder β]
  [BoundedOrder γ] [BoundedOrder δ]

#print BoundedLatticeHom.toSupBotHom /-
/-- Reinterpret a `bounded_lattice_hom` as a `sup_bot_hom`. -/
def toSupBotHom (f : BoundedLatticeHom α β) : SupBotHom α β :=
  { f with }
#align bounded_lattice_hom.to_sup_bot_hom BoundedLatticeHom.toSupBotHom
-/

#print BoundedLatticeHom.toInfTopHom /-
/-- Reinterpret a `bounded_lattice_hom` as an `inf_top_hom`. -/
def toInfTopHom (f : BoundedLatticeHom α β) : InfTopHom α β :=
  { f with }
#align bounded_lattice_hom.to_inf_top_hom BoundedLatticeHom.toInfTopHom
-/

#print BoundedLatticeHom.toBoundedOrderHom /-
/-- Reinterpret a `bounded_lattice_hom` as a `bounded_order_hom`. -/
def toBoundedOrderHom (f : BoundedLatticeHom α β) : BoundedOrderHom α β :=
  { f, (f.toLatticeHom : α →o β) with }
#align bounded_lattice_hom.to_bounded_order_hom BoundedLatticeHom.toBoundedOrderHom
-/

instance : BoundedLatticeHomClass (BoundedLatticeHom α β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f <;> obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g <;> congr
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'
  map_bot f := f.map_bot'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (BoundedLatticeHom α β) fun _ => α → β :=
  ⟨fun f => f.toFun⟩

#print BoundedLatticeHom.toFun_eq_coe /-
@[simp]
theorem toFun_eq_coe {f : BoundedLatticeHom α β} : f.toFun = (f : α → β) :=
  rfl
#align bounded_lattice_hom.to_fun_eq_coe BoundedLatticeHom.toFun_eq_coe
-/

#print BoundedLatticeHom.ext /-
@[ext]
theorem ext {f g : BoundedLatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align bounded_lattice_hom.ext BoundedLatticeHom.ext
-/

#print BoundedLatticeHom.copy /-
/-- Copy of a `bounded_lattice_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : BoundedLatticeHom α β) (f' : α → β) (h : f' = f) : BoundedLatticeHom α β :=
  { f.toLatticeHom.copy f' h, f.toBoundedOrderHom.copy f' h with }
#align bounded_lattice_hom.copy BoundedLatticeHom.copy
-/

#print BoundedLatticeHom.coe_copy /-
@[simp]
theorem coe_copy (f : BoundedLatticeHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align bounded_lattice_hom.coe_copy BoundedLatticeHom.coe_copy
-/

#print BoundedLatticeHom.copy_eq /-
theorem copy_eq (f : BoundedLatticeHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align bounded_lattice_hom.copy_eq BoundedLatticeHom.copy_eq
-/

variable (α)

#print BoundedLatticeHom.id /-
/-- `id` as a `bounded_lattice_hom`. -/
protected def id : BoundedLatticeHom α α :=
  { LatticeHom.id α, BoundedOrderHom.id α with }
#align bounded_lattice_hom.id BoundedLatticeHom.id
-/

instance : Inhabited (BoundedLatticeHom α α) :=
  ⟨BoundedLatticeHom.id α⟩

#print BoundedLatticeHom.coe_id /-
@[simp]
theorem coe_id : ⇑(BoundedLatticeHom.id α) = id :=
  rfl
#align bounded_lattice_hom.coe_id BoundedLatticeHom.coe_id
-/

variable {α}

#print BoundedLatticeHom.id_apply /-
@[simp]
theorem id_apply (a : α) : BoundedLatticeHom.id α a = a :=
  rfl
#align bounded_lattice_hom.id_apply BoundedLatticeHom.id_apply
-/

#print BoundedLatticeHom.comp /-
/-- Composition of `bounded_lattice_hom`s as a `bounded_lattice_hom`. -/
def comp (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) : BoundedLatticeHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom, f.toBoundedOrderHom.comp g.toBoundedOrderHom with }
#align bounded_lattice_hom.comp BoundedLatticeHom.comp
-/

#print BoundedLatticeHom.coe_comp /-
@[simp]
theorem coe_comp (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : α → γ) = f ∘ g :=
  rfl
#align bounded_lattice_hom.coe_comp BoundedLatticeHom.coe_comp
-/

#print BoundedLatticeHom.comp_apply /-
@[simp]
theorem comp_apply (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) (a : α) :
    (f.comp g) a = f (g a) :=
  rfl
#align bounded_lattice_hom.comp_apply BoundedLatticeHom.comp_apply
-/

#print BoundedLatticeHom.coe_comp_lattice_hom /-
@[simp]
theorem coe_comp_lattice_hom (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : LatticeHom α γ) = (f : LatticeHom β γ).comp g :=
  rfl
#align bounded_lattice_hom.coe_comp_lattice_hom BoundedLatticeHom.coe_comp_lattice_hom
-/

#print BoundedLatticeHom.coe_comp_sup_hom /-
@[simp]
theorem coe_comp_sup_hom (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : SupHom α γ) = (f : SupHom β γ).comp g :=
  rfl
#align bounded_lattice_hom.coe_comp_sup_hom BoundedLatticeHom.coe_comp_sup_hom
-/

#print BoundedLatticeHom.coe_comp_inf_hom /-
@[simp]
theorem coe_comp_inf_hom (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : InfHom α γ) = (f : InfHom β γ).comp g :=
  rfl
#align bounded_lattice_hom.coe_comp_inf_hom BoundedLatticeHom.coe_comp_inf_hom
-/

#print BoundedLatticeHom.comp_assoc /-
@[simp]
theorem comp_assoc (f : BoundedLatticeHom γ δ) (g : BoundedLatticeHom β γ)
    (h : BoundedLatticeHom α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align bounded_lattice_hom.comp_assoc BoundedLatticeHom.comp_assoc
-/

#print BoundedLatticeHom.comp_id /-
@[simp]
theorem comp_id (f : BoundedLatticeHom α β) : f.comp (BoundedLatticeHom.id α) = f :=
  BoundedLatticeHom.ext fun a => rfl
#align bounded_lattice_hom.comp_id BoundedLatticeHom.comp_id
-/

#print BoundedLatticeHom.id_comp /-
@[simp]
theorem id_comp (f : BoundedLatticeHom α β) : (BoundedLatticeHom.id β).comp f = f :=
  BoundedLatticeHom.ext fun a => rfl
#align bounded_lattice_hom.id_comp BoundedLatticeHom.id_comp
-/

#print BoundedLatticeHom.cancel_right /-
theorem cancel_right {g₁ g₂ : BoundedLatticeHom β γ} {f : BoundedLatticeHom α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => BoundedLatticeHom.ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align bounded_lattice_hom.cancel_right BoundedLatticeHom.cancel_right
-/

#print BoundedLatticeHom.cancel_left /-
theorem cancel_left {g : BoundedLatticeHom β γ} {f₁ f₂ : BoundedLatticeHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align bounded_lattice_hom.cancel_left BoundedLatticeHom.cancel_left
-/

end BoundedLatticeHom

/-! ### Dual homs -/


namespace SupHom

variable [Sup α] [Sup β] [Sup γ]

#print SupHom.dual /-
/-- Reinterpret a supremum homomorphism as an infimum homomorphism between the dual lattices. -/
@[simps]
protected def dual : SupHom α β ≃ InfHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨f, f.map_sup'⟩
  invFun f := ⟨f, f.map_inf'⟩
  left_inv f := SupHom.ext fun _ => rfl
  right_inv f := InfHom.ext fun _ => rfl
#align sup_hom.dual SupHom.dual
-/

#print SupHom.dual_id /-
@[simp]
theorem dual_id : (SupHom.id α).dual = InfHom.id _ :=
  rfl
#align sup_hom.dual_id SupHom.dual_id
-/

#print SupHom.dual_comp /-
@[simp]
theorem dual_comp (g : SupHom β γ) (f : SupHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl
#align sup_hom.dual_comp SupHom.dual_comp
-/

#print SupHom.symm_dual_id /-
@[simp]
theorem symm_dual_id : SupHom.dual.symm (InfHom.id _) = SupHom.id α :=
  rfl
#align sup_hom.symm_dual_id SupHom.symm_dual_id
-/

#print SupHom.symm_dual_comp /-
@[simp]
theorem symm_dual_comp (g : InfHom βᵒᵈ γᵒᵈ) (f : InfHom αᵒᵈ βᵒᵈ) :
    SupHom.dual.symm (g.comp f) = (SupHom.dual.symm g).comp (SupHom.dual.symm f) :=
  rfl
#align sup_hom.symm_dual_comp SupHom.symm_dual_comp
-/

end SupHom

namespace InfHom

variable [Inf α] [Inf β] [Inf γ]

#print InfHom.dual /-
/-- Reinterpret an infimum homomorphism as a supremum homomorphism between the dual lattices. -/
@[simps]
protected def dual : InfHom α β ≃ SupHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨f, f.map_inf'⟩
  invFun f := ⟨f, f.map_sup'⟩
  left_inv f := InfHom.ext fun _ => rfl
  right_inv f := SupHom.ext fun _ => rfl
#align inf_hom.dual InfHom.dual
-/

#print InfHom.dual_id /-
@[simp]
theorem dual_id : (InfHom.id α).dual = SupHom.id _ :=
  rfl
#align inf_hom.dual_id InfHom.dual_id
-/

#print InfHom.dual_comp /-
@[simp]
theorem dual_comp (g : InfHom β γ) (f : InfHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl
#align inf_hom.dual_comp InfHom.dual_comp
-/

#print InfHom.symm_dual_id /-
@[simp]
theorem symm_dual_id : InfHom.dual.symm (SupHom.id _) = InfHom.id α :=
  rfl
#align inf_hom.symm_dual_id InfHom.symm_dual_id
-/

#print InfHom.symm_dual_comp /-
@[simp]
theorem symm_dual_comp (g : SupHom βᵒᵈ γᵒᵈ) (f : SupHom αᵒᵈ βᵒᵈ) :
    InfHom.dual.symm (g.comp f) = (InfHom.dual.symm g).comp (InfHom.dual.symm f) :=
  rfl
#align inf_hom.symm_dual_comp InfHom.symm_dual_comp
-/

end InfHom

namespace SupBotHom

variable [Sup α] [Bot α] [Sup β] [Bot β] [Sup γ] [Bot γ]

#print SupBotHom.dual /-
/-- Reinterpret a finitary supremum homomorphism as a finitary infimum homomorphism between the dual
lattices. -/
def dual : SupBotHom α β ≃ InfTopHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨f.toSupHom.dual, f.map_bot'⟩
  invFun f := ⟨SupHom.dual.symm f.toInfHom, f.map_top'⟩
  left_inv f := SupBotHom.ext fun _ => rfl
  right_inv f := InfTopHom.ext fun _ => rfl
#align sup_bot_hom.dual SupBotHom.dual
-/

#print SupBotHom.dual_id /-
@[simp]
theorem dual_id : (SupBotHom.id α).dual = InfTopHom.id _ :=
  rfl
#align sup_bot_hom.dual_id SupBotHom.dual_id
-/

#print SupBotHom.dual_comp /-
@[simp]
theorem dual_comp (g : SupBotHom β γ) (f : SupBotHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl
#align sup_bot_hom.dual_comp SupBotHom.dual_comp
-/

#print SupBotHom.symm_dual_id /-
@[simp]
theorem symm_dual_id : SupBotHom.dual.symm (InfTopHom.id _) = SupBotHom.id α :=
  rfl
#align sup_bot_hom.symm_dual_id SupBotHom.symm_dual_id
-/

#print SupBotHom.symm_dual_comp /-
@[simp]
theorem symm_dual_comp (g : InfTopHom βᵒᵈ γᵒᵈ) (f : InfTopHom αᵒᵈ βᵒᵈ) :
    SupBotHom.dual.symm (g.comp f) = (SupBotHom.dual.symm g).comp (SupBotHom.dual.symm f) :=
  rfl
#align sup_bot_hom.symm_dual_comp SupBotHom.symm_dual_comp
-/

end SupBotHom

namespace InfTopHom

variable [Inf α] [Top α] [Inf β] [Top β] [Inf γ] [Top γ]

#print InfTopHom.dual /-
/-- Reinterpret a finitary infimum homomorphism as a finitary supremum homomorphism between the dual
lattices. -/
@[simps]
protected def dual : InfTopHom α β ≃ SupBotHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨f.toInfHom.dual, f.map_top'⟩
  invFun f := ⟨InfHom.dual.symm f.toSupHom, f.map_bot'⟩
  left_inv f := InfTopHom.ext fun _ => rfl
  right_inv f := SupBotHom.ext fun _ => rfl
#align inf_top_hom.dual InfTopHom.dual
-/

#print InfTopHom.dual_id /-
@[simp]
theorem dual_id : (InfTopHom.id α).dual = SupBotHom.id _ :=
  rfl
#align inf_top_hom.dual_id InfTopHom.dual_id
-/

#print InfTopHom.dual_comp /-
@[simp]
theorem dual_comp (g : InfTopHom β γ) (f : InfTopHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl
#align inf_top_hom.dual_comp InfTopHom.dual_comp
-/

#print InfTopHom.symm_dual_id /-
@[simp]
theorem symm_dual_id : InfTopHom.dual.symm (SupBotHom.id _) = InfTopHom.id α :=
  rfl
#align inf_top_hom.symm_dual_id InfTopHom.symm_dual_id
-/

#print InfTopHom.symm_dual_comp /-
@[simp]
theorem symm_dual_comp (g : SupBotHom βᵒᵈ γᵒᵈ) (f : SupBotHom αᵒᵈ βᵒᵈ) :
    InfTopHom.dual.symm (g.comp f) = (InfTopHom.dual.symm g).comp (InfTopHom.dual.symm f) :=
  rfl
#align inf_top_hom.symm_dual_comp InfTopHom.symm_dual_comp
-/

end InfTopHom

namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ]

#print LatticeHom.dual /-
/-- Reinterpret a lattice homomorphism as a lattice homomorphism between the dual lattices. -/
@[simps]
protected def dual : LatticeHom α β ≃ LatticeHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨f.toInfHom.dual, f.map_sup'⟩
  invFun f := ⟨f.toInfHom.dual, f.map_sup'⟩
  left_inv f := ext fun a => rfl
  right_inv f := ext fun a => rfl
#align lattice_hom.dual LatticeHom.dual
-/

#print LatticeHom.dual_id /-
@[simp]
theorem dual_id : (LatticeHom.id α).dual = LatticeHom.id _ :=
  rfl
#align lattice_hom.dual_id LatticeHom.dual_id
-/

#print LatticeHom.dual_comp /-
@[simp]
theorem dual_comp (g : LatticeHom β γ) (f : LatticeHom α β) :
    (g.comp f).dual = g.dual.comp f.dual :=
  rfl
#align lattice_hom.dual_comp LatticeHom.dual_comp
-/

#print LatticeHom.symm_dual_id /-
@[simp]
theorem symm_dual_id : LatticeHom.dual.symm (LatticeHom.id _) = LatticeHom.id α :=
  rfl
#align lattice_hom.symm_dual_id LatticeHom.symm_dual_id
-/

#print LatticeHom.symm_dual_comp /-
@[simp]
theorem symm_dual_comp (g : LatticeHom βᵒᵈ γᵒᵈ) (f : LatticeHom αᵒᵈ βᵒᵈ) :
    LatticeHom.dual.symm (g.comp f) = (LatticeHom.dual.symm g).comp (LatticeHom.dual.symm f) :=
  rfl
#align lattice_hom.symm_dual_comp LatticeHom.symm_dual_comp
-/

end LatticeHom

namespace BoundedLatticeHom

variable [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β] [Lattice γ] [BoundedOrder γ]

#print BoundedLatticeHom.dual /-
/-- Reinterpret a bounded lattice homomorphism as a bounded lattice homomorphism between the dual
bounded lattices. -/
@[simps]
protected def dual : BoundedLatticeHom α β ≃ BoundedLatticeHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨f.toLatticeHom.dual, f.map_bot', f.map_top'⟩
  invFun f := ⟨LatticeHom.dual.symm f.toLatticeHom, f.map_bot', f.map_top'⟩
  left_inv f := ext fun a => rfl
  right_inv f := ext fun a => rfl
#align bounded_lattice_hom.dual BoundedLatticeHom.dual
-/

#print BoundedLatticeHom.dual_id /-
@[simp]
theorem dual_id : (BoundedLatticeHom.id α).dual = BoundedLatticeHom.id _ :=
  rfl
#align bounded_lattice_hom.dual_id BoundedLatticeHom.dual_id
-/

#print BoundedLatticeHom.dual_comp /-
@[simp]
theorem dual_comp (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β) :
    (g.comp f).dual = g.dual.comp f.dual :=
  rfl
#align bounded_lattice_hom.dual_comp BoundedLatticeHom.dual_comp
-/

#print BoundedLatticeHom.symm_dual_id /-
@[simp]
theorem symm_dual_id :
    BoundedLatticeHom.dual.symm (BoundedLatticeHom.id _) = BoundedLatticeHom.id α :=
  rfl
#align bounded_lattice_hom.symm_dual_id BoundedLatticeHom.symm_dual_id
-/

#print BoundedLatticeHom.symm_dual_comp /-
@[simp]
theorem symm_dual_comp (g : BoundedLatticeHom βᵒᵈ γᵒᵈ) (f : BoundedLatticeHom αᵒᵈ βᵒᵈ) :
    BoundedLatticeHom.dual.symm (g.comp f) =
      (BoundedLatticeHom.dual.symm g).comp (BoundedLatticeHom.dual.symm f) :=
  rfl
#align bounded_lattice_hom.symm_dual_comp BoundedLatticeHom.symm_dual_comp
-/

end BoundedLatticeHom

/-! ### `with_top`, `with_bot` -/


namespace SupHom

variable [SemilatticeSup α] [SemilatticeSup β] [SemilatticeSup γ]

#print SupHom.withTop /-
/-- Adjoins a `⊤` to the domain and codomain of a `sup_hom`. -/
@[simps]
protected def withTop (f : SupHom α β) : SupHom (WithTop α) (WithTop β)
    where
  toFun := Option.map f
  map_sup' a b :=
    match a, b with
    | ⊤, ⊤ => rfl
    | ⊤, (b : α) => rfl
    | (a : α), ⊤ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_sup' _ _)
#align sup_hom.with_top SupHom.withTop
-/

#print SupHom.withTop_id /-
@[simp]
theorem withTop_id : (SupHom.id α).WithTop = SupHom.id _ :=
  FunLike.coe_injective Option.map_id
#align sup_hom.with_top_id SupHom.withTop_id
-/

#print SupHom.withTop_comp /-
@[simp]
theorem withTop_comp (f : SupHom β γ) (g : SupHom α β) :
    (f.comp g).WithTop = f.WithTop.comp g.WithTop :=
  FunLike.coe_injective (Option.map_comp_map _ _).symm
#align sup_hom.with_top_comp SupHom.withTop_comp
-/

#print SupHom.withBot /-
/-- Adjoins a `⊥` to the domain and codomain of a `sup_hom`. -/
@[simps]
protected def withBot (f : SupHom α β) : SupBotHom (WithBot α) (WithBot β)
    where
  toFun := Option.map f
  map_sup' a b :=
    match a, b with
    | ⊥, ⊥ => rfl
    | ⊥, (b : α) => rfl
    | (a : α), ⊥ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_sup' _ _)
  map_bot' := rfl
#align sup_hom.with_bot SupHom.withBot
-/

#print SupHom.withBot_id /-
@[simp]
theorem withBot_id : (SupHom.id α).WithBot = SupBotHom.id _ :=
  FunLike.coe_injective Option.map_id
#align sup_hom.with_bot_id SupHom.withBot_id
-/

#print SupHom.withBot_comp /-
@[simp]
theorem withBot_comp (f : SupHom β γ) (g : SupHom α β) :
    (f.comp g).WithBot = f.WithBot.comp g.WithBot :=
  FunLike.coe_injective (Option.map_comp_map _ _).symm
#align sup_hom.with_bot_comp SupHom.withBot_comp
-/

#print SupHom.withTop' /-
/-- Adjoins a `⊤` to the codomain of a `sup_hom`. -/
@[simps]
def withTop' [OrderTop β] (f : SupHom α β) : SupHom (WithTop α) β
    where
  toFun a := a.elim ⊤ f
  map_sup' a b :=
    match a, b with
    | ⊤, ⊤ => top_sup_eq.symm
    | ⊤, (b : α) => top_sup_eq.symm
    | (a : α), ⊤ => sup_top_eq.symm
    | (a : α), (b : α) => f.map_sup' _ _
#align sup_hom.with_top' SupHom.withTop'
-/

#print SupHom.withBot' /-
/-- Adjoins a `⊥` to the domain of a `sup_hom`. -/
@[simps]
def withBot' [OrderBot β] (f : SupHom α β) : SupBotHom (WithBot α) β
    where
  toFun a := a.elim ⊥ f
  map_sup' a b :=
    match a, b with
    | ⊥, ⊥ => bot_sup_eq.symm
    | ⊥, (b : α) => bot_sup_eq.symm
    | (a : α), ⊥ => sup_bot_eq.symm
    | (a : α), (b : α) => f.map_sup' _ _
  map_bot' := rfl
#align sup_hom.with_bot' SupHom.withBot'
-/

end SupHom

namespace InfHom

variable [SemilatticeInf α] [SemilatticeInf β] [SemilatticeInf γ]

#print InfHom.withTop /-
/-- Adjoins a `⊤` to the domain and codomain of an `inf_hom`. -/
@[simps]
protected def withTop (f : InfHom α β) : InfTopHom (WithTop α) (WithTop β)
    where
  toFun := Option.map f
  map_inf' a b :=
    match a, b with
    | ⊤, ⊤ => rfl
    | ⊤, (b : α) => rfl
    | (a : α), ⊤ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_inf' _ _)
  map_top' := rfl
#align inf_hom.with_top InfHom.withTop
-/

#print InfHom.withTop_id /-
@[simp]
theorem withTop_id : (InfHom.id α).WithTop = InfTopHom.id _ :=
  FunLike.coe_injective Option.map_id
#align inf_hom.with_top_id InfHom.withTop_id
-/

#print InfHom.withTop_comp /-
@[simp]
theorem withTop_comp (f : InfHom β γ) (g : InfHom α β) :
    (f.comp g).WithTop = f.WithTop.comp g.WithTop :=
  FunLike.coe_injective (Option.map_comp_map _ _).symm
#align inf_hom.with_top_comp InfHom.withTop_comp
-/

#print InfHom.withBot /-
/-- Adjoins a `⊥ to the domain and codomain of an `inf_hom`. -/
@[simps]
protected def withBot (f : InfHom α β) : InfHom (WithBot α) (WithBot β)
    where
  toFun := Option.map f
  map_inf' a b :=
    match a, b with
    | ⊥, ⊥ => rfl
    | ⊥, (b : α) => rfl
    | (a : α), ⊥ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_inf' _ _)
#align inf_hom.with_bot InfHom.withBot
-/

#print InfHom.withBot_id /-
@[simp]
theorem withBot_id : (InfHom.id α).WithBot = InfHom.id _ :=
  FunLike.coe_injective Option.map_id
#align inf_hom.with_bot_id InfHom.withBot_id
-/

#print InfHom.withBot_comp /-
@[simp]
theorem withBot_comp (f : InfHom β γ) (g : InfHom α β) :
    (f.comp g).WithBot = f.WithBot.comp g.WithBot :=
  FunLike.coe_injective (Option.map_comp_map _ _).symm
#align inf_hom.with_bot_comp InfHom.withBot_comp
-/

#print InfHom.withTop' /-
/-- Adjoins a `⊤` to the codomain of an `inf_hom`. -/
@[simps]
def withTop' [OrderTop β] (f : InfHom α β) : InfTopHom (WithTop α) β
    where
  toFun a := a.elim ⊤ f
  map_inf' a b :=
    match a, b with
    | ⊤, ⊤ => top_inf_eq.symm
    | ⊤, (b : α) => top_inf_eq.symm
    | (a : α), ⊤ => inf_top_eq.symm
    | (a : α), (b : α) => f.map_inf' _ _
  map_top' := rfl
#align inf_hom.with_top' InfHom.withTop'
-/

#print InfHom.withBot' /-
/-- Adjoins a `⊥` to the codomain of an `inf_hom`. -/
@[simps]
def withBot' [OrderBot β] (f : InfHom α β) : InfHom (WithBot α) β
    where
  toFun a := a.elim ⊥ f
  map_inf' a b :=
    match a, b with
    | ⊥, ⊥ => bot_inf_eq.symm
    | ⊥, (b : α) => bot_inf_eq.symm
    | (a : α), ⊥ => inf_bot_eq.symm
    | (a : α), (b : α) => f.map_inf' _ _
#align inf_hom.with_bot' InfHom.withBot'
-/

end InfHom

namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ]

#print LatticeHom.withTop /-
/-- Adjoins a `⊤` to the domain and codomain of a `lattice_hom`. -/
@[simps]
protected def withTop (f : LatticeHom α β) : LatticeHom (WithTop α) (WithTop β) :=
  { f.toInfHom.WithTop with toSupHom := f.toSupHom.WithTop }
#align lattice_hom.with_top LatticeHom.withTop
-/

#print LatticeHom.withTop_id /-
@[simp]
theorem withTop_id : (LatticeHom.id α).WithTop = LatticeHom.id _ :=
  FunLike.coe_injective Option.map_id
#align lattice_hom.with_top_id LatticeHom.withTop_id
-/

#print LatticeHom.withTop_comp /-
@[simp]
theorem withTop_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).WithTop = f.WithTop.comp g.WithTop :=
  FunLike.coe_injective (Option.map_comp_map _ _).symm
#align lattice_hom.with_top_comp LatticeHom.withTop_comp
-/

#print LatticeHom.withBot /-
/-- Adjoins a `⊥` to the domain and codomain of a `lattice_hom`. -/
@[simps]
protected def withBot (f : LatticeHom α β) : LatticeHom (WithBot α) (WithBot β) :=
  { f.toInfHom.WithBot with toSupHom := f.toSupHom.WithBot }
#align lattice_hom.with_bot LatticeHom.withBot
-/

#print LatticeHom.withBot_id /-
@[simp]
theorem withBot_id : (LatticeHom.id α).WithBot = LatticeHom.id _ :=
  FunLike.coe_injective Option.map_id
#align lattice_hom.with_bot_id LatticeHom.withBot_id
-/

#print LatticeHom.withBot_comp /-
@[simp]
theorem withBot_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).WithBot = f.WithBot.comp g.WithBot :=
  FunLike.coe_injective (Option.map_comp_map _ _).symm
#align lattice_hom.with_bot_comp LatticeHom.withBot_comp
-/

#print LatticeHom.withTopWithBot /-
/-- Adjoins a `⊤` and `⊥` to the domain and codomain of a `lattice_hom`. -/
@[simps]
def withTopWithBot (f : LatticeHom α β) :
    BoundedLatticeHom (WithTop <| WithBot α) (WithTop <| WithBot β) :=
  ⟨f.WithBot.WithTop, rfl, rfl⟩
#align lattice_hom.with_top_with_bot LatticeHom.withTopWithBot
-/

#print LatticeHom.withTopWithBot_id /-
@[simp]
theorem withTopWithBot_id : (LatticeHom.id α).withTopWithBot = BoundedLatticeHom.id _ :=
  FunLike.coe_injective <|
    by
    refine' (congr_arg Option.map _).trans Option.map_id
    rw [with_bot_id]
    rfl
#align lattice_hom.with_top_with_bot_id LatticeHom.withTopWithBot_id
-/

#print LatticeHom.withTopWithBot_comp /-
@[simp]
theorem withTopWithBot_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).withTopWithBot = f.withTopWithBot.comp g.withTopWithBot :=
  FunLike.coe_injective <|
    (congr_arg Option.map <| (Option.map_comp_map _ _).symm).trans (Option.map_comp_map _ _).symm
#align lattice_hom.with_top_with_bot_comp LatticeHom.withTopWithBot_comp
-/

#print LatticeHom.withTop' /-
/-- Adjoins a `⊥` to the codomain of a `lattice_hom`. -/
@[simps]
def withTop' [OrderTop β] (f : LatticeHom α β) : LatticeHom (WithTop α) β :=
  { f.toSupHom.withTop', f.toInfHom.withTop' with }
#align lattice_hom.with_top' LatticeHom.withTop'
-/

#print LatticeHom.withBot' /-
/-- Adjoins a `⊥` to the domain and codomain of a `lattice_hom`. -/
@[simps]
def withBot' [OrderBot β] (f : LatticeHom α β) : LatticeHom (WithBot α) β :=
  { f.toSupHom.withBot', f.toInfHom.withBot' with }
#align lattice_hom.with_bot' LatticeHom.withBot'
-/

#print LatticeHom.withTopWithBot' /-
/-- Adjoins a `⊤` and `⊥` to the codomain of a `lattice_hom`. -/
@[simps]
def withTopWithBot' [BoundedOrder β] (f : LatticeHom α β) :
    BoundedLatticeHom (WithTop <| WithBot α) β
    where
  toLatticeHom := f.withBot'.withTop'
  map_top' := rfl
  map_bot' := rfl
#align lattice_hom.with_top_with_bot' LatticeHom.withTopWithBot'
-/

end LatticeHom

