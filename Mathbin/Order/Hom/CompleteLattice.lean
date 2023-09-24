/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Data.Set.Lattice
import Order.Hom.Lattice

#align_import order.hom.complete_lattice from "leanprover-community/mathlib"@"9d684a893c52e1d6692a504a118bfccbae04feeb"

/-!
# Complete lattice homomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines frame homorphisms and complete lattice homomorphisms.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `Sup_hom`: Maps which preserve `⨆`.
* `Inf_hom`: Maps which preserve `⨅`.
* `frame_hom`: Frame homomorphisms. Maps which preserve `⨆`, `⊓` and `⊤`.
* `complete_lattice_hom`: Complete lattice homomorphisms. Maps which preserve `⨆` and `⨅`.

## Typeclasses

* `Sup_hom_class`
* `Inf_hom_class`
* `frame_hom_class`
* `complete_lattice_hom_class`

## Concrete homs

* `complete_lattice.set_preimage`: `set.preimage` as a complete lattice homomorphism.

## TODO

Frame homs are Heyting homs.
-/


open Function OrderDual Set

variable {F α β γ δ : Type _} {ι : Sort _} {κ : ι → Sort _}

#print sSupHom /-
/-- The type of `⨆`-preserving functions from `α` to `β`. -/
structure sSupHom (α β : Type _) [SupSet α] [SupSet β] where
  toFun : α → β
  map_Sup' (s : Set α) : to_fun (sSup s) = sSup (to_fun '' s)
#align Sup_hom sSupHom
-/

#print sInfHom /-
/-- The type of `⨅`-preserving functions from `α` to `β`. -/
structure sInfHom (α β : Type _) [InfSet α] [InfSet β] where
  toFun : α → β
  map_Inf' (s : Set α) : to_fun (sInf s) = sInf (to_fun '' s)
#align Inf_hom sInfHom
-/

#print FrameHom /-
/-- The type of frame homomorphisms from `α` to `β`. They preserve finite meets and arbitrary joins.
-/
structure FrameHom (α β : Type _) [CompleteLattice α] [CompleteLattice β] extends
    InfTopHom α β where
  map_Sup' (s : Set α) : to_fun (sSup s) = sSup (to_fun '' s)
#align frame_hom FrameHom
-/

#print CompleteLatticeHom /-
/-- The type of complete lattice homomorphisms from `α` to `β`. -/
structure CompleteLatticeHom (α β : Type _) [CompleteLattice α] [CompleteLattice β] extends
    sInfHom α β where
  map_Sup' (s : Set α) : to_fun (sSup s) = sSup (to_fun '' s)
#align complete_lattice_hom CompleteLatticeHom
-/

section

#print sSupHomClass /-
/-- `Sup_hom_class F α β` states that `F` is a type of `⨆`-preserving morphisms.

You should extend this class when you extend `Sup_hom`. -/
class sSupHomClass (F : Type _) (α β : outParam <| Type _) [SupSet α] [SupSet β] extends
    FunLike F α fun _ => β where
  map_sSup (f : F) (s : Set α) : f (sSup s) = sSup (f '' s)
#align Sup_hom_class sSupHomClass
-/

#print sInfHomClass /-
/-- `Inf_hom_class F α β` states that `F` is a type of `⨅`-preserving morphisms.

You should extend this class when you extend `Inf_hom`. -/
class sInfHomClass (F : Type _) (α β : outParam <| Type _) [InfSet α] [InfSet β] extends
    FunLike F α fun _ => β where
  map_sInf (f : F) (s : Set α) : f (sInf s) = sInf (f '' s)
#align Inf_hom_class sInfHomClass
-/

#print FrameHomClass /-
/-- `frame_hom_class F α β` states that `F` is a type of frame morphisms. They preserve `⊓` and `⨆`.

You should extend this class when you extend `frame_hom`. -/
class FrameHomClass (F : Type _) (α β : outParam <| Type _) [CompleteLattice α]
    [CompleteLattice β] extends InfTopHomClass F α β where
  map_sSup (f : F) (s : Set α) : f (sSup s) = sSup (f '' s)
#align frame_hom_class FrameHomClass
-/

#print CompleteLatticeHomClass /-
/-- `complete_lattice_hom_class F α β` states that `F` is a type of complete lattice morphisms.

You should extend this class when you extend `complete_lattice_hom`. -/
class CompleteLatticeHomClass (F : Type _) (α β : outParam <| Type _) [CompleteLattice α]
    [CompleteLattice β] extends sInfHomClass F α β where
  map_sSup (f : F) (s : Set α) : f (sSup s) = sSup (f '' s)
#align complete_lattice_hom_class CompleteLatticeHomClass
-/

end

export sSupHomClass (map_sSup)

export sInfHomClass (map_sInf)

attribute [simp] map_Sup map_Inf

#print map_iSup /-
theorem map_iSup [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g : ι → α) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by rw [iSup, iSup, map_Sup, Set.range_comp]
#align map_supr map_iSup
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print map_iSup₂ /-
theorem map_iSup₂ [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨆ (i) (j), g i j) = ⨆ (i) (j), f (g i j) := by simp_rw [map_iSup]
#align map_supr₂ map_iSup₂
-/

#print map_iInf /-
theorem map_iInf [InfSet α] [InfSet β] [sInfHomClass F α β] (f : F) (g : ι → α) :
    f (⨅ i, g i) = ⨅ i, f (g i) := by rw [iInf, iInf, map_Inf, Set.range_comp]
#align map_infi map_iInf
-/

/- warning: map_infi₂ clashes with map_infi -> map_iInf
Case conversion may be inaccurate. Consider using '#align map_infi₂ map_iInfₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print map_iInf /-
theorem map_iInf [InfSet α] [InfSet β] [sInfHomClass F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨅ (i) (j), g i j) = ⨅ (i) (j), f (g i j) := by simp_rw [map_iInf]
#align map_infi₂ map_iInf
-/

#print sSupHomClass.toSupBotHomClass /-
-- See note [lower instance priority]
instance (priority := 100) sSupHomClass.toSupBotHomClass [CompleteLattice α] [CompleteLattice β]
    [sSupHomClass F α β] : SupBotHomClass F α β :=
  {
    ‹sSupHomClass F α
        β› with
    map_sup := fun f a b => by rw [← sSup_pair, map_Sup, Set.image_pair, sSup_pair]
    map_bot := fun f => by rw [← sSup_empty, map_Sup, Set.image_empty, sSup_empty] }
#align Sup_hom_class.to_sup_bot_hom_class sSupHomClass.toSupBotHomClass
-/

#print sInfHomClass.toInfTopHomClass /-
-- See note [lower instance priority]
instance (priority := 100) sInfHomClass.toInfTopHomClass [CompleteLattice α] [CompleteLattice β]
    [sInfHomClass F α β] : InfTopHomClass F α β :=
  {
    ‹sInfHomClass F α
        β› with
    map_inf := fun f a b => by rw [← sInf_pair, map_Inf, Set.image_pair, sInf_pair]
    map_top := fun f => by rw [← sInf_empty, map_Inf, Set.image_empty, sInf_empty] }
#align Inf_hom_class.to_inf_top_hom_class sInfHomClass.toInfTopHomClass
-/

#print FrameHomClass.tosSupHomClass /-
-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.tosSupHomClass [CompleteLattice α] [CompleteLattice β]
    [FrameHomClass F α β] : sSupHomClass F α β :=
  { ‹FrameHomClass F α β› with }
#align frame_hom_class.to_Sup_hom_class FrameHomClass.tosSupHomClass
-/

#print FrameHomClass.toBoundedLatticeHomClass /-
-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [FrameHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹FrameHomClass F α β›, sSupHomClass.toSupBotHomClass with }
#align frame_hom_class.to_bounded_lattice_hom_class FrameHomClass.toBoundedLatticeHomClass
-/

#print CompleteLatticeHomClass.toFrameHomClass /-
-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toFrameHomClass [CompleteLattice α]
    [CompleteLattice β] [CompleteLatticeHomClass F α β] : FrameHomClass F α β :=
  { ‹CompleteLatticeHomClass F α β›, sInfHomClass.toInfTopHomClass with }
#align complete_lattice_hom_class.to_frame_hom_class CompleteLatticeHomClass.toFrameHomClass
-/

#print CompleteLatticeHomClass.toBoundedLatticeHomClass /-
-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [CompleteLatticeHomClass F α β] : BoundedLatticeHomClass F α β :=
  { sSupHomClass.toSupBotHomClass, sInfHomClass.toInfTopHomClass with }
#align complete_lattice_hom_class.to_bounded_lattice_hom_class CompleteLatticeHomClass.toBoundedLatticeHomClass
-/

#print OrderIsoClass.tosSupHomClass /-
-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.tosSupHomClass [CompleteLattice α] [CompleteLattice β]
    [OrderIsoClass F α β] : sSupHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_sSup := fun f s =>
      eq_of_forall_ge_iff fun c => by
        simp only [← le_map_inv_iff, sSup_le_iff, Set.ball_image_iff] }
#align order_iso_class.to_Sup_hom_class OrderIsoClass.tosSupHomClass
-/

#print OrderIsoClass.tosInfHomClass /-
-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.tosInfHomClass [CompleteLattice α] [CompleteLattice β]
    [OrderIsoClass F α β] : sInfHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_sInf := fun f s =>
      eq_of_forall_le_iff fun c => by
        simp only [← map_inv_le_iff, le_sInf_iff, Set.ball_image_iff] }
#align order_iso_class.to_Inf_hom_class OrderIsoClass.tosInfHomClass
-/

#print OrderIsoClass.toCompleteLatticeHomClass /-
-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toCompleteLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [OrderIsoClass F α β] : CompleteLatticeHomClass F α β :=
  { OrderIsoClass.tosSupHomClass, OrderIsoClass.toLatticeHomClass,
    show sInfHomClass F α β from inferInstance with }
#align order_iso_class.to_complete_lattice_hom_class OrderIsoClass.toCompleteLatticeHomClass
-/

instance [SupSet α] [SupSet β] [sSupHomClass F α β] : CoeTC F (sSupHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩

instance [InfSet α] [InfSet β] [sInfHomClass F α β] : CoeTC F (sInfHom α β) :=
  ⟨fun f => ⟨f, map_sInf f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [FrameHomClass F α β] : CoeTC F (FrameHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [CompleteLatticeHomClass F α β] :
    CoeTC F (CompleteLatticeHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩

/-! ### Supremum homomorphisms -/


namespace sSupHom

variable [SupSet α]

section SupSet

variable [SupSet β] [SupSet γ] [SupSet δ]

instance : sSupHomClass (sSupHom α β) α β
    where
  coe := sSupHom.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_sSup := sSupHom.map_Sup'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (sSupHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

#print sSupHom.toFun_eq_coe /-
@[simp]
theorem toFun_eq_coe {f : sSupHom α β} : f.toFun = (f : α → β) :=
  rfl
#align Sup_hom.to_fun_eq_coe sSupHom.toFun_eq_coe
-/

#print sSupHom.ext /-
@[ext]
theorem ext {f g : sSupHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align Sup_hom.ext sSupHom.ext
-/

#print sSupHom.copy /-
/-- Copy of a `Sup_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : sSupHom α β) (f' : α → β) (h : f' = f) : sSupHom α β
    where
  toFun := f'
  map_Sup' := h.symm ▸ f.map_Sup'
#align Sup_hom.copy sSupHom.copy
-/

#print sSupHom.coe_copy /-
@[simp]
theorem coe_copy (f : sSupHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align Sup_hom.coe_copy sSupHom.coe_copy
-/

#print sSupHom.copy_eq /-
theorem copy_eq (f : sSupHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align Sup_hom.copy_eq sSupHom.copy_eq
-/

variable (α)

#print sSupHom.id /-
/-- `id` as a `Sup_hom`. -/
protected def id : sSupHom α α :=
  ⟨id, fun s => by rw [id, Set.image_id]⟩
#align Sup_hom.id sSupHom.id
-/

instance : Inhabited (sSupHom α α) :=
  ⟨sSupHom.id α⟩

#print sSupHom.coe_id /-
@[simp]
theorem coe_id : ⇑(sSupHom.id α) = id :=
  rfl
#align Sup_hom.coe_id sSupHom.coe_id
-/

variable {α}

#print sSupHom.id_apply /-
@[simp]
theorem id_apply (a : α) : sSupHom.id α a = a :=
  rfl
#align Sup_hom.id_apply sSupHom.id_apply
-/

#print sSupHom.comp /-
/-- Composition of `Sup_hom`s as a `Sup_hom`. -/
def comp (f : sSupHom β γ) (g : sSupHom α β) : sSupHom α γ
    where
  toFun := f ∘ g
  map_Sup' s := by rw [comp_apply, map_Sup, map_Sup, Set.image_image]
#align Sup_hom.comp sSupHom.comp
-/

#print sSupHom.coe_comp /-
@[simp]
theorem coe_comp (f : sSupHom β γ) (g : sSupHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align Sup_hom.coe_comp sSupHom.coe_comp
-/

#print sSupHom.comp_apply /-
@[simp]
theorem comp_apply (f : sSupHom β γ) (g : sSupHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align Sup_hom.comp_apply sSupHom.comp_apply
-/

#print sSupHom.comp_assoc /-
@[simp]
theorem comp_assoc (f : sSupHom γ δ) (g : sSupHom β γ) (h : sSupHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align Sup_hom.comp_assoc sSupHom.comp_assoc
-/

#print sSupHom.comp_id /-
@[simp]
theorem comp_id (f : sSupHom α β) : f.comp (sSupHom.id α) = f :=
  ext fun a => rfl
#align Sup_hom.comp_id sSupHom.comp_id
-/

#print sSupHom.id_comp /-
@[simp]
theorem id_comp (f : sSupHom α β) : (sSupHom.id β).comp f = f :=
  ext fun a => rfl
#align Sup_hom.id_comp sSupHom.id_comp
-/

#print sSupHom.cancel_right /-
theorem cancel_right {g₁ g₂ : sSupHom β γ} {f : sSupHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align Sup_hom.cancel_right sSupHom.cancel_right
-/

#print sSupHom.cancel_left /-
theorem cancel_left {g : sSupHom β γ} {f₁ f₂ : sSupHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align Sup_hom.cancel_left sSupHom.cancel_left
-/

end SupSet

variable [CompleteLattice β]

instance : PartialOrder (sSupHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

instance : Bot (sSupHom α β) :=
  ⟨⟨fun _ => ⊥, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, sSup_empty]
      · rw [hs.image_const, sSup_singleton]⟩⟩

instance : OrderBot (sSupHom α β) :=
  ⟨⊥, fun f a => bot_le⟩

#print sSupHom.coe_bot /-
@[simp]
theorem coe_bot : ⇑(⊥ : sSupHom α β) = ⊥ :=
  rfl
#align Sup_hom.coe_bot sSupHom.coe_bot
-/

#print sSupHom.bot_apply /-
@[simp]
theorem bot_apply (a : α) : (⊥ : sSupHom α β) a = ⊥ :=
  rfl
#align Sup_hom.bot_apply sSupHom.bot_apply
-/

end sSupHom

/-! ### Infimum homomorphisms -/


namespace sInfHom

variable [InfSet α]

section InfSet

variable [InfSet β] [InfSet γ] [InfSet δ]

instance : sInfHomClass (sInfHom α β) α β
    where
  coe := sInfHom.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_sInf := sInfHom.map_Inf'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (sInfHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

#print sInfHom.toFun_eq_coe /-
@[simp]
theorem toFun_eq_coe {f : sInfHom α β} : f.toFun = (f : α → β) :=
  rfl
#align Inf_hom.to_fun_eq_coe sInfHom.toFun_eq_coe
-/

#print sInfHom.ext /-
@[ext]
theorem ext {f g : sInfHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align Inf_hom.ext sInfHom.ext
-/

#print sInfHom.copy /-
/-- Copy of a `Inf_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : sInfHom α β) (f' : α → β) (h : f' = f) : sInfHom α β
    where
  toFun := f'
  map_Inf' := h.symm ▸ f.map_Inf'
#align Inf_hom.copy sInfHom.copy
-/

#print sInfHom.coe_copy /-
@[simp]
theorem coe_copy (f : sInfHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align Inf_hom.coe_copy sInfHom.coe_copy
-/

#print sInfHom.copy_eq /-
theorem copy_eq (f : sInfHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align Inf_hom.copy_eq sInfHom.copy_eq
-/

variable (α)

#print sInfHom.id /-
/-- `id` as an `Inf_hom`. -/
protected def id : sInfHom α α :=
  ⟨id, fun s => by rw [id, Set.image_id]⟩
#align Inf_hom.id sInfHom.id
-/

instance : Inhabited (sInfHom α α) :=
  ⟨sInfHom.id α⟩

#print sInfHom.coe_id /-
@[simp]
theorem coe_id : ⇑(sInfHom.id α) = id :=
  rfl
#align Inf_hom.coe_id sInfHom.coe_id
-/

variable {α}

#print sInfHom.id_apply /-
@[simp]
theorem id_apply (a : α) : sInfHom.id α a = a :=
  rfl
#align Inf_hom.id_apply sInfHom.id_apply
-/

#print sInfHom.comp /-
/-- Composition of `Inf_hom`s as a `Inf_hom`. -/
def comp (f : sInfHom β γ) (g : sInfHom α β) : sInfHom α γ
    where
  toFun := f ∘ g
  map_Inf' s := by rw [comp_apply, map_Inf, map_Inf, Set.image_image]
#align Inf_hom.comp sInfHom.comp
-/

#print sInfHom.coe_comp /-
@[simp]
theorem coe_comp (f : sInfHom β γ) (g : sInfHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align Inf_hom.coe_comp sInfHom.coe_comp
-/

#print sInfHom.comp_apply /-
@[simp]
theorem comp_apply (f : sInfHom β γ) (g : sInfHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align Inf_hom.comp_apply sInfHom.comp_apply
-/

#print sInfHom.comp_assoc /-
@[simp]
theorem comp_assoc (f : sInfHom γ δ) (g : sInfHom β γ) (h : sInfHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align Inf_hom.comp_assoc sInfHom.comp_assoc
-/

#print sInfHom.comp_id /-
@[simp]
theorem comp_id (f : sInfHom α β) : f.comp (sInfHom.id α) = f :=
  ext fun a => rfl
#align Inf_hom.comp_id sInfHom.comp_id
-/

#print sInfHom.id_comp /-
@[simp]
theorem id_comp (f : sInfHom α β) : (sInfHom.id β).comp f = f :=
  ext fun a => rfl
#align Inf_hom.id_comp sInfHom.id_comp
-/

#print sInfHom.cancel_right /-
theorem cancel_right {g₁ g₂ : sInfHom β γ} {f : sInfHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align Inf_hom.cancel_right sInfHom.cancel_right
-/

#print sInfHom.cancel_left /-
theorem cancel_left {g : sInfHom β γ} {f₁ f₂ : sInfHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align Inf_hom.cancel_left sInfHom.cancel_left
-/

end InfSet

variable [CompleteLattice β]

instance : PartialOrder (sInfHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

instance : Top (sInfHom α β) :=
  ⟨⟨fun _ => ⊤, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, sInf_empty]
      · rw [hs.image_const, sInf_singleton]⟩⟩

instance : OrderTop (sInfHom α β) :=
  ⟨⊤, fun f a => le_top⟩

#print sInfHom.coe_top /-
@[simp]
theorem coe_top : ⇑(⊤ : sInfHom α β) = ⊤ :=
  rfl
#align Inf_hom.coe_top sInfHom.coe_top
-/

#print sInfHom.top_apply /-
@[simp]
theorem top_apply (a : α) : (⊤ : sInfHom α β) a = ⊤ :=
  rfl
#align Inf_hom.top_apply sInfHom.top_apply
-/

end sInfHom

/-! ### Frame homomorphisms -/


namespace FrameHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]

instance : FrameHomClass (FrameHom α β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr
  map_sSup f := f.map_Sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (FrameHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

#print FrameHom.toLatticeHom /-
/-- Reinterpret a `frame_hom` as a `lattice_hom`. -/
def toLatticeHom (f : FrameHom α β) : LatticeHom α β :=
  f
#align frame_hom.to_lattice_hom FrameHom.toLatticeHom
-/

#print FrameHom.toFun_eq_coe /-
@[simp]
theorem toFun_eq_coe {f : FrameHom α β} : f.toFun = (f : α → β) :=
  rfl
#align frame_hom.to_fun_eq_coe FrameHom.toFun_eq_coe
-/

#print FrameHom.ext /-
@[ext]
theorem ext {f g : FrameHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align frame_hom.ext FrameHom.ext
-/

#print FrameHom.copy /-
/-- Copy of a `frame_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : FrameHom α β) (f' : α → β) (h : f' = f) : FrameHom α β :=
  { (f : sSupHom α β).copy f' h with toInfTopHom := f.toInfTopHom.copy f' h }
#align frame_hom.copy FrameHom.copy
-/

#print FrameHom.coe_copy /-
@[simp]
theorem coe_copy (f : FrameHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align frame_hom.coe_copy FrameHom.coe_copy
-/

#print FrameHom.copy_eq /-
theorem copy_eq (f : FrameHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align frame_hom.copy_eq FrameHom.copy_eq
-/

variable (α)

#print FrameHom.id /-
/-- `id` as a `frame_hom`. -/
protected def id : FrameHom α α :=
  { sSupHom.id α with toInfTopHom := InfTopHom.id α }
#align frame_hom.id FrameHom.id
-/

instance : Inhabited (FrameHom α α) :=
  ⟨FrameHom.id α⟩

#print FrameHom.coe_id /-
@[simp]
theorem coe_id : ⇑(FrameHom.id α) = id :=
  rfl
#align frame_hom.coe_id FrameHom.coe_id
-/

variable {α}

#print FrameHom.id_apply /-
@[simp]
theorem id_apply (a : α) : FrameHom.id α a = a :=
  rfl
#align frame_hom.id_apply FrameHom.id_apply
-/

#print FrameHom.comp /-
/-- Composition of `frame_hom`s as a `frame_hom`. -/
def comp (f : FrameHom β γ) (g : FrameHom α β) : FrameHom α γ :=
  { (f : sSupHom β γ).comp (g : sSupHom α β) with toInfTopHom := f.toInfTopHom.comp g.toInfTopHom }
#align frame_hom.comp FrameHom.comp
-/

#print FrameHom.coe_comp /-
@[simp]
theorem coe_comp (f : FrameHom β γ) (g : FrameHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align frame_hom.coe_comp FrameHom.coe_comp
-/

#print FrameHom.comp_apply /-
@[simp]
theorem comp_apply (f : FrameHom β γ) (g : FrameHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align frame_hom.comp_apply FrameHom.comp_apply
-/

#print FrameHom.comp_assoc /-
@[simp]
theorem comp_assoc (f : FrameHom γ δ) (g : FrameHom β γ) (h : FrameHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align frame_hom.comp_assoc FrameHom.comp_assoc
-/

#print FrameHom.comp_id /-
@[simp]
theorem comp_id (f : FrameHom α β) : f.comp (FrameHom.id α) = f :=
  ext fun a => rfl
#align frame_hom.comp_id FrameHom.comp_id
-/

#print FrameHom.id_comp /-
@[simp]
theorem id_comp (f : FrameHom α β) : (FrameHom.id β).comp f = f :=
  ext fun a => rfl
#align frame_hom.id_comp FrameHom.id_comp
-/

#print FrameHom.cancel_right /-
theorem cancel_right {g₁ g₂ : FrameHom β γ} {f : FrameHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align frame_hom.cancel_right FrameHom.cancel_right
-/

#print FrameHom.cancel_left /-
theorem cancel_left {g : FrameHom β γ} {f₁ f₂ : FrameHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align frame_hom.cancel_left FrameHom.cancel_left
-/

instance : PartialOrder (FrameHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

end FrameHom

/-! ### Complete lattice homomorphisms -/


namespace CompleteLatticeHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]

instance : CompleteLatticeHomClass (CompleteLatticeHom α β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f <;> obtain ⟨⟨_, _⟩, _⟩ := g <;> congr
  map_sSup f := f.map_Sup'
  map_sInf f := f.map_Inf'

#print CompleteLatticeHom.tosSupHom /-
/-- Reinterpret a `complete_lattice_hom` as a `Sup_hom`. -/
def tosSupHom (f : CompleteLatticeHom α β) : sSupHom α β :=
  f
#align complete_lattice_hom.to_Sup_hom CompleteLatticeHom.tosSupHom
-/

#print CompleteLatticeHom.toBoundedLatticeHom /-
/-- Reinterpret a `complete_lattice_hom` as a `bounded_lattice_hom`. -/
def toBoundedLatticeHom (f : CompleteLatticeHom α β) : BoundedLatticeHom α β :=
  f
#align complete_lattice_hom.to_bounded_lattice_hom CompleteLatticeHom.toBoundedLatticeHom
-/

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (CompleteLatticeHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

#print CompleteLatticeHom.toFun_eq_coe /-
@[simp]
theorem toFun_eq_coe {f : CompleteLatticeHom α β} : f.toFun = (f : α → β) :=
  rfl
#align complete_lattice_hom.to_fun_eq_coe CompleteLatticeHom.toFun_eq_coe
-/

#print CompleteLatticeHom.ext /-
@[ext]
theorem ext {f g : CompleteLatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align complete_lattice_hom.ext CompleteLatticeHom.ext
-/

#print CompleteLatticeHom.copy /-
/-- Copy of a `complete_lattice_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) :
    CompleteLatticeHom α β :=
  { f.tosSupHom.copy f' h with toInfHom := f.toInfHom.copy f' h }
#align complete_lattice_hom.copy CompleteLatticeHom.copy
-/

#print CompleteLatticeHom.coe_copy /-
@[simp]
theorem coe_copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align complete_lattice_hom.coe_copy CompleteLatticeHom.coe_copy
-/

#print CompleteLatticeHom.copy_eq /-
theorem copy_eq (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align complete_lattice_hom.copy_eq CompleteLatticeHom.copy_eq
-/

variable (α)

#print CompleteLatticeHom.id /-
/-- `id` as a `complete_lattice_hom`. -/
protected def id : CompleteLatticeHom α α :=
  { sSupHom.id α, sInfHom.id α with toFun := id }
#align complete_lattice_hom.id CompleteLatticeHom.id
-/

instance : Inhabited (CompleteLatticeHom α α) :=
  ⟨CompleteLatticeHom.id α⟩

#print CompleteLatticeHom.coe_id /-
@[simp]
theorem coe_id : ⇑(CompleteLatticeHom.id α) = id :=
  rfl
#align complete_lattice_hom.coe_id CompleteLatticeHom.coe_id
-/

variable {α}

#print CompleteLatticeHom.id_apply /-
@[simp]
theorem id_apply (a : α) : CompleteLatticeHom.id α a = a :=
  rfl
#align complete_lattice_hom.id_apply CompleteLatticeHom.id_apply
-/

#print CompleteLatticeHom.comp /-
/-- Composition of `complete_lattice_hom`s as a `complete_lattice_hom`. -/
def comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : CompleteLatticeHom α γ :=
  { f.tosSupHom.comp g.tosSupHom with toInfHom := f.toInfHom.comp g.toInfHom }
#align complete_lattice_hom.comp CompleteLatticeHom.comp
-/

#print CompleteLatticeHom.coe_comp /-
@[simp]
theorem coe_comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align complete_lattice_hom.coe_comp CompleteLatticeHom.coe_comp
-/

#print CompleteLatticeHom.comp_apply /-
@[simp]
theorem comp_apply (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) (a : α) :
    (f.comp g) a = f (g a) :=
  rfl
#align complete_lattice_hom.comp_apply CompleteLatticeHom.comp_apply
-/

#print CompleteLatticeHom.comp_assoc /-
@[simp]
theorem comp_assoc (f : CompleteLatticeHom γ δ) (g : CompleteLatticeHom β γ)
    (h : CompleteLatticeHom α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align complete_lattice_hom.comp_assoc CompleteLatticeHom.comp_assoc
-/

#print CompleteLatticeHom.comp_id /-
@[simp]
theorem comp_id (f : CompleteLatticeHom α β) : f.comp (CompleteLatticeHom.id α) = f :=
  ext fun a => rfl
#align complete_lattice_hom.comp_id CompleteLatticeHom.comp_id
-/

#print CompleteLatticeHom.id_comp /-
@[simp]
theorem id_comp (f : CompleteLatticeHom α β) : (CompleteLatticeHom.id β).comp f = f :=
  ext fun a => rfl
#align complete_lattice_hom.id_comp CompleteLatticeHom.id_comp
-/

#print CompleteLatticeHom.cancel_right /-
theorem cancel_right {g₁ g₂ : CompleteLatticeHom β γ} {f : CompleteLatticeHom α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align complete_lattice_hom.cancel_right CompleteLatticeHom.cancel_right
-/

#print CompleteLatticeHom.cancel_left /-
theorem cancel_left {g : CompleteLatticeHom β γ} {f₁ f₂ : CompleteLatticeHom α β}
    (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align complete_lattice_hom.cancel_left CompleteLatticeHom.cancel_left
-/

end CompleteLatticeHom

/-! ### Dual homs -/


namespace sSupHom

variable [SupSet α] [SupSet β] [SupSet γ]

#print sSupHom.dual /-
/-- Reinterpret a `⨆`-homomorphism as an `⨅`-homomorphism between the dual orders. -/
@[simps]
protected def dual : sSupHom α β ≃ sInfHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨toDual ∘ f ∘ ofDual, f.map_Sup'⟩
  invFun f := ⟨ofDual ∘ f ∘ toDual, f.map_Inf'⟩
  left_inv f := sSupHom.ext fun a => rfl
  right_inv f := sInfHom.ext fun a => rfl
#align Sup_hom.dual sSupHom.dual
-/

#print sSupHom.dual_id /-
@[simp]
theorem dual_id : (sSupHom.id α).dual = sInfHom.id _ :=
  rfl
#align Sup_hom.dual_id sSupHom.dual_id
-/

#print sSupHom.dual_comp /-
@[simp]
theorem dual_comp (g : sSupHom β γ) (f : sSupHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl
#align Sup_hom.dual_comp sSupHom.dual_comp
-/

#print sSupHom.symm_dual_id /-
@[simp]
theorem symm_dual_id : sSupHom.dual.symm (sInfHom.id _) = sSupHom.id α :=
  rfl
#align Sup_hom.symm_dual_id sSupHom.symm_dual_id
-/

#print sSupHom.symm_dual_comp /-
@[simp]
theorem symm_dual_comp (g : sInfHom βᵒᵈ γᵒᵈ) (f : sInfHom αᵒᵈ βᵒᵈ) :
    sSupHom.dual.symm (g.comp f) = (sSupHom.dual.symm g).comp (sSupHom.dual.symm f) :=
  rfl
#align Sup_hom.symm_dual_comp sSupHom.symm_dual_comp
-/

end sSupHom

namespace sInfHom

variable [InfSet α] [InfSet β] [InfSet γ]

#print sInfHom.dual /-
/-- Reinterpret an `⨅`-homomorphism as a `⨆`-homomorphism between the dual orders. -/
@[simps]
protected def dual : sInfHom α β ≃ sSupHom αᵒᵈ βᵒᵈ
    where
  toFun f :=
    { toFun := toDual ∘ f ∘ ofDual
      map_Sup' := fun _ => congr_arg toDual (map_sInf f _) }
  invFun f :=
    { toFun := ofDual ∘ f ∘ toDual
      map_Inf' := fun _ => congr_arg ofDual (map_sSup f _) }
  left_inv f := sInfHom.ext fun a => rfl
  right_inv f := sSupHom.ext fun a => rfl
#align Inf_hom.dual sInfHom.dual
-/

#print sInfHom.dual_id /-
@[simp]
theorem dual_id : (sInfHom.id α).dual = sSupHom.id _ :=
  rfl
#align Inf_hom.dual_id sInfHom.dual_id
-/

#print sInfHom.dual_comp /-
@[simp]
theorem dual_comp (g : sInfHom β γ) (f : sInfHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl
#align Inf_hom.dual_comp sInfHom.dual_comp
-/

#print sInfHom.symm_dual_id /-
@[simp]
theorem symm_dual_id : sInfHom.dual.symm (sSupHom.id _) = sInfHom.id α :=
  rfl
#align Inf_hom.symm_dual_id sInfHom.symm_dual_id
-/

#print sInfHom.symm_dual_comp /-
@[simp]
theorem symm_dual_comp (g : sSupHom βᵒᵈ γᵒᵈ) (f : sSupHom αᵒᵈ βᵒᵈ) :
    sInfHom.dual.symm (g.comp f) = (sInfHom.dual.symm g).comp (sInfHom.dual.symm f) :=
  rfl
#align Inf_hom.symm_dual_comp sInfHom.symm_dual_comp
-/

end sInfHom

namespace CompleteLatticeHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ]

#print CompleteLatticeHom.dual /-
/-- Reinterpret a complete lattice homomorphism as a complete lattice homomorphism between the dual
lattices. -/
@[simps]
protected def dual : CompleteLatticeHom α β ≃ CompleteLatticeHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨f.tosSupHom.dual, f.map_Inf'⟩
  invFun f := ⟨f.tosSupHom.dual, f.map_Inf'⟩
  left_inv f := ext fun a => rfl
  right_inv f := ext fun a => rfl
#align complete_lattice_hom.dual CompleteLatticeHom.dual
-/

#print CompleteLatticeHom.dual_id /-
@[simp]
theorem dual_id : (CompleteLatticeHom.id α).dual = CompleteLatticeHom.id _ :=
  rfl
#align complete_lattice_hom.dual_id CompleteLatticeHom.dual_id
-/

#print CompleteLatticeHom.dual_comp /-
@[simp]
theorem dual_comp (g : CompleteLatticeHom β γ) (f : CompleteLatticeHom α β) :
    (g.comp f).dual = g.dual.comp f.dual :=
  rfl
#align complete_lattice_hom.dual_comp CompleteLatticeHom.dual_comp
-/

#print CompleteLatticeHom.symm_dual_id /-
@[simp]
theorem symm_dual_id :
    CompleteLatticeHom.dual.symm (CompleteLatticeHom.id _) = CompleteLatticeHom.id α :=
  rfl
#align complete_lattice_hom.symm_dual_id CompleteLatticeHom.symm_dual_id
-/

#print CompleteLatticeHom.symm_dual_comp /-
@[simp]
theorem symm_dual_comp (g : CompleteLatticeHom βᵒᵈ γᵒᵈ) (f : CompleteLatticeHom αᵒᵈ βᵒᵈ) :
    CompleteLatticeHom.dual.symm (g.comp f) =
      (CompleteLatticeHom.dual.symm g).comp (CompleteLatticeHom.dual.symm f) :=
  rfl
#align complete_lattice_hom.symm_dual_comp CompleteLatticeHom.symm_dual_comp
-/

end CompleteLatticeHom

/-! ### Concrete homs -/


namespace CompleteLatticeHom

#print CompleteLatticeHom.setPreimage /-
/-- `set.preimage` as a complete lattice homomorphism.

See also `Sup_hom.set_image`. -/
def setPreimage (f : α → β) : CompleteLatticeHom (Set β) (Set α)
    where
  toFun := preimage f
  map_Sup' s := preimage_sUnion.trans <| by simp only [Set.sSup_eq_sUnion, Set.sUnion_image]
  map_Inf' s := preimage_sInter.trans <| by simp only [Set.sInf_eq_sInter, Set.sInter_image]
#align complete_lattice_hom.set_preimage CompleteLatticeHom.setPreimage
-/

#print CompleteLatticeHom.coe_setPreimage /-
@[simp]
theorem coe_setPreimage (f : α → β) : ⇑(setPreimage f) = preimage f :=
  rfl
#align complete_lattice_hom.coe_set_preimage CompleteLatticeHom.coe_setPreimage
-/

#print CompleteLatticeHom.setPreimage_apply /-
@[simp]
theorem setPreimage_apply (f : α → β) (s : Set β) : setPreimage f s = s.Preimage f :=
  rfl
#align complete_lattice_hom.set_preimage_apply CompleteLatticeHom.setPreimage_apply
-/

#print CompleteLatticeHom.setPreimage_id /-
@[simp]
theorem setPreimage_id : setPreimage (id : α → α) = CompleteLatticeHom.id _ :=
  rfl
#align complete_lattice_hom.set_preimage_id CompleteLatticeHom.setPreimage_id
-/

#print CompleteLatticeHom.setPreimage_comp /-
-- This lemma can't be `simp` because `g ∘ f` matches anything (`id ∘ f = f` synctatically)
theorem setPreimage_comp (g : β → γ) (f : α → β) :
    setPreimage (g ∘ f) = (setPreimage f).comp (setPreimage g) :=
  rfl
#align complete_lattice_hom.set_preimage_comp CompleteLatticeHom.setPreimage_comp
-/

end CompleteLatticeHom

#print Set.image_sSup /-
theorem Set.image_sSup {f : α → β} (s : Set (Set α)) : f '' sSup s = sSup (image f '' s) :=
  by
  ext b
  simp only [Sup_eq_sUnion, mem_image, mem_sUnion, exists_prop, sUnion_image, mem_Union]
  constructor
  · rintro ⟨a, ⟨t, ht₁, ht₂⟩, rfl⟩; exact ⟨t, ht₁, a, ht₂, rfl⟩
  · rintro ⟨t, ht₁, a, ht₂, rfl⟩; exact ⟨a, ⟨t, ht₁, ht₂⟩, rfl⟩
#align set.image_Sup Set.image_sSup
-/

#print sSupHom.setImage /-
/-- Using `set.image`, a function between types yields a `Sup_hom` between their lattices of
subsets.

See also `complete_lattice_hom.set_preimage`. -/
@[simps]
def sSupHom.setImage (f : α → β) : sSupHom (Set α) (Set β)
    where
  toFun := image f
  map_Sup' := Set.image_sSup
#align Sup_hom.set_image sSupHom.setImage
-/

#print Equiv.toOrderIsoSet /-
/-- An equivalence of types yields an order isomorphism between their lattices of subsets. -/
@[simps]
def Equiv.toOrderIsoSet (e : α ≃ β) : Set α ≃o Set β
    where
  toFun := image e
  invFun := image e.symm
  left_inv s := by simp only [← image_comp, Equiv.symm_comp_self, id.def, image_id']
  right_inv s := by simp only [← image_comp, Equiv.self_comp_symm, id.def, image_id']
  map_rel_iff' s t :=
    ⟨fun h => by simpa using @monotone_image _ _ e.symm _ _ h, fun h => monotone_image h⟩
#align equiv.to_order_iso_set Equiv.toOrderIsoSet
-/

variable [CompleteLattice α] (x : α × α)

#print supsSupHom /-
/-- The map `(a, b) ↦ a ⊔ b` as a `Sup_hom`. -/
def supsSupHom : sSupHom (α × α) α where
  toFun x := x.1 ⊔ x.2
  map_Sup' s := by simp_rw [Prod.fst_sSup, Prod.snd_sSup, sSup_image, iSup_sup_eq]
#align sup_Sup_hom supsSupHom
-/

#print infsInfHom /-
/-- The map `(a, b) ↦ a ⊓ b` as an `Inf_hom`. -/
def infsInfHom : sInfHom (α × α) α where
  toFun x := x.1 ⊓ x.2
  map_Inf' s := by simp_rw [Prod.fst_sInf, Prod.snd_sInf, sInf_image, iInf_inf_eq]
#align inf_Inf_hom infsInfHom
-/

#print supsSupHom_apply /-
@[simp, norm_cast]
theorem supsSupHom_apply : supsSupHom x = x.1 ⊔ x.2 :=
  rfl
#align sup_Sup_hom_apply supsSupHom_apply
-/

#print infsInfHom_apply /-
@[simp, norm_cast]
theorem infsInfHom_apply : infsInfHom x = x.1 ⊓ x.2 :=
  rfl
#align inf_Inf_hom_apply infsInfHom_apply
-/

