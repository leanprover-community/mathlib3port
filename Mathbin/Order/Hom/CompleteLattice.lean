/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.CompleteLattice
import Mathbin.Order.Hom.Lattice

/-!
# Complete lattice homomorphisms

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

/-- The type of frame homomorphisms from `α` to `β`. They preserve finite meets and arbitrary joins.
-/
structure FrameHom (α β : Type _) [CompleteLattice α] [CompleteLattice β] extends InfTopHom α β where
  map_Sup' (s : Set α) : to_fun (sup s) = sup (to_fun '' s)

/-- The type of complete lattice homomorphisms from `α` to `β`. -/
structure CompleteLatticeHom (α β : Type _) [CompleteLattice α] [CompleteLattice β] extends InfHom α β where
  map_Sup' (s : Set α) : to_fun (sup s) = sup (to_fun '' s)

section

/-- `frame_hom_class F α β` states that `F` is a type of frame morphisms. They preserve `⊓` and `⨆`.

You should extend this class when you extend `frame_hom`. -/
class FrameHomClass (F : Type _) (α β : outParam <| Type _) [CompleteLattice α] [CompleteLattice β] extends
  InfTopHomClass F α β where
  map_Sup (f : F) (s : Set α) : f (sup s) = sup (f '' s)

/-- `complete_lattice_hom_class F α β` states that `F` is a type of complete lattice morphisms.

You should extend this class when you extend `complete_lattice_hom`. -/
class CompleteLatticeHomClass (F : Type _) (α β : outParam <| Type _) [CompleteLattice α] [CompleteLattice β] extends
  InfHomClass F α β where
  map_Sup (f : F) (s : Set α) : f (sup s) = sup (f '' s)

end

export SupHomClass (map_Sup)

export InfHomClass (map_Inf)

attribute [simp] map_Sup map_Inf

theorem map_supr [HasSup α] [HasSup β] [SupHomClass F α β] (f : F) (g : ι → α) : f (⨆ i, g i) = ⨆ i, f (g i) := by
  rw [supr, supr, map_Sup, Set.range_comp]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem map_supr₂ [HasSup α] [HasSup β] [SupHomClass F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨆ (i) (j), g i j) = ⨆ (i) (j), f (g i j) := by simp_rw [map_supr]

theorem map_infi [HasInf α] [HasInf β] [InfHomClass F α β] (f : F) (g : ι → α) : f (⨅ i, g i) = ⨅ i, f (g i) := by
  rw [infi, infi, map_Inf, Set.range_comp]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem map_infi₂ [HasInf α] [HasInf β] [InfHomClass F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨅ (i) (j), g i j) = ⨅ (i) (j), f (g i j) := by simp_rw [map_infi]

-- See note [lower instance priority]
instance (priority := 100) SupHomClass.toSupBotHomClass [CompleteLattice α] [CompleteLattice β] [SupHomClass F α β] :
    SupBotHomClass F α β :=
  { ‹SupHomClass F α β› with map_sup := fun f a b => by rw [← Sup_pair, map_Sup, Set.image_pair, Sup_pair],
    map_bot := fun f => by rw [← Sup_empty, map_Sup, Set.image_empty, Sup_empty] }

-- See note [lower instance priority]
instance (priority := 100) InfHomClass.toInfTopHomClass [CompleteLattice α] [CompleteLattice β] [InfHomClass F α β] :
    InfTopHomClass F α β :=
  { ‹InfHomClass F α β› with map_inf := fun f a b => by rw [← Inf_pair, map_Inf, Set.image_pair, Inf_pair],
    map_top := fun f => by rw [← Inf_empty, map_Inf, Set.image_empty, Inf_empty] }

-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.toSupHomClass [CompleteLattice α] [CompleteLattice β] [FrameHomClass F α β] :
    SupHomClass F α β :=
  { ‹FrameHomClass F α β› with }

-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.toBoundedLatticeHomClass [CompleteLattice α] [CompleteLattice β]
    [FrameHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹FrameHomClass F α β›, SupHomClass.toSupBotHomClass with }

-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toFrameHomClass [CompleteLattice α] [CompleteLattice β]
    [CompleteLatticeHomClass F α β] : FrameHomClass F α β :=
  { ‹CompleteLatticeHomClass F α β›, InfHomClass.toInfTopHomClass with }

-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toBoundedLatticeHomClass [CompleteLattice α] [CompleteLattice β]
    [CompleteLatticeHomClass F α β] : BoundedLatticeHomClass F α β :=
  { SupHomClass.toSupBotHomClass, InfHomClass.toInfTopHomClass with }

-- See note [lower instance priority]
-- See note [lower instance priority]
-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toCompleteLatticeHomClass [CompleteLattice α] [CompleteLattice β]
    [OrderIsoClass F α β] : CompleteLatticeHomClass F α β :=
  { OrderIsoClass.toSupHomClass, OrderIsoClass.toLatticeHomClass, show InfHomClass F α β from inferInstance with }

instance [HasSup α] [HasSup β] [SupHomClass F α β] : CoeT F (SupHom α β) :=
  ⟨fun f => ⟨f, map_Sup f⟩⟩

instance [HasInf α] [HasInf β] [InfHomClass F α β] : CoeT F (InfHom α β) :=
  ⟨fun f => ⟨f, map_Inf f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [FrameHomClass F α β] : CoeT F (FrameHom α β) :=
  ⟨fun f => ⟨f, map_Sup f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [CompleteLatticeHomClass F α β] : CoeT F (CompleteLatticeHom α β) :=
  ⟨fun f => ⟨f, map_Sup f⟩⟩

/-! ### Supremum homomorphisms -/


namespace SupHom

variable [HasSup α]

section HasSup

variable [HasSup β] [HasSup γ] [HasSup δ]

instance : SupHomClass (SupHom α β) α β where
  coe := SupHom.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_Sup := SupHom.map_Sup'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (SupHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

variable (α)

instance : Inhabited (SupHom α α) :=
  ⟨SupHom.id α⟩

variable {α}

end HasSup

variable [CompleteLattice β]

instance : PartialOrder (SupHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

instance : HasBot (SupHom α β) :=
  ⟨⟨fun _ => ⊥, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, Sup_empty]
        
      · rw [hs.image_const, Sup_singleton]
        ⟩⟩

instance : OrderBot (SupHom α β) :=
  ⟨⊥, fun f a => bot_le⟩

end SupHom

/-! ### Infimum homomorphisms -/


namespace InfHom

variable [HasInf α]

section HasInf

variable [HasInf β] [HasInf γ] [HasInf δ]

instance : InfHomClass (InfHom α β) α β where
  coe := InfHom.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_Inf := InfHom.map_Inf'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (InfHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

variable (α)

instance : Inhabited (InfHom α α) :=
  ⟨InfHom.id α⟩

variable {α}

end HasInf

variable [CompleteLattice β]

instance : PartialOrder (InfHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

instance : HasTop (InfHom α β) :=
  ⟨⟨fun _ => ⊤, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, Inf_empty]
        
      · rw [hs.image_const, Inf_singleton]
        ⟩⟩

instance : OrderTop (InfHom α β) :=
  ⟨⊤, fun f a => le_top⟩

end InfHom

/-! ### Frame homomorphisms -/


namespace FrameHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]

instance : FrameHomClass (FrameHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr
  map_Sup f := f.map_Sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (FrameHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

/-- Reinterpret a `frame_hom` as a `lattice_hom`. -/
def toLatticeHom (f : FrameHom α β) : LatticeHom α β :=
  f

@[simp]
theorem to_fun_eq_coe {f : FrameHom α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : FrameHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `frame_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : FrameHom α β) (f' : α → β) (h : f' = f) : FrameHom α β :=
  { (f : SupHom α β).copy f' h with toInfTopHom := f.toInfTopHom.copy f' h }

variable (α)

/-- `id` as a `frame_hom`. -/
protected def id : FrameHom α α :=
  { SupHom.id α with toInfTopHom := InfTopHom.id α }

instance : Inhabited (FrameHom α α) :=
  ⟨FrameHom.id α⟩

@[simp]
theorem coe_id : ⇑(FrameHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : FrameHom.id α a = a :=
  rfl

/-- Composition of `frame_hom`s as a `frame_hom`. -/
def comp (f : FrameHom β γ) (g : FrameHom α β) : FrameHom α γ :=
  { (f : SupHom β γ).comp (g : SupHom α β) with toInfTopHom := f.toInfTopHom.comp g.toInfTopHom }

@[simp]
theorem coe_comp (f : FrameHom β γ) (g : FrameHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : FrameHom β γ) (g : FrameHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : FrameHom γ δ) (g : FrameHom β γ) (h : FrameHom α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : FrameHom α β) : f.comp (FrameHom.id α) = f :=
  ext fun a => rfl

@[simp]
theorem id_comp (f : FrameHom α β) : (FrameHom.id β).comp f = f :=
  ext fun a => rfl

theorem cancel_right {g₁ g₂ : FrameHom β γ} {f : FrameHom α β} (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : FrameHom β γ} {f₁ f₂ : FrameHom α β} (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

instance : PartialOrder (FrameHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

end FrameHom

/-! ### Complete lattice homomorphisms -/


namespace CompleteLatticeHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]

instance : CompleteLatticeHomClass (CompleteLatticeHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f <;> obtain ⟨⟨_, _⟩, _⟩ := g <;> congr
  map_Sup f := f.map_Sup'
  map_Inf f := f.map_Inf'

/-- Reinterpret a `complete_lattice_hom` as a `Sup_hom`. -/
def toSupHom (f : CompleteLatticeHom α β) : SupHom α β :=
  f

/-- Reinterpret a `complete_lattice_hom` as a `bounded_lattice_hom`. -/
def toBoundedLatticeHom (f : CompleteLatticeHom α β) : BoundedLatticeHom α β :=
  f

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (CompleteLatticeHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {f : CompleteLatticeHom α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : CompleteLatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `complete_lattice_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) : CompleteLatticeHom α β :=
  { f.toSupHom.copy f' h with toInfHom := f.toInfHom.copy f' h }

variable (α)

/-- `id` as a `complete_lattice_hom`. -/
protected def id : CompleteLatticeHom α α :=
  { SupHom.id α, InfHom.id α with toFun := id }

instance : Inhabited (CompleteLatticeHom α α) :=
  ⟨CompleteLatticeHom.id α⟩

@[simp]
theorem coe_id : ⇑(CompleteLatticeHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : CompleteLatticeHom.id α a = a :=
  rfl

/-- Composition of `complete_lattice_hom`s as a `complete_lattice_hom`. -/
def comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : CompleteLatticeHom α γ :=
  { f.toSupHom.comp g.toSupHom with toInfHom := f.toInfHom.comp g.toInfHom }

@[simp]
theorem coe_comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : CompleteLatticeHom γ δ) (g : CompleteLatticeHom β γ) (h : CompleteLatticeHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : CompleteLatticeHom α β) : f.comp (CompleteLatticeHom.id α) = f :=
  ext fun a => rfl

@[simp]
theorem id_comp (f : CompleteLatticeHom α β) : (CompleteLatticeHom.id β).comp f = f :=
  ext fun a => rfl

theorem cancel_right {g₁ g₂ : CompleteLatticeHom β γ} {f : CompleteLatticeHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : CompleteLatticeHom β γ} {f₁ f₂ : CompleteLatticeHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end CompleteLatticeHom

/-! ### Dual homs -/


namespace SupHom

variable [HasSup α] [HasSup β] [HasSup γ]

/- warning: Sup_hom.dual_id clashes with sup_hom.dual_id -> SupHom.dual_id
warning: Sup_hom.dual_id -> SupHom.dual_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} [_inst_1 : HasSup.{u_2} α], Eq.{succ u_2} (InfHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_2} α _inst_1)) (coeFn.{(max 1 (succ u_2)) succ u_2} (Equiv.{succ u_2 succ u_2} (SupHom.{u_2 u_2} α α _inst_1 _inst_1) (InfHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_2} α _inst_1))) (fun (_x : Equiv.{succ u_2 succ u_2} (SupHom.{u_2 u_2} α α _inst_1 _inst_1) (InfHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_2} α _inst_1))) => (SupHom.{u_2 u_2} α α _inst_1 _inst_1) -> (InfHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_2} α _inst_1))) (Equiv.hasCoeToFun.{succ u_2 succ u_2} (SupHom.{u_2 u_2} α α _inst_1 _inst_1) (InfHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_2} α _inst_1))) (SupHom.dual.{u_2 u_2} α α _inst_1 _inst_1) (SupHom.id.{u_2} α _inst_1)) (InfHom.id.{u_2} (OrderDual.{u_2} α) (OrderDual.hasInf.{u_2} α _inst_1))
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align Sup_hom.dual_id SupHom.dual_idₓ'. -/
@[simp]
theorem dual_id : (SupHom.id α).dual = InfHom.id _ :=
  rfl

/- warning: Sup_hom.dual_comp clashes with sup_hom.dual_comp -> SupHom.dual_comp
warning: Sup_hom.dual_comp -> SupHom.dual_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {β : Type.{u_3}} {γ : Type.{u_4}} [_inst_1 : HasSup.{u_2} α] [_inst_2 : HasSup.{u_3} β] [_inst_3 : HasSup.{u_4} γ] (g : SupHom.{u_3 u_4} β γ _inst_2 _inst_3) (f : SupHom.{u_2 u_3} α β _inst_1 _inst_2), Eq.{(max (succ u_2) (succ u_4))} (InfHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_4} γ _inst_3)) (coeFn.{(max 1 (succ u_2) (succ u_4)) (max (succ u_2) (succ u_4))} (Equiv.{(max (succ u_2) (succ u_4)) (max (succ u_2) (succ u_4))} (SupHom.{u_2 u_4} α γ _inst_1 _inst_3) (InfHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_4} γ _inst_3))) (fun (_x : Equiv.{(max (succ u_2) (succ u_4)) (max (succ u_2) (succ u_4))} (SupHom.{u_2 u_4} α γ _inst_1 _inst_3) (InfHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_4} γ _inst_3))) => (SupHom.{u_2 u_4} α γ _inst_1 _inst_3) -> (InfHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_4} γ _inst_3))) (Equiv.hasCoeToFun.{(max (succ u_2) (succ u_4)) (max (succ u_2) (succ u_4))} (SupHom.{u_2 u_4} α γ _inst_1 _inst_3) (InfHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_4} γ _inst_3))) (SupHom.dual.{u_2 u_4} α γ _inst_1 _inst_3) (SupHom.comp.{u_2 u_3 u_4} α β γ _inst_1 _inst_2 _inst_3 g f)) (InfHom.comp.{u_2 u_3 u_4} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_3} β _inst_2) (OrderDual.hasInf.{u_4} γ _inst_3) (coeFn.{(max 1 (succ u_3) (succ u_4)) (max (succ u_3) (succ u_4))} (Equiv.{(max (succ u_3) (succ u_4)) (max (succ u_3) (succ u_4))} (SupHom.{u_3 u_4} β γ _inst_2 _inst_3) (InfHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_3} β _inst_2) (OrderDual.hasInf.{u_4} γ _inst_3))) (fun (_x : Equiv.{(max (succ u_3) (succ u_4)) (max (succ u_3) (succ u_4))} (SupHom.{u_3 u_4} β γ _inst_2 _inst_3) (InfHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_3} β _inst_2) (OrderDual.hasInf.{u_4} γ _inst_3))) => (SupHom.{u_3 u_4} β γ _inst_2 _inst_3) -> (InfHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_3} β _inst_2) (OrderDual.hasInf.{u_4} γ _inst_3))) (Equiv.hasCoeToFun.{(max (succ u_3) (succ u_4)) (max (succ u_3) (succ u_4))} (SupHom.{u_3 u_4} β γ _inst_2 _inst_3) (InfHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_3} β _inst_2) (OrderDual.hasInf.{u_4} γ _inst_3))) (SupHom.dual.{u_3 u_4} β γ _inst_2 _inst_3) g) (coeFn.{(max 1 (succ u_2) (succ u_3)) (max (succ u_2) (succ u_3))} (Equiv.{(max (succ u_2) (succ u_3)) (max (succ u_2) (succ u_3))} (SupHom.{u_2 u_3} α β _inst_1 _inst_2) (InfHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_3} β _inst_2))) (fun (_x : Equiv.{(max (succ u_2) (succ u_3)) (max (succ u_2) (succ u_3))} (SupHom.{u_2 u_3} α β _inst_1 _inst_2) (InfHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_3} β _inst_2))) => (SupHom.{u_2 u_3} α β _inst_1 _inst_2) -> (InfHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_3} β _inst_2))) (Equiv.hasCoeToFun.{(max (succ u_2) (succ u_3)) (max (succ u_2) (succ u_3))} (SupHom.{u_2 u_3} α β _inst_1 _inst_2) (InfHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_3} β _inst_2))) (SupHom.dual.{u_2 u_3} α β _inst_1 _inst_2) f))
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align Sup_hom.dual_comp SupHom.dual_compₓ'. -/
@[simp]
theorem dual_comp (g : SupHom β γ) (f : SupHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl

/- warning: Sup_hom.symm_dual_id clashes with sup_hom.symm_dual_id -> SupHom.symm_dual_id
warning: Sup_hom.symm_dual_id -> SupHom.symm_dual_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} [_inst_1 : HasSup.{u_2} α], Eq.{succ u_2} (SupHom.{u_2 u_2} α α _inst_1 _inst_1) (coeFn.{(max 1 (succ u_2)) succ u_2} (Equiv.{succ u_2 succ u_2} (InfHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_2} α _inst_1)) (SupHom.{u_2 u_2} α α _inst_1 _inst_1)) (fun (_x : Equiv.{succ u_2 succ u_2} (InfHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_2} α _inst_1)) (SupHom.{u_2 u_2} α α _inst_1 _inst_1)) => (InfHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_2} α _inst_1)) -> (SupHom.{u_2 u_2} α α _inst_1 _inst_1)) (Equiv.hasCoeToFun.{succ u_2 succ u_2} (InfHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_2} α _inst_1)) (SupHom.{u_2 u_2} α α _inst_1 _inst_1)) (Equiv.symm.{succ u_2 succ u_2} (SupHom.{u_2 u_2} α α _inst_1 _inst_1) (InfHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_2} α _inst_1)) (SupHom.dual.{u_2 u_2} α α _inst_1 _inst_1)) (InfHom.id.{u_2} (OrderDual.{u_2} α) (OrderDual.hasInf.{u_2} α _inst_1))) (SupHom.id.{u_2} α _inst_1)
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align Sup_hom.symm_dual_id SupHom.symm_dual_idₓ'. -/
@[simp]
theorem symm_dual_id : SupHom.dual.symm (InfHom.id _) = SupHom.id α :=
  rfl

/- warning: Sup_hom.symm_dual_comp clashes with sup_hom.symm_dual_comp -> SupHom.symm_dual_comp
warning: Sup_hom.symm_dual_comp -> SupHom.symm_dual_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {β : Type.{u_3}} {γ : Type.{u_4}} [_inst_1 : HasSup.{u_2} α] [_inst_2 : HasSup.{u_3} β] [_inst_3 : HasSup.{u_4} γ] (g : InfHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_3} β _inst_2) (OrderDual.hasInf.{u_4} γ _inst_3)) (f : InfHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_3} β _inst_2)), Eq.{(max (succ u_2) (succ u_4))} (SupHom.{u_2 u_4} α γ _inst_1 _inst_3) (coeFn.{(max 1 (succ u_2) (succ u_4)) (max (succ u_2) (succ u_4))} (Equiv.{(max (succ u_2) (succ u_4)) (max (succ u_2) (succ u_4))} (InfHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_4} γ _inst_3)) (SupHom.{u_2 u_4} α γ _inst_1 _inst_3)) (fun (_x : Equiv.{(max (succ u_2) (succ u_4)) (max (succ u_2) (succ u_4))} (InfHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_4} γ _inst_3)) (SupHom.{u_2 u_4} α γ _inst_1 _inst_3)) => (InfHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_4} γ _inst_3)) -> (SupHom.{u_2 u_4} α γ _inst_1 _inst_3)) (Equiv.hasCoeToFun.{(max (succ u_2) (succ u_4)) (max (succ u_2) (succ u_4))} (InfHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_4} γ _inst_3)) (SupHom.{u_2 u_4} α γ _inst_1 _inst_3)) (Equiv.symm.{(max (succ u_2) (succ u_4)) (max (succ u_2) (succ u_4))} (SupHom.{u_2 u_4} α γ _inst_1 _inst_3) (InfHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_4} γ _inst_3)) (SupHom.dual.{u_2 u_4} α γ _inst_1 _inst_3)) (InfHom.comp.{u_2 u_3 u_4} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_3} β _inst_2) (OrderDual.hasInf.{u_4} γ _inst_3) g f)) (SupHom.comp.{u_2 u_3 u_4} α β γ _inst_1 _inst_2 _inst_3 (coeFn.{(max 1 (succ u_3) (succ u_4)) (max (succ u_3) (succ u_4))} (Equiv.{(max (succ u_3) (succ u_4)) (max (succ u_3) (succ u_4))} (InfHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_3} β _inst_2) (OrderDual.hasInf.{u_4} γ _inst_3)) (SupHom.{u_3 u_4} β γ _inst_2 _inst_3)) (fun (_x : Equiv.{(max (succ u_3) (succ u_4)) (max (succ u_3) (succ u_4))} (InfHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_3} β _inst_2) (OrderDual.hasInf.{u_4} γ _inst_3)) (SupHom.{u_3 u_4} β γ _inst_2 _inst_3)) => (InfHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_3} β _inst_2) (OrderDual.hasInf.{u_4} γ _inst_3)) -> (SupHom.{u_3 u_4} β γ _inst_2 _inst_3)) (Equiv.hasCoeToFun.{(max (succ u_3) (succ u_4)) (max (succ u_3) (succ u_4))} (InfHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_3} β _inst_2) (OrderDual.hasInf.{u_4} γ _inst_3)) (SupHom.{u_3 u_4} β γ _inst_2 _inst_3)) (Equiv.symm.{(max (succ u_3) (succ u_4)) (max (succ u_3) (succ u_4))} (SupHom.{u_3 u_4} β γ _inst_2 _inst_3) (InfHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasInf.{u_3} β _inst_2) (OrderDual.hasInf.{u_4} γ _inst_3)) (SupHom.dual.{u_3 u_4} β γ _inst_2 _inst_3)) g) (coeFn.{(max 1 (succ u_2) (succ u_3)) (max (succ u_2) (succ u_3))} (Equiv.{(max (succ u_2) (succ u_3)) (max (succ u_2) (succ u_3))} (InfHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_3} β _inst_2)) (SupHom.{u_2 u_3} α β _inst_1 _inst_2)) (fun (_x : Equiv.{(max (succ u_2) (succ u_3)) (max (succ u_2) (succ u_3))} (InfHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_3} β _inst_2)) (SupHom.{u_2 u_3} α β _inst_1 _inst_2)) => (InfHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_3} β _inst_2)) -> (SupHom.{u_2 u_3} α β _inst_1 _inst_2)) (Equiv.hasCoeToFun.{(max (succ u_2) (succ u_3)) (max (succ u_2) (succ u_3))} (InfHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_3} β _inst_2)) (SupHom.{u_2 u_3} α β _inst_1 _inst_2)) (Equiv.symm.{(max (succ u_2) (succ u_3)) (max (succ u_2) (succ u_3))} (SupHom.{u_2 u_3} α β _inst_1 _inst_2) (InfHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasInf.{u_2} α _inst_1) (OrderDual.hasInf.{u_3} β _inst_2)) (SupHom.dual.{u_2 u_3} α β _inst_1 _inst_2)) f))
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align Sup_hom.symm_dual_comp SupHom.symm_dual_compₓ'. -/
@[simp]
theorem symm_dual_comp (g : InfHom βᵒᵈ γᵒᵈ) (f : InfHom αᵒᵈ βᵒᵈ) :
    SupHom.dual.symm (g.comp f) = (SupHom.dual.symm g).comp (SupHom.dual.symm f) :=
  rfl

end SupHom

namespace InfHom

variable [HasInf α] [HasInf β] [HasInf γ]

/- warning: Inf_hom.dual_id clashes with inf_hom.dual_id -> InfHom.dual_id
warning: Inf_hom.dual_id -> InfHom.dual_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} [_inst_1 : HasInf.{u_2} α], Eq.{succ u_2} (SupHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_2} α _inst_1)) (coeFn.{(max 1 (succ u_2)) succ u_2} (Equiv.{succ u_2 succ u_2} (InfHom.{u_2 u_2} α α _inst_1 _inst_1) (SupHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_2} α _inst_1))) (fun (_x : Equiv.{succ u_2 succ u_2} (InfHom.{u_2 u_2} α α _inst_1 _inst_1) (SupHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_2} α _inst_1))) => (InfHom.{u_2 u_2} α α _inst_1 _inst_1) -> (SupHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_2} α _inst_1))) (Equiv.hasCoeToFun.{succ u_2 succ u_2} (InfHom.{u_2 u_2} α α _inst_1 _inst_1) (SupHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_2} α _inst_1))) (InfHom.dual.{u_2 u_2} α α _inst_1 _inst_1) (InfHom.id.{u_2} α _inst_1)) (SupHom.id.{u_2} (OrderDual.{u_2} α) (OrderDual.hasSup.{u_2} α _inst_1))
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align Inf_hom.dual_id InfHom.dual_idₓ'. -/
@[simp]
theorem dual_id : (InfHom.id α).dual = SupHom.id _ :=
  rfl

/- warning: Inf_hom.dual_comp clashes with inf_hom.dual_comp -> InfHom.dual_comp
warning: Inf_hom.dual_comp -> InfHom.dual_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {β : Type.{u_3}} {γ : Type.{u_4}} [_inst_1 : HasInf.{u_2} α] [_inst_2 : HasInf.{u_3} β] [_inst_3 : HasInf.{u_4} γ] (g : InfHom.{u_3 u_4} β γ _inst_2 _inst_3) (f : InfHom.{u_2 u_3} α β _inst_1 _inst_2), Eq.{(max (succ u_2) (succ u_4))} (SupHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_4} γ _inst_3)) (coeFn.{(max 1 (succ u_2) (succ u_4)) (max (succ u_2) (succ u_4))} (Equiv.{(max (succ u_2) (succ u_4)) (max (succ u_2) (succ u_4))} (InfHom.{u_2 u_4} α γ _inst_1 _inst_3) (SupHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_4} γ _inst_3))) (fun (_x : Equiv.{(max (succ u_2) (succ u_4)) (max (succ u_2) (succ u_4))} (InfHom.{u_2 u_4} α γ _inst_1 _inst_3) (SupHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_4} γ _inst_3))) => (InfHom.{u_2 u_4} α γ _inst_1 _inst_3) -> (SupHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_4} γ _inst_3))) (Equiv.hasCoeToFun.{(max (succ u_2) (succ u_4)) (max (succ u_2) (succ u_4))} (InfHom.{u_2 u_4} α γ _inst_1 _inst_3) (SupHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_4} γ _inst_3))) (InfHom.dual.{u_2 u_4} α γ _inst_1 _inst_3) (InfHom.comp.{u_2 u_3 u_4} α β γ _inst_1 _inst_2 _inst_3 g f)) (SupHom.comp.{u_2 u_3 u_4} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_3} β _inst_2) (OrderDual.hasSup.{u_4} γ _inst_3) (coeFn.{(max 1 (succ u_3) (succ u_4)) (max (succ u_3) (succ u_4))} (Equiv.{(max (succ u_3) (succ u_4)) (max (succ u_3) (succ u_4))} (InfHom.{u_3 u_4} β γ _inst_2 _inst_3) (SupHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_3} β _inst_2) (OrderDual.hasSup.{u_4} γ _inst_3))) (fun (_x : Equiv.{(max (succ u_3) (succ u_4)) (max (succ u_3) (succ u_4))} (InfHom.{u_3 u_4} β γ _inst_2 _inst_3) (SupHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_3} β _inst_2) (OrderDual.hasSup.{u_4} γ _inst_3))) => (InfHom.{u_3 u_4} β γ _inst_2 _inst_3) -> (SupHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_3} β _inst_2) (OrderDual.hasSup.{u_4} γ _inst_3))) (Equiv.hasCoeToFun.{(max (succ u_3) (succ u_4)) (max (succ u_3) (succ u_4))} (InfHom.{u_3 u_4} β γ _inst_2 _inst_3) (SupHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_3} β _inst_2) (OrderDual.hasSup.{u_4} γ _inst_3))) (InfHom.dual.{u_3 u_4} β γ _inst_2 _inst_3) g) (coeFn.{(max 1 (succ u_2) (succ u_3)) (max (succ u_2) (succ u_3))} (Equiv.{(max (succ u_2) (succ u_3)) (max (succ u_2) (succ u_3))} (InfHom.{u_2 u_3} α β _inst_1 _inst_2) (SupHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_3} β _inst_2))) (fun (_x : Equiv.{(max (succ u_2) (succ u_3)) (max (succ u_2) (succ u_3))} (InfHom.{u_2 u_3} α β _inst_1 _inst_2) (SupHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_3} β _inst_2))) => (InfHom.{u_2 u_3} α β _inst_1 _inst_2) -> (SupHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_3} β _inst_2))) (Equiv.hasCoeToFun.{(max (succ u_2) (succ u_3)) (max (succ u_2) (succ u_3))} (InfHom.{u_2 u_3} α β _inst_1 _inst_2) (SupHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_3} β _inst_2))) (InfHom.dual.{u_2 u_3} α β _inst_1 _inst_2) f))
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align Inf_hom.dual_comp InfHom.dual_compₓ'. -/
@[simp]
theorem dual_comp (g : InfHom β γ) (f : InfHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl

/- warning: Inf_hom.symm_dual_id clashes with inf_hom.symm_dual_id -> InfHom.symm_dual_id
warning: Inf_hom.symm_dual_id -> InfHom.symm_dual_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} [_inst_1 : HasInf.{u_2} α], Eq.{succ u_2} (InfHom.{u_2 u_2} α α _inst_1 _inst_1) (coeFn.{(max 1 (succ u_2)) succ u_2} (Equiv.{succ u_2 succ u_2} (SupHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_2} α _inst_1)) (InfHom.{u_2 u_2} α α _inst_1 _inst_1)) (fun (_x : Equiv.{succ u_2 succ u_2} (SupHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_2} α _inst_1)) (InfHom.{u_2 u_2} α α _inst_1 _inst_1)) => (SupHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_2} α _inst_1)) -> (InfHom.{u_2 u_2} α α _inst_1 _inst_1)) (Equiv.hasCoeToFun.{succ u_2 succ u_2} (SupHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_2} α _inst_1)) (InfHom.{u_2 u_2} α α _inst_1 _inst_1)) (Equiv.symm.{succ u_2 succ u_2} (InfHom.{u_2 u_2} α α _inst_1 _inst_1) (SupHom.{u_2 u_2} (OrderDual.{u_2} α) (OrderDual.{u_2} α) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_2} α _inst_1)) (InfHom.dual.{u_2 u_2} α α _inst_1 _inst_1)) (SupHom.id.{u_2} (OrderDual.{u_2} α) (OrderDual.hasSup.{u_2} α _inst_1))) (InfHom.id.{u_2} α _inst_1)
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align Inf_hom.symm_dual_id InfHom.symm_dual_idₓ'. -/
@[simp]
theorem symm_dual_id : InfHom.dual.symm (SupHom.id _) = InfHom.id α :=
  rfl

/- warning: Inf_hom.symm_dual_comp clashes with inf_hom.symm_dual_comp -> InfHom.symm_dual_comp
warning: Inf_hom.symm_dual_comp -> InfHom.symm_dual_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {β : Type.{u_3}} {γ : Type.{u_4}} [_inst_1 : HasInf.{u_2} α] [_inst_2 : HasInf.{u_3} β] [_inst_3 : HasInf.{u_4} γ] (g : SupHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_3} β _inst_2) (OrderDual.hasSup.{u_4} γ _inst_3)) (f : SupHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_3} β _inst_2)), Eq.{(max (succ u_2) (succ u_4))} (InfHom.{u_2 u_4} α γ _inst_1 _inst_3) (coeFn.{(max 1 (succ u_2) (succ u_4)) (max (succ u_2) (succ u_4))} (Equiv.{(max (succ u_2) (succ u_4)) (max (succ u_2) (succ u_4))} (SupHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_4} γ _inst_3)) (InfHom.{u_2 u_4} α γ _inst_1 _inst_3)) (fun (_x : Equiv.{(max (succ u_2) (succ u_4)) (max (succ u_2) (succ u_4))} (SupHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_4} γ _inst_3)) (InfHom.{u_2 u_4} α γ _inst_1 _inst_3)) => (SupHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_4} γ _inst_3)) -> (InfHom.{u_2 u_4} α γ _inst_1 _inst_3)) (Equiv.hasCoeToFun.{(max (succ u_2) (succ u_4)) (max (succ u_2) (succ u_4))} (SupHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_4} γ _inst_3)) (InfHom.{u_2 u_4} α γ _inst_1 _inst_3)) (Equiv.symm.{(max (succ u_2) (succ u_4)) (max (succ u_2) (succ u_4))} (InfHom.{u_2 u_4} α γ _inst_1 _inst_3) (SupHom.{u_2 u_4} (OrderDual.{u_2} α) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_4} γ _inst_3)) (InfHom.dual.{u_2 u_4} α γ _inst_1 _inst_3)) (SupHom.comp.{u_2 u_3 u_4} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_3} β _inst_2) (OrderDual.hasSup.{u_4} γ _inst_3) g f)) (InfHom.comp.{u_2 u_3 u_4} α β γ _inst_1 _inst_2 _inst_3 (coeFn.{(max 1 (succ u_3) (succ u_4)) (max (succ u_3) (succ u_4))} (Equiv.{(max (succ u_3) (succ u_4)) (max (succ u_3) (succ u_4))} (SupHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_3} β _inst_2) (OrderDual.hasSup.{u_4} γ _inst_3)) (InfHom.{u_3 u_4} β γ _inst_2 _inst_3)) (fun (_x : Equiv.{(max (succ u_3) (succ u_4)) (max (succ u_3) (succ u_4))} (SupHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_3} β _inst_2) (OrderDual.hasSup.{u_4} γ _inst_3)) (InfHom.{u_3 u_4} β γ _inst_2 _inst_3)) => (SupHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_3} β _inst_2) (OrderDual.hasSup.{u_4} γ _inst_3)) -> (InfHom.{u_3 u_4} β γ _inst_2 _inst_3)) (Equiv.hasCoeToFun.{(max (succ u_3) (succ u_4)) (max (succ u_3) (succ u_4))} (SupHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_3} β _inst_2) (OrderDual.hasSup.{u_4} γ _inst_3)) (InfHom.{u_3 u_4} β γ _inst_2 _inst_3)) (Equiv.symm.{(max (succ u_3) (succ u_4)) (max (succ u_3) (succ u_4))} (InfHom.{u_3 u_4} β γ _inst_2 _inst_3) (SupHom.{u_3 u_4} (OrderDual.{u_3} β) (OrderDual.{u_4} γ) (OrderDual.hasSup.{u_3} β _inst_2) (OrderDual.hasSup.{u_4} γ _inst_3)) (InfHom.dual.{u_3 u_4} β γ _inst_2 _inst_3)) g) (coeFn.{(max 1 (succ u_2) (succ u_3)) (max (succ u_2) (succ u_3))} (Equiv.{(max (succ u_2) (succ u_3)) (max (succ u_2) (succ u_3))} (SupHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_3} β _inst_2)) (InfHom.{u_2 u_3} α β _inst_1 _inst_2)) (fun (_x : Equiv.{(max (succ u_2) (succ u_3)) (max (succ u_2) (succ u_3))} (SupHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_3} β _inst_2)) (InfHom.{u_2 u_3} α β _inst_1 _inst_2)) => (SupHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_3} β _inst_2)) -> (InfHom.{u_2 u_3} α β _inst_1 _inst_2)) (Equiv.hasCoeToFun.{(max (succ u_2) (succ u_3)) (max (succ u_2) (succ u_3))} (SupHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_3} β _inst_2)) (InfHom.{u_2 u_3} α β _inst_1 _inst_2)) (Equiv.symm.{(max (succ u_2) (succ u_3)) (max (succ u_2) (succ u_3))} (InfHom.{u_2 u_3} α β _inst_1 _inst_2) (SupHom.{u_2 u_3} (OrderDual.{u_2} α) (OrderDual.{u_3} β) (OrderDual.hasSup.{u_2} α _inst_1) (OrderDual.hasSup.{u_3} β _inst_2)) (InfHom.dual.{u_2 u_3} α β _inst_1 _inst_2)) f))
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align Inf_hom.symm_dual_comp InfHom.symm_dual_compₓ'. -/
@[simp]
theorem symm_dual_comp (g : SupHom βᵒᵈ γᵒᵈ) (f : SupHom αᵒᵈ βᵒᵈ) :
    InfHom.dual.symm (g.comp f) = (InfHom.dual.symm g).comp (InfHom.dual.symm f) :=
  rfl

end InfHom

namespace CompleteLatticeHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ]

/-- Reinterpret a complete lattice homomorphism as a complete lattice homomorphism between the dual
lattices. -/
@[simps]
protected def dual : CompleteLatticeHom α β ≃ CompleteLatticeHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨f.toSupHom.dual, f.map_Inf'⟩
  invFun f := ⟨f.toSupHom.dual, f.map_Inf'⟩
  left_inv f := ext fun a => rfl
  right_inv f := ext fun a => rfl

@[simp]
theorem dual_id : (CompleteLatticeHom.id α).dual = CompleteLatticeHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : CompleteLatticeHom β γ) (f : CompleteLatticeHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
theorem symm_dual_id : CompleteLatticeHom.dual.symm (CompleteLatticeHom.id _) = CompleteLatticeHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : CompleteLatticeHom βᵒᵈ γᵒᵈ) (f : CompleteLatticeHom αᵒᵈ βᵒᵈ) :
    CompleteLatticeHom.dual.symm (g.comp f) = (CompleteLatticeHom.dual.symm g).comp (CompleteLatticeHom.dual.symm f) :=
  rfl

end CompleteLatticeHom

/-! ### Concrete homs -/


namespace CompleteLatticeHom

/-- `set.preimage` as a complete lattice homomorphism. -/
def setPreimage (f : α → β) : CompleteLatticeHom (Set β) (Set α) where
  toFun := Preimage f
  map_Sup' s := preimage_sUnion.trans <| by simp only [Set.Sup_eq_sUnion, Set.sUnion_image]
  map_Inf' s := preimage_sInter.trans <| by simp only [Set.Inf_eq_sInter, Set.sInter_image]

@[simp]
theorem coe_set_preimage (f : α → β) : ⇑(setPreimage f) = Preimage f :=
  rfl

@[simp]
theorem set_preimage_apply (f : α → β) (s : Set β) : setPreimage f s = s.Preimage f :=
  rfl

@[simp]
theorem set_preimage_id : setPreimage (id : α → α) = CompleteLatticeHom.id _ :=
  rfl

-- This lemma can't be `simp` because `g ∘ f` matches anything (`id ∘ f = f` synctatically)
theorem set_preimage_comp (g : β → γ) (f : α → β) : setPreimage (g ∘ f) = (setPreimage f).comp (setPreimage g) :=
  rfl

end CompleteLatticeHom

