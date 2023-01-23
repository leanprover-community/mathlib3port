/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

! This file was ported from Lean 3 source module logic.equiv.defs
! leanprover-community/mathlib commit 1f0096e6caa61e9c849ec2adbd227e960e9dff58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.FunLike.Equiv
import Mathbin.Logic.Unique

/-!
# Equivalence between types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define two types:

* `equiv α β` a.k.a. `α ≃ β`: a bijective map `α → β` bundled with its inverse map; we use this (and
  not equality!) to express that various `Type`s or `Sort`s are equivalent.

* `equiv.perm α`: the group of permutations `α ≃ α`. More lemmas about `equiv.perm` can be found in
  `group_theory/perm`.

Then we define

* canonical isomorphisms between various types: e.g.,

  - `equiv.refl α` is the identity map interpreted as `α ≃ α`;

* operations on equivalences: e.g.,

  - `equiv.symm e : β ≃ α` is the inverse of `e : α ≃ β`;

  - `equiv.trans e₁ e₂ : α ≃ γ` is the composition of `e₁ : α ≃ β` and `e₂ : β ≃ γ` (note the order
    of the arguments!);

* definitions that transfer some instances along an equivalence. By convention, we transfer
  instances from right to left.

  - `equiv.inhabited` takes `e : α ≃ β` and `[inhabited β]` and returns `inhabited α`;
  - `equiv.unique` takes `e : α ≃ β` and `[unique β]` and returns `unique α`;
  - `equiv.decidable_eq` takes `e : α ≃ β` and `[decidable_eq β]` and returns `decidable_eq α`.

  More definitions of this kind can be found in other files. E.g., `data/equiv/transfer_instance`
  does it for many algebraic type classes like `group`, `module`, etc.

Many more such isomorphisms and operations are defined in `logic/equiv/basic`.

## Tags

equivalence, congruence, bijective map
-/


open Function

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

/- warning: equiv -> Equiv is a dubious translation:
lean 3 declaration is
  Sort.{u1} -> Sort.{u2} -> Sort.{max 1 (imax u1 u2) (imax u2 u1)}
but is expected to have type
  Sort.{u1} -> Sort.{u2} -> Sort.{max (max 1 u1) u2}
Case conversion may be inaccurate. Consider using '#align equiv Equivₓ'. -/
/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
structure Equiv (α : Sort _) (β : Sort _) where
  toFun : α → β
  invFun : β → α
  left_inv : LeftInverse inv_fun to_fun
  right_inv : RightInverse inv_fun to_fun
#align equiv Equiv

-- mathport name: «expr ≃ »
infixl:25 " ≃ " => Equiv

instance {F} [EquivLike F α β] : CoeTC F (α ≃ β) :=
  ⟨fun f =>
    { toFun := f
      invFun := EquivLike.inv f
      left_inv := EquivLike.left_inv f
      right_inv := EquivLike.right_inv f }⟩

#print Equiv.Perm /-
/-- `perm α` is the type of bijections from `α` to itself. -/
@[reducible]
def Equiv.Perm (α : Sort _) :=
  Equiv α α
#align equiv.perm Equiv.Perm
-/

namespace Equiv

instance : EquivLike (α ≃ β) α β where
  coe := toFun
  inv := invFun
  left_inv := left_inv
  right_inv := right_inv
  coe_injective' e₁ e₂ h₁ h₂ := by
    cases e₁
    cases e₂
    congr

instance : CoeFun (α ≃ β) fun _ => α → β :=
  ⟨toFun⟩

@[simp]
theorem coeFn_mk (f : α → β) (g l r) : (Equiv.mk f g l r : α → β) = f :=
  rfl
#align equiv.coe_fn_mk Equiv.coeFn_mk

/-- The map `coe_fn : (r ≃ s) → (r → s)` is injective. -/
theorem coeFn_injective : @Function.Injective (α ≃ β) (α → β) coeFn :=
  FunLike.coe_injective
#align equiv.coe_fn_injective Equiv.coeFn_injective

#print Equiv.coe_inj /-
protected theorem coe_inj {e₁ e₂ : α ≃ β} : (e₁ : α → β) = e₂ ↔ e₁ = e₂ :=
  FunLike.coeFn_eq
#align equiv.coe_inj Equiv.coe_inj
-/

#print Equiv.ext /-
@[ext]
theorem ext {f g : Equiv α β} (H : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g H
#align equiv.ext Equiv.ext
-/

#print Equiv.congr_arg /-
protected theorem congr_arg {f : Equiv α β} {x x' : α} : x = x' → f x = f x' :=
  FunLike.congr_arg f
#align equiv.congr_arg Equiv.congr_arg
-/

/- warning: equiv.congr_fun -> Equiv.congr_fun is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {f : Equiv.{u1, u2} α β} {g : Equiv.{u1, u2} α β}, (Eq.{max 1 (imax u1 u2) (imax u2 u1)} (Equiv.{u1, u2} α β) f g) -> (forall (x : α), Eq.{u2} β (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) f x) (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) g x))
but is expected to have type
  forall {α : Sort.{u1}} {β : Sort.{u2}} {f : Equiv.{u1, u2} α β} {g : Equiv.{u1, u2} α β}, (Eq.{max (max 1 u1) u2} (Equiv.{u1, u2} α β) f g) -> (forall (x : α), Eq.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) x) (FunLike.coe.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α β) α β (Equiv.instEquivLikeEquiv.{u1, u2} α β))) f x) (FunLike.coe.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α β) α β (Equiv.instEquivLikeEquiv.{u1, u2} α β))) g x))
Case conversion may be inaccurate. Consider using '#align equiv.congr_fun Equiv.congr_funₓ'. -/
protected theorem congr_fun {f g : Equiv α β} (h : f = g) (x : α) : f x = g x :=
  FunLike.congr_fun h x
#align equiv.congr_fun Equiv.congr_fun

/- warning: equiv.ext_iff -> Equiv.ext_iff is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {f : Equiv.{u1, u2} α β} {g : Equiv.{u1, u2} α β}, Iff (Eq.{max 1 (imax u1 u2) (imax u2 u1)} (Equiv.{u1, u2} α β) f g) (forall (x : α), Eq.{u2} β (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) f x) (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) g x))
but is expected to have type
  forall {α : Sort.{u1}} {β : Sort.{u2}} {f : Equiv.{u1, u2} α β} {g : Equiv.{u1, u2} α β}, Iff (Eq.{max (max 1 u1) u2} (Equiv.{u1, u2} α β) f g) (forall (x : α), Eq.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) x) (FunLike.coe.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α β) α β (Equiv.instEquivLikeEquiv.{u1, u2} α β))) f x) (FunLike.coe.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α β) α β (Equiv.instEquivLikeEquiv.{u1, u2} α β))) g x))
Case conversion may be inaccurate. Consider using '#align equiv.ext_iff Equiv.ext_iffₓ'. -/
theorem ext_iff {f g : Equiv α β} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align equiv.ext_iff Equiv.ext_iff

#print Equiv.Perm.ext /-
@[ext]
theorem Perm.ext {σ τ : Equiv.Perm α} (H : ∀ x, σ x = τ x) : σ = τ :=
  Equiv.ext H
#align equiv.perm.ext Equiv.Perm.ext
-/

#print Equiv.Perm.congr_arg /-
protected theorem Perm.congr_arg {f : Equiv.Perm α} {x x' : α} : x = x' → f x = f x' :=
  Equiv.congr_arg
#align equiv.perm.congr_arg Equiv.Perm.congr_arg
-/

#print Equiv.Perm.congr_fun /-
protected theorem Perm.congr_fun {f g : Equiv.Perm α} (h : f = g) (x : α) : f x = g x :=
  Equiv.congr_fun h x
#align equiv.perm.congr_fun Equiv.Perm.congr_fun
-/

#print Equiv.Perm.ext_iff /-
theorem Perm.ext_iff {σ τ : Equiv.Perm α} : σ = τ ↔ ∀ x, σ x = τ x :=
  ext_iff
#align equiv.perm.ext_iff Equiv.Perm.ext_iff
-/

#print Equiv.refl /-
/-- Any type is equivalent to itself. -/
@[refl]
protected def refl (α : Sort _) : α ≃ α :=
  ⟨id, id, fun x => rfl, fun x => rfl⟩
#align equiv.refl Equiv.refl
-/

#print Equiv.inhabited' /-
instance inhabited' : Inhabited (α ≃ α) :=
  ⟨Equiv.refl α⟩
#align equiv.inhabited' Equiv.inhabited'
-/

#print Equiv.symm /-
/-- Inverse of an equivalence `e : α ≃ β`. -/
@[symm]
protected def symm (e : α ≃ β) : β ≃ α :=
  ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩
#align equiv.symm Equiv.symm
-/

/-- See Note [custom simps projection] -/
def Simps.symmApply (e : α ≃ β) : β → α :=
  e.symm
#align equiv.simps.symm_apply Equiv.Simps.symmApply

initialize_simps_projections Equiv (toFun → apply, invFun → symmApply)

#print Equiv.trans /-
/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[trans]
protected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm, e₂.left_inv.comp e₁.left_inv, e₂.right_inv.comp e₁.right_inv⟩
#align equiv.trans Equiv.trans
-/

#print Equiv.toFun_as_coe /-
@[simp]
theorem toFun_as_coe (e : α ≃ β) : e.toFun = e :=
  rfl
#align equiv.to_fun_as_coe Equiv.toFun_as_coe
-/

#print Equiv.invFun_as_coe /-
@[simp]
theorem invFun_as_coe (e : α ≃ β) : e.invFun = e.symm :=
  rfl
#align equiv.inv_fun_as_coe Equiv.invFun_as_coe
-/

#print Equiv.injective /-
protected theorem injective (e : α ≃ β) : Injective e :=
  EquivLike.injective e
#align equiv.injective Equiv.injective
-/

#print Equiv.surjective /-
protected theorem surjective (e : α ≃ β) : Surjective e :=
  EquivLike.surjective e
#align equiv.surjective Equiv.surjective
-/

#print Equiv.bijective /-
protected theorem bijective (e : α ≃ β) : Bijective e :=
  EquivLike.bijective e
#align equiv.bijective Equiv.bijective
-/

#print Equiv.subsingleton /-
protected theorem subsingleton (e : α ≃ β) [Subsingleton β] : Subsingleton α :=
  e.Injective.Subsingleton
#align equiv.subsingleton Equiv.subsingleton
-/

#print Equiv.subsingleton.symm /-
protected theorem subsingleton.symm (e : α ≃ β) [Subsingleton α] : Subsingleton β :=
  e.symm.Injective.Subsingleton
#align equiv.subsingleton.symm Equiv.subsingleton.symm
-/

#print Equiv.subsingleton_congr /-
theorem subsingleton_congr (e : α ≃ β) : Subsingleton α ↔ Subsingleton β :=
  ⟨fun h => e.symm.subsingleton, fun h => e.subsingleton⟩
#align equiv.subsingleton_congr Equiv.subsingleton_congr
-/

/- warning: equiv.equiv_subsingleton_cod -> Equiv.equiv_subsingleton_cod is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Subsingleton.{u2} β], Subsingleton.{max 1 (imax u1 u2) (imax u2 u1)} (Equiv.{u1, u2} α β)
but is expected to have type
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Subsingleton.{u2} β], Subsingleton.{max (max 1 u2) u1} (Equiv.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align equiv.equiv_subsingleton_cod Equiv.equiv_subsingleton_codₓ'. -/
instance equiv_subsingleton_cod [Subsingleton β] : Subsingleton (α ≃ β) :=
  FunLike.subsingleton_cod
#align equiv.equiv_subsingleton_cod Equiv.equiv_subsingleton_cod

/- warning: equiv.equiv_subsingleton_dom -> Equiv.equiv_subsingleton_dom is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Subsingleton.{u1} α], Subsingleton.{max 1 (imax u1 u2) (imax u2 u1)} (Equiv.{u1, u2} α β)
but is expected to have type
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Subsingleton.{u1} α], Subsingleton.{max (max 1 u2) u1} (Equiv.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align equiv.equiv_subsingleton_dom Equiv.equiv_subsingleton_domₓ'. -/
instance equiv_subsingleton_dom [Subsingleton α] : Subsingleton (α ≃ β) :=
  EquivLike.subsingleton_dom
#align equiv.equiv_subsingleton_dom Equiv.equiv_subsingleton_dom

#print Equiv.permUnique /-
instance permUnique [Subsingleton α] : Unique (Perm α) :=
  uniqueOfSubsingleton (Equiv.refl α)
#align equiv.perm_unique Equiv.permUnique
-/

#print Equiv.Perm.subsingleton_eq_refl /-
theorem Perm.subsingleton_eq_refl [Subsingleton α] (e : Perm α) : e = Equiv.refl α :=
  Subsingleton.elim _ _
#align equiv.perm.subsingleton_eq_refl Equiv.Perm.subsingleton_eq_refl
-/

#print Equiv.decidableEq /-
/-- Transfer `decidable_eq` across an equivalence. -/
protected def decidableEq (e : α ≃ β) [DecidableEq β] : DecidableEq α :=
  e.Injective.DecidableEq
#align equiv.decidable_eq Equiv.decidableEq
-/

#print Equiv.nonempty_congr /-
theorem nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty β :=
  Nonempty.congr e e.symm
#align equiv.nonempty_congr Equiv.nonempty_congr
-/

#print Equiv.nonempty /-
protected theorem nonempty (e : α ≃ β) [Nonempty β] : Nonempty α :=
  e.nonempty_congr.mpr ‹_›
#align equiv.nonempty Equiv.nonempty
-/

#print Equiv.inhabited /-
/-- If `α ≃ β` and `β` is inhabited, then so is `α`. -/
protected def inhabited [Inhabited β] (e : α ≃ β) : Inhabited α :=
  ⟨e.symm default⟩
#align equiv.inhabited Equiv.inhabited
-/

#print Equiv.unique /-
/-- If `α ≃ β` and `β` is a singleton type, then so is `α`. -/
protected def unique [Unique β] (e : α ≃ β) : Unique α :=
  e.symm.Surjective.unique
#align equiv.unique Equiv.unique
-/

#print Equiv.cast /-
/-- Equivalence between equal types. -/
protected def cast {α β : Sort _} (h : α = β) : α ≃ β :=
  ⟨cast h, cast h.symm, fun x => by
    cases h
    rfl, fun x => by
    cases h
    rfl⟩
#align equiv.cast Equiv.cast
-/

@[simp]
theorem coeFn_symm_mk (f : α → β) (g l r) : ((Equiv.mk f g l r).symm : β → α) = g :=
  rfl
#align equiv.coe_fn_symm_mk Equiv.coeFn_symm_mk

#print Equiv.coe_refl /-
@[simp]
theorem coe_refl : ⇑(Equiv.refl α) = id :=
  rfl
#align equiv.coe_refl Equiv.coe_refl
-/

#print Equiv.Perm.coe_subsingleton /-
/-- This cannot be a `simp` lemmas as it incorrectly matches against `e : α ≃ synonym α`, when
`synonym α` is semireducible. This makes a mess of `multiplicative.of_add` etc. -/
theorem Perm.coe_subsingleton {α : Type _} [Subsingleton α] (e : Perm α) : ⇑e = id := by
  rw [perm.subsingleton_eq_refl e, coe_refl]
#align equiv.perm.coe_subsingleton Equiv.Perm.coe_subsingleton
-/

#print Equiv.refl_apply /-
theorem refl_apply (x : α) : Equiv.refl α x = x :=
  rfl
#align equiv.refl_apply Equiv.refl_apply
-/

#print Equiv.coe_trans /-
@[simp]
theorem coe_trans (f : α ≃ β) (g : β ≃ γ) : ⇑(f.trans g) = g ∘ f :=
  rfl
#align equiv.coe_trans Equiv.coe_trans
-/

#print Equiv.trans_apply /-
theorem trans_apply (f : α ≃ β) (g : β ≃ γ) (a : α) : (f.trans g) a = g (f a) :=
  rfl
#align equiv.trans_apply Equiv.trans_apply
-/

#print Equiv.apply_symm_apply /-
@[simp]
theorem apply_symm_apply (e : α ≃ β) (x : β) : e (e.symm x) = x :=
  e.right_inv x
#align equiv.apply_symm_apply Equiv.apply_symm_apply
-/

#print Equiv.symm_apply_apply /-
@[simp]
theorem symm_apply_apply (e : α ≃ β) (x : α) : e.symm (e x) = x :=
  e.left_inv x
#align equiv.symm_apply_apply Equiv.symm_apply_apply
-/

#print Equiv.symm_comp_self /-
@[simp]
theorem symm_comp_self (e : α ≃ β) : e.symm ∘ e = id :=
  funext e.symm_apply_apply
#align equiv.symm_comp_self Equiv.symm_comp_self
-/

#print Equiv.self_comp_symm /-
@[simp]
theorem self_comp_symm (e : α ≃ β) : e ∘ e.symm = id :=
  funext e.apply_symm_apply
#align equiv.self_comp_symm Equiv.self_comp_symm
-/

#print Equiv.symm_trans_apply /-
@[simp]
theorem symm_trans_apply (f : α ≃ β) (g : β ≃ γ) (a : γ) : (f.trans g).symm a = f.symm (g.symm a) :=
  rfl
#align equiv.symm_trans_apply Equiv.symm_trans_apply
-/

#print Equiv.symm_symm_apply /-
-- The `simp` attribute is needed to make this a `dsimp` lemma.
-- `simp` will always rewrite with `equiv.symm_symm` before this has a chance to fire.
@[simp, nolint simp_nf]
theorem symm_symm_apply (f : α ≃ β) (b : α) : f.symm.symm b = f b :=
  rfl
#align equiv.symm_symm_apply Equiv.symm_symm_apply
-/

#print Equiv.apply_eq_iff_eq /-
theorem apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y ↔ x = y :=
  EquivLike.apply_eq_iff_eq f
#align equiv.apply_eq_iff_eq Equiv.apply_eq_iff_eq
-/

/- warning: equiv.apply_eq_iff_eq_symm_apply -> Equiv.apply_eq_iff_eq_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} (f : Equiv.{u1, u2} α β) {x : α} {y : β}, Iff (Eq.{u2} β (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) f x) y) (Eq.{u1} α x (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β f) y))
but is expected to have type
  forall {α : Sort.{u1}} {β : Sort.{u2}} {f : α} {x : (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) f} (y : Equiv.{u1, u2} α β), Iff (Eq.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) f) (FunLike.coe.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} α β) α β (Equiv.instEquivLikeEquiv.{u1, u2} α β))) y f) x) (Eq.{u1} α f (FunLike.coe.{max (max 1 u1) u2, u2, u1} (Equiv.{u2, u1} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u2, u1} (Equiv.{u2, u1} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u2, u1} (Equiv.{u2, u1} β α) β α (Equiv.instEquivLikeEquiv.{u2, u1} β α))) (Equiv.symm.{u1, u2} α β y) x))
Case conversion may be inaccurate. Consider using '#align equiv.apply_eq_iff_eq_symm_apply Equiv.apply_eq_iff_eq_symm_applyₓ'. -/
theorem apply_eq_iff_eq_symm_apply {α β : Sort _} (f : α ≃ β) {x : α} {y : β} :
    f x = y ↔ x = f.symm y := by
  conv_lhs => rw [← apply_symm_apply f y]
  rw [apply_eq_iff_eq]
#align equiv.apply_eq_iff_eq_symm_apply Equiv.apply_eq_iff_eq_symm_apply

#print Equiv.cast_apply /-
@[simp]
theorem cast_apply {α β} (h : α = β) (x : α) : Equiv.cast h x = cast h x :=
  rfl
#align equiv.cast_apply Equiv.cast_apply
-/

#print Equiv.cast_symm /-
@[simp]
theorem cast_symm {α β} (h : α = β) : (Equiv.cast h).symm = Equiv.cast h.symm :=
  rfl
#align equiv.cast_symm Equiv.cast_symm
-/

#print Equiv.cast_refl /-
@[simp]
theorem cast_refl {α} (h : α = α := rfl) : Equiv.cast h = Equiv.refl α :=
  rfl
#align equiv.cast_refl Equiv.cast_refl
-/

#print Equiv.cast_trans /-
@[simp]
theorem cast_trans {α β γ} (h : α = β) (h2 : β = γ) :
    (Equiv.cast h).trans (Equiv.cast h2) = Equiv.cast (h.trans h2) :=
  ext fun x => by
    substs h h2
    rfl
#align equiv.cast_trans Equiv.cast_trans
-/

theorem cast_eq_iff_hEq {α β} (h : α = β) {a : α} {b : β} : Equiv.cast h a = b ↔ HEq a b :=
  by
  subst h
  simp
#align equiv.cast_eq_iff_heq Equiv.cast_eq_iff_hEq

/- warning: equiv.symm_apply_eq -> Equiv.symm_apply_eq is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} (e : Equiv.{u1, u2} α β) {x : β} {y : α}, Iff (Eq.{u1} α (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) x) y) (Eq.{u2} β x (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e y))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} (e : Equiv.{u2, u1} α β) {x : β} {y : (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) x}, Iff (Eq.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) x) (FunLike.coe.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β e) x) y) (Eq.{u1} β x (FunLike.coe.{max (max 1 u1) u2, u2, u1} (Equiv.{u2, u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) e y))
Case conversion may be inaccurate. Consider using '#align equiv.symm_apply_eq Equiv.symm_apply_eqₓ'. -/
theorem symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = y ↔ x = e y :=
  ⟨fun H => by simp [H.symm], fun H => by simp [H]⟩
#align equiv.symm_apply_eq Equiv.symm_apply_eq

/- warning: equiv.eq_symm_apply -> Equiv.eq_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} (e : Equiv.{u1, u2} α β) {x : β} {y : α}, Iff (Eq.{u1} α y (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e) x)) (Eq.{u2} β (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e y) x)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} (e : Equiv.{u2, u1} α β) {x : β} {y : (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) x}, Iff (Eq.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) x) y (FunLike.coe.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β e) x)) (Eq.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) y) (FunLike.coe.{max (max 1 u1) u2, u2, u1} (Equiv.{u2, u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u2, u1} (Equiv.{u2, u1} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u2, u1} (Equiv.{u2, u1} α β) α β (Equiv.instEquivLikeEquiv.{u2, u1} α β))) e y) x)
Case conversion may be inaccurate. Consider using '#align equiv.eq_symm_apply Equiv.eq_symm_applyₓ'. -/
theorem eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm x ↔ e y = x :=
  (eq_comm.trans e.symm_apply_eq).trans eq_comm
#align equiv.eq_symm_apply Equiv.eq_symm_apply

/- warning: equiv.symm_symm -> Equiv.symm_symm is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} (e : Equiv.{u1, u2} α β), Eq.{max 1 (imax u1 u2) (imax u2 u1)} (Equiv.{u1, u2} α β) (Equiv.symm.{u2, u1} β α (Equiv.symm.{u1, u2} α β e)) e
but is expected to have type
  forall {α : Sort.{u1}} {β : Sort.{u2}} (e : Equiv.{u1, u2} α β), Eq.{max (max 1 u1) u2} (Equiv.{u1, u2} α β) (Equiv.symm.{u2, u1} β α (Equiv.symm.{u1, u2} α β e)) e
Case conversion may be inaccurate. Consider using '#align equiv.symm_symm Equiv.symm_symmₓ'. -/
@[simp]
theorem symm_symm (e : α ≃ β) : e.symm.symm = e :=
  by
  cases e
  rfl
#align equiv.symm_symm Equiv.symm_symm

/- warning: equiv.trans_refl -> Equiv.trans_refl is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} (e : Equiv.{u1, u2} α β), Eq.{max 1 (imax u1 u2) (imax u2 u1)} (Equiv.{u1, u2} α β) (Equiv.trans.{u1, u2, u2} α β β e (Equiv.refl.{u2} β)) e
but is expected to have type
  forall {α : Sort.{u1}} {β : Sort.{u2}} (e : Equiv.{u1, u2} α β), Eq.{max (max 1 u1) u2} (Equiv.{u1, u2} α β) (Equiv.trans.{u1, u2, u2} α β β e (Equiv.refl.{u2} β)) e
Case conversion may be inaccurate. Consider using '#align equiv.trans_refl Equiv.trans_reflₓ'. -/
@[simp]
theorem trans_refl (e : α ≃ β) : e.trans (Equiv.refl β) = e :=
  by
  cases e
  rfl
#align equiv.trans_refl Equiv.trans_refl

#print Equiv.refl_symm /-
@[simp]
theorem refl_symm : (Equiv.refl α).symm = Equiv.refl α :=
  rfl
#align equiv.refl_symm Equiv.refl_symm
-/

/- warning: equiv.refl_trans -> Equiv.refl_trans is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} (e : Equiv.{u1, u2} α β), Eq.{max 1 (imax u1 u2) (imax u2 u1)} (Equiv.{u1, u2} α β) (Equiv.trans.{u1, u1, u2} α α β (Equiv.refl.{u1} α) e) e
but is expected to have type
  forall {α : Sort.{u1}} {β : Sort.{u2}} (e : Equiv.{u1, u2} α β), Eq.{max (max 1 u1) u2} (Equiv.{u1, u2} α β) (Equiv.trans.{u1, u1, u2} α α β (Equiv.refl.{u1} α) e) e
Case conversion may be inaccurate. Consider using '#align equiv.refl_trans Equiv.refl_transₓ'. -/
@[simp]
theorem refl_trans (e : α ≃ β) : (Equiv.refl α).trans e = e :=
  by
  cases e
  rfl
#align equiv.refl_trans Equiv.refl_trans

#print Equiv.symm_trans_self /-
@[simp]
theorem symm_trans_self (e : α ≃ β) : e.symm.trans e = Equiv.refl β :=
  ext (by simp)
#align equiv.symm_trans_self Equiv.symm_trans_self
-/

#print Equiv.self_trans_symm /-
@[simp]
theorem self_trans_symm (e : α ≃ β) : e.trans e.symm = Equiv.refl α :=
  ext (by simp)
#align equiv.self_trans_symm Equiv.self_trans_symm
-/

/- warning: equiv.trans_assoc -> Equiv.trans_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} {δ : Sort.{u4}} (ab : Equiv.{u1, u2} α β) (bc : Equiv.{u2, u3} β γ) (cd : Equiv.{u3, u4} γ δ), Eq.{max 1 (imax u1 u4) (imax u4 u1)} (Equiv.{u1, u4} α δ) (Equiv.trans.{u1, u3, u4} α γ δ (Equiv.trans.{u1, u2, u3} α β γ ab bc) cd) (Equiv.trans.{u1, u2, u4} α β δ ab (Equiv.trans.{u2, u3, u4} β γ δ bc cd))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u3}} {γ : Sort.{u4}} {δ : Sort.{u1}} (ab : Equiv.{u2, u3} α β) (bc : Equiv.{u3, u4} β γ) (cd : Equiv.{u4, u1} γ δ), Eq.{max (max 1 u2) u1} (Equiv.{u2, u1} α δ) (Equiv.trans.{u2, u4, u1} α γ δ (Equiv.trans.{u2, u3, u4} α β γ ab bc) cd) (Equiv.trans.{u2, u3, u1} α β δ ab (Equiv.trans.{u3, u4, u1} β γ δ bc cd))
Case conversion may be inaccurate. Consider using '#align equiv.trans_assoc Equiv.trans_assocₓ'. -/
theorem trans_assoc {δ} (ab : α ≃ β) (bc : β ≃ γ) (cd : γ ≃ δ) :
    (ab.trans bc).trans cd = ab.trans (bc.trans cd) :=
  Equiv.ext fun a => rfl
#align equiv.trans_assoc Equiv.trans_assoc

#print Equiv.leftInverse_symm /-
theorem leftInverse_symm (f : Equiv α β) : LeftInverse f.symm f :=
  f.left_inv
#align equiv.left_inverse_symm Equiv.leftInverse_symm
-/

#print Equiv.rightInverse_symm /-
theorem rightInverse_symm (f : Equiv α β) : Function.RightInverse f.symm f :=
  f.right_inv
#align equiv.right_inverse_symm Equiv.rightInverse_symm
-/

#print Equiv.injective_comp /-
theorem injective_comp (e : α ≃ β) (f : β → γ) : Injective (f ∘ e) ↔ Injective f :=
  EquivLike.injective_comp e f
#align equiv.injective_comp Equiv.injective_comp
-/

#print Equiv.comp_injective /-
theorem comp_injective (f : α → β) (e : β ≃ γ) : Injective (e ∘ f) ↔ Injective f :=
  EquivLike.comp_injective f e
#align equiv.comp_injective Equiv.comp_injective
-/

#print Equiv.surjective_comp /-
theorem surjective_comp (e : α ≃ β) (f : β → γ) : Surjective (f ∘ e) ↔ Surjective f :=
  EquivLike.surjective_comp e f
#align equiv.surjective_comp Equiv.surjective_comp
-/

#print Equiv.comp_surjective /-
theorem comp_surjective (f : α → β) (e : β ≃ γ) : Surjective (e ∘ f) ↔ Surjective f :=
  EquivLike.comp_surjective f e
#align equiv.comp_surjective Equiv.comp_surjective
-/

#print Equiv.bijective_comp /-
theorem bijective_comp (e : α ≃ β) (f : β → γ) : Bijective (f ∘ e) ↔ Bijective f :=
  EquivLike.bijective_comp e f
#align equiv.bijective_comp Equiv.bijective_comp
-/

#print Equiv.comp_bijective /-
theorem comp_bijective (f : α → β) (e : β ≃ γ) : Bijective (e ∘ f) ↔ Bijective f :=
  EquivLike.comp_bijective f e
#align equiv.comp_bijective Equiv.comp_bijective
-/

/- warning: equiv.equiv_congr -> Equiv.equivCongr is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} {δ : Sort.{u4}}, (Equiv.{u1, u2} α β) -> (Equiv.{u3, u4} γ δ) -> (Equiv.{max 1 (imax u1 u3) (imax u3 u1), max 1 (imax u2 u4) (imax u4 u2)} (Equiv.{u1, u3} α γ) (Equiv.{u2, u4} β δ))
but is expected to have type
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} {δ : Sort.{u4}}, (Equiv.{u1, u2} α β) -> (Equiv.{u3, u4} γ δ) -> (Equiv.{max (max 1 u3) u1, max (max 1 u4) u2} (Equiv.{u1, u3} α γ) (Equiv.{u2, u4} β δ))
Case conversion may be inaccurate. Consider using '#align equiv.equiv_congr Equiv.equivCongrₓ'. -/
/-- If `α` is equivalent to `β` and `γ` is equivalent to `δ`, then the type of equivalences `α ≃ γ`
is equivalent to the type of equivalences `β ≃ δ`. -/
def equivCongr {δ} (ab : α ≃ β) (cd : γ ≃ δ) : α ≃ γ ≃ (β ≃ δ) :=
  ⟨fun ac => (ab.symm.trans ac).trans cd, fun bd => ab.trans <| bd.trans <| cd.symm, fun ac =>
    by
    ext x
    simp, fun ac => by
    ext x
    simp⟩
#align equiv.equiv_congr Equiv.equivCongr

/- warning: equiv.equiv_congr_refl -> Equiv.equivCongr_refl is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}}, Eq.{max 1 (imax u1 u2) (imax u2 u1)} (Equiv.{max 1 (imax u1 u2) (imax u2 u1), max 1 (imax u1 u2) (imax u2 u1)} (Equiv.{u1, u2} α β) (Equiv.{u1, u2} α β)) (Equiv.equivCongr.{u1, u1, u2, u2} α α β β (Equiv.refl.{u1} α) (Equiv.refl.{u2} β)) (Equiv.refl.{max 1 (imax u1 u2) (imax u2 u1)} (Equiv.{u1, u2} α β))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}}, Eq.{max (max 1 u2) u1} (Equiv.{max (max 1 u1) u2, max (max 1 u1) u2} (Equiv.{u2, u1} α β) (Equiv.{u2, u1} α β)) (Equiv.equivCongr.{u2, u2, u1, u1} α α β β (Equiv.refl.{u2} α) (Equiv.refl.{u1} β)) (Equiv.refl.{max (max 1 u1) u2} (Equiv.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align equiv.equiv_congr_refl Equiv.equivCongr_reflₓ'. -/
@[simp]
theorem equivCongr_refl {α β} : (Equiv.refl α).equivCongr (Equiv.refl β) = Equiv.refl (α ≃ β) :=
  by
  ext
  rfl
#align equiv.equiv_congr_refl Equiv.equivCongr_refl

/- warning: equiv.equiv_congr_symm -> Equiv.equivCongr_symm is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} {δ : Sort.{u4}} (ab : Equiv.{u1, u2} α β) (cd : Equiv.{u3, u4} γ δ), Eq.{max 1 (max (max 1 (imax u2 u4) (imax u4 u2)) 1 (imax u1 u3) (imax u3 u1)) (max 1 (imax u1 u3) (imax u3 u1)) 1 (imax u2 u4) (imax u4 u2)} (Equiv.{max 1 (imax u2 u4) (imax u4 u2), max 1 (imax u1 u3) (imax u3 u1)} (Equiv.{u2, u4} β δ) (Equiv.{u1, u3} α γ)) (Equiv.symm.{max 1 (imax u1 u3) (imax u3 u1), max 1 (imax u2 u4) (imax u4 u2)} (Equiv.{u1, u3} α γ) (Equiv.{u2, u4} β δ) (Equiv.equivCongr.{u1, u2, u3, u4} α β γ δ ab cd)) (Equiv.equivCongr.{u2, u1, u4, u3} β α δ γ (Equiv.symm.{u1, u2} α β ab) (Equiv.symm.{u3, u4} γ δ cd))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u3}} {γ : Sort.{u4}} {δ : Sort.{u1}} (ab : Equiv.{u2, u3} α β) (cd : Equiv.{u4, u1} γ δ), Eq.{max (max (max (max 1 u2) u3) u4) u1} (Equiv.{max (max 1 u3) u1, max (max 1 u2) u4} (Equiv.{u3, u1} β δ) (Equiv.{u2, u4} α γ)) (Equiv.symm.{max (max 1 u2) u4, max (max 1 u3) u1} (Equiv.{u2, u4} α γ) (Equiv.{u3, u1} β δ) (Equiv.equivCongr.{u2, u3, u4, u1} α β γ δ ab cd)) (Equiv.equivCongr.{u3, u2, u1, u4} β α δ γ (Equiv.symm.{u2, u3} α β ab) (Equiv.symm.{u4, u1} γ δ cd))
Case conversion may be inaccurate. Consider using '#align equiv.equiv_congr_symm Equiv.equivCongr_symmₓ'. -/
@[simp]
theorem equivCongr_symm {δ} (ab : α ≃ β) (cd : γ ≃ δ) :
    (ab.equivCongr cd).symm = ab.symm.equivCongr cd.symm :=
  by
  ext
  rfl
#align equiv.equiv_congr_symm Equiv.equivCongr_symm

/- warning: equiv.equiv_congr_trans -> Equiv.equivCongr_trans is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} {δ : Sort.{u4}} {ε : Sort.{u5}} {ζ : Sort.{u6}} (ab : Equiv.{u1, u2} α β) (de : Equiv.{u4, u5} δ ε) (bc : Equiv.{u2, u3} β γ) (ef : Equiv.{u5, u6} ε ζ), Eq.{max 1 (max (max 1 (imax u1 u4) (imax u4 u1)) 1 (imax u3 u6) (imax u6 u3)) (max 1 (imax u3 u6) (imax u6 u3)) 1 (imax u1 u4) (imax u4 u1)} (Equiv.{max 1 (imax u1 u4) (imax u4 u1), max 1 (imax u3 u6) (imax u6 u3)} (Equiv.{u1, u4} α δ) (Equiv.{u3, u6} γ ζ)) (Equiv.trans.{max 1 (imax u1 u4) (imax u4 u1), max 1 (imax u2 u5) (imax u5 u2), max 1 (imax u3 u6) (imax u6 u3)} (Equiv.{u1, u4} α δ) (Equiv.{u2, u5} β ε) (Equiv.{u3, u6} γ ζ) (Equiv.equivCongr.{u1, u2, u4, u5} α β δ ε ab de) (Equiv.equivCongr.{u2, u3, u5, u6} β γ ε ζ bc ef)) (Equiv.equivCongr.{u1, u3, u4, u6} α γ δ ζ (Equiv.trans.{u1, u2, u3} α β γ ab bc) (Equiv.trans.{u4, u5, u6} δ ε ζ de ef))
but is expected to have type
  forall {α : Sort.{u4}} {β : Sort.{u5}} {γ : Sort.{u6}} {δ : Sort.{u3}} {ε : Sort.{u2}} {ζ : Sort.{u1}} (ab : Equiv.{u4, u5} α β) (de : Equiv.{u3, u2} δ ε) (bc : Equiv.{u5, u6} β γ) (ef : Equiv.{u2, u1} ε ζ), Eq.{max (max (max (max 1 u4) u6) u3) u1} (Equiv.{max (max 1 u4) u3, max (max 1 u6) u1} (Equiv.{u4, u3} α δ) (Equiv.{u6, u1} γ ζ)) (Equiv.trans.{max (max 1 u4) u3, max (max 1 u5) u2, max (max 1 u6) u1} (Equiv.{u4, u3} α δ) (Equiv.{u5, u2} β ε) (Equiv.{u6, u1} γ ζ) (Equiv.equivCongr.{u4, u5, u3, u2} α β δ ε ab de) (Equiv.equivCongr.{u5, u6, u2, u1} β γ ε ζ bc ef)) (Equiv.equivCongr.{u4, u6, u3, u1} α γ δ ζ (Equiv.trans.{u4, u5, u6} α β γ ab bc) (Equiv.trans.{u3, u2, u1} δ ε ζ de ef))
Case conversion may be inaccurate. Consider using '#align equiv.equiv_congr_trans Equiv.equivCongr_transₓ'. -/
@[simp]
theorem equivCongr_trans {δ ε ζ} (ab : α ≃ β) (de : δ ≃ ε) (bc : β ≃ γ) (ef : ε ≃ ζ) :
    (ab.equivCongr de).trans (bc.equivCongr ef) = (ab.trans bc).equivCongr (de.trans ef) :=
  by
  ext
  rfl
#align equiv.equiv_congr_trans Equiv.equivCongr_trans

/- warning: equiv.equiv_congr_refl_left -> Equiv.equivCongr_refl_left is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} (bg : Equiv.{u2, u3} β γ) (e : Equiv.{u1, u2} α β), Eq.{max 1 (imax u1 u3) (imax u3 u1)} (Equiv.{u1, u3} α γ) (coeFn.{max 1 (max (max 1 (imax u1 u2) (imax u2 u1)) 1 (imax u1 u3) (imax u3 u1)) (max 1 (imax u1 u3) (imax u3 u1)) 1 (imax u1 u2) (imax u2 u1), max (max 1 (imax u1 u2) (imax u2 u1)) 1 (imax u1 u3) (imax u3 u1)} (Equiv.{max 1 (imax u1 u2) (imax u2 u1), max 1 (imax u1 u3) (imax u3 u1)} (Equiv.{u1, u2} α β) (Equiv.{u1, u3} α γ)) (fun (_x : Equiv.{max 1 (imax u1 u2) (imax u2 u1), max 1 (imax u1 u3) (imax u3 u1)} (Equiv.{u1, u2} α β) (Equiv.{u1, u3} α γ)) => (Equiv.{u1, u2} α β) -> (Equiv.{u1, u3} α γ)) (Equiv.hasCoeToFun.{max 1 (imax u1 u2) (imax u2 u1), max 1 (imax u1 u3) (imax u3 u1)} (Equiv.{u1, u2} α β) (Equiv.{u1, u3} α γ)) (Equiv.equivCongr.{u1, u1, u2, u3} α α β γ (Equiv.refl.{u1} α) bg) e) (Equiv.trans.{u1, u2, u3} α β γ e bg)
but is expected to have type
  forall {α : Sort.{u3}} {β : Sort.{u2}} {γ : Sort.{u1}} (bg : Equiv.{u2, u1} β γ) (e : Equiv.{u3, u2} α β), Eq.{max (max 1 u1) u3} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Equiv.{u3, u2} α β) => Equiv.{u3, u1} α γ) e) (FunLike.coe.{max (max (max 1 u1) u2) u3, max (max 1 u2) u3, max (max 1 u1) u3} (Equiv.{max (max 1 u2) u3, max (max 1 u1) u3} (Equiv.{u3, u2} α β) (Equiv.{u3, u1} α γ)) (Equiv.{u3, u2} α β) (fun (_x : Equiv.{u3, u2} α β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Equiv.{u3, u2} α β) => Equiv.{u3, u1} α γ) _x) (EmbeddingLike.toFunLike.{max (max (max 1 u1) u2) u3, max (max 1 u2) u3, max (max 1 u1) u3} (Equiv.{max (max 1 u2) u3, max (max 1 u1) u3} (Equiv.{u3, u2} α β) (Equiv.{u3, u1} α γ)) (Equiv.{u3, u2} α β) (Equiv.{u3, u1} α γ) (EquivLike.toEmbeddingLike.{max (max (max 1 u1) u2) u3, max (max 1 u2) u3, max (max 1 u1) u3} (Equiv.{max (max 1 u2) u3, max (max 1 u1) u3} (Equiv.{u3, u2} α β) (Equiv.{u3, u1} α γ)) (Equiv.{u3, u2} α β) (Equiv.{u3, u1} α γ) (Equiv.instEquivLikeEquiv.{max (max 1 u2) u3, max (max 1 u1) u3} (Equiv.{u3, u2} α β) (Equiv.{u3, u1} α γ)))) (Equiv.equivCongr.{u3, u3, u2, u1} α α β γ (Equiv.refl.{u3} α) bg) e) (Equiv.trans.{u3, u2, u1} α β γ e bg)
Case conversion may be inaccurate. Consider using '#align equiv.equiv_congr_refl_left Equiv.equivCongr_refl_leftₓ'. -/
@[simp]
theorem equivCongr_refl_left {α β γ} (bg : β ≃ γ) (e : α ≃ β) :
    (Equiv.refl α).equivCongr bg e = e.trans bg :=
  rfl
#align equiv.equiv_congr_refl_left Equiv.equivCongr_refl_left

/- warning: equiv.equiv_congr_refl_right -> Equiv.equivCongr_refl_right is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} (ab : Equiv.{u1, u2} α β) (e : Equiv.{u1, u2} α β), Eq.{max 1 u2} (Equiv.{u2, u2} β β) (coeFn.{max 1 (max (max 1 (imax u1 u2) (imax u2 u1)) 1 u2) (max 1 u2) 1 (imax u1 u2) (imax u2 u1), max (max 1 (imax u1 u2) (imax u2 u1)) 1 u2} (Equiv.{max 1 (imax u1 u2) (imax u2 u1), max 1 u2} (Equiv.{u1, u2} α β) (Equiv.{u2, u2} β β)) (fun (_x : Equiv.{max 1 (imax u1 u2) (imax u2 u1), max 1 u2} (Equiv.{u1, u2} α β) (Equiv.{u2, u2} β β)) => (Equiv.{u1, u2} α β) -> (Equiv.{u2, u2} β β)) (Equiv.hasCoeToFun.{max 1 (imax u1 u2) (imax u2 u1), max 1 u2} (Equiv.{u1, u2} α β) (Equiv.{u2, u2} β β)) (Equiv.equivCongr.{u1, u2, u2, u2} α β β β ab (Equiv.refl.{u2} β)) e) (Equiv.trans.{u2, u1, u2} β α β (Equiv.symm.{u1, u2} α β ab) e)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} (ab : Equiv.{u2, u1} α β) (e : Equiv.{u2, u1} α β), Eq.{max 1 u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Equiv.{u2, u1} α β) => Equiv.{u1, u1} β β) e) (FunLike.coe.{max (max 1 u1) u2, max (max 1 u1) u2, max 1 u1} (Equiv.{max (max 1 u1) u2, max 1 u1} (Equiv.{u2, u1} α β) (Equiv.{u1, u1} β β)) (Equiv.{u2, u1} α β) (fun (_x : Equiv.{u2, u1} α β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Equiv.{u2, u1} α β) => Equiv.{u1, u1} β β) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, max (max 1 u1) u2, max 1 u1} (Equiv.{max (max 1 u1) u2, max 1 u1} (Equiv.{u2, u1} α β) (Equiv.{u1, u1} β β)) (Equiv.{u2, u1} α β) (Equiv.{u1, u1} β β) (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, max (max 1 u1) u2, max 1 u1} (Equiv.{max (max 1 u1) u2, max 1 u1} (Equiv.{u2, u1} α β) (Equiv.{u1, u1} β β)) (Equiv.{u2, u1} α β) (Equiv.{u1, u1} β β) (Equiv.instEquivLikeEquiv.{max (max 1 u1) u2, max 1 u1} (Equiv.{u2, u1} α β) (Equiv.{u1, u1} β β)))) (Equiv.equivCongr.{u2, u1, u1, u1} α β β β ab (Equiv.refl.{u1} β)) e) (Equiv.trans.{u1, u2, u1} β α β (Equiv.symm.{u2, u1} α β ab) e)
Case conversion may be inaccurate. Consider using '#align equiv.equiv_congr_refl_right Equiv.equivCongr_refl_rightₓ'. -/
@[simp]
theorem equivCongr_refl_right {α β} (ab e : α ≃ β) :
    ab.equivCongr (Equiv.refl β) e = ab.symm.trans e :=
  rfl
#align equiv.equiv_congr_refl_right Equiv.equivCongr_refl_right

/- warning: equiv.equiv_congr_apply_apply -> Equiv.equivCongr_apply_apply is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} {δ : Sort.{u4}} (ab : Equiv.{u1, u2} α β) (cd : Equiv.{u3, u4} γ δ) (e : Equiv.{u1, u3} α γ) (x : β), Eq.{u4} δ (coeFn.{max 1 (imax u2 u4) (imax u4 u2), imax u2 u4} (Equiv.{u2, u4} β δ) (fun (_x : Equiv.{u2, u4} β δ) => β -> δ) (Equiv.hasCoeToFun.{u2, u4} β δ) (coeFn.{max 1 (max (max 1 (imax u1 u3) (imax u3 u1)) 1 (imax u2 u4) (imax u4 u2)) (max 1 (imax u2 u4) (imax u4 u2)) 1 (imax u1 u3) (imax u3 u1), max (max 1 (imax u1 u3) (imax u3 u1)) 1 (imax u2 u4) (imax u4 u2)} (Equiv.{max 1 (imax u1 u3) (imax u3 u1), max 1 (imax u2 u4) (imax u4 u2)} (Equiv.{u1, u3} α γ) (Equiv.{u2, u4} β δ)) (fun (_x : Equiv.{max 1 (imax u1 u3) (imax u3 u1), max 1 (imax u2 u4) (imax u4 u2)} (Equiv.{u1, u3} α γ) (Equiv.{u2, u4} β δ)) => (Equiv.{u1, u3} α γ) -> (Equiv.{u2, u4} β δ)) (Equiv.hasCoeToFun.{max 1 (imax u1 u3) (imax u3 u1), max 1 (imax u2 u4) (imax u4 u2)} (Equiv.{u1, u3} α γ) (Equiv.{u2, u4} β δ)) (Equiv.equivCongr.{u1, u2, u3, u4} α β γ δ ab cd) e) x) (coeFn.{max 1 (imax u3 u4) (imax u4 u3), imax u3 u4} (Equiv.{u3, u4} γ δ) (fun (_x : Equiv.{u3, u4} γ δ) => γ -> δ) (Equiv.hasCoeToFun.{u3, u4} γ δ) cd (coeFn.{max 1 (imax u1 u3) (imax u3 u1), imax u1 u3} (Equiv.{u1, u3} α γ) (fun (_x : Equiv.{u1, u3} α γ) => α -> γ) (Equiv.hasCoeToFun.{u1, u3} α γ) e (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β ab) x)))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u3}} {γ : Sort.{u4}} {δ : Sort.{u1}} (ab : Equiv.{u2, u3} α β) (cd : Equiv.{u4, u1} γ δ) (e : Equiv.{u2, u4} α γ) (x : β), Eq.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => δ) x) (FunLike.coe.{max (max 1 u3) u1, u3, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Equiv.{u2, u4} α γ) => Equiv.{u3, u1} β δ) e) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => δ) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u1, u3, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Equiv.{u2, u4} α γ) => Equiv.{u3, u1} β δ) e) β δ (EquivLike.toEmbeddingLike.{max (max 1 u3) u1, u3, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Equiv.{u2, u4} α γ) => Equiv.{u3, u1} β δ) e) β δ (Equiv.instEquivLikeEquiv.{u3, u1} β δ))) (FunLike.coe.{max (max (max (max 1 u2) u3) u4) u1, max (max 1 u2) u4, max (max 1 u3) u1} (Equiv.{max (max 1 u4) u2, max (max 1 u1) u3} (Equiv.{u2, u4} α γ) (Equiv.{u3, u1} β δ)) (Equiv.{u2, u4} α γ) (fun (_x : Equiv.{u2, u4} α γ) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Equiv.{u2, u4} α γ) => Equiv.{u3, u1} β δ) _x) (EmbeddingLike.toFunLike.{max (max (max (max 1 u2) u3) u4) u1, max (max 1 u2) u4, max (max 1 u3) u1} (Equiv.{max (max 1 u4) u2, max (max 1 u1) u3} (Equiv.{u2, u4} α γ) (Equiv.{u3, u1} β δ)) (Equiv.{u2, u4} α γ) (Equiv.{u3, u1} β δ) (EquivLike.toEmbeddingLike.{max (max (max (max 1 u2) u3) u4) u1, max (max 1 u2) u4, max (max 1 u3) u1} (Equiv.{max (max 1 u4) u2, max (max 1 u1) u3} (Equiv.{u2, u4} α γ) (Equiv.{u3, u1} β δ)) (Equiv.{u2, u4} α γ) (Equiv.{u3, u1} β δ) (Equiv.instEquivLikeEquiv.{max (max 1 u2) u4, max (max 1 u3) u1} (Equiv.{u2, u4} α γ) (Equiv.{u3, u1} β δ)))) (Equiv.equivCongr.{u2, u3, u4, u1} α β γ δ ab cd) e) x) (FunLike.coe.{max (max 1 u4) u1, u4, u1} (Equiv.{u4, u1} γ δ) γ (fun (_x : γ) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : γ) => δ) _x) (EmbeddingLike.toFunLike.{max (max 1 u4) u1, u4, u1} (Equiv.{u4, u1} γ δ) γ δ (EquivLike.toEmbeddingLike.{max (max 1 u4) u1, u4, u1} (Equiv.{u4, u1} γ δ) γ δ (Equiv.instEquivLikeEquiv.{u4, u1} γ δ))) cd (FunLike.coe.{max (max 1 u2) u4, u2, u4} (Equiv.{u2, u4} α γ) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => γ) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u4, u2, u4} (Equiv.{u2, u4} α γ) α γ (EquivLike.toEmbeddingLike.{max (max 1 u2) u4, u2, u4} (Equiv.{u2, u4} α γ) α γ (Equiv.instEquivLikeEquiv.{u2, u4} α γ))) e (FunLike.coe.{max (max 1 u2) u3, u3, u2} (Equiv.{u3, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u3, u3, u2} (Equiv.{u3, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u3, u3, u2} (Equiv.{u3, u2} β α) β α (Equiv.instEquivLikeEquiv.{u3, u2} β α))) (Equiv.symm.{u2, u3} α β ab) x)))
Case conversion may be inaccurate. Consider using '#align equiv.equiv_congr_apply_apply Equiv.equivCongr_apply_applyₓ'. -/
@[simp]
theorem equivCongr_apply_apply {δ} (ab : α ≃ β) (cd : γ ≃ δ) (e : α ≃ γ) (x) :
    ab.equivCongr cd e x = cd (e (ab.symm x)) :=
  rfl
#align equiv.equiv_congr_apply_apply Equiv.equivCongr_apply_apply

section PermCongr

variable {α' β' : Type _} (e : α' ≃ β')

#print Equiv.permCongr /-
/-- If `α` is equivalent to `β`, then `perm α` is equivalent to `perm β`. -/
def permCongr : Perm α' ≃ Perm β' :=
  equivCongr e e
#align equiv.perm_congr Equiv.permCongr
-/

/- warning: equiv.perm_congr_def -> Equiv.permCongr_def is a dubious translation:
lean 3 declaration is
  forall {α' : Type.{u1}} {β' : Type.{u2}} (e : Equiv.{succ u1, succ u2} α' β') (p : Equiv.Perm.{succ u1} α'), Eq.{succ u2} (Equiv.Perm.{succ u2} β') (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} (Equiv.Perm.{succ u1} α') (Equiv.Perm.{succ u2} β')) (fun (_x : Equiv.{succ u1, succ u2} (Equiv.Perm.{succ u1} α') (Equiv.Perm.{succ u2} β')) => (Equiv.Perm.{succ u1} α') -> (Equiv.Perm.{succ u2} β')) (Equiv.hasCoeToFun.{succ u1, succ u2} (Equiv.Perm.{succ u1} α') (Equiv.Perm.{succ u2} β')) (Equiv.permCongr.{u1, u2} α' β' e) p) (Equiv.trans.{succ u2, succ u1, succ u2} β' α' β' (Equiv.trans.{succ u2, succ u1, succ u1} β' α' α' (Equiv.symm.{succ u1, succ u2} α' β' e) p) e)
but is expected to have type
  forall {α' : Type.{u2}} {β' : Type.{u1}} (e : Equiv.{succ u2, succ u1} α' β') (p : Equiv.Perm.{succ u2} α'), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Equiv.Perm.{succ u2} α') => Equiv.Perm.{succ u1} β') p) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')) (Equiv.Perm.{succ u2} α') (fun (_x : Equiv.Perm.{succ u2} α') => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Equiv.Perm.{succ u2} α') => Equiv.Perm.{succ u1} β') _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')) (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β') (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')) (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β') (Equiv.instEquivLikeEquiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')))) (Equiv.permCongr.{u2, u1} α' β' e) p) (Equiv.trans.{succ u1, succ u2, succ u1} β' α' β' (Equiv.trans.{succ u1, succ u2, succ u2} β' α' α' (Equiv.symm.{succ u2, succ u1} α' β' e) p) e)
Case conversion may be inaccurate. Consider using '#align equiv.perm_congr_def Equiv.permCongr_defₓ'. -/
theorem permCongr_def (p : Equiv.Perm α') : e.permCongr p = (e.symm.trans p).trans e :=
  rfl
#align equiv.perm_congr_def Equiv.permCongr_def

#print Equiv.permCongr_refl /-
@[simp]
theorem permCongr_refl : e.permCongr (Equiv.refl _) = Equiv.refl _ := by simp [perm_congr_def]
#align equiv.perm_congr_refl Equiv.permCongr_refl
-/

/- warning: equiv.perm_congr_symm -> Equiv.permCongr_symm is a dubious translation:
lean 3 declaration is
  forall {α' : Type.{u1}} {β' : Type.{u2}} (e : Equiv.{succ u1, succ u2} α' β'), Eq.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2)} (Equiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} β') (Equiv.Perm.{succ u1} α')) (Equiv.symm.{succ u1, succ u2} (Equiv.Perm.{succ u1} α') (Equiv.Perm.{succ u2} β') (Equiv.permCongr.{u1, u2} α' β' e)) (Equiv.permCongr.{u2, u1} β' α' (Equiv.symm.{succ u1, succ u2} α' β' e))
but is expected to have type
  forall {α' : Type.{u2}} {β' : Type.{u1}} (e : Equiv.{succ u2, succ u1} α' β'), Eq.{max (succ u2) (succ u1)} (Equiv.{succ u1, succ u2} (Equiv.Perm.{succ u1} β') (Equiv.Perm.{succ u2} α')) (Equiv.symm.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β') (Equiv.permCongr.{u2, u1} α' β' e)) (Equiv.permCongr.{u1, u2} β' α' (Equiv.symm.{succ u2, succ u1} α' β' e))
Case conversion may be inaccurate. Consider using '#align equiv.perm_congr_symm Equiv.permCongr_symmₓ'. -/
@[simp]
theorem permCongr_symm : e.permCongr.symm = e.symm.permCongr :=
  rfl
#align equiv.perm_congr_symm Equiv.permCongr_symm

/- warning: equiv.perm_congr_apply -> Equiv.permCongr_apply is a dubious translation:
lean 3 declaration is
  forall {α' : Type.{u1}} {β' : Type.{u2}} (e : Equiv.{succ u1, succ u2} α' β') (p : Equiv.Perm.{succ u1} α') (x : β'), Eq.{succ u2} β' (coeFn.{succ u2, succ u2} (Equiv.Perm.{succ u2} β') (fun (_x : Equiv.{succ u2, succ u2} β' β') => β' -> β') (Equiv.hasCoeToFun.{succ u2, succ u2} β' β') (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} (Equiv.Perm.{succ u1} α') (Equiv.Perm.{succ u2} β')) (fun (_x : Equiv.{succ u1, succ u2} (Equiv.Perm.{succ u1} α') (Equiv.Perm.{succ u2} β')) => (Equiv.Perm.{succ u1} α') -> (Equiv.Perm.{succ u2} β')) (Equiv.hasCoeToFun.{succ u1, succ u2} (Equiv.Perm.{succ u1} α') (Equiv.Perm.{succ u2} β')) (Equiv.permCongr.{u1, u2} α' β' e) p) x) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α' β') (fun (_x : Equiv.{succ u1, succ u2} α' β') => α' -> β') (Equiv.hasCoeToFun.{succ u1, succ u2} α' β') e (coeFn.{succ u1, succ u1} (Equiv.Perm.{succ u1} α') (fun (_x : Equiv.{succ u1, succ u1} α' α') => α' -> α') (Equiv.hasCoeToFun.{succ u1, succ u1} α' α') p (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β' α') (fun (_x : Equiv.{succ u2, succ u1} β' α') => β' -> α') (Equiv.hasCoeToFun.{succ u2, succ u1} β' α') (Equiv.symm.{succ u1, succ u2} α' β' e) x)))
but is expected to have type
  forall {α' : Type.{u2}} {β' : Type.{u1}} (e : Equiv.{succ u2, succ u1} α' β') (p : Equiv.Perm.{succ u2} α') (x : β'), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β') => β') x) (FunLike.coe.{succ u1, succ u1, succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Equiv.Perm.{succ u2} α') => Equiv.Perm.{succ u1} β') p) β' (fun (_x : β') => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β') => β') _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Equiv.Perm.{succ u2} α') => Equiv.Perm.{succ u1} β') p) β' β' (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Equiv.Perm.{succ u2} α') => Equiv.Perm.{succ u1} β') p) β' β' (Equiv.instEquivLikeEquiv.{succ u1, succ u1} β' β'))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')) (Equiv.Perm.{succ u2} α') (fun (_x : Equiv.Perm.{succ u2} α') => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Equiv.Perm.{succ u2} α') => Equiv.Perm.{succ u1} β') _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')) (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β') (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')) (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β') (Equiv.instEquivLikeEquiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')))) (Equiv.permCongr.{u2, u1} α' β' e) p) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α' β') α' (fun (_x : α') => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α') => β') _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α' β') α' β' (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α' β') α' β' (Equiv.instEquivLikeEquiv.{succ u2, succ u1} α' β'))) e (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.Perm.{succ u2} α') α' (fun (_x : α') => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α') => α') _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.Perm.{succ u2} α') α' α' (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.Perm.{succ u2} α') α' α' (Equiv.instEquivLikeEquiv.{succ u2, succ u2} α' α'))) p (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β' α') β' (fun (_x : β') => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β') => α') _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β' α') β' α' (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β' α') β' α' (Equiv.instEquivLikeEquiv.{succ u1, succ u2} β' α'))) (Equiv.symm.{succ u2, succ u1} α' β' e) x)))
Case conversion may be inaccurate. Consider using '#align equiv.perm_congr_apply Equiv.permCongr_applyₓ'. -/
@[simp]
theorem permCongr_apply (p : Equiv.Perm α') (x) : e.permCongr p x = e (p (e.symm x)) :=
  rfl
#align equiv.perm_congr_apply Equiv.permCongr_apply

#print Equiv.permCongr_symm_apply /-
theorem permCongr_symm_apply (p : Equiv.Perm β') (x) : e.permCongr.symm p x = e.symm (p (e x)) :=
  rfl
#align equiv.perm_congr_symm_apply Equiv.permCongr_symm_apply
-/

/- warning: equiv.perm_congr_trans -> Equiv.permCongr_trans is a dubious translation:
lean 3 declaration is
  forall {α' : Type.{u1}} {β' : Type.{u2}} (e : Equiv.{succ u1, succ u2} α' β') (p : Equiv.Perm.{succ u1} α') (p' : Equiv.Perm.{succ u1} α'), Eq.{succ u2} (Equiv.{succ u2, succ u2} β' β') (Equiv.trans.{succ u2, succ u2, succ u2} β' β' β' (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} (Equiv.Perm.{succ u1} α') (Equiv.Perm.{succ u2} β')) (fun (_x : Equiv.{succ u1, succ u2} (Equiv.Perm.{succ u1} α') (Equiv.Perm.{succ u2} β')) => (Equiv.Perm.{succ u1} α') -> (Equiv.Perm.{succ u2} β')) (Equiv.hasCoeToFun.{succ u1, succ u2} (Equiv.Perm.{succ u1} α') (Equiv.Perm.{succ u2} β')) (Equiv.permCongr.{u1, u2} α' β' e) p) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} (Equiv.Perm.{succ u1} α') (Equiv.Perm.{succ u2} β')) (fun (_x : Equiv.{succ u1, succ u2} (Equiv.Perm.{succ u1} α') (Equiv.Perm.{succ u2} β')) => (Equiv.Perm.{succ u1} α') -> (Equiv.Perm.{succ u2} β')) (Equiv.hasCoeToFun.{succ u1, succ u2} (Equiv.Perm.{succ u1} α') (Equiv.Perm.{succ u2} β')) (Equiv.permCongr.{u1, u2} α' β' e) p')) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} (Equiv.Perm.{succ u1} α') (Equiv.Perm.{succ u2} β')) (fun (_x : Equiv.{succ u1, succ u2} (Equiv.Perm.{succ u1} α') (Equiv.Perm.{succ u2} β')) => (Equiv.Perm.{succ u1} α') -> (Equiv.Perm.{succ u2} β')) (Equiv.hasCoeToFun.{succ u1, succ u2} (Equiv.Perm.{succ u1} α') (Equiv.Perm.{succ u2} β')) (Equiv.permCongr.{u1, u2} α' β' e) (Equiv.trans.{succ u1, succ u1, succ u1} α' α' α' p p'))
but is expected to have type
  forall {α' : Type.{u2}} {β' : Type.{u1}} (e : Equiv.{succ u2, succ u1} α' β') (p : Equiv.Perm.{succ u2} α') (p' : Equiv.Perm.{succ u2} α'), Eq.{succ u1} (Equiv.{succ u1, succ u1} β' β') (Equiv.trans.{succ u1, succ u1, succ u1} β' β' β' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')) (Equiv.Perm.{succ u2} α') (fun (_x : Equiv.Perm.{succ u2} α') => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Equiv.Perm.{succ u2} α') => Equiv.Perm.{succ u1} β') _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')) (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β') (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')) (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β') (Equiv.instEquivLikeEquiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')))) (Equiv.permCongr.{u2, u1} α' β' e) p) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')) (Equiv.Perm.{succ u2} α') (fun (_x : Equiv.Perm.{succ u2} α') => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Equiv.Perm.{succ u2} α') => Equiv.Perm.{succ u1} β') _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')) (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β') (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')) (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β') (Equiv.instEquivLikeEquiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')))) (Equiv.permCongr.{u2, u1} α' β' e) p')) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')) (Equiv.Perm.{succ u2} α') (fun (_x : Equiv.Perm.{succ u2} α') => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Equiv.Perm.{succ u2} α') => Equiv.Perm.{succ u1} β') _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')) (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β') (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')) (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β') (Equiv.instEquivLikeEquiv.{succ u2, succ u1} (Equiv.Perm.{succ u2} α') (Equiv.Perm.{succ u1} β')))) (Equiv.permCongr.{u2, u1} α' β' e) (Equiv.trans.{succ u2, succ u2, succ u2} α' α' α' p p'))
Case conversion may be inaccurate. Consider using '#align equiv.perm_congr_trans Equiv.permCongr_transₓ'. -/
theorem permCongr_trans (p p' : Equiv.Perm α') :
    (e.permCongr p).trans (e.permCongr p') = e.permCongr (p.trans p') :=
  by
  ext
  simp
#align equiv.perm_congr_trans Equiv.permCongr_trans

end PermCongr

#print Equiv.equivOfIsEmpty /-
/-- Two empty types are equivalent. -/
def equivOfIsEmpty (α β : Sort _) [IsEmpty α] [IsEmpty β] : α ≃ β :=
  ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim⟩
#align equiv.equiv_of_is_empty Equiv.equivOfIsEmpty
-/

#print Equiv.equivEmpty /-
/-- If `α` is an empty type, then it is equivalent to the `empty` type. -/
def equivEmpty (α : Sort u) [IsEmpty α] : α ≃ Empty :=
  equivOfIsEmpty α _
#align equiv.equiv_empty Equiv.equivEmpty
-/

#print Equiv.equivPEmpty /-
/-- If `α` is an empty type, then it is equivalent to the `pempty` type in any universe. -/
def equivPEmpty (α : Sort v) [IsEmpty α] : α ≃ PEmpty.{u} :=
  equivOfIsEmpty α _
#align equiv.equiv_pempty Equiv.equivPEmpty
-/

/- warning: equiv.equiv_empty_equiv -> Equiv.equivEmptyEquiv is a dubious translation:
lean 3 declaration is
  forall (α : Sort.{u1}), Equiv.{max 1 (max u1 1) (imax 1 u1), 0} (Equiv.{u1, 1} α Empty) (IsEmpty.{u1} α)
but is expected to have type
  forall (α : Sort.{u1}), Equiv.{max 1 u1, 0} (Equiv.{u1, 1} α Empty) (IsEmpty.{u1} α)
Case conversion may be inaccurate. Consider using '#align equiv.equiv_empty_equiv Equiv.equivEmptyEquivₓ'. -/
/-- `α` is equivalent to an empty type iff `α` is empty. -/
def equivEmptyEquiv (α : Sort u) : α ≃ Empty ≃ IsEmpty α :=
  ⟨fun e => Function.isEmpty e, @equivEmpty α, fun e => ext fun x => (e x).elim, fun p => rfl⟩
#align equiv.equiv_empty_equiv Equiv.equivEmptyEquiv

#print Equiv.propEquivPEmpty /-
/-- The `Sort` of proofs of a false proposition is equivalent to `pempty`. -/
def propEquivPEmpty {p : Prop} (h : ¬p) : p ≃ PEmpty :=
  @equivPEmpty p <| IsEmpty.prop_iff.2 h
#align equiv.prop_equiv_pempty Equiv.propEquivPEmpty
-/

#print Equiv.equivOfUnique /-
/-- If both `α` and `β` have a unique element, then `α ≃ β`. -/
def equivOfUnique (α β : Sort _) [Unique α] [Unique β] : α ≃ β
    where
  toFun := default
  invFun := default
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align equiv.equiv_of_unique Equiv.equivOfUnique
-/

/- warning: equiv.equiv_punit -> Equiv.equivPUnit is a dubious translation:
lean 3 declaration is
  forall (α : Sort.{u2}) [_inst_1 : Unique.{u2} α], Equiv.{u2, u1} α PUnit.{u1}
but is expected to have type
  forall (α : Sort.{u1}) [_inst_1 : Unique.{u1} α], Equiv.{u1, u2} α PUnit.{u2}
Case conversion may be inaccurate. Consider using '#align equiv.equiv_punit Equiv.equivPUnitₓ'. -/
/-- If `α` has a unique element, then it is equivalent to any `punit`. -/
def equivPUnit (α : Sort _) [Unique α] : α ≃ PUnit.{v} :=
  equivOfUnique α _
#align equiv.equiv_punit Equiv.equivPUnit

/- warning: equiv.prop_equiv_punit -> Equiv.propEquivPUnit is a dubious translation:
lean 3 declaration is
  forall {p : Prop}, p -> (Equiv.{0, u_1} p PUnit.{u_1})
but is expected to have type
  forall {p : Prop}, p -> (Equiv.{0, 0} p PUnit.{0})
Case conversion may be inaccurate. Consider using '#align equiv.prop_equiv_punit Equiv.propEquivPUnitₓ'. -/
/-- The `Sort` of proofs of a true proposition is equivalent to `punit`. -/
def propEquivPUnit {p : Prop} (h : p) : p ≃ PUnit :=
  @equivPUnit p <| uniqueProp h
#align equiv.prop_equiv_punit Equiv.propEquivPUnit

#print Equiv.ulift /-
/-- `ulift α` is equivalent to `α`. -/
@[simps (config := { fullyApplied := false }) apply symmApply]
protected def ulift {α : Type v} : ULift.{u} α ≃ α :=
  ⟨ULift.down, ULift.up, ULift.up_down, fun a => rfl⟩
#align equiv.ulift Equiv.ulift
-/

#print Equiv.plift /-
/-- `plift α` is equivalent to `α`. -/
@[simps (config := { fullyApplied := false }) apply symmApply]
protected def plift : PLift α ≃ α :=
  ⟨PLift.down, PLift.up, PLift.up_down, PLift.down_up⟩
#align equiv.plift Equiv.plift
-/

#print Equiv.ofIff /-
/-- equivalence of propositions is the same as iff -/
def ofIff {P Q : Prop} (h : P ↔ Q) : P ≃ Q
    where
  toFun := h.mp
  invFun := h.mpr
  left_inv x := rfl
  right_inv y := rfl
#align equiv.of_iff Equiv.ofIff
-/

#print Equiv.arrowCongr /-
/-- If `α₁` is equivalent to `α₂` and `β₁` is equivalent to `β₂`, then the type of maps `α₁ → β₁`
is equivalent to the type of maps `α₂ → β₂`. -/
@[congr, simps apply]
def arrowCongr {α₁ β₁ α₂ β₂ : Sort _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂)
    where
  toFun f := e₂ ∘ f ∘ e₁.symm
  invFun f := e₂.symm ∘ f ∘ e₁
  left_inv f := funext fun x => by simp
  right_inv f := funext fun x => by simp
#align equiv.arrow_congr Equiv.arrowCongr
-/

/- warning: equiv.arrow_congr_comp -> Equiv.arrowCongr_comp is a dubious translation:
lean 3 declaration is
  forall {α₁ : Sort.{u1}} {β₁ : Sort.{u2}} {γ₁ : Sort.{u3}} {α₂ : Sort.{u4}} {β₂ : Sort.{u5}} {γ₂ : Sort.{u6}} (ea : Equiv.{u1, u4} α₁ α₂) (eb : Equiv.{u2, u5} β₁ β₂) (ec : Equiv.{u3, u6} γ₁ γ₂) (f : α₁ -> β₁) (g : β₁ -> γ₁), Eq.{imax u4 u6} (α₂ -> γ₂) (coeFn.{max 1 (imax (imax u1 u3) u4 u6) (imax (imax u4 u6) u1 u3), imax (imax u1 u3) u4 u6} (Equiv.{imax u1 u3, imax u4 u6} (α₁ -> γ₁) (α₂ -> γ₂)) (fun (_x : Equiv.{imax u1 u3, imax u4 u6} (α₁ -> γ₁) (α₂ -> γ₂)) => (α₁ -> γ₁) -> α₂ -> γ₂) (Equiv.hasCoeToFun.{imax u1 u3, imax u4 u6} (α₁ -> γ₁) (α₂ -> γ₂)) (Equiv.arrowCongr.{u1, u3, u4, u6} α₁ γ₁ α₂ γ₂ ea ec) (Function.comp.{u1, u2, u3} α₁ β₁ γ₁ g f)) (Function.comp.{u4, u5, u6} α₂ β₂ γ₂ (coeFn.{max 1 (imax (imax u2 u3) u5 u6) (imax (imax u5 u6) u2 u3), imax (imax u2 u3) u5 u6} (Equiv.{imax u2 u3, imax u5 u6} (β₁ -> γ₁) (β₂ -> γ₂)) (fun (_x : Equiv.{imax u2 u3, imax u5 u6} (β₁ -> γ₁) (β₂ -> γ₂)) => (β₁ -> γ₁) -> β₂ -> γ₂) (Equiv.hasCoeToFun.{imax u2 u3, imax u5 u6} (β₁ -> γ₁) (β₂ -> γ₂)) (Equiv.arrowCongr.{u2, u3, u5, u6} β₁ γ₁ β₂ γ₂ eb ec) g) (coeFn.{max 1 (imax (imax u1 u2) u4 u5) (imax (imax u4 u5) u1 u2), imax (imax u1 u2) u4 u5} (Equiv.{imax u1 u2, imax u4 u5} (α₁ -> β₁) (α₂ -> β₂)) (fun (_x : Equiv.{imax u1 u2, imax u4 u5} (α₁ -> β₁) (α₂ -> β₂)) => (α₁ -> β₁) -> α₂ -> β₂) (Equiv.hasCoeToFun.{imax u1 u2, imax u4 u5} (α₁ -> β₁) (α₂ -> β₂)) (Equiv.arrowCongr.{u1, u2, u4, u5} α₁ β₁ α₂ β₂ ea eb) f))
but is expected to have type
  forall {α₁ : Sort.{u6}} {β₁ : Sort.{u5}} {γ₁ : Sort.{u4}} {α₂ : Sort.{u3}} {β₂ : Sort.{u2}} {γ₂ : Sort.{u1}} (ea : Equiv.{u6, u3} α₁ α₂) (eb : Equiv.{u5, u2} β₁ β₂) (ec : Equiv.{u4, u1} γ₁ γ₂) (f : α₁ -> β₁) (g : β₁ -> γ₁), Eq.{imax u3 u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α₁ -> γ₁) => α₂ -> γ₂) (Function.comp.{u6, u5, u4} α₁ β₁ γ₁ g f)) (FunLike.coe.{max (max 1 (imax u6 u4)) (imax u3 u1), imax u6 u4, imax u3 u1} (Equiv.{imax u6 u4, imax u3 u1} (α₁ -> γ₁) (α₂ -> γ₂)) (α₁ -> γ₁) (fun (_x : α₁ -> γ₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α₁ -> γ₁) => α₂ -> γ₂) _x) (EmbeddingLike.toFunLike.{max (max 1 (imax u6 u4)) (imax u3 u1), imax u6 u4, imax u3 u1} (Equiv.{imax u6 u4, imax u3 u1} (α₁ -> γ₁) (α₂ -> γ₂)) (α₁ -> γ₁) (α₂ -> γ₂) (EquivLike.toEmbeddingLike.{max (max 1 (imax u6 u4)) (imax u3 u1), imax u6 u4, imax u3 u1} (Equiv.{imax u6 u4, imax u3 u1} (α₁ -> γ₁) (α₂ -> γ₂)) (α₁ -> γ₁) (α₂ -> γ₂) (Equiv.instEquivLikeEquiv.{imax u6 u4, imax u3 u1} (α₁ -> γ₁) (α₂ -> γ₂)))) (Equiv.arrowCongr.{u6, u4, u3, u1} α₁ γ₁ α₂ γ₂ ea ec) (Function.comp.{u6, u5, u4} α₁ β₁ γ₁ g f)) (Function.comp.{u3, u2, u1} α₂ β₂ γ₂ (FunLike.coe.{max (max 1 (imax u5 u4)) (imax u2 u1), imax u5 u4, imax u2 u1} (Equiv.{imax u5 u4, imax u2 u1} (β₁ -> γ₁) (β₂ -> γ₂)) (β₁ -> γ₁) (fun (_x : β₁ -> γ₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β₁ -> γ₁) => β₂ -> γ₂) _x) (EmbeddingLike.toFunLike.{max (max 1 (imax u5 u4)) (imax u2 u1), imax u5 u4, imax u2 u1} (Equiv.{imax u5 u4, imax u2 u1} (β₁ -> γ₁) (β₂ -> γ₂)) (β₁ -> γ₁) (β₂ -> γ₂) (EquivLike.toEmbeddingLike.{max (max 1 (imax u5 u4)) (imax u2 u1), imax u5 u4, imax u2 u1} (Equiv.{imax u5 u4, imax u2 u1} (β₁ -> γ₁) (β₂ -> γ₂)) (β₁ -> γ₁) (β₂ -> γ₂) (Equiv.instEquivLikeEquiv.{imax u5 u4, imax u2 u1} (β₁ -> γ₁) (β₂ -> γ₂)))) (Equiv.arrowCongr.{u5, u4, u2, u1} β₁ γ₁ β₂ γ₂ eb ec) g) (FunLike.coe.{max (max 1 (imax u6 u5)) (imax u3 u2), imax u6 u5, imax u3 u2} (Equiv.{imax u6 u5, imax u3 u2} (α₁ -> β₁) (α₂ -> β₂)) (α₁ -> β₁) (fun (_x : α₁ -> β₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α₁ -> β₁) => α₂ -> β₂) _x) (EmbeddingLike.toFunLike.{max (max 1 (imax u6 u5)) (imax u3 u2), imax u6 u5, imax u3 u2} (Equiv.{imax u6 u5, imax u3 u2} (α₁ -> β₁) (α₂ -> β₂)) (α₁ -> β₁) (α₂ -> β₂) (EquivLike.toEmbeddingLike.{max (max 1 (imax u6 u5)) (imax u3 u2), imax u6 u5, imax u3 u2} (Equiv.{imax u6 u5, imax u3 u2} (α₁ -> β₁) (α₂ -> β₂)) (α₁ -> β₁) (α₂ -> β₂) (Equiv.instEquivLikeEquiv.{imax u6 u5, imax u3 u2} (α₁ -> β₁) (α₂ -> β₂)))) (Equiv.arrowCongr.{u6, u5, u3, u2} α₁ β₁ α₂ β₂ ea eb) f))
Case conversion may be inaccurate. Consider using '#align equiv.arrow_congr_comp Equiv.arrowCongr_compₓ'. -/
theorem arrowCongr_comp {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂)
    (f : α₁ → β₁) (g : β₁ → γ₁) :
    arrowCongr ea ec (g ∘ f) = arrowCongr eb ec g ∘ arrowCongr ea eb f :=
  by
  ext
  simp only [comp, arrow_congr_apply, eb.symm_apply_apply]
#align equiv.arrow_congr_comp Equiv.arrowCongr_comp

/- warning: equiv.arrow_congr_refl -> Equiv.arrowCongr_refl is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}}, Eq.{max 1 (imax u1 u2)} (Equiv.{imax u1 u2, imax u1 u2} (α -> β) (α -> β)) (Equiv.arrowCongr.{u1, u2, u1, u2} α β α β (Equiv.refl.{u1} α) (Equiv.refl.{u2} β)) (Equiv.refl.{imax u1 u2} (α -> β))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}}, Eq.{max 1 (imax u2 u1)} (Equiv.{imax u2 u1, imax u2 u1} (α -> β) (α -> β)) (Equiv.arrowCongr.{u2, u1, u2, u1} α β α β (Equiv.refl.{u2} α) (Equiv.refl.{u1} β)) (Equiv.refl.{imax u2 u1} (α -> β))
Case conversion may be inaccurate. Consider using '#align equiv.arrow_congr_refl Equiv.arrowCongr_reflₓ'. -/
@[simp]
theorem arrowCongr_refl {α β : Sort _} :
    arrowCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α → β) :=
  rfl
#align equiv.arrow_congr_refl Equiv.arrowCongr_refl

/- warning: equiv.arrow_congr_trans -> Equiv.arrowCongr_trans is a dubious translation:
lean 3 declaration is
  forall {α₁ : Sort.{u1}} {β₁ : Sort.{u2}} {α₂ : Sort.{u3}} {β₂ : Sort.{u4}} {α₃ : Sort.{u5}} {β₃ : Sort.{u6}} (e₁ : Equiv.{u1, u3} α₁ α₂) (e₁' : Equiv.{u2, u4} β₁ β₂) (e₂ : Equiv.{u3, u5} α₂ α₃) (e₂' : Equiv.{u4, u6} β₂ β₃), Eq.{max 1 (imax (imax u1 u2) u5 u6) (imax (imax u5 u6) u1 u2)} (Equiv.{imax u1 u2, imax u5 u6} (α₁ -> β₁) (α₃ -> β₃)) (Equiv.arrowCongr.{u1, u2, u5, u6} α₁ β₁ α₃ β₃ (Equiv.trans.{u1, u3, u5} α₁ α₂ α₃ e₁ e₂) (Equiv.trans.{u2, u4, u6} β₁ β₂ β₃ e₁' e₂')) (Equiv.trans.{imax u1 u2, imax u3 u4, imax u5 u6} (α₁ -> β₁) (α₂ -> β₂) (α₃ -> β₃) (Equiv.arrowCongr.{u1, u2, u3, u4} α₁ β₁ α₂ β₂ e₁ e₁') (Equiv.arrowCongr.{u3, u4, u5, u6} α₂ β₂ α₃ β₃ e₂ e₂'))
but is expected to have type
  forall {α₁ : Sort.{u6}} {β₁ : Sort.{u5}} {α₂ : Sort.{u4}} {β₂ : Sort.{u3}} {α₃ : Sort.{u2}} {β₃ : Sort.{u1}} (e₁ : Equiv.{u6, u5} α₁ β₁) (e₁' : Equiv.{u4, u3} α₂ β₂) (e₂ : Equiv.{u5, u2} β₁ α₃) (e₂' : Equiv.{u3, u1} β₂ β₃), Eq.{max (max 1 (imax u6 u4)) (imax u2 u1)} (Equiv.{imax u6 u4, imax u2 u1} (α₁ -> α₂) (α₃ -> β₃)) (Equiv.arrowCongr.{u6, u4, u2, u1} α₁ α₂ α₃ β₃ (Equiv.trans.{u6, u5, u2} α₁ β₁ α₃ e₁ e₂) (Equiv.trans.{u4, u3, u1} α₂ β₂ β₃ e₁' e₂')) (Equiv.trans.{imax u6 u4, imax u5 u3, imax u2 u1} (α₁ -> α₂) (β₁ -> β₂) (α₃ -> β₃) (Equiv.arrowCongr.{u6, u4, u5, u3} α₁ α₂ β₁ β₂ e₁ e₁') (Equiv.arrowCongr.{u5, u3, u2, u1} β₁ β₂ α₃ β₃ e₂ e₂'))
Case conversion may be inaccurate. Consider using '#align equiv.arrow_congr_trans Equiv.arrowCongr_transₓ'. -/
@[simp]
theorem arrowCongr_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Sort _} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃)
    (e₂' : β₂ ≃ β₃) :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') :=
  rfl
#align equiv.arrow_congr_trans Equiv.arrowCongr_trans

/- warning: equiv.arrow_congr_symm -> Equiv.arrowCongr_symm is a dubious translation:
lean 3 declaration is
  forall {α₁ : Sort.{u1}} {β₁ : Sort.{u2}} {α₂ : Sort.{u3}} {β₂ : Sort.{u4}} (e₁ : Equiv.{u1, u3} α₁ α₂) (e₂ : Equiv.{u2, u4} β₁ β₂), Eq.{max 1 (imax (imax u3 u4) u1 u2) (imax (imax u1 u2) u3 u4)} (Equiv.{imax u3 u4, imax u1 u2} (α₂ -> β₂) (α₁ -> β₁)) (Equiv.symm.{imax u1 u2, imax u3 u4} (α₁ -> β₁) (α₂ -> β₂) (Equiv.arrowCongr.{u1, u2, u3, u4} α₁ β₁ α₂ β₂ e₁ e₂)) (Equiv.arrowCongr.{u3, u4, u1, u2} α₂ β₂ α₁ β₁ (Equiv.symm.{u1, u3} α₁ α₂ e₁) (Equiv.symm.{u2, u4} β₁ β₂ e₂))
but is expected to have type
  forall {α₁ : Sort.{u4}} {β₁ : Sort.{u3}} {α₂ : Sort.{u2}} {β₂ : Sort.{u1}} (e₁ : Equiv.{u4, u3} α₁ β₁) (e₂ : Equiv.{u2, u1} α₂ β₂), Eq.{max (max 1 (imax u3 u1)) (imax u4 u2)} (Equiv.{imax u3 u1, imax u4 u2} (β₁ -> β₂) (α₁ -> α₂)) (Equiv.symm.{imax u4 u2, imax u3 u1} (α₁ -> α₂) (β₁ -> β₂) (Equiv.arrowCongr.{u4, u2, u3, u1} α₁ α₂ β₁ β₂ e₁ e₂)) (Equiv.arrowCongr.{u3, u1, u4, u2} β₁ β₂ α₁ α₂ (Equiv.symm.{u4, u3} α₁ β₁ e₁) (Equiv.symm.{u2, u1} α₂ β₂ e₂))
Case conversion may be inaccurate. Consider using '#align equiv.arrow_congr_symm Equiv.arrowCongr_symmₓ'. -/
@[simp]
theorem arrowCongr_symm {α₁ β₁ α₂ β₂ : Sort _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (arrowCongr e₁ e₂).symm = arrowCongr e₁.symm e₂.symm :=
  rfl
#align equiv.arrow_congr_symm Equiv.arrowCongr_symm

#print Equiv.arrowCongr' /-
/-- A version of `equiv.arrow_congr` in `Type`, rather than `Sort`.

The `equiv_rw` tactic is not able to use the default `Sort` level `equiv.arrow_congr`,
because Lean's universe rules will not unify `?l_1` with `imax (1 ?m_1)`.
-/
@[congr, simps apply]
def arrowCongr' {α₁ β₁ α₂ β₂ : Type _} (hα : α₁ ≃ α₂) (hβ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) :=
  Equiv.arrowCongr hα hβ
#align equiv.arrow_congr' Equiv.arrowCongr'
-/

/- warning: equiv.arrow_congr'_refl -> Equiv.arrowCongr'_refl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{max 1 (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> β) (α -> β)) (Equiv.arrowCongr'.{u1, u2, u1, u2} α β α β (Equiv.refl.{succ u1} α) (Equiv.refl.{succ u2} β)) (Equiv.refl.{max (succ u1) (succ u2)} (α -> β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (α -> β) (α -> β)) (Equiv.arrowCongr'.{u2, u1, u2, u1} α β α β (Equiv.refl.{succ u2} α) (Equiv.refl.{succ u1} β)) (Equiv.refl.{max (succ u2) (succ u1)} (α -> β))
Case conversion may be inaccurate. Consider using '#align equiv.arrow_congr'_refl Equiv.arrowCongr'_reflₓ'. -/
@[simp]
theorem arrowCongr'_refl {α β : Type _} :
    arrowCongr' (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α → β) :=
  rfl
#align equiv.arrow_congr'_refl Equiv.arrowCongr'_refl

/- warning: equiv.arrow_congr'_trans -> Equiv.arrowCongr'_trans is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} {α₂ : Type.{u3}} {β₂ : Type.{u4}} {α₃ : Type.{u5}} {β₃ : Type.{u6}} (e₁ : Equiv.{succ u1, succ u3} α₁ α₂) (e₁' : Equiv.{succ u2, succ u4} β₁ β₂) (e₂ : Equiv.{succ u3, succ u5} α₂ α₃) (e₂' : Equiv.{succ u4, succ u6} β₂ β₃), Eq.{max 1 (max (max (succ u1) (succ u2)) (succ u5) (succ u6)) (max (succ u5) (succ u6)) (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u5) (succ u6)} (α₁ -> β₁) (α₃ -> β₃)) (Equiv.arrowCongr'.{u1, u2, u5, u6} α₁ β₁ α₃ β₃ (Equiv.trans.{succ u1, succ u3, succ u5} α₁ α₂ α₃ e₁ e₂) (Equiv.trans.{succ u2, succ u4, succ u6} β₁ β₂ β₃ e₁' e₂')) (Equiv.trans.{max (succ u1) (succ u2), max (succ u3) (succ u4), max (succ u5) (succ u6)} (α₁ -> β₁) (α₂ -> β₂) (α₃ -> β₃) (Equiv.arrowCongr'.{u1, u2, u3, u4} α₁ β₁ α₂ β₂ e₁ e₁') (Equiv.arrowCongr'.{u3, u4, u5, u6} α₂ β₂ α₃ β₃ e₂ e₂'))
but is expected to have type
  forall {α₁ : Type.{u6}} {β₁ : Type.{u5}} {α₂ : Type.{u4}} {β₂ : Type.{u3}} {α₃ : Type.{u2}} {β₃ : Type.{u1}} (e₁ : Equiv.{succ u6, succ u5} α₁ β₁) (e₁' : Equiv.{succ u4, succ u3} α₂ β₂) (e₂ : Equiv.{succ u5, succ u2} β₁ α₃) (e₂' : Equiv.{succ u3, succ u1} β₂ β₃), Eq.{max (max (max (succ u1) (succ u2)) (succ u4)) (succ u6)} (Equiv.{max (succ u6) (succ u4), max (succ u2) (succ u1)} (α₁ -> α₂) (α₃ -> β₃)) (Equiv.arrowCongr'.{u6, u4, u2, u1} α₁ α₂ α₃ β₃ (Equiv.trans.{succ u6, succ u5, succ u2} α₁ β₁ α₃ e₁ e₂) (Equiv.trans.{succ u4, succ u3, succ u1} α₂ β₂ β₃ e₁' e₂')) (Equiv.trans.{max (succ u4) (succ u6), max (succ u3) (succ u5), max (succ u1) (succ u2)} (α₁ -> α₂) (β₁ -> β₂) (α₃ -> β₃) (Equiv.arrowCongr'.{u6, u4, u5, u3} α₁ α₂ β₁ β₂ e₁ e₁') (Equiv.arrowCongr'.{u5, u3, u2, u1} β₁ β₂ α₃ β₃ e₂ e₂'))
Case conversion may be inaccurate. Consider using '#align equiv.arrow_congr'_trans Equiv.arrowCongr'_transₓ'. -/
@[simp]
theorem arrowCongr'_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Type _} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃)
    (e₂' : β₂ ≃ β₃) :
    arrowCongr' (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr' e₁ e₁').trans (arrowCongr' e₂ e₂') :=
  rfl
#align equiv.arrow_congr'_trans Equiv.arrowCongr'_trans

/- warning: equiv.arrow_congr'_symm -> Equiv.arrowCongr'_symm is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {β₁ : Type.{u2}} {α₂ : Type.{u3}} {β₂ : Type.{u4}} (e₁ : Equiv.{succ u1, succ u3} α₁ α₂) (e₂ : Equiv.{succ u2, succ u4} β₁ β₂), Eq.{max 1 (max (max (succ u3) (succ u4)) (succ u1) (succ u2)) (max (succ u1) (succ u2)) (succ u3) (succ u4)} (Equiv.{max (succ u3) (succ u4), max (succ u1) (succ u2)} (α₂ -> β₂) (α₁ -> β₁)) (Equiv.symm.{max (succ u1) (succ u2), max (succ u3) (succ u4)} (α₁ -> β₁) (α₂ -> β₂) (Equiv.arrowCongr'.{u1, u2, u3, u4} α₁ β₁ α₂ β₂ e₁ e₂)) (Equiv.arrowCongr'.{u3, u4, u1, u2} α₂ β₂ α₁ β₁ (Equiv.symm.{succ u1, succ u3} α₁ α₂ e₁) (Equiv.symm.{succ u2, succ u4} β₁ β₂ e₂))
but is expected to have type
  forall {α₁ : Type.{u4}} {β₁ : Type.{u3}} {α₂ : Type.{u2}} {β₂ : Type.{u1}} (e₁ : Equiv.{succ u4, succ u3} α₁ β₁) (e₂ : Equiv.{succ u2, succ u1} α₂ β₂), Eq.{max (max (max (succ u1) (succ u3)) (succ u2)) (succ u4)} (Equiv.{max (succ u1) (succ u3), max (succ u2) (succ u4)} (β₁ -> β₂) (α₁ -> α₂)) (Equiv.symm.{max (succ u2) (succ u4), max (succ u1) (succ u3)} (α₁ -> α₂) (β₁ -> β₂) (Equiv.arrowCongr'.{u4, u2, u3, u1} α₁ α₂ β₁ β₂ e₁ e₂)) (Equiv.arrowCongr'.{u3, u1, u4, u2} β₁ β₂ α₁ α₂ (Equiv.symm.{succ u4, succ u3} α₁ β₁ e₁) (Equiv.symm.{succ u2, succ u1} α₂ β₂ e₂))
Case conversion may be inaccurate. Consider using '#align equiv.arrow_congr'_symm Equiv.arrowCongr'_symmₓ'. -/
@[simp]
theorem arrowCongr'_symm {α₁ β₁ α₂ β₂ : Type _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (arrowCongr' e₁ e₂).symm = arrowCongr' e₁.symm e₂.symm :=
  rfl
#align equiv.arrow_congr'_symm Equiv.arrowCongr'_symm

#print Equiv.conj /-
/-- Conjugate a map `f : α → α` by an equivalence `α ≃ β`. -/
@[simps apply]
def conj (e : α ≃ β) : (α → α) ≃ (β → β) :=
  arrowCongr e e
#align equiv.conj Equiv.conj
-/

#print Equiv.conj_refl /-
@[simp]
theorem conj_refl : conj (Equiv.refl α) = Equiv.refl (α → α) :=
  rfl
#align equiv.conj_refl Equiv.conj_refl
-/

/- warning: equiv.conj_symm -> Equiv.conj_symm is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} (e : Equiv.{u1, u2} α β), Eq.{max 1 (imax u2 u1) (imax u1 u2)} (Equiv.{u2, u1} (β -> β) (α -> α)) (Equiv.symm.{u1, u2} (α -> α) (β -> β) (Equiv.conj.{u1, u2} α β e)) (Equiv.conj.{u2, u1} β α (Equiv.symm.{u1, u2} α β e))
but is expected to have type
  forall {α : Sort.{u1}} {β : Sort.{u2}} (e : Equiv.{u1, u2} α β), Eq.{max (max 1 u1) u2} (Equiv.{u2, u1} (β -> β) (α -> α)) (Equiv.symm.{u1, u2} (α -> α) (β -> β) (Equiv.conj.{u1, u2} α β e)) (Equiv.conj.{u2, u1} β α (Equiv.symm.{u1, u2} α β e))
Case conversion may be inaccurate. Consider using '#align equiv.conj_symm Equiv.conj_symmₓ'. -/
@[simp]
theorem conj_symm (e : α ≃ β) : e.conj.symm = e.symm.conj :=
  rfl
#align equiv.conj_symm Equiv.conj_symm

/- warning: equiv.conj_trans -> Equiv.conj_trans is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} (e₁ : Equiv.{u1, u2} α β) (e₂ : Equiv.{u2, u3} β γ), Eq.{max 1 (imax u1 u3) (imax u3 u1)} (Equiv.{u1, u3} (α -> α) (γ -> γ)) (Equiv.conj.{u1, u3} α γ (Equiv.trans.{u1, u2, u3} α β γ e₁ e₂)) (Equiv.trans.{u1, u2, u3} (α -> α) (β -> β) (γ -> γ) (Equiv.conj.{u1, u2} α β e₁) (Equiv.conj.{u2, u3} β γ e₂))
but is expected to have type
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} (e₁ : Equiv.{u1, u2} α β) (e₂ : Equiv.{u2, u3} β γ), Eq.{max (max 1 u1) u3} (Equiv.{u1, u3} (α -> α) (γ -> γ)) (Equiv.conj.{u1, u3} α γ (Equiv.trans.{u1, u2, u3} α β γ e₁ e₂)) (Equiv.trans.{u1, u2, u3} (α -> α) (β -> β) (γ -> γ) (Equiv.conj.{u1, u2} α β e₁) (Equiv.conj.{u2, u3} β γ e₂))
Case conversion may be inaccurate. Consider using '#align equiv.conj_trans Equiv.conj_transₓ'. -/
@[simp]
theorem conj_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : (e₁.trans e₂).conj = e₁.conj.trans e₂.conj :=
  rfl
#align equiv.conj_trans Equiv.conj_trans

#print Equiv.conj_comp /-
-- This should not be a simp lemma as long as `(∘)` is reducible:
-- when `(∘)` is reducible, Lean can unify `f₁ ∘ f₂` with any `g` using
-- `f₁ := g` and `f₂ := λ x, x`.  This causes nontermination.
theorem conj_comp (e : α ≃ β) (f₁ f₂ : α → α) : e.conj (f₁ ∘ f₂) = e.conj f₁ ∘ e.conj f₂ := by
  apply arrow_congr_comp
#align equiv.conj_comp Equiv.conj_comp
-/

/- warning: equiv.eq_comp_symm -> Equiv.eq_comp_symm is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} (e : Equiv.{u1, u2} α β) (f : β -> γ) (g : α -> γ), Iff (Eq.{imax u2 u3} (β -> γ) f (Function.comp.{u2, u1, u3} β α γ g (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e)))) (Eq.{imax u1 u3} (α -> γ) (Function.comp.{u1, u2, u3} α β γ f (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e)) g)
but is expected to have type
  forall {α : Sort.{u3}} {β : Sort.{u2}} {γ : Sort.{u1}} (e : Equiv.{u3, u2} α β) (f : β -> γ) (g : α -> γ), Iff (Eq.{imax u2 u1} (β -> γ) f (Function.comp.{u2, u3, u1} β α γ g (FunLike.coe.{max (max 1 u2) u3, u2, u3} (Equiv.{u2, u3} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u3, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u3, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e)))) (Eq.{imax u3 u1} (α -> γ) (Function.comp.{u3, u2, u1} α β γ f (FunLike.coe.{max (max 1 u2) u3, u3, u2} (Equiv.{u3, u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u3, u3, u2} (Equiv.{u3, u2} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u3, u3, u2} (Equiv.{u3, u2} α β) α β (Equiv.instEquivLikeEquiv.{u3, u2} α β))) e)) g)
Case conversion may be inaccurate. Consider using '#align equiv.eq_comp_symm Equiv.eq_comp_symmₓ'. -/
theorem eq_comp_symm {α β γ} (e : α ≃ β) (f : β → γ) (g : α → γ) : f = g ∘ e.symm ↔ f ∘ e = g :=
  (e.arrowCongr (Equiv.refl γ)).symm_apply_eq.symm
#align equiv.eq_comp_symm Equiv.eq_comp_symm

/- warning: equiv.comp_symm_eq -> Equiv.comp_symm_eq is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} (e : Equiv.{u1, u2} α β) (f : β -> γ) (g : α -> γ), Iff (Eq.{imax u2 u3} (β -> γ) (Function.comp.{u2, u1, u3} β α γ g (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e))) f) (Eq.{imax u1 u3} (α -> γ) g (Function.comp.{u1, u2, u3} α β γ f (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e)))
but is expected to have type
  forall {α : Sort.{u3}} {β : Sort.{u2}} {γ : Sort.{u1}} (e : Equiv.{u3, u2} α β) (f : β -> γ) (g : α -> γ), Iff (Eq.{imax u2 u1} (β -> γ) (Function.comp.{u2, u3, u1} β α γ g (FunLike.coe.{max (max 1 u2) u3, u2, u3} (Equiv.{u2, u3} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u3, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u3, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e))) f) (Eq.{imax u3 u1} (α -> γ) g (Function.comp.{u3, u2, u1} α β γ f (FunLike.coe.{max (max 1 u2) u3, u3, u2} (Equiv.{u3, u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u3, u3, u2} (Equiv.{u3, u2} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u3, u3, u2} (Equiv.{u3, u2} α β) α β (Equiv.instEquivLikeEquiv.{u3, u2} α β))) e)))
Case conversion may be inaccurate. Consider using '#align equiv.comp_symm_eq Equiv.comp_symm_eqₓ'. -/
theorem comp_symm_eq {α β γ} (e : α ≃ β) (f : β → γ) (g : α → γ) : g ∘ e.symm = f ↔ g = f ∘ e :=
  (e.arrowCongr (Equiv.refl γ)).eq_symm_apply.symm
#align equiv.comp_symm_eq Equiv.comp_symm_eq

/- warning: equiv.eq_symm_comp -> Equiv.eq_symm_comp is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} (e : Equiv.{u1, u2} α β) (f : γ -> α) (g : γ -> β), Iff (Eq.{imax u3 u1} (γ -> α) f (Function.comp.{u3, u2, u1} γ β α (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e)) g)) (Eq.{imax u3 u2} (γ -> β) (Function.comp.{u3, u1, u2} γ α β (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e) f) g)
but is expected to have type
  forall {α : Sort.{u3}} {β : Sort.{u2}} {γ : Sort.{u1}} (e : Equiv.{u3, u2} α β) (f : γ -> α) (g : γ -> β), Iff (Eq.{imax u1 u3} (γ -> α) f (Function.comp.{u1, u2, u3} γ β α (FunLike.coe.{max (max 1 u2) u3, u2, u3} (Equiv.{u2, u3} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u3, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u3, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e)) g)) (Eq.{imax u1 u2} (γ -> β) (Function.comp.{u1, u3, u2} γ α β (FunLike.coe.{max (max 1 u2) u3, u3, u2} (Equiv.{u3, u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u3, u3, u2} (Equiv.{u3, u2} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u3, u3, u2} (Equiv.{u3, u2} α β) α β (Equiv.instEquivLikeEquiv.{u3, u2} α β))) e) f) g)
Case conversion may be inaccurate. Consider using '#align equiv.eq_symm_comp Equiv.eq_symm_compₓ'. -/
theorem eq_symm_comp {α β γ} (e : α ≃ β) (f : γ → α) (g : γ → β) : f = e.symm ∘ g ↔ e ∘ f = g :=
  ((Equiv.refl γ).arrowCongr e).eq_symm_apply
#align equiv.eq_symm_comp Equiv.eq_symm_comp

/- warning: equiv.symm_comp_eq -> Equiv.symm_comp_eq is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} (e : Equiv.{u1, u2} α β) (f : γ -> α) (g : γ -> β), Iff (Eq.{imax u3 u1} (γ -> α) (Function.comp.{u3, u2, u1} γ β α (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β e)) g) f) (Eq.{imax u3 u2} (γ -> β) g (Function.comp.{u3, u1, u2} γ α β (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α β) (fun (_x : Equiv.{u1, u2} α β) => α -> β) (Equiv.hasCoeToFun.{u1, u2} α β) e) f))
but is expected to have type
  forall {α : Sort.{u3}} {β : Sort.{u2}} {γ : Sort.{u1}} (e : Equiv.{u3, u2} α β) (f : γ -> α) (g : γ -> β), Iff (Eq.{imax u1 u3} (γ -> α) (Function.comp.{u1, u2, u3} γ β α (FunLike.coe.{max (max 1 u2) u3, u2, u3} (Equiv.{u2, u3} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u3, u2, u3} (Equiv.{u2, u3} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u2) u3, u2, u3} (Equiv.{u2, u3} β α) β α (Equiv.instEquivLikeEquiv.{u2, u3} β α))) (Equiv.symm.{u3, u2} α β e)) g) f) (Eq.{imax u1 u2} (γ -> β) g (Function.comp.{u1, u3, u2} γ α β (FunLike.coe.{max (max 1 u2) u3, u3, u2} (Equiv.{u3, u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (max 1 u2) u3, u3, u2} (Equiv.{u3, u2} α β) α β (EquivLike.toEmbeddingLike.{max (max 1 u2) u3, u3, u2} (Equiv.{u3, u2} α β) α β (Equiv.instEquivLikeEquiv.{u3, u2} α β))) e) f))
Case conversion may be inaccurate. Consider using '#align equiv.symm_comp_eq Equiv.symm_comp_eqₓ'. -/
theorem symm_comp_eq {α β γ} (e : α ≃ β) (f : γ → α) (g : γ → β) : e.symm ∘ g = f ↔ g = e ∘ f :=
  ((Equiv.refl γ).arrowCongr e).symm_apply_eq
#align equiv.symm_comp_eq Equiv.symm_comp_eq

#print Equiv.punitEquivPUnit /-
/-- `punit` sorts in any two universes are equivalent. -/
def punitEquivPUnit : PUnit.{v} ≃ PUnit.{w} :=
  ⟨fun _ => PUnit.unit, fun _ => PUnit.unit, fun u =>
    by
    cases u
    rfl, fun u => by
    cases u
    rfl⟩
#align equiv.punit_equiv_punit Equiv.punitEquivPUnit
-/

#print Equiv.propEquivBool /-
/-- `Prop` is noncomputably equivalent to `bool`. -/
noncomputable def propEquivBool : Prop ≃ Bool :=
  ⟨fun p => @decide p (Classical.propDecidable _), fun b => b, fun p => by simp, fun b => by simp⟩
#align equiv.Prop_equiv_bool Equiv.propEquivBool
-/

section

#print Equiv.arrowPUnitEquivPUnit /-
/-- The sort of maps to `punit.{v}` is equivalent to `punit.{w}`. -/
def arrowPUnitEquivPUnit (α : Sort _) : (α → PUnit.{v}) ≃ PUnit.{w} :=
  ⟨fun f => PUnit.unit, fun u f => PUnit.unit, fun f =>
    by
    funext x
    cases f x
    rfl, fun u => by
    cases u
    rfl⟩
#align equiv.arrow_punit_equiv_punit Equiv.arrowPUnitEquivPUnit
-/

#print Equiv.piSubsingleton /-
/-- If `α` is `subsingleton` and `a : α`, then the type of dependent functions `Π (i : α), β
i` is equivalent to `β i`. -/
@[simps]
def piSubsingleton {α} (β : α → Sort _) [Subsingleton α] (a : α) : (∀ a', β a') ≃ β a
    where
  toFun := eval a
  invFun x b := cast (congr_arg β <| Subsingleton.elim a b) x
  left_inv f :=
    funext fun b => by
      rw [Subsingleton.elim b a]
      rfl
  right_inv b := rfl
#align equiv.Pi_subsingleton Equiv.piSubsingleton
-/

#print Equiv.funUnique /-
/-- If `α` has a unique term, then the type of function `α → β` is equivalent to `β`. -/
@[simps (config := { fullyApplied := false })]
def funUnique (α β) [Unique α] : (α → β) ≃ β :=
  piSubsingleton _ default
#align equiv.fun_unique Equiv.funUnique
-/

#print Equiv.punitArrowEquiv /-
/-- The sort of maps from `punit` is equivalent to the codomain. -/
def punitArrowEquiv (α : Sort _) : (PUnit.{u} → α) ≃ α :=
  funUnique _ _
#align equiv.punit_arrow_equiv Equiv.punitArrowEquiv
-/

#print Equiv.trueArrowEquiv /-
/-- The sort of maps from `true` is equivalent to the codomain. -/
def trueArrowEquiv (α : Sort _) : (True → α) ≃ α :=
  funUnique _ _
#align equiv.true_arrow_equiv Equiv.trueArrowEquiv
-/

/-- The sort of maps from a type that `is_empty` is equivalent to `punit`. -/
def arrowPunitOfIsEmpty (α β : Sort _) [IsEmpty α] : (α → β) ≃ PUnit.{u} :=
  ⟨fun f => PUnit.unit, fun u => isEmptyElim, fun f => funext isEmptyElim, fun u =>
    by
    cases u
    rfl⟩
#align equiv.arrow_punit_of_is_empty Equiv.arrowPunitOfIsEmpty

#print Equiv.emptyArrowEquivPUnit /-
/-- The sort of maps from `empty` is equivalent to `punit`. -/
def emptyArrowEquivPUnit (α : Sort _) : (Empty → α) ≃ PUnit.{u} :=
  arrowPunitOfIsEmpty _ _
#align equiv.empty_arrow_equiv_punit Equiv.emptyArrowEquivPUnit
-/

#print Equiv.pemptyArrowEquivPUnit /-
/-- The sort of maps from `pempty` is equivalent to `punit`. -/
def pemptyArrowEquivPUnit (α : Sort _) : (PEmpty → α) ≃ PUnit.{u} :=
  arrowPunitOfIsEmpty _ _
#align equiv.pempty_arrow_equiv_punit Equiv.pemptyArrowEquivPUnit
-/

#print Equiv.falseArrowEquivPUnit /-
/-- The sort of maps from `false` is equivalent to `punit`. -/
def falseArrowEquivPUnit (α : Sort _) : (False → α) ≃ PUnit.{u} :=
  arrowPunitOfIsEmpty _ _
#align equiv.false_arrow_equiv_punit Equiv.falseArrowEquivPUnit
-/

end

section

#print Equiv.psigmaEquivSigma /-
/-- A `psigma`-type is equivalent to the corresponding `sigma`-type. -/
@[simps apply symmApply]
def psigmaEquivSigma {α} (β : α → Type _) : (Σ'i, β i) ≃ Σi, β i :=
  ⟨fun a => ⟨a.1, a.2⟩, fun a => ⟨a.1, a.2⟩, fun ⟨a, b⟩ => rfl, fun ⟨a, b⟩ => rfl⟩
#align equiv.psigma_equiv_sigma Equiv.psigmaEquivSigma
-/

#print Equiv.psigmaEquivSigmaPLift /-
/-- A `psigma`-type is equivalent to the corresponding `sigma`-type. -/
@[simps apply symmApply]
def psigmaEquivSigmaPLift {α} (β : α → Sort _) : (Σ'i, β i) ≃ Σi : PLift α, PLift (β i.down) :=
  ⟨fun a => ⟨PLift.up a.1, PLift.up a.2⟩, fun a => ⟨a.1.down, a.2.down⟩, fun ⟨a, b⟩ => rfl,
    fun ⟨⟨a⟩, ⟨b⟩⟩ => rfl⟩
#align equiv.psigma_equiv_sigma_plift Equiv.psigmaEquivSigmaPLift
-/

#print Equiv.psigmaCongrRight /-
/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ' a, β₁ a` and
`Σ' a, β₂ a`. -/
@[simps apply]
def psigmaCongrRight {α} {β₁ β₂ : α → Sort _} (F : ∀ a, β₁ a ≃ β₂ a) : (Σ'a, β₁ a) ≃ Σ'a, β₂ a :=
  ⟨fun a => ⟨a.1, F a.1 a.2⟩, fun a => ⟨a.1, (F a.1).symm a.2⟩, fun ⟨a, b⟩ =>
    congr_arg (PSigma.mk a) <| symm_apply_apply (F a) b, fun ⟨a, b⟩ =>
    congr_arg (PSigma.mk a) <| apply_symm_apply (F a) b⟩
#align equiv.psigma_congr_right Equiv.psigmaCongrRight
-/

/- warning: equiv.psigma_congr_right_trans -> Equiv.psigmaCongrRight_trans is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β₁ : α -> Sort.{u2}} {β₂ : α -> Sort.{u3}} {β₃ : α -> Sort.{u4}} (F : forall (a : α), Equiv.{u2, u3} (β₁ a) (β₂ a)) (G : forall (a : α), Equiv.{u3, u4} (β₂ a) (β₃ a)), Eq.{max 1 (max (max 1 u1 u2) 1 u1 u4) (max 1 u1 u4) 1 u1 u2} (Equiv.{max 1 u1 u2, max 1 u1 u4} (PSigma.{u1, u2} α (fun (a : α) => β₁ a)) (PSigma.{u1, u4} α (fun (a : α) => β₃ a))) (Equiv.trans.{max 1 u1 u2, max 1 u1 u3, max 1 u1 u4} (PSigma.{u1, u2} α (fun (a : α) => β₁ a)) (PSigma.{u1, u3} α (fun (a : α) => β₂ a)) (PSigma.{u1, u4} α (fun (a : α) => β₃ a)) (Equiv.psigmaCongrRight.{u1, u2, u3} α (fun (a : α) => β₁ a) (fun (a : α) => β₂ a) F) (Equiv.psigmaCongrRight.{u1, u3, u4} α (fun (a : α) => β₂ a) (fun (a : α) => β₃ a) G)) (Equiv.psigmaCongrRight.{u1, u2, u4} α (fun (a : α) => β₁ a) (fun (a : α) => β₃ a) (fun (a : α) => Equiv.trans.{u2, u3, u4} (β₁ a) (β₂ a) (β₃ a) (F a) (G a)))
but is expected to have type
  forall {α : Sort.{u4}} {β₁ : α -> Sort.{u3}} {β₂ : α -> Sort.{u2}} {β₃ : α -> Sort.{u1}} (F : forall (a : α), Equiv.{u3, u2} (β₁ a) (β₂ a)) (G : forall (a : α), Equiv.{u2, u1} (β₂ a) (β₃ a)), Eq.{max (max (max 1 u4) u3) u1} (Equiv.{max (max 1 u4) u3, max (max 1 u4) u1} (PSigma.{u4, u3} α (fun (a : α) => β₁ a)) (PSigma.{u4, u1} α (fun (a : α) => β₃ a))) (Equiv.trans.{max (max 1 u4) u3, max (max 1 u4) u2, max (max 1 u4) u1} (PSigma.{u4, u3} α (fun (a : α) => β₁ a)) (PSigma.{u4, u2} α (fun (a : α) => β₂ a)) (PSigma.{u4, u1} α (fun (a : α) => β₃ a)) (Equiv.psigmaCongrRight.{u4, u3, u2} α (fun (a : α) => β₁ a) (fun (a : α) => β₂ a) F) (Equiv.psigmaCongrRight.{u4, u2, u1} α (fun (a : α) => β₂ a) (fun (a : α) => β₃ a) G)) (Equiv.psigmaCongrRight.{u4, u3, u1} α (fun (a : α) => β₁ a) (fun (a : α) => β₃ a) (fun (a : α) => Equiv.trans.{u3, u2, u1} (β₁ a) (β₂ a) (β₃ a) (F a) (G a)))
Case conversion may be inaccurate. Consider using '#align equiv.psigma_congr_right_trans Equiv.psigmaCongrRight_transₓ'. -/
@[simp]
theorem psigmaCongrRight_trans {α} {β₁ β₂ β₃ : α → Sort _} (F : ∀ a, β₁ a ≃ β₂ a)
    (G : ∀ a, β₂ a ≃ β₃ a) :
    (psigmaCongrRight F).trans (psigmaCongrRight G) = psigmaCongrRight fun a => (F a).trans (G a) :=
  by
  ext1 x
  cases x
  rfl
#align equiv.psigma_congr_right_trans Equiv.psigmaCongrRight_trans

/- warning: equiv.psigma_congr_right_symm -> Equiv.psigmaCongrRight_symm is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β₁ : α -> Sort.{u2}} {β₂ : α -> Sort.{u3}} (F : forall (a : α), Equiv.{u2, u3} (β₁ a) (β₂ a)), Eq.{max 1 (max (max 1 u1 u3) 1 u1 u2) (max 1 u1 u2) 1 u1 u3} (Equiv.{max 1 u1 u3, max 1 u1 u2} (PSigma.{u1, u3} α (fun (a : α) => β₂ a)) (PSigma.{u1, u2} α (fun (a : α) => β₁ a))) (Equiv.symm.{max 1 u1 u2, max 1 u1 u3} (PSigma.{u1, u2} α (fun (a : α) => β₁ a)) (PSigma.{u1, u3} α (fun (a : α) => β₂ a)) (Equiv.psigmaCongrRight.{u1, u2, u3} α (fun (a : α) => β₁ a) (fun (a : α) => β₂ a) F)) (Equiv.psigmaCongrRight.{u1, u3, u2} α (fun (a : α) => β₂ a) (fun (a : α) => β₁ a) (fun (a : α) => Equiv.symm.{u2, u3} (β₁ a) (β₂ a) (F a)))
but is expected to have type
  forall {α : Sort.{u3}} {β₁ : α -> Sort.{u2}} {β₂ : α -> Sort.{u1}} (F : forall (a : α), Equiv.{u2, u1} (β₁ a) (β₂ a)), Eq.{max (max (max 1 u3) u2) u1} (Equiv.{max (max 1 u3) u1, max (max 1 u3) u2} (PSigma.{u3, u1} α (fun (a : α) => β₂ a)) (PSigma.{u3, u2} α (fun (a : α) => β₁ a))) (Equiv.symm.{max (max 1 u3) u2, max (max 1 u3) u1} (PSigma.{u3, u2} α (fun (a : α) => β₁ a)) (PSigma.{u3, u1} α (fun (a : α) => β₂ a)) (Equiv.psigmaCongrRight.{u3, u2, u1} α (fun (a : α) => β₁ a) (fun (a : α) => β₂ a) F)) (Equiv.psigmaCongrRight.{u3, u1, u2} α (fun (a : α) => β₂ a) (fun (a : α) => β₁ a) (fun (a : α) => Equiv.symm.{u2, u1} (β₁ a) (β₂ a) (F a)))
Case conversion may be inaccurate. Consider using '#align equiv.psigma_congr_right_symm Equiv.psigmaCongrRight_symmₓ'. -/
@[simp]
theorem psigmaCongrRight_symm {α} {β₁ β₂ : α → Sort _} (F : ∀ a, β₁ a ≃ β₂ a) :
    (psigmaCongrRight F).symm = psigmaCongrRight fun a => (F a).symm :=
  by
  ext1 x
  cases x
  rfl
#align equiv.psigma_congr_right_symm Equiv.psigmaCongrRight_symm

/- warning: equiv.psigma_congr_right_refl -> Equiv.psigmaCongrRight_refl is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : α -> Sort.{u2}}, Eq.{max 1 u1 u2} (Equiv.{max 1 u1 u2, max 1 u1 u2} (PSigma.{u1, u2} α (fun (a : α) => β a)) (PSigma.{u1, u2} α (fun (a : α) => β a))) (Equiv.psigmaCongrRight.{u1, u2, u2} α (fun (a : α) => β a) (fun (a : α) => β a) (fun (a : α) => Equiv.refl.{u2} (β a))) (Equiv.refl.{max 1 u1 u2} (PSigma.{u1, u2} α (fun (a : α) => β a)))
but is expected to have type
  forall {α : Sort.{u2}} {β : α -> Sort.{u1}}, Eq.{max (max 1 u2) u1} (Equiv.{max (max 1 u1) u2, max (max 1 u1) u2} (PSigma.{u2, u1} α (fun (a : α) => β a)) (PSigma.{u2, u1} α (fun (a : α) => β a))) (Equiv.psigmaCongrRight.{u2, u1, u1} α (fun (a : α) => β a) (fun (a : α) => β a) (fun (a : α) => Equiv.refl.{u1} (β a))) (Equiv.refl.{max (max 1 u1) u2} (PSigma.{u2, u1} α (fun (a : α) => β a)))
Case conversion may be inaccurate. Consider using '#align equiv.psigma_congr_right_refl Equiv.psigmaCongrRight_reflₓ'. -/
@[simp]
theorem psigmaCongrRight_refl {α} {β : α → Sort _} :
    (psigmaCongrRight fun a => Equiv.refl (β a)) = Equiv.refl (Σ'a, β a) :=
  by
  ext1 x
  cases x
  rfl
#align equiv.psigma_congr_right_refl Equiv.psigmaCongrRight_refl

#print Equiv.sigmaCongrRight /-
/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ a, β₁ a` and
`Σ a, β₂ a`. -/
@[simps apply]
def sigmaCongrRight {α} {β₁ β₂ : α → Type _} (F : ∀ a, β₁ a ≃ β₂ a) : (Σa, β₁ a) ≃ Σa, β₂ a :=
  ⟨fun a => ⟨a.1, F a.1 a.2⟩, fun a => ⟨a.1, (F a.1).symm a.2⟩, fun ⟨a, b⟩ =>
    congr_arg (Sigma.mk a) <| symm_apply_apply (F a) b, fun ⟨a, b⟩ =>
    congr_arg (Sigma.mk a) <| apply_symm_apply (F a) b⟩
#align equiv.sigma_congr_right Equiv.sigmaCongrRight
-/

/- warning: equiv.sigma_congr_right_trans clashes with equiv.sigmaCongrRight -> Equiv.sigmaCongrRight_trans
warning: equiv.sigma_congr_right_trans -> Equiv.sigmaCongrRight_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β₁ : α -> Type.{u2}} {β₂ : α -> Type.{u3}} {β₃ : α -> Type.{u4}} (F : forall (a : α), Equiv.{succ u2, succ u3} (β₁ a) (β₂ a)) (G : forall (a : α), Equiv.{succ u3, succ u4} (β₂ a) (β₃ a)), Eq.{max 1 (max (max (succ u1) (succ u2)) (succ u1) (succ u4)) (max (succ u1) (succ u4)) (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u4)} (Sigma.{u1, u2} α (fun (a : α) => β₁ a)) (Sigma.{u1, u4} α (fun (a : α) => β₃ a))) (Equiv.trans.{max (succ u1) (succ u2), max (succ u1) (succ u3), max (succ u1) (succ u4)} (Sigma.{u1, u2} α (fun (a : α) => β₁ a)) (Sigma.{u1, u3} α (fun (a : α) => β₂ a)) (Sigma.{u1, u4} α (fun (a : α) => β₃ a)) (Equiv.sigmaCongrRight.{u1, u2, u3} α (fun (a : α) => β₁ a) (fun (a : α) => β₂ a) F) (Equiv.sigmaCongrRight.{u1, u3, u4} α (fun (a : α) => β₂ a) (fun (a : α) => β₃ a) G)) (Equiv.sigmaCongrRight.{u1, u2, u4} α (fun (a : α) => β₁ a) (fun (a : α) => β₃ a) (fun (a : α) => Equiv.trans.{succ u2, succ u3, succ u4} (β₁ a) (β₂ a) (β₃ a) (F a) (G a)))
but is expected to have type
  forall {α : Type.{u4}} {β₁ : α -> Type.{u3}} {β₂ : α -> Type.{u2}} {β₃ : α -> Type.{u1}} (F : forall (a : α), Equiv.{succ u3, succ u2} (β₁ a) (β₂ a)) (G : forall (a : α), Equiv.{succ u2, succ u1} (β₂ a) (β₃ a)), Eq.{max (max (succ u3) (succ u1)) (succ u4)} (Equiv.{max (succ u3) (succ u4), max (succ u4) (succ u1)} (Sigma.{u4, u3} α (fun (a : α) => β₁ a)) (Sigma.{u4, u1} α (fun (a : α) => β₃ a))) (Equiv.trans.{max (succ u3) (succ u4), max (succ u2) (succ u4), max (succ u4) (succ u1)} (Sigma.{u4, u3} α (fun (a : α) => β₁ a)) (Sigma.{u4, u2} α (fun (a : α) => β₂ a)) (Sigma.{u4, u1} α (fun (a : α) => β₃ a)) (Equiv.sigmaCongrRight.{u4, u3, u2} α (fun (a : α) => β₁ a) (fun (a : α) => β₂ a) F) (Equiv.sigmaCongrRight.{u4, u2, u1} α (fun (a : α) => β₂ a) (fun (a : α) => β₃ a) G)) (Equiv.sigmaCongrRight.{u4, u3, u1} α (fun (a : α) => β₁ a) (fun (a : α) => β₃ a) (fun (a : α) => Equiv.trans.{succ u3, succ u2, succ u1} (β₁ a) (β₂ a) (β₃ a) (F a) (G a)))
Case conversion may be inaccurate. Consider using '#align equiv.sigma_congr_right_trans Equiv.sigmaCongrRight_transₓ'. -/
@[simp]
theorem sigmaCongrRight_trans {α} {β₁ β₂ β₃ : α → Type _} (F : ∀ a, β₁ a ≃ β₂ a)
    (G : ∀ a, β₂ a ≃ β₃ a) :
    (sigmaCongrRight F).trans (sigmaCongrRight G) = sigmaCongrRight fun a => (F a).trans (G a) :=
  by
  ext1 x
  cases x
  rfl
#align equiv.sigma_congr_right_trans Equiv.sigmaCongrRight_trans

/- warning: equiv.sigma_congr_right_symm -> Equiv.sigmaCongrRight_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β₁ : α -> Type.{u2}} {β₂ : α -> Type.{u3}} (F : forall (a : α), Equiv.{succ u2, succ u3} (β₁ a) (β₂ a)), Eq.{max 1 (max (max (succ u1) (succ u3)) (succ u1) (succ u2)) (max (succ u1) (succ u2)) (succ u1) (succ u3)} (Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u2)} (Sigma.{u1, u3} α (fun (a : α) => β₂ a)) (Sigma.{u1, u2} α (fun (a : α) => β₁ a))) (Equiv.symm.{max (succ u1) (succ u2), max (succ u1) (succ u3)} (Sigma.{u1, u2} α (fun (a : α) => β₁ a)) (Sigma.{u1, u3} α (fun (a : α) => β₂ a)) (Equiv.sigmaCongrRight.{u1, u2, u3} α (fun (a : α) => β₁ a) (fun (a : α) => β₂ a) F)) (Equiv.sigmaCongrRight.{u1, u3, u2} α (fun (a : α) => β₂ a) (fun (a : α) => β₁ a) (fun (a : α) => Equiv.symm.{succ u2, succ u3} (β₁ a) (β₂ a) (F a)))
but is expected to have type
  forall {α : Type.{u3}} {β₁ : α -> Type.{u2}} {β₂ : α -> Type.{u1}} (F : forall (a : α), Equiv.{succ u2, succ u1} (β₁ a) (β₂ a)), Eq.{max (max (succ u2) (succ u1)) (succ u3)} (Equiv.{max (succ u1) (succ u3), max (succ u2) (succ u3)} (Sigma.{u3, u1} α (fun (a : α) => β₂ a)) (Sigma.{u3, u2} α (fun (a : α) => β₁ a))) (Equiv.symm.{max (succ u2) (succ u3), max (succ u1) (succ u3)} (Sigma.{u3, u2} α (fun (a : α) => β₁ a)) (Sigma.{u3, u1} α (fun (a : α) => β₂ a)) (Equiv.sigmaCongrRight.{u3, u2, u1} α (fun (a : α) => β₁ a) (fun (a : α) => β₂ a) F)) (Equiv.sigmaCongrRight.{u3, u1, u2} α (fun (a : α) => β₂ a) (fun (a : α) => β₁ a) (fun (a : α) => Equiv.symm.{succ u2, succ u1} (β₁ a) (β₂ a) (F a)))
Case conversion may be inaccurate. Consider using '#align equiv.sigma_congr_right_symm Equiv.sigmaCongrRight_symmₓ'. -/
@[simp]
theorem sigmaCongrRight_symm {α} {β₁ β₂ : α → Type _} (F : ∀ a, β₁ a ≃ β₂ a) :
    (sigmaCongrRight F).symm = sigmaCongrRight fun a => (F a).symm :=
  by
  ext1 x
  cases x
  rfl
#align equiv.sigma_congr_right_symm Equiv.sigmaCongrRight_symm

/- warning: equiv.sigma_congr_right_refl -> Equiv.sigmaCongrRight_refl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}}, Eq.{max 1 (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a)) (Sigma.{u1, u2} α (fun (a : α) => β a))) (Equiv.sigmaCongrRight.{u1, u2, u2} α (fun (a : α) => β a) (fun (a : α) => β a) (fun (a : α) => Equiv.refl.{succ u2} (β a))) (Equiv.refl.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a)))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}}, Eq.{max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a)) (Sigma.{u2, u1} α (fun (a : α) => β a))) (Equiv.sigmaCongrRight.{u2, u1, u1} α (fun (a : α) => β a) (fun (a : α) => β a) (fun (a : α) => Equiv.refl.{succ u1} (β a))) (Equiv.refl.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a)))
Case conversion may be inaccurate. Consider using '#align equiv.sigma_congr_right_refl Equiv.sigmaCongrRight_reflₓ'. -/
@[simp]
theorem sigmaCongrRight_refl {α} {β : α → Type _} :
    (sigmaCongrRight fun a => Equiv.refl (β a)) = Equiv.refl (Σa, β a) :=
  by
  ext1 x
  cases x
  rfl
#align equiv.sigma_congr_right_refl Equiv.sigmaCongrRight_refl

#print Equiv.psigmaEquivSubtype /-
/-- A `psigma` with `Prop` fibers is equivalent to the subtype.  -/
def psigmaEquivSubtype {α : Type v} (P : α → Prop) : (Σ'i, P i) ≃ Subtype P
    where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv x := by
    cases x
    rfl
  right_inv x := by
    cases x
    rfl
#align equiv.psigma_equiv_subtype Equiv.psigmaEquivSubtype
-/

#print Equiv.sigmaPLiftEquivSubtype /-
/-- A `sigma` with `plift` fibers is equivalent to the subtype. -/
def sigmaPLiftEquivSubtype {α : Type v} (P : α → Prop) : (Σi, PLift (P i)) ≃ Subtype P :=
  ((psigmaEquivSigma _).symm.trans (psigmaCongrRight fun a => Equiv.plift)).trans
    (psigmaEquivSubtype P)
#align equiv.sigma_plift_equiv_subtype Equiv.sigmaPLiftEquivSubtype
-/

#print Equiv.sigmaULiftPLiftEquivSubtype /-
/-- A `sigma` with `λ i, ulift (plift (P i))` fibers is equivalent to `{ x // P x }`.
Variant of `sigma_plift_equiv_subtype`.
-/
def sigmaULiftPLiftEquivSubtype {α : Type v} (P : α → Prop) :
    (Σi, ULift (PLift (P i))) ≃ Subtype P :=
  (sigmaCongrRight fun a => Equiv.ulift).trans (sigmaPLiftEquivSubtype P)
#align equiv.sigma_ulift_plift_equiv_subtype Equiv.sigmaULiftPLiftEquivSubtype
-/

namespace Perm

#print Equiv.Perm.sigmaCongrRight /-
/-- A family of permutations `Π a, perm (β a)` generates a permuation `perm (Σ a, β₁ a)`. -/
@[reducible]
def sigmaCongrRight {α} {β : α → Sort _} (F : ∀ a, Perm (β a)) : Perm (Σa, β a) :=
  Equiv.sigmaCongrRight F
#align equiv.perm.sigma_congr_right Equiv.Perm.sigmaCongrRight
-/

/- warning: equiv.perm.sigma_congr_right_trans -> Equiv.Perm.sigmaCongrRight_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} (F : forall (a : α), Equiv.Perm.{succ u2} (β a)) (G : forall (a : α), Equiv.Perm.{succ u2} (β a)), Eq.{max 1 (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a)) (Sigma.{u1, u2} α (fun (a : α) => β a))) (Equiv.trans.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a)) (Sigma.{u1, u2} α (fun (a : α) => β a)) (Sigma.{u1, u2} α (fun (a : α) => β a)) (Equiv.Perm.sigmaCongrRight.{u1, u2} α (fun (a : α) => β a) F) (Equiv.Perm.sigmaCongrRight.{u1, u2} α (fun (a : α) => β a) G)) (Equiv.Perm.sigmaCongrRight.{u1, u2} α (fun (a : α) => β a) (fun (a : α) => Equiv.trans.{succ u2, succ u2, succ u2} (β a) (β a) (β a) (F a) (G a)))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} (F : forall (a : α), Equiv.Perm.{succ u1} (β a)) (G : forall (a : α), Equiv.Perm.{succ u1} (β a)), Eq.{max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a)) (Sigma.{u2, u1} α (fun (a : α) => β a))) (Equiv.trans.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a)) (Sigma.{u2, u1} α (fun (a : α) => β a)) (Sigma.{u2, u1} α (fun (a : α) => β a)) (Equiv.Perm.sigmaCongrRight.{u2, u1} α (fun (a : α) => β a) F) (Equiv.Perm.sigmaCongrRight.{u2, u1} α (fun (a : α) => β a) G)) (Equiv.Perm.sigmaCongrRight.{u2, u1} α (fun (a : α) => β a) (fun (a : α) => Equiv.trans.{succ u1, succ u1, succ u1} (β a) (β a) (β a) (F a) (G a)))
Case conversion may be inaccurate. Consider using '#align equiv.perm.sigma_congr_right_trans Equiv.Perm.sigmaCongrRight_transₓ'. -/
@[simp]
theorem sigmaCongrRight_trans {α} {β : α → Sort _} (F : ∀ a, Perm (β a)) (G : ∀ a, Perm (β a)) :
    (sigmaCongrRight F).trans (sigmaCongrRight G) = sigmaCongrRight fun a => (F a).trans (G a) :=
  Equiv.sigmaCongrRight_trans F G
#align equiv.perm.sigma_congr_right_trans Equiv.Perm.sigmaCongrRight_trans

/- warning: equiv.perm.sigma_congr_right_symm -> Equiv.Perm.sigmaCongrRight_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} (F : forall (a : α), Equiv.Perm.{succ u2} (β a)), Eq.{max 1 (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a)) (Sigma.{u1, u2} α (fun (a : α) => β a))) (Equiv.symm.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a)) (Sigma.{u1, u2} α (fun (a : α) => β a)) (Equiv.Perm.sigmaCongrRight.{u1, u2} α (fun (a : α) => β a) F)) (Equiv.Perm.sigmaCongrRight.{u1, u2} α (fun (a : α) => β a) (fun (a : α) => Equiv.symm.{succ u2, succ u2} (β a) (β a) (F a)))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} (F : forall (a : α), Equiv.Perm.{succ u1} (β a)), Eq.{max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a)) (Sigma.{u2, u1} α (fun (a : α) => β a))) (Equiv.symm.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a)) (Sigma.{u2, u1} α (fun (a : α) => β a)) (Equiv.Perm.sigmaCongrRight.{u2, u1} α (fun (a : α) => β a) F)) (Equiv.Perm.sigmaCongrRight.{u2, u1} α (fun (a : α) => β a) (fun (a : α) => Equiv.symm.{succ u1, succ u1} (β a) (β a) (F a)))
Case conversion may be inaccurate. Consider using '#align equiv.perm.sigma_congr_right_symm Equiv.Perm.sigmaCongrRight_symmₓ'. -/
@[simp]
theorem sigmaCongrRight_symm {α} {β : α → Sort _} (F : ∀ a, Perm (β a)) :
    (sigmaCongrRight F).symm = sigmaCongrRight fun a => (F a).symm :=
  Equiv.sigmaCongrRight_symm F
#align equiv.perm.sigma_congr_right_symm Equiv.Perm.sigmaCongrRight_symm

/- warning: equiv.perm.sigma_congr_right_refl -> Equiv.Perm.sigmaCongrRight_refl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}}, Eq.{max 1 (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Equiv.Perm.sigmaCongrRight.{u1, u2} α (fun (a : α) => β a) (fun (a : α) => Equiv.refl.{succ u2} (β a))) (Equiv.refl.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a)))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}}, Eq.{max (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Equiv.Perm.sigmaCongrRight.{u2, u1} α (fun (a : α) => β a) (fun (a : α) => Equiv.refl.{succ u1} (β a))) (Equiv.refl.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a)))
Case conversion may be inaccurate. Consider using '#align equiv.perm.sigma_congr_right_refl Equiv.Perm.sigmaCongrRight_reflₓ'. -/
@[simp]
theorem sigmaCongrRight_refl {α} {β : α → Sort _} :
    (sigmaCongrRight fun a => Equiv.refl (β a)) = Equiv.refl (Σa, β a) :=
  Equiv.sigmaCongrRight_refl
#align equiv.perm.sigma_congr_right_refl Equiv.Perm.sigmaCongrRight_refl

end Perm

/- warning: equiv.sigma_congr_left -> Equiv.sigmaCongrLeft is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {α₂ : Type.{u2}} {β : α₂ -> Type.{u3}} (e : Equiv.{succ u1, succ u2} α₁ α₂), Equiv.{max (succ u1) (succ u3), max (succ u2) (succ u3)} (Sigma.{u1, u3} α₁ (fun (a : α₁) => β (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α₁ α₂) (fun (_x : Equiv.{succ u1, succ u2} α₁ α₂) => α₁ -> α₂) (Equiv.hasCoeToFun.{succ u1, succ u2} α₁ α₂) e a))) (Sigma.{u2, u3} α₂ (fun (a : α₂) => β a))
but is expected to have type
  forall {α₁ : Type.{u1}} {α₂ : Type.{u2}} {β : α₁ -> Type.{u3}} (e : Equiv.{succ u2, succ u1} α₂ α₁), Equiv.{max (succ u3) (succ u2), max (succ u3) (succ u1)} (Sigma.{u2, u3} α₂ (fun (a : α₂) => β (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} α₂ α₁) α₂ (fun (_x : α₂) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α₂) => α₁) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} α₂ α₁) α₂ α₁ (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} α₂ α₁) α₂ α₁ (Equiv.instEquivLikeEquiv.{succ u2, succ u1} α₂ α₁))) e a))) (Sigma.{u1, u3} α₁ (fun (a : α₁) => β a))
Case conversion may be inaccurate. Consider using '#align equiv.sigma_congr_left Equiv.sigmaCongrLeftₓ'. -/
/-- An equivalence `f : α₁ ≃ α₂` generates an equivalence between `Σ a, β (f a)` and `Σ a, β a`. -/
@[simps apply]
def sigmaCongrLeft {α₁ α₂} {β : α₂ → Sort _} (e : α₁ ≃ α₂) : (Σa : α₁, β (e a)) ≃ Σa : α₂, β a :=
  ⟨fun a => ⟨e a.1, a.2⟩, fun a => ⟨e.symm a.1, @Eq.ndrec β a.2 (e.right_inv a.1).symm⟩,
    fun ⟨a, b⟩ =>
    match (motive :=
      ∀ (a') (h : a' = a), @Sigma.mk _ (β ∘ e) _ (@Eq.ndrec β b (congr_arg e h.symm)) = ⟨a, b⟩)
      e.symm (e a), e.left_inv a with
    | _, rfl => rfl,
    fun ⟨a, b⟩ =>
    match (motive := ∀ (a') (h : a' = a), Sigma.mk a' (@Eq.ndrec β b h.symm) = ⟨a, b⟩) e (e.symm a),
      _ with
    | _, rfl => rfl⟩
#align equiv.sigma_congr_left Equiv.sigmaCongrLeft

#print Equiv.sigmaCongrLeft' /-
/-- Transporting a sigma type through an equivalence of the base -/
def sigmaCongrLeft' {α₁ α₂} {β : α₁ → Sort _} (f : α₁ ≃ α₂) :
    (Σa : α₁, β a) ≃ Σa : α₂, β (f.symm a) :=
  (sigmaCongrLeft f.symm).symm
#align equiv.sigma_congr_left' Equiv.sigmaCongrLeft'
-/

#print Equiv.sigmaCongr /-
/-- Transporting a sigma type through an equivalence of the base and a family of equivalences
of matching fibers -/
def sigmaCongr {α₁ α₂} {β₁ : α₁ → Sort _} {β₂ : α₂ → Sort _} (f : α₁ ≃ α₂)
    (F : ∀ a, β₁ a ≃ β₂ (f a)) : Sigma β₁ ≃ Sigma β₂ :=
  (sigmaCongrRight F).trans (sigmaCongrLeft f)
#align equiv.sigma_congr Equiv.sigmaCongr
-/

#print Equiv.sigmaEquivProd /-
/-- `sigma` type with a constant fiber is equivalent to the product. -/
@[simps apply symmApply]
def sigmaEquivProd (α β : Type _) : (Σ_ : α, β) ≃ α × β :=
  ⟨fun a => ⟨a.1, a.2⟩, fun a => ⟨a.1, a.2⟩, fun ⟨a, b⟩ => rfl, fun ⟨a, b⟩ => rfl⟩
#align equiv.sigma_equiv_prod Equiv.sigmaEquivProd
-/

#print Equiv.sigmaEquivProdOfEquiv /-
/-- If each fiber of a `sigma` type is equivalent to a fixed type, then the sigma type
is equivalent to the product. -/
def sigmaEquivProdOfEquiv {α β} {β₁ : α → Sort _} (F : ∀ a, β₁ a ≃ β) : Sigma β₁ ≃ α × β :=
  (sigmaCongrRight F).trans (sigmaEquivProd α β)
#align equiv.sigma_equiv_prod_of_equiv Equiv.sigmaEquivProdOfEquiv
-/

#print Equiv.sigmaAssoc /-
/-- Dependent product of types is associative up to an equivalence. -/
def sigmaAssoc {α : Type _} {β : α → Type _} (γ : ∀ a : α, β a → Type _) :
    (Σab : Σa : α, β a, γ ab.1 ab.2) ≃ Σa : α, Σb : β a, γ a b
    where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv := fun ⟨⟨a, b⟩, c⟩ => rfl
  right_inv := fun ⟨a, ⟨b, c⟩⟩ => rfl
#align equiv.sigma_assoc Equiv.sigmaAssoc
-/

end

protected theorem existsUnique_congr {p : α → Prop} {q : β → Prop} (f : α ≃ β)
    (h : ∀ {x}, p x ↔ q (f x)) : (∃! x, p x) ↔ ∃! y, q y :=
  by
  constructor
  · rintro ⟨a, ha₁, ha₂⟩
    exact ⟨f a, h.1 ha₁, fun b hb => f.symm_apply_eq.1 (ha₂ (f.symm b) (h.2 (by simpa using hb)))⟩
  · rintro ⟨b, hb₁, hb₂⟩
    exact ⟨f.symm b, h.2 (by simpa using hb₁), fun y hy => (eq_symm_apply f).2 (hb₂ _ (h.1 hy))⟩
#align equiv.exists_unique_congr Equiv.existsUnique_congr

protected theorem existsUnique_congr_left' {p : α → Prop} (f : α ≃ β) :
    (∃! x, p x) ↔ ∃! y, p (f.symm y) :=
  Equiv.existsUnique_congr f fun x => by simp
#align equiv.exists_unique_congr_left' Equiv.existsUnique_congr_left'

protected theorem existsUnique_congr_left {p : β → Prop} (f : α ≃ β) :
    (∃! x, p (f x)) ↔ ∃! y, p y :=
  (Equiv.existsUnique_congr_left' f.symm).symm
#align equiv.exists_unique_congr_left Equiv.existsUnique_congr_left

#print Equiv.forall_congr /-
protected theorem forall_congr {p : α → Prop} {q : β → Prop} (f : α ≃ β)
    (h : ∀ {x}, p x ↔ q (f x)) : (∀ x, p x) ↔ ∀ y, q y :=
  by
  constructor <;> intro h₂ x
  · rw [← f.right_inv x]
    apply h.mp
    apply h₂
  apply h.mpr; apply h₂
#align equiv.forall_congr Equiv.forall_congr
-/

#print Equiv.forall_congr' /-
protected theorem forall_congr' {p : α → Prop} {q : β → Prop} (f : α ≃ β)
    (h : ∀ {x}, p (f.symm x) ↔ q x) : (∀ x, p x) ↔ ∀ y, q y :=
  (Equiv.forall_congr f.symm fun x => h.symm).symm
#align equiv.forall_congr' Equiv.forall_congr'
-/

-- We next build some higher arity versions of `equiv.forall_congr`.
-- Although they appear to just be repeated applications of `equiv.forall_congr`,
-- unification of metavariables works better with these versions.
-- In particular, they are necessary in `equiv_rw`.
-- (Stopping at ternary functions seems reasonable: at least in 1-categorical mathematics,
-- it's rare to have axioms involving more than 3 elements at once.)
universe ua1 ua2 ub1 ub2 ug1 ug2

variable {α₁ : Sort ua1} {α₂ : Sort ua2} {β₁ : Sort ub1} {β₂ : Sort ub2} {γ₁ : Sort ug1}
  {γ₂ : Sort ug2}

/- warning: equiv.forall₂_congr -> Equiv.forall₂_congr is a dubious translation:
lean 3 declaration is
  forall {α₁ : Sort.{u1}} {α₂ : Sort.{u2}} {β₁ : Sort.{u3}} {β₂ : Sort.{u4}} {p : α₁ -> β₁ -> Prop} {q : α₂ -> β₂ -> Prop} (eα : Equiv.{u1, u2} α₁ α₂) (eβ : Equiv.{u3, u4} β₁ β₂), (forall {x : α₁} {y : β₁}, Iff (p x y) (q (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α₁ α₂) (fun (_x : Equiv.{u1, u2} α₁ α₂) => α₁ -> α₂) (Equiv.hasCoeToFun.{u1, u2} α₁ α₂) eα x) (coeFn.{max 1 (imax u3 u4) (imax u4 u3), imax u3 u4} (Equiv.{u3, u4} β₁ β₂) (fun (_x : Equiv.{u3, u4} β₁ β₂) => β₁ -> β₂) (Equiv.hasCoeToFun.{u3, u4} β₁ β₂) eβ y))) -> (Iff (forall (x : α₁) (y : β₁), p x y) (forall (x : α₂) (y : β₂), q x y))
but is expected to have type
  forall {α₁ : Sort.{u4}} {α₂ : Sort.{u3}} {β₁ : Sort.{u2}} {β₂ : Sort.{u1}} {p : α₁ -> α₂ -> Prop} {q : β₁ -> β₂ -> Prop} (eα : Equiv.{u4, u2} α₁ β₁) (eβ : Equiv.{u3, u1} α₂ β₂), (forall {x : α₁} {y : α₂}, Iff (p x y) (q (FunLike.coe.{max (max 1 u4) u2, u4, u2} (Equiv.{u4, u2} α₁ β₁) α₁ (fun (_x : α₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α₁) => β₁) _x) (EmbeddingLike.toFunLike.{max (max 1 u4) u2, u4, u2} (Equiv.{u4, u2} α₁ β₁) α₁ β₁ (EquivLike.toEmbeddingLike.{max (max 1 u4) u2, u4, u2} (Equiv.{u4, u2} α₁ β₁) α₁ β₁ (Equiv.instEquivLikeEquiv.{u4, u2} α₁ β₁))) eα x) (FunLike.coe.{max (max 1 u3) u1, u3, u1} (Equiv.{u3, u1} α₂ β₂) α₂ (fun (_x : α₂) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α₂) => β₂) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u1, u3, u1} (Equiv.{u3, u1} α₂ β₂) α₂ β₂ (EquivLike.toEmbeddingLike.{max (max 1 u3) u1, u3, u1} (Equiv.{u3, u1} α₂ β₂) α₂ β₂ (Equiv.instEquivLikeEquiv.{u3, u1} α₂ β₂))) eβ y))) -> (Iff (forall (x : α₁) (y : α₂), p x y) (forall (x : β₁) (y : β₂), q x y))
Case conversion may be inaccurate. Consider using '#align equiv.forall₂_congr Equiv.forall₂_congrₓ'. -/
protected theorem forall₂_congr {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop} (eα : α₁ ≃ α₂)
    (eβ : β₁ ≃ β₂) (h : ∀ {x y}, p x y ↔ q (eα x) (eβ y)) : (∀ x y, p x y) ↔ ∀ x y, q x y :=
  by
  apply Equiv.forall_congr
  intros
  apply Equiv.forall_congr
  intros
  apply h
#align equiv.forall₂_congr Equiv.forall₂_congr

/- warning: equiv.forall₂_congr' -> Equiv.forall₂_congr' is a dubious translation:
lean 3 declaration is
  forall {α₁ : Sort.{u1}} {α₂ : Sort.{u2}} {β₁ : Sort.{u3}} {β₂ : Sort.{u4}} {p : α₁ -> β₁ -> Prop} {q : α₂ -> β₂ -> Prop} (eα : Equiv.{u1, u2} α₁ α₂) (eβ : Equiv.{u3, u4} β₁ β₂), (forall {x : α₂} {y : β₂}, Iff (p (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} α₂ α₁) (fun (_x : Equiv.{u2, u1} α₂ α₁) => α₂ -> α₁) (Equiv.hasCoeToFun.{u2, u1} α₂ α₁) (Equiv.symm.{u1, u2} α₁ α₂ eα) x) (coeFn.{max 1 (imax u4 u3) (imax u3 u4), imax u4 u3} (Equiv.{u4, u3} β₂ β₁) (fun (_x : Equiv.{u4, u3} β₂ β₁) => β₂ -> β₁) (Equiv.hasCoeToFun.{u4, u3} β₂ β₁) (Equiv.symm.{u3, u4} β₁ β₂ eβ) y)) (q x y)) -> (Iff (forall (x : α₁) (y : β₁), p x y) (forall (x : α₂) (y : β₂), q x y))
but is expected to have type
  forall {α₁ : Sort.{u4}} {α₂ : Sort.{u3}} {β₁ : Sort.{u2}} {β₂ : Sort.{u1}} {p : α₁ -> α₂ -> Prop} {q : β₁ -> β₂ -> Prop} (eα : Equiv.{u4, u2} α₁ β₁) (eβ : Equiv.{u3, u1} α₂ β₂), (forall {x : β₁} {y : β₂}, Iff (p (FunLike.coe.{max (max 1 u4) u2, u2, u4} (Equiv.{u2, u4} β₁ α₁) β₁ (fun (_x : β₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β₁) => α₁) _x) (EmbeddingLike.toFunLike.{max (max 1 u4) u2, u2, u4} (Equiv.{u2, u4} β₁ α₁) β₁ α₁ (EquivLike.toEmbeddingLike.{max (max 1 u4) u2, u2, u4} (Equiv.{u2, u4} β₁ α₁) β₁ α₁ (Equiv.instEquivLikeEquiv.{u2, u4} β₁ α₁))) (Equiv.symm.{u4, u2} α₁ β₁ eα) x) (FunLike.coe.{max (max 1 u3) u1, u1, u3} (Equiv.{u1, u3} β₂ α₂) β₂ (fun (_x : β₂) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β₂) => α₂) _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u1, u1, u3} (Equiv.{u1, u3} β₂ α₂) β₂ α₂ (EquivLike.toEmbeddingLike.{max (max 1 u3) u1, u1, u3} (Equiv.{u1, u3} β₂ α₂) β₂ α₂ (Equiv.instEquivLikeEquiv.{u1, u3} β₂ α₂))) (Equiv.symm.{u3, u1} α₂ β₂ eβ) y)) (q x y)) -> (Iff (forall (x : α₁) (y : α₂), p x y) (forall (x : β₁) (y : β₂), q x y))
Case conversion may be inaccurate. Consider using '#align equiv.forall₂_congr' Equiv.forall₂_congr'ₓ'. -/
protected theorem forall₂_congr' {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop} (eα : α₁ ≃ α₂)
    (eβ : β₁ ≃ β₂) (h : ∀ {x y}, p (eα.symm x) (eβ.symm y) ↔ q x y) :
    (∀ x y, p x y) ↔ ∀ x y, q x y :=
  (Equiv.forall₂_congr eα.symm eβ.symm fun x y => h.symm).symm
#align equiv.forall₂_congr' Equiv.forall₂_congr'

/- warning: equiv.forall₃_congr -> Equiv.forall₃_congr is a dubious translation:
lean 3 declaration is
  forall {α₁ : Sort.{u1}} {α₂ : Sort.{u2}} {β₁ : Sort.{u3}} {β₂ : Sort.{u4}} {γ₁ : Sort.{u5}} {γ₂ : Sort.{u6}} {p : α₁ -> β₁ -> γ₁ -> Prop} {q : α₂ -> β₂ -> γ₂ -> Prop} (eα : Equiv.{u1, u2} α₁ α₂) (eβ : Equiv.{u3, u4} β₁ β₂) (eγ : Equiv.{u5, u6} γ₁ γ₂), (forall {x : α₁} {y : β₁} {z : γ₁}, Iff (p x y z) (q (coeFn.{max 1 (imax u1 u2) (imax u2 u1), imax u1 u2} (Equiv.{u1, u2} α₁ α₂) (fun (_x : Equiv.{u1, u2} α₁ α₂) => α₁ -> α₂) (Equiv.hasCoeToFun.{u1, u2} α₁ α₂) eα x) (coeFn.{max 1 (imax u3 u4) (imax u4 u3), imax u3 u4} (Equiv.{u3, u4} β₁ β₂) (fun (_x : Equiv.{u3, u4} β₁ β₂) => β₁ -> β₂) (Equiv.hasCoeToFun.{u3, u4} β₁ β₂) eβ y) (coeFn.{max 1 (imax u5 u6) (imax u6 u5), imax u5 u6} (Equiv.{u5, u6} γ₁ γ₂) (fun (_x : Equiv.{u5, u6} γ₁ γ₂) => γ₁ -> γ₂) (Equiv.hasCoeToFun.{u5, u6} γ₁ γ₂) eγ z))) -> (Iff (forall (x : α₁) (y : β₁) (z : γ₁), p x y z) (forall (x : α₂) (y : β₂) (z : γ₂), q x y z))
but is expected to have type
  forall {α₁ : Sort.{u6}} {α₂ : Sort.{u5}} {β₁ : Sort.{u4}} {β₂ : Sort.{u3}} {γ₁ : Sort.{u2}} {γ₂ : Sort.{u1}} {p : α₁ -> α₂ -> β₁ -> Prop} {q : β₂ -> γ₁ -> γ₂ -> Prop} (eα : Equiv.{u6, u3} α₁ β₂) (eβ : Equiv.{u5, u2} α₂ γ₁) (eγ : Equiv.{u4, u1} β₁ γ₂), (forall {x : α₁} {y : α₂} {z : β₁}, Iff (p x y z) (q (FunLike.coe.{max (max 1 u6) u3, u6, u3} (Equiv.{u6, u3} α₁ β₂) α₁ (fun (_x : α₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α₁) => β₂) _x) (EmbeddingLike.toFunLike.{max (max 1 u6) u3, u6, u3} (Equiv.{u6, u3} α₁ β₂) α₁ β₂ (EquivLike.toEmbeddingLike.{max (max 1 u6) u3, u6, u3} (Equiv.{u6, u3} α₁ β₂) α₁ β₂ (Equiv.instEquivLikeEquiv.{u6, u3} α₁ β₂))) eα x) (FunLike.coe.{max (max 1 u5) u2, u5, u2} (Equiv.{u5, u2} α₂ γ₁) α₂ (fun (_x : α₂) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α₂) => γ₁) _x) (EmbeddingLike.toFunLike.{max (max 1 u5) u2, u5, u2} (Equiv.{u5, u2} α₂ γ₁) α₂ γ₁ (EquivLike.toEmbeddingLike.{max (max 1 u5) u2, u5, u2} (Equiv.{u5, u2} α₂ γ₁) α₂ γ₁ (Equiv.instEquivLikeEquiv.{u5, u2} α₂ γ₁))) eβ y) (FunLike.coe.{max (max 1 u4) u1, u4, u1} (Equiv.{u4, u1} β₁ γ₂) β₁ (fun (_x : β₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β₁) => γ₂) _x) (EmbeddingLike.toFunLike.{max (max 1 u4) u1, u4, u1} (Equiv.{u4, u1} β₁ γ₂) β₁ γ₂ (EquivLike.toEmbeddingLike.{max (max 1 u4) u1, u4, u1} (Equiv.{u4, u1} β₁ γ₂) β₁ γ₂ (Equiv.instEquivLikeEquiv.{u4, u1} β₁ γ₂))) eγ z))) -> (Iff (forall (x : α₁) (y : α₂) (z : β₁), p x y z) (forall (x : β₂) (y : γ₁) (z : γ₂), q x y z))
Case conversion may be inaccurate. Consider using '#align equiv.forall₃_congr Equiv.forall₃_congrₓ'. -/
protected theorem forall₃_congr {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop} (eα : α₁ ≃ α₂)
    (eβ : β₁ ≃ β₂) (eγ : γ₁ ≃ γ₂) (h : ∀ {x y z}, p x y z ↔ q (eα x) (eβ y) (eγ z)) :
    (∀ x y z, p x y z) ↔ ∀ x y z, q x y z :=
  by
  apply Equiv.forall₂_congr
  intros
  apply Equiv.forall_congr
  intros
  apply h
#align equiv.forall₃_congr Equiv.forall₃_congr

/- warning: equiv.forall₃_congr' -> Equiv.forall₃_congr' is a dubious translation:
lean 3 declaration is
  forall {α₁ : Sort.{u1}} {α₂ : Sort.{u2}} {β₁ : Sort.{u3}} {β₂ : Sort.{u4}} {γ₁ : Sort.{u5}} {γ₂ : Sort.{u6}} {p : α₁ -> β₁ -> γ₁ -> Prop} {q : α₂ -> β₂ -> γ₂ -> Prop} (eα : Equiv.{u1, u2} α₁ α₂) (eβ : Equiv.{u3, u4} β₁ β₂) (eγ : Equiv.{u5, u6} γ₁ γ₂), (forall {x : α₂} {y : β₂} {z : γ₂}, Iff (p (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} α₂ α₁) (fun (_x : Equiv.{u2, u1} α₂ α₁) => α₂ -> α₁) (Equiv.hasCoeToFun.{u2, u1} α₂ α₁) (Equiv.symm.{u1, u2} α₁ α₂ eα) x) (coeFn.{max 1 (imax u4 u3) (imax u3 u4), imax u4 u3} (Equiv.{u4, u3} β₂ β₁) (fun (_x : Equiv.{u4, u3} β₂ β₁) => β₂ -> β₁) (Equiv.hasCoeToFun.{u4, u3} β₂ β₁) (Equiv.symm.{u3, u4} β₁ β₂ eβ) y) (coeFn.{max 1 (imax u6 u5) (imax u5 u6), imax u6 u5} (Equiv.{u6, u5} γ₂ γ₁) (fun (_x : Equiv.{u6, u5} γ₂ γ₁) => γ₂ -> γ₁) (Equiv.hasCoeToFun.{u6, u5} γ₂ γ₁) (Equiv.symm.{u5, u6} γ₁ γ₂ eγ) z)) (q x y z)) -> (Iff (forall (x : α₁) (y : β₁) (z : γ₁), p x y z) (forall (x : α₂) (y : β₂) (z : γ₂), q x y z))
but is expected to have type
  forall {α₁ : Sort.{u6}} {α₂ : Sort.{u5}} {β₁ : Sort.{u4}} {β₂ : Sort.{u3}} {γ₁ : Sort.{u2}} {γ₂ : Sort.{u1}} {p : α₁ -> α₂ -> β₁ -> Prop} {q : β₂ -> γ₁ -> γ₂ -> Prop} (eα : Equiv.{u6, u3} α₁ β₂) (eβ : Equiv.{u5, u2} α₂ γ₁) (eγ : Equiv.{u4, u1} β₁ γ₂), (forall {x : β₂} {y : γ₁} {z : γ₂}, Iff (p (FunLike.coe.{max (max 1 u6) u3, u3, u6} (Equiv.{u3, u6} β₂ α₁) β₂ (fun (_x : β₂) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β₂) => α₁) _x) (EmbeddingLike.toFunLike.{max (max 1 u6) u3, u3, u6} (Equiv.{u3, u6} β₂ α₁) β₂ α₁ (EquivLike.toEmbeddingLike.{max (max 1 u6) u3, u3, u6} (Equiv.{u3, u6} β₂ α₁) β₂ α₁ (Equiv.instEquivLikeEquiv.{u3, u6} β₂ α₁))) (Equiv.symm.{u6, u3} α₁ β₂ eα) x) (FunLike.coe.{max (max 1 u5) u2, u2, u5} (Equiv.{u2, u5} γ₁ α₂) γ₁ (fun (_x : γ₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : γ₁) => α₂) _x) (EmbeddingLike.toFunLike.{max (max 1 u5) u2, u2, u5} (Equiv.{u2, u5} γ₁ α₂) γ₁ α₂ (EquivLike.toEmbeddingLike.{max (max 1 u5) u2, u2, u5} (Equiv.{u2, u5} γ₁ α₂) γ₁ α₂ (Equiv.instEquivLikeEquiv.{u2, u5} γ₁ α₂))) (Equiv.symm.{u5, u2} α₂ γ₁ eβ) y) (FunLike.coe.{max (max 1 u4) u1, u1, u4} (Equiv.{u1, u4} γ₂ β₁) γ₂ (fun (_x : γ₂) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : γ₂) => β₁) _x) (EmbeddingLike.toFunLike.{max (max 1 u4) u1, u1, u4} (Equiv.{u1, u4} γ₂ β₁) γ₂ β₁ (EquivLike.toEmbeddingLike.{max (max 1 u4) u1, u1, u4} (Equiv.{u1, u4} γ₂ β₁) γ₂ β₁ (Equiv.instEquivLikeEquiv.{u1, u4} γ₂ β₁))) (Equiv.symm.{u4, u1} β₁ γ₂ eγ) z)) (q x y z)) -> (Iff (forall (x : α₁) (y : α₂) (z : β₁), p x y z) (forall (x : β₂) (y : γ₁) (z : γ₂), q x y z))
Case conversion may be inaccurate. Consider using '#align equiv.forall₃_congr' Equiv.forall₃_congr'ₓ'. -/
protected theorem forall₃_congr' {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop} (eα : α₁ ≃ α₂)
    (eβ : β₁ ≃ β₂) (eγ : γ₁ ≃ γ₂) (h : ∀ {x y z}, p (eα.symm x) (eβ.symm y) (eγ.symm z) ↔ q x y z) :
    (∀ x y z, p x y z) ↔ ∀ x y z, q x y z :=
  (Equiv.forall₃_congr eα.symm eβ.symm eγ.symm fun x y z => h.symm).symm
#align equiv.forall₃_congr' Equiv.forall₃_congr'

#print Equiv.forall_congr_left' /-
protected theorem forall_congr_left' {p : α → Prop} (f : α ≃ β) : (∀ x, p x) ↔ ∀ y, p (f.symm y) :=
  Equiv.forall_congr f fun x => by simp
#align equiv.forall_congr_left' Equiv.forall_congr_left'
-/

#print Equiv.forall_congr_left /-
protected theorem forall_congr_left {p : β → Prop} (f : α ≃ β) : (∀ x, p (f x)) ↔ ∀ y, p y :=
  (Equiv.forall_congr_left' f.symm).symm
#align equiv.forall_congr_left Equiv.forall_congr_left
-/

/- warning: equiv.exists_congr_left -> Equiv.exists_congr_left is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} (f : Equiv.{u1, u2} α β) {p : α -> Prop}, Iff (Exists.{u1} α (fun (a : α) => p a)) (Exists.{u2} β (fun (b : β) => p (coeFn.{max 1 (imax u2 u1) (imax u1 u2), imax u2 u1} (Equiv.{u2, u1} β α) (fun (_x : Equiv.{u2, u1} β α) => β -> α) (Equiv.hasCoeToFun.{u2, u1} β α) (Equiv.symm.{u1, u2} α β f) b)))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} (f : Equiv.{u2, u1} α β) {p : α -> Prop}, Iff (Exists.{u2} α (fun (a : α) => p a)) (Exists.{u1} β (fun (b : β) => p (FunLike.coe.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} β α) β α (EquivLike.toEmbeddingLike.{max (max 1 u1) u2, u1, u2} (Equiv.{u1, u2} β α) β α (Equiv.instEquivLikeEquiv.{u1, u2} β α))) (Equiv.symm.{u2, u1} α β f) b)))
Case conversion may be inaccurate. Consider using '#align equiv.exists_congr_left Equiv.exists_congr_leftₓ'. -/
protected theorem exists_congr_left {α β} (f : α ≃ β) {p : α → Prop} :
    (∃ a, p a) ↔ ∃ b, p (f.symm b) :=
  ⟨fun ⟨a, h⟩ => ⟨f a, by simpa using h⟩, fun ⟨b, h⟩ => ⟨_, h⟩⟩
#align equiv.exists_congr_left Equiv.exists_congr_left

end Equiv

namespace Quot

#print Quot.congr /-
/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂). -/
protected def congr {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β)
    (eq : ∀ a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) : Quot ra ≃ Quot rb
    where
  toFun := Quot.map e fun a₁ a₂ => (Eq a₁ a₂).1
  invFun :=
    Quot.map e.symm fun b₁ b₂ h =>
      (Eq (e.symm b₁) (e.symm b₂)).2
        ((e.apply_symm_apply b₁).symm ▸ (e.apply_symm_apply b₂).symm ▸ h)
  left_inv := by
    rintro ⟨a⟩
    dsimp only [Quot.map]
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨a⟩
    dsimp only [Quot.map]
    simp only [Equiv.apply_symm_apply]
#align quot.congr Quot.congr
-/

#print Quot.congr_mk /-
@[simp]
theorem congr_mk {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β)
    (eq : ∀ a₁ a₂ : α, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) (a : α) :
    Quot.congr e Eq (Quot.mk ra a) = Quot.mk rb (e a) :=
  rfl
#align quot.congr_mk Quot.congr_mk
-/

#print Quot.congrRight /-
/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congrRight {r r' : α → α → Prop} (eq : ∀ a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂) :
    Quot r ≃ Quot r' :=
  Quot.congr (Equiv.refl α) Eq
#align quot.congr_right Quot.congrRight
-/

#print Quot.congrLeft /-
/-- An equivalence `e : α ≃ β` generates an equivalence between the quotient space of `α`
by a relation `ra` and the quotient space of `β` by the image of this relation under `e`. -/
protected def congrLeft {r : α → α → Prop} (e : α ≃ β) :
    Quot r ≃ Quot fun b b' => r (e.symm b) (e.symm b') :=
  @Quot.congr α β r (fun b b' => r (e.symm b) (e.symm b')) e fun a₁ a₂ => by
    simp only [e.symm_apply_apply]
#align quot.congr_left Quot.congrLeft
-/

end Quot

namespace Quotient

#print Quotient.congr /-
/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂). -/
protected def congr {ra : Setoid α} {rb : Setoid β} (e : α ≃ β)
    (eq : ∀ a₁ a₂, @Setoid.r α ra a₁ a₂ ↔ @Setoid.r β rb (e a₁) (e a₂)) :
    Quotient ra ≃ Quotient rb :=
  Quot.congr e Eq
#align quotient.congr Quotient.congr
-/

@[simp]
theorem congr_mk'' {ra : Setoid α} {rb : Setoid β} (e : α ≃ β)
    (eq : ∀ a₁ a₂ : α, Setoid.r a₁ a₂ ↔ Setoid.r (e a₁) (e a₂)) (a : α) :
    Quotient.congr e Eq (Quotient.mk'' a) = Quotient.mk'' (e a) :=
  rfl
#align quotient.congr_mk Quotient.congr_mk''

#print Quotient.congrRight /-
/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congrRight {r r' : Setoid α}
    (eq : ∀ a₁ a₂, @Setoid.r α r a₁ a₂ ↔ @Setoid.r α r' a₁ a₂) : Quotient r ≃ Quotient r' :=
  Quot.congrRight Eq
#align quotient.congr_right Quotient.congrRight
-/

end Quotient

