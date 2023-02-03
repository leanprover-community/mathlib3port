/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module logic.equiv.option
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Control.EquivFunctor
import Mathbin.Data.Option.Basic
import Mathbin.Data.Subtype
import Mathbin.Logic.Equiv.Defs

/-!
# Equivalences for `option α`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.


We define
* `equiv.option_congr`: the `option α ≃ option β` constructed from `e : α ≃ β` by sending `none` to
  `none`, and applying a `e` elsewhere.
* `equiv.remove_none`: the `α ≃ β` constructed from `option α ≃ option β` by removing `none` from
  both sides.
-/


namespace Equiv

open Option

variable {α β γ : Type _}

section OptionCongr

#print Equiv.optionCongr /-
/-- A universe-polymorphic version of `equiv_functor.map_equiv option e`. -/
@[simps apply]
def optionCongr (e : α ≃ β) : Option α ≃ Option β
    where
  toFun := Option.map e
  invFun := Option.map e.symm
  left_inv x := (Option.map_map _ _ _).trans <| e.symm_comp_self.symm ▸ congr_fun Option.map_id x
  right_inv x := (Option.map_map _ _ _).trans <| e.self_comp_symm.symm ▸ congr_fun Option.map_id x
#align equiv.option_congr Equiv.optionCongr
-/

#print Equiv.optionCongr_refl /-
@[simp]
theorem optionCongr_refl : optionCongr (Equiv.refl α) = Equiv.refl _ :=
  ext <| congr_fun Option.map_id
#align equiv.option_congr_refl Equiv.optionCongr_refl
-/

/- warning: equiv.option_congr_symm -> Equiv.optionCongr_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.{succ u1, succ u2} α β), Eq.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2)} (Equiv.{succ u2, succ u1} (Option.{u2} β) (Option.{u1} α)) (Equiv.symm.{succ u1, succ u2} (Option.{u1} α) (Option.{u2} β) (Equiv.optionCongr.{u1, u2} α β e)) (Equiv.optionCongr.{u2, u1} β α (Equiv.symm.{succ u1, succ u2} α β e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : Equiv.{succ u2, succ u1} α β), Eq.{max (succ u2) (succ u1)} (Equiv.{succ u1, succ u2} (Option.{u1} β) (Option.{u2} α)) (Equiv.symm.{succ u2, succ u1} (Option.{u2} α) (Option.{u1} β) (Equiv.optionCongr.{u2, u1} α β e)) (Equiv.optionCongr.{u1, u2} β α (Equiv.symm.{succ u2, succ u1} α β e))
Case conversion may be inaccurate. Consider using '#align equiv.option_congr_symm Equiv.optionCongr_symmₓ'. -/
@[simp]
theorem optionCongr_symm (e : α ≃ β) : (optionCongr e).symm = optionCongr e.symm :=
  rfl
#align equiv.option_congr_symm Equiv.optionCongr_symm

/- warning: equiv.option_congr_trans -> Equiv.optionCongr_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (e₁ : Equiv.{succ u1, succ u2} α β) (e₂ : Equiv.{succ u2, succ u3} β γ), Eq.{max 1 (max (succ u1) (succ u3)) (succ u3) (succ u1)} (Equiv.{succ u1, succ u3} (Option.{u1} α) (Option.{u3} γ)) (Equiv.trans.{succ u1, succ u2, succ u3} (Option.{u1} α) (Option.{u2} β) (Option.{u3} γ) (Equiv.optionCongr.{u1, u2} α β e₁) (Equiv.optionCongr.{u2, u3} β γ e₂)) (Equiv.optionCongr.{u1, u3} α γ (Equiv.trans.{succ u1, succ u2, succ u3} α β γ e₁ e₂))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (e₁ : Equiv.{succ u3, succ u2} α β) (e₂ : Equiv.{succ u2, succ u1} β γ), Eq.{max (succ u3) (succ u1)} (Equiv.{succ u3, succ u1} (Option.{u3} α) (Option.{u1} γ)) (Equiv.trans.{succ u3, succ u2, succ u1} (Option.{u3} α) (Option.{u2} β) (Option.{u1} γ) (Equiv.optionCongr.{u3, u2} α β e₁) (Equiv.optionCongr.{u2, u1} β γ e₂)) (Equiv.optionCongr.{u3, u1} α γ (Equiv.trans.{succ u3, succ u2, succ u1} α β γ e₁ e₂))
Case conversion may be inaccurate. Consider using '#align equiv.option_congr_trans Equiv.optionCongr_transₓ'. -/
@[simp]
theorem optionCongr_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
    (optionCongr e₁).trans (optionCongr e₂) = optionCongr (e₁.trans e₂) :=
  ext <| Option.map_map _ _
#align equiv.option_congr_trans Equiv.optionCongr_trans

/- warning: equiv.option_congr_eq_equiv_function_map_equiv -> Equiv.optionCongr_eq_equivFunctor_mapEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (e : Equiv.{succ u1, succ u1} α β), Eq.{succ u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} β)) (Equiv.optionCongr.{u1, u1} α β e) (EquivFunctor.mapEquiv.{u1, u1} Option.{u1} (EquivFunctor.ofLawfulFunctor.{u1, u1} Option.{u1} (Applicative.toFunctor.{u1, u1} Option.{u1} (Monad.toApplicative.{u1, u1} Option.{u1} Option.monad.{u1})) (LawfulApplicative.to_lawfulFunctor.{u1, u1} Option.{u1} (Monad.toApplicative.{u1, u1} Option.{u1} Option.monad.{u1}) (LawfulMonad.to_lawfulApplicative.{u1, u1} Option.{u1} Option.monad.{u1} Option.lawfulMonad.{u1}))) α β e)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (e : Equiv.{succ u1, succ u1} α β), Eq.{succ u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} β)) (Equiv.optionCongr.{u1, u1} α β e) (EquivFunctor.mapEquiv.{u1, u1} Option.{u1} (EquivFunctor.ofLawfulFunctor.{u1, u1} Option.{u1} instFunctorOption.{u1} instLawfulFunctorOptionInstFunctorOption.{u1}) α β e)
Case conversion may be inaccurate. Consider using '#align equiv.option_congr_eq_equiv_function_map_equiv Equiv.optionCongr_eq_equivFunctor_mapEquivₓ'. -/
/-- When `α` and `β` are in the same universe, this is the same as the result of
`equiv_functor.map_equiv`. -/
theorem optionCongr_eq_equivFunctor_mapEquiv {α β : Type _} (e : α ≃ β) :
    optionCongr e = EquivFunctor.mapEquiv Option e :=
  rfl
#align equiv.option_congr_eq_equiv_function_map_equiv Equiv.optionCongr_eq_equivFunctor_mapEquiv

end OptionCongr

section RemoveNone

variable (e : Option α ≃ Option β)

private def remove_none_aux (x : α) : β :=
  if h : (e (some x)).isSome then Option.get h
  else
    Option.get <|
      show (e none).isSome by
        rw [← Option.ne_none_iff_isSome]
        intro hn
        rw [Option.not_isSome_iff_eq_none, ← hn] at h
        simpa only using e.injective h
#align equiv.remove_none_aux equiv.remove_none_aux

private theorem remove_none_aux_some {x : α} (h : ∃ x', e (some x) = some x') :
    some (removeNoneAux e x) = e (some x) := by
  simp [remove_none_aux, option.is_some_iff_exists.mpr h]
#align equiv.remove_none_aux_some equiv.remove_none_aux_some

private theorem remove_none_aux_none {x : α} (h : e (some x) = none) :
    some (removeNoneAux e x) = e none := by
  simp [remove_none_aux, option.not_is_some_iff_eq_none.mpr h]
#align equiv.remove_none_aux_none equiv.remove_none_aux_none

private theorem remove_none_aux_inv (x : α) : removeNoneAux e.symm (removeNoneAux e x) = x :=
  Option.some_injective _
    (by
      cases h1 : e.symm (some (remove_none_aux e x)) <;> cases h2 : e (some x)
      · rw [remove_none_aux_none _ h1]
        exact (e.eq_symm_apply.mpr h2).symm
      · rw [remove_none_aux_some _ ⟨_, h2⟩] at h1
        simpa using h1
      · rw [remove_none_aux_none _ h2] at h1
        simpa using h1
      · rw [remove_none_aux_some _ ⟨_, h1⟩]
        rw [remove_none_aux_some _ ⟨_, h2⟩]
        simp)
#align equiv.remove_none_aux_inv equiv.remove_none_aux_inv

#print Equiv.removeNone /-
/-- Given an equivalence between two `option` types, eliminate `none` from that equivalence by
mapping `e.symm none` to `e none`. -/
def removeNone : α ≃ β where
  toFun := removeNoneAux e
  invFun := removeNoneAux e.symm
  left_inv := removeNoneAux_inv e
  right_inv := removeNoneAux_inv e.symm
#align equiv.remove_none Equiv.removeNone
-/

/- warning: equiv.remove_none_symm -> Equiv.removeNone_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.{succ u1, succ u2} (Option.{u1} α) (Option.{u2} β)), Eq.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2)} (Equiv.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β (Equiv.removeNone.{u1, u2} α β e)) (Equiv.removeNone.{u2, u1} β α (Equiv.symm.{succ u1, succ u2} (Option.{u1} α) (Option.{u2} β) e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : Equiv.{succ u2, succ u1} (Option.{u2} α) (Option.{u1} β)), Eq.{max (succ u2) (succ u1)} (Equiv.{succ u1, succ u2} β α) (Equiv.symm.{succ u2, succ u1} α β (Equiv.removeNone.{u2, u1} α β e)) (Equiv.removeNone.{u1, u2} β α (Equiv.symm.{succ u2, succ u1} (Option.{u2} α) (Option.{u1} β) e))
Case conversion may be inaccurate. Consider using '#align equiv.remove_none_symm Equiv.removeNone_symmₓ'. -/
@[simp]
theorem removeNone_symm : (removeNone e).symm = removeNone e.symm :=
  rfl
#align equiv.remove_none_symm Equiv.removeNone_symm

#print Equiv.removeNone_some /-
theorem removeNone_some {x : α} (h : ∃ x', e (some x) = some x') :
    some (removeNone e x) = e (some x) :=
  removeNoneAux_some e h
#align equiv.remove_none_some Equiv.removeNone_some
-/

#print Equiv.removeNone_none /-
theorem removeNone_none {x : α} (h : e (some x) = none) : some (removeNone e x) = e none :=
  removeNoneAux_none e h
#align equiv.remove_none_none Equiv.removeNone_none
-/

/- warning: equiv.option_symm_apply_none_iff -> Equiv.option_symm_apply_none_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.{succ u1, succ u2} (Option.{u1} α) (Option.{u2} β)), Iff (Eq.{succ u1} (Option.{u1} α) (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} (Option.{u2} β) (Option.{u1} α)) (fun (_x : Equiv.{succ u2, succ u1} (Option.{u2} β) (Option.{u1} α)) => (Option.{u2} β) -> (Option.{u1} α)) (Equiv.hasCoeToFun.{succ u2, succ u1} (Option.{u2} β) (Option.{u1} α)) (Equiv.symm.{succ u1, succ u2} (Option.{u1} α) (Option.{u2} β) e) (Option.none.{u2} β)) (Option.none.{u1} α)) (Eq.{succ u2} (Option.{u2} β) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} (Option.{u1} α) (Option.{u2} β)) (fun (_x : Equiv.{succ u1, succ u2} (Option.{u1} α) (Option.{u2} β)) => (Option.{u1} α) -> (Option.{u2} β)) (Equiv.hasCoeToFun.{succ u1, succ u2} (Option.{u1} α) (Option.{u2} β)) e (Option.none.{u1} α)) (Option.none.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : Equiv.{succ u2, succ u1} (Option.{u2} α) (Option.{u1} β)), Iff (Eq.{succ u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Option.{u1} β) => Option.{u2} α) (Option.none.{u1} β)) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} (Option.{u1} β) (Option.{u2} α)) (Option.{u1} β) (fun (_x : Option.{u1} β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Option.{u1} β) => Option.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} (Option.{u1} β) (Option.{u2} α)) (Equiv.symm.{succ u2, succ u1} (Option.{u2} α) (Option.{u1} β) e) (Option.none.{u1} β)) (Option.none.{u2} α)) (Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Option.{u2} α) => Option.{u1} β) (Option.none.{u2} α)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} (Option.{u2} α) (Option.{u1} β)) (Option.{u2} α) (fun (_x : Option.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Option.{u2} α) => Option.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} (Option.{u2} α) (Option.{u1} β)) e (Option.none.{u2} α)) (Option.none.{u1} β))
Case conversion may be inaccurate. Consider using '#align equiv.option_symm_apply_none_iff Equiv.option_symm_apply_none_iffₓ'. -/
@[simp]
theorem option_symm_apply_none_iff : e.symm none = none ↔ e none = none :=
  ⟨fun h => by simpa using (congr_arg e h).symm, fun h => by simpa using (congr_arg e.symm h).symm⟩
#align equiv.option_symm_apply_none_iff Equiv.option_symm_apply_none_iff

#print Equiv.some_removeNone_iff /-
theorem some_removeNone_iff {x : α} : some (removeNone e x) = e none ↔ e.symm none = some x :=
  by
  cases' h : e (some x) with a
  · rw [remove_none_none _ h]
    simpa using (congr_arg e.symm h).symm
  · rw [remove_none_some _ ⟨a, h⟩]
    have := congr_arg e.symm h
    rw [symm_apply_apply] at this
    simp only [false_iff_iff, apply_eq_iff_eq]
    simp [this]
#align equiv.some_remove_none_iff Equiv.some_removeNone_iff
-/

/- warning: equiv.remove_none_option_congr -> Equiv.removeNone_optionCongr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.{succ u1, succ u2} α β), Eq.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{succ u1, succ u2} α β) (Equiv.removeNone.{u1, u2} α β (Equiv.optionCongr.{u1, u2} α β e)) e
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : Equiv.{succ u2, succ u1} α β), Eq.{max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} α β) (Equiv.removeNone.{u2, u1} α β (Equiv.optionCongr.{u2, u1} α β e)) e
Case conversion may be inaccurate. Consider using '#align equiv.remove_none_option_congr Equiv.removeNone_optionCongrₓ'. -/
@[simp]
theorem removeNone_optionCongr (e : α ≃ β) : removeNone e.optionCongr = e :=
  Equiv.ext fun x => Option.some_injective _ <| removeNone_some _ ⟨e x, by simp [EquivFunctor.map]⟩
#align equiv.remove_none_option_congr Equiv.removeNone_optionCongr

end RemoveNone

/- warning: equiv.option_congr_injective -> Equiv.optionCongr_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Function.Injective.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{succ u1, succ u2} α β) (Equiv.{succ u1, succ u2} (Option.{u1} α) (Option.{u2} β)) (Equiv.optionCongr.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} α β) (Equiv.{succ u2, succ u1} (Option.{u2} α) (Option.{u1} β)) (Equiv.optionCongr.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align equiv.option_congr_injective Equiv.optionCongr_injectiveₓ'. -/
theorem optionCongr_injective : Function.Injective (optionCongr : α ≃ β → Option α ≃ Option β) :=
  Function.LeftInverse.injective removeNone_optionCongr
#align equiv.option_congr_injective Equiv.optionCongr_injective

#print Equiv.optionSubtype /-
/-- Equivalences between `option α` and `β` that send `none` to `x` are equivalent to
equivalences between `α` and `{y : β // y ≠ x}`. -/
def optionSubtype [DecidableEq β] (x : β) :
    { e : Option α ≃ β // e none = x } ≃ (α ≃ { y : β // y ≠ x })
    where
  toFun e :=
    { toFun := fun a => ⟨e a, ((EquivLike.injective _).ne_iff' e.property).2 (some_ne_none _)⟩
      invFun := fun b =>
        get
          (ne_none_iff_isSome.1
            (((EquivLike.injective _).ne_iff' ((apply_eq_iff_eq_symm_apply _).1 e.property).symm).2
              b.property))
      left_inv := fun a => by
        rw [← some_inj, some_get, ← coe_def]
        exact symm_apply_apply (e : Option α ≃ β) a
      right_inv := fun b => by
        ext
        simp
        exact apply_symm_apply _ _ }
  invFun e :=
    ⟨{  toFun := fun a => casesOn' a x (coe ∘ e)
        invFun := fun b => if h : b = x then none else e.symm ⟨b, h⟩
        left_inv := fun a => by
          cases a; · simp
          simp only [cases_on'_some, Function.comp_apply, Subtype.coe_eta, symm_apply_apply,
            dite_eq_ite]
          exact if_neg (e a).property
        right_inv := fun b => by by_cases h : b = x <;> simp [h] }, rfl⟩
  left_inv e := by
    ext a
    cases a
    · simpa using e.property.symm
    · simpa
  right_inv e := by
    ext a
    rfl
#align equiv.option_subtype Equiv.optionSubtype
-/

#print Equiv.optionSubtype_apply_apply /-
@[simp]
theorem optionSubtype_apply_apply [DecidableEq β] (x : β) (e : { e : Option α ≃ β // e none = x })
    (a : α) (h) : optionSubtype x e a = ⟨(e : Option α ≃ β) a, h⟩ :=
  rfl
#align equiv.option_subtype_apply_apply Equiv.optionSubtype_apply_apply
-/

#print Equiv.coe_optionSubtype_apply_apply /-
@[simp]
theorem coe_optionSubtype_apply_apply [DecidableEq β] (x : β)
    (e : { e : Option α ≃ β // e none = x }) (a : α) :
    ↑(optionSubtype x e a) = (e : Option α ≃ β) a :=
  rfl
#align equiv.coe_option_subtype_apply_apply Equiv.coe_optionSubtype_apply_apply
-/

#print Equiv.optionSubtype_apply_symm_apply /-
@[simp]
theorem optionSubtype_apply_symm_apply [DecidableEq β] (x : β)
    (e : { e : Option α ≃ β // e none = x }) (b : { y : β // y ≠ x }) :
    ↑((optionSubtype x e).symm b) = (e : Option α ≃ β).symm b :=
  by
  dsimp only [option_subtype]
  simp
#align equiv.option_subtype_apply_symm_apply Equiv.optionSubtype_apply_symm_apply
-/

#print Equiv.optionSubtype_symm_apply_apply_coe /-
@[simp]
theorem optionSubtype_symm_apply_apply_coe [DecidableEq β] (x : β) (e : α ≃ { y : β // y ≠ x })
    (a : α) : (optionSubtype x).symm e a = e a :=
  rfl
#align equiv.option_subtype_symm_apply_apply_coe Equiv.optionSubtype_symm_apply_apply_coe
-/

#print Equiv.optionSubtype_symm_apply_apply_some /-
@[simp]
theorem optionSubtype_symm_apply_apply_some [DecidableEq β] (x : β) (e : α ≃ { y : β // y ≠ x })
    (a : α) : (optionSubtype x).symm e (some a) = e a :=
  rfl
#align equiv.option_subtype_symm_apply_apply_some Equiv.optionSubtype_symm_apply_apply_some
-/

#print Equiv.optionSubtype_symm_apply_apply_none /-
@[simp]
theorem optionSubtype_symm_apply_apply_none [DecidableEq β] (x : β) (e : α ≃ { y : β // y ≠ x }) :
    (optionSubtype x).symm e none = x :=
  rfl
#align equiv.option_subtype_symm_apply_apply_none Equiv.optionSubtype_symm_apply_apply_none
-/

#print Equiv.optionSubtype_symm_apply_symm_apply /-
@[simp]
theorem optionSubtype_symm_apply_symm_apply [DecidableEq β] (x : β) (e : α ≃ { y : β // y ≠ x })
    (b : { y : β // y ≠ x }) : ((optionSubtype x).symm e : Option α ≃ β).symm b = e.symm b :=
  by
  simp only [option_subtype, coe_fn_symm_mk, Subtype.coe_mk, Subtype.coe_eta, dite_eq_ite,
    ite_eq_right_iff]
  exact fun h => False.elim (b.property h)
#align equiv.option_subtype_symm_apply_symm_apply Equiv.optionSubtype_symm_apply_symm_apply
-/

end Equiv

