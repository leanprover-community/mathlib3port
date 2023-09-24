/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Order.Hom.Basic
import Logic.Equiv.Set
import Data.Set.Image

#align_import order.hom.set from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

/-!
# Order homomorphisms and sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open OrderDual

variable {F α β γ δ : Type _}

namespace OrderIso

section LE

variable [LE α] [LE β] [LE γ]

#print OrderIso.range_eq /-
theorem range_eq (e : α ≃o β) : Set.range e = Set.univ :=
  e.Surjective.range_eq
#align order_iso.range_eq OrderIso.range_eq
-/

#print OrderIso.symm_image_image /-
@[simp]
theorem symm_image_image (e : α ≃o β) (s : Set α) : e.symm '' (e '' s) = s :=
  e.toEquiv.symm_image_image s
#align order_iso.symm_image_image OrderIso.symm_image_image
-/

#print OrderIso.image_symm_image /-
@[simp]
theorem image_symm_image (e : α ≃o β) (s : Set β) : e '' (e.symm '' s) = s :=
  e.toEquiv.image_symm_image s
#align order_iso.image_symm_image OrderIso.image_symm_image
-/

#print OrderIso.image_eq_preimage /-
theorem image_eq_preimage (e : α ≃o β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage s
#align order_iso.image_eq_preimage OrderIso.image_eq_preimage
-/

#print OrderIso.preimage_symm_preimage /-
@[simp]
theorem preimage_symm_preimage (e : α ≃o β) (s : Set α) : e ⁻¹' (e.symm ⁻¹' s) = s :=
  e.toEquiv.preimage_symm_preimage s
#align order_iso.preimage_symm_preimage OrderIso.preimage_symm_preimage
-/

#print OrderIso.symm_preimage_preimage /-
@[simp]
theorem symm_preimage_preimage (e : α ≃o β) (s : Set β) : e.symm ⁻¹' (e ⁻¹' s) = s :=
  e.toEquiv.symm_preimage_preimage s
#align order_iso.symm_preimage_preimage OrderIso.symm_preimage_preimage
-/

#print OrderIso.image_preimage /-
@[simp]
theorem image_preimage (e : α ≃o β) (s : Set β) : e '' (e ⁻¹' s) = s :=
  e.toEquiv.image_preimage s
#align order_iso.image_preimage OrderIso.image_preimage
-/

#print OrderIso.preimage_image /-
@[simp]
theorem preimage_image (e : α ≃o β) (s : Set α) : e ⁻¹' (e '' s) = s :=
  e.toEquiv.preimage_image s
#align order_iso.preimage_image OrderIso.preimage_image
-/

end LE

open Set

variable [Preorder α] [Preorder β] [Preorder γ]

#print OrderIso.setCongr /-
/-- Order isomorphism between two equal sets. -/
def setCongr (s t : Set α) (h : s = t) : s ≃o t
    where
  toEquiv := Equiv.setCongr h
  map_rel_iff' x y := Iff.rfl
#align order_iso.set_congr OrderIso.setCongr
-/

#print OrderIso.Set.univ /-
/-- Order isomorphism between `univ : set α` and `α`. -/
def Set.univ : (Set.univ : Set α) ≃o α
    where
  toEquiv := Equiv.Set.univ α
  map_rel_iff' x y := Iff.rfl
#align order_iso.set.univ OrderIso.Set.univ
-/

end OrderIso

#print StrictMonoOn.orderIso /-
/-- If a function `f` is strictly monotone on a set `s`, then it defines an order isomorphism
between `s` and its image. -/
protected noncomputable def StrictMonoOn.orderIso {α β} [LinearOrder α] [Preorder β] (f : α → β)
    (s : Set α) (hf : StrictMonoOn f s) : s ≃o f '' s
    where
  toEquiv := hf.InjOn.bijOn_image.Equiv _
  map_rel_iff' x y := hf.le_iff_le x.2 y.2
#align strict_mono_on.order_iso StrictMonoOn.orderIso
-/

namespace StrictMono

variable {α β} [LinearOrder α] [Preorder β]

variable (f : α → β) (h_mono : StrictMono f) (h_surj : Function.Surjective f)

#print StrictMono.orderIso /-
/-- A strictly monotone function from a linear order is an order isomorphism between its domain and
its range. -/
@[simps apply]
protected noncomputable def orderIso : α ≃o Set.range f
    where
  toEquiv := Equiv.ofInjective f h_mono.Injective
  map_rel_iff' a b := h_mono.le_iff_le
#align strict_mono.order_iso StrictMono.orderIso
-/

#print StrictMono.orderIsoOfSurjective /-
/-- A strictly monotone surjective function from a linear order is an order isomorphism. -/
noncomputable def orderIsoOfSurjective : α ≃o β :=
  (h_mono.OrderIso f).trans <| (OrderIso.setCongr _ _ h_surj.range_eq).trans OrderIso.Set.univ
#align strict_mono.order_iso_of_surjective StrictMono.orderIsoOfSurjective
-/

#print StrictMono.coe_orderIsoOfSurjective /-
@[simp]
theorem coe_orderIsoOfSurjective : (orderIsoOfSurjective f h_mono h_surj : α → β) = f :=
  rfl
#align strict_mono.coe_order_iso_of_surjective StrictMono.coe_orderIsoOfSurjective
-/

#print StrictMono.orderIsoOfSurjective_symm_apply_self /-
@[simp]
theorem orderIsoOfSurjective_symm_apply_self (a : α) :
    (orderIsoOfSurjective f h_mono h_surj).symm (f a) = a :=
  (orderIsoOfSurjective f h_mono h_surj).symm_apply_apply _
#align strict_mono.order_iso_of_surjective_symm_apply_self StrictMono.orderIsoOfSurjective_symm_apply_self
-/

#print StrictMono.orderIsoOfSurjective_self_symm_apply /-
theorem orderIsoOfSurjective_self_symm_apply (b : β) :
    f ((orderIsoOfSurjective f h_mono h_surj).symm b) = b :=
  (orderIsoOfSurjective f h_mono h_surj).apply_symm_apply _
#align strict_mono.order_iso_of_surjective_self_symm_apply StrictMono.orderIsoOfSurjective_self_symm_apply
-/

end StrictMono

section BooleanAlgebra

variable (α) [BooleanAlgebra α]

#print OrderIso.compl /-
/-- Taking complements as an order isomorphism to the order dual. -/
@[simps]
def OrderIso.compl : α ≃o αᵒᵈ where
  toFun := OrderDual.toDual ∘ compl
  invFun := compl ∘ OrderDual.ofDual
  left_inv := compl_compl
  right_inv := compl_compl
  map_rel_iff' x y := compl_le_compl_iff_le
#align order_iso.compl OrderIso.compl
-/

#print compl_strictAnti /-
theorem compl_strictAnti : StrictAnti (compl : α → α) :=
  (OrderIso.compl α).StrictMono
#align compl_strict_anti compl_strictAnti
-/

#print compl_antitone /-
theorem compl_antitone : Antitone (compl : α → α) :=
  (OrderIso.compl α).Monotone
#align compl_antitone compl_antitone
-/

end BooleanAlgebra

