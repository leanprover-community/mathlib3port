/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module logic.small.basic
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Equiv.Set

/-!
# Small types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A type is `w`-small if there exists an equivalence to some `S : Type w`.

We provide a noncomputable model `shrink α : Type w`, and `equiv_shrink α : α ≃ shrink α`.

A subsingleton type is `w`-small for any `w`.

If `α ≃ β`, then `small.{w} α ↔ small.{w} β`.
-/


universe u w v

#print Small /-
/-- A type is `small.{w}` if there exists an equivalence to some `S : Type w`.
-/
class Small (α : Type v) : Prop where
  equiv_small : ∃ S : Type w, Nonempty (α ≃ S)
#align small Small
-/

#print Small.mk' /-
/-- Constructor for `small α` from an explicit witness type and equivalence.
-/
theorem Small.mk' {α : Type v} {S : Type w} (e : α ≃ S) : Small.{w} α :=
  ⟨⟨S, ⟨e⟩⟩⟩
#align small.mk' Small.mk'
-/

#print Shrink /-
/-- An arbitrarily chosen model in `Type w` for a `w`-small type.
-/
@[nolint has_nonempty_instance]
def Shrink (α : Type v) [Small.{w} α] : Type w :=
  Classical.choose (@Small.equiv_small α _)
#align shrink Shrink
-/

#print equivShrink /-
/-- The noncomputable equivalence between a `w`-small type and a model.
-/
noncomputable def equivShrink (α : Type v) [Small.{w} α] : α ≃ Shrink α :=
  Nonempty.some (Classical.choose_spec (@Small.equiv_small α _))
#align equiv_shrink equivShrink
-/

#print small_self /-
instance (priority := 100) small_self (α : Type v) : Small.{v} α :=
  Small.mk' <| Equiv.refl α
#align small_self small_self
-/

/- warning: small_map -> small_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u2}} {β : Type.{u3}} [hβ : Small.{u1, u3} β], (Equiv.{succ u2, succ u3} α β) -> (Small.{u1, u2} α)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [hβ : Small.{u3, u1} β], (Equiv.{succ u2, succ u1} α β) -> (Small.{u3, u2} α)
Case conversion may be inaccurate. Consider using '#align small_map small_mapₓ'. -/
theorem small_map {α : Type _} {β : Type _} [hβ : Small.{w} β] (e : α ≃ β) : Small.{w} α :=
  let ⟨γ, ⟨f⟩⟩ := hβ.equiv_small
  Small.mk' (e.trans f)
#align small_map small_map

#print small_lift /-
theorem small_lift (α : Type u) [hα : Small.{v} α] : Small.{max v w} α :=
  let ⟨⟨γ, ⟨f⟩⟩⟩ := hα
  Small.mk' <| f.trans Equiv.ulift.symm
#align small_lift small_lift
-/

#print small_max /-
instance (priority := 100) small_max (α : Type v) : Small.{max w v} α :=
  small_lift.{v, w} α
#align small_max small_max
-/

#print small_ulift /-
instance small_ulift (α : Type u) [Small.{v} α] : Small.{v} (ULift.{w} α) :=
  small_map Equiv.ulift
#align small_ulift small_ulift
-/

#print small_type /-
theorem small_type : Small.{max (u + 1) v} (Type u) :=
  small_max.{max (u + 1) v} _
#align small_type small_type
-/

section

open Classical

/- warning: small_congr -> small_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u2}} {β : Type.{u3}}, (Equiv.{succ u2, succ u3} α β) -> (Iff (Small.{u1, u2} α) (Small.{u1, u3} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, (Equiv.{succ u2, succ u1} α β) -> (Iff (Small.{u3, u2} α) (Small.{u3, u1} β))
Case conversion may be inaccurate. Consider using '#align small_congr small_congrₓ'. -/
theorem small_congr {α : Type _} {β : Type _} (e : α ≃ β) : Small.{w} α ↔ Small.{w} β :=
  ⟨fun h => @small_map _ _ h e.symm, fun h => @small_map _ _ h e⟩
#align small_congr small_congr

#print small_subtype /-
instance small_subtype (α : Type v) [Small.{w} α] (P : α → Prop) : Small.{w} { x // P x } :=
  small_map (equivShrink α).subtypeEquivOfSubtype'
#align small_subtype small_subtype
-/

#print small_of_injective /-
theorem small_of_injective {α : Type v} {β : Type w} [Small.{u} β] {f : α → β}
    (hf : Function.Injective f) : Small.{u} α :=
  small_map (Equiv.ofInjective f hf)
#align small_of_injective small_of_injective
-/

#print small_of_surjective /-
theorem small_of_surjective {α : Type v} {β : Type w} [Small.{u} α] {f : α → β}
    (hf : Function.Surjective f) : Small.{u} β :=
  small_of_injective (Function.injective_surjInv hf)
#align small_of_surjective small_of_surjective
-/

#print small_subset /-
theorem small_subset {α : Type v} {s t : Set α} (hts : t ⊆ s) [Small.{u} s] : Small.{u} t :=
  let f : t → s := fun x => ⟨x, hts x.Prop⟩
  @small_of_injective _ _ _ f fun x y hxy => Subtype.ext (Subtype.mk.inj hxy)
#align small_subset small_subset
-/

#print small_subsingleton /-
instance (priority := 100) small_subsingleton (α : Type v) [Subsingleton α] : Small.{w} α :=
  by
  rcases isEmpty_or_nonempty α with ⟨⟩ <;> skip
  · apply small_map (Equiv.equivPEmpty α)
  · apply small_map Equiv.punitOfNonemptyOfSubsingleton
    assumption'
#align small_subsingleton small_subsingleton
-/

/-!
We don't define `small_of_fintype` or `small_of_countable` in this file,
to keep imports to `logic` to a minimum.
-/


#print small_Pi /-
instance small_Pi {α} (β : α → Type _) [Small.{w} α] [∀ a, Small.{w} (β a)] :
    Small.{w} (∀ a, β a) :=
  ⟨⟨∀ a' : Shrink α, Shrink (β ((equivShrink α).symm a')),
      ⟨Equiv.piCongr (equivShrink α) fun a => by simpa using equivShrink (β a)⟩⟩⟩
#align small_Pi small_Pi
-/

#print small_sigma /-
instance small_sigma {α} (β : α → Type _) [Small.{w} α] [∀ a, Small.{w} (β a)] :
    Small.{w} (Σa, β a) :=
  ⟨⟨Σa' : Shrink α, Shrink (β ((equivShrink α).symm a')),
      ⟨Equiv.sigmaCongr (equivShrink α) fun a => by simpa using equivShrink (β a)⟩⟩⟩
#align small_sigma small_sigma
-/

#print small_prod /-
instance small_prod {α β} [Small.{w} α] [Small.{w} β] : Small.{w} (α × β) :=
  ⟨⟨Shrink α × Shrink β, ⟨Equiv.prodCongr (equivShrink α) (equivShrink β)⟩⟩⟩
#align small_prod small_prod
-/

#print small_sum /-
instance small_sum {α β} [Small.{w} α] [Small.{w} β] : Small.{w} (Sum α β) :=
  ⟨⟨Sum (Shrink α) (Shrink β), ⟨Equiv.sumCongr (equivShrink α) (equivShrink β)⟩⟩⟩
#align small_sum small_sum
-/

#print small_set /-
instance small_set {α} [Small.{w} α] : Small.{w} (Set α) :=
  ⟨⟨Set (Shrink α), ⟨Equiv.Set.congr (equivShrink α)⟩⟩⟩
#align small_set small_set
-/

#print small_range /-
instance small_range {α : Type v} {β : Type w} (f : α → β) [Small.{u} α] :
    Small.{u} (Set.range f) :=
  small_of_surjective Set.surjective_onto_range
#align small_range small_range
-/

#print small_image /-
instance small_image {α : Type v} {β : Type w} (f : α → β) (S : Set α) [Small.{u} S] :
    Small.{u} (f '' S) :=
  small_of_surjective Set.surjective_onto_image
#align small_image small_image
-/

#print not_small_type /-
theorem not_small_type : ¬Small.{u} (Type max u v)
  | ⟨⟨S, ⟨e⟩⟩⟩ =>
    @Function.cantor_injective (Σα, e.symm α) (fun a => ⟨_, cast (e.3 _).symm a⟩) fun a b e =>
      (cast_inj _).1 <| eq_of_heq (Sigma.mk.inj e).2
#align not_small_type not_small_type
-/

end

