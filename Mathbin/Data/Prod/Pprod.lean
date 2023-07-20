/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Logic.Basic

#align_import data.prod.pprod from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Extra facts about `pprod`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Function

variable {α β γ δ : Sort _}

namespace PProd

#print PProd.mk.eta /-
@[simp]
theorem mk.eta {p : PProd α β} : PProd.mk p.1 p.2 = p :=
  PProd.casesOn p fun a b => rfl
#align pprod.mk.eta PProd.mk.eta
-/

#print PProd.forall /-
@[simp]
theorem forall {p : PProd α β → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩
#align pprod.forall PProd.forall
-/

#print PProd.exists /-
@[simp]
theorem exists {p : PProd α β → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩
#align pprod.exists PProd.exists
-/

#print PProd.forall' /-
theorem forall' {p : α → β → Prop} : (∀ x : PProd α β, p x.1 x.2) ↔ ∀ a b, p a b :=
  PProd.forall
#align pprod.forall' PProd.forall'
-/

#print PProd.exists' /-
theorem exists' {p : α → β → Prop} : (∃ x : PProd α β, p x.1 x.2) ↔ ∃ a b, p a b :=
  PProd.exists
#align pprod.exists' PProd.exists'
-/

end PProd

#print Function.Injective.pprod_map /-
theorem Function.Injective.pprod_map {f : α → β} {g : γ → δ} (hf : Injective f) (hg : Injective g) :
    Injective (fun x => ⟨f x.1, g x.2⟩ : PProd α γ → PProd β δ) := fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h =>
  have A := congr_arg PProd.fst h
  have B := congr_arg PProd.snd h
  congr_arg₂ PProd.mk (hf A) (hg B)
#align function.injective.pprod_map Function.Injective.pprod_map
-/

