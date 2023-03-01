/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn

! This file was ported from Lean 3 source module set_theory.cardinal.basic
! leanprover-community/mathlib commit 34ee86e6a59d911a8e4f89b68793ee7577ae79c7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.BigOperators
import Mathbin.Data.Finsupp.Defs
import Mathbin.Data.Nat.PartEnat
import Mathbin.Data.Set.Countable
import Mathbin.Logic.Small.Basic
import Mathbin.Order.ConditionallyCompleteLattice.Basic
import Mathbin.Order.SuccPred.Basic
import Mathbin.SetTheory.Cardinal.SchroederBernstein
import Mathbin.Tactic.Positivity

/-!
# Cardinal Numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define cardinal numbers as a quotient of types under the equivalence relation of equinumerity.

## Main definitions

* `cardinal` the type of cardinal numbers (in a given universe).
* `cardinal.mk α` or `#α` is the cardinality of `α`. The notation `#` lives in the locale
  `cardinal`.
* Addition `c₁ + c₂` is defined by `cardinal.add_def α β : #α + #β = #(α ⊕ β)`.
* Multiplication `c₁ * c₂` is defined by `cardinal.mul_def : #α * #β = #(α × β)`.
* The order `c₁ ≤ c₂` is defined by `cardinal.le_def α β : #α ≤ #β ↔ nonempty (α ↪ β)`.
* Exponentiation `c₁ ^ c₂` is defined by `cardinal.power_def α β : #α ^ #β = #(β → α)`.
* `cardinal.aleph_0` or `ℵ₀` is the cardinality of `ℕ`. This definition is universe polymorphic:
  `cardinal.aleph_0.{u} : cardinal.{u}` (contrast with `ℕ : Type`, which lives in a specific
  universe). In some cases the universe level has to be given explicitly.
* `cardinal.sum` is the sum of an indexed family of cardinals, i.e. the cardinality of the
  corresponding sigma type.
* `cardinal.prod` is the product of an indexed family of cardinals, i.e. the cardinality of the
  corresponding pi type.
* `cardinal.powerlt a b` or `a ^< b` is defined as the supremum of `a ^ c` for `c < b`.

## Main instances

* Cardinals form a `canonically_ordered_comm_semiring` with the aforementioned sum and product.
* Cardinals form a `succ_order`. Use `order.succ c` for the smallest cardinal greater than `c`.
* The less than relation on cardinals forms a well-order.
* Cardinals form a `conditionally_complete_linear_order_bot`. Bounded sets for cardinals in universe
  `u` are precisely the sets indexed by some type in universe `u`, see
  `cardinal.bdd_above_iff_small`. One can use `Sup` for the cardinal supremum, and `Inf` for the
  minimum of a set of cardinals.

## Main Statements

* Cantor's theorem: `cardinal.cantor c : c < 2 ^ c`.
* König's theorem: `cardinal.sum_lt_prod`

## Implementation notes

* There is a type of cardinal numbers in every universe level:
  `cardinal.{u} : Type (u + 1)` is the quotient of types in `Type u`.
  The operation `cardinal.lift` lifts cardinal numbers to a higher level.
* Cardinal arithmetic specifically for infinite cardinals (like `κ * κ = κ`) is in the file
  `set_theory/cardinal_ordinal.lean`.
* There is an instance `has_pow cardinal`, but this will only fire if Lean already knows that both
  the base and the exponent live in the same universe. As a workaround, you can add
  ```
    local infixr (name := cardinal.pow) ^ := @has_pow.pow cardinal cardinal cardinal.has_pow
  ```
  to a file. This notation will work even if Lean doesn't know yet that the base and the exponent
  live in the same universe (but no exponents in other types can be used).

## References

* <https://en.wikipedia.org/wiki/Cardinal_number>

## Tags

cardinal number, cardinal arithmetic, cardinal exponentiation, aleph,
Cantor's theorem, König's theorem, Konig's theorem
-/


open Function Set Order

open BigOperators Classical

noncomputable section

universe u v w

variable {α β : Type u}

#print Cardinal.isEquivalent /-
/-- The equivalence relation on types given by equivalence (bijective correspondence) of types.
  Quotienting by this equivalence relation gives the cardinal numbers.
-/
instance Cardinal.isEquivalent : Setoid (Type u)
    where
  R α β := Nonempty (α ≃ β)
  iseqv := ⟨fun α => ⟨Equiv.refl α⟩, fun α β ⟨e⟩ => ⟨e.symm⟩, fun α β γ ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩
#align cardinal.is_equivalent Cardinal.isEquivalent
-/

#print Cardinal /-
/-- `cardinal.{u}` is the type of cardinal numbers in `Type u`,
  defined as the quotient of `Type u` by existence of an equivalence
  (a bijection with explicit inverse). -/
def Cardinal : Type (u + 1) :=
  Quotient Cardinal.isEquivalent
#align cardinal Cardinal
-/

namespace Cardinal

#print Cardinal.mk /-
/-- The cardinal number of a type -/
def mk : Type u → Cardinal :=
  Quotient.mk'
#align cardinal.mk Cardinal.mk
-/

-- mathport name: cardinal.mk
scoped prefix:0 "#" => Cardinal.mk

#print Cardinal.canLiftCardinalType /-
instance canLiftCardinalType : CanLift Cardinal.{u} (Type u) mk fun _ => True :=
  ⟨fun c _ => Quot.inductionOn c fun α => ⟨α, rfl⟩⟩
#align cardinal.can_lift_cardinal_Type Cardinal.canLiftCardinalType
-/

#print Cardinal.inductionOn /-
@[elab_as_elim]
theorem inductionOn {p : Cardinal → Prop} (c : Cardinal) (h : ∀ α, p (#α)) : p c :=
  Quotient.inductionOn c h
#align cardinal.induction_on Cardinal.inductionOn
-/

/- warning: cardinal.induction_on₂ -> Cardinal.inductionOn₂ is a dubious translation:
lean 3 declaration is
  forall {p : Cardinal.{u1} -> Cardinal.{u2} -> Prop} (c₁ : Cardinal.{u1}) (c₂ : Cardinal.{u2}), (forall (α : Type.{u1}) (β : Type.{u2}), p (Cardinal.mk.{u1} α) (Cardinal.mk.{u2} β)) -> (p c₁ c₂)
but is expected to have type
  forall {p : Cardinal.{u2} -> Cardinal.{u1} -> Prop} (c₁ : Cardinal.{u2}) (c₂ : Cardinal.{u1}), (forall (α : Type.{u2}) (β : Type.{u1}), p (Cardinal.mk.{u2} α) (Cardinal.mk.{u1} β)) -> (p c₁ c₂)
Case conversion may be inaccurate. Consider using '#align cardinal.induction_on₂ Cardinal.inductionOn₂ₓ'. -/
@[elab_as_elim]
theorem inductionOn₂ {p : Cardinal → Cardinal → Prop} (c₁ : Cardinal) (c₂ : Cardinal)
    (h : ∀ α β, p (#α) (#β)) : p c₁ c₂ :=
  Quotient.induction_on₂ c₁ c₂ h
#align cardinal.induction_on₂ Cardinal.inductionOn₂

/- warning: cardinal.induction_on₃ -> Cardinal.inductionOn₃ is a dubious translation:
lean 3 declaration is
  forall {p : Cardinal.{u1} -> Cardinal.{u2} -> Cardinal.{u3} -> Prop} (c₁ : Cardinal.{u1}) (c₂ : Cardinal.{u2}) (c₃ : Cardinal.{u3}), (forall (α : Type.{u1}) (β : Type.{u2}) (γ : Type.{u3}), p (Cardinal.mk.{u1} α) (Cardinal.mk.{u2} β) (Cardinal.mk.{u3} γ)) -> (p c₁ c₂ c₃)
but is expected to have type
  forall {p : Cardinal.{u3} -> Cardinal.{u2} -> Cardinal.{u1} -> Prop} (c₁ : Cardinal.{u3}) (c₂ : Cardinal.{u2}) (c₃ : Cardinal.{u1}), (forall (α : Type.{u3}) (β : Type.{u2}) (γ : Type.{u1}), p (Cardinal.mk.{u3} α) (Cardinal.mk.{u2} β) (Cardinal.mk.{u1} γ)) -> (p c₁ c₂ c₃)
Case conversion may be inaccurate. Consider using '#align cardinal.induction_on₃ Cardinal.inductionOn₃ₓ'. -/
@[elab_as_elim]
theorem inductionOn₃ {p : Cardinal → Cardinal → Cardinal → Prop} (c₁ : Cardinal) (c₂ : Cardinal)
    (c₃ : Cardinal) (h : ∀ α β γ, p (#α) (#β) (#γ)) : p c₁ c₂ c₃ :=
  Quotient.induction_on₃ c₁ c₂ c₃ h
#align cardinal.induction_on₃ Cardinal.inductionOn₃

#print Cardinal.eq /-
protected theorem eq : (#α) = (#β) ↔ Nonempty (α ≃ β) :=
  Quotient.eq'
#align cardinal.eq Cardinal.eq
-/

#print Cardinal.mk'_def /-
@[simp]
theorem mk'_def (α : Type u) : @Eq Cardinal ⟦α⟧ (#α) :=
  rfl
#align cardinal.mk_def Cardinal.mk'_def
-/

#print Cardinal.mk_out /-
@[simp]
theorem mk_out (c : Cardinal) : (#c.out) = c :=
  Quotient.out_eq _
#align cardinal.mk_out Cardinal.mk_out
-/

#print Cardinal.outMkEquiv /-
/-- The representative of the cardinal of a type is equivalent ot the original type. -/
def outMkEquiv {α : Type v} : (#α).out ≃ α :=
  Nonempty.some <| Cardinal.eq.mp (by simp)
#align cardinal.out_mk_equiv Cardinal.outMkEquiv
-/

#print Cardinal.mk_congr /-
theorem mk_congr (e : α ≃ β) : (#α) = (#β) :=
  Quot.sound ⟨e⟩
#align cardinal.mk_congr Cardinal.mk_congr
-/

alias mk_congr ← _root_.equiv.cardinal_eq
#align equiv.cardinal_eq Equiv.cardinal_eq

#print Cardinal.map /-
/-- Lift a function between `Type*`s to a function between `cardinal`s. -/
def map (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) : Cardinal.{u} → Cardinal.{v} :=
  Quotient.map f fun α β ⟨e⟩ => ⟨hf α β e⟩
#align cardinal.map Cardinal.map
-/

#print Cardinal.map_mk /-
@[simp]
theorem map_mk (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) (α : Type u) :
    map f hf (#α) = (#f α) :=
  rfl
#align cardinal.map_mk Cardinal.map_mk
-/

#print Cardinal.map₂ /-
/-- Lift a binary operation `Type* → Type* → Type*` to a binary operation on `cardinal`s. -/
def map₂ (f : Type u → Type v → Type w) (hf : ∀ α β γ δ, α ≃ β → γ ≃ δ → f α γ ≃ f β δ) :
    Cardinal.{u} → Cardinal.{v} → Cardinal.{w} :=
  Quotient.map₂ f fun α β ⟨e₁⟩ γ δ ⟨e₂⟩ => ⟨hf α β γ δ e₁ e₂⟩
#align cardinal.map₂ Cardinal.map₂
-/

#print Cardinal.lift /-
/-- The universe lift operation on cardinals. You can specify the universes explicitly with
  `lift.{u v} : cardinal.{v} → cardinal.{max v u}` -/
def lift (c : Cardinal.{v}) : Cardinal.{max v u} :=
  map ULift (fun α β e => Equiv.ulift.trans <| e.trans Equiv.ulift.symm) c
#align cardinal.lift Cardinal.lift
-/

#print Cardinal.mk_uLift /-
@[simp]
theorem mk_uLift (α) : (#ULift.{v, u} α) = lift.{v} (#α) :=
  rfl
#align cardinal.mk_ulift Cardinal.mk_uLift
-/

#print Cardinal.lift_umax /-
/-- `lift.{(max u v) u}` equals `lift.{v u}`. Using `set_option pp.universes true` will make it much
    easier to understand what's happening when using this lemma. -/
@[simp]
theorem lift_umax : lift.{max u v, u} = lift.{v, u} :=
  funext fun a => inductionOn a fun α => (Equiv.ulift.trans Equiv.ulift.symm).cardinal_eq
#align cardinal.lift_umax Cardinal.lift_umax
-/

#print Cardinal.lift_umax' /-
/-- `lift.{(max v u) u}` equals `lift.{v u}`. Using `set_option pp.universes true` will make it much
    easier to understand what's happening when using this lemma. -/
@[simp]
theorem lift_umax' : lift.{max v u, u} = lift.{v, u} :=
  lift_umax
#align cardinal.lift_umax' Cardinal.lift_umax'
-/

#print Cardinal.lift_id' /-
/-- A cardinal lifted to a lower or equal universe equals itself. -/
@[simp]
theorem lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a :=
  inductionOn a fun α => mk_congr Equiv.ulift
#align cardinal.lift_id' Cardinal.lift_id'
-/

#print Cardinal.lift_id /-
/-- A cardinal lifted to the same universe equals itself. -/
@[simp]
theorem lift_id (a : Cardinal) : lift.{u, u} a = a :=
  lift_id'.{u, u} a
#align cardinal.lift_id Cardinal.lift_id
-/

#print Cardinal.lift_uzero /-
/-- A cardinal lifted to the zero universe equals itself. -/
@[simp]
theorem lift_uzero (a : Cardinal.{u}) : lift.{0} a = a :=
  lift_id'.{0, u} a
#align cardinal.lift_uzero Cardinal.lift_uzero
-/

/- warning: cardinal.lift_lift -> Cardinal.lift_lift is a dubious translation:
lean 3 declaration is
  forall (a : Cardinal.{u3}), Eq.{succ (succ (max (max u3 u1) u2))} Cardinal.{max (max u3 u1) u2} (Cardinal.lift.{u2, max u3 u1} (Cardinal.lift.{u1, u3} a)) (Cardinal.lift.{max u1 u2, u3} a)
but is expected to have type
  forall (a : Cardinal.{u1}), Eq.{max (max (succ (succ u2)) (succ (succ u3))) (succ (succ u1))} Cardinal.{max (max u2 u1) u3} (Cardinal.lift.{u3, max u2 u1} (Cardinal.lift.{u2, u1} a)) (Cardinal.lift.{max u2 u3, u1} a)
Case conversion may be inaccurate. Consider using '#align cardinal.lift_lift Cardinal.lift_liftₓ'. -/
@[simp]
theorem lift_lift (a : Cardinal) : lift.{w} (lift.{v} a) = lift.{max v w} a :=
  inductionOn a fun α => (Equiv.ulift.trans <| Equiv.ulift.trans Equiv.ulift.symm).cardinal_eq
#align cardinal.lift_lift Cardinal.lift_lift

/-- We define the order on cardinal numbers by `#α ≤ #β` if and only if
  there exists an embedding (injective function) from α to β. -/
instance : LE Cardinal.{u} :=
  ⟨fun q₁ q₂ =>
    Quotient.liftOn₂ q₁ q₂ (fun α β => Nonempty <| α ↪ β) fun α β γ δ ⟨e₁⟩ ⟨e₂⟩ =>
      propext ⟨fun ⟨e⟩ => ⟨e.congr e₁ e₂⟩, fun ⟨e⟩ => ⟨e.congr e₁.symm e₂.symm⟩⟩⟩

instance : PartialOrder Cardinal.{u} where
  le := (· ≤ ·)
  le_refl := by rintro ⟨α⟩ <;> exact ⟨embedding.refl _⟩
  le_trans := by rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨e₁⟩ ⟨e₂⟩ <;> exact ⟨e₁.trans e₂⟩
  le_antisymm := by
    rintro ⟨α⟩ ⟨β⟩ ⟨e₁⟩ ⟨e₂⟩
    exact Quotient.sound (e₁.antisymm e₂)

#print Cardinal.le_def /-
theorem le_def (α β : Type u) : (#α) ≤ (#β) ↔ Nonempty (α ↪ β) :=
  Iff.rfl
#align cardinal.le_def Cardinal.le_def
-/

#print Cardinal.mk_le_of_injective /-
theorem mk_le_of_injective {α β : Type u} {f : α → β} (hf : Injective f) : (#α) ≤ (#β) :=
  ⟨⟨f, hf⟩⟩
#align cardinal.mk_le_of_injective Cardinal.mk_le_of_injective
-/

#print Function.Embedding.cardinal_le /-
theorem Function.Embedding.cardinal_le {α β : Type u} (f : α ↪ β) : (#α) ≤ (#β) :=
  ⟨f⟩
#align function.embedding.cardinal_le Function.Embedding.cardinal_le
-/

#print Cardinal.mk_le_of_surjective /-
theorem mk_le_of_surjective {α β : Type u} {f : α → β} (hf : Surjective f) : (#β) ≤ (#α) :=
  ⟨Embedding.ofSurjective f hf⟩
#align cardinal.mk_le_of_surjective Cardinal.mk_le_of_surjective
-/

#print Cardinal.le_mk_iff_exists_set /-
theorem le_mk_iff_exists_set {c : Cardinal} {α : Type u} : c ≤ (#α) ↔ ∃ p : Set α, (#p) = c :=
  ⟨inductionOn c fun β ⟨⟨f, hf⟩⟩ => ⟨Set.range f, (Equiv.ofInjective f hf).cardinal_eq.symm⟩,
    fun ⟨p, e⟩ => e ▸ ⟨⟨Subtype.val, fun a b => Subtype.eq⟩⟩⟩
#align cardinal.le_mk_iff_exists_set Cardinal.le_mk_iff_exists_set
-/

#print Cardinal.mk_subtype_le /-
theorem mk_subtype_le {α : Type u} (p : α → Prop) : (#Subtype p) ≤ (#α) :=
  ⟨Embedding.subtype p⟩
#align cardinal.mk_subtype_le Cardinal.mk_subtype_le
-/

#print Cardinal.mk_set_le /-
theorem mk_set_le (s : Set α) : (#s) ≤ (#α) :=
  mk_subtype_le s
#align cardinal.mk_set_le Cardinal.mk_set_le
-/

#print Cardinal.out_embedding /-
theorem out_embedding {c c' : Cardinal} : c ≤ c' ↔ Nonempty (c.out ↪ c'.out) :=
  by
  trans _
  rw [← Quotient.out_eq c, ← Quotient.out_eq c']
  rfl
#align cardinal.out_embedding Cardinal.out_embedding
-/

#print Cardinal.lift_mk_le /-
theorem lift_mk_le {α : Type u} {β : Type v} :
    lift.{max v w} (#α) ≤ lift.{max u w} (#β) ↔ Nonempty (α ↪ β) :=
  ⟨fun ⟨f⟩ => ⟨Embedding.congr Equiv.ulift Equiv.ulift f⟩, fun ⟨f⟩ =>
    ⟨Embedding.congr Equiv.ulift.symm Equiv.ulift.symm f⟩⟩
#align cardinal.lift_mk_le Cardinal.lift_mk_le
-/

#print Cardinal.lift_mk_le' /-
/-- A variant of `cardinal.lift_mk_le` with specialized universes.
Because Lean often can not realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specialization problem either.
-/
theorem lift_mk_le' {α : Type u} {β : Type v} : lift.{v} (#α) ≤ lift.{u} (#β) ↔ Nonempty (α ↪ β) :=
  lift_mk_le.{u, v, 0}
#align cardinal.lift_mk_le' Cardinal.lift_mk_le'
-/

#print Cardinal.lift_mk_eq /-
theorem lift_mk_eq {α : Type u} {β : Type v} :
    lift.{max v w} (#α) = lift.{max u w} (#β) ↔ Nonempty (α ≃ β) :=
  Quotient.eq'.trans
    ⟨fun ⟨f⟩ => ⟨Equiv.ulift.symm.trans <| f.trans Equiv.ulift⟩, fun ⟨f⟩ =>
      ⟨Equiv.ulift.trans <| f.trans Equiv.ulift.symm⟩⟩
#align cardinal.lift_mk_eq Cardinal.lift_mk_eq
-/

#print Cardinal.lift_mk_eq' /-
/-- A variant of `cardinal.lift_mk_eq` with specialized universes.
Because Lean often can not realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specialization problem either.
-/
theorem lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} (#α) = lift.{u} (#β) ↔ Nonempty (α ≃ β) :=
  lift_mk_eq.{u, v, 0}
#align cardinal.lift_mk_eq' Cardinal.lift_mk_eq'
-/

#print Cardinal.lift_le /-
@[simp]
theorem lift_le {a b : Cardinal} : lift a ≤ lift b ↔ a ≤ b :=
  inductionOn₂ a b fun α β => by
    rw [← lift_umax]
    exact lift_mk_le
#align cardinal.lift_le Cardinal.lift_le
-/

#print Cardinal.liftOrderEmbedding /-
/-- `cardinal.lift` as an `order_embedding`. -/
@[simps (config := { fullyApplied := false })]
def liftOrderEmbedding : Cardinal.{v} ↪o Cardinal.{max v u} :=
  OrderEmbedding.ofMapLeIff lift fun _ _ => lift_le
#align cardinal.lift_order_embedding Cardinal.liftOrderEmbedding
-/

#print Cardinal.lift_injective /-
theorem lift_injective : Injective lift.{u, v} :=
  liftOrderEmbedding.Injective
#align cardinal.lift_injective Cardinal.lift_injective
-/

#print Cardinal.lift_inj /-
@[simp]
theorem lift_inj {a b : Cardinal} : lift a = lift b ↔ a = b :=
  lift_injective.eq_iff
#align cardinal.lift_inj Cardinal.lift_inj
-/

#print Cardinal.lift_lt /-
@[simp]
theorem lift_lt {a b : Cardinal} : lift a < lift b ↔ a < b :=
  liftOrderEmbedding.lt_iff_lt
#align cardinal.lift_lt Cardinal.lift_lt
-/

/- warning: cardinal.lift_strict_mono -> Cardinal.lift_strictMono is a dubious translation:
lean 3 declaration is
  StrictMono.{succ u1, succ (max u1 u2)} Cardinal.{u1} Cardinal.{max u1 u2} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) (PartialOrder.toPreorder.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.partialOrder.{max u1 u2}) Cardinal.lift.{u2, u1}
but is expected to have type
  StrictMono.{succ u2, max (succ u2) (succ u1)} Cardinal.{u2} Cardinal.{max u2 u1} (PartialOrder.toPreorder.{succ u2} Cardinal.{u2} Cardinal.partialOrder.{u2}) (PartialOrder.toPreorder.{max (succ u2) (succ u1)} Cardinal.{max u2 u1} Cardinal.partialOrder.{max u2 u1}) Cardinal.lift.{u1, u2}
Case conversion may be inaccurate. Consider using '#align cardinal.lift_strict_mono Cardinal.lift_strictMonoₓ'. -/
theorem lift_strictMono : StrictMono lift := fun a b => lift_lt.2
#align cardinal.lift_strict_mono Cardinal.lift_strictMono

/- warning: cardinal.lift_monotone -> Cardinal.lift_monotone is a dubious translation:
lean 3 declaration is
  Monotone.{succ u1, succ (max u1 u2)} Cardinal.{u1} Cardinal.{max u1 u2} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) (PartialOrder.toPreorder.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.partialOrder.{max u1 u2}) Cardinal.lift.{u2, u1}
but is expected to have type
  Monotone.{succ u2, max (succ u2) (succ u1)} Cardinal.{u2} Cardinal.{max u2 u1} (PartialOrder.toPreorder.{succ u2} Cardinal.{u2} Cardinal.partialOrder.{u2}) (PartialOrder.toPreorder.{max (succ u2) (succ u1)} Cardinal.{max u2 u1} Cardinal.partialOrder.{max u2 u1}) Cardinal.lift.{u1, u2}
Case conversion may be inaccurate. Consider using '#align cardinal.lift_monotone Cardinal.lift_monotoneₓ'. -/
theorem lift_monotone : Monotone lift :=
  lift_strictMono.Monotone
#align cardinal.lift_monotone Cardinal.lift_monotone

instance : Zero Cardinal.{u} :=
  ⟨#PEmpty⟩

instance : Inhabited Cardinal.{u} :=
  ⟨0⟩

#print Cardinal.mk_eq_zero /-
theorem mk_eq_zero (α : Type u) [IsEmpty α] : (#α) = 0 :=
  (Equiv.equivPEmpty α).cardinal_eq
#align cardinal.mk_eq_zero Cardinal.mk_eq_zero
-/

/- warning: cardinal.lift_zero -> Cardinal.lift_zero is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))) (OfNat.ofNat.{succ (max u1 u2)} Cardinal.{max u1 u2} 0 (OfNat.mk.{succ (max u1 u2)} Cardinal.{max u1 u2} 0 (Zero.zero.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasZero.{max u1 u2})))
but is expected to have type
  Eq.{max (succ (succ u2)) (succ (succ u1))} Cardinal.{max u2 u1} (Cardinal.lift.{u1, u2} (OfNat.ofNat.{succ u2} Cardinal.{u2} 0 (Zero.toOfNat0.{succ u2} Cardinal.{u2} Cardinal.instZeroCardinal.{u2}))) (OfNat.ofNat.{max (succ u2) (succ u1)} Cardinal.{max u2 u1} 0 (Zero.toOfNat0.{max (succ u2) (succ u1)} Cardinal.{max u2 u1} Cardinal.instZeroCardinal.{max u2 u1}))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_zero Cardinal.lift_zeroₓ'. -/
@[simp]
theorem lift_zero : lift 0 = 0 :=
  mk_congr (Equiv.equivPEmpty _)
#align cardinal.lift_zero Cardinal.lift_zero

#print Cardinal.lift_eq_zero /-
@[simp]
theorem lift_eq_zero {a : Cardinal.{v}} : lift.{u} a = 0 ↔ a = 0 :=
  lift_injective.eq_iff' lift_zero
#align cardinal.lift_eq_zero Cardinal.lift_eq_zero
-/

#print Cardinal.mk_eq_zero_iff /-
theorem mk_eq_zero_iff {α : Type u} : (#α) = 0 ↔ IsEmpty α :=
  ⟨fun e =>
    let ⟨h⟩ := Quotient.exact e
    h.isEmpty,
    @mk_eq_zero α⟩
#align cardinal.mk_eq_zero_iff Cardinal.mk_eq_zero_iff
-/

#print Cardinal.mk_ne_zero_iff /-
theorem mk_ne_zero_iff {α : Type u} : (#α) ≠ 0 ↔ Nonempty α :=
  (not_iff_not.2 mk_eq_zero_iff).trans not_isEmpty_iff
#align cardinal.mk_ne_zero_iff Cardinal.mk_ne_zero_iff
-/

#print Cardinal.mk_ne_zero /-
@[simp]
theorem mk_ne_zero (α : Type u) [Nonempty α] : (#α) ≠ 0 :=
  mk_ne_zero_iff.2 ‹_›
#align cardinal.mk_ne_zero Cardinal.mk_ne_zero
-/

instance : One Cardinal.{u} :=
  ⟨#PUnit⟩

instance : Nontrivial Cardinal.{u} :=
  ⟨⟨1, 0, mk_ne_zero _⟩⟩

#print Cardinal.mk_eq_one /-
theorem mk_eq_one (α : Type u) [Unique α] : (#α) = 1 :=
  (Equiv.equivPUnit α).cardinal_eq
#align cardinal.mk_eq_one Cardinal.mk_eq_one
-/

#print Cardinal.le_one_iff_subsingleton /-
theorem le_one_iff_subsingleton {α : Type u} : (#α) ≤ 1 ↔ Subsingleton α :=
  ⟨fun ⟨f⟩ => ⟨fun a b => f.Injective (Subsingleton.elim _ _)⟩, fun ⟨h⟩ =>
    ⟨⟨fun a => PUnit.unit, fun a b _ => h _ _⟩⟩⟩
#align cardinal.le_one_iff_subsingleton Cardinal.le_one_iff_subsingleton
-/

#print Cardinal.mk_le_one_iff_set_subsingleton /-
@[simp]
theorem mk_le_one_iff_set_subsingleton {s : Set α} : (#s) ≤ 1 ↔ s.Subsingleton :=
  le_one_iff_subsingleton.trans s.subsingleton_coe
#align cardinal.mk_le_one_iff_set_subsingleton Cardinal.mk_le_one_iff_set_subsingleton
-/

alias mk_le_one_iff_set_subsingleton ↔ _ _root_.set.subsingleton.cardinal_mk_le_one
#align set.subsingleton.cardinal_mk_le_one Set.Subsingleton.cardinal_mk_le_one

instance : Add Cardinal.{u} :=
  ⟨map₂ Sum fun α β γ δ => Equiv.sumCongr⟩

/- warning: cardinal.add_def -> Cardinal.add_def is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β)) (Cardinal.mk.{u1} (Sum.{u1, u1} α β))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β)) (Cardinal.mk.{u1} (Sum.{u1, u1} α β))
Case conversion may be inaccurate. Consider using '#align cardinal.add_def Cardinal.add_defₓ'. -/
theorem add_def (α β : Type u) : (#α) + (#β) = (#Sum α β) :=
  rfl
#align cardinal.add_def Cardinal.add_def

instance : NatCast Cardinal.{u} :=
  ⟨Nat.unaryCast⟩

/- warning: cardinal.mk_sum -> Cardinal.mk_sum is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}), Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.mk.{max u1 u2} (Sum.{u1, u2} α β)) (HAdd.hAdd.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHAdd.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasAdd.{max u1 u2}) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} α)) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} β)))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u2}), Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u2 u1} (Cardinal.mk.{max u2 u1} (Sum.{u1, u2} α β)) (HAdd.hAdd.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.{max u2 u1} Cardinal.{max u1 u2} (instHAdd.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instAddCardinal.{max u1 u2}) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} α)) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} β)))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_sum Cardinal.mk_sumₓ'. -/
@[simp]
theorem mk_sum (α : Type u) (β : Type v) : (#Sum α β) = lift.{v, u} (#α) + lift.{u, v} (#β) :=
  mk_congr (Equiv.ulift.symm.sumCongr Equiv.ulift.symm)
#align cardinal.mk_sum Cardinal.mk_sum

/- warning: cardinal.mk_option -> Cardinal.mk_option is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Option.{u1} α)) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) (Cardinal.mk.{u1} α) (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (OfNat.mk.{succ u1} Cardinal.{u1} 1 (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1}))))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Option.{u1} α)) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (Cardinal.mk.{u1} α) (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (One.toOfNat1.{succ u1} Cardinal.{u1} Cardinal.instOneCardinal.{u1})))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_option Cardinal.mk_optionₓ'. -/
@[simp]
theorem mk_option {α : Type u} : (#Option α) = (#α) + 1 :=
  (Equiv.optionEquivSumPUnit α).cardinal_eq
#align cardinal.mk_option Cardinal.mk_option

/- warning: cardinal.mk_psum -> Cardinal.mk_pSum is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}), Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.mk.{max u1 u2} (PSum.{succ u1, succ u2} α β)) (HAdd.hAdd.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHAdd.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasAdd.{max u1 u2}) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} α)) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} β)))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u2}), Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u1 u2} (Cardinal.mk.{max u1 u2} (PSum.{succ u1, succ u2} α β)) (HAdd.hAdd.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.{max u2 u1} Cardinal.{max u1 u2} (instHAdd.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instAddCardinal.{max u1 u2}) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} α)) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} β)))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_psum Cardinal.mk_pSumₓ'. -/
@[simp]
theorem mk_pSum (α : Type u) (β : Type v) : (#PSum α β) = lift.{v} (#α) + lift.{u} (#β) :=
  (mk_congr (Equiv.psumEquivSum α β)).trans (mk_sum α β)
#align cardinal.mk_psum Cardinal.mk_pSum

/- warning: cardinal.mk_fintype -> Cardinal.mk_fintype is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Fintype.{u1} α], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} α) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) (Fintype.card.{u1} α _inst_1))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Fintype.{u1} α], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} α) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} (Fintype.card.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_fintype Cardinal.mk_fintypeₓ'. -/
@[simp]
theorem mk_fintype (α : Type u) [Fintype α] : (#α) = Fintype.card α :=
  by
  refine' Fintype.induction_empty_option _ _ _ α
  · intro α β h e hα
    letI := Fintype.ofEquiv β e.symm
    rwa [mk_congr e, Fintype.card_congr e] at hα
  · rfl
  · intro α h hα
    simp [hα]
    rfl
#align cardinal.mk_fintype Cardinal.mk_fintype

instance : Mul Cardinal.{u} :=
  ⟨map₂ Prod fun α β γ δ => Equiv.prodCongr⟩

/- warning: cardinal.mul_def -> Cardinal.mul_def is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β)) (Cardinal.mk.{u1} (Prod.{u1, u1} α β))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β)) (Cardinal.mk.{u1} (Prod.{u1, u1} α β))
Case conversion may be inaccurate. Consider using '#align cardinal.mul_def Cardinal.mul_defₓ'. -/
theorem mul_def (α β : Type u) : (#α) * (#β) = (#α × β) :=
  rfl
#align cardinal.mul_def Cardinal.mul_def

/- warning: cardinal.mk_prod -> Cardinal.mk_prod is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}), Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.mk.{max u1 u2} (Prod.{u1, u2} α β)) (HMul.hMul.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHMul.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasMul.{max u1 u2}) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} α)) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} β)))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u2}), Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u2 u1} (Cardinal.mk.{max u2 u1} (Prod.{u1, u2} α β)) (HMul.hMul.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.{max u2 u1} Cardinal.{max u1 u2} (instHMul.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instMulCardinal.{max u1 u2}) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} α)) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} β)))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_prod Cardinal.mk_prodₓ'. -/
@[simp]
theorem mk_prod (α : Type u) (β : Type v) : (#α × β) = lift.{v, u} (#α) * lift.{u, v} (#β) :=
  mk_congr (Equiv.ulift.symm.prodCongr Equiv.ulift.symm)
#align cardinal.mk_prod Cardinal.mk_prod

private theorem mul_comm' (a b : Cardinal.{u}) : a * b = b * a :=
  inductionOn₂ a b fun α β => mk_congr <| Equiv.prodComm α β
#align cardinal.mul_comm' cardinal.mul_comm'

/-- The cardinal exponential. `#α ^ #β` is the cardinal of `β → α`. -/
instance : Pow Cardinal.{u} Cardinal.{u} :=
  ⟨map₂ (fun α β => β → α) fun α β γ δ e₁ e₂ => e₂.arrowCongr e₁⟩

-- mathport name: cardinal.pow
local infixr:0 "^" => @Pow.pow Cardinal Cardinal Cardinal.hasPow

-- mathport name: cardinal.pow.nat
local infixr:80 " ^ℕ " => @Pow.pow Cardinal ℕ Monoid.Pow

#print Cardinal.power_def /-
theorem power_def (α β) : ((#α)^#β) = (#β → α) :=
  rfl
#align cardinal.power_def Cardinal.power_def
-/

#print Cardinal.mk_arrow /-
theorem mk_arrow (α : Type u) (β : Type v) : (#α → β) = (lift.{u} (#β)^lift.{v} (#α)) :=
  mk_congr (Equiv.ulift.symm.arrowCongr Equiv.ulift.symm)
#align cardinal.mk_arrow Cardinal.mk_arrow
-/

#print Cardinal.lift_power /-
@[simp]
theorem lift_power (a b) : lift (a^b) = (lift a^lift b) :=
  inductionOn₂ a b fun α β =>
    mk_congr <| Equiv.ulift.trans (Equiv.ulift.arrowCongr Equiv.ulift).symm
#align cardinal.lift_power Cardinal.lift_power
-/

#print Cardinal.power_zero /-
@[simp]
theorem power_zero {a : Cardinal} : (a^0) = 1 :=
  inductionOn a fun α => mk_congr <| Equiv.pemptyArrowEquivPUnit α
#align cardinal.power_zero Cardinal.power_zero
-/

#print Cardinal.power_one /-
@[simp]
theorem power_one {a : Cardinal} : (a^1) = a :=
  inductionOn a fun α => mk_congr <| Equiv.punitArrowEquiv α
#align cardinal.power_one Cardinal.power_one
-/

/- warning: cardinal.power_add -> Cardinal.power_add is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) a (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) b c)) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) a c))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) a (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) b c)) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) a c))
Case conversion may be inaccurate. Consider using '#align cardinal.power_add Cardinal.power_addₓ'. -/
theorem power_add {a b c : Cardinal} : (a^b + c) = (a^b) * (a^c) :=
  inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.sumArrowEquivProdArrow β γ α
#align cardinal.power_add Cardinal.power_add

instance : CommSemiring Cardinal.{u} where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  zero_add a := inductionOn a fun α => mk_congr <| Equiv.emptySum PEmpty α
  add_zero a := inductionOn a fun α => mk_congr <| Equiv.sumEmpty α PEmpty
  add_assoc a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.sumAssoc α β γ
  add_comm a b := inductionOn₂ a b fun α β => mk_congr <| Equiv.sumComm α β
  zero_mul a := inductionOn a fun α => mk_congr <| Equiv.pemptyProd α
  mul_zero a := inductionOn a fun α => mk_congr <| Equiv.prodPEmpty α
  one_mul a := inductionOn a fun α => mk_congr <| Equiv.punitProd α
  mul_one a := inductionOn a fun α => mk_congr <| Equiv.prodPUnit α
  mul_assoc a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.prodAssoc α β γ
  mul_comm := mul_comm'
  left_distrib a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.prodSumDistrib α β γ
  right_distrib a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.sumProdDistrib α β γ
  npow n c := c^n
  npow_zero := @power_zero
  npow_succ n c := show (c^n + 1) = c * (c^n) by rw [power_add, power_one, mul_comm']

/- warning: cardinal.power_bit0 -> Cardinal.power_bit0 is a dubious translation:
lean 3 declaration is
  forall (a : Cardinal.{u1}) (b : Cardinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) a (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} b)) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) a b))
but is expected to have type
  forall (a : Cardinal.{u1}) (b : Cardinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) a (bit0.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1} b)) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) a b))
Case conversion may be inaccurate. Consider using '#align cardinal.power_bit0 Cardinal.power_bit0ₓ'. -/
theorem power_bit0 (a b : Cardinal) : (a^bit0 b) = (a^b) * (a^b) :=
  power_add
#align cardinal.power_bit0 Cardinal.power_bit0

/- warning: cardinal.power_bit1 -> Cardinal.power_bit1 is a dubious translation:
lean 3 declaration is
  forall (a : Cardinal.{u1}) (b : Cardinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) a (bit1.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1} Cardinal.hasAdd.{u1} b)) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) a b)) a)
but is expected to have type
  forall (a : Cardinal.{u1}) (b : Cardinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) a (bit1.{succ u1} Cardinal.{u1} Cardinal.instOneCardinal.{u1} Cardinal.instAddCardinal.{u1} b)) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) a b)) a)
Case conversion may be inaccurate. Consider using '#align cardinal.power_bit1 Cardinal.power_bit1ₓ'. -/
theorem power_bit1 (a b : Cardinal) : (a^bit1 b) = (a^b) * (a^b) * a := by
  rw [bit1, ← power_bit0, power_add, power_one]
#align cardinal.power_bit1 Cardinal.power_bit1

#print Cardinal.one_power /-
@[simp]
theorem one_power {a : Cardinal} : (1^a) = 1 :=
  inductionOn a fun α => (Equiv.arrowPUnitEquivPUnit α).cardinal_eq
#align cardinal.one_power Cardinal.one_power
-/

/- warning: cardinal.mk_bool -> Cardinal.mk_bool is a dubious translation:
lean 3 declaration is
  Eq.{2} Cardinal.{0} (Cardinal.mk.{0} Bool) (OfNat.ofNat.{1} Cardinal.{0} 2 (OfNat.mk.{1} Cardinal.{0} 2 (bit0.{1} Cardinal.{0} Cardinal.hasAdd.{0} (One.one.{1} Cardinal.{0} Cardinal.hasOne.{0}))))
but is expected to have type
  Eq.{2} Cardinal.{0} (Cardinal.mk.{0} Bool) (OfNat.ofNat.{1} Cardinal.{0} 2 (instOfNat.{1} Cardinal.{0} 2 Cardinal.instNatCastCardinal.{0} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_bool Cardinal.mk_boolₓ'. -/
@[simp]
theorem mk_bool : (#Bool) = 2 := by simp
#align cardinal.mk_bool Cardinal.mk_bool

/- warning: cardinal.mk_Prop -> Cardinal.mk_Prop is a dubious translation:
lean 3 declaration is
  Eq.{2} Cardinal.{0} (Cardinal.mk.{0} Prop) (OfNat.ofNat.{1} Cardinal.{0} 2 (OfNat.mk.{1} Cardinal.{0} 2 (bit0.{1} Cardinal.{0} Cardinal.hasAdd.{0} (One.one.{1} Cardinal.{0} Cardinal.hasOne.{0}))))
but is expected to have type
  Eq.{2} Cardinal.{0} (Cardinal.mk.{0} Prop) (OfNat.ofNat.{1} Cardinal.{0} 2 (instOfNat.{1} Cardinal.{0} 2 Cardinal.instNatCastCardinal.{0} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_Prop Cardinal.mk_Propₓ'. -/
@[simp]
theorem mk_Prop : (#Prop) = 2 := by simp
#align cardinal.mk_Prop Cardinal.mk_Prop

#print Cardinal.zero_power /-
@[simp]
theorem zero_power {a : Cardinal} : a ≠ 0 → (0^a) = 0 :=
  inductionOn a fun α heq =>
    mk_eq_zero_iff.2 <|
      isEmpty_pi.2 <|
        let ⟨a⟩ := mk_ne_zero_iff.1 HEq
        ⟨a, PEmpty.isEmpty⟩
#align cardinal.zero_power Cardinal.zero_power
-/

#print Cardinal.power_ne_zero /-
theorem power_ne_zero {a : Cardinal} (b) : a ≠ 0 → (a^b) ≠ 0 :=
  inductionOn₂ a b fun α β h =>
    let ⟨a⟩ := mk_ne_zero_iff.1 h
    mk_ne_zero_iff.2 ⟨fun _ => a⟩
#align cardinal.power_ne_zero Cardinal.power_ne_zero
-/

/- warning: cardinal.mul_power -> Cardinal.mul_power is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b) c) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) a c) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) b c))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b) c) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) a c) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) b c))
Case conversion may be inaccurate. Consider using '#align cardinal.mul_power Cardinal.mul_powerₓ'. -/
theorem mul_power {a b c : Cardinal} : (a * b^c) = (a^c) * (b^c) :=
  inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.arrowProdEquivProdArrow α β γ
#align cardinal.mul_power Cardinal.mul_power

/- warning: cardinal.power_mul -> Cardinal.power_mul is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) a (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) b c)) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) a b) c)
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) a (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) b c)) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) a b) c)
Case conversion may be inaccurate. Consider using '#align cardinal.power_mul Cardinal.power_mulₓ'. -/
theorem power_mul {a b c : Cardinal} : (a^b * c) = ((a^b)^c) :=
  by
  rw [mul_comm b c]
  exact induction_on₃ a b c fun α β γ => mk_congr <| Equiv.curry γ β α
#align cardinal.power_mul Cardinal.power_mul

/- warning: cardinal.pow_cast_right -> Cardinal.pow_cast_right is a dubious translation:
lean 3 declaration is
  forall (a : Cardinal.{u1}) (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) a ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) (HPow.hPow.{succ u1, 0, succ u1} Cardinal.{u1} Nat Cardinal.{u1} (instHPow.{succ u1, 0} Cardinal.{u1} Nat (Monoid.Pow.{succ u1} Cardinal.{u1} (MonoidWithZero.toMonoid.{succ u1} Cardinal.{u1} (Semiring.toMonoidWithZero.{succ u1} Cardinal.{u1} (CommSemiring.toSemiring.{succ u1} Cardinal.{u1} Cardinal.commSemiring.{u1}))))) a n)
but is expected to have type
  forall (a : Cardinal.{u1}) (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) a (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (HPow.hPow.{succ u1, 0, succ u1} Cardinal.{u1} Nat Cardinal.{u1} (instHPow.{succ u1, 0} Cardinal.{u1} Nat (Monoid.Pow.{succ u1} Cardinal.{u1} (MonoidWithZero.toMonoid.{succ u1} Cardinal.{u1} (Semiring.toMonoidWithZero.{succ u1} Cardinal.{u1} (CommSemiring.toSemiring.{succ u1} Cardinal.{u1} Cardinal.commSemiring.{u1}))))) a n)
Case conversion may be inaccurate. Consider using '#align cardinal.pow_cast_right Cardinal.pow_cast_rightₓ'. -/
@[simp]
theorem pow_cast_right (a : Cardinal.{u}) (n : ℕ) : (a^(↑n : Cardinal.{u})) = a ^ℕ n :=
  rfl
#align cardinal.pow_cast_right Cardinal.pow_cast_right

/- warning: cardinal.lift_one -> Cardinal.lift_one is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (OfNat.mk.{succ u1} Cardinal.{u1} 1 (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) (OfNat.ofNat.{succ (max u1 u2)} Cardinal.{max u1 u2} 1 (OfNat.mk.{succ (max u1 u2)} Cardinal.{max u1 u2} 1 (One.one.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasOne.{max u1 u2})))
but is expected to have type
  Eq.{max (succ (succ u2)) (succ (succ u1))} Cardinal.{max u2 u1} (Cardinal.lift.{u1, u2} (OfNat.ofNat.{succ u2} Cardinal.{u2} 1 (One.toOfNat1.{succ u2} Cardinal.{u2} Cardinal.instOneCardinal.{u2}))) (OfNat.ofNat.{max (succ u2) (succ u1)} Cardinal.{max u2 u1} 1 (One.toOfNat1.{max (succ u2) (succ u1)} Cardinal.{max u2 u1} Cardinal.instOneCardinal.{max u2 u1}))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_one Cardinal.lift_oneₓ'. -/
@[simp]
theorem lift_one : lift 1 = 1 :=
  mk_congr <| Equiv.ulift.trans Equiv.punitEquivPUnit
#align cardinal.lift_one Cardinal.lift_one

/- warning: cardinal.lift_add -> Cardinal.lift_add is a dubious translation:
lean 3 declaration is
  forall (a : Cardinal.{u1}) (b : Cardinal.{u1}), Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) a b)) (HAdd.hAdd.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHAdd.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasAdd.{max u1 u2}) (Cardinal.lift.{u2, u1} a) (Cardinal.lift.{u2, u1} b))
but is expected to have type
  forall (a : Cardinal.{u1}) (b : Cardinal.{u1}), Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) a b)) (HAdd.hAdd.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHAdd.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instAddCardinal.{max u1 u2}) (Cardinal.lift.{u2, u1} a) (Cardinal.lift.{u2, u1} b))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_add Cardinal.lift_addₓ'. -/
@[simp]
theorem lift_add (a b) : lift (a + b) = lift a + lift b :=
  inductionOn₂ a b fun α β =>
    mk_congr <| Equiv.ulift.trans (Equiv.sumCongr Equiv.ulift Equiv.ulift).symm
#align cardinal.lift_add Cardinal.lift_add

/- warning: cardinal.lift_mul -> Cardinal.lift_mul is a dubious translation:
lean 3 declaration is
  forall (a : Cardinal.{u1}) (b : Cardinal.{u1}), Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b)) (HMul.hMul.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHMul.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasMul.{max u1 u2}) (Cardinal.lift.{u2, u1} a) (Cardinal.lift.{u2, u1} b))
but is expected to have type
  forall (a : Cardinal.{u1}) (b : Cardinal.{u1}), Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b)) (HMul.hMul.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHMul.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instMulCardinal.{max u1 u2}) (Cardinal.lift.{u2, u1} a) (Cardinal.lift.{u2, u1} b))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_mul Cardinal.lift_mulₓ'. -/
@[simp]
theorem lift_mul (a b) : lift (a * b) = lift a * lift b :=
  inductionOn₂ a b fun α β =>
    mk_congr <| Equiv.ulift.trans (Equiv.prodCongr Equiv.ulift Equiv.ulift).symm
#align cardinal.lift_mul Cardinal.lift_mul

/- warning: cardinal.lift_bit0 -> Cardinal.lift_bit0 is a dubious translation:
lean 3 declaration is
  forall (a : Cardinal.{u1}), Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} a)) (bit0.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasAdd.{max u1 u2} (Cardinal.lift.{u2, u1} a))
but is expected to have type
  forall (a : Cardinal.{u1}), Eq.{max (succ (succ u2)) (succ (succ u1))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (bit0.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1} a)) (bit0.{max (succ u2) (succ u1)} Cardinal.{max u1 u2} Cardinal.instAddCardinal.{max u2 u1} (Cardinal.lift.{u2, u1} a))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_bit0 Cardinal.lift_bit0ₓ'. -/
@[simp]
theorem lift_bit0 (a : Cardinal) : lift (bit0 a) = bit0 (lift a) :=
  lift_add a a
#align cardinal.lift_bit0 Cardinal.lift_bit0

/- warning: cardinal.lift_bit1 -> Cardinal.lift_bit1 is a dubious translation:
lean 3 declaration is
  forall (a : Cardinal.{u1}), Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (bit1.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1} Cardinal.hasAdd.{u1} a)) (bit1.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasOne.{max u1 u2} Cardinal.hasAdd.{max u1 u2} (Cardinal.lift.{u2, u1} a))
but is expected to have type
  forall (a : Cardinal.{u1}), Eq.{max (succ (succ u2)) (succ (succ u1))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (bit1.{succ u1} Cardinal.{u1} Cardinal.instOneCardinal.{u1} Cardinal.instAddCardinal.{u1} a)) (bit1.{max (succ u2) (succ u1)} Cardinal.{max u1 u2} Cardinal.instOneCardinal.{max u2 u1} Cardinal.instAddCardinal.{max u2 u1} (Cardinal.lift.{u2, u1} a))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_bit1 Cardinal.lift_bit1ₓ'. -/
@[simp]
theorem lift_bit1 (a : Cardinal) : lift (bit1 a) = bit1 (lift a) := by simp [bit1]
#align cardinal.lift_bit1 Cardinal.lift_bit1

/- warning: cardinal.lift_two -> Cardinal.lift_two is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ (max u2 u1))} Cardinal.{max u2 u1} (Cardinal.lift.{u1, u2} (OfNat.ofNat.{succ u2} Cardinal.{u2} 2 (OfNat.mk.{succ u2} Cardinal.{u2} 2 (bit0.{succ u2} Cardinal.{u2} Cardinal.hasAdd.{u2} (One.one.{succ u2} Cardinal.{u2} Cardinal.hasOne.{u2}))))) (OfNat.ofNat.{succ (max u2 u1)} Cardinal.{max u2 u1} 2 (OfNat.mk.{succ (max u2 u1)} Cardinal.{max u2 u1} 2 (bit0.{succ (max u2 u1)} Cardinal.{max u2 u1} Cardinal.hasAdd.{max u2 u1} (One.one.{succ (max u2 u1)} Cardinal.{max u2 u1} Cardinal.hasOne.{max u2 u1}))))
but is expected to have type
  Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u2 u1} (Cardinal.lift.{u1, u2} (OfNat.ofNat.{succ u2} Cardinal.{u2} 2 (instOfNat.{succ u2} Cardinal.{u2} 2 Cardinal.instNatCastCardinal.{u2} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (OfNat.ofNat.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} 2 (instOfNat.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} 2 Cardinal.instNatCastCardinal.{max u1 u2} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_two Cardinal.lift_twoₓ'. -/
theorem lift_two : lift.{u, v} 2 = 2 := by simp
#align cardinal.lift_two Cardinal.lift_two

/- warning: cardinal.mk_set -> Cardinal.mk_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Set.{u1} α)) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (OfNat.mk.{succ u1} Cardinal.{u1} 2 (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) (Cardinal.mk.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Set.{u1} α)) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (instOfNat.{succ u1} Cardinal.{u1} 2 Cardinal.instNatCastCardinal.{u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Cardinal.mk.{u1} α))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_set Cardinal.mk_setₓ'. -/
@[simp]
theorem mk_set {α : Type u} : (#Set α) = (2^#α) := by simp [Set, mk_arrow]
#align cardinal.mk_set Cardinal.mk_set

/- warning: cardinal.mk_powerset -> Cardinal.mk_powerset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) (Set.powerset.{u1} α s))) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (OfNat.mk.{succ u1} Cardinal.{u1} 2 (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} (Set.{u1} α) (Set.powerset.{u1} α s))) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (instOfNat.{succ u1} Cardinal.{u1} 2 Cardinal.instNatCastCardinal.{u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Cardinal.mk.{u1} (Set.Elem.{u1} α s)))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_powerset Cardinal.mk_powersetₓ'. -/
/-- A variant of `cardinal.mk_set` expressed in terms of a `set` instead of a `Type`. -/
@[simp]
theorem mk_powerset {α : Type u} (s : Set α) : (#↥(𝒫 s)) = (2^#↥s) :=
  (mk_congr (Equiv.Set.powerset s)).trans mk_set
#align cardinal.mk_powerset Cardinal.mk_powerset

/- warning: cardinal.lift_two_power -> Cardinal.lift_two_power is a dubious translation:
lean 3 declaration is
  forall (a : Cardinal.{u1}), Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (OfNat.mk.{succ u1} Cardinal.{u1} 2 (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) a)) (HPow.hPow.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHPow.{succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.hasPow.{max u1 u2}) (OfNat.ofNat.{succ (max u1 u2)} Cardinal.{max u1 u2} 2 (OfNat.mk.{succ (max u1 u2)} Cardinal.{max u1 u2} 2 (bit0.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasAdd.{max u1 u2} (One.one.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasOne.{max u1 u2})))) (Cardinal.lift.{u2, u1} a))
but is expected to have type
  forall (a : Cardinal.{u1}), Eq.{max (succ (succ u2)) (succ (succ u1))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (instOfNat.{succ u1} Cardinal.{u1} 2 Cardinal.instNatCastCardinal.{u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) a)) (HPow.hPow.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHPow.{max (succ u2) (succ u1), max (succ u2) (succ u1)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.instPowCardinal.{max u2 u1}) (OfNat.ofNat.{max (succ u2) (succ u1)} Cardinal.{max u1 u2} 2 (instOfNat.{max (succ u2) (succ u1)} Cardinal.{max u1 u2} 2 Cardinal.instNatCastCardinal.{max u2 u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Cardinal.lift.{u2, u1} a))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_two_power Cardinal.lift_two_powerₓ'. -/
theorem lift_two_power (a) : lift (2^a) = (2^lift a) := by simp
#align cardinal.lift_two_power Cardinal.lift_two_power

section OrderProperties

open Sum

#print Cardinal.zero_le /-
protected theorem zero_le : ∀ a : Cardinal, 0 ≤ a := by rintro ⟨α⟩ <;> exact ⟨embedding.of_is_empty⟩
#align cardinal.zero_le Cardinal.zero_le
-/

private theorem add_le_add' : ∀ {a b c d : Cardinal}, a ≤ b → c ≤ d → a + c ≤ b + d := by
  rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨δ⟩ ⟨e₁⟩ ⟨e₂⟩ <;> exact ⟨e₁.sum_map e₂⟩
#align cardinal.add_le_add' cardinal.add_le_add'

/- warning: cardinal.add_covariant_class -> Cardinal.add_covariantClass is a dubious translation:
lean 3 declaration is
  CovariantClass.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1})) (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1})
but is expected to have type
  CovariantClass.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} (fun (x._@.Mathlib.SetTheory.Cardinal.Basic._hyg.4896 : Cardinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Basic._hyg.4898 : Cardinal.{u1}) => HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) x._@.Mathlib.SetTheory.Cardinal.Basic._hyg.4896 x._@.Mathlib.SetTheory.Cardinal.Basic._hyg.4898) (fun (x._@.Mathlib.SetTheory.Cardinal.Basic._hyg.4911 : Cardinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Basic._hyg.4913 : Cardinal.{u1}) => LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} x._@.Mathlib.SetTheory.Cardinal.Basic._hyg.4911 x._@.Mathlib.SetTheory.Cardinal.Basic._hyg.4913)
Case conversion may be inaccurate. Consider using '#align cardinal.add_covariant_class Cardinal.add_covariantClassₓ'. -/
instance add_covariantClass : CovariantClass Cardinal Cardinal (· + ·) (· ≤ ·) :=
  ⟨fun a b c => add_le_add' le_rfl⟩
#align cardinal.add_covariant_class Cardinal.add_covariantClass

/- warning: cardinal.add_swap_covariant_class -> Cardinal.add_swap_covariantClass is a dubious translation:
lean 3 declaration is
  CovariantClass.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} (Function.swap.{succ (succ u1), succ (succ u1), succ (succ u1)} Cardinal.{u1} Cardinal.{u1} (fun (ᾰ : Cardinal.{u1}) (ᾰ : Cardinal.{u1}) => Cardinal.{u1}) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}))) (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1})
but is expected to have type
  CovariantClass.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} (Function.swap.{succ (succ u1), succ (succ u1), succ (succ u1)} Cardinal.{u1} Cardinal.{u1} (fun (ᾰ : Cardinal.{u1}) (ᾰ : Cardinal.{u1}) => Cardinal.{u1}) (fun (x._@.Mathlib.SetTheory.Cardinal.Basic._hyg.4963 : Cardinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Basic._hyg.4965 : Cardinal.{u1}) => HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) x._@.Mathlib.SetTheory.Cardinal.Basic._hyg.4963 x._@.Mathlib.SetTheory.Cardinal.Basic._hyg.4965)) (fun (x._@.Mathlib.SetTheory.Cardinal.Basic._hyg.4978 : Cardinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Basic._hyg.4980 : Cardinal.{u1}) => LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} x._@.Mathlib.SetTheory.Cardinal.Basic._hyg.4978 x._@.Mathlib.SetTheory.Cardinal.Basic._hyg.4980)
Case conversion may be inaccurate. Consider using '#align cardinal.add_swap_covariant_class Cardinal.add_swap_covariantClassₓ'. -/
instance add_swap_covariantClass : CovariantClass Cardinal Cardinal (swap (· + ·)) (· ≤ ·) :=
  ⟨fun a b c h => add_le_add' h le_rfl⟩
#align cardinal.add_swap_covariant_class Cardinal.add_swap_covariantClass

instance : CanonicallyOrderedCommSemiring Cardinal.{u} :=
  { Cardinal.commSemiring,
    Cardinal.partialOrder with
    bot := 0
    bot_le := Cardinal.zero_le
    add_le_add_left := fun a b => add_le_add_left
    exists_add_of_le := fun a b =>
      inductionOn₂ a b fun α β ⟨⟨f, hf⟩⟩ =>
        have : Sum α (range fᶜ : Set β) ≃ β :=
          (Equiv.sumCongr (Equiv.ofInjective f hf) (Equiv.refl _)).trans <|
            Equiv.Set.sumCompl (range f)
        ⟨#↥(range fᶜ), mk_congr this.symm⟩
    le_self_add := fun a b => (add_zero a).ge.trans <| add_le_add_left (Cardinal.zero_le _) _
    eq_zero_or_eq_zero_of_mul_eq_zero := fun a b =>
      inductionOn₂ a b fun α β => by simpa only [mul_def, mk_eq_zero_iff, isEmpty_prod] using id }

#print Cardinal.zero_power_le /-
theorem zero_power_le (c : Cardinal.{u}) : ((0 : Cardinal.{u})^c) ≤ 1 :=
  by
  by_cases h : c = 0
  rw [h, power_zero]
  rw [zero_power h]
  apply zero_le
#align cardinal.zero_power_le Cardinal.zero_power_le
-/

#print Cardinal.power_le_power_left /-
theorem power_le_power_left : ∀ {a b c : Cardinal}, a ≠ 0 → b ≤ c → (a^b) ≤ (a^c) := by
  rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ hα ⟨e⟩ <;>
    exact
      let ⟨a⟩ := mk_ne_zero_iff.1 hα
      ⟨@embedding.arrow_congr_left _ _ _ ⟨a⟩ e⟩
#align cardinal.power_le_power_left Cardinal.power_le_power_left
-/

#print Cardinal.self_le_power /-
theorem self_le_power (a : Cardinal) {b : Cardinal} (hb : 1 ≤ b) : a ≤ (a^b) :=
  by
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact zero_le _
  · convert power_le_power_left ha hb
    exact power_one.symm
#align cardinal.self_le_power Cardinal.self_le_power
-/

/- warning: cardinal.cantor -> Cardinal.cantor is a dubious translation:
lean 3 declaration is
  forall (a : Cardinal.{u1}), LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (OfNat.mk.{succ u1} Cardinal.{u1} 2 (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) a)
but is expected to have type
  forall (a : Cardinal.{u1}), LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (instOfNat.{succ u1} Cardinal.{u1} 2 Cardinal.instNatCastCardinal.{u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) a)
Case conversion may be inaccurate. Consider using '#align cardinal.cantor Cardinal.cantorₓ'. -/
/-- **Cantor's theorem** -/
theorem cantor (a : Cardinal.{u}) : a < (2^a) :=
  by
  induction' a using Cardinal.inductionOn with α
  rw [← mk_set]
  refine' ⟨⟨⟨singleton, fun a b => singleton_eq_singleton_iff.1⟩⟩, _⟩
  rintro ⟨⟨f, hf⟩⟩
  exact cantor_injective f hf
#align cardinal.cantor Cardinal.cantor

instance : NoMaxOrder Cardinal.{u} :=
  { Cardinal.partialOrder with exists_gt := fun a => ⟨_, cantor a⟩ }

instance : CanonicallyLinearOrderedAddMonoid Cardinal.{u} :=
  { (inferInstance : CanonicallyOrderedAddMonoid Cardinal),
    Cardinal.partialOrder with
    le_total := by
      rintro ⟨α⟩ ⟨β⟩
      apply embedding.total
    decidableLe := Classical.decRel _ }

-- short-circuit type class inference
instance : DistribLattice Cardinal.{u} := by infer_instance

#print Cardinal.one_lt_iff_nontrivial /-
theorem one_lt_iff_nontrivial {α : Type u} : 1 < (#α) ↔ Nontrivial α := by
  rw [← not_le, le_one_iff_subsingleton, ← not_nontrivial_iff_subsingleton, Classical.not_not]
#align cardinal.one_lt_iff_nontrivial Cardinal.one_lt_iff_nontrivial
-/

/- warning: cardinal.power_le_max_power_one -> Cardinal.power_le_max_power_one is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} b c) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) a b) (LinearOrder.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toLinearOrder.{succ u1} Cardinal.{u1} Cardinal.canonicallyLinearOrderedAddMonoid.{u1}) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) a c) (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (OfNat.mk.{succ u1} Cardinal.{u1} 1 (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} b c) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) a b) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) a c) (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (One.toOfNat1.{succ u1} Cardinal.{u1} Cardinal.instOneCardinal.{u1}))))
Case conversion may be inaccurate. Consider using '#align cardinal.power_le_max_power_one Cardinal.power_le_max_power_oneₓ'. -/
theorem power_le_max_power_one {a b c : Cardinal} (h : b ≤ c) : (a^b) ≤ max (a^c) 1 :=
  by
  by_cases ha : a = 0
  simp [ha, zero_power_le]
  exact (power_le_power_left ha h).trans (le_max_left _ _)
#align cardinal.power_le_max_power_one Cardinal.power_le_max_power_one

#print Cardinal.power_le_power_right /-
theorem power_le_power_right {a b c : Cardinal} : a ≤ b → (a^c) ≤ (b^c) :=
  inductionOn₃ a b c fun α β γ ⟨e⟩ => ⟨Embedding.arrowCongrRight e⟩
#align cardinal.power_le_power_right Cardinal.power_le_power_right
-/

#print Cardinal.power_pos /-
theorem power_pos {a : Cardinal} (b) (ha : 0 < a) : 0 < (a^b) :=
  (power_ne_zero _ ha.ne').bot_lt
#align cardinal.power_pos Cardinal.power_pos
-/

end OrderProperties

#print Cardinal.lt_wf /-
protected theorem lt_wf : @WellFounded Cardinal.{u} (· < ·) :=
  ⟨fun a =>
    by_contradiction fun h => by
      let ι := { c : Cardinal // ¬Acc (· < ·) c }
      let f : ι → Cardinal := Subtype.val
      haveI hι : Nonempty ι := ⟨⟨_, h⟩⟩
      obtain ⟨⟨c : Cardinal, hc : ¬Acc (· < ·) c⟩, ⟨h_1 : ∀ j, (f ⟨c, hc⟩).out ↪ (f j).out⟩⟩ :=
        embedding.min_injective fun i => (f i).out
      apply hc (Acc.intro _ fun j h' => by_contradiction fun hj => h'.2 _)
      have : (#_) ≤ (#_) := ⟨h_1 ⟨j, hj⟩⟩
      simpa only [f, mk_out] using this⟩
#align cardinal.lt_wf Cardinal.lt_wf
-/

instance : WellFoundedRelation Cardinal.{u} :=
  ⟨(· < ·), Cardinal.lt_wf⟩

instance : WellFoundedLT Cardinal.{u} :=
  ⟨Cardinal.lt_wf⟩

#print Cardinal.wo /-
instance wo : @IsWellOrder Cardinal.{u} (· < ·) where
#align cardinal.wo Cardinal.wo
-/

instance : ConditionallyCompleteLinearOrderBot Cardinal :=
  IsWellOrder.conditionallyCompleteLinearOrderBot _

/- warning: cardinal.Inf_empty -> Cardinal.infₛ_empty is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Cardinal.{u1} (InfSet.infₛ.{succ u1} Cardinal.{u1} (ConditionallyCompleteLattice.toHasInf.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1}))) (EmptyCollection.emptyCollection.{succ u1} (Set.{succ u1} Cardinal.{u1}) (Set.hasEmptyc.{succ u1} Cardinal.{u1}))) (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))
but is expected to have type
  Eq.{succ (succ u1)} Cardinal.{u1} (InfSet.infₛ.{succ u1} Cardinal.{u1} (ConditionallyCompleteLattice.toInfSet.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u1}))) (EmptyCollection.emptyCollection.{succ u1} (Set.{succ u1} Cardinal.{u1}) (Set.instEmptyCollectionSet.{succ u1} Cardinal.{u1}))) (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))
Case conversion may be inaccurate. Consider using '#align cardinal.Inf_empty Cardinal.infₛ_emptyₓ'. -/
@[simp]
theorem infₛ_empty : infₛ (∅ : Set Cardinal.{u}) = 0 :=
  dif_neg not_nonempty_empty
#align cardinal.Inf_empty Cardinal.infₛ_empty

/-- Note that the successor of `c` is not the same as `c + 1` except in the case of finite `c`. -/
instance : SuccOrder Cardinal :=
  SuccOrder.ofSuccLeIff (fun c => infₛ { c' | c < c' }) fun a b =>
    ⟨lt_of_lt_of_le <| cinfₛ_mem <| exists_gt a, cinfₛ_le'⟩

/- warning: cardinal.succ_def -> Cardinal.succ_def is a dubious translation:
lean 3 declaration is
  forall (c : Cardinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.succOrder.{u1} c) (InfSet.infₛ.{succ u1} Cardinal.{u1} (ConditionallyCompleteLattice.toHasInf.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1}))) (setOf.{succ u1} Cardinal.{u1} (fun (c' : Cardinal.{u1}) => LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) c c')))
but is expected to have type
  forall (c : Cardinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.instSuccOrderCardinalToPreorderPartialOrder.{u1} c) (InfSet.infₛ.{succ u1} Cardinal.{u1} (ConditionallyCompleteLattice.toInfSet.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u1}))) (setOf.{succ u1} Cardinal.{u1} (fun (c' : Cardinal.{u1}) => LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) c c')))
Case conversion may be inaccurate. Consider using '#align cardinal.succ_def Cardinal.succ_defₓ'. -/
theorem succ_def (c : Cardinal) : succ c = infₛ { c' | c < c' } :=
  rfl
#align cardinal.succ_def Cardinal.succ_def

/- warning: cardinal.add_one_le_succ -> Cardinal.add_one_le_succ is a dubious translation:
lean 3 declaration is
  forall (c : Cardinal.{u1}), LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) c (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (OfNat.mk.{succ u1} Cardinal.{u1} 1 (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.succOrder.{u1} c)
but is expected to have type
  forall (c : Cardinal.{u1}), LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) c (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (One.toOfNat1.{succ u1} Cardinal.{u1} Cardinal.instOneCardinal.{u1}))) (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.instSuccOrderCardinalToPreorderPartialOrder.{u1} c)
Case conversion may be inaccurate. Consider using '#align cardinal.add_one_le_succ Cardinal.add_one_le_succₓ'. -/
theorem add_one_le_succ (c : Cardinal.{u}) : c + 1 ≤ succ c :=
  by
  refine' (le_cinfₛ_iff'' (exists_gt c)).2 fun b hlt => _
  rcases b, c with ⟨⟨β⟩, ⟨γ⟩⟩
  cases' le_of_lt hlt with f
  have : ¬surjective f := fun hn => (not_le_of_lt hlt) (mk_le_of_surjective hn)
  simp only [surjective, not_forall] at this
  rcases this with ⟨b, hb⟩
  calc
    (#γ) + 1 = (#Option γ) := mk_option.symm
    _ ≤ (#β) := (f.option_elim b hb).cardinal_le
    
#align cardinal.add_one_le_succ Cardinal.add_one_le_succ

/- warning: cardinal.succ_pos -> Cardinal.succ_pos is a dubious translation:
lean 3 declaration is
  forall (c : Cardinal.{u1}), LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1}))) (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.succOrder.{u1} c)
but is expected to have type
  forall (c : Cardinal.{u1}), LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1})) (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.instSuccOrderCardinalToPreorderPartialOrder.{u1} c)
Case conversion may be inaccurate. Consider using '#align cardinal.succ_pos Cardinal.succ_posₓ'. -/
theorem succ_pos : ∀ c : Cardinal, 0 < succ c :=
  bot_lt_succ
#align cardinal.succ_pos Cardinal.succ_pos

/- warning: cardinal.succ_ne_zero -> Cardinal.succ_ne_zero is a dubious translation:
lean 3 declaration is
  forall (c : Cardinal.{u1}), Ne.{succ (succ u1)} Cardinal.{u1} (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.succOrder.{u1} c) (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))
but is expected to have type
  forall (c : Cardinal.{u1}), Ne.{succ (succ u1)} Cardinal.{u1} (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.instSuccOrderCardinalToPreorderPartialOrder.{u1} c) (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))
Case conversion may be inaccurate. Consider using '#align cardinal.succ_ne_zero Cardinal.succ_ne_zeroₓ'. -/
theorem succ_ne_zero (c : Cardinal) : succ c ≠ 0 :=
  (succ_pos _).ne'
#align cardinal.succ_ne_zero Cardinal.succ_ne_zero

#print Cardinal.sum /-
/-- The indexed sum of cardinals is the cardinality of the
  indexed disjoint union, i.e. sigma type. -/
def sum {ι} (f : ι → Cardinal) : Cardinal :=
  mk (Σi, (f i).out)
#align cardinal.sum Cardinal.sum
-/

/- warning: cardinal.le_sum -> Cardinal.le_sum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (f : ι -> Cardinal.{max u1 u2}) (i : ι), LE.le.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasLe.{max u1 u2} (f i) (Cardinal.sum.{u1, max u1 u2} ι f)
but is expected to have type
  forall {ι : Type.{u2}} (f : ι -> Cardinal.{max u2 u1}) (i : ι), LE.le.{max (succ u2) (succ u1)} Cardinal.{max u2 u1} Cardinal.instLECardinal.{max u2 u1} (f i) (Cardinal.sum.{u2, max u2 u1} ι f)
Case conversion may be inaccurate. Consider using '#align cardinal.le_sum Cardinal.le_sumₓ'. -/
theorem le_sum {ι} (f : ι → Cardinal) (i) : f i ≤ sum f := by
  rw [← Quotient.out_eq (f i)] <;>
    exact ⟨⟨fun a => ⟨i, a⟩, fun a b h => eq_of_hEq <| by injection h⟩⟩
#align cardinal.le_sum Cardinal.le_sum

/- warning: cardinal.mk_sigma -> Cardinal.mk_sigma is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (f : ι -> Type.{u2}), Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.mk.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => f i))) (Cardinal.sum.{u1, u2} ι (fun (i : ι) => Cardinal.mk.{u2} (f i)))
but is expected to have type
  forall {ι : Type.{u2}} (f : ι -> Type.{u1}), Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u1 u2} (Cardinal.mk.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => f i))) (Cardinal.sum.{u2, u1} ι (fun (i : ι) => Cardinal.mk.{u1} (f i)))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_sigma Cardinal.mk_sigmaₓ'. -/
@[simp]
theorem mk_sigma {ι} (f : ι → Type _) : (#Σi, f i) = sum fun i => #f i :=
  mk_congr <| Equiv.sigmaCongrRight fun i => outMkEquiv.symm
#align cardinal.mk_sigma Cardinal.mk_sigma

/- warning: cardinal.sum_const -> Cardinal.sum_const is a dubious translation:
lean 3 declaration is
  forall (ι : Type.{u1}) (a : Cardinal.{u2}), Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.sum.{u1, u2} ι (fun (i : ι) => a)) (HMul.hMul.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHMul.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasMul.{max u1 u2}) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} ι)) (Cardinal.lift.{u1, u2} a))
but is expected to have type
  forall (ι : Type.{u1}) (a : Cardinal.{u2}), Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u2 u1} (Cardinal.sum.{u1, u2} ι (fun (i : ι) => a)) (HMul.hMul.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.{max u2 u1} Cardinal.{max u1 u2} (instHMul.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instMulCardinal.{max u1 u2}) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} ι)) (Cardinal.lift.{u1, u2} a))
Case conversion may be inaccurate. Consider using '#align cardinal.sum_const Cardinal.sum_constₓ'. -/
@[simp]
theorem sum_const (ι : Type u) (a : Cardinal.{v}) :
    (sum fun i : ι => a) = lift.{v} (#ι) * lift.{u} a :=
  inductionOn a fun α =>
    mk_congr <|
      calc
        (Σi : ι, Quotient.out (#α)) ≃ ι × Quotient.out (#α) := Equiv.sigmaEquivProd _ _
        _ ≃ ULift ι × ULift α := Equiv.ulift.symm.prodCongr (outMkEquiv.trans Equiv.ulift.symm)
        
#align cardinal.sum_const Cardinal.sum_const

/- warning: cardinal.sum_const' -> Cardinal.sum_const' is a dubious translation:
lean 3 declaration is
  forall (ι : Type.{u1}) (a : Cardinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.sum.{u1, u1} ι (fun (_x : ι) => a)) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) (Cardinal.mk.{u1} ι) a)
but is expected to have type
  forall (ι : Type.{u1}) (a : Cardinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.sum.{u1, u1} ι (fun (_x : ι) => a)) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (Cardinal.mk.{u1} ι) a)
Case conversion may be inaccurate. Consider using '#align cardinal.sum_const' Cardinal.sum_const'ₓ'. -/
theorem sum_const' (ι : Type u) (a : Cardinal.{u}) : (sum fun _ : ι => a) = (#ι) * a := by simp
#align cardinal.sum_const' Cardinal.sum_const'

/- warning: cardinal.sum_add_distrib -> Cardinal.sum_add_distrib is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (f : ι -> Cardinal.{u2}) (g : ι -> Cardinal.{u2}), Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.sum.{u1, u2} ι (HAdd.hAdd.{max u1 (succ u2), max u1 (succ u2), max u1 (succ u2)} (ι -> Cardinal.{u2}) (ι -> Cardinal.{u2}) (ι -> Cardinal.{u2}) (instHAdd.{max u1 (succ u2)} (ι -> Cardinal.{u2}) (Pi.instAdd.{u1, succ u2} ι (fun (ᾰ : ι) => Cardinal.{u2}) (fun (i : ι) => Cardinal.hasAdd.{u2}))) f g)) (HAdd.hAdd.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHAdd.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasAdd.{max u1 u2}) (Cardinal.sum.{u1, u2} ι f) (Cardinal.sum.{u1, u2} ι g))
but is expected to have type
  forall {ι : Type.{u2}} (f : ι -> Cardinal.{u1}) (g : ι -> Cardinal.{u1}), Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u1 u2} (Cardinal.sum.{u2, u1} ι (HAdd.hAdd.{max (succ u1) u2, max (succ u1) u2, max (succ u1) u2} (ι -> Cardinal.{u1}) (ι -> Cardinal.{u1}) (ι -> Cardinal.{u1}) (instHAdd.{max (succ u1) u2} (ι -> Cardinal.{u1}) (Pi.instAdd.{u2, succ u1} ι (fun (ᾰ : ι) => Cardinal.{u1}) (fun (i : ι) => Cardinal.instAddCardinal.{u1}))) f g)) (HAdd.hAdd.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHAdd.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instAddCardinal.{max u1 u2}) (Cardinal.sum.{u2, u1} ι f) (Cardinal.sum.{u2, u1} ι g))
Case conversion may be inaccurate. Consider using '#align cardinal.sum_add_distrib Cardinal.sum_add_distribₓ'. -/
@[simp]
theorem sum_add_distrib {ι} (f g : ι → Cardinal) : sum (f + g) = sum f + sum g := by
  simpa only [mk_sigma, mk_sum, mk_out, lift_id] using
    mk_congr (Equiv.sigmaSumDistrib (Quotient.out ∘ f) (Quotient.out ∘ g))
#align cardinal.sum_add_distrib Cardinal.sum_add_distrib

/- warning: cardinal.sum_add_distrib' -> Cardinal.sum_add_distrib' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (f : ι -> Cardinal.{u2}) (g : ι -> Cardinal.{u2}), Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.sum.{u1, u2} ι (fun (i : ι) => HAdd.hAdd.{succ u2, succ u2, succ u2} Cardinal.{u2} Cardinal.{u2} Cardinal.{u2} (instHAdd.{succ u2} Cardinal.{u2} Cardinal.hasAdd.{u2}) (f i) (g i))) (HAdd.hAdd.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHAdd.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasAdd.{max u1 u2}) (Cardinal.sum.{u1, u2} ι f) (Cardinal.sum.{u1, u2} ι g))
but is expected to have type
  forall {ι : Type.{u2}} (f : ι -> Cardinal.{u1}) (g : ι -> Cardinal.{u1}), Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u1 u2} (Cardinal.sum.{u2, u1} ι (fun (i : ι) => HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (f i) (g i))) (HAdd.hAdd.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHAdd.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instAddCardinal.{max u1 u2}) (Cardinal.sum.{u2, u1} ι f) (Cardinal.sum.{u2, u1} ι g))
Case conversion may be inaccurate. Consider using '#align cardinal.sum_add_distrib' Cardinal.sum_add_distrib'ₓ'. -/
@[simp]
theorem sum_add_distrib' {ι} (f g : ι → Cardinal) :
    (Cardinal.sum fun i => f i + g i) = sum f + sum g :=
  sum_add_distrib f g
#align cardinal.sum_add_distrib' Cardinal.sum_add_distrib'

#print Cardinal.lift_sum /-
@[simp]
theorem lift_sum {ι : Type u} (f : ι → Cardinal.{v}) :
    Cardinal.lift.{w} (Cardinal.sum f) = Cardinal.sum fun i => Cardinal.lift.{w} (f i) :=
  Equiv.cardinal_eq <|
    Equiv.ulift.trans <|
      Equiv.sigmaCongrRight fun a =>
        Nonempty.some <| by rw [← lift_mk_eq, mk_out, mk_out, lift_lift]
#align cardinal.lift_sum Cardinal.lift_sum
-/

/- warning: cardinal.sum_le_sum -> Cardinal.sum_le_sum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (f : ι -> Cardinal.{u2}) (g : ι -> Cardinal.{u2}), (forall (i : ι), LE.le.{succ u2} Cardinal.{u2} Cardinal.hasLe.{u2} (f i) (g i)) -> (LE.le.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasLe.{max u1 u2} (Cardinal.sum.{u1, u2} ι f) (Cardinal.sum.{u1, u2} ι g))
but is expected to have type
  forall {ι : Type.{u2}} (f : ι -> Cardinal.{u1}) (g : ι -> Cardinal.{u1}), (forall (i : ι), LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (f i) (g i)) -> (LE.le.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instLECardinal.{max u1 u2} (Cardinal.sum.{u2, u1} ι f) (Cardinal.sum.{u2, u1} ι g))
Case conversion may be inaccurate. Consider using '#align cardinal.sum_le_sum Cardinal.sum_le_sumₓ'. -/
theorem sum_le_sum {ι} (f g : ι → Cardinal) (H : ∀ i, f i ≤ g i) : sum f ≤ sum g :=
  ⟨(Embedding.refl _).sigma_map fun i =>
      Classical.choice <| by have := H i <;> rwa [← Quot.out_eq (f i), ← Quot.out_eq (g i)] at this⟩
#align cardinal.sum_le_sum Cardinal.sum_le_sum

/- warning: cardinal.mk_le_mk_mul_of_mk_preimage_le -> Cardinal.mk_le_mk_mul_of_mk_preimage_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {c : Cardinal.{u1}} (f : α -> β), (forall (b : β), LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.preimage.{u1, u1} α β f (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.hasSingleton.{u1} β) b)))) c) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.mk.{u1} α) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) (Cardinal.mk.{u1} β) c))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {c : Cardinal.{u1}} (f : α -> β), (forall (b : β), LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α (Set.preimage.{u1, u1} α β f (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b)))) c) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.mk.{u1} α) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (Cardinal.mk.{u1} β) c))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_le_mk_mul_of_mk_preimage_le Cardinal.mk_le_mk_mul_of_mk_preimage_leₓ'. -/
theorem mk_le_mk_mul_of_mk_preimage_le {c : Cardinal} (f : α → β) (hf : ∀ b : β, (#f ⁻¹' {b}) ≤ c) :
    (#α) ≤ (#β) * c := by
  simpa only [← mk_congr (@Equiv.sigmaFiberEquiv α β f), mk_sigma, ← sum_const'] using
    sum_le_sum _ _ hf
#align cardinal.mk_le_mk_mul_of_mk_preimage_le Cardinal.mk_le_mk_mul_of_mk_preimage_le

/- warning: cardinal.lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le -> Cardinal.lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {c : Cardinal.{max u1 u2}} (f : α -> β), (forall (b : β), LE.le.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasLe.{max u1 u2} (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.preimage.{u1, u2} α β f (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b))))) c) -> (LE.le.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasLe.{max u1 u2} (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} α)) (HMul.hMul.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHMul.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasMul.{max u1 u2}) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} β)) c))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {c : Cardinal.{max u1 u2}} (f : α -> β), (forall (b : β), LE.le.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instLECardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α (Set.preimage.{u1, u2} α β f (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.instSingletonSet.{u2} β) b))))) c) -> (LE.le.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instLECardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} α)) (HMul.hMul.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} Cardinal.{max u2 u1} Cardinal.{max u1 u2} Cardinal.{max u2 u1} (instHMul.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} Cardinal.instMulCardinal.{max u1 u2}) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} β)) c))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le Cardinal.lift_mk_le_lift_mk_mul_of_lift_mk_preimage_leₓ'. -/
theorem lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le {α : Type u} {β : Type v} {c : Cardinal}
    (f : α → β) (hf : ∀ b : β, lift.{v} (#f ⁻¹' {b}) ≤ c) : lift.{v} (#α) ≤ lift.{u} (#β) * c :=
  (mk_le_mk_mul_of_mk_preimage_le fun x : ULift.{v} α => ULift.up.{u} (f x.1)) <|
    ULift.forall.2 fun b =>
      (mk_congr <|
            (Equiv.ulift.image _).trans
              (Equiv.trans
                (by
                  rw [Equiv.image_eq_preimage]
                  simp [Set.preimage])
                Equiv.ulift.symm)).trans_le
        (hf b)
#align cardinal.lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le Cardinal.lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le

#print Cardinal.bddAbove_range /-
/-- The range of an indexed cardinal function, whose outputs live in a higher universe than the
    inputs, is always bounded above. -/
theorem bddAbove_range {ι : Type u} (f : ι → Cardinal.{max u v}) : BddAbove (Set.range f) :=
  ⟨_, by
    rintro a ⟨i, rfl⟩
    exact le_sum f i⟩
#align cardinal.bdd_above_range Cardinal.bddAbove_range
-/

instance (a : Cardinal.{u}) : Small.{u} (Set.Iic a) :=
  by
  rw [← mk_out a]
  apply @small_of_surjective (Set a.out) (Iic (#a.out)) _ fun x => ⟨#x, mk_set_le x⟩
  rintro ⟨x, hx⟩
  simpa using le_mk_iff_exists_set.1 hx

instance (a : Cardinal.{u}) : Small.{u} (Set.Iio a) :=
  small_subset Iio_subset_Iic_self

#print Cardinal.bddAbove_iff_small /-
/-- A set of cardinals is bounded above iff it's small, i.e. it corresponds to an usual ZFC set. -/
theorem bddAbove_iff_small {s : Set Cardinal.{u}} : BddAbove s ↔ Small.{u} s :=
  ⟨fun ⟨a, ha⟩ => @small_subset _ (Iic a) s (fun x h => ha h) _,
    by
    rintro ⟨ι, ⟨e⟩⟩
    suffices (range fun x : ι => (e.symm x).1) = s
      by
      rw [← this]
      apply bddAbove_range.{u, u}
    ext x
    refine' ⟨_, fun hx => ⟨e ⟨x, hx⟩, _⟩⟩
    · rintro ⟨a, rfl⟩
      exact (e.symm a).Prop
    · simp_rw [Subtype.val_eq_coe, Equiv.symm_apply_apply]
      rfl⟩
#align cardinal.bdd_above_iff_small Cardinal.bddAbove_iff_small
-/

#print Cardinal.bddAbove_of_small /-
theorem bddAbove_of_small (s : Set Cardinal.{u}) [h : Small.{u} s] : BddAbove s :=
  bddAbove_iff_small.2 h
#align cardinal.bdd_above_of_small Cardinal.bddAbove_of_small
-/

#print Cardinal.bddAbove_image /-
theorem bddAbove_image (f : Cardinal.{u} → Cardinal.{max u v}) {s : Set Cardinal.{u}}
    (hs : BddAbove s) : BddAbove (f '' s) :=
  by
  rw [bdd_above_iff_small] at hs⊢
  exact small_lift _
#align cardinal.bdd_above_image Cardinal.bddAbove_image
-/

#print Cardinal.bddAbove_range_comp /-
theorem bddAbove_range_comp {ι : Type u} {f : ι → Cardinal.{v}} (hf : BddAbove (range f))
    (g : Cardinal.{v} → Cardinal.{max v w}) : BddAbove (range (g ∘ f)) :=
  by
  rw [range_comp]
  exact bdd_above_image g hf
#align cardinal.bdd_above_range_comp Cardinal.bddAbove_range_comp
-/

/- warning: cardinal.supr_le_sum -> Cardinal.supᵢ_le_sum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (f : ι -> Cardinal.{max u1 u2}), LE.le.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasLe.{max u1 u2} (supᵢ.{succ (max u1 u2), succ u1} Cardinal.{max u1 u2} (ConditionallyCompleteLattice.toHasSup.{succ (max u1 u2)} Cardinal.{max u1 u2} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ (max u1 u2)} Cardinal.{max u1 u2} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.conditionallyCompleteLinearOrderBot.{max u1 u2}))) ι f) (Cardinal.sum.{u1, max u1 u2} ι f)
but is expected to have type
  forall {ι : Type.{u2}} (f : ι -> Cardinal.{max u2 u1}), LE.le.{max (succ u2) (succ u1)} Cardinal.{max u2 u1} Cardinal.instLECardinal.{max u2 u1} (supᵢ.{succ (max u2 u1), succ u2} Cardinal.{max u2 u1} (ConditionallyCompleteLattice.toSupSet.{succ (max u2 u1)} Cardinal.{max u2 u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ (max u2 u1)} Cardinal.{max u2 u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ (max u2 u1)} Cardinal.{max u2 u1} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{max u2 u1}))) ι f) (Cardinal.sum.{u2, max u2 u1} ι f)
Case conversion may be inaccurate. Consider using '#align cardinal.supr_le_sum Cardinal.supᵢ_le_sumₓ'. -/
theorem supᵢ_le_sum {ι} (f : ι → Cardinal) : supᵢ f ≤ sum f :=
  csupᵢ_le' <| le_sum _
#align cardinal.supr_le_sum Cardinal.supᵢ_le_sum

/- warning: cardinal.sum_le_supr_lift -> Cardinal.sum_le_supᵢ_lift is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (f : ι -> Cardinal.{max u1 u2}), LE.le.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasLe.{max u1 u2} (Cardinal.sum.{u1, max u1 u2} ι f) (HMul.hMul.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHMul.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasMul.{max u1 u2}) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} ι)) (supᵢ.{succ (max u1 u2), succ u1} Cardinal.{max u1 u2} (ConditionallyCompleteLattice.toHasSup.{succ (max u1 u2)} Cardinal.{max u1 u2} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ (max u1 u2)} Cardinal.{max u1 u2} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.conditionallyCompleteLinearOrderBot.{max u1 u2}))) ι f))
but is expected to have type
  forall {ι : Type.{u1}} (f : ι -> Cardinal.{max u1 u2}), LE.le.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instLECardinal.{max u1 u2} (Cardinal.sum.{u1, max u1 u2} ι f) (HMul.hMul.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHMul.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instMulCardinal.{max u1 u2}) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} ι)) (supᵢ.{max (succ u1) (succ u2), succ u1} Cardinal.{max u1 u2} (ConditionallyCompleteLattice.toSupSet.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{max u1 u2}))) ι f))
Case conversion may be inaccurate. Consider using '#align cardinal.sum_le_supr_lift Cardinal.sum_le_supᵢ_liftₓ'. -/
theorem sum_le_supᵢ_lift {ι : Type u} (f : ι → Cardinal.{max u v}) : sum f ≤ (#ι).lift * supᵢ f :=
  by
  rw [← (supᵢ f).lift_id, ← lift_umax, lift_umax.{max u v, u}, ← sum_const]
  exact sum_le_sum _ _ (le_csupᵢ <| bddAbove_range.{u, v} f)
#align cardinal.sum_le_supr_lift Cardinal.sum_le_supᵢ_lift

/- warning: cardinal.sum_le_supr -> Cardinal.sum_le_supᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (f : ι -> Cardinal.{u1}), LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.sum.{u1, u1} ι f) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) (Cardinal.mk.{u1} ι) (supᵢ.{succ u1, succ u1} Cardinal.{u1} (ConditionallyCompleteLattice.toHasSup.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1}))) ι f))
but is expected to have type
  forall {ι : Type.{u1}} (f : ι -> Cardinal.{u1}), LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.sum.{u1, u1} ι f) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (Cardinal.mk.{u1} ι) (supᵢ.{succ u1, succ u1} Cardinal.{u1} (ConditionallyCompleteLattice.toSupSet.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u1}))) ι f))
Case conversion may be inaccurate. Consider using '#align cardinal.sum_le_supr Cardinal.sum_le_supᵢₓ'. -/
theorem sum_le_supᵢ {ι : Type u} (f : ι → Cardinal.{u}) : sum f ≤ (#ι) * supᵢ f :=
  by
  rw [← lift_id (#ι)]
  exact sum_le_supr_lift f
#align cardinal.sum_le_supr Cardinal.sum_le_supᵢ

/- warning: cardinal.sum_nat_eq_add_sum_succ -> Cardinal.sum_nat_eq_add_sum_succ is a dubious translation:
lean 3 declaration is
  forall (f : Nat -> Cardinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.sum.{0, u1} Nat f) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Cardinal.sum.{0, u1} Nat (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall (f : Nat -> Cardinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.sum.{0, u1} Nat f) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Cardinal.sum.{0, u1} Nat (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))
Case conversion may be inaccurate. Consider using '#align cardinal.sum_nat_eq_add_sum_succ Cardinal.sum_nat_eq_add_sum_succₓ'. -/
theorem sum_nat_eq_add_sum_succ (f : ℕ → Cardinal.{u}) :
    Cardinal.sum f = f 0 + Cardinal.sum fun i => f (i + 1) :=
  by
  refine' (Equiv.sigmaNatSucc fun i => Quotient.out (f i)).cardinal_eq.trans _
  simp only [mk_sum, mk_out, lift_id, mk_sigma]
#align cardinal.sum_nat_eq_add_sum_succ Cardinal.sum_nat_eq_add_sum_succ

/- warning: cardinal.supr_of_empty -> Cardinal.supᵢ_of_empty is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} (f : ι -> Cardinal.{u2}) [_inst_1 : IsEmpty.{u1} ι], Eq.{succ (succ u2)} Cardinal.{u2} (supᵢ.{succ u2, u1} Cardinal.{u2} (ConditionallyCompleteLattice.toHasSup.{succ u2} Cardinal.{u2} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u2} Cardinal.{u2} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u2} Cardinal.{u2} Cardinal.conditionallyCompleteLinearOrderBot.{u2}))) ι f) (OfNat.ofNat.{succ u2} Cardinal.{u2} 0 (OfNat.mk.{succ u2} Cardinal.{u2} 0 (Zero.zero.{succ u2} Cardinal.{u2} Cardinal.hasZero.{u2})))
but is expected to have type
  forall {ι : Sort.{u2}} (f : ι -> Cardinal.{u1}) [_inst_1 : IsEmpty.{u2} ι], Eq.{succ (succ u1)} Cardinal.{u1} (supᵢ.{succ u1, u2} Cardinal.{u1} (ConditionallyCompleteLattice.toSupSet.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u1}))) ι f) (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))
Case conversion may be inaccurate. Consider using '#align cardinal.supr_of_empty Cardinal.supᵢ_of_emptyₓ'. -/
/-- A variant of `csupr_of_empty` but with `0` on the RHS for convenience -/
@[simp]
protected theorem supᵢ_of_empty {ι} (f : ι → Cardinal) [IsEmpty ι] : supᵢ f = 0 :=
  csupᵢ_of_empty f
#align cardinal.supr_of_empty Cardinal.supᵢ_of_empty

#print Cardinal.lift_mk_shrink /-
@[simp]
theorem lift_mk_shrink (α : Type u) [Small.{v} α] :
    Cardinal.lift.{max u w} (#Shrink.{v} α) = Cardinal.lift.{max v w} (#α) :=
  lift_mk_eq.2 ⟨(equivShrink α).symm⟩
#align cardinal.lift_mk_shrink Cardinal.lift_mk_shrink
-/

#print Cardinal.lift_mk_shrink' /-
@[simp]
theorem lift_mk_shrink' (α : Type u) [Small.{v} α] :
    Cardinal.lift.{u} (#Shrink.{v} α) = Cardinal.lift.{v} (#α) :=
  lift_mk_shrink.{u, v, 0} α
#align cardinal.lift_mk_shrink' Cardinal.lift_mk_shrink'
-/

#print Cardinal.lift_mk_shrink'' /-
@[simp]
theorem lift_mk_shrink'' (α : Type max u v) [Small.{v} α] :
    Cardinal.lift.{u} (#Shrink.{v} α) = (#α) := by
  rw [← lift_umax', lift_mk_shrink.{max u v, v, 0} α, ← lift_umax, lift_id]
#align cardinal.lift_mk_shrink'' Cardinal.lift_mk_shrink''
-/

#print Cardinal.prod /-
/-- The indexed product of cardinals is the cardinality of the Pi type
  (dependent product). -/
def prod {ι : Type u} (f : ι → Cardinal) : Cardinal :=
  #∀ i, (f i).out
#align cardinal.prod Cardinal.prod
-/

#print Cardinal.mk_pi /-
@[simp]
theorem mk_pi {ι : Type u} (α : ι → Type v) : (#∀ i, α i) = prod fun i => #α i :=
  mk_congr <| Equiv.piCongrRight fun i => outMkEquiv.symm
#align cardinal.mk_pi Cardinal.mk_pi
-/

#print Cardinal.prod_const /-
@[simp]
theorem prod_const (ι : Type u) (a : Cardinal.{v}) :
    (prod fun i : ι => a) = (lift.{u} a^lift.{v} (#ι)) :=
  inductionOn a fun α =>
    mk_congr <| Equiv.piCongr Equiv.ulift.symm fun i => outMkEquiv.trans Equiv.ulift.symm
#align cardinal.prod_const Cardinal.prod_const
-/

#print Cardinal.prod_const' /-
theorem prod_const' (ι : Type u) (a : Cardinal.{u}) : (prod fun _ : ι => a) = (a^#ι) :=
  inductionOn a fun α => (mk_pi _).symm
#align cardinal.prod_const' Cardinal.prod_const'
-/

/- warning: cardinal.prod_le_prod -> Cardinal.prod_le_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (f : ι -> Cardinal.{u2}) (g : ι -> Cardinal.{u2}), (forall (i : ι), LE.le.{succ u2} Cardinal.{u2} Cardinal.hasLe.{u2} (f i) (g i)) -> (LE.le.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasLe.{max u1 u2} (Cardinal.prod.{u1, u2} ι f) (Cardinal.prod.{u1, u2} ι g))
but is expected to have type
  forall {ι : Type.{u2}} (f : ι -> Cardinal.{u1}) (g : ι -> Cardinal.{u1}), (forall (i : ι), LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (f i) (g i)) -> (LE.le.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} Cardinal.instLECardinal.{max u1 u2} (Cardinal.prod.{u2, u1} ι f) (Cardinal.prod.{u2, u1} ι g))
Case conversion may be inaccurate. Consider using '#align cardinal.prod_le_prod Cardinal.prod_le_prodₓ'. -/
theorem prod_le_prod {ι} (f g : ι → Cardinal) (H : ∀ i, f i ≤ g i) : prod f ≤ prod g :=
  ⟨Embedding.piCongrRight fun i =>
      Classical.choice <| by have := H i <;> rwa [← mk_out (f i), ← mk_out (g i)] at this⟩
#align cardinal.prod_le_prod Cardinal.prod_le_prod

/- warning: cardinal.prod_eq_zero -> Cardinal.prod_eq_zero is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u2}} (f : ι -> Cardinal.{u1}), Iff (Eq.{succ (succ (max u2 u1))} Cardinal.{max u2 u1} (Cardinal.prod.{u2, u1} ι f) (OfNat.ofNat.{succ (max u2 u1)} Cardinal.{max u2 u1} 0 (OfNat.mk.{succ (max u2 u1)} Cardinal.{max u2 u1} 0 (Zero.zero.{succ (max u2 u1)} Cardinal.{max u2 u1} Cardinal.hasZero.{max u2 u1})))) (Exists.{succ u2} ι (fun (i : ι) => Eq.{succ (succ u1)} Cardinal.{u1} (f i) (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))))
but is expected to have type
  forall {ι : Type.{u1}} (f : ι -> Cardinal.{u2}), Iff (Eq.{max (succ (succ u2)) (succ (succ u1))} Cardinal.{max u1 u2} (Cardinal.prod.{u1, u2} ι f) (OfNat.ofNat.{max (succ u2) (succ u1)} Cardinal.{max u1 u2} 0 (Zero.toOfNat0.{max (succ u2) (succ u1)} Cardinal.{max u1 u2} Cardinal.instZeroCardinal.{max u2 u1}))) (Exists.{succ u1} ι (fun (i : ι) => Eq.{succ (succ u2)} Cardinal.{u2} (f i) (OfNat.ofNat.{succ u2} Cardinal.{u2} 0 (Zero.toOfNat0.{succ u2} Cardinal.{u2} Cardinal.instZeroCardinal.{u2}))))
Case conversion may be inaccurate. Consider using '#align cardinal.prod_eq_zero Cardinal.prod_eq_zeroₓ'. -/
@[simp]
theorem prod_eq_zero {ι} (f : ι → Cardinal.{u}) : prod f = 0 ↔ ∃ i, f i = 0 :=
  by
  lift f to ι → Type u using fun _ => trivial
  simp only [mk_eq_zero_iff, ← mk_pi, isEmpty_pi]
#align cardinal.prod_eq_zero Cardinal.prod_eq_zero

/- warning: cardinal.prod_ne_zero -> Cardinal.prod_ne_zero is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (f : ι -> Cardinal.{u2}), Iff (Ne.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.prod.{u1, u2} ι f) (OfNat.ofNat.{succ (max u1 u2)} Cardinal.{max u1 u2} 0 (OfNat.mk.{succ (max u1 u2)} Cardinal.{max u1 u2} 0 (Zero.zero.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasZero.{max u1 u2})))) (forall (i : ι), Ne.{succ (succ u2)} Cardinal.{u2} (f i) (OfNat.ofNat.{succ u2} Cardinal.{u2} 0 (OfNat.mk.{succ u2} Cardinal.{u2} 0 (Zero.zero.{succ u2} Cardinal.{u2} Cardinal.hasZero.{u2}))))
but is expected to have type
  forall {ι : Type.{u2}} (f : ι -> Cardinal.{u1}), Iff (Ne.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u2 u1} (Cardinal.prod.{u2, u1} ι f) (OfNat.ofNat.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} 0 (Zero.toOfNat0.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} Cardinal.instZeroCardinal.{max u1 u2}))) (forall (i : ι), Ne.{succ (succ u1)} Cardinal.{u1} (f i) (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1})))
Case conversion may be inaccurate. Consider using '#align cardinal.prod_ne_zero Cardinal.prod_ne_zeroₓ'. -/
theorem prod_ne_zero {ι} (f : ι → Cardinal) : prod f ≠ 0 ↔ ∀ i, f i ≠ 0 := by simp [prod_eq_zero]
#align cardinal.prod_ne_zero Cardinal.prod_ne_zero

#print Cardinal.lift_prod /-
@[simp]
theorem lift_prod {ι : Type u} (c : ι → Cardinal.{v}) :
    lift.{w} (prod c) = prod fun i => lift.{w} (c i) :=
  by
  lift c to ι → Type v using fun _ => trivial
  simp only [← mk_pi, ← mk_ulift]
  exact mk_congr (equiv.ulift.trans <| Equiv.piCongrRight fun i => equiv.ulift.symm)
#align cardinal.lift_prod Cardinal.lift_prod
-/

#print Cardinal.prod_eq_of_fintype /-
theorem prod_eq_of_fintype {α : Type u} [Fintype α] (f : α → Cardinal.{v}) :
    prod f = Cardinal.lift.{u} (∏ i, f i) := by
  revert f
  refine' Fintype.induction_empty_option _ _ _ α
  · intro α β hβ e h f
    letI := Fintype.ofEquiv β e.symm
    rw [← e.prod_comp f, ← h]
    exact mk_congr (e.Pi_congr_left _).symm
  · intro f
    rw [Fintype.univ_pempty, Finset.prod_empty, lift_one, Cardinal.prod, mk_eq_one]
  · intro α hα h f
    rw [Cardinal.prod, mk_congr Equiv.piOptionEquivProd, mk_prod, lift_umax', mk_out, ←
      Cardinal.prod, lift_prod, Fintype.prod_option, lift_mul, ← h fun a => f (some a)]
    simp only [lift_id]
#align cardinal.prod_eq_of_fintype Cardinal.prod_eq_of_fintype
-/

/- warning: cardinal.lift_Inf -> Cardinal.lift_infₛ is a dubious translation:
lean 3 declaration is
  forall (s : Set.{succ u1} Cardinal.{u1}), Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (InfSet.infₛ.{succ u1} Cardinal.{u1} (ConditionallyCompleteLattice.toHasInf.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1}))) s)) (InfSet.infₛ.{succ (max u1 u2)} Cardinal.{max u1 u2} (ConditionallyCompleteLattice.toHasInf.{succ (max u1 u2)} Cardinal.{max u1 u2} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ (max u1 u2)} Cardinal.{max u1 u2} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.conditionallyCompleteLinearOrderBot.{max u1 u2}))) (Set.image.{succ u1, succ (max u1 u2)} Cardinal.{u1} Cardinal.{max u1 u2} Cardinal.lift.{u2, u1} s))
but is expected to have type
  forall (s : Set.{succ u2} Cardinal.{u2}), Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u2 u1} (Cardinal.lift.{u1, u2} (InfSet.infₛ.{succ u2} Cardinal.{u2} (ConditionallyCompleteLattice.toInfSet.{succ u2} Cardinal.{u2} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u2} Cardinal.{u2} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u2} Cardinal.{u2} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u2}))) s)) (InfSet.infₛ.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} (ConditionallyCompleteLattice.toInfSet.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{max u1 u2}))) (Set.image.{succ u2, max (succ u1) (succ u2)} Cardinal.{u2} Cardinal.{max u2 u1} Cardinal.lift.{u1, u2} s))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_Inf Cardinal.lift_infₛₓ'. -/
@[simp]
theorem lift_infₛ (s : Set Cardinal) : lift (infₛ s) = infₛ (lift '' s) :=
  by
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · simp
  · exact lift_monotone.map_Inf hs
#align cardinal.lift_Inf Cardinal.lift_infₛ

/- warning: cardinal.lift_infi -> Cardinal.lift_infᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} (f : ι -> Cardinal.{u2}), Eq.{succ (succ (max u2 u3))} Cardinal.{max u2 u3} (Cardinal.lift.{u3, u2} (infᵢ.{succ u2, u1} Cardinal.{u2} (ConditionallyCompleteLattice.toHasInf.{succ u2} Cardinal.{u2} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u2} Cardinal.{u2} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u2} Cardinal.{u2} Cardinal.conditionallyCompleteLinearOrderBot.{u2}))) ι f)) (infᵢ.{succ (max u2 u3), u1} Cardinal.{max u2 u3} (ConditionallyCompleteLattice.toHasInf.{succ (max u2 u3)} Cardinal.{max u2 u3} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ (max u2 u3)} Cardinal.{max u2 u3} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ (max u2 u3)} Cardinal.{max u2 u3} Cardinal.conditionallyCompleteLinearOrderBot.{max u2 u3}))) ι (fun (i : ι) => Cardinal.lift.{u3, u2} (f i)))
but is expected to have type
  forall {ι : Sort.{u1}} (f : ι -> Cardinal.{u3}), Eq.{max (succ (succ u2)) (succ (succ u3))} Cardinal.{max u3 u2} (Cardinal.lift.{u2, u3} (infᵢ.{succ u3, u1} Cardinal.{u3} (ConditionallyCompleteLattice.toInfSet.{succ u3} Cardinal.{u3} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u3} Cardinal.{u3} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u3} Cardinal.{u3} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u3}))) ι f)) (infᵢ.{max (succ u2) (succ u3), u1} Cardinal.{max u3 u2} (ConditionallyCompleteLattice.toInfSet.{max (succ u2) (succ u3)} Cardinal.{max u3 u2} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{max (succ u2) (succ u3)} Cardinal.{max u3 u2} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{max (succ u2) (succ u3)} Cardinal.{max u3 u2} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{max u2 u3}))) ι (fun (i : ι) => Cardinal.lift.{u2, u3} (f i)))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_infi Cardinal.lift_infᵢₓ'. -/
@[simp]
theorem lift_infᵢ {ι} (f : ι → Cardinal) : lift (infᵢ f) = ⨅ i, lift (f i) :=
  by
  unfold infᵢ
  convert lift_Inf (range f)
  rw [range_comp]
#align cardinal.lift_infi Cardinal.lift_infᵢ

#print Cardinal.lift_down /-
theorem lift_down {a : Cardinal.{u}} {b : Cardinal.{max u v}} : b ≤ lift a → ∃ a', lift a' = b :=
  inductionOn₂ a b fun α β => by
    rw [← lift_id (#β), ← lift_umax, ← lift_umax.{u, v}, lift_mk_le] <;>
      exact fun ⟨f⟩ =>
        ⟨#Set.range f,
          Eq.symm <|
            lift_mk_eq.2
              ⟨embedding.equiv_of_surjective (Embedding.codRestrict _ f Set.mem_range_self)
                  fun ⟨a, ⟨b, e⟩⟩ => ⟨b, Subtype.eq e⟩⟩⟩
#align cardinal.lift_down Cardinal.lift_down
-/

#print Cardinal.le_lift_iff /-
theorem le_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b ≤ lift a ↔ ∃ a', lift a' = b ∧ a' ≤ a :=
  ⟨fun h =>
    let ⟨a', e⟩ := lift_down h
    ⟨a', e, lift_le.1 <| e.symm ▸ h⟩,
    fun ⟨a', e, h⟩ => e ▸ lift_le.2 h⟩
#align cardinal.le_lift_iff Cardinal.le_lift_iff
-/

#print Cardinal.lt_lift_iff /-
theorem lt_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b < lift a ↔ ∃ a', lift a' = b ∧ a' < a :=
  ⟨fun h =>
    let ⟨a', e⟩ := lift_down h.le
    ⟨a', e, lift_lt.1 <| e.symm ▸ h⟩,
    fun ⟨a', e, h⟩ => e ▸ lift_lt.2 h⟩
#align cardinal.lt_lift_iff Cardinal.lt_lift_iff
-/

/- warning: cardinal.lift_succ -> Cardinal.lift_succ is a dubious translation:
lean 3 declaration is
  forall (a : Cardinal.{u1}), Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.succOrder.{u1} a)) (Order.succ.{succ (max u1 u2)} Cardinal.{max u1 u2} (PartialOrder.toPreorder.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.partialOrder.{max u1 u2}) Cardinal.succOrder.{max u1 u2} (Cardinal.lift.{u2, u1} a))
but is expected to have type
  forall (a : Cardinal.{u1}), Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.instSuccOrderCardinalToPreorderPartialOrder.{u1} a)) (Order.succ.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} (PartialOrder.toPreorder.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.partialOrder.{max u1 u2}) Cardinal.instSuccOrderCardinalToPreorderPartialOrder.{max u1 u2} (Cardinal.lift.{u2, u1} a))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_succ Cardinal.lift_succₓ'. -/
@[simp]
theorem lift_succ (a) : lift (succ a) = succ (lift a) :=
  le_antisymm
    (le_of_not_gt fun h => by
      rcases lt_lift_iff.1 h with ⟨b, e, h⟩
      rw [lt_succ_iff, ← lift_le, e] at h
      exact h.not_lt (lt_succ _))
    (succ_le_of_lt <| lift_lt.2 <| lt_succ a)
#align cardinal.lift_succ Cardinal.lift_succ

#print Cardinal.lift_umax_eq /-
@[simp]
theorem lift_umax_eq {a : Cardinal.{u}} {b : Cardinal.{v}} :
    lift.{max v w} a = lift.{max u w} b ↔ lift.{v} a = lift.{u} b := by
  rw [← lift_lift, ← lift_lift, lift_inj]
#align cardinal.lift_umax_eq Cardinal.lift_umax_eq
-/

/- warning: cardinal.lift_min -> Cardinal.lift_min is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (LinearOrder.min.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toLinearOrder.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1})) a b)) (LinearOrder.min.{succ (max u1 u2)} Cardinal.{max u1 u2} (ConditionallyCompleteLinearOrder.toLinearOrder.{succ (max u1 u2)} Cardinal.{max u1 u2} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.conditionallyCompleteLinearOrderBot.{max u1 u2})) (Cardinal.lift.{u2, u1} a) (Cardinal.lift.{u2, u1} b))
but is expected to have type
  forall {a : Cardinal.{u2}} {b : Cardinal.{u2}}, Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u2 u1} (Cardinal.lift.{u1, u2} (Min.min.{succ u2} Cardinal.{u2} (CanonicallyLinearOrderedAddMonoid.toMin.{succ u2} Cardinal.{u2} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u2}) a b)) (Min.min.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} (CanonicallyLinearOrderedAddMonoid.toMin.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{max u1 u2}) (Cardinal.lift.{u1, u2} a) (Cardinal.lift.{u1, u2} b))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_min Cardinal.lift_minₓ'. -/
@[simp]
theorem lift_min {a b : Cardinal} : lift (min a b) = min (lift a) (lift b) :=
  lift_monotone.map_min
#align cardinal.lift_min Cardinal.lift_min

/- warning: cardinal.lift_max -> Cardinal.lift_max is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (LinearOrder.max.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toLinearOrder.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1})) a b)) (LinearOrder.max.{succ (max u1 u2)} Cardinal.{max u1 u2} (ConditionallyCompleteLinearOrder.toLinearOrder.{succ (max u1 u2)} Cardinal.{max u1 u2} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.conditionallyCompleteLinearOrderBot.{max u1 u2})) (Cardinal.lift.{u2, u1} a) (Cardinal.lift.{u2, u1} b))
but is expected to have type
  forall {a : Cardinal.{u2}} {b : Cardinal.{u2}}, Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u2 u1} (Cardinal.lift.{u1, u2} (Max.max.{succ u2} Cardinal.{u2} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u2} Cardinal.{u2} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u2}) a b)) (Max.max.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} (CanonicallyLinearOrderedAddMonoid.toMax.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{max u1 u2}) (Cardinal.lift.{u1, u2} a) (Cardinal.lift.{u1, u2} b))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_max Cardinal.lift_maxₓ'. -/
@[simp]
theorem lift_max {a b : Cardinal} : lift (max a b) = max (lift a) (lift b) :=
  lift_monotone.map_max
#align cardinal.lift_max Cardinal.lift_max

/- warning: cardinal.lift_Sup -> Cardinal.lift_supₛ is a dubious translation:
lean 3 declaration is
  forall {s : Set.{succ u2} Cardinal.{u2}}, (BddAbove.{succ u2} Cardinal.{u2} (PartialOrder.toPreorder.{succ u2} Cardinal.{u2} Cardinal.partialOrder.{u2}) s) -> (Eq.{succ (succ (max u2 u1))} Cardinal.{max u2 u1} (Cardinal.lift.{u1, u2} (SupSet.supₛ.{succ u2} Cardinal.{u2} (ConditionallyCompleteLattice.toHasSup.{succ u2} Cardinal.{u2} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u2} Cardinal.{u2} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u2} Cardinal.{u2} Cardinal.conditionallyCompleteLinearOrderBot.{u2}))) s)) (SupSet.supₛ.{succ (max u2 u1)} Cardinal.{max u2 u1} (ConditionallyCompleteLattice.toHasSup.{succ (max u2 u1)} Cardinal.{max u2 u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ (max u2 u1)} Cardinal.{max u2 u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ (max u2 u1)} Cardinal.{max u2 u1} Cardinal.conditionallyCompleteLinearOrderBot.{max u2 u1}))) (Set.image.{succ u2, succ (max u2 u1)} Cardinal.{u2} Cardinal.{max u2 u1} Cardinal.lift.{u1, u2} s)))
but is expected to have type
  forall {s : Set.{succ u1} Cardinal.{u1}}, (BddAbove.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) s) -> (Eq.{max (succ (succ u2)) (succ (succ u1))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (SupSet.supₛ.{succ u1} Cardinal.{u1} (ConditionallyCompleteLattice.toSupSet.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u1}))) s)) (SupSet.supₛ.{max (succ u2) (succ u1)} Cardinal.{max u1 u2} (ConditionallyCompleteLattice.toSupSet.{max (succ u2) (succ u1)} Cardinal.{max u1 u2} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{max (succ u2) (succ u1)} Cardinal.{max u1 u2} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{max (succ u2) (succ u1)} Cardinal.{max u1 u2} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{max u2 u1}))) (Set.image.{succ u1, max (succ u2) (succ u1)} Cardinal.{u1} Cardinal.{max u1 u2} Cardinal.lift.{u2, u1} s)))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_Sup Cardinal.lift_supₛₓ'. -/
/-- The lift of a supremum is the supremum of the lifts. -/
theorem lift_supₛ {s : Set Cardinal} (hs : BddAbove s) : lift.{u} (supₛ s) = supₛ (lift.{u} '' s) :=
  by
  apply ((le_csupₛ_iff' (bdd_above_image _ hs)).2 fun c hc => _).antisymm (csupₛ_le' _)
  · by_contra h
    obtain ⟨d, rfl⟩ := Cardinal.lift_down (not_le.1 h).le
    simp_rw [lift_le] at h hc
    rw [csupₛ_le_iff' hs] at h
    exact h fun a ha => lift_le.1 <| hc (mem_image_of_mem _ ha)
  · rintro i ⟨j, hj, rfl⟩
    exact lift_le.2 (le_csupₛ hs hj)
#align cardinal.lift_Sup Cardinal.lift_supₛ

/- warning: cardinal.lift_supr -> Cardinal.lift_supᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u2}} {f : ι -> Cardinal.{u3}}, (BddAbove.{succ u3} Cardinal.{u3} (PartialOrder.toPreorder.{succ u3} Cardinal.{u3} Cardinal.partialOrder.{u3}) (Set.range.{succ u3, succ u2} Cardinal.{u3} ι f)) -> (Eq.{succ (succ (max u3 u1))} Cardinal.{max u3 u1} (Cardinal.lift.{u1, u3} (supᵢ.{succ u3, succ u2} Cardinal.{u3} (ConditionallyCompleteLattice.toHasSup.{succ u3} Cardinal.{u3} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u3} Cardinal.{u3} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u3} Cardinal.{u3} Cardinal.conditionallyCompleteLinearOrderBot.{u3}))) ι f)) (supᵢ.{succ (max u3 u1), succ u2} Cardinal.{max u3 u1} (ConditionallyCompleteLattice.toHasSup.{succ (max u3 u1)} Cardinal.{max u3 u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ (max u3 u1)} Cardinal.{max u3 u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ (max u3 u1)} Cardinal.{max u3 u1} Cardinal.conditionallyCompleteLinearOrderBot.{max u3 u1}))) ι (fun (i : ι) => Cardinal.lift.{u1, u3} (f i))))
but is expected to have type
  forall {ι : Type.{u2}} {f : ι -> Cardinal.{u3}}, (BddAbove.{succ u3} Cardinal.{u3} (PartialOrder.toPreorder.{succ u3} Cardinal.{u3} Cardinal.partialOrder.{u3}) (Set.range.{succ u3, succ u2} Cardinal.{u3} ι f)) -> (Eq.{max (succ (succ u1)) (succ (succ u3))} Cardinal.{max u3 u1} (Cardinal.lift.{u1, u3} (supᵢ.{succ u3, succ u2} Cardinal.{u3} (ConditionallyCompleteLattice.toSupSet.{succ u3} Cardinal.{u3} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u3} Cardinal.{u3} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u3} Cardinal.{u3} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u3}))) ι f)) (supᵢ.{max (succ u1) (succ u3), succ u2} Cardinal.{max u3 u1} (ConditionallyCompleteLattice.toSupSet.{max (succ u1) (succ u3)} Cardinal.{max u3 u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{max (succ u1) (succ u3)} Cardinal.{max u3 u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{max (succ u1) (succ u3)} Cardinal.{max u3 u1} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{max u1 u3}))) ι (fun (i : ι) => Cardinal.lift.{u1, u3} (f i))))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_supr Cardinal.lift_supᵢₓ'. -/
/-- The lift of a supremum is the supremum of the lifts. -/
theorem lift_supᵢ {ι : Type v} {f : ι → Cardinal.{w}} (hf : BddAbove (range f)) :
    lift.{u} (supᵢ f) = ⨆ i, lift.{u} (f i) := by rw [supᵢ, supᵢ, lift_Sup hf, ← range_comp]
#align cardinal.lift_supr Cardinal.lift_supᵢ

/- warning: cardinal.lift_supr_le -> Cardinal.lift_supᵢ_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u2}} {f : ι -> Cardinal.{u3}} {t : Cardinal.{max u3 u1}}, (BddAbove.{succ u3} Cardinal.{u3} (PartialOrder.toPreorder.{succ u3} Cardinal.{u3} Cardinal.partialOrder.{u3}) (Set.range.{succ u3, succ u2} Cardinal.{u3} ι f)) -> (forall (i : ι), LE.le.{succ (max u3 u1)} Cardinal.{max u3 u1} Cardinal.hasLe.{max u3 u1} (Cardinal.lift.{u1, u3} (f i)) t) -> (LE.le.{succ (max u3 u1)} Cardinal.{max u3 u1} Cardinal.hasLe.{max u3 u1} (Cardinal.lift.{u1, u3} (supᵢ.{succ u3, succ u2} Cardinal.{u3} (ConditionallyCompleteLattice.toHasSup.{succ u3} Cardinal.{u3} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u3} Cardinal.{u3} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u3} Cardinal.{u3} Cardinal.conditionallyCompleteLinearOrderBot.{u3}))) ι f)) t)
but is expected to have type
  forall {ι : Type.{u2}} {f : ι -> Cardinal.{u3}} {t : Cardinal.{max u1 u3}}, (BddAbove.{succ u3} Cardinal.{u3} (PartialOrder.toPreorder.{succ u3} Cardinal.{u3} Cardinal.partialOrder.{u3}) (Set.range.{succ u3, succ u2} Cardinal.{u3} ι f)) -> (forall (i : ι), LE.le.{max (succ u1) (succ u3)} Cardinal.{max u3 u1} Cardinal.instLECardinal.{max u1 u3} (Cardinal.lift.{u1, u3} (f i)) t) -> (LE.le.{max (succ u1) (succ u3)} Cardinal.{max u3 u1} Cardinal.instLECardinal.{max u1 u3} (Cardinal.lift.{u1, u3} (supᵢ.{succ u3, succ u2} Cardinal.{u3} (ConditionallyCompleteLattice.toSupSet.{succ u3} Cardinal.{u3} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u3} Cardinal.{u3} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u3} Cardinal.{u3} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u3}))) ι f)) t)
Case conversion may be inaccurate. Consider using '#align cardinal.lift_supr_le Cardinal.lift_supᵢ_leₓ'. -/
/-- To prove that the lift of a supremum is bounded by some cardinal `t`,
it suffices to show that the lift of each cardinal is bounded by `t`. -/
theorem lift_supᵢ_le {ι : Type v} {f : ι → Cardinal.{w}} {t : Cardinal} (hf : BddAbove (range f))
    (w : ∀ i, lift.{u} (f i) ≤ t) : lift.{u} (supᵢ f) ≤ t :=
  by
  rw [lift_supr hf]
  exact csupᵢ_le' w
#align cardinal.lift_supr_le Cardinal.lift_supᵢ_le

/- warning: cardinal.lift_supr_le_iff -> Cardinal.lift_supᵢ_le_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u2}} {f : ι -> Cardinal.{u3}}, (BddAbove.{succ u3} Cardinal.{u3} (PartialOrder.toPreorder.{succ u3} Cardinal.{u3} Cardinal.partialOrder.{u3}) (Set.range.{succ u3, succ u2} Cardinal.{u3} ι f)) -> (forall {t : Cardinal.{max u3 u1}}, Iff (LE.le.{succ (max u3 u1)} Cardinal.{max u3 u1} Cardinal.hasLe.{max u3 u1} (Cardinal.lift.{u1, u3} (supᵢ.{succ u3, succ u2} Cardinal.{u3} (ConditionallyCompleteLattice.toHasSup.{succ u3} Cardinal.{u3} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u3} Cardinal.{u3} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u3} Cardinal.{u3} Cardinal.conditionallyCompleteLinearOrderBot.{u3}))) ι f)) t) (forall (i : ι), LE.le.{succ (max u3 u1)} Cardinal.{max u3 u1} Cardinal.hasLe.{max u3 u1} (Cardinal.lift.{u1, u3} (f i)) t))
but is expected to have type
  forall {ι : Type.{u2}} {f : ι -> Cardinal.{u3}}, (BddAbove.{succ u3} Cardinal.{u3} (PartialOrder.toPreorder.{succ u3} Cardinal.{u3} Cardinal.partialOrder.{u3}) (Set.range.{succ u3, succ u2} Cardinal.{u3} ι f)) -> (forall {t : Cardinal.{max u1 u3}}, Iff (LE.le.{max (succ u1) (succ u3)} Cardinal.{max u3 u1} Cardinal.instLECardinal.{max u1 u3} (Cardinal.lift.{u1, u3} (supᵢ.{succ u3, succ u2} Cardinal.{u3} (ConditionallyCompleteLattice.toSupSet.{succ u3} Cardinal.{u3} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u3} Cardinal.{u3} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u3} Cardinal.{u3} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u3}))) ι f)) t) (forall (i : ι), LE.le.{max (succ u1) (succ u3)} Cardinal.{max u3 u1} Cardinal.instLECardinal.{max u1 u3} (Cardinal.lift.{u1, u3} (f i)) t))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_supr_le_iff Cardinal.lift_supᵢ_le_iffₓ'. -/
@[simp]
theorem lift_supᵢ_le_iff {ι : Type v} {f : ι → Cardinal.{w}} (hf : BddAbove (range f))
    {t : Cardinal} : lift.{u} (supᵢ f) ≤ t ↔ ∀ i, lift.{u} (f i) ≤ t :=
  by
  rw [lift_supr hf]
  exact csupᵢ_le_iff' (bdd_above_range_comp hf _)
#align cardinal.lift_supr_le_iff Cardinal.lift_supᵢ_le_iff

universe v' w'

/- warning: cardinal.lift_supr_le_lift_supr -> Cardinal.lift_supᵢ_le_lift_supᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u3}} {f : ι -> Cardinal.{u2}} {f' : ι' -> Cardinal.{u4}}, (BddAbove.{succ u2} Cardinal.{u2} (PartialOrder.toPreorder.{succ u2} Cardinal.{u2} Cardinal.partialOrder.{u2}) (Set.range.{succ u2, succ u1} Cardinal.{u2} ι f)) -> (BddAbove.{succ u4} Cardinal.{u4} (PartialOrder.toPreorder.{succ u4} Cardinal.{u4} Cardinal.partialOrder.{u4}) (Set.range.{succ u4, succ u3} Cardinal.{u4} ι' f')) -> (forall {g : ι -> ι'}, (forall (i : ι), LE.le.{succ (max u2 u4)} Cardinal.{max u2 u4} Cardinal.hasLe.{max u2 u4} (Cardinal.lift.{u4, u2} (f i)) (Cardinal.lift.{u2, u4} (f' (g i)))) -> (LE.le.{succ (max u2 u4)} Cardinal.{max u2 u4} Cardinal.hasLe.{max u2 u4} (Cardinal.lift.{u4, u2} (supᵢ.{succ u2, succ u1} Cardinal.{u2} (ConditionallyCompleteLattice.toHasSup.{succ u2} Cardinal.{u2} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u2} Cardinal.{u2} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u2} Cardinal.{u2} Cardinal.conditionallyCompleteLinearOrderBot.{u2}))) ι f)) (Cardinal.lift.{u2, u4} (supᵢ.{succ u4, succ u3} Cardinal.{u4} (ConditionallyCompleteLattice.toHasSup.{succ u4} Cardinal.{u4} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u4} Cardinal.{u4} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u4} Cardinal.{u4} Cardinal.conditionallyCompleteLinearOrderBot.{u4}))) ι' f'))))
but is expected to have type
  forall {ι : Type.{u1}} {ι' : Type.{u3}} {f : ι -> Cardinal.{u2}} {f' : ι' -> Cardinal.{u4}}, (BddAbove.{succ u2} Cardinal.{u2} (PartialOrder.toPreorder.{succ u2} Cardinal.{u2} Cardinal.partialOrder.{u2}) (Set.range.{succ u2, succ u1} Cardinal.{u2} ι f)) -> (BddAbove.{succ u4} Cardinal.{u4} (PartialOrder.toPreorder.{succ u4} Cardinal.{u4} Cardinal.partialOrder.{u4}) (Set.range.{succ u4, succ u3} Cardinal.{u4} ι' f')) -> (forall {g : ι -> ι'}, (forall (i : ι), LE.le.{max (succ u2) (succ u4)} Cardinal.{max u2 u4} Cardinal.instLECardinal.{max u2 u4} (Cardinal.lift.{u4, u2} (f i)) (Cardinal.lift.{u2, u4} (f' (g i)))) -> (LE.le.{max (succ u2) (succ u4)} Cardinal.{max u2 u4} Cardinal.instLECardinal.{max u2 u4} (Cardinal.lift.{u4, u2} (supᵢ.{succ u2, succ u1} Cardinal.{u2} (ConditionallyCompleteLattice.toSupSet.{succ u2} Cardinal.{u2} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u2} Cardinal.{u2} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u2} Cardinal.{u2} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u2}))) ι f)) (Cardinal.lift.{u2, u4} (supᵢ.{succ u4, succ u3} Cardinal.{u4} (ConditionallyCompleteLattice.toSupSet.{succ u4} Cardinal.{u4} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u4} Cardinal.{u4} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u4} Cardinal.{u4} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u4}))) ι' f'))))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_supr_le_lift_supr Cardinal.lift_supᵢ_le_lift_supᵢₓ'. -/
/-- To prove an inequality between the lifts to a common universe of two different supremums,
it suffices to show that the lift of each cardinal from the smaller supremum
if bounded by the lift of some cardinal from the larger supremum.
-/
theorem lift_supᵢ_le_lift_supᵢ {ι : Type v} {ι' : Type v'} {f : ι → Cardinal.{w}}
    {f' : ι' → Cardinal.{w'}} (hf : BddAbove (range f)) (hf' : BddAbove (range f')) {g : ι → ι'}
    (h : ∀ i, lift.{w'} (f i) ≤ lift.{w} (f' (g i))) : lift.{w'} (supᵢ f) ≤ lift.{w} (supᵢ f') :=
  by
  rw [lift_supr hf, lift_supr hf']
  exact csupᵢ_mono' (bdd_above_range_comp hf' _) fun i => ⟨_, h i⟩
#align cardinal.lift_supr_le_lift_supr Cardinal.lift_supᵢ_le_lift_supᵢ

/- warning: cardinal.lift_supr_le_lift_supr' -> Cardinal.lift_supᵢ_le_lift_supᵢ' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {f : ι -> Cardinal.{u1}} {f' : ι' -> Cardinal.{u2}}, (BddAbove.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) (Set.range.{succ u1, succ u1} Cardinal.{u1} ι f)) -> (BddAbove.{succ u2} Cardinal.{u2} (PartialOrder.toPreorder.{succ u2} Cardinal.{u2} Cardinal.partialOrder.{u2}) (Set.range.{succ u2, succ u2} Cardinal.{u2} ι' f')) -> (forall (g : ι -> ι'), (forall (i : ι), LE.le.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasLe.{max u1 u2} (Cardinal.lift.{u2, u1} (f i)) (Cardinal.lift.{u1, u2} (f' (g i)))) -> (LE.le.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasLe.{max u1 u2} (Cardinal.lift.{u2, u1} (supᵢ.{succ u1, succ u1} Cardinal.{u1} (ConditionallyCompleteLattice.toHasSup.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1}))) ι f)) (Cardinal.lift.{u1, u2} (supᵢ.{succ u2, succ u2} Cardinal.{u2} (ConditionallyCompleteLattice.toHasSup.{succ u2} Cardinal.{u2} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u2} Cardinal.{u2} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u2} Cardinal.{u2} Cardinal.conditionallyCompleteLinearOrderBot.{u2}))) ι' f'))))
but is expected to have type
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {f : ι -> Cardinal.{u1}} {f' : ι' -> Cardinal.{u2}}, (BddAbove.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) (Set.range.{succ u1, succ u1} Cardinal.{u1} ι f)) -> (BddAbove.{succ u2} Cardinal.{u2} (PartialOrder.toPreorder.{succ u2} Cardinal.{u2} Cardinal.partialOrder.{u2}) (Set.range.{succ u2, succ u2} Cardinal.{u2} ι' f')) -> (forall (g : ι -> ι'), (forall (i : ι), LE.le.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instLECardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (f i)) (Cardinal.lift.{u1, u2} (f' (g i)))) -> (LE.le.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instLECardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (supᵢ.{succ u1, succ u1} Cardinal.{u1} (ConditionallyCompleteLattice.toSupSet.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u1}))) ι f)) (Cardinal.lift.{u1, u2} (supᵢ.{succ u2, succ u2} Cardinal.{u2} (ConditionallyCompleteLattice.toSupSet.{succ u2} Cardinal.{u2} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u2} Cardinal.{u2} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u2} Cardinal.{u2} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u2}))) ι' f'))))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_supr_le_lift_supr' Cardinal.lift_supᵢ_le_lift_supᵢ'ₓ'. -/
/-- A variant of `lift_supr_le_lift_supr` with universes specialized via `w = v` and `w' = v'`.
This is sometimes necessary to avoid universe unification issues. -/
theorem lift_supᵢ_le_lift_supᵢ' {ι : Type v} {ι' : Type v'} {f : ι → Cardinal.{v}}
    {f' : ι' → Cardinal.{v'}} (hf : BddAbove (range f)) (hf' : BddAbove (range f')) (g : ι → ι')
    (h : ∀ i, lift.{v'} (f i) ≤ lift.{v} (f' (g i))) : lift.{v'} (supᵢ f) ≤ lift.{v} (supᵢ f') :=
  lift_supᵢ_le_lift_supᵢ hf hf' h
#align cardinal.lift_supr_le_lift_supr' Cardinal.lift_supᵢ_le_lift_supᵢ'

#print Cardinal.aleph0 /-
/-- `ℵ₀` is the smallest infinite cardinal. -/
def aleph0 : Cardinal.{u} :=
  lift (#ℕ)
#align cardinal.aleph_0 Cardinal.aleph0
-/

-- mathport name: cardinal.aleph_0
scoped notation "ℵ₀" => Cardinal.aleph0

#print Cardinal.mk_nat /-
theorem mk_nat : (#ℕ) = ℵ₀ :=
  (lift_id _).symm
#align cardinal.mk_nat Cardinal.mk_nat
-/

#print Cardinal.aleph0_ne_zero /-
theorem aleph0_ne_zero : ℵ₀ ≠ 0 :=
  mk_ne_zero _
#align cardinal.aleph_0_ne_zero Cardinal.aleph0_ne_zero
-/

#print Cardinal.aleph0_pos /-
theorem aleph0_pos : 0 < ℵ₀ :=
  pos_iff_ne_zero.2 aleph0_ne_zero
#align cardinal.aleph_0_pos Cardinal.aleph0_pos
-/

#print Cardinal.lift_aleph0 /-
@[simp]
theorem lift_aleph0 : lift ℵ₀ = ℵ₀ :=
  lift_lift _
#align cardinal.lift_aleph_0 Cardinal.lift_aleph0
-/

#print Cardinal.aleph0_le_lift /-
@[simp]
theorem aleph0_le_lift {c : Cardinal.{u}} : ℵ₀ ≤ lift.{v} c ↔ ℵ₀ ≤ c := by
  rw [← lift_aleph_0, lift_le]
#align cardinal.aleph_0_le_lift Cardinal.aleph0_le_lift
-/

#print Cardinal.lift_le_aleph0 /-
@[simp]
theorem lift_le_aleph0 {c : Cardinal.{u}} : lift.{v} c ≤ ℵ₀ ↔ c ≤ ℵ₀ := by
  rw [← lift_aleph_0, lift_le]
#align cardinal.lift_le_aleph_0 Cardinal.lift_le_aleph0
-/

/-! ### Properties about the cast from `ℕ` -/


/- warning: cardinal.mk_fin -> Cardinal.mk_fin is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{2} Cardinal.{0} (Cardinal.mk.{0} (Fin n)) ((fun (a : Type) (b : Type.{1}) [self : HasLiftT.{1, 2} a b] => self.0) Nat Cardinal.{0} (HasLiftT.mk.{1, 2} Nat Cardinal.{0} (CoeTCₓ.coe.{1, 2} Nat Cardinal.{0} (Nat.castCoe.{1} Cardinal.{0} Cardinal.hasNatCast.{0}))) n)
but is expected to have type
  forall (n : Nat), Eq.{2} Cardinal.{0} (Cardinal.mk.{0} (Fin n)) (Nat.cast.{1} Cardinal.{0} Cardinal.instNatCastCardinal.{0} n)
Case conversion may be inaccurate. Consider using '#align cardinal.mk_fin Cardinal.mk_finₓ'. -/
@[simp]
theorem mk_fin (n : ℕ) : (#Fin n) = n := by simp
#align cardinal.mk_fin Cardinal.mk_fin

/- warning: cardinal.lift_nat_cast -> Cardinal.lift_natCast is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{succ (succ (max u2 u1))} Cardinal.{max u2 u1} (Cardinal.lift.{u1, u2} ((fun (a : Type) (b : Type.{succ u2}) [self : HasLiftT.{1, succ (succ u2)} a b] => self.0) Nat Cardinal.{u2} (HasLiftT.mk.{1, succ (succ u2)} Nat Cardinal.{u2} (CoeTCₓ.coe.{1, succ (succ u2)} Nat Cardinal.{u2} (Nat.castCoe.{succ u2} Cardinal.{u2} Cardinal.hasNatCast.{u2}))) n)) ((fun (a : Type) (b : Type.{succ (max u2 u1)}) [self : HasLiftT.{1, succ (succ (max u2 u1))} a b] => self.0) Nat Cardinal.{max u2 u1} (HasLiftT.mk.{1, succ (succ (max u2 u1))} Nat Cardinal.{max u2 u1} (CoeTCₓ.coe.{1, succ (succ (max u2 u1))} Nat Cardinal.{max u2 u1} (Nat.castCoe.{succ (max u2 u1)} Cardinal.{max u2 u1} Cardinal.hasNatCast.{max u2 u1}))) n)
but is expected to have type
  forall (n : Nat), Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u2 u1} (Cardinal.lift.{u1, u2} (Nat.cast.{succ u2} Cardinal.{u2} Cardinal.instNatCastCardinal.{u2} n)) (Nat.cast.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} Cardinal.instNatCastCardinal.{max u1 u2} n)
Case conversion may be inaccurate. Consider using '#align cardinal.lift_nat_cast Cardinal.lift_natCastₓ'. -/
@[simp]
theorem lift_natCast (n : ℕ) : lift.{u} (n : Cardinal.{v}) = n := by induction n <;> simp [*]
#align cardinal.lift_nat_cast Cardinal.lift_natCast

/- warning: cardinal.lift_eq_nat_iff -> Cardinal.lift_eq_nat_iff is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {n : Nat}, Iff (Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} a) ((fun (a : Type) (b : Type.{succ (max u1 u2)}) [self : HasLiftT.{1, succ (succ (max u1 u2))} a b] => self.0) Nat Cardinal.{max u1 u2} (HasLiftT.mk.{1, succ (succ (max u1 u2))} Nat Cardinal.{max u1 u2} (CoeTCₓ.coe.{1, succ (succ (max u1 u2))} Nat Cardinal.{max u1 u2} (Nat.castCoe.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasNatCast.{max u1 u2}))) n)) (Eq.{succ (succ u1)} Cardinal.{u1} a ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n))
but is expected to have type
  forall {a : Cardinal.{u1}} {n : Nat}, Iff (Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} a) (Nat.cast.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instNatCastCardinal.{max u1 u2} n)) (Eq.{succ (succ u1)} Cardinal.{u1} a (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_eq_nat_iff Cardinal.lift_eq_nat_iffₓ'. -/
@[simp]
theorem lift_eq_nat_iff {a : Cardinal.{u}} {n : ℕ} : lift.{v} a = n ↔ a = n :=
  lift_injective.eq_iff' (lift_natCast n)
#align cardinal.lift_eq_nat_iff Cardinal.lift_eq_nat_iff

/- warning: cardinal.nat_eq_lift_iff -> Cardinal.nat_eq_lift_iff is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {a : Cardinal.{u1}}, Iff (Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} ((fun (a : Type) (b : Type.{succ (max u1 u2)}) [self : HasLiftT.{1, succ (succ (max u1 u2))} a b] => self.0) Nat Cardinal.{max u1 u2} (HasLiftT.mk.{1, succ (succ (max u1 u2))} Nat Cardinal.{max u1 u2} (CoeTCₓ.coe.{1, succ (succ (max u1 u2))} Nat Cardinal.{max u1 u2} (Nat.castCoe.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasNatCast.{max u1 u2}))) n) (Cardinal.lift.{u2, u1} a)) (Eq.{succ (succ u1)} Cardinal.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n) a)
but is expected to have type
  forall {n : Nat} {a : Cardinal.{u1}}, Iff (Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u1 u2} (Nat.cast.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.instNatCastCardinal.{max u1 u2} n) (Cardinal.lift.{u2, u1} a)) (Eq.{succ (succ u1)} Cardinal.{u1} (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n) a)
Case conversion may be inaccurate. Consider using '#align cardinal.nat_eq_lift_iff Cardinal.nat_eq_lift_iffₓ'. -/
@[simp]
theorem nat_eq_lift_iff {n : ℕ} {a : Cardinal.{u}} :
    (n : Cardinal) = lift.{v} a ↔ (n : Cardinal) = a := by rw [← lift_natCast.{v} n, lift_inj]
#align cardinal.nat_eq_lift_iff Cardinal.nat_eq_lift_iff

/- warning: cardinal.lift_mk_fin -> Cardinal.lift_mk_fin is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.lift.{u1, 0} (Cardinal.mk.{0} (Fin n))) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)
but is expected to have type
  forall (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.lift.{u1, 0} (Cardinal.mk.{0} (Fin n))) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)
Case conversion may be inaccurate. Consider using '#align cardinal.lift_mk_fin Cardinal.lift_mk_finₓ'. -/
theorem lift_mk_fin (n : ℕ) : lift (#Fin n) = n := by simp
#align cardinal.lift_mk_fin Cardinal.lift_mk_fin

/- warning: cardinal.mk_coe_finset -> Cardinal.mk_coe_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α}, Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s)) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) (Finset.card.{u1} α s))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α}, Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s))) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} (Finset.card.{u1} α s))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_coe_finset Cardinal.mk_coe_finsetₓ'. -/
theorem mk_coe_finset {α : Type u} {s : Finset α} : (#s) = ↑(Finset.card s) := by simp
#align cardinal.mk_coe_finset Cardinal.mk_coe_finset

/- warning: cardinal.mk_finset_of_fintype -> Cardinal.mk_finset_of_fintype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Finset.{u1} α)) (HPow.hPow.{succ u1, 0, succ u1} Cardinal.{u1} Nat Cardinal.{u1} (instHPow.{succ u1, 0} Cardinal.{u1} Nat (Monoid.Pow.{succ u1} Cardinal.{u1} (MonoidWithZero.toMonoid.{succ u1} Cardinal.{u1} (Semiring.toMonoidWithZero.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))))) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (OfNat.mk.{succ u1} Cardinal.{u1} 2 (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) (Fintype.card.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Finset.{u1} α)) (HPow.hPow.{succ u1, 0, succ u1} Cardinal.{u1} Nat Cardinal.{u1} (instHPow.{succ u1, 0} Cardinal.{u1} Nat (Monoid.Pow.{succ u1} Cardinal.{u1} (MonoidWithZero.toMonoid.{succ u1} Cardinal.{u1} (Semiring.toMonoidWithZero.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1}))))))) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (instOfNat.{succ u1} Cardinal.{u1} 2 Cardinal.instNatCastCardinal.{u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Fintype.card.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_finset_of_fintype Cardinal.mk_finset_of_fintypeₓ'. -/
theorem mk_finset_of_fintype [Fintype α] : (#Finset α) = 2 ^ℕ Fintype.card α := by simp
#align cardinal.mk_finset_of_fintype Cardinal.mk_finset_of_fintype

/- warning: cardinal.mk_finsupp_lift_of_fintype -> Cardinal.mk_finsupp_lift_of_fintype is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : Fintype.{u1} α] [_inst_2 : Zero.{u2} β], Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.mk.{max u1 u2} (Finsupp.{u1, u2} α β _inst_2)) (HPow.hPow.{succ (max u2 u1), 0, succ (max u2 u1)} Cardinal.{max u2 u1} Nat Cardinal.{max u2 u1} (instHPow.{succ (max u2 u1), 0} Cardinal.{max u2 u1} Nat (Monoid.Pow.{succ (max u2 u1)} Cardinal.{max u2 u1} (MonoidWithZero.toMonoid.{succ (max u2 u1)} Cardinal.{max u2 u1} (Semiring.toMonoidWithZero.{succ (max u2 u1)} Cardinal.{max u2 u1} (OrderedSemiring.toSemiring.{succ (max u2 u1)} Cardinal.{max u2 u1} (OrderedCommSemiring.toOrderedSemiring.{succ (max u2 u1)} Cardinal.{max u2 u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ (max u2 u1)} Cardinal.{max u2 u1} Cardinal.canonicallyOrderedCommSemiring.{max u2 u1}))))))) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} β)) (Fintype.card.{u1} α _inst_1))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : Fintype.{u1} α] [_inst_2 : Zero.{u2} β], Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u2 u1} (Cardinal.mk.{max u2 u1} (Finsupp.{u1, u2} α β _inst_2)) (HPow.hPow.{succ (max u1 u2), 0, succ (max u1 u2)} Cardinal.{max u1 u2} Nat Cardinal.{max u1 u2} (instHPow.{succ (max u1 u2), 0} Cardinal.{max u1 u2} Nat (Monoid.Pow.{succ (max u1 u2)} Cardinal.{max u1 u2} (MonoidWithZero.toMonoid.{succ (max u1 u2)} Cardinal.{max u1 u2} (Semiring.toMonoidWithZero.{succ (max u1 u2)} Cardinal.{max u1 u2} (OrderedSemiring.toSemiring.{succ (max u1 u2)} Cardinal.{max u1 u2} (OrderedCommSemiring.toOrderedSemiring.{succ (max u1 u2)} Cardinal.{max u1 u2} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{max u1 u2}))))))) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} β)) (Fintype.card.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_finsupp_lift_of_fintype Cardinal.mk_finsupp_lift_of_fintypeₓ'. -/
@[simp]
theorem mk_finsupp_lift_of_fintype (α : Type u) (β : Type v) [Fintype α] [Zero β] :
    (#α →₀ β) = lift.{u} (#β) ^ℕ Fintype.card α := by
  simpa using (@Finsupp.equivFunOnFinite α β _ _).cardinal_eq
#align cardinal.mk_finsupp_lift_of_fintype Cardinal.mk_finsupp_lift_of_fintype

/- warning: cardinal.mk_finsupp_of_fintype -> Cardinal.mk_finsupp_of_fintype is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u1}) [_inst_1 : Fintype.{u1} α] [_inst_2 : Zero.{u1} β], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Finsupp.{u1, u1} α β _inst_2)) (HPow.hPow.{succ u1, 0, succ u1} Cardinal.{u1} Nat Cardinal.{u1} (instHPow.{succ u1, 0} Cardinal.{u1} Nat (Monoid.Pow.{succ u1} Cardinal.{u1} (MonoidWithZero.toMonoid.{succ u1} Cardinal.{u1} (Semiring.toMonoidWithZero.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))))) (Cardinal.mk.{u1} β) (Fintype.card.{u1} α _inst_1))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u1}) [_inst_1 : Fintype.{u1} α] [_inst_2 : Zero.{u1} β], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Finsupp.{u1, u1} α β _inst_2)) (HPow.hPow.{succ u1, 0, succ u1} Cardinal.{u1} Nat Cardinal.{u1} (instHPow.{succ u1, 0} Cardinal.{u1} Nat (Monoid.Pow.{succ u1} Cardinal.{u1} (MonoidWithZero.toMonoid.{succ u1} Cardinal.{u1} (Semiring.toMonoidWithZero.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1}))))))) (Cardinal.mk.{u1} β) (Fintype.card.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_finsupp_of_fintype Cardinal.mk_finsupp_of_fintypeₓ'. -/
theorem mk_finsupp_of_fintype (α β : Type u) [Fintype α] [Zero β] :
    (#α →₀ β) = (#β) ^ℕ Fintype.card α := by simp
#align cardinal.mk_finsupp_of_fintype Cardinal.mk_finsupp_of_fintype

/- warning: cardinal.card_le_of_finset -> Cardinal.card_le_of_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} α), LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) (Finset.card.{u1} α s)) (Cardinal.mk.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} α), LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} (Finset.card.{u1} α s)) (Cardinal.mk.{u1} α)
Case conversion may be inaccurate. Consider using '#align cardinal.card_le_of_finset Cardinal.card_le_of_finsetₓ'. -/
theorem card_le_of_finset {α} (s : Finset α) : (s.card : Cardinal) ≤ (#α) :=
  @mk_coe_finset _ s ▸ mk_set_le _
#align cardinal.card_le_of_finset Cardinal.card_le_of_finset

/- warning: cardinal.nat_cast_pow -> Cardinal.natCast_pow is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat}, Eq.{succ (succ u1)} Cardinal.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) m n)) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) m) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n))
but is expected to have type
  forall {m : Nat} {n : Nat}, Eq.{succ (succ u1)} Cardinal.{u1} (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) m n)) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} m) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n))
Case conversion may be inaccurate. Consider using '#align cardinal.nat_cast_pow Cardinal.natCast_powₓ'. -/
@[simp, norm_cast]
theorem natCast_pow {m n : ℕ} : (↑(pow m n) : Cardinal) = (m^n) := by
  induction n <;> simp [pow_succ', power_add, *]
#align cardinal.nat_cast_pow Cardinal.natCast_pow

/- warning: cardinal.nat_cast_le -> Cardinal.natCast_le is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) m) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) (LE.le.{0} Nat Nat.hasLe m n)
but is expected to have type
  forall {m : Nat} {n : Nat}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} m) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (LE.le.{0} Nat instLENat m n)
Case conversion may be inaccurate. Consider using '#align cardinal.nat_cast_le Cardinal.natCast_leₓ'. -/
@[simp, norm_cast]
theorem natCast_le {m n : ℕ} : (m : Cardinal) ≤ n ↔ m ≤ n := by
  rw [← lift_mk_fin, ← lift_mk_fin, lift_le, le_def, Function.Embedding.nonempty_iff_card_le,
    Fintype.card_fin, Fintype.card_fin]
#align cardinal.nat_cast_le Cardinal.natCast_le

/- warning: cardinal.nat_cast_lt -> Cardinal.natCast_lt is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) m) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) (LT.lt.{0} Nat Nat.hasLt m n)
but is expected to have type
  forall {m : Nat} {n : Nat}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} m) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (LT.lt.{0} Nat instLTNat m n)
Case conversion may be inaccurate. Consider using '#align cardinal.nat_cast_lt Cardinal.natCast_ltₓ'. -/
@[simp, norm_cast]
theorem natCast_lt {m n : ℕ} : (m : Cardinal) < n ↔ m < n := by simp [lt_iff_le_not_le, ← not_le]
#align cardinal.nat_cast_lt Cardinal.natCast_lt

instance : CharZero Cardinal :=
  ⟨StrictMono.injective fun m n => natCast_lt.2⟩

/- warning: cardinal.nat_cast_inj -> Cardinal.natCast_inj is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) m) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) (Eq.{1} Nat m n)
but is expected to have type
  forall {m : Nat} {n : Nat}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} m) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (Eq.{1} Nat m n)
Case conversion may be inaccurate. Consider using '#align cardinal.nat_cast_inj Cardinal.natCast_injₓ'. -/
theorem natCast_inj {m n : ℕ} : (m : Cardinal) = n ↔ m = n :=
  Nat.cast_inj
#align cardinal.nat_cast_inj Cardinal.natCast_inj

/- warning: cardinal.nat_cast_injective -> Cardinal.natCast_injective is a dubious translation:
lean 3 declaration is
  Function.Injective.{1, succ (succ u1)} Nat Cardinal.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))))
but is expected to have type
  Function.Injective.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1})
Case conversion may be inaccurate. Consider using '#align cardinal.nat_cast_injective Cardinal.natCast_injectiveₓ'. -/
theorem natCast_injective : Injective (coe : ℕ → Cardinal) :=
  Nat.cast_injective
#align cardinal.nat_cast_injective Cardinal.natCast_injective

/- warning: cardinal.nat_succ -> Cardinal.nat_succ is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) (Nat.succ n)) (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.succOrder.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n))
but is expected to have type
  forall (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} (Nat.succ n)) (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.instSuccOrderCardinalToPreorderPartialOrder.{u1} (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n))
Case conversion may be inaccurate. Consider using '#align cardinal.nat_succ Cardinal.nat_succₓ'. -/
@[simp, norm_cast]
theorem nat_succ (n : ℕ) : (n.succ : Cardinal) = succ n :=
  (add_one_le_succ _).antisymm (succ_le_of_lt <| natCast_lt.2 <| Nat.lt_succ_self _)
#align cardinal.nat_succ Cardinal.nat_succ

/- warning: cardinal.succ_zero -> Cardinal.succ_zero is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Cardinal.{u1} (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.succOrder.{u1} (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))) (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (OfNat.mk.{succ u1} Cardinal.{u1} 1 (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))
but is expected to have type
  Eq.{succ (succ u1)} Cardinal.{u1} (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.instSuccOrderCardinalToPreorderPartialOrder.{u1} (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))) (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (One.toOfNat1.{succ u1} Cardinal.{u1} Cardinal.instOneCardinal.{u1}))
Case conversion may be inaccurate. Consider using '#align cardinal.succ_zero Cardinal.succ_zeroₓ'. -/
@[simp]
theorem succ_zero : succ (0 : Cardinal) = 1 := by norm_cast
#align cardinal.succ_zero Cardinal.succ_zero

/- warning: cardinal.card_le_of -> Cardinal.card_le_of is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat}, (forall (s : Finset.{u1} α), LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α s) n) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.mk.{u1} α) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n))
but is expected to have type
  forall {α : Type.{u1}} {n : Nat}, (forall (s : Finset.{u1} α), LE.le.{0} Nat instLENat (Finset.card.{u1} α s) n) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.mk.{u1} α) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n))
Case conversion may be inaccurate. Consider using '#align cardinal.card_le_of Cardinal.card_le_ofₓ'. -/
theorem card_le_of {α : Type u} {n : ℕ} (H : ∀ s : Finset α, s.card ≤ n) : (#α) ≤ n :=
  by
  refine' le_of_lt_succ (lt_of_not_ge fun hn => _)
  rw [← Cardinal.nat_succ, ← lift_mk_fin n.succ] at hn
  cases' hn with f
  refine' (H <| finset.univ.map f).not_lt _
  rw [Finset.card_map, ← Fintype.card, Fintype.card_ulift, Fintype.card_fin]
  exact n.lt_succ_self
#align cardinal.card_le_of Cardinal.card_le_of

#print Cardinal.cantor' /-
theorem cantor' (a) {b : Cardinal} (hb : 1 < b) : a < (b^a) :=
  by
  rw [← succ_le_iff, (by norm_cast : succ (1 : Cardinal) = 2)] at hb
  exact (cantor a).trans_le (power_le_power_right hb)
#align cardinal.cantor' Cardinal.cantor'
-/

#print Cardinal.one_le_iff_pos /-
theorem one_le_iff_pos {c : Cardinal} : 1 ≤ c ↔ 0 < c := by rw [← succ_zero, succ_le_iff]
#align cardinal.one_le_iff_pos Cardinal.one_le_iff_pos
-/

#print Cardinal.one_le_iff_ne_zero /-
theorem one_le_iff_ne_zero {c : Cardinal} : 1 ≤ c ↔ c ≠ 0 := by rw [one_le_iff_pos, pos_iff_ne_zero]
#align cardinal.one_le_iff_ne_zero Cardinal.one_le_iff_ne_zero
-/

/- warning: cardinal.nat_lt_aleph_0 -> Cardinal.nat_lt_aleph0 is a dubious translation:
lean 3 declaration is
  forall (n : Nat), LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n) Cardinal.aleph0.{u1}
but is expected to have type
  forall (n : Nat), LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n) Cardinal.aleph0.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.nat_lt_aleph_0 Cardinal.nat_lt_aleph0ₓ'. -/
theorem nat_lt_aleph0 (n : ℕ) : (n : Cardinal.{u}) < ℵ₀ :=
  succ_le_iff.1
    (by
      rw [← nat_succ, ← lift_mk_fin, aleph_0, lift_mk_le.{0, 0, u}]
      exact ⟨⟨coe, fun a b => Fin.ext⟩⟩)
#align cardinal.nat_lt_aleph_0 Cardinal.nat_lt_aleph0

#print Cardinal.one_lt_aleph0 /-
@[simp]
theorem one_lt_aleph0 : 1 < ℵ₀ := by simpa using nat_lt_aleph_0 1
#align cardinal.one_lt_aleph_0 Cardinal.one_lt_aleph0
-/

#print Cardinal.one_le_aleph0 /-
theorem one_le_aleph0 : 1 ≤ ℵ₀ :=
  one_lt_aleph0.le
#align cardinal.one_le_aleph_0 Cardinal.one_le_aleph0
-/

/- warning: cardinal.lt_aleph_0 -> Cardinal.lt_aleph0 is a dubious translation:
lean 3 declaration is
  forall {c : Cardinal.{u1}}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) c Cardinal.aleph0.{u1}) (Exists.{1} Nat (fun (n : Nat) => Eq.{succ (succ u1)} Cardinal.{u1} c ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)))
but is expected to have type
  forall {c : Cardinal.{u1}}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) c Cardinal.aleph0.{u1}) (Exists.{1} Nat (fun (n : Nat) => Eq.{succ (succ u1)} Cardinal.{u1} c (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)))
Case conversion may be inaccurate. Consider using '#align cardinal.lt_aleph_0 Cardinal.lt_aleph0ₓ'. -/
theorem lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ ∃ n : ℕ, c = n :=
  ⟨fun h => by
    rcases lt_lift_iff.1 h with ⟨c, rfl, h'⟩
    rcases le_mk_iff_exists_set.1 h'.1 with ⟨S, rfl⟩
    suffices S.finite by
      lift S to Finset ℕ using this
      simp
    contrapose! h'
    haveI := infinite.to_subtype h'
    exact ⟨Infinite.natEmbedding S⟩, fun ⟨n, e⟩ => e.symm ▸ nat_lt_aleph0 _⟩
#align cardinal.lt_aleph_0 Cardinal.lt_aleph0

/- warning: cardinal.aleph_0_le -> Cardinal.aleph0_le is a dubious translation:
lean 3 declaration is
  forall {c : Cardinal.{u1}}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} c) (forall (n : Nat), LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n) c)
but is expected to have type
  forall {c : Cardinal.{u1}}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} c) (forall (n : Nat), LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n) c)
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_0_le Cardinal.aleph0_leₓ'. -/
theorem aleph0_le {c : Cardinal} : ℵ₀ ≤ c ↔ ∀ n : ℕ, ↑n ≤ c :=
  ⟨fun h n => (nat_lt_aleph0 _).le.trans h, fun h =>
    le_of_not_lt fun hn => by
      rcases lt_aleph_0.1 hn with ⟨n, rfl⟩
      exact (Nat.lt_succ_self _).not_le (nat_cast_le.1 (h (n + 1)))⟩
#align cardinal.aleph_0_le Cardinal.aleph0_le

/- warning: cardinal.range_nat_cast -> Cardinal.range_natCast is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} (Set.{succ u1} Cardinal.{u1}) (Set.range.{succ u1, 1} Cardinal.{u1} Nat ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))))) (Set.Iio.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.aleph0.{u1})
but is expected to have type
  Eq.{succ (succ u1)} (Set.{succ u1} Cardinal.{u1}) (Set.range.{succ u1, 1} Cardinal.{u1} Nat (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1})) (Set.Iio.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.aleph0.{u1})
Case conversion may be inaccurate. Consider using '#align cardinal.range_nat_cast Cardinal.range_natCastₓ'. -/
@[simp]
theorem range_natCast : range (coe : ℕ → Cardinal) = Iio ℵ₀ :=
  ext fun x => by simp only [mem_Iio, mem_range, eq_comm, lt_aleph_0]
#align cardinal.range_nat_cast Cardinal.range_natCast

/- warning: cardinal.mk_eq_nat_iff -> Cardinal.mk_eq_nat_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} α) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) (Nonempty.{succ u1} (Equiv.{succ u1, 1} α (Fin n)))
but is expected to have type
  forall {α : Type.{u1}} {n : Nat}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} α) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (Nonempty.{succ u1} (Equiv.{succ u1, 1} α (Fin n)))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_eq_nat_iff Cardinal.mk_eq_nat_iffₓ'. -/
theorem mk_eq_nat_iff {α : Type u} {n : ℕ} : (#α) = n ↔ Nonempty (α ≃ Fin n) := by
  rw [← lift_mk_fin, ← lift_uzero (#α), lift_mk_eq']
#align cardinal.mk_eq_nat_iff Cardinal.mk_eq_nat_iff

#print Cardinal.lt_aleph0_iff_finite /-
theorem lt_aleph0_iff_finite {α : Type u} : (#α) < ℵ₀ ↔ Finite α := by
  simp only [lt_aleph_0, mk_eq_nat_iff, finite_iff_exists_equiv_fin]
#align cardinal.lt_aleph_0_iff_finite Cardinal.lt_aleph0_iff_finite
-/

#print Cardinal.lt_aleph0_iff_fintype /-
theorem lt_aleph0_iff_fintype {α : Type u} : (#α) < ℵ₀ ↔ Nonempty (Fintype α) :=
  lt_aleph0_iff_finite.trans (finite_iff_nonempty_fintype _)
#align cardinal.lt_aleph_0_iff_fintype Cardinal.lt_aleph0_iff_fintype
-/

#print Cardinal.lt_aleph0_of_finite /-
theorem lt_aleph0_of_finite (α : Type u) [Finite α] : (#α) < ℵ₀ :=
  lt_aleph0_iff_finite.2 ‹_›
#align cardinal.lt_aleph_0_of_finite Cardinal.lt_aleph0_of_finite
-/

#print Cardinal.lt_aleph0_iff_set_finite /-
@[simp]
theorem lt_aleph0_iff_set_finite {S : Set α} : (#S) < ℵ₀ ↔ S.Finite :=
  lt_aleph0_iff_finite.trans finite_coe_iff
#align cardinal.lt_aleph_0_iff_set_finite Cardinal.lt_aleph0_iff_set_finite
-/

alias lt_aleph_0_iff_set_finite ↔ _ _root_.set.finite.lt_aleph_0
#align set.finite.lt_aleph_0 Set.Finite.lt_aleph0

#print Cardinal.lt_aleph0_iff_subtype_finite /-
@[simp]
theorem lt_aleph0_iff_subtype_finite {p : α → Prop} : (#{ x // p x }) < ℵ₀ ↔ { x | p x }.Finite :=
  lt_aleph0_iff_set_finite
#align cardinal.lt_aleph_0_iff_subtype_finite Cardinal.lt_aleph0_iff_subtype_finite
-/

#print Cardinal.mk_le_aleph0_iff /-
theorem mk_le_aleph0_iff : (#α) ≤ ℵ₀ ↔ Countable α := by
  rw [countable_iff_nonempty_embedding, aleph_0, ← lift_uzero (#α), lift_mk_le']
#align cardinal.mk_le_aleph_0_iff Cardinal.mk_le_aleph0_iff
-/

#print Cardinal.mk_le_aleph0 /-
@[simp]
theorem mk_le_aleph0 [Countable α] : (#α) ≤ ℵ₀ :=
  mk_le_aleph0_iff.mpr ‹_›
#align cardinal.mk_le_aleph_0 Cardinal.mk_le_aleph0
-/

#print Cardinal.le_aleph0_iff_set_countable /-
@[simp]
theorem le_aleph0_iff_set_countable {s : Set α} : (#s) ≤ ℵ₀ ↔ s.Countable := by
  rw [mk_le_aleph_0_iff, countable_coe_iff]
#align cardinal.le_aleph_0_iff_set_countable Cardinal.le_aleph0_iff_set_countable
-/

alias le_aleph_0_iff_set_countable ↔ _ _root_.set.countable.le_aleph_0
#align set.countable.le_aleph_0 Set.Countable.le_aleph0

#print Cardinal.le_aleph0_iff_subtype_countable /-
@[simp]
theorem le_aleph0_iff_subtype_countable {p : α → Prop} :
    (#{ x // p x }) ≤ ℵ₀ ↔ { x | p x }.Countable :=
  le_aleph0_iff_set_countable
#align cardinal.le_aleph_0_iff_subtype_countable Cardinal.le_aleph0_iff_subtype_countable
-/

/- warning: cardinal.can_lift_cardinal_nat -> Cardinal.canLiftCardinalNat is a dubious translation:
lean 3 declaration is
  CanLift.{succ (succ u1), 1} Cardinal.{u1} Nat ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1})))) (fun (x : Cardinal.{u1}) => LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) x Cardinal.aleph0.{u1})
but is expected to have type
  CanLift.{succ (succ u1), 1} Cardinal.{u1} Nat (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1}) (fun (x : Cardinal.{u1}) => LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) x Cardinal.aleph0.{u1})
Case conversion may be inaccurate. Consider using '#align cardinal.can_lift_cardinal_nat Cardinal.canLiftCardinalNatₓ'. -/
instance canLiftCardinalNat : CanLift Cardinal ℕ coe fun x => x < ℵ₀ :=
  ⟨fun x hx =>
    let ⟨n, hn⟩ := lt_aleph0.mp hx
    ⟨n, hn.symm⟩⟩
#align cardinal.can_lift_cardinal_nat Cardinal.canLiftCardinalNat

/- warning: cardinal.add_lt_aleph_0 -> Cardinal.add_lt_aleph0 is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a Cardinal.aleph0.{u1}) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) b Cardinal.aleph0.{u1}) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) a b) Cardinal.aleph0.{u1})
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a Cardinal.aleph0.{u1}) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) b Cardinal.aleph0.{u1}) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) a b) Cardinal.aleph0.{u1})
Case conversion may be inaccurate. Consider using '#align cardinal.add_lt_aleph_0 Cardinal.add_lt_aleph0ₓ'. -/
theorem add_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a + b < ℵ₀ :=
  match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [← Nat.cast_add] <;> apply nat_lt_aleph_0
#align cardinal.add_lt_aleph_0 Cardinal.add_lt_aleph0

/- warning: cardinal.add_lt_aleph_0_iff -> Cardinal.add_lt_aleph0_iff is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) a b) Cardinal.aleph0.{u1}) (And (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a Cardinal.aleph0.{u1}) (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) b Cardinal.aleph0.{u1}))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) a b) Cardinal.aleph0.{u1}) (And (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a Cardinal.aleph0.{u1}) (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) b Cardinal.aleph0.{u1}))
Case conversion may be inaccurate. Consider using '#align cardinal.add_lt_aleph_0_iff Cardinal.add_lt_aleph0_iffₓ'. -/
theorem add_lt_aleph0_iff {a b : Cardinal} : a + b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀ :=
  ⟨fun h => ⟨(self_le_add_right _ _).trans_lt h, (self_le_add_left _ _).trans_lt h⟩, fun ⟨h1, h2⟩ =>
    add_lt_aleph0 h1 h2⟩
#align cardinal.add_lt_aleph_0_iff Cardinal.add_lt_aleph0_iff

/- warning: cardinal.aleph_0_le_add_iff -> Cardinal.aleph0_le_add_iff is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) a b)) (Or (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} a) (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} b))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) a b)) (Or (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} a) (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} b))
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_0_le_add_iff Cardinal.aleph0_le_add_iffₓ'. -/
theorem aleph0_le_add_iff {a b : Cardinal} : ℵ₀ ≤ a + b ↔ ℵ₀ ≤ a ∨ ℵ₀ ≤ b := by
  simp only [← not_lt, add_lt_aleph_0_iff, not_and_or]
#align cardinal.aleph_0_le_add_iff Cardinal.aleph0_le_add_iff

/- warning: cardinal.nsmul_lt_aleph_0_iff -> Cardinal.nsmul_lt_aleph0_iff is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {a : Cardinal.{u1}}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (SMul.smul.{0, succ u1} Nat Cardinal.{u1} (AddMonoid.SMul.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) n a) Cardinal.aleph0.{u1}) (Or (Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a Cardinal.aleph0.{u1}))
but is expected to have type
  forall {n : Nat} {a : Cardinal.{u1}}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (HSMul.hSMul.{0, succ u1, succ u1} Nat Cardinal.{u1} Cardinal.{u1} (instHSMul.{0, succ u1} Nat Cardinal.{u1} (AddMonoid.SMul.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1}))))))))) n a) Cardinal.aleph0.{u1}) (Or (Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a Cardinal.aleph0.{u1}))
Case conversion may be inaccurate. Consider using '#align cardinal.nsmul_lt_aleph_0_iff Cardinal.nsmul_lt_aleph0_iffₓ'. -/
/-- See also `cardinal.nsmul_lt_aleph_0_iff_of_ne_zero` if you already have `n ≠ 0`. -/
theorem nsmul_lt_aleph0_iff {n : ℕ} {a : Cardinal} : n • a < ℵ₀ ↔ n = 0 ∨ a < ℵ₀ :=
  by
  cases n
  · simpa using nat_lt_aleph_0 0
  simp only [Nat.succ_ne_zero, false_or_iff]
  induction' n with n ih
  · simp
  rw [succ_nsmul, add_lt_aleph_0_iff, ih, and_self_iff]
#align cardinal.nsmul_lt_aleph_0_iff Cardinal.nsmul_lt_aleph0_iff

/- warning: cardinal.nsmul_lt_aleph_0_iff_of_ne_zero -> Cardinal.nsmul_lt_aleph0_iff_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {a : Cardinal.{u1}}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (SMul.smul.{0, succ u1} Nat Cardinal.{u1} (AddMonoid.SMul.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) n a) Cardinal.aleph0.{u1}) (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a Cardinal.aleph0.{u1}))
but is expected to have type
  forall {n : Nat} {a : Cardinal.{u1}}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (HSMul.hSMul.{0, succ u1, succ u1} Nat Cardinal.{u1} Cardinal.{u1} (instHSMul.{0, succ u1} Nat Cardinal.{u1} (AddMonoid.SMul.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1}))))))))) n a) Cardinal.aleph0.{u1}) (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a Cardinal.aleph0.{u1}))
Case conversion may be inaccurate. Consider using '#align cardinal.nsmul_lt_aleph_0_iff_of_ne_zero Cardinal.nsmul_lt_aleph0_iff_of_ne_zeroₓ'. -/
/-- See also `cardinal.nsmul_lt_aleph_0_iff` for a hypothesis-free version. -/
theorem nsmul_lt_aleph0_iff_of_ne_zero {n : ℕ} {a : Cardinal} (h : n ≠ 0) : n • a < ℵ₀ ↔ a < ℵ₀ :=
  nsmul_lt_aleph0_iff.trans <| or_iff_right h
#align cardinal.nsmul_lt_aleph_0_iff_of_ne_zero Cardinal.nsmul_lt_aleph0_iff_of_ne_zero

/- warning: cardinal.mul_lt_aleph_0 -> Cardinal.mul_lt_aleph0 is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a Cardinal.aleph0.{u1}) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) b Cardinal.aleph0.{u1}) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b) Cardinal.aleph0.{u1})
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a Cardinal.aleph0.{u1}) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) b Cardinal.aleph0.{u1}) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b) Cardinal.aleph0.{u1})
Case conversion may be inaccurate. Consider using '#align cardinal.mul_lt_aleph_0 Cardinal.mul_lt_aleph0ₓ'. -/
theorem mul_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a * b < ℵ₀ :=
  match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [← Nat.cast_mul] <;> apply nat_lt_aleph_0
#align cardinal.mul_lt_aleph_0 Cardinal.mul_lt_aleph0

/- warning: cardinal.mul_lt_aleph_0_iff -> Cardinal.mul_lt_aleph0_iff is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b) Cardinal.aleph0.{u1}) (Or (Eq.{succ (succ u1)} Cardinal.{u1} a (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))) (Or (Eq.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))) (And (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a Cardinal.aleph0.{u1}) (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) b Cardinal.aleph0.{u1}))))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b) Cardinal.aleph0.{u1}) (Or (Eq.{succ (succ u1)} Cardinal.{u1} a (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))) (Or (Eq.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))) (And (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a Cardinal.aleph0.{u1}) (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) b Cardinal.aleph0.{u1}))))
Case conversion may be inaccurate. Consider using '#align cardinal.mul_lt_aleph_0_iff Cardinal.mul_lt_aleph0_iffₓ'. -/
theorem mul_lt_aleph0_iff {a b : Cardinal} : a * b < ℵ₀ ↔ a = 0 ∨ b = 0 ∨ a < ℵ₀ ∧ b < ℵ₀ :=
  by
  refine' ⟨fun h => _, _⟩
  · by_cases ha : a = 0
    · exact Or.inl ha
    right
    by_cases hb : b = 0
    · exact Or.inl hb
    right
    rw [← Ne, ← one_le_iff_ne_zero] at ha hb
    constructor
    · rw [← mul_one a]
      refine' (mul_le_mul' le_rfl hb).trans_lt h
    · rw [← one_mul b]
      refine' (mul_le_mul' ha le_rfl).trans_lt h
  rintro (rfl | rfl | ⟨ha, hb⟩) <;> simp only [*, mul_lt_aleph_0, aleph_0_pos, zero_mul, mul_zero]
#align cardinal.mul_lt_aleph_0_iff Cardinal.mul_lt_aleph0_iff

/- warning: cardinal.aleph_0_le_mul_iff -> Cardinal.aleph0_le_mul_iff is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b)) (And (Ne.{succ (succ u1)} Cardinal.{u1} a (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))) (And (Ne.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))) (Or (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} a) (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} b))))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b)) (And (Ne.{succ (succ u1)} Cardinal.{u1} a (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))) (And (Ne.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))) (Or (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} a) (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} b))))
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_0_le_mul_iff Cardinal.aleph0_le_mul_iffₓ'. -/
/-- See also `cardinal.aleph_0_le_mul_iff`. -/
theorem aleph0_le_mul_iff {a b : Cardinal} : ℵ₀ ≤ a * b ↔ a ≠ 0 ∧ b ≠ 0 ∧ (ℵ₀ ≤ a ∨ ℵ₀ ≤ b) :=
  by
  let h := (@mul_lt_aleph0_iff a b).Not
  rwa [not_lt, not_or, not_or, not_and_or, not_lt, not_lt] at h
#align cardinal.aleph_0_le_mul_iff Cardinal.aleph0_le_mul_iff

/- warning: cardinal.aleph_0_le_mul_iff' -> Cardinal.aleph0_le_mul_iff' is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b)) (Or (And (Ne.{succ (succ u1)} Cardinal.{u1} a (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))) (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} b)) (And (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} a) (Ne.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1}))))))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b)) (Or (And (Ne.{succ (succ u1)} Cardinal.{u1} a (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))) (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} b)) (And (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} a) (Ne.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1})))))
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_0_le_mul_iff' Cardinal.aleph0_le_mul_iff'ₓ'. -/
/-- See also `cardinal.aleph_0_le_mul_iff'`. -/
theorem aleph0_le_mul_iff' {a b : Cardinal.{u}} : ℵ₀ ≤ a * b ↔ a ≠ 0 ∧ ℵ₀ ≤ b ∨ ℵ₀ ≤ a ∧ b ≠ 0 :=
  by
  have : ∀ {a : Cardinal.{u}}, ℵ₀ ≤ a → a ≠ 0 := fun a => ne_bot_of_le_ne_bot aleph_0_ne_zero
  simp only [aleph_0_le_mul_iff, and_or_left, and_iff_right_of_imp this, @and_left_comm (a ≠ 0)]
  simp only [and_comm, or_comm]
#align cardinal.aleph_0_le_mul_iff' Cardinal.aleph0_le_mul_iff'

/- warning: cardinal.mul_lt_aleph_0_iff_of_ne_zero -> Cardinal.mul_lt_aleph0_iff_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (Ne.{succ (succ u1)} Cardinal.{u1} a (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))) -> (Ne.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))) -> (Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b) Cardinal.aleph0.{u1}) (And (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a Cardinal.aleph0.{u1}) (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) b Cardinal.aleph0.{u1})))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (Ne.{succ (succ u1)} Cardinal.{u1} a (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))) -> (Ne.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))) -> (Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b) Cardinal.aleph0.{u1}) (And (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a Cardinal.aleph0.{u1}) (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) b Cardinal.aleph0.{u1})))
Case conversion may be inaccurate. Consider using '#align cardinal.mul_lt_aleph_0_iff_of_ne_zero Cardinal.mul_lt_aleph0_iff_of_ne_zeroₓ'. -/
theorem mul_lt_aleph0_iff_of_ne_zero {a b : Cardinal} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀ := by simp [mul_lt_aleph_0_iff, ha, hb]
#align cardinal.mul_lt_aleph_0_iff_of_ne_zero Cardinal.mul_lt_aleph0_iff_of_ne_zero

#print Cardinal.power_lt_aleph0 /-
theorem power_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : (a^b) < ℵ₀ :=
  match a, b, lt_aleph0.1 ha, lt_aleph0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by rw [← nat_cast_pow] <;> apply nat_lt_aleph_0
#align cardinal.power_lt_aleph_0 Cardinal.power_lt_aleph0
-/

#print Cardinal.eq_one_iff_unique /-
theorem eq_one_iff_unique {α : Type _} : (#α) = 1 ↔ Subsingleton α ∧ Nonempty α :=
  calc
    (#α) = 1 ↔ (#α) ≤ 1 ∧ 1 ≤ (#α) := le_antisymm_iff
    _ ↔ Subsingleton α ∧ Nonempty α :=
      le_one_iff_subsingleton.And (one_le_iff_ne_zero.trans mk_ne_zero_iff)
    
#align cardinal.eq_one_iff_unique Cardinal.eq_one_iff_unique
-/

#print Cardinal.infinite_iff /-
theorem infinite_iff {α : Type u} : Infinite α ↔ ℵ₀ ≤ (#α) := by
  rw [← not_lt, lt_aleph_0_iff_finite, not_finite_iff_infinite]
#align cardinal.infinite_iff Cardinal.infinite_iff
-/

#print Cardinal.aleph0_le_mk /-
@[simp]
theorem aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ ≤ (#α) :=
  infinite_iff.1 ‹_›
#align cardinal.aleph_0_le_mk Cardinal.aleph0_le_mk
-/

#print Cardinal.mk_eq_aleph0 /-
@[simp]
theorem mk_eq_aleph0 (α : Type _) [Countable α] [Infinite α] : (#α) = ℵ₀ :=
  mk_le_aleph0.antisymm <| aleph0_le_mk _
#align cardinal.mk_eq_aleph_0 Cardinal.mk_eq_aleph0
-/

#print Cardinal.denumerable_iff /-
theorem denumerable_iff {α : Type u} : Nonempty (Denumerable α) ↔ (#α) = ℵ₀ :=
  ⟨fun ⟨h⟩ => mk_congr ((@Denumerable.eqv α h).trans Equiv.ulift.symm), fun h =>
    by
    cases' Quotient.exact h with f
    exact ⟨Denumerable.mk' <| f.trans Equiv.ulift⟩⟩
#align cardinal.denumerable_iff Cardinal.denumerable_iff
-/

#print Cardinal.mk_denumerable /-
@[simp]
theorem mk_denumerable (α : Type u) [Denumerable α] : (#α) = ℵ₀ :=
  denumerable_iff.1 ⟨‹_›⟩
#align cardinal.mk_denumerable Cardinal.mk_denumerable
-/

/- warning: cardinal.aleph_0_add_aleph_0 -> Cardinal.aleph0_add_aleph0 is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) Cardinal.aleph0.{u1} Cardinal.aleph0.{u1}) Cardinal.aleph0.{u1}
but is expected to have type
  Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) Cardinal.aleph0.{u1} Cardinal.aleph0.{u1}) Cardinal.aleph0.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_0_add_aleph_0 Cardinal.aleph0_add_aleph0ₓ'. -/
@[simp]
theorem aleph0_add_aleph0 : ℵ₀ + ℵ₀ = ℵ₀ :=
  mk_denumerable _
#align cardinal.aleph_0_add_aleph_0 Cardinal.aleph0_add_aleph0

/- warning: cardinal.aleph_0_mul_aleph_0 -> Cardinal.aleph0_mul_aleph0 is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) Cardinal.aleph0.{u1} Cardinal.aleph0.{u1}) Cardinal.aleph0.{u1}
but is expected to have type
  Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) Cardinal.aleph0.{u1} Cardinal.aleph0.{u1}) Cardinal.aleph0.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_0_mul_aleph_0 Cardinal.aleph0_mul_aleph0ₓ'. -/
theorem aleph0_mul_aleph0 : ℵ₀ * ℵ₀ = ℵ₀ :=
  mk_denumerable _
#align cardinal.aleph_0_mul_aleph_0 Cardinal.aleph0_mul_aleph0

/- warning: cardinal.nat_mul_aleph_0 -> Cardinal.nat_mul_aleph0 is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n) Cardinal.aleph0.{u1}) Cardinal.aleph0.{u1})
but is expected to have type
  forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n) Cardinal.aleph0.{u1}) Cardinal.aleph0.{u1})
Case conversion may be inaccurate. Consider using '#align cardinal.nat_mul_aleph_0 Cardinal.nat_mul_aleph0ₓ'. -/
@[simp]
theorem nat_mul_aleph0 {n : ℕ} (hn : n ≠ 0) : ↑n * ℵ₀ = ℵ₀ :=
  le_antisymm (lift_mk_fin n ▸ mk_le_aleph0) <|
    le_mul_of_one_le_left (zero_le _) <| by
      rwa [← Nat.cast_one, nat_cast_le, Nat.one_le_iff_ne_zero]
#align cardinal.nat_mul_aleph_0 Cardinal.nat_mul_aleph0

/- warning: cardinal.aleph_0_mul_nat -> Cardinal.aleph0_mul_nat is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) Cardinal.aleph0.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) Cardinal.aleph0.{u1})
but is expected to have type
  forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) Cardinal.aleph0.{u1} (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) Cardinal.aleph0.{u1})
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_0_mul_nat Cardinal.aleph0_mul_natₓ'. -/
@[simp]
theorem aleph0_mul_nat {n : ℕ} (hn : n ≠ 0) : ℵ₀ * n = ℵ₀ := by rw [mul_comm, nat_mul_aleph_0 hn]
#align cardinal.aleph_0_mul_nat Cardinal.aleph0_mul_nat

/- warning: cardinal.add_le_aleph_0 -> Cardinal.add_le_aleph0 is a dubious translation:
lean 3 declaration is
  forall {c₁ : Cardinal.{u1}} {c₂ : Cardinal.{u1}}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) c₁ c₂) Cardinal.aleph0.{u1}) (And (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} c₁ Cardinal.aleph0.{u1}) (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} c₂ Cardinal.aleph0.{u1}))
but is expected to have type
  forall {c₁ : Cardinal.{u1}} {c₂ : Cardinal.{u1}}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) c₁ c₂) Cardinal.aleph0.{u1}) (And (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} c₁ Cardinal.aleph0.{u1}) (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} c₂ Cardinal.aleph0.{u1}))
Case conversion may be inaccurate. Consider using '#align cardinal.add_le_aleph_0 Cardinal.add_le_aleph0ₓ'. -/
@[simp]
theorem add_le_aleph0 {c₁ c₂ : Cardinal} : c₁ + c₂ ≤ ℵ₀ ↔ c₁ ≤ ℵ₀ ∧ c₂ ≤ ℵ₀ :=
  ⟨fun h => ⟨le_self_add.trans h, le_add_self.trans h⟩, fun h =>
    aleph0_add_aleph0 ▸ add_le_add h.1 h.2⟩
#align cardinal.add_le_aleph_0 Cardinal.add_le_aleph0

/- warning: cardinal.aleph_0_add_nat -> Cardinal.aleph0_add_nat is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) Cardinal.aleph0.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) Cardinal.aleph0.{u1}
but is expected to have type
  forall (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) Cardinal.aleph0.{u1} (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) Cardinal.aleph0.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_0_add_nat Cardinal.aleph0_add_natₓ'. -/
@[simp]
theorem aleph0_add_nat (n : ℕ) : ℵ₀ + n = ℵ₀ :=
  (add_le_aleph0.2 ⟨le_rfl, (nat_lt_aleph0 n).le⟩).antisymm le_self_add
#align cardinal.aleph_0_add_nat Cardinal.aleph0_add_nat

/- warning: cardinal.nat_add_aleph_0 -> Cardinal.nat_add_aleph0 is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n) Cardinal.aleph0.{u1}) Cardinal.aleph0.{u1}
but is expected to have type
  forall (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n) Cardinal.aleph0.{u1}) Cardinal.aleph0.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.nat_add_aleph_0 Cardinal.nat_add_aleph0ₓ'. -/
@[simp]
theorem nat_add_aleph0 (n : ℕ) : ↑n + ℵ₀ = ℵ₀ := by rw [add_comm, aleph_0_add_nat]
#align cardinal.nat_add_aleph_0 Cardinal.nat_add_aleph0

#print Cardinal.toNat /-
/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
  to 0. -/
def toNat : ZeroHom Cardinal ℕ :=
  ⟨fun c => if h : c < aleph0.{v} then Classical.choose (lt_aleph0.1 h) else 0,
    by
    have h : 0 < ℵ₀ := nat_lt_aleph_0 0
    rw [dif_pos h, ← Cardinal.natCast_inj, ← Classical.choose_spec (lt_aleph_0.1 h), Nat.cast_zero]⟩
#align cardinal.to_nat Cardinal.toNat
-/

/- warning: cardinal.to_nat_apply_of_lt_aleph_0 -> Cardinal.toNat_apply_of_lt_aleph0 is a dubious translation:
lean 3 declaration is
  forall {c : Cardinal.{u1}} (h : LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) c Cardinal.aleph0.{u1}), Eq.{1} Nat (coeFn.{succ (succ u1), succ (succ u1)} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) (fun (_x : ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) => Cardinal.{u1} -> Nat) (ZeroHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) Cardinal.toNat.{u1} c) (Classical.choose.{1} Nat (fun (x : Nat) => Eq.{succ (succ u1)} Cardinal.{u1} c ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) x)) (Iff.mp (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) c Cardinal.aleph0.{u1}) (Exists.{1} Nat (fun (n : Nat) => Eq.{succ (succ u1)} Cardinal.{u1} c ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n))) (Cardinal.lt_aleph0.{u1} c) h))
but is expected to have type
  forall {c : Cardinal.{u1}} (h : LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) c Cardinal.aleph0.{u1}), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) c) (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) _x) (ZeroHomClass.toFunLike.{succ u1, succ u1, 0} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (ZeroHom.zeroHomClass.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) Cardinal.toNat.{u1} c) (Classical.choose.{1} Nat (fun (x : Nat) => Eq.{succ (succ u1)} Cardinal.{u1} c (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} x)) (Iff.mp (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) c Cardinal.aleph0.{u1}) (Exists.{1} Nat (fun (n : Nat) => Eq.{succ (succ u1)} Cardinal.{u1} c (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n))) (Cardinal.lt_aleph0.{u1} c) h))
Case conversion may be inaccurate. Consider using '#align cardinal.to_nat_apply_of_lt_aleph_0 Cardinal.toNat_apply_of_lt_aleph0ₓ'. -/
theorem toNat_apply_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) :
    c.toNat = Classical.choose (lt_aleph0.1 h) :=
  dif_pos h
#align cardinal.to_nat_apply_of_lt_aleph_0 Cardinal.toNat_apply_of_lt_aleph0

#print Cardinal.toNat_apply_of_aleph0_le /-
theorem toNat_apply_of_aleph0_le {c : Cardinal} (h : ℵ₀ ≤ c) : c.toNat = 0 :=
  dif_neg h.not_lt
#align cardinal.to_nat_apply_of_aleph_0_le Cardinal.toNat_apply_of_aleph0_le
-/

/- warning: cardinal.cast_to_nat_of_lt_aleph_0 -> Cardinal.cast_toNat_of_lt_aleph0 is a dubious translation:
lean 3 declaration is
  forall {c : Cardinal.{u1}}, (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) c Cardinal.aleph0.{u1}) -> (Eq.{succ (succ u1)} Cardinal.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) (coeFn.{succ (succ u1), succ (succ u1)} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) (fun (_x : ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) => Cardinal.{u1} -> Nat) (ZeroHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) Cardinal.toNat.{u1} c)) c)
but is expected to have type
  forall {c : Cardinal.{u1}}, (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) c Cardinal.aleph0.{u1}) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) _x) (ZeroHomClass.toFunLike.{succ u1, succ u1, 0} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (ZeroHom.zeroHomClass.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) Cardinal.toNat.{u1} c)) c)
Case conversion may be inaccurate. Consider using '#align cardinal.cast_to_nat_of_lt_aleph_0 Cardinal.cast_toNat_of_lt_aleph0ₓ'. -/
theorem cast_toNat_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : ↑c.toNat = c := by
  rw [to_nat_apply_of_lt_aleph_0 h, ← Classical.choose_spec (lt_aleph_0.1 h)]
#align cardinal.cast_to_nat_of_lt_aleph_0 Cardinal.cast_toNat_of_lt_aleph0

/- warning: cardinal.cast_to_nat_of_aleph_0_le -> Cardinal.cast_toNat_of_aleph0_le is a dubious translation:
lean 3 declaration is
  forall {c : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} c) -> (Eq.{succ (succ u2)} Cardinal.{u2} ((fun (a : Type) (b : Type.{succ u2}) [self : HasLiftT.{1, succ (succ u2)} a b] => self.0) Nat Cardinal.{u2} (HasLiftT.mk.{1, succ (succ u2)} Nat Cardinal.{u2} (CoeTCₓ.coe.{1, succ (succ u2)} Nat Cardinal.{u2} (Nat.castCoe.{succ u2} Cardinal.{u2} Cardinal.hasNatCast.{u2}))) (coeFn.{succ (succ u1), succ (succ u1)} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) (fun (_x : ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) => Cardinal.{u1} -> Nat) (ZeroHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) Cardinal.toNat.{u1} c)) (OfNat.ofNat.{succ u2} Cardinal.{u2} 0 (OfNat.mk.{succ u2} Cardinal.{u2} 0 (Zero.zero.{succ u2} Cardinal.{u2} Cardinal.hasZero.{u2}))))
but is expected to have type
  forall {c : Cardinal.{u2}}, (LE.le.{succ u2} Cardinal.{u2} Cardinal.instLECardinal.{u2} Cardinal.aleph0.{u2} c) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} (FunLike.coe.{succ (succ u2), succ (succ u2), 1} (ZeroHom.{succ u2, 0} Cardinal.{u2} Nat Cardinal.instZeroCardinal.{u2} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u2} (fun (_x : Cardinal.{u2}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u2}) => Nat) _x) (ZeroHomClass.toFunLike.{succ u2, succ u2, 0} (ZeroHom.{succ u2, 0} Cardinal.{u2} Nat Cardinal.instZeroCardinal.{u2} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u2} Nat Cardinal.instZeroCardinal.{u2} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (ZeroHom.zeroHomClass.{succ u2, 0} Cardinal.{u2} Nat Cardinal.instZeroCardinal.{u2} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) Cardinal.toNat.{u2} c)) (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1})))
Case conversion may be inaccurate. Consider using '#align cardinal.cast_to_nat_of_aleph_0_le Cardinal.cast_toNat_of_aleph0_leₓ'. -/
theorem cast_toNat_of_aleph0_le {c : Cardinal} (h : ℵ₀ ≤ c) : ↑c.toNat = (0 : Cardinal) := by
  rw [to_nat_apply_of_aleph_0_le h, Nat.cast_zero]
#align cardinal.cast_to_nat_of_aleph_0_le Cardinal.cast_toNat_of_aleph0_le

#print Cardinal.toNat_le_iff_le_of_lt_aleph0 /-
theorem toNat_le_iff_le_of_lt_aleph0 {c d : Cardinal} (hc : c < ℵ₀) (hd : d < ℵ₀) :
    c.toNat ≤ d.toNat ↔ c ≤ d := by
  rw [← nat_cast_le, cast_to_nat_of_lt_aleph_0 hc, cast_to_nat_of_lt_aleph_0 hd]
#align cardinal.to_nat_le_iff_le_of_lt_aleph_0 Cardinal.toNat_le_iff_le_of_lt_aleph0
-/

#print Cardinal.toNat_lt_iff_lt_of_lt_aleph0 /-
theorem toNat_lt_iff_lt_of_lt_aleph0 {c d : Cardinal} (hc : c < ℵ₀) (hd : d < ℵ₀) :
    c.toNat < d.toNat ↔ c < d := by
  rw [← nat_cast_lt, cast_to_nat_of_lt_aleph_0 hc, cast_to_nat_of_lt_aleph_0 hd]
#align cardinal.to_nat_lt_iff_lt_of_lt_aleph_0 Cardinal.toNat_lt_iff_lt_of_lt_aleph0
-/

#print Cardinal.toNat_le_of_le_of_lt_aleph0 /-
theorem toNat_le_of_le_of_lt_aleph0 {c d : Cardinal} (hd : d < ℵ₀) (hcd : c ≤ d) :
    c.toNat ≤ d.toNat :=
  (toNat_le_iff_le_of_lt_aleph0 (hcd.trans_lt hd) hd).mpr hcd
#align cardinal.to_nat_le_of_le_of_lt_aleph_0 Cardinal.toNat_le_of_le_of_lt_aleph0
-/

#print Cardinal.toNat_lt_of_lt_of_lt_aleph0 /-
theorem toNat_lt_of_lt_of_lt_aleph0 {c d : Cardinal} (hd : d < ℵ₀) (hcd : c < d) :
    c.toNat < d.toNat :=
  (toNat_lt_iff_lt_of_lt_aleph0 (hcd.trans hd) hd).mpr hcd
#align cardinal.to_nat_lt_of_lt_of_lt_aleph_0 Cardinal.toNat_lt_of_lt_of_lt_aleph0
-/

/- warning: cardinal.to_nat_cast -> Cardinal.toNat_cast is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} Nat (coeFn.{succ (succ u1), succ (succ u1)} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) (fun (_x : ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) => Cardinal.{u1} -> Nat) (ZeroHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) Cardinal.toNat.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) n
but is expected to have type
  forall (n : Nat), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) _x) (ZeroHomClass.toFunLike.{succ u1, succ u1, 0} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (ZeroHom.zeroHomClass.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) Cardinal.toNat.{u1} (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) n
Case conversion may be inaccurate. Consider using '#align cardinal.to_nat_cast Cardinal.toNat_castₓ'. -/
@[simp]
theorem toNat_cast (n : ℕ) : Cardinal.toNat n = n :=
  by
  rw [to_nat_apply_of_lt_aleph_0 (nat_lt_aleph_0 n), ← nat_cast_inj]
  exact (Classical.choose_spec (lt_aleph_0.1 (nat_lt_aleph_0 n))).symm
#align cardinal.to_nat_cast Cardinal.toNat_cast

/- warning: cardinal.to_nat_right_inverse -> Cardinal.toNat_rightInverse is a dubious translation:
lean 3 declaration is
  Function.RightInverse.{succ (succ u1), 1} Cardinal.{u1} Nat ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1})))) (coeFn.{succ (succ u1), succ (succ u1)} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) (fun (_x : ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) => Cardinal.{u1} -> Nat) (ZeroHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) Cardinal.toNat.{u1})
but is expected to have type
  Function.RightInverse.{succ (succ u1), 1} Cardinal.{u1} Nat (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1}) (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) _x) (ZeroHomClass.toFunLike.{succ u1, succ u1, 0} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (ZeroHom.zeroHomClass.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) Cardinal.toNat.{u1})
Case conversion may be inaccurate. Consider using '#align cardinal.to_nat_right_inverse Cardinal.toNat_rightInverseₓ'. -/
/-- `to_nat` has a right-inverse: coercion. -/
theorem toNat_rightInverse : Function.RightInverse (coe : ℕ → Cardinal) toNat :=
  toNat_cast
#align cardinal.to_nat_right_inverse Cardinal.toNat_rightInverse

#print Cardinal.toNat_surjective /-
theorem toNat_surjective : Surjective toNat :=
  toNat_rightInverse.Surjective
#align cardinal.to_nat_surjective Cardinal.toNat_surjective
-/

/- warning: cardinal.exists_nat_eq_of_le_nat -> Cardinal.exists_nat_eq_of_le_nat is a dubious translation:
lean 3 declaration is
  forall {c : Cardinal.{u1}} {n : Nat}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} c ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) -> (Exists.{1} Nat (fun (m : Nat) => And (LE.le.{0} Nat Nat.hasLe m n) (Eq.{succ (succ u1)} Cardinal.{u1} c ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) m))))
but is expected to have type
  forall {c : Cardinal.{u1}} {n : Nat}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} c (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) -> (Exists.{1} Nat (fun (m : Nat) => And (LE.le.{0} Nat instLENat m n) (Eq.{succ (succ u1)} Cardinal.{u1} c (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} m))))
Case conversion may be inaccurate. Consider using '#align cardinal.exists_nat_eq_of_le_nat Cardinal.exists_nat_eq_of_le_natₓ'. -/
theorem exists_nat_eq_of_le_nat {c : Cardinal} {n : ℕ} (h : c ≤ n) : ∃ m, m ≤ n ∧ c = m :=
  let he := cast_toNat_of_lt_aleph0 (h.trans_lt <| nat_lt_aleph0 n)
  ⟨c.toNat, natCast_le.1 (he.trans_le h), he.symm⟩
#align cardinal.exists_nat_eq_of_le_nat Cardinal.exists_nat_eq_of_le_nat

#print Cardinal.mk_toNat_of_infinite /-
@[simp]
theorem mk_toNat_of_infinite [h : Infinite α] : (#α).toNat = 0 :=
  dif_neg (infinite_iff.1 h).not_lt
#align cardinal.mk_to_nat_of_infinite Cardinal.mk_toNat_of_infinite
-/

#print Cardinal.aleph0_toNat /-
@[simp]
theorem aleph0_toNat : toNat ℵ₀ = 0 :=
  toNat_apply_of_aleph0_le le_rfl
#align cardinal.aleph_0_to_nat Cardinal.aleph0_toNat
-/

#print Cardinal.mk_toNat_eq_card /-
theorem mk_toNat_eq_card [Fintype α] : (#α).toNat = Fintype.card α := by simp
#align cardinal.mk_to_nat_eq_card Cardinal.mk_toNat_eq_card
-/

#print Cardinal.zero_toNat /-
@[simp]
theorem zero_toNat : toNat 0 = 0 := by rw [← to_nat_cast 0, Nat.cast_zero]
#align cardinal.zero_to_nat Cardinal.zero_toNat
-/

#print Cardinal.one_toNat /-
@[simp]
theorem one_toNat : toNat 1 = 1 := by rw [← to_nat_cast 1, Nat.cast_one]
#align cardinal.one_to_nat Cardinal.one_toNat
-/

/- warning: cardinal.to_nat_eq_iff -> Cardinal.toNat_eq_iff is a dubious translation:
lean 3 declaration is
  forall {c : Cardinal.{u1}} {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Iff (Eq.{1} Nat (coeFn.{succ (succ u1), succ (succ u1)} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) (fun (_x : ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) => Cardinal.{u1} -> Nat) (ZeroHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) Cardinal.toNat.{u1} c) n) (Eq.{succ (succ u1)} Cardinal.{u1} c ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)))
but is expected to have type
  forall {c : Cardinal.{u1}} {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Iff (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) c) (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) _x) (ZeroHomClass.toFunLike.{succ u1, succ u1, 0} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (ZeroHom.zeroHomClass.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) Cardinal.toNat.{u1} c) n) (Eq.{succ (succ u1)} Cardinal.{u1} c (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)))
Case conversion may be inaccurate. Consider using '#align cardinal.to_nat_eq_iff Cardinal.toNat_eq_iffₓ'. -/
theorem toNat_eq_iff {c : Cardinal} {n : ℕ} (hn : n ≠ 0) : toNat c = n ↔ c = n :=
  ⟨fun h =>
    (cast_toNat_of_lt_aleph0
            (lt_of_not_ge (hn ∘ h.symm.trans ∘ toNat_apply_of_aleph0_le))).symm.trans
      (congr_arg coe h),
    fun h => (congr_arg toNat h).trans (toNat_cast n)⟩
#align cardinal.to_nat_eq_iff Cardinal.toNat_eq_iff

#print Cardinal.toNat_eq_one /-
@[simp]
theorem toNat_eq_one {c : Cardinal} : toNat c = 1 ↔ c = 1 := by
  rw [to_nat_eq_iff one_ne_zero, Nat.cast_one]
#align cardinal.to_nat_eq_one Cardinal.toNat_eq_one
-/

#print Cardinal.toNat_eq_one_iff_unique /-
theorem toNat_eq_one_iff_unique {α : Type _} : (#α).toNat = 1 ↔ Subsingleton α ∧ Nonempty α :=
  toNat_eq_one.trans eq_one_iff_unique
#align cardinal.to_nat_eq_one_iff_unique Cardinal.toNat_eq_one_iff_unique
-/

#print Cardinal.toNat_lift /-
@[simp]
theorem toNat_lift (c : Cardinal.{v}) : (lift.{u, v} c).toNat = c.toNat :=
  by
  apply nat_cast_injective
  cases' lt_or_ge c ℵ₀ with hc hc
  · rw [cast_to_nat_of_lt_aleph_0, ← lift_nat_cast, cast_to_nat_of_lt_aleph_0 hc]
    rwa [← lift_aleph_0, lift_lt]
  · rw [cast_to_nat_of_aleph_0_le, ← lift_nat_cast, cast_to_nat_of_aleph_0_le hc, lift_zero]
    rwa [← lift_aleph_0, lift_le]
#align cardinal.to_nat_lift Cardinal.toNat_lift
-/

#print Cardinal.toNat_congr /-
theorem toNat_congr {β : Type v} (e : α ≃ β) : (#α).toNat = (#β).toNat := by
  rw [← to_nat_lift, lift_mk_eq.mpr ⟨e⟩, to_nat_lift]
#align cardinal.to_nat_congr Cardinal.toNat_congr
-/

/- warning: cardinal.to_nat_mul -> Cardinal.toNat_mul is a dubious translation:
lean 3 declaration is
  forall (x : Cardinal.{u1}) (y : Cardinal.{u1}), Eq.{1} Nat (coeFn.{succ (succ u1), succ (succ u1)} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) (fun (_x : ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) => Cardinal.{u1} -> Nat) (ZeroHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) Cardinal.toNat.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) x y)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (coeFn.{succ (succ u1), succ (succ u1)} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) (fun (_x : ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) => Cardinal.{u1} -> Nat) (ZeroHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) Cardinal.toNat.{u1} x) (coeFn.{succ (succ u1), succ (succ u1)} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) (fun (_x : ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) => Cardinal.{u1} -> Nat) (ZeroHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) Cardinal.toNat.{u1} y))
but is expected to have type
  forall (x : Cardinal.{u1}) (y : Cardinal.{u1}), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) x y)) (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) _x) (ZeroHomClass.toFunLike.{succ u1, succ u1, 0} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (ZeroHom.zeroHomClass.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) Cardinal.toNat.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) x y)) (HMul.hMul.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) y) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) x) (instHMul.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) x) instMulNat) (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) _x) (ZeroHomClass.toFunLike.{succ u1, succ u1, 0} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (ZeroHom.zeroHomClass.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) Cardinal.toNat.{u1} x) (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) _x) (ZeroHomClass.toFunLike.{succ u1, succ u1, 0} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (ZeroHom.zeroHomClass.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) Cardinal.toNat.{u1} y))
Case conversion may be inaccurate. Consider using '#align cardinal.to_nat_mul Cardinal.toNat_mulₓ'. -/
@[simp]
theorem toNat_mul (x y : Cardinal) : (x * y).toNat = x.toNat * y.toNat :=
  by
  rcases eq_or_ne x 0 with (rfl | hx1)
  · rw [zero_mul, zero_to_nat, zero_mul]
  rcases eq_or_ne y 0 with (rfl | hy1)
  · rw [mul_zero, zero_to_nat, mul_zero]
  cases' lt_or_le x ℵ₀ with hx2 hx2
  · cases' lt_or_le y ℵ₀ with hy2 hy2
    · lift x to ℕ using hx2
      lift y to ℕ using hy2
      rw [← Nat.cast_mul, to_nat_cast, to_nat_cast, to_nat_cast]
    · rw [to_nat_apply_of_aleph_0_le hy2, mul_zero, to_nat_apply_of_aleph_0_le]
      exact aleph_0_le_mul_iff'.2 (Or.inl ⟨hx1, hy2⟩)
  · rw [to_nat_apply_of_aleph_0_le hx2, zero_mul, to_nat_apply_of_aleph_0_le]
    exact aleph_0_le_mul_iff'.2 (Or.inr ⟨hx2, hy1⟩)
#align cardinal.to_nat_mul Cardinal.toNat_mul

/- warning: cardinal.to_nat_hom -> Cardinal.toNatHom is a dubious translation:
lean 3 declaration is
  MonoidWithZeroHom.{succ u1, 0} Cardinal.{u1} Nat (NonAssocSemiring.toMulZeroOneClass.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))) (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))
but is expected to have type
  MonoidWithZeroHom.{succ u1, 0} Cardinal.{u1} Nat (NonAssocSemiring.toMulZeroOneClass.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1}))))) (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))
Case conversion may be inaccurate. Consider using '#align cardinal.to_nat_hom Cardinal.toNatHomₓ'. -/
/-- `cardinal.to_nat` as a `monoid_with_zero_hom`. -/
@[simps]
def toNatHom : Cardinal →*₀ ℕ where
  toFun := toNat
  map_zero' := zero_toNat
  map_one' := one_toNat
  map_mul' := toNat_mul
#align cardinal.to_nat_hom Cardinal.toNatHom

/- warning: cardinal.to_nat_finset_prod -> Cardinal.toNat_finset_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} α) (f : α -> Cardinal.{u2}), Eq.{1} Nat (coeFn.{succ (succ u2), succ (succ u2)} (ZeroHom.{succ u2, 0} Cardinal.{u2} Nat Cardinal.hasZero.{u2} Nat.hasZero) (fun (_x : ZeroHom.{succ u2, 0} Cardinal.{u2} Nat Cardinal.hasZero.{u2} Nat.hasZero) => Cardinal.{u2} -> Nat) (ZeroHom.hasCoeToFun.{succ u2, 0} Cardinal.{u2} Nat Cardinal.hasZero.{u2} Nat.hasZero) Cardinal.toNat.{u2} (Finset.prod.{succ u2, u1} Cardinal.{u2} α (CommSemiring.toCommMonoid.{succ u2} Cardinal.{u2} Cardinal.commSemiring.{u2}) s (fun (i : α) => f i))) (Finset.prod.{0, u1} Nat α Nat.commMonoid s (fun (i : α) => coeFn.{succ (succ u2), succ (succ u2)} (ZeroHom.{succ u2, 0} Cardinal.{u2} Nat Cardinal.hasZero.{u2} Nat.hasZero) (fun (_x : ZeroHom.{succ u2, 0} Cardinal.{u2} Nat Cardinal.hasZero.{u2} Nat.hasZero) => Cardinal.{u2} -> Nat) (ZeroHom.hasCoeToFun.{succ u2, 0} Cardinal.{u2} Nat Cardinal.hasZero.{u2} Nat.hasZero) Cardinal.toNat.{u2} (f i)))
but is expected to have type
  forall {α : Type.{u2}} (s : Finset.{u2} α) (f : α -> Cardinal.{u1}), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) (Finset.prod.{succ u1, u2} Cardinal.{u1} α (CommSemiring.toCommMonoid.{succ u1} Cardinal.{u1} Cardinal.commSemiring.{u1}) s (fun (i : α) => f i))) (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) _x) (ZeroHomClass.toFunLike.{succ u1, succ u1, 0} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (ZeroHom.zeroHomClass.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) Cardinal.toNat.{u1} (Finset.prod.{succ u1, u2} Cardinal.{u1} α (CommSemiring.toCommMonoid.{succ u1} Cardinal.{u1} Cardinal.commSemiring.{u1}) s (fun (i : α) => f i))) (Finset.prod.{0, u2} Nat α Nat.commMonoid s (fun (i : α) => FunLike.coe.{succ (succ u1), succ (succ u1), 1} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) _x) (ZeroHomClass.toFunLike.{succ u1, succ u1, 0} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (ZeroHom.zeroHomClass.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) Cardinal.toNat.{u1} (f i)))
Case conversion may be inaccurate. Consider using '#align cardinal.to_nat_finset_prod Cardinal.toNat_finset_prodₓ'. -/
theorem toNat_finset_prod (s : Finset α) (f : α → Cardinal) :
    toNat (∏ i in s, f i) = ∏ i in s, toNat (f i) :=
  map_prod toNatHom _ _
#align cardinal.to_nat_finset_prod Cardinal.toNat_finset_prod

/- warning: cardinal.to_nat_add_of_lt_aleph_0 -> Cardinal.toNat_add_of_lt_aleph0 is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u2}}, (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a Cardinal.aleph0.{u1}) -> (LT.lt.{succ u2} Cardinal.{u2} (Preorder.toLT.{succ u2} Cardinal.{u2} (PartialOrder.toPreorder.{succ u2} Cardinal.{u2} Cardinal.partialOrder.{u2})) b Cardinal.aleph0.{u2}) -> (Eq.{1} Nat (coeFn.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} (ZeroHom.{succ (max u1 u2), 0} Cardinal.{max u1 u2} Nat Cardinal.hasZero.{max u1 u2} Nat.hasZero) (fun (_x : ZeroHom.{succ (max u1 u2), 0} Cardinal.{max u1 u2} Nat Cardinal.hasZero.{max u1 u2} Nat.hasZero) => Cardinal.{max u1 u2} -> Nat) (ZeroHom.hasCoeToFun.{succ (max u1 u2), 0} Cardinal.{max u1 u2} Nat Cardinal.hasZero.{max u1 u2} Nat.hasZero) Cardinal.toNat.{max u1 u2} (HAdd.hAdd.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHAdd.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasAdd.{max u1 u2}) (Cardinal.lift.{u2, u1} a) (Cardinal.lift.{u1, u2} b))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (coeFn.{succ (succ u1), succ (succ u1)} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) (fun (_x : ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) => Cardinal.{u1} -> Nat) (ZeroHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) Cardinal.toNat.{u1} a) (coeFn.{succ (succ u2), succ (succ u2)} (ZeroHom.{succ u2, 0} Cardinal.{u2} Nat Cardinal.hasZero.{u2} Nat.hasZero) (fun (_x : ZeroHom.{succ u2, 0} Cardinal.{u2} Nat Cardinal.hasZero.{u2} Nat.hasZero) => Cardinal.{u2} -> Nat) (ZeroHom.hasCoeToFun.{succ u2, 0} Cardinal.{u2} Nat Cardinal.hasZero.{u2} Nat.hasZero) Cardinal.toNat.{u2} b)))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u2}}, (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a Cardinal.aleph0.{u1}) -> (LT.lt.{succ u2} Cardinal.{u2} (Preorder.toLT.{succ u2} Cardinal.{u2} (PartialOrder.toPreorder.{succ u2} Cardinal.{u2} Cardinal.partialOrder.{u2})) b Cardinal.aleph0.{u2}) -> (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{max u1 u2}) => Nat) (HAdd.hAdd.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.{max u2 u1} Cardinal.{max u1 u2} (instHAdd.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instAddCardinal.{max u1 u2}) (Cardinal.lift.{u2, u1} a) (Cardinal.lift.{u1, u2} b))) (FunLike.coe.{succ (succ (max u1 u2)), succ (succ (max u1 u2)), 1} (ZeroHom.{succ (max u1 u2), 0} Cardinal.{max u1 u2} Nat Cardinal.instZeroCardinal.{max u1 u2} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{max u1 u2} (fun (_x : Cardinal.{max u1 u2}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{max u1 u2}) => Nat) _x) (ZeroHomClass.toFunLike.{succ (max u1 u2), succ (max u1 u2), 0} (ZeroHom.{succ (max u1 u2), 0} Cardinal.{max u1 u2} Nat Cardinal.instZeroCardinal.{max u1 u2} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{max u1 u2} Nat Cardinal.instZeroCardinal.{max u1 u2} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (ZeroHom.zeroHomClass.{succ (max u1 u2), 0} Cardinal.{max u1 u2} Nat Cardinal.instZeroCardinal.{max u1 u2} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) Cardinal.toNat.{max u1 u2} (HAdd.hAdd.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.{max u2 u1} Cardinal.{max u1 u2} (instHAdd.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instAddCardinal.{max u1 u2}) (Cardinal.lift.{u2, u1} a) (Cardinal.lift.{u1, u2} b))) (HAdd.hAdd.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) a) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u2}) => Nat) b) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) a) (instHAdd.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) a) instAddNat) (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) _x) (ZeroHomClass.toFunLike.{succ u1, succ u1, 0} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (ZeroHom.zeroHomClass.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) Cardinal.toNat.{u1} a) (FunLike.coe.{succ (succ u2), succ (succ u2), 1} (ZeroHom.{succ u2, 0} Cardinal.{u2} Nat Cardinal.instZeroCardinal.{u2} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u2} (fun (_x : Cardinal.{u2}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u2}) => Nat) _x) (ZeroHomClass.toFunLike.{succ u2, succ u2, 0} (ZeroHom.{succ u2, 0} Cardinal.{u2} Nat Cardinal.instZeroCardinal.{u2} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u2} Nat Cardinal.instZeroCardinal.{u2} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (ZeroHom.zeroHomClass.{succ u2, 0} Cardinal.{u2} Nat Cardinal.instZeroCardinal.{u2} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) Cardinal.toNat.{u2} b)))
Case conversion may be inaccurate. Consider using '#align cardinal.to_nat_add_of_lt_aleph_0 Cardinal.toNat_add_of_lt_aleph0ₓ'. -/
@[simp]
theorem toNat_add_of_lt_aleph0 {a : Cardinal.{u}} {b : Cardinal.{v}} (ha : a < ℵ₀) (hb : b < ℵ₀) :
    (lift.{v, u} a + lift.{u, v} b).toNat = a.toNat + b.toNat :=
  by
  apply Cardinal.natCast_injective
  replace ha : lift.{v, u} a < ℵ₀ := by
    rw [← lift_aleph_0]
    exact lift_lt.2 ha
  replace hb : lift.{u, v} b < ℵ₀ := by
    rw [← lift_aleph_0]
    exact lift_lt.2 hb
  rw [Nat.cast_add, ← toNat_lift.{v, u} a, ← toNat_lift.{u, v} b, cast_to_nat_of_lt_aleph_0 ha,
    cast_to_nat_of_lt_aleph_0 hb, cast_to_nat_of_lt_aleph_0 (add_lt_aleph_0 ha hb)]
#align cardinal.to_nat_add_of_lt_aleph_0 Cardinal.toNat_add_of_lt_aleph0

/- warning: cardinal.to_part_enat -> Cardinal.toPartENat is a dubious translation:
lean 3 declaration is
  AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))
but is expected to have type
  AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))
Case conversion may be inaccurate. Consider using '#align cardinal.to_part_enat Cardinal.toPartENatₓ'. -/
/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
  to `⊤`. -/
def toPartENat : Cardinal →+ PartENat
    where
  toFun c := if c < ℵ₀ then c.toNat else ⊤
  map_zero' := by simp [if_pos (zero_lt_one.trans one_lt_aleph_0)]
  map_add' x y := by
    by_cases hx : x < ℵ₀
    · obtain ⟨x0, rfl⟩ := lt_aleph_0.1 hx
      by_cases hy : y < ℵ₀
      · obtain ⟨y0, rfl⟩ := lt_aleph_0.1 hy
        simp only [add_lt_aleph_0 hx hy, hx, hy, to_nat_cast, if_true]
        rw [← Nat.cast_add, to_nat_cast, Nat.cast_add]
      · rw [if_neg hy, if_neg, PartENat.add_top]
        contrapose! hy
        apply le_add_self.trans_lt hy
    · rw [if_neg hx, if_neg, PartENat.top_add]
      contrapose! hx
      apply le_self_add.trans_lt hx
#align cardinal.to_part_enat Cardinal.toPartENat

/- warning: cardinal.to_part_enat_apply_of_lt_aleph_0 -> Cardinal.toPartENat_apply_of_lt_aleph0 is a dubious translation:
lean 3 declaration is
  forall {c : Cardinal.{u1}}, (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) c Cardinal.aleph0.{u1}) -> (Eq.{1} PartENat (coeFn.{succ (succ u1), succ (succ u1)} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) (fun (_x : AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) => Cardinal.{u1} -> PartENat) (AddMonoidHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) Cardinal.toPartENat.{u1} c) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) (coeFn.{succ (succ u1), succ (succ u1)} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) (fun (_x : ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) => Cardinal.{u1} -> Nat) (ZeroHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} Nat Cardinal.hasZero.{u1} Nat.hasZero) Cardinal.toNat.{u1} c)))
but is expected to have type
  forall {c : Cardinal.{u1}}, (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) c Cardinal.aleph0.{u1}) -> (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) c) (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) _x) (AddHomClass.toFunLike.{succ u1, succ u1, 0} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} PartENat (AddZeroClass.toAdd.{succ u1} Cardinal.{u1} (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1}))))))))) (AddZeroClass.toAdd.{0} PartENat (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) (AddMonoidHomClass.toAddHomClass.{succ u1, succ u1, 0} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat))) (AddMonoidHom.addMonoidHomClass.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))))) Cardinal.toPartENat.{u1} c) (Nat.cast.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) c) (AddMonoidWithOne.toNatCast.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) c) (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) c) PartENat.instAddCommMonoidWithOnePartENat)) (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : Cardinal.{u1}) => Nat) _x) (ZeroHomClass.toFunLike.{succ u1, succ u1, 0} (ZeroHom.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (ZeroHom.zeroHomClass.{succ u1, 0} Cardinal.{u1} Nat Cardinal.instZeroCardinal.{u1} (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) Cardinal.toNat.{u1} c)))
Case conversion may be inaccurate. Consider using '#align cardinal.to_part_enat_apply_of_lt_aleph_0 Cardinal.toPartENat_apply_of_lt_aleph0ₓ'. -/
theorem toPartENat_apply_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : c.toPartENat = c.toNat :=
  if_pos h
#align cardinal.to_part_enat_apply_of_lt_aleph_0 Cardinal.toPartENat_apply_of_lt_aleph0

/- warning: cardinal.to_part_enat_apply_of_aleph_0_le -> Cardinal.toPartENat_apply_of_aleph0_le is a dubious translation:
lean 3 declaration is
  forall {c : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} c) -> (Eq.{1} PartENat (coeFn.{succ (succ u1), succ (succ u1)} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) (fun (_x : AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) => Cardinal.{u1} -> PartENat) (AddMonoidHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) Cardinal.toPartENat.{u1} c) (Top.top.{0} PartENat PartENat.hasTop))
but is expected to have type
  forall {c : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} c) -> (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) c) (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) _x) (AddHomClass.toFunLike.{succ u1, succ u1, 0} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} PartENat (AddZeroClass.toAdd.{succ u1} Cardinal.{u1} (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1}))))))))) (AddZeroClass.toAdd.{0} PartENat (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) (AddMonoidHomClass.toAddHomClass.{succ u1, succ u1, 0} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat))) (AddMonoidHom.addMonoidHomClass.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))))) Cardinal.toPartENat.{u1} c) (Top.top.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) c) PartENat.instTopPartENat))
Case conversion may be inaccurate. Consider using '#align cardinal.to_part_enat_apply_of_aleph_0_le Cardinal.toPartENat_apply_of_aleph0_leₓ'. -/
theorem toPartENat_apply_of_aleph0_le {c : Cardinal} (h : ℵ₀ ≤ c) : c.toPartENat = ⊤ :=
  if_neg h.not_lt
#align cardinal.to_part_enat_apply_of_aleph_0_le Cardinal.toPartENat_apply_of_aleph0_le

/- warning: cardinal.to_part_enat_cast -> Cardinal.toPartENat_cast is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} PartENat (coeFn.{succ (succ u1), succ (succ u1)} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) (fun (_x : AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) => Cardinal.{u1} -> PartENat) (AddMonoidHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) Cardinal.toPartENat.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) n)
but is expected to have type
  forall (n : Nat), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) _x) (AddHomClass.toFunLike.{succ u1, succ u1, 0} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} PartENat (AddZeroClass.toAdd.{succ u1} Cardinal.{u1} (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1}))))))))) (AddZeroClass.toAdd.{0} PartENat (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) (AddMonoidHomClass.toAddHomClass.{succ u1, succ u1, 0} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat))) (AddMonoidHom.addMonoidHomClass.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))))) Cardinal.toPartENat.{u1} (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (Nat.cast.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (AddMonoidWithOne.toNatCast.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) PartENat.instAddCommMonoidWithOnePartENat)) n)
Case conversion may be inaccurate. Consider using '#align cardinal.to_part_enat_cast Cardinal.toPartENat_castₓ'. -/
@[simp]
theorem toPartENat_cast (n : ℕ) : Cardinal.toPartENat n = n := by
  rw [to_part_enat_apply_of_lt_aleph_0 (nat_lt_aleph_0 n), to_nat_cast]
#align cardinal.to_part_enat_cast Cardinal.toPartENat_cast

/- warning: cardinal.mk_to_part_enat_of_infinite -> Cardinal.mk_toPartENat_of_infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [h : Infinite.{succ u1} α], Eq.{1} PartENat (coeFn.{succ (succ u1), succ (succ u1)} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) (fun (_x : AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) => Cardinal.{u1} -> PartENat) (AddMonoidHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) Cardinal.toPartENat.{u1} (Cardinal.mk.{u1} α)) (Top.top.{0} PartENat PartENat.hasTop)
but is expected to have type
  forall {α : Type.{u1}} [h : Infinite.{succ u1} α], Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) (Cardinal.mk.{u1} α)) (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) _x) (AddHomClass.toFunLike.{succ u1, succ u1, 0} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} PartENat (AddZeroClass.toAdd.{succ u1} Cardinal.{u1} (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1}))))))))) (AddZeroClass.toAdd.{0} PartENat (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) (AddMonoidHomClass.toAddHomClass.{succ u1, succ u1, 0} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat))) (AddMonoidHom.addMonoidHomClass.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))))) Cardinal.toPartENat.{u1} (Cardinal.mk.{u1} α)) (Top.top.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) (Cardinal.mk.{u1} α)) PartENat.instTopPartENat)
Case conversion may be inaccurate. Consider using '#align cardinal.mk_to_part_enat_of_infinite Cardinal.mk_toPartENat_of_infiniteₓ'. -/
@[simp]
theorem mk_toPartENat_of_infinite [h : Infinite α] : (#α).toPartENat = ⊤ :=
  toPartENat_apply_of_aleph0_le (infinite_iff.1 h)
#align cardinal.mk_to_part_enat_of_infinite Cardinal.mk_toPartENat_of_infinite

/- warning: cardinal.aleph_0_to_part_enat -> Cardinal.aleph0_toPartENat is a dubious translation:
lean 3 declaration is
  Eq.{1} PartENat (coeFn.{succ (succ u1), succ (succ u1)} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) (fun (_x : AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) => Cardinal.{u1} -> PartENat) (AddMonoidHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) Cardinal.toPartENat.{u1} Cardinal.aleph0.{u1}) (Top.top.{0} PartENat PartENat.hasTop)
but is expected to have type
  Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) Cardinal.aleph0.{u1}) (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) _x) (AddHomClass.toFunLike.{succ u1, succ u1, 0} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} PartENat (AddZeroClass.toAdd.{succ u1} Cardinal.{u1} (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1}))))))))) (AddZeroClass.toAdd.{0} PartENat (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) (AddMonoidHomClass.toAddHomClass.{succ u1, succ u1, 0} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat))) (AddMonoidHom.addMonoidHomClass.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))))) Cardinal.toPartENat.{u1} Cardinal.aleph0.{u1}) (Top.top.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) Cardinal.aleph0.{u1}) PartENat.instTopPartENat)
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_0_to_part_enat Cardinal.aleph0_toPartENatₓ'. -/
@[simp]
theorem aleph0_toPartENat : toPartENat ℵ₀ = ⊤ :=
  toPartENat_apply_of_aleph0_le le_rfl
#align cardinal.aleph_0_to_part_enat Cardinal.aleph0_toPartENat

/- warning: cardinal.to_part_enat_surjective -> Cardinal.toPartENat_surjective is a dubious translation:
lean 3 declaration is
  Function.Surjective.{succ (succ u1), 1} Cardinal.{u1} PartENat (coeFn.{succ (succ u1), succ (succ u1)} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) (fun (_x : AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) => Cardinal.{u1} -> PartENat) (AddMonoidHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) Cardinal.toPartENat.{u1})
but is expected to have type
  Function.Surjective.{succ (succ u1), 1} Cardinal.{u1} PartENat (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) _x) (AddHomClass.toFunLike.{succ u1, succ u1, 0} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} PartENat (AddZeroClass.toAdd.{succ u1} Cardinal.{u1} (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1}))))))))) (AddZeroClass.toAdd.{0} PartENat (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) (AddMonoidHomClass.toAddHomClass.{succ u1, succ u1, 0} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat))) (AddMonoidHom.addMonoidHomClass.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))))) Cardinal.toPartENat.{u1})
Case conversion may be inaccurate. Consider using '#align cardinal.to_part_enat_surjective Cardinal.toPartENat_surjectiveₓ'. -/
theorem toPartENat_surjective : Surjective toPartENat := fun x =>
  PartENat.casesOn x ⟨ℵ₀, toPartENat_apply_of_aleph0_le le_rfl⟩ fun n => ⟨n, toPartENat_cast n⟩
#align cardinal.to_part_enat_surjective Cardinal.toPartENat_surjective

/- warning: cardinal.mk_to_part_enat_eq_coe_card -> Cardinal.mk_toPartENat_eq_coe_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α], Eq.{1} PartENat (coeFn.{succ (succ u1), succ (succ u1)} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) (fun (_x : AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) => Cardinal.{u1} -> PartENat) (AddMonoidHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) Cardinal.toPartENat.{u1} (Cardinal.mk.{u1} α)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) (Fintype.card.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α], Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) (Cardinal.mk.{u1} α)) (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) _x) (AddHomClass.toFunLike.{succ u1, succ u1, 0} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} PartENat (AddZeroClass.toAdd.{succ u1} Cardinal.{u1} (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1}))))))))) (AddZeroClass.toAdd.{0} PartENat (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) (AddMonoidHomClass.toAddHomClass.{succ u1, succ u1, 0} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat))) (AddMonoidHom.addMonoidHomClass.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))))) Cardinal.toPartENat.{u1} (Cardinal.mk.{u1} α)) (Nat.cast.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) (Cardinal.mk.{u1} α)) (AddMonoidWithOne.toNatCast.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) (Cardinal.mk.{u1} α)) (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Cardinal.{u1}) => PartENat) (Cardinal.mk.{u1} α)) PartENat.instAddCommMonoidWithOnePartENat)) (Fintype.card.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_to_part_enat_eq_coe_card Cardinal.mk_toPartENat_eq_coe_cardₓ'. -/
theorem mk_toPartENat_eq_coe_card [Fintype α] : (#α).toPartENat = Fintype.card α := by simp
#align cardinal.mk_to_part_enat_eq_coe_card Cardinal.mk_toPartENat_eq_coe_card

#print Cardinal.mk_int /-
theorem mk_int : (#ℤ) = ℵ₀ :=
  mk_denumerable ℤ
#align cardinal.mk_int Cardinal.mk_int
-/

#print Cardinal.mk_pNat /-
theorem mk_pNat : (#ℕ+) = ℵ₀ :=
  mk_denumerable ℕ+
#align cardinal.mk_pnat Cardinal.mk_pNat
-/

/- warning: cardinal.sum_lt_prod -> Cardinal.sum_lt_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (f : ι -> Cardinal.{u2}) (g : ι -> Cardinal.{u2}), (forall (i : ι), LT.lt.{succ u2} Cardinal.{u2} (Preorder.toLT.{succ u2} Cardinal.{u2} (PartialOrder.toPreorder.{succ u2} Cardinal.{u2} Cardinal.partialOrder.{u2})) (f i) (g i)) -> (LT.lt.{succ (max u1 u2)} Cardinal.{max u1 u2} (Preorder.toLT.{succ (max u1 u2)} Cardinal.{max u1 u2} (PartialOrder.toPreorder.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.partialOrder.{max u1 u2})) (Cardinal.sum.{u1, u2} ι f) (Cardinal.prod.{u1, u2} ι g))
but is expected to have type
  forall {ι : Type.{u2}} (f : ι -> Cardinal.{u1}) (g : ι -> Cardinal.{u1}), (forall (i : ι), LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (f i) (g i)) -> (LT.lt.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} (Preorder.toLT.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} (PartialOrder.toPreorder.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.partialOrder.{max u1 u2})) (Cardinal.sum.{u2, u1} ι f) (Cardinal.prod.{u2, u1} ι g))
Case conversion may be inaccurate. Consider using '#align cardinal.sum_lt_prod Cardinal.sum_lt_prodₓ'. -/
/-- **König's theorem** -/
theorem sum_lt_prod {ι} (f g : ι → Cardinal) (H : ∀ i, f i < g i) : sum f < prod g :=
  lt_of_not_ge fun ⟨F⟩ =>
    by
    have : Inhabited (∀ i : ι, (g i).out) :=
      by
      refine' ⟨fun i => Classical.choice <| mk_ne_zero_iff.1 _⟩
      rw [mk_out]
      exact (H i).ne_bot
    let G := inv_fun F
    have sG : surjective G := inv_fun_surjective F.2
    choose C hc using
      show ∀ i, ∃ b, ∀ a, G ⟨i, a⟩ i ≠ b by
        intro i
        simp only [-not_exists, not_exists.symm, not_forall.symm]
        refine' fun h => (H i).not_le _
        rw [← mk_out (f i), ← mk_out (g i)]
        exact ⟨embedding.of_surjective _ h⟩
    exact
      let ⟨⟨i, a⟩, h⟩ := sG C
      hc i a (congr_fun h _)
#align cardinal.sum_lt_prod Cardinal.sum_lt_prod

#print Cardinal.mk_empty /-
@[simp]
theorem mk_empty : (#Empty) = 0 :=
  mk_eq_zero _
#align cardinal.mk_empty Cardinal.mk_empty
-/

#print Cardinal.mk_pEmpty /-
@[simp]
theorem mk_pEmpty : (#PEmpty) = 0 :=
  mk_eq_zero _
#align cardinal.mk_pempty Cardinal.mk_pEmpty
-/

#print Cardinal.mk_pUnit /-
@[simp]
theorem mk_pUnit : (#PUnit) = 1 :=
  mk_eq_one PUnit
#align cardinal.mk_punit Cardinal.mk_pUnit
-/

#print Cardinal.mk_unit /-
theorem mk_unit : (#Unit) = 1 :=
  mk_pUnit
#align cardinal.mk_unit Cardinal.mk_unit
-/

#print Cardinal.mk_singleton /-
@[simp]
theorem mk_singleton {α : Type u} (x : α) : (#({x} : Set α)) = 1 :=
  mk_eq_one _
#align cardinal.mk_singleton Cardinal.mk_singleton
-/

#print Cardinal.mk_pLift_true /-
@[simp]
theorem mk_pLift_true : (#PLift True) = 1 :=
  mk_eq_one _
#align cardinal.mk_plift_true Cardinal.mk_pLift_true
-/

#print Cardinal.mk_pLift_false /-
@[simp]
theorem mk_pLift_false : (#PLift False) = 0 :=
  mk_eq_zero _
#align cardinal.mk_plift_false Cardinal.mk_pLift_false
-/

/- warning: cardinal.mk_vector -> Cardinal.mk_vector is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Vector.{u1} α n)) (HPow.hPow.{succ u1, 0, succ u1} Cardinal.{u1} Nat Cardinal.{u1} (instHPow.{succ u1, 0} Cardinal.{u1} Nat (Monoid.Pow.{succ u1} Cardinal.{u1} (MonoidWithZero.toMonoid.{succ u1} Cardinal.{u1} (Semiring.toMonoidWithZero.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))))) (Cardinal.mk.{u1} α) n)
but is expected to have type
  forall (α : Type.{u1}) (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Vector.{u1} α n)) (HPow.hPow.{succ u1, 0, succ u1} Cardinal.{u1} Nat Cardinal.{u1} (instHPow.{succ u1, 0} Cardinal.{u1} Nat (Monoid.Pow.{succ u1} Cardinal.{u1} (MonoidWithZero.toMonoid.{succ u1} Cardinal.{u1} (Semiring.toMonoidWithZero.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1}))))))) (Cardinal.mk.{u1} α) n)
Case conversion may be inaccurate. Consider using '#align cardinal.mk_vector Cardinal.mk_vectorₓ'. -/
@[simp]
theorem mk_vector (α : Type u) (n : ℕ) : (#Vector α n) = (#α) ^ℕ n :=
  (mk_congr (Equiv.vectorEquivFin α n)).trans <| by simp
#align cardinal.mk_vector Cardinal.mk_vector

/- warning: cardinal.mk_list_eq_sum_pow -> Cardinal.mk_list_eq_sum_pow is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (List.{u1} α)) (Cardinal.sum.{0, u1} Nat (fun (n : Nat) => HPow.hPow.{succ u1, 0, succ u1} Cardinal.{u1} Nat Cardinal.{u1} (instHPow.{succ u1, 0} Cardinal.{u1} Nat (Monoid.Pow.{succ u1} Cardinal.{u1} (MonoidWithZero.toMonoid.{succ u1} Cardinal.{u1} (Semiring.toMonoidWithZero.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))))) (Cardinal.mk.{u1} α) n))
but is expected to have type
  forall (α : Type.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (List.{u1} α)) (Cardinal.sum.{0, u1} Nat (fun (n : Nat) => HPow.hPow.{succ u1, 0, succ u1} Cardinal.{u1} Nat Cardinal.{u1} (instHPow.{succ u1, 0} Cardinal.{u1} Nat (Monoid.Pow.{succ u1} Cardinal.{u1} (MonoidWithZero.toMonoid.{succ u1} Cardinal.{u1} (Semiring.toMonoidWithZero.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1}))))))) (Cardinal.mk.{u1} α) n))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_list_eq_sum_pow Cardinal.mk_list_eq_sum_powₓ'. -/
theorem mk_list_eq_sum_pow (α : Type u) : (#List α) = sum fun n : ℕ => (#α) ^ℕ n :=
  calc
    (#List α) = (#Σn, Vector α n) := mk_congr (Equiv.sigmaFiberEquiv List.length).symm
    _ = sum fun n : ℕ => (#α) ^ℕ n := by simp
    
#align cardinal.mk_list_eq_sum_pow Cardinal.mk_list_eq_sum_pow

#print Cardinal.mk_quot_le /-
theorem mk_quot_le {α : Type u} {r : α → α → Prop} : (#Quot r) ≤ (#α) :=
  mk_le_of_surjective Quot.exists_rep
#align cardinal.mk_quot_le Cardinal.mk_quot_le
-/

#print Cardinal.mk_quotient_le /-
theorem mk_quotient_le {α : Type u} {s : Setoid α} : (#Quotient s) ≤ (#α) :=
  mk_quot_le
#align cardinal.mk_quotient_le Cardinal.mk_quotient_le
-/

#print Cardinal.mk_subtype_le_of_subset /-
theorem mk_subtype_le_of_subset {α : Type u} {p q : α → Prop} (h : ∀ ⦃x⦄, p x → q x) :
    (#Subtype p) ≤ (#Subtype q) :=
  ⟨Embedding.subtypeMap (Embedding.refl α) h⟩
#align cardinal.mk_subtype_le_of_subset Cardinal.mk_subtype_le_of_subset
-/

#print Cardinal.mk_emptyCollection /-
@[simp]
theorem mk_emptyCollection (α : Type u) : (#(∅ : Set α)) = 0 :=
  mk_eq_zero _
#align cardinal.mk_emptyc Cardinal.mk_emptyCollection
-/

#print Cardinal.mk_emptyCollection_iff /-
theorem mk_emptyCollection_iff {α : Type u} {s : Set α} : (#s) = 0 ↔ s = ∅ :=
  by
  constructor
  · intro h
    rw [mk_eq_zero_iff] at h
    exact eq_empty_iff_forall_not_mem.2 fun x hx => h.elim' ⟨x, hx⟩
  · rintro rfl
    exact mk_emptyc _
#align cardinal.mk_emptyc_iff Cardinal.mk_emptyCollection_iff
-/

#print Cardinal.mk_univ /-
@[simp]
theorem mk_univ {α : Type u} : (#@univ α) = (#α) :=
  mk_congr (Equiv.Set.univ α)
#align cardinal.mk_univ Cardinal.mk_univ
-/

#print Cardinal.mk_image_le /-
theorem mk_image_le {α β : Type u} {f : α → β} {s : Set α} : (#f '' s) ≤ (#s) :=
  mk_le_of_surjective surjective_onto_image
#align cardinal.mk_image_le Cardinal.mk_image_le
-/

#print Cardinal.mk_image_le_lift /-
theorem mk_image_le_lift {α : Type u} {β : Type v} {f : α → β} {s : Set α} :
    lift.{u} (#f '' s) ≤ lift.{v} (#s) :=
  lift_mk_le.{v, u, 0}.mpr ⟨Embedding.ofSurjective _ surjective_onto_image⟩
#align cardinal.mk_image_le_lift Cardinal.mk_image_le_lift
-/

#print Cardinal.mk_range_le /-
theorem mk_range_le {α β : Type u} {f : α → β} : (#range f) ≤ (#α) :=
  mk_le_of_surjective surjective_onto_range
#align cardinal.mk_range_le Cardinal.mk_range_le
-/

#print Cardinal.mk_range_le_lift /-
theorem mk_range_le_lift {α : Type u} {β : Type v} {f : α → β} :
    lift.{u} (#range f) ≤ lift.{v} (#α) :=
  lift_mk_le.{v, u, 0}.mpr ⟨Embedding.ofSurjective _ surjective_onto_range⟩
#align cardinal.mk_range_le_lift Cardinal.mk_range_le_lift
-/

#print Cardinal.mk_range_eq /-
theorem mk_range_eq (f : α → β) (h : Injective f) : (#range f) = (#α) :=
  mk_congr (Equiv.ofInjective f h).symm
#align cardinal.mk_range_eq Cardinal.mk_range_eq
-/

#print Cardinal.mk_range_eq_of_injective /-
theorem mk_range_eq_of_injective {α : Type u} {β : Type v} {f : α → β} (hf : Injective f) :
    lift.{u} (#range f) = lift.{v} (#α) :=
  lift_mk_eq'.mpr ⟨(Equiv.ofInjective f hf).symm⟩
#align cardinal.mk_range_eq_of_injective Cardinal.mk_range_eq_of_injective
-/

#print Cardinal.mk_range_eq_lift /-
theorem mk_range_eq_lift {α : Type u} {β : Type v} {f : α → β} (hf : Injective f) :
    lift.{max u w} (#range f) = lift.{max v w} (#α) :=
  lift_mk_eq.mpr ⟨(Equiv.ofInjective f hf).symm⟩
#align cardinal.mk_range_eq_lift Cardinal.mk_range_eq_lift
-/

#print Cardinal.mk_image_eq /-
theorem mk_image_eq {α β : Type u} {f : α → β} {s : Set α} (hf : Injective f) : (#f '' s) = (#s) :=
  mk_congr (Equiv.Set.image f s hf).symm
#align cardinal.mk_image_eq Cardinal.mk_image_eq
-/

#print Cardinal.mk_unionᵢ_le_sum_mk /-
theorem mk_unionᵢ_le_sum_mk {α ι : Type u} {f : ι → Set α} : (#⋃ i, f i) ≤ sum fun i => #f i :=
  calc
    (#⋃ i, f i) ≤ (#Σi, f i) := mk_le_of_surjective (Set.sigmaToUnionᵢ_surjective f)
    _ = sum fun i => #f i := mk_sigma _
    
#align cardinal.mk_Union_le_sum_mk Cardinal.mk_unionᵢ_le_sum_mk
-/

/- warning: cardinal.mk_Union_eq_sum_mk -> Cardinal.mk_unionᵢ_eq_sum_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u1}} {f : ι -> (Set.{u1} α)}, (forall (i : ι) (j : ι), (Ne.{succ u1} ι i j) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (f i) (f j))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.unionᵢ.{u1, succ u1} α ι (fun (i : ι) => f i)))) (Cardinal.sum.{u1, u1} ι (fun (i : ι) => Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (f i)))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u1}} {f : ι -> (Set.{u1} α)}, (forall (i : ι) (j : ι), (Ne.{succ u1} ι i j) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (f i) (f j))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α (Set.unionᵢ.{u1, succ u1} α ι (fun (i : ι) => f i)))) (Cardinal.sum.{u1, u1} ι (fun (i : ι) => Cardinal.mk.{u1} (Set.Elem.{u1} α (f i)))))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_Union_eq_sum_mk Cardinal.mk_unionᵢ_eq_sum_mkₓ'. -/
theorem mk_unionᵢ_eq_sum_mk {α ι : Type u} {f : ι → Set α}
    (h : ∀ i j, i ≠ j → Disjoint (f i) (f j)) : (#⋃ i, f i) = sum fun i => #f i :=
  calc
    (#⋃ i, f i) = (#Σi, f i) := mk_congr (Set.unionEqSigmaOfDisjoint h)
    _ = sum fun i => #f i := mk_sigma _
    
#align cardinal.mk_Union_eq_sum_mk Cardinal.mk_unionᵢ_eq_sum_mk

/- warning: cardinal.mk_Union_le -> Cardinal.mk_unionᵢ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u1}} (f : ι -> (Set.{u1} α)), LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.unionᵢ.{u1, succ u1} α ι (fun (i : ι) => f i)))) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) (Cardinal.mk.{u1} ι) (supᵢ.{succ u1, succ u1} Cardinal.{u1} (ConditionallyCompleteLattice.toHasSup.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1}))) ι (fun (i : ι) => Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (f i)))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u1}} (f : ι -> (Set.{u1} α)), LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α (Set.unionᵢ.{u1, succ u1} α ι (fun (i : ι) => f i)))) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (Cardinal.mk.{u1} ι) (supᵢ.{succ u1, succ u1} Cardinal.{u1} (ConditionallyCompleteLattice.toSupSet.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u1}))) ι (fun (i : ι) => Cardinal.mk.{u1} (Set.Elem.{u1} α (f i)))))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_Union_le Cardinal.mk_unionᵢ_leₓ'. -/
theorem mk_unionᵢ_le {α ι : Type u} (f : ι → Set α) : (#⋃ i, f i) ≤ (#ι) * ⨆ i, #f i :=
  mk_unionᵢ_le_sum_mk.trans (sum_le_supᵢ _)
#align cardinal.mk_Union_le Cardinal.mk_unionᵢ_le

/- warning: cardinal.mk_sUnion_le -> Cardinal.mk_unionₛ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (A : Set.{u1} (Set.{u1} α)), LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.unionₛ.{u1} α A))) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) A)) (supᵢ.{succ u1, succ u1} Cardinal.{u1} (ConditionallyCompleteLattice.toHasSup.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1}))) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) A) (fun (s : coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) A) => Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) A) Type.{u1} (coeSortTrans.{succ (succ u1), succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) A) (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (coeBaseAux.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) A) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) x A)))) s))))
but is expected to have type
  forall {α : Type.{u1}} (A : Set.{u1} (Set.{u1} α)), LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α (Set.unionₛ.{u1} α A))) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (Cardinal.mk.{u1} (Set.Elem.{u1} (Set.{u1} α) A)) (supᵢ.{succ u1, succ u1} Cardinal.{u1} (ConditionallyCompleteLattice.toSupSet.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u1}))) (Set.Elem.{u1} (Set.{u1} α) A) (fun (s : Set.Elem.{u1} (Set.{u1} α) A) => Cardinal.mk.{u1} (Set.Elem.{u1} α (Subtype.val.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) x A) s)))))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_sUnion_le Cardinal.mk_unionₛ_leₓ'. -/
theorem mk_unionₛ_le {α : Type u} (A : Set (Set α)) : (#⋃₀ A) ≤ (#A) * ⨆ s : A, #s :=
  by
  rw [sUnion_eq_Union]
  apply mk_Union_le
#align cardinal.mk_sUnion_le Cardinal.mk_unionₛ_le

/- warning: cardinal.mk_bUnion_le -> Cardinal.mk_bunionᵢ_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u1}} (A : ι -> (Set.{u1} α)) (s : Set.{u1} ι), LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.unionᵢ.{u1, succ u1} α ι (fun (x : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) x s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) x s) => A x))))) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} ι) Type.{u1} (Set.hasCoeToSort.{u1} ι) s)) (supᵢ.{succ u1, succ u1} Cardinal.{u1} (ConditionallyCompleteLattice.toHasSup.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1}))) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} ι) Type.{u1} (Set.hasCoeToSort.{u1} ι) s) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} ι) Type.{u1} (Set.hasCoeToSort.{u1} ι) s) => Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (A (Subtype.val.{succ u1} ι (fun (x : ι) => Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) x s) x))))))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u1}} (A : ι -> (Set.{u1} α)) (s : Set.{u1} ι), LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α (Set.unionᵢ.{u1, succ u1} α ι (fun (x : ι) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) x s) (fun (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) x s) => A x))))) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (Cardinal.mk.{u1} (Set.Elem.{u1} ι s)) (supᵢ.{succ u1, succ u1} Cardinal.{u1} (ConditionallyCompleteLattice.toSupSet.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u1}))) (Set.Elem.{u1} ι s) (fun (x : Set.Elem.{u1} ι s) => Cardinal.mk.{u1} (Set.Elem.{u1} α (A (Subtype.val.{succ u1} ι (fun (x : ι) => Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) x s) x))))))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_bUnion_le Cardinal.mk_bunionᵢ_leₓ'. -/
theorem mk_bunionᵢ_le {ι α : Type u} (A : ι → Set α) (s : Set ι) :
    (#⋃ x ∈ s, A x) ≤ (#s) * ⨆ x : s, #A x.1 :=
  by
  rw [bUnion_eq_Union]
  apply mk_Union_le
#align cardinal.mk_bUnion_le Cardinal.mk_bunionᵢ_le

#print Cardinal.finset_card_lt_aleph0 /-
theorem finset_card_lt_aleph0 (s : Finset α) : (#(↑s : Set α)) < ℵ₀ :=
  lt_aleph0_of_finite _
#align cardinal.finset_card_lt_aleph_0 Cardinal.finset_card_lt_aleph0
-/

/- warning: cardinal.mk_set_eq_nat_iff_finset -> Cardinal.mk_set_eq_nat_iff_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {n : Nat}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) (Exists.{succ u1} (Finset.{u1} α) (fun (t : Finset.{u1} α) => And (Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t) s) (Eq.{1} Nat (Finset.card.{u1} α t) n)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {n : Nat}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α s)) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (Exists.{succ u1} (Finset.{u1} α) (fun (t : Finset.{u1} α) => And (Eq.{succ u1} (Set.{u1} α) (Finset.toSet.{u1} α t) s) (Eq.{1} Nat (Finset.card.{u1} α t) n)))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_set_eq_nat_iff_finset Cardinal.mk_set_eq_nat_iff_finsetₓ'. -/
theorem mk_set_eq_nat_iff_finset {α} {s : Set α} {n : ℕ} :
    (#s) = n ↔ ∃ t : Finset α, (t : Set α) = s ∧ t.card = n :=
  by
  constructor
  · intro h
    lift s to Finset α using lt_aleph_0_iff_set_finite.1 (h.symm ▸ nat_lt_aleph_0 n)
    simpa using h
  · rintro ⟨t, rfl, rfl⟩
    exact mk_coe_finset
#align cardinal.mk_set_eq_nat_iff_finset Cardinal.mk_set_eq_nat_iff_finset

/- warning: cardinal.mk_eq_nat_iff_finset -> Cardinal.mk_eq_nat_iff_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} α) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) (Exists.{succ u1} (Finset.{u1} α) (fun (t : Finset.{u1} α) => And (Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t) (Set.univ.{u1} α)) (Eq.{1} Nat (Finset.card.{u1} α t) n)))
but is expected to have type
  forall {α : Type.{u1}} {n : Nat}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} α) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (Exists.{succ u1} (Finset.{u1} α) (fun (t : Finset.{u1} α) => And (Eq.{succ u1} (Set.{u1} α) (Finset.toSet.{u1} α t) (Set.univ.{u1} α)) (Eq.{1} Nat (Finset.card.{u1} α t) n)))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_eq_nat_iff_finset Cardinal.mk_eq_nat_iff_finsetₓ'. -/
theorem mk_eq_nat_iff_finset {n : ℕ} : (#α) = n ↔ ∃ t : Finset α, (t : Set α) = univ ∧ t.card = n :=
  by rw [← mk_univ, mk_set_eq_nat_iff_finset]
#align cardinal.mk_eq_nat_iff_finset Cardinal.mk_eq_nat_iff_finset

/- warning: cardinal.mk_eq_nat_iff_fintype -> Cardinal.mk_eq_nat_iff_fintype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} α) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) (Exists.{succ u1} (Fintype.{u1} α) (fun (h : Fintype.{u1} α) => Eq.{1} Nat (Fintype.card.{u1} α h) n))
but is expected to have type
  forall {α : Type.{u1}} {n : Nat}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} α) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (Exists.{succ u1} (Fintype.{u1} α) (fun (h : Fintype.{u1} α) => Eq.{1} Nat (Fintype.card.{u1} α h) n))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_eq_nat_iff_fintype Cardinal.mk_eq_nat_iff_fintypeₓ'. -/
theorem mk_eq_nat_iff_fintype {n : ℕ} : (#α) = n ↔ ∃ h : Fintype α, @Fintype.card α h = n :=
  by
  rw [mk_eq_nat_iff_finset]
  constructor
  · rintro ⟨t, ht, hn⟩
    exact ⟨⟨t, eq_univ_iff_forall.1 ht⟩, hn⟩
  · rintro ⟨⟨t, ht⟩, hn⟩
    exact ⟨t, eq_univ_iff_forall.2 ht, hn⟩
#align cardinal.mk_eq_nat_iff_fintype Cardinal.mk_eq_nat_iff_fintype

/- warning: cardinal.mk_union_add_mk_inter -> Cardinal.mk_union_add_mk_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {S : Set.{u1} α} {T : Set.{u1} α}, Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) S T))) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) S T)))) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S)) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T)))
but is expected to have type
  forall {α : Type.{u1}} {S : Set.{u1} α} {T : Set.{u1} α}, Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (Cardinal.mk.{u1} (Set.Elem.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) S T))) (Cardinal.mk.{u1} (Set.Elem.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) S T)))) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (Cardinal.mk.{u1} (Set.Elem.{u1} α S)) (Cardinal.mk.{u1} (Set.Elem.{u1} α T)))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_union_add_mk_inter Cardinal.mk_union_add_mk_interₓ'. -/
theorem mk_union_add_mk_inter {α : Type u} {S T : Set α} :
    (#(S ∪ T : Set α)) + (#(S ∩ T : Set α)) = (#S) + (#T) :=
  Quot.sound ⟨Equiv.Set.unionSumInter S T⟩
#align cardinal.mk_union_add_mk_inter Cardinal.mk_union_add_mk_inter

/- warning: cardinal.mk_union_le -> Cardinal.mk_union_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (S : Set.{u1} α) (T : Set.{u1} α), LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) S T))) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S)) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T)))
but is expected to have type
  forall {α : Type.{u1}} (S : Set.{u1} α) (T : Set.{u1} α), LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) S T))) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (Cardinal.mk.{u1} (Set.Elem.{u1} α S)) (Cardinal.mk.{u1} (Set.Elem.{u1} α T)))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_union_le Cardinal.mk_union_leₓ'. -/
/-- The cardinality of a union is at most the sum of the cardinalities
of the two sets. -/
theorem mk_union_le {α : Type u} (S T : Set α) : (#(S ∪ T : Set α)) ≤ (#S) + (#T) :=
  @mk_union_add_mk_inter α S T ▸ self_le_add_right (#(S ∪ T : Set α)) (#(S ∩ T : Set α))
#align cardinal.mk_union_le Cardinal.mk_union_le

/- warning: cardinal.mk_union_of_disjoint -> Cardinal.mk_union_of_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {S : Set.{u1} α} {T : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) S T) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) S T))) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S)) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T))))
but is expected to have type
  forall {α : Type.{u1}} {S : Set.{u1} α} {T : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) S T) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) S T))) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (Cardinal.mk.{u1} (Set.Elem.{u1} α S)) (Cardinal.mk.{u1} (Set.Elem.{u1} α T))))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_union_of_disjoint Cardinal.mk_union_of_disjointₓ'. -/
theorem mk_union_of_disjoint {α : Type u} {S T : Set α} (H : Disjoint S T) :
    (#(S ∪ T : Set α)) = (#S) + (#T) :=
  Quot.sound ⟨Equiv.Set.union H.le_bot⟩
#align cardinal.mk_union_of_disjoint Cardinal.mk_union_of_disjoint

/- warning: cardinal.mk_insert -> Cardinal.mk_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {a : α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s))) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (OfNat.mk.{succ u1} Cardinal.{u1} 1 (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {a : α}, (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s))) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (Cardinal.mk.{u1} (Set.Elem.{u1} α s)) (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (One.toOfNat1.{succ u1} Cardinal.{u1} Cardinal.instOneCardinal.{u1}))))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_insert Cardinal.mk_insertₓ'. -/
theorem mk_insert {α : Type u} {s : Set α} {a : α} (h : a ∉ s) :
    (#(insert a s : Set α)) = (#s) + 1 :=
  by
  rw [← union_singleton, mk_union_of_disjoint, mk_singleton]
  simpa
#align cardinal.mk_insert Cardinal.mk_insert

/- warning: cardinal.mk_sum_compl -> Cardinal.mk_sum_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)))) (Cardinal.mk.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (Cardinal.mk.{u1} (Set.Elem.{u1} α s)) (Cardinal.mk.{u1} (Set.Elem.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)))) (Cardinal.mk.{u1} α)
Case conversion may be inaccurate. Consider using '#align cardinal.mk_sum_compl Cardinal.mk_sum_complₓ'. -/
theorem mk_sum_compl {α} (s : Set α) : (#s) + (#(sᶜ : Set α)) = (#α) :=
  mk_congr (Equiv.Set.sumCompl s)
#align cardinal.mk_sum_compl Cardinal.mk_sum_compl

#print Cardinal.mk_le_mk_of_subset /-
theorem mk_le_mk_of_subset {α} {s t : Set α} (h : s ⊆ t) : (#s) ≤ (#t) :=
  ⟨Set.embeddingOfSubset s t h⟩
#align cardinal.mk_le_mk_of_subset Cardinal.mk_le_mk_of_subset
-/

#print Cardinal.mk_subtype_mono /-
theorem mk_subtype_mono {p q : α → Prop} (h : ∀ x, p x → q x) : (#{ x // p x }) ≤ (#{ x // q x }) :=
  ⟨embeddingOfSubset _ _ h⟩
#align cardinal.mk_subtype_mono Cardinal.mk_subtype_mono
-/

/- warning: cardinal.le_mk_diff_add_mk -> Cardinal.le_mk_diff_add_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (S : Set.{u1} α) (T : Set.{u1} α), LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S)) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) S T))) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T)))
but is expected to have type
  forall {α : Type.{u1}} (S : Set.{u1} α) (T : Set.{u1} α), LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α S)) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (Cardinal.mk.{u1} (Set.Elem.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) S T))) (Cardinal.mk.{u1} (Set.Elem.{u1} α T)))
Case conversion may be inaccurate. Consider using '#align cardinal.le_mk_diff_add_mk Cardinal.le_mk_diff_add_mkₓ'. -/
theorem le_mk_diff_add_mk (S T : Set α) : (#S) ≤ (#(S \ T : Set α)) + (#T) :=
  (mk_le_mk_of_subset <| subset_diff_union _ _).trans <| mk_union_le _ _
#align cardinal.le_mk_diff_add_mk Cardinal.le_mk_diff_add_mk

/- warning: cardinal.mk_diff_add_mk -> Cardinal.mk_diff_add_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {S : Set.{u1} α} {T : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) T S) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) S T))) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T))) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S)))
but is expected to have type
  forall {α : Type.{u1}} {S : Set.{u1} α} {T : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) T S) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (Cardinal.mk.{u1} (Set.Elem.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) S T))) (Cardinal.mk.{u1} (Set.Elem.{u1} α T))) (Cardinal.mk.{u1} (Set.Elem.{u1} α S)))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_diff_add_mk Cardinal.mk_diff_add_mkₓ'. -/
theorem mk_diff_add_mk {S T : Set α} (h : T ⊆ S) : (#(S \ T : Set α)) + (#T) = (#S) :=
  (mk_union_of_disjoint <| disjoint_sdiff_self_left).symm.trans <| by rw [diff_union_of_subset h]
#align cardinal.mk_diff_add_mk Cardinal.mk_diff_add_mk

/- warning: cardinal.mk_union_le_aleph_0 -> Cardinal.mk_union_le_aleph0 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : Set.{u1} α} {Q : Set.{u1} α}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) P Q))) Cardinal.aleph0.{u1}) (And (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) P)) Cardinal.aleph0.{u1}) (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) Q)) Cardinal.aleph0.{u1}))
but is expected to have type
  forall {α : Type.{u1}} {P : Set.{u1} α} {Q : Set.{u1} α}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) P Q))) Cardinal.aleph0.{u1}) (And (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α P)) Cardinal.aleph0.{u1}) (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α Q)) Cardinal.aleph0.{u1}))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_union_le_aleph_0 Cardinal.mk_union_le_aleph0ₓ'. -/
theorem mk_union_le_aleph0 {α} {P Q : Set α} : (#(P ∪ Q : Set α)) ≤ ℵ₀ ↔ (#P) ≤ ℵ₀ ∧ (#Q) ≤ ℵ₀ := by
  simp
#align cardinal.mk_union_le_aleph_0 Cardinal.mk_union_le_aleph0

#print Cardinal.mk_image_eq_lift /-
theorem mk_image_eq_lift {α : Type u} {β : Type v} (f : α → β) (s : Set α) (h : Injective f) :
    lift.{u} (#f '' s) = lift.{v} (#s) :=
  lift_mk_eq.{v, u, 0}.mpr ⟨(Equiv.Set.image f s h).symm⟩
#align cardinal.mk_image_eq_lift Cardinal.mk_image_eq_lift
-/

#print Cardinal.mk_image_eq_of_injOn_lift /-
theorem mk_image_eq_of_injOn_lift {α : Type u} {β : Type v} (f : α → β) (s : Set α)
    (h : InjOn f s) : lift.{u} (#f '' s) = lift.{v} (#s) :=
  lift_mk_eq.{v, u, 0}.mpr ⟨(Equiv.Set.imageOfInjOn f s h).symm⟩
#align cardinal.mk_image_eq_of_inj_on_lift Cardinal.mk_image_eq_of_injOn_lift
-/

#print Cardinal.mk_image_eq_of_injOn /-
theorem mk_image_eq_of_injOn {α β : Type u} (f : α → β) (s : Set α) (h : InjOn f s) :
    (#f '' s) = (#s) :=
  mk_congr (Equiv.Set.imageOfInjOn f s h).symm
#align cardinal.mk_image_eq_of_inj_on Cardinal.mk_image_eq_of_injOn
-/

#print Cardinal.mk_subtype_of_equiv /-
theorem mk_subtype_of_equiv {α β : Type u} (p : β → Prop) (e : α ≃ β) :
    (#{ a : α // p (e a) }) = (#{ b : β // p b }) :=
  mk_congr (Equiv.subtypeEquivOfSubtype e)
#align cardinal.mk_subtype_of_equiv Cardinal.mk_subtype_of_equiv
-/

#print Cardinal.mk_sep /-
theorem mk_sep (s : Set α) (t : α → Prop) : (#({ x ∈ s | t x } : Set α)) = (#{ x : s | t x.1 }) :=
  mk_congr (Equiv.Set.sep s t)
#align cardinal.mk_sep Cardinal.mk_sep
-/

#print Cardinal.mk_preimage_of_injective_lift /-
theorem mk_preimage_of_injective_lift {α : Type u} {β : Type v} (f : α → β) (s : Set β)
    (h : Injective f) : lift.{v} (#f ⁻¹' s) ≤ lift.{u} (#s) :=
  by
  rw [lift_mk_le.{u, v, 0}]; use Subtype.coind (fun x => f x.1) fun x => x.2
  apply Subtype.coind_injective; exact h.comp Subtype.val_injective
#align cardinal.mk_preimage_of_injective_lift Cardinal.mk_preimage_of_injective_lift
-/

#print Cardinal.mk_preimage_of_subset_range_lift /-
theorem mk_preimage_of_subset_range_lift {α : Type u} {β : Type v} (f : α → β) (s : Set β)
    (h : s ⊆ range f) : lift.{u} (#s) ≤ lift.{v} (#f ⁻¹' s) :=
  by
  rw [lift_mk_le.{v, u, 0}]
  refine' ⟨⟨_, _⟩⟩
  · rintro ⟨y, hy⟩
    rcases Classical.subtype_of_exists (h hy) with ⟨x, rfl⟩
    exact ⟨x, hy⟩
  rintro ⟨y, hy⟩ ⟨y', hy'⟩; dsimp
  rcases Classical.subtype_of_exists (h hy) with ⟨x, rfl⟩
  rcases Classical.subtype_of_exists (h hy') with ⟨x', rfl⟩
  simp; intro hxx'; rw [hxx']
#align cardinal.mk_preimage_of_subset_range_lift Cardinal.mk_preimage_of_subset_range_lift
-/

#print Cardinal.mk_preimage_of_injective_of_subset_range_lift /-
theorem mk_preimage_of_injective_of_subset_range_lift {β : Type v} (f : α → β) (s : Set β)
    (h : Injective f) (h2 : s ⊆ range f) : lift.{v} (#f ⁻¹' s) = lift.{u} (#s) :=
  le_antisymm (mk_preimage_of_injective_lift f s h) (mk_preimage_of_subset_range_lift f s h2)
#align cardinal.mk_preimage_of_injective_of_subset_range_lift Cardinal.mk_preimage_of_injective_of_subset_range_lift
-/

#print Cardinal.mk_preimage_of_injective /-
theorem mk_preimage_of_injective (f : α → β) (s : Set β) (h : Injective f) : (#f ⁻¹' s) ≤ (#s) := by
  convert mk_preimage_of_injective_lift.{u, u} f s h using 1 <;> rw [lift_id]
#align cardinal.mk_preimage_of_injective Cardinal.mk_preimage_of_injective
-/

#print Cardinal.mk_preimage_of_subset_range /-
theorem mk_preimage_of_subset_range (f : α → β) (s : Set β) (h : s ⊆ range f) : (#s) ≤ (#f ⁻¹' s) :=
  by convert mk_preimage_of_subset_range_lift.{u, u} f s h using 1 <;> rw [lift_id]
#align cardinal.mk_preimage_of_subset_range Cardinal.mk_preimage_of_subset_range
-/

#print Cardinal.mk_preimage_of_injective_of_subset_range /-
theorem mk_preimage_of_injective_of_subset_range (f : α → β) (s : Set β) (h : Injective f)
    (h2 : s ⊆ range f) : (#f ⁻¹' s) = (#s) := by
  convert mk_preimage_of_injective_of_subset_range_lift.{u, u} f s h h2 using 1 <;> rw [lift_id]
#align cardinal.mk_preimage_of_injective_of_subset_range Cardinal.mk_preimage_of_injective_of_subset_range
-/

#print Cardinal.mk_subset_ge_of_subset_image_lift /-
theorem mk_subset_ge_of_subset_image_lift {α : Type u} {β : Type v} (f : α → β) {s : Set α}
    {t : Set β} (h : t ⊆ f '' s) : lift.{u} (#t) ≤ lift.{v} (#({ x ∈ s | f x ∈ t } : Set α)) :=
  by
  rw [image_eq_range] at h
  convert mk_preimage_of_subset_range_lift _ _ h using 1
  rw [mk_sep]
  rfl
#align cardinal.mk_subset_ge_of_subset_image_lift Cardinal.mk_subset_ge_of_subset_image_lift
-/

#print Cardinal.mk_subset_ge_of_subset_image /-
theorem mk_subset_ge_of_subset_image (f : α → β) {s : Set α} {t : Set β} (h : t ⊆ f '' s) :
    (#t) ≤ (#({ x ∈ s | f x ∈ t } : Set α)) :=
  by
  rw [image_eq_range] at h
  convert mk_preimage_of_subset_range _ _ h using 1
  rw [mk_sep]
  rfl
#align cardinal.mk_subset_ge_of_subset_image Cardinal.mk_subset_ge_of_subset_image
-/

#print Cardinal.le_mk_iff_exists_subset /-
theorem le_mk_iff_exists_subset {c : Cardinal} {α : Type u} {s : Set α} :
    c ≤ (#s) ↔ ∃ p : Set α, p ⊆ s ∧ (#p) = c :=
  by
  rw [le_mk_iff_exists_set, ← Subtype.exists_set_subtype]
  apply exists_congr; intro t; rw [mk_image_eq]; apply Subtype.val_injective
#align cardinal.le_mk_iff_exists_subset Cardinal.le_mk_iff_exists_subset
-/

/- warning: cardinal.two_le_iff -> Cardinal.two_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (OfNat.mk.{succ u1} Cardinal.{u1} 2 (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) (Cardinal.mk.{u1} α)) (Exists.{succ u1} α (fun (x : α) => Exists.{succ u1} α (fun (y : α) => Ne.{succ u1} α x y)))
but is expected to have type
  forall {α : Type.{u1}}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (instOfNat.{succ u1} Cardinal.{u1} 2 Cardinal.instNatCastCardinal.{u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Cardinal.mk.{u1} α)) (Exists.{succ u1} α (fun (x : α) => Exists.{succ u1} α (fun (y : α) => Ne.{succ u1} α x y)))
Case conversion may be inaccurate. Consider using '#align cardinal.two_le_iff Cardinal.two_le_iffₓ'. -/
theorem two_le_iff : (2 : Cardinal) ≤ (#α) ↔ ∃ x y : α, x ≠ y := by
  rw [← Nat.cast_two, nat_succ, succ_le_iff, Nat.cast_one, one_lt_iff_nontrivial, nontrivial_iff]
#align cardinal.two_le_iff Cardinal.two_le_iff

/- warning: cardinal.two_le_iff' -> Cardinal.two_le_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : α), Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (OfNat.mk.{succ u1} Cardinal.{u1} 2 (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) (Cardinal.mk.{u1} α)) (Exists.{succ u1} α (fun (y : α) => Ne.{succ u1} α y x))
but is expected to have type
  forall {α : Type.{u1}} (x : α), Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (instOfNat.{succ u1} Cardinal.{u1} 2 Cardinal.instNatCastCardinal.{u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Cardinal.mk.{u1} α)) (Exists.{succ u1} α (fun (y : α) => Ne.{succ u1} α y x))
Case conversion may be inaccurate. Consider using '#align cardinal.two_le_iff' Cardinal.two_le_iff'ₓ'. -/
theorem two_le_iff' (x : α) : (2 : Cardinal) ≤ (#α) ↔ ∃ y : α, y ≠ x := by
  rw [two_le_iff, ← nontrivial_iff, nontrivial_iff_exists_ne x]
#align cardinal.two_le_iff' Cardinal.two_le_iff'

/- warning: cardinal.mk_eq_two_iff -> Cardinal.mk_eq_two_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} α) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (OfNat.mk.{succ u1} Cardinal.{u1} 2 (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1}))))) (Exists.{succ u1} α (fun (x : α) => Exists.{succ u1} α (fun (y : α) => And (Ne.{succ u1} α x y) (Eq.{succ u1} (Set.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) y)) (Set.univ.{u1} α)))))
but is expected to have type
  forall {α : Type.{u1}}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} α) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (instOfNat.{succ u1} Cardinal.{u1} 2 Cardinal.instNatCastCardinal.{u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (Exists.{succ u1} α (fun (x : α) => Exists.{succ u1} α (fun (y : α) => And (Ne.{succ u1} α x y) (Eq.{succ u1} (Set.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) y)) (Set.univ.{u1} α)))))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_eq_two_iff Cardinal.mk_eq_two_iffₓ'. -/
theorem mk_eq_two_iff : (#α) = 2 ↔ ∃ x y : α, x ≠ y ∧ ({x, y} : Set α) = univ :=
  by
  simp only [← @Nat.cast_two Cardinal, mk_eq_nat_iff_finset, Finset.card_eq_two]
  constructor
  · rintro ⟨t, ht, x, y, hne, rfl⟩
    exact ⟨x, y, hne, by simpa using ht⟩
  · rintro ⟨x, y, hne, h⟩
    exact ⟨{x, y}, by simpa using h, x, y, hne, rfl⟩
#align cardinal.mk_eq_two_iff Cardinal.mk_eq_two_iff

/- warning: cardinal.mk_eq_two_iff' -> Cardinal.mk_eq_two_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : α), Iff (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} α) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (OfNat.mk.{succ u1} Cardinal.{u1} 2 (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1}))))) (ExistsUnique.{succ u1} α (fun (y : α) => Ne.{succ u1} α y x))
but is expected to have type
  forall {α : Type.{u1}} (x : α), Iff (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} α) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (instOfNat.{succ u1} Cardinal.{u1} 2 Cardinal.instNatCastCardinal.{u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (ExistsUnique.{succ u1} α (fun (y : α) => Ne.{succ u1} α y x))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_eq_two_iff' Cardinal.mk_eq_two_iff'ₓ'. -/
theorem mk_eq_two_iff' (x : α) : (#α) = 2 ↔ ∃! y, y ≠ x :=
  by
  rw [mk_eq_two_iff]; constructor
  · rintro ⟨a, b, hne, h⟩
    simp only [eq_univ_iff_forall, mem_insert_iff, mem_singleton_iff] at h
    rcases h x with (rfl | rfl)
    exacts[⟨b, hne.symm, fun z => (h z).resolve_left⟩, ⟨a, hne, fun z => (h z).resolve_right⟩]
  · rintro ⟨y, hne, hy⟩
    exact ⟨x, y, hne.symm, eq_univ_of_forall fun z => or_iff_not_imp_left.2 (hy z)⟩
#align cardinal.mk_eq_two_iff' Cardinal.mk_eq_two_iff'

/- warning: cardinal.exists_not_mem_of_length_lt -> Cardinal.exists_not_mem_of_length_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (l : List.{u1} α), (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) (List.length.{u1} α l)) (Cardinal.mk.{u1} α)) -> (Exists.{succ u1} α (fun (z : α) => Not (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) z l)))
but is expected to have type
  forall {α : Type.{u1}} (l : List.{u1} α), (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} (List.length.{u1} α l)) (Cardinal.mk.{u1} α)) -> (Exists.{succ u1} α (fun (z : α) => Not (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) z l)))
Case conversion may be inaccurate. Consider using '#align cardinal.exists_not_mem_of_length_lt Cardinal.exists_not_mem_of_length_ltₓ'. -/
theorem exists_not_mem_of_length_lt {α : Type _} (l : List α) (h : ↑l.length < (#α)) :
    ∃ z : α, z ∉ l := by
  contrapose! h
  calc
    (#α) = (#(Set.univ : Set α)) := mk_univ.symm
    _ ≤ (#l.to_finset) := (mk_le_mk_of_subset fun x _ => list.mem_to_finset.mpr (h x))
    _ = l.to_finset.card := Cardinal.mk_coe_finset
    _ ≤ l.length := cardinal.nat_cast_le.mpr (List.toFinset_card_le l)
    
#align cardinal.exists_not_mem_of_length_lt Cardinal.exists_not_mem_of_length_lt

/- warning: cardinal.three_le -> Cardinal.three_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (OfNat.ofNat.{succ u1} Cardinal.{u1} 3 (OfNat.mk.{succ u1} Cardinal.{u1} 3 (bit1.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1} Cardinal.hasAdd.{u1} (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) (Cardinal.mk.{u1} α)) -> (forall (x : α) (y : α), Exists.{succ u1} α (fun (z : α) => And (Ne.{succ u1} α z x) (Ne.{succ u1} α z y)))
but is expected to have type
  forall {α : Type.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (OfNat.ofNat.{succ u1} Cardinal.{u1} 3 (instOfNat.{succ u1} Cardinal.{u1} 3 Cardinal.instNatCastCardinal.{u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Cardinal.mk.{u1} α)) -> (forall (x : α) (y : α), Exists.{succ u1} α (fun (z : α) => And (Ne.{succ u1} α z x) (Ne.{succ u1} α z y)))
Case conversion may be inaccurate. Consider using '#align cardinal.three_le Cardinal.three_leₓ'. -/
theorem three_le {α : Type _} (h : 3 ≤ (#α)) (x : α) (y : α) : ∃ z : α, z ≠ x ∧ z ≠ y :=
  by
  have : ↑(3 : ℕ) ≤ (#α); simpa using h
  have : ↑(2 : ℕ) < (#α); rwa [← succ_le_iff, ← Cardinal.nat_succ]
  have := exists_not_mem_of_length_lt [x, y] this
  simpa [not_or] using this
#align cardinal.three_le Cardinal.three_le

#print Cardinal.powerlt /-
/-- The function `a ^< b`, defined as the supremum of `a ^ c` for `c < b`. -/
def powerlt (a b : Cardinal.{u}) : Cardinal.{u} :=
  ⨆ c : Iio b, a^c
#align cardinal.powerlt Cardinal.powerlt
-/

-- mathport name: «expr ^< »
infixl:80 " ^< " => powerlt

#print Cardinal.le_powerlt /-
theorem le_powerlt {b c : Cardinal.{u}} (a) (h : c < b) : (a^c) ≤ a ^< b :=
  by
  apply @le_csupᵢ _ _ _ (fun y : Iio b => a^y) _ ⟨c, h⟩
  rw [← image_eq_range]
  exact bddAbove_image.{u, u} _ bddAbove_Iio
#align cardinal.le_powerlt Cardinal.le_powerlt
-/

#print Cardinal.powerlt_le /-
theorem powerlt_le {a b c : Cardinal.{u}} : a ^< b ≤ c ↔ ∀ x < b, (a^x) ≤ c :=
  by
  rw [powerlt, csupᵢ_le_iff']
  · simp
  · rw [← image_eq_range]
    exact bddAbove_image.{u, u} _ bddAbove_Iio
#align cardinal.powerlt_le Cardinal.powerlt_le
-/

#print Cardinal.powerlt_le_powerlt_left /-
theorem powerlt_le_powerlt_left {a b c : Cardinal} (h : b ≤ c) : a ^< b ≤ a ^< c :=
  powerlt_le.2 fun x hx => le_powerlt a <| hx.trans_le h
#align cardinal.powerlt_le_powerlt_left Cardinal.powerlt_le_powerlt_left
-/

#print Cardinal.powerlt_mono_left /-
theorem powerlt_mono_left (a) : Monotone fun c => a ^< c := fun b c => powerlt_le_powerlt_left
#align cardinal.powerlt_mono_left Cardinal.powerlt_mono_left
-/

/- warning: cardinal.powerlt_succ -> Cardinal.powerlt_succ is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (Ne.{succ (succ u1)} Cardinal.{u1} a (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.powerlt.{u1} a (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.succOrder.{u1} b)) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) a b))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (Ne.{succ (succ u1)} Cardinal.{u1} a (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.powerlt.{u1} a (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.instSuccOrderCardinalToPreorderPartialOrder.{u1} b)) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) a b))
Case conversion may be inaccurate. Consider using '#align cardinal.powerlt_succ Cardinal.powerlt_succₓ'. -/
theorem powerlt_succ {a b : Cardinal} (h : a ≠ 0) : a ^< succ b = (a^b) :=
  (powerlt_le.2 fun c h' => power_le_power_left h <| le_of_lt_succ h').antisymm <|
    le_powerlt a (lt_succ b)
#align cardinal.powerlt_succ Cardinal.powerlt_succ

/- warning: cardinal.powerlt_min -> Cardinal.powerlt_min is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.powerlt.{u1} a (LinearOrder.min.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toLinearOrder.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1})) b c)) (LinearOrder.min.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toLinearOrder.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1})) (Cardinal.powerlt.{u1} a b) (Cardinal.powerlt.{u1} a c))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.powerlt.{u1} a (Min.min.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMin.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) b c)) (Min.min.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMin.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Cardinal.powerlt.{u1} a b) (Cardinal.powerlt.{u1} a c))
Case conversion may be inaccurate. Consider using '#align cardinal.powerlt_min Cardinal.powerlt_minₓ'. -/
theorem powerlt_min {a b c : Cardinal} : a ^< min b c = min (a ^< b) (a ^< c) :=
  (powerlt_mono_left a).map_min
#align cardinal.powerlt_min Cardinal.powerlt_min

/- warning: cardinal.powerlt_max -> Cardinal.powerlt_max is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.powerlt.{u1} a (LinearOrder.max.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toLinearOrder.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1})) b c)) (LinearOrder.max.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toLinearOrder.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1})) (Cardinal.powerlt.{u1} a b) (Cardinal.powerlt.{u1} a c))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.powerlt.{u1} a (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) b c)) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Cardinal.powerlt.{u1} a b) (Cardinal.powerlt.{u1} a c))
Case conversion may be inaccurate. Consider using '#align cardinal.powerlt_max Cardinal.powerlt_maxₓ'. -/
theorem powerlt_max {a b c : Cardinal} : a ^< max b c = max (a ^< b) (a ^< c) :=
  (powerlt_mono_left a).map_max
#align cardinal.powerlt_max Cardinal.powerlt_max

#print Cardinal.zero_powerlt /-
theorem zero_powerlt {a : Cardinal} (h : a ≠ 0) : 0 ^< a = 1 :=
  by
  apply (powerlt_le.2 fun c hc => zero_power_le _).antisymm
  rw [← power_zero]
  exact le_powerlt 0 (pos_iff_ne_zero.2 h)
#align cardinal.zero_powerlt Cardinal.zero_powerlt
-/

#print Cardinal.powerlt_zero /-
@[simp]
theorem powerlt_zero {a : Cardinal} : a ^< 0 = 0 :=
  by
  convert Cardinal.supᵢ_of_empty _
  exact Subtype.isEmpty_of_false fun x => (Cardinal.zero_le _).not_lt
#align cardinal.powerlt_zero Cardinal.powerlt_zero
-/

end Cardinal

namespace Tactic

open Cardinal Positivity

/-- Extension for the `positivity` tactic: The cardinal power of a positive cardinal is positive. -/
@[positivity]
unsafe def positivity_cardinal_pow : expr → tactic strictness
  | q(@Pow.pow _ _ $(inst) $(a) $(b)) => do
    let strictness_a ← core a
    match strictness_a with
      | positive p => positive <$> mk_app `` power_pos [b, p]
      | _ => failed
  |-- We already know that `0 ≤ x` for all `x : cardinal`
    _ =>
    failed
#align tactic.positivity_cardinal_pow tactic.positivity_cardinal_pow

end Tactic

