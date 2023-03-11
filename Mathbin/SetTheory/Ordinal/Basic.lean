/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn

! This file was ported from Lean 3 source module set_theory.ordinal.basic
! leanprover-community/mathlib commit 8da9e30545433fdd8fe55a0d3da208e5d9263f03
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Sum.Order
import Mathbin.Order.InitialSeg
import Mathbin.SetTheory.Cardinal.Basic

/-!
# Ordinals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Ordinals are defined as equivalences of well-ordered sets under order isomorphism. They are endowed
with a total order, where an ordinal is smaller than another one if it embeds into it as an
initial segment (or, equivalently, in any way). This total order is well founded.

## Main definitions

* `ordinal`: the type of ordinals (in a given universe)
* `ordinal.type r`: given a well-founded order `r`, this is the corresponding ordinal
* `ordinal.typein r a`: given a well-founded order `r` on a type `α`, and `a : α`, the ordinal
  corresponding to all elements smaller than `a`.
* `enum r o h`: given a well-order `r` on a type `α`, and an ordinal `o` strictly smaller than
  the ordinal corresponding to `r` (this is the assumption `h`), returns the `o`-th element of `α`.
  In other words, the elements of `α` can be enumerated using ordinals up to `type r`.
* `ordinal.card o`: the cardinality of an ordinal `o`.
* `ordinal.lift` lifts an ordinal in universe `u` to an ordinal in universe `max u v`.
  For a version registering additionally that this is an initial segment embedding, see
  `ordinal.lift.initial_seg`.
  For a version regiserting that it is a principal segment embedding if `u < v`, see
  `ordinal.lift.principal_seg`.
* `ordinal.omega` or `ω` is the order type of `ℕ`. This definition is universe polymorphic:
  `ordinal.omega.{u} : ordinal.{u}` (contrast with `ℕ : Type`, which lives in a specific
  universe). In some cases the universe level has to be given explicitly.

* `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`. The main properties of addition
  (and the other operations on ordinals) are stated and proved in `ordinal_arithmetic.lean`. Here,
  we only introduce it and prove its basic properties to deduce the fact that the order on ordinals
  is total (and well founded).
* `succ o` is the successor of the ordinal `o`.
* `cardinal.ord c`: when `c` is a cardinal, `ord c` is the smallest ordinal with this cardinality.
  It is the canonical way to represent a cardinal with an ordinal.

A conditionally complete linear order with bot structure is registered on ordinals, where `⊥` is
`0`, the ordinal corresponding to the empty type, and `Inf` is the minimum for nonempty sets and `0`
for the empty set by convention.

## Notations

* `ω` is a notation for the first infinite ordinal in the locale `ordinal`.
-/


noncomputable section

open Function Cardinal Set Equiv Order

open Classical Cardinal InitialSeg

universe u v w

variable {α : Type _} {β : Type _} {γ : Type _} {r : α → α → Prop} {s : β → β → Prop}
  {t : γ → γ → Prop}

/-! ### Well order on an arbitrary type -/


section WellOrderingThm

parameter {σ : Type u}

open Function

#print nonempty_embedding_to_cardinal /-
theorem nonempty_embedding_to_cardinal : Nonempty (σ ↪ Cardinal.{u}) :=
  (Embedding.total _ _).resolve_left fun ⟨⟨f, hf⟩⟩ =>
    let g : σ → Cardinal.{u} := invFun f
    let ⟨x, (hx : g x = 2 ^ Sum g)⟩ := invFun_surjective hf (2 ^ Sum g)
    have : g x ≤ Sum g := le_sum.{u, u} g x
    not_le_of_gt (by rw [hx] <;> exact cantor _) this
#align nonempty_embedding_to_cardinal nonempty_embedding_to_cardinal
-/

#print embeddingToCardinal /-
/-- An embedding of any type to the set of cardinals. -/
def embeddingToCardinal : σ ↪ Cardinal.{u} :=
  Classical.choice nonempty_embedding_to_cardinal
#align embedding_to_cardinal embeddingToCardinal
-/

#print WellOrderingRel /-
/-- Any type can be endowed with a well order, obtained by pulling back the well order over
cardinals by some embedding. -/
def WellOrderingRel : σ → σ → Prop :=
  embeddingToCardinal ⁻¹'o (· < ·)
#align well_ordering_rel WellOrderingRel
-/

#print WellOrderingRel.isWellOrder /-
instance WellOrderingRel.isWellOrder : IsWellOrder σ WellOrderingRel :=
  (RelEmbedding.preimage _ _).IsWellOrder
#align well_ordering_rel.is_well_order WellOrderingRel.isWellOrder
-/

#print IsWellOrder.subtype_nonempty /-
instance IsWellOrder.subtype_nonempty : Nonempty { r // IsWellOrder σ r } :=
  ⟨⟨WellOrderingRel, inferInstance⟩⟩
#align is_well_order.subtype_nonempty IsWellOrder.subtype_nonempty
-/

end WellOrderingThm

/-! ### Definition of ordinals -/


#print WellOrder /-
/-- Bundled structure registering a well order on a type. Ordinals will be defined as a quotient
of this type. -/
structure WellOrder : Type (u + 1) where
  α : Type u
  R : α → α → Prop
  wo : IsWellOrder α r
#align Well_order WellOrder
-/

attribute [instance] WellOrder.wo

namespace WellOrder

instance : Inhabited WellOrder :=
  ⟨⟨PEmpty, _, EmptyRelation.isWellOrder⟩⟩

#print WellOrder.eta /-
@[simp]
theorem eta (o : WellOrder) : mk o.α o.R o.wo = o :=
  by
  cases o
  rfl
#align Well_order.eta WellOrder.eta
-/

end WellOrder

#print Ordinal.isEquivalent /-
/-- Equivalence relation on well orders on arbitrary types in universe `u`, given by order
isomorphism. -/
instance Ordinal.isEquivalent : Setoid WellOrder
    where
  R := fun ⟨α, r, wo⟩ ⟨β, s, wo'⟩ => Nonempty (r ≃r s)
  iseqv :=
    ⟨fun ⟨α, r, _⟩ => ⟨RelIso.refl _⟩, fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨e⟩ => ⟨e.symm⟩,
      fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩
#align ordinal.is_equivalent Ordinal.isEquivalent
-/

#print Ordinal /-
/-- `ordinal.{u}` is the type of well orders in `Type u`, up to order isomorphism. -/
def Ordinal : Type (u + 1) :=
  Quotient Ordinal.isEquivalent
#align ordinal Ordinal
-/

#print hasWellFoundedOut /-
instance hasWellFoundedOut (o : Ordinal) : WellFoundedRelation o.out.α :=
  ⟨o.out.R, o.out.wo.wf⟩
#align has_well_founded_out hasWellFoundedOut
-/

#print linearOrderOut /-
instance linearOrderOut (o : Ordinal) : LinearOrder o.out.α :=
  IsWellOrder.linearOrder o.out.R
#align linear_order_out linearOrderOut
-/

#print isWellOrder_out_lt /-
instance isWellOrder_out_lt (o : Ordinal) : IsWellOrder o.out.α (· < ·) :=
  o.out.wo
#align is_well_order_out_lt isWellOrder_out_lt
-/

namespace Ordinal

#print Ordinal.type /-
-- ### Basic properties of the order type
/-- The order type of a well order is an ordinal. -/
def type (r : α → α → Prop) [wo : IsWellOrder α r] : Ordinal :=
  ⟦⟨α, r, wo⟩⟧
#align ordinal.type Ordinal.type
-/

instance : Zero Ordinal :=
  ⟨type <| @EmptyRelation PEmpty⟩

instance : Inhabited Ordinal :=
  ⟨0⟩

instance : One Ordinal :=
  ⟨type <| @EmptyRelation PUnit⟩

#print Ordinal.typein /-
/-- The order type of an element inside a well order. For the embedding as a principal segment, see
`typein.principal_seg`. -/
def typein (r : α → α → Prop) [IsWellOrder α r] (a : α) : Ordinal :=
  type (Subrel r { b | r b a })
#align ordinal.typein Ordinal.typein
-/

#print Ordinal.type_def' /-
@[simp]
theorem type_def' (w : WellOrder) : ⟦w⟧ = type w.R :=
  by
  cases w
  rfl
#align ordinal.type_def' Ordinal.type_def'
-/

#print Ordinal.type_def /-
@[simp]
theorem type_def (r) [wo : IsWellOrder α r] : (⟦⟨α, r, wo⟩⟧ : Ordinal) = type r :=
  rfl
#align ordinal.type_def Ordinal.type_def
-/

#print Ordinal.type_out /-
@[simp]
theorem type_out (o : Ordinal) : Ordinal.type o.out.R = o := by
  rw [Ordinal.type, WellOrder.eta, Quotient.out_eq]
#align ordinal.type_out Ordinal.type_out
-/

#print Ordinal.type_eq /-
theorem type_eq {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s] :
    type r = type s ↔ Nonempty (r ≃r s) :=
  Quotient.eq'
#align ordinal.type_eq Ordinal.type_eq
-/

#print RelIso.ordinal_type_eq /-
theorem RelIso.ordinal_type_eq {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] (h : r ≃r s) : type r = type s :=
  type_eq.2 ⟨h⟩
#align rel_iso.ordinal_type_eq RelIso.ordinal_type_eq
-/

#print Ordinal.type_lt /-
@[simp]
theorem type_lt (o : Ordinal) : type ((· < ·) : o.out.α → o.out.α → Prop) = o :=
  (type_def' _).symm.trans <| Quotient.out_eq o
#align ordinal.type_lt Ordinal.type_lt
-/

#print Ordinal.type_eq_zero_of_empty /-
theorem type_eq_zero_of_empty (r) [IsWellOrder α r] [IsEmpty α] : type r = 0 :=
  (RelIso.relIsoOfIsEmpty r _).ordinal_type_eq
#align ordinal.type_eq_zero_of_empty Ordinal.type_eq_zero_of_empty
-/

#print Ordinal.type_eq_zero_iff_isEmpty /-
@[simp]
theorem type_eq_zero_iff_isEmpty [IsWellOrder α r] : type r = 0 ↔ IsEmpty α :=
  ⟨fun h =>
    let ⟨s⟩ := type_eq.1 h
    s.toEquiv.isEmpty,
    @type_eq_zero_of_empty α r _⟩
#align ordinal.type_eq_zero_iff_is_empty Ordinal.type_eq_zero_iff_isEmpty
-/

#print Ordinal.type_ne_zero_iff_nonempty /-
theorem type_ne_zero_iff_nonempty [IsWellOrder α r] : type r ≠ 0 ↔ Nonempty α := by simp
#align ordinal.type_ne_zero_iff_nonempty Ordinal.type_ne_zero_iff_nonempty
-/

#print Ordinal.type_ne_zero_of_nonempty /-
theorem type_ne_zero_of_nonempty (r) [IsWellOrder α r] [h : Nonempty α] : type r ≠ 0 :=
  type_ne_zero_iff_nonempty.2 h
#align ordinal.type_ne_zero_of_nonempty Ordinal.type_ne_zero_of_nonempty
-/

#print Ordinal.type_pEmpty /-
theorem type_pEmpty : type (@EmptyRelation PEmpty) = 0 :=
  rfl
#align ordinal.type_pempty Ordinal.type_pEmpty
-/

#print Ordinal.type_empty /-
theorem type_empty : type (@EmptyRelation Empty) = 0 :=
  type_eq_zero_of_empty _
#align ordinal.type_empty Ordinal.type_empty
-/

/- warning: ordinal.type_eq_one_of_unique -> Ordinal.type_eq_one_of_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (r : α -> α -> Prop) [_inst_1 : IsWellOrder.{u1} α r] [_inst_2 : Unique.{succ u1} α], Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.type.{u1} α r _inst_1) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))
but is expected to have type
  forall {α : Type.{u1}} (r : α -> α -> Prop) [_inst_1 : IsWellOrder.{u1} α r] [_inst_2 : Unique.{succ u1} α], Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.type.{u1} α r _inst_1) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.type_eq_one_of_unique Ordinal.type_eq_one_of_uniqueₓ'. -/
theorem type_eq_one_of_unique (r) [IsWellOrder α r] [Unique α] : type r = 1 :=
  (RelIso.relIsoOfUniqueOfIrrefl r _).ordinal_type_eq
#align ordinal.type_eq_one_of_unique Ordinal.type_eq_one_of_unique

/- warning: ordinal.type_eq_one_iff_unique -> Ordinal.type_eq_one_iff_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} [_inst_1 : IsWellOrder.{u1} α r], Iff (Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.type.{u1} α r _inst_1) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))) (Nonempty.{succ u1} (Unique.{succ u1} α))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} [_inst_1 : IsWellOrder.{u1} α r], Iff (Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.type.{u1} α r _inst_1) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))) (Nonempty.{succ u1} (Unique.{succ u1} α))
Case conversion may be inaccurate. Consider using '#align ordinal.type_eq_one_iff_unique Ordinal.type_eq_one_iff_uniqueₓ'. -/
@[simp]
theorem type_eq_one_iff_unique [IsWellOrder α r] : type r = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h =>
    let ⟨s⟩ := type_eq.1 h
    ⟨s.toEquiv.unique⟩,
    fun ⟨h⟩ => @type_eq_one_of_unique α r _ h⟩
#align ordinal.type_eq_one_iff_unique Ordinal.type_eq_one_iff_unique

/- warning: ordinal.type_punit -> Ordinal.type_pUnit is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.type.{u1} PUnit.{succ u1} (EmptyRelation.{succ u1} PUnit.{succ u1}) (EmptyRelation.isWellOrder.{u1} PUnit.{succ u1} PUnit.subsingleton.{succ u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))
but is expected to have type
  Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.type.{u1} PUnit.{succ u1} (EmptyRelation.{succ u1} PUnit.{succ u1}) (instIsWellOrderEmptyRelation.{u1} PUnit.{succ u1} instSubsingletonPUnit.{succ u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.type_punit Ordinal.type_pUnitₓ'. -/
theorem type_pUnit : type (@EmptyRelation PUnit) = 1 :=
  rfl
#align ordinal.type_punit Ordinal.type_pUnit

/- warning: ordinal.type_unit -> Ordinal.type_unit is a dubious translation:
lean 3 declaration is
  Eq.{2} Ordinal.{0} (Ordinal.type.{0} Unit (EmptyRelation.{1} Unit) (EmptyRelation.isWellOrder.{0} Unit PUnit.subsingleton.{1})) (OfNat.ofNat.{1} Ordinal.{0} 1 (OfNat.mk.{1} Ordinal.{0} 1 (One.one.{1} Ordinal.{0} Ordinal.hasOne.{0})))
but is expected to have type
  Eq.{2} Ordinal.{0} (Ordinal.type.{0} Unit (EmptyRelation.{1} Unit) (instIsWellOrderEmptyRelation.{0} Unit instSubsingletonPUnit.{1})) (OfNat.ofNat.{1} Ordinal.{0} 1 (One.toOfNat1.{1} Ordinal.{0} Ordinal.one.{0}))
Case conversion may be inaccurate. Consider using '#align ordinal.type_unit Ordinal.type_unitₓ'. -/
theorem type_unit : type (@EmptyRelation Unit) = 1 :=
  rfl
#align ordinal.type_unit Ordinal.type_unit

#print Ordinal.out_empty_iff_eq_zero /-
@[simp]
theorem out_empty_iff_eq_zero {o : Ordinal} : IsEmpty o.out.α ↔ o = 0 := by
  rw [← @type_eq_zero_iff_is_empty o.out.α (· < ·), type_lt]
#align ordinal.out_empty_iff_eq_zero Ordinal.out_empty_iff_eq_zero
-/

#print Ordinal.eq_zero_of_out_empty /-
theorem eq_zero_of_out_empty (o : Ordinal) [h : IsEmpty o.out.α] : o = 0 :=
  out_empty_iff_eq_zero.1 h
#align ordinal.eq_zero_of_out_empty Ordinal.eq_zero_of_out_empty
-/

#print Ordinal.isEmpty_out_zero /-
instance isEmpty_out_zero : IsEmpty (0 : Ordinal).out.α :=
  out_empty_iff_eq_zero.2 rfl
#align ordinal.is_empty_out_zero Ordinal.isEmpty_out_zero
-/

#print Ordinal.out_nonempty_iff_ne_zero /-
@[simp]
theorem out_nonempty_iff_ne_zero {o : Ordinal} : Nonempty o.out.α ↔ o ≠ 0 := by
  rw [← @type_ne_zero_iff_nonempty o.out.α (· < ·), type_lt]
#align ordinal.out_nonempty_iff_ne_zero Ordinal.out_nonempty_iff_ne_zero
-/

#print Ordinal.ne_zero_of_out_nonempty /-
theorem ne_zero_of_out_nonempty (o : Ordinal) [h : Nonempty o.out.α] : o ≠ 0 :=
  out_nonempty_iff_ne_zero.1 h
#align ordinal.ne_zero_of_out_nonempty Ordinal.ne_zero_of_out_nonempty
-/

/- warning: ordinal.one_ne_zero -> Ordinal.one_ne_zero is a dubious translation:
lean 3 declaration is
  Ne.{succ (succ u1)} Ordinal.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))
but is expected to have type
  Ne.{succ (succ u1)} Ordinal.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.one_ne_zero Ordinal.one_ne_zeroₓ'. -/
protected theorem one_ne_zero : (1 : Ordinal) ≠ 0 :=
  type_ne_zero_of_nonempty _
#align ordinal.one_ne_zero Ordinal.one_ne_zero

instance : Nontrivial Ordinal.{u} :=
  ⟨⟨1, 0, Ordinal.one_ne_zero⟩⟩

#print Ordinal.type_preimage /-
@[simp]
theorem type_preimage {α β : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β ≃ α) :
    type (f ⁻¹'o r) = type r :=
  (RelIso.preimage f r).ordinal_type_eq
#align ordinal.type_preimage Ordinal.type_preimage
-/

#print Ordinal.inductionOn /-
@[elab_as_elim]
theorem inductionOn {C : Ordinal → Prop} (o : Ordinal) (H : ∀ (α r) [IsWellOrder α r], C (type r)) :
    C o :=
  Quot.inductionOn o fun ⟨α, r, wo⟩ => @H α r wo
#align ordinal.induction_on Ordinal.inductionOn
-/

/-! ### The order on ordinals -/


instance : PartialOrder Ordinal
    where
  le a b :=
    Quotient.liftOn₂ a b (fun ⟨α, r, wo⟩ ⟨β, s, wo'⟩ => Nonempty (r ≼i s))
      fun ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩ =>
      propext
        ⟨fun ⟨h⟩ => ⟨(InitialSeg.ofIso f.symm).trans <| h.trans (InitialSeg.ofIso g)⟩, fun ⟨h⟩ =>
          ⟨(InitialSeg.ofIso f).trans <| h.trans (InitialSeg.ofIso g.symm)⟩⟩
  lt a b :=
    Quotient.liftOn₂ a b (fun ⟨α, r, wo⟩ ⟨β, s, wo'⟩ => Nonempty (r ≺i s))
      fun ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩ =>
      propext
        ⟨fun ⟨h⟩ => ⟨PrincipalSeg.equivLT f.symm <| h.ltLe (InitialSeg.ofIso g)⟩, fun ⟨h⟩ =>
          ⟨PrincipalSeg.equivLT f <| h.ltLe (InitialSeg.ofIso g.symm)⟩⟩
  le_refl := Quot.ind fun ⟨α, r, wo⟩ => ⟨InitialSeg.refl _⟩
  le_trans a b c :=
    Quotient.induction_on₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩
  lt_iff_le_not_le a b :=
    Quotient.induction_on₂ a b fun ⟨α, r, _⟩ ⟨β, s, _⟩ =>
      ⟨fun ⟨f⟩ => ⟨⟨f⟩, fun ⟨g⟩ => (f.ltLe g).irrefl⟩, fun ⟨⟨f⟩, h⟩ =>
        Sum.recOn f.lt_or_eq (fun g => ⟨g⟩) fun g => (h ⟨InitialSeg.ofIso g.symm⟩).elim⟩
  le_antisymm a b :=
    Quotient.induction_on₂ a b fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨h₁⟩ ⟨h₂⟩ =>
      Quot.sound ⟨InitialSeg.antisymm h₁ h₂⟩

/-- Ordinal less-equal is defined such that
  well orders `r` and `s` satisfy `type r ≤ type s` if there exists
  a function embedding `r` as an initial segment of `s`. -/
add_decl_doc ordinal.partial_order.le

/-- Ordinal less-than is defined such that
  well orders `r` and `s` satisfy `type r < type s` if there exists
  a function embedding `r` as a principal segment of `s`. -/
add_decl_doc ordinal.partial_order.lt

#print Ordinal.type_le_iff /-
theorem type_le_iff {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] : type r ≤ type s ↔ Nonempty (r ≼i s) :=
  Iff.rfl
#align ordinal.type_le_iff Ordinal.type_le_iff
-/

#print Ordinal.type_le_iff' /-
theorem type_le_iff' {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] : type r ≤ type s ↔ Nonempty (r ↪r s) :=
  ⟨fun ⟨f⟩ => ⟨f⟩, fun ⟨f⟩ => ⟨f.collapse⟩⟩
#align ordinal.type_le_iff' Ordinal.type_le_iff'
-/

#print InitialSeg.ordinal_type_le /-
theorem InitialSeg.ordinal_type_le {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] (h : r ≼i s) : type r ≤ type s :=
  ⟨h⟩
#align initial_seg.ordinal_type_le InitialSeg.ordinal_type_le
-/

#print RelEmbedding.ordinal_type_le /-
theorem RelEmbedding.ordinal_type_le {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] (h : r ↪r s) : type r ≤ type s :=
  ⟨h.collapse⟩
#align rel_embedding.ordinal_type_le RelEmbedding.ordinal_type_le
-/

#print Ordinal.type_lt_iff /-
@[simp]
theorem type_lt_iff {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] : type r < type s ↔ Nonempty (r ≺i s) :=
  Iff.rfl
#align ordinal.type_lt_iff Ordinal.type_lt_iff
-/

#print PrincipalSeg.ordinal_type_lt /-
theorem PrincipalSeg.ordinal_type_lt {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] (h : r ≺i s) : type r < type s :=
  ⟨h⟩
#align principal_seg.ordinal_type_lt PrincipalSeg.ordinal_type_lt
-/

#print Ordinal.zero_le /-
protected theorem zero_le (o : Ordinal) : 0 ≤ o :=
  inductionOn o fun α r _ => (InitialSeg.ofIsEmpty _ r).ordinal_type_le
#align ordinal.zero_le Ordinal.zero_le
-/

instance : OrderBot Ordinal :=
  ⟨0, Ordinal.zero_le⟩

/- warning: ordinal.bot_eq_zero -> Ordinal.bot_eq_zero is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Ordinal.{u1} (Bot.bot.{succ u1} Ordinal.{u1} (OrderBot.toHasBot.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) Ordinal.orderBot.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))
but is expected to have type
  Eq.{succ (succ u1)} Ordinal.{u1} (Bot.bot.{succ u1} Ordinal.{u1} (OrderBot.toBot.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) Ordinal.orderBot.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.bot_eq_zero Ordinal.bot_eq_zeroₓ'. -/
@[simp]
theorem bot_eq_zero : (⊥ : Ordinal) = 0 :=
  rfl
#align ordinal.bot_eq_zero Ordinal.bot_eq_zero

#print Ordinal.le_zero /-
@[simp]
protected theorem le_zero {o : Ordinal} : o ≤ 0 ↔ o = 0 :=
  le_bot_iff
#align ordinal.le_zero Ordinal.le_zero
-/

#print Ordinal.pos_iff_ne_zero /-
protected theorem pos_iff_ne_zero {o : Ordinal} : 0 < o ↔ o ≠ 0 :=
  bot_lt_iff_ne_bot
#align ordinal.pos_iff_ne_zero Ordinal.pos_iff_ne_zero
-/

#print Ordinal.not_lt_zero /-
protected theorem not_lt_zero (o : Ordinal) : ¬o < 0 :=
  not_lt_bot
#align ordinal.not_lt_zero Ordinal.not_lt_zero
-/

#print Ordinal.eq_zero_or_pos /-
theorem eq_zero_or_pos : ∀ a : Ordinal, a = 0 ∨ 0 < a :=
  eq_bot_or_bot_lt
#align ordinal.eq_zero_or_pos Ordinal.eq_zero_or_pos
-/

instance : ZeroLEOneClass Ordinal :=
  ⟨Ordinal.zero_le _⟩

/- warning: ordinal.ne_zero.one -> Ordinal.NeZero.one is a dubious translation:
lean 3 declaration is
  NeZero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))
but is expected to have type
  NeZero.{succ u1} Ordinal.{u1} Ordinal.zero.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.ne_zero.one Ordinal.NeZero.oneₓ'. -/
instance NeZero.one : NeZero (1 : Ordinal) :=
  ⟨Ordinal.one_ne_zero⟩
#align ordinal.ne_zero.one Ordinal.NeZero.one

#print Ordinal.initialSegOut /-
/-- Given two ordinals `α ≤ β`, then `initial_seg_out α β` is the initial segment embedding
of `α` to `β`, as map from a model type for `α` to a model type for `β`. -/
def initialSegOut {α β : Ordinal} (h : α ≤ β) :
    InitialSeg ((· < ·) : α.out.α → α.out.α → Prop) ((· < ·) : β.out.α → β.out.α → Prop) :=
  by
  change α.out.r ≼i β.out.r
  rw [← Quotient.out_eq α, ← Quotient.out_eq β] at h; revert h
  cases Quotient.out α; cases Quotient.out β; exact Classical.choice
#align ordinal.initial_seg_out Ordinal.initialSegOut
-/

#print Ordinal.principalSegOut /-
/-- Given two ordinals `α < β`, then `principal_seg_out α β` is the principal segment embedding
of `α` to `β`, as map from a model type for `α` to a model type for `β`. -/
def principalSegOut {α β : Ordinal} (h : α < β) :
    PrincipalSeg ((· < ·) : α.out.α → α.out.α → Prop) ((· < ·) : β.out.α → β.out.α → Prop) :=
  by
  change α.out.r ≺i β.out.r
  rw [← Quotient.out_eq α, ← Quotient.out_eq β] at h; revert h
  cases Quotient.out α; cases Quotient.out β; exact Classical.choice
#align ordinal.principal_seg_out Ordinal.principalSegOut
-/

#print Ordinal.typein_lt_type /-
theorem typein_lt_type (r : α → α → Prop) [IsWellOrder α r] (a : α) : typein r a < type r :=
  ⟨PrincipalSeg.ofElement _ _⟩
#align ordinal.typein_lt_type Ordinal.typein_lt_type
-/

#print Ordinal.typein_lt_self /-
theorem typein_lt_self {o : Ordinal} (i : o.out.α) : typein (· < ·) i < o :=
  by
  simp_rw [← type_lt o]
  apply typein_lt_type
#align ordinal.typein_lt_self Ordinal.typein_lt_self
-/

#print Ordinal.typein_top /-
@[simp]
theorem typein_top {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s]
    (f : r ≺i s) : typein s f.top = type r :=
  Eq.symm <|
    Quot.sound
      ⟨RelIso.ofSurjective (RelEmbedding.codRestrict _ f f.lt_top) fun ⟨a, h⟩ => by
          rcases f.down.1 h with ⟨b, rfl⟩ <;> exact ⟨b, rfl⟩⟩
#align ordinal.typein_top Ordinal.typein_top
-/

/- warning: ordinal.typein_apply -> Ordinal.typein_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u1} α r] [_inst_2 : IsWellOrder.{u1} β s] (f : InitialSeg.{u1, u1} α β r s) (a : α), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.typein.{u1} β s _inst_2 (coeFn.{succ u1, succ u1} (InitialSeg.{u1, u1} α β r s) (fun (_x : InitialSeg.{u1, u1} α β r s) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u1, succ u1} (InitialSeg.{u1, u1} α β r s) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (InitialSeg.{u1, u1} α β r s) α β (InitialSeg.embeddingLike.{u1, u1} α β r s))) f a)) (Ordinal.typein.{u1} α r _inst_1 a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u1} α r] [_inst_2 : IsWellOrder.{u1} β s] (f : InitialSeg.{u1, u1} α β r s) (a : α), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.typein.{u1} β s _inst_2 (FunLike.coe.{succ u1, succ u1, succ u1} (InitialSeg.{u1, u1} α β r s) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (InitialSeg.{u1, u1} α β r s) α β (InitialSeg.instEmbeddingLikeInitialSeg.{u1, u1} α β r s)) f a)) (Ordinal.typein.{u1} α r _inst_1 a)
Case conversion may be inaccurate. Consider using '#align ordinal.typein_apply Ordinal.typein_applyₓ'. -/
@[simp]
theorem typein_apply {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s]
    (f : r ≼i s) (a : α) : Ordinal.typein s (f a) = Ordinal.typein r a :=
  Eq.symm <|
    Quotient.sound
      ⟨RelIso.ofSurjective
          (RelEmbedding.codRestrict _ ((Subrel.relEmbedding _ _).trans f) fun ⟨x, h⟩ => by
            rw [RelEmbedding.trans_apply] <;> exact f.to_rel_embedding.map_rel_iff.2 h)
          fun ⟨y, h⟩ => by
          rcases f.init h with ⟨a, rfl⟩ <;>
            exact
              ⟨⟨a, f.to_rel_embedding.map_rel_iff.1 h⟩,
                Subtype.eq <| RelEmbedding.trans_apply _ _ _⟩⟩
#align ordinal.typein_apply Ordinal.typein_apply

#print Ordinal.typein_lt_typein /-
@[simp]
theorem typein_lt_typein (r : α → α → Prop) [IsWellOrder α r] {a b : α} :
    typein r a < typein r b ↔ r a b :=
  ⟨fun ⟨f⟩ =>
    by
    have : f.top.1 = a := by
      let f' := PrincipalSeg.ofElement r a
      let g' := f.trans (PrincipalSeg.ofElement r b)
      have : g'.top = f'.top := by rw [Subsingleton.elim f' g']
      exact this
    rw [← this]
    exact f.top.2, fun h =>
    ⟨PrincipalSeg.codRestrict _ (PrincipalSeg.ofElement r a) (fun x => @trans _ r _ _ _ _ x.2 h) h⟩⟩
#align ordinal.typein_lt_typein Ordinal.typein_lt_typein
-/

#print Ordinal.typein_surj /-
theorem typein_surj (r : α → α → Prop) [IsWellOrder α r] {o} (h : o < type r) :
    ∃ a, typein r a = o :=
  inductionOn o (fun β s _ ⟨f⟩ => ⟨f.top, typein_top _⟩) h
#align ordinal.typein_surj Ordinal.typein_surj
-/

#print Ordinal.typein_injective /-
theorem typein_injective (r : α → α → Prop) [IsWellOrder α r] : Injective (typein r) :=
  injective_of_increasing r (· < ·) (typein r) fun x y => (typein_lt_typein r).2
#align ordinal.typein_injective Ordinal.typein_injective
-/

#print Ordinal.typein_inj /-
@[simp]
theorem typein_inj (r : α → α → Prop) [IsWellOrder α r] {a b} : typein r a = typein r b ↔ a = b :=
  (typein_injective r).eq_iff
#align ordinal.typein_inj Ordinal.typein_inj
-/

/-! ### Enumerating elements in a well-order with ordinals. -/


#print Ordinal.enum /-
/-- `enum r o h` is the `o`-th element of `α` ordered by `r`.
  That is, `enum` maps an initial segment of the ordinals, those
  less than the order type of `r`, to the elements of `α`. -/
def enum (r : α → α → Prop) [IsWellOrder α r] (o) : o < type r → α :=
  Quot.recOn' o (fun ⟨β, s, _⟩ h => (Classical.choice h).top) fun ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨h⟩ =>
    by
    skip
    refine' funext fun H₂ : type t < type r => _
    have H₁ : type s < type r := by rwa [type_eq.2 ⟨h⟩]
    have :
      ∀ {o e} (H : o < type r),
        @Eq.ndrec (fun o : Ordinal => o < type r → α)
            (fun h : type s < type r => (Classical.choice h).top) e H =
          (Classical.choice H₁).top :=
      by
      intros
      subst e
    exact (this H₂).trans (PrincipalSeg.top_eq h (Classical.choice H₁) (Classical.choice H₂))
#align ordinal.enum Ordinal.enum
-/

#print Ordinal.enum_type /-
theorem enum_type {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s]
    (f : s ≺i r) {h : type s < type r} : enum r (type s) h = f.top :=
  PrincipalSeg.top_eq (RelIso.refl _) _ _
#align ordinal.enum_type Ordinal.enum_type
-/

#print Ordinal.enum_typein /-
@[simp]
theorem enum_typein (r : α → α → Prop) [IsWellOrder α r] (a : α) :
    enum r (typein r a) (typein_lt_type r a) = a :=
  enum_type (PrincipalSeg.ofElement r a)
#align ordinal.enum_typein Ordinal.enum_typein
-/

#print Ordinal.typein_enum /-
@[simp]
theorem typein_enum (r : α → α → Prop) [IsWellOrder α r] {o} (h : o < type r) :
    typein r (enum r o h) = o := by
  let ⟨a, e⟩ := typein_surj r h
  clear _let_match <;> subst e <;> rw [enum_typein]
#align ordinal.typein_enum Ordinal.typein_enum
-/

#print Ordinal.enum_lt_enum /-
theorem enum_lt_enum {r : α → α → Prop} [IsWellOrder α r] {o₁ o₂ : Ordinal} (h₁ : o₁ < type r)
    (h₂ : o₂ < type r) : r (enum r o₁ h₁) (enum r o₂ h₂) ↔ o₁ < o₂ := by
  rw [← typein_lt_typein r, typein_enum, typein_enum]
#align ordinal.enum_lt_enum Ordinal.enum_lt_enum
-/

/- warning: ordinal.rel_iso_enum' -> Ordinal.relIso_enum' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u1} α r] [_inst_2 : IsWellOrder.{u1} β s] (f : RelIso.{u1, u1} α β r s) (o : Ordinal.{u1}) (hr : LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o (Ordinal.type.{u1} α r _inst_1)) (hs : LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o (Ordinal.type.{u1} β s _inst_2)), Eq.{succ u1} β (coeFn.{succ u1, succ u1} (RelIso.{u1, u1} α β r s) (fun (_x : RelIso.{u1, u1} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u1} α β r s) f (Ordinal.enum.{u1} α r _inst_1 o hr)) (Ordinal.enum.{u1} β s _inst_2 o hs)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u1} α r] [_inst_2 : IsWellOrder.{u1} β s] (f : RelIso.{u1, u1} α β r s) (o : Ordinal.{u1}) (hr : LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o (Ordinal.type.{u1} α r _inst_1)) (hs : LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o (Ordinal.type.{u1} β s _inst_2)), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (Ordinal.enum.{u1} α r _inst_1 o hr)) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} α β)) (RelEmbedding.toEmbedding.{u1, u1} α β r s (RelIso.toRelEmbedding.{u1, u1} α β r s f)) (Ordinal.enum.{u1} α r _inst_1 o hr)) (Ordinal.enum.{u1} β s _inst_2 o hs)
Case conversion may be inaccurate. Consider using '#align ordinal.rel_iso_enum' Ordinal.relIso_enum'ₓ'. -/
theorem relIso_enum' {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] (f : r ≃r s) (o : Ordinal) :
    ∀ (hr : o < type r) (hs : o < type s), f (enum r o hr) = enum s o hs :=
  by
  refine' induction_on o _; rintro γ t wo ⟨g⟩ ⟨h⟩
  skip; rw [enum_type g, enum_type (PrincipalSeg.ltEquiv g f)]; rfl
#align ordinal.rel_iso_enum' Ordinal.relIso_enum'

/- warning: ordinal.rel_iso_enum -> Ordinal.relIso_enum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u1} α r] [_inst_2 : IsWellOrder.{u1} β s] (f : RelIso.{u1, u1} α β r s) (o : Ordinal.{u1}) (hr : LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o (Ordinal.type.{u1} α r _inst_1)), Eq.{succ u1} β (coeFn.{succ u1, succ u1} (RelIso.{u1, u1} α β r s) (fun (_x : RelIso.{u1, u1} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u1} α β r s) f (Ordinal.enum.{u1} α r _inst_1 o hr)) (Ordinal.enum.{u1} β s _inst_2 o (Eq.mpr.{0} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o (Ordinal.type.{u1} β s _inst_2)) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o (Ordinal.type.{u1} α r _inst_1)) ((fun [self : LT.{succ u1} Ordinal.{u1}] (ᾰ : Ordinal.{u1}) (ᾰ_1 : Ordinal.{u1}) (e_2 : Eq.{succ (succ u1)} Ordinal.{u1} ᾰ ᾰ_1) (ᾰ_2 : Ordinal.{u1}) (ᾰ_3 : Ordinal.{u1}) (e_3 : Eq.{succ (succ u1)} Ordinal.{u1} ᾰ_2 ᾰ_3) => congr.{succ (succ u1), 1} Ordinal.{u1} Prop (LT.lt.{succ u1} Ordinal.{u1} self ᾰ) (LT.lt.{succ u1} Ordinal.{u1} self ᾰ_1) ᾰ_2 ᾰ_3 (congr_arg.{succ (succ u1), succ (succ u1)} Ordinal.{u1} (Ordinal.{u1} -> Prop) ᾰ ᾰ_1 (LT.lt.{succ u1} Ordinal.{u1} self) e_2) e_3) (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o o (rfl.{succ (succ u1)} Ordinal.{u1} o) (Ordinal.type.{u1} β s _inst_2) (Ordinal.type.{u1} α r _inst_1) (Quotient.sound.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (WellOrder.mk.{u1} β s _inst_2) (WellOrder.mk.{u1} α r _inst_1) (Nonempty.intro.{succ u1} (RelIso.{u1, u1} β α s r) (RelIso.symm.{u1, u1} α β r s f)))) hr))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} [_inst_1 : IsWellOrder.{u1} α r] [_inst_2 : IsWellOrder.{u1} β s] (f : RelIso.{u1, u1} α β r s) (o : Ordinal.{u1}) (hr : LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o (Ordinal.type.{u1} α r _inst_1)), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (Ordinal.enum.{u1} α r _inst_1 o hr)) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} α β)) (RelEmbedding.toEmbedding.{u1, u1} α β r s (RelIso.toRelEmbedding.{u1, u1} α β r s f)) (Ordinal.enum.{u1} α r _inst_1 o hr)) (Ordinal.enum.{u1} β s _inst_2 o (Eq.mpr.{0} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o (Ordinal.type.{u1} β s _inst_2)) (Quot.lift.{succ (succ u1), 1} WellOrder.{u1} (fun (a : WellOrder.{u1}) (b : WellOrder.{u1}) => HasEquiv.Equiv.{succ (succ u1), 0} WellOrder.{u1} (instHasEquiv.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1}) a b) Prop (fun (a₁ : WellOrder.{u1}) => Quotient.lift.{succ (succ u1), 1} WellOrder.{u1} Prop Ordinal.isEquivalent.{u1} ((fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2468 : WellOrder.{u1}) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2469 : WellOrder.{u1}) => Ordinal.isEquivalent.match_1.{u1, 1} (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2468.2537 : WellOrder.{u1}) => Prop) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2468 (fun (α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2549 : Type.{u1}) (r : α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2549 -> α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2549 -> Prop) (wo._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2550 : IsWellOrder.{u1} α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2549 r) => Ordinal.isEquivalent.match_1.{u1, 1} (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2469.2555 : WellOrder.{u1}) => Prop) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2469 (fun (α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2567 : Type.{u1}) (s : α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2567 -> α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2567 -> Prop) (wo._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2568 : IsWellOrder.{u1} α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2567 s) => Nonempty.{succ u1} (PrincipalSeg.{u1, u1} α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2549 α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2567 r s)))) a₁) (Quotient.lift₂.proof_1.{succ (succ u1), 1, succ (succ u1)} WellOrder.{u1} WellOrder.{u1} Prop Ordinal.isEquivalent.{u1} Ordinal.isEquivalent.{u1} (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2468 : WellOrder.{u1}) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2469 : WellOrder.{u1}) => Ordinal.isEquivalent.match_1.{u1, 1} (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2468.2537 : WellOrder.{u1}) => Prop) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2468 (fun (α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2549 : Type.{u1}) (r : α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2549 -> α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2549 -> Prop) (wo._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2550 : IsWellOrder.{u1} α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2549 r) => Ordinal.isEquivalent.match_1.{u1, 1} (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2469.2555 : WellOrder.{u1}) => Prop) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2469 (fun (α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2567 : Type.{u1}) (s : α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2567 -> α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2567 -> Prop) (wo._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2568 : IsWellOrder.{u1} α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2567 s) => Nonempty.{succ u1} (PrincipalSeg.{u1, u1} α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2549 α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2567 r s)))) Ordinal.partialOrder.proof_2.{u1} a₁) (Ordinal.type.{u1} α r _inst_1)) (Quotient.lift₂.proof_2.{succ (succ u1), 1, succ (succ u1)} WellOrder.{u1} WellOrder.{u1} Prop Ordinal.isEquivalent.{u1} Ordinal.isEquivalent.{u1} (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2468 : WellOrder.{u1}) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2469 : WellOrder.{u1}) => Ordinal.isEquivalent.match_1.{u1, 1} (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2468.2537 : WellOrder.{u1}) => Prop) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2468 (fun (α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2549 : Type.{u1}) (r : α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2549 -> α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2549 -> Prop) (wo._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2550 : IsWellOrder.{u1} α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2549 r) => Ordinal.isEquivalent.match_1.{u1, 1} (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2469.2555 : WellOrder.{u1}) => Prop) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2469 (fun (α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2567 : Type.{u1}) (s : α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2567 -> α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2567 -> Prop) (wo._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2568 : IsWellOrder.{u1} α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2567 s) => Nonempty.{succ u1} (PrincipalSeg.{u1, u1} α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2549 α._@.Mathlib.SetTheory.Ordinal.Basic._hyg.2567 r s)))) Ordinal.partialOrder.proof_2.{u1} (Ordinal.type.{u1} α r _inst_1)) o) ((fun {α : Type.{succ u1}} [self : LT.{succ u1} α] (a._@.Init.Prelude._hyg.2009 : α) (a_1._@.Init.Prelude._hyg.2009 : α) (e_a._@.Init.Prelude._hyg.2009 : Eq.{succ (succ u1)} α a._@.Init.Prelude._hyg.2009 a_1._@.Init.Prelude._hyg.2009) => Eq.rec.{0, succ (succ u1)} α a._@.Init.Prelude._hyg.2009 (fun (a_1._@.Init.Prelude._hyg.2009 : α) (e_a._@.Init.Prelude._hyg.2009 : Eq.{succ (succ u1)} α a._@.Init.Prelude._hyg.2009 a_1._@.Init.Prelude._hyg.2009) => forall (a._@.Init.Prelude._hyg.2011 : α) (a_1._@.Init.Prelude._hyg.2011 : α), (Eq.{succ (succ u1)} α a._@.Init.Prelude._hyg.2011 a_1._@.Init.Prelude._hyg.2011) -> (Eq.{1} Prop (LT.lt.{succ u1} α self a._@.Init.Prelude._hyg.2009 a._@.Init.Prelude._hyg.2011) (LT.lt.{succ u1} α self a_1._@.Init.Prelude._hyg.2009 a_1._@.Init.Prelude._hyg.2011))) (fun (a._@.Init.Prelude._hyg.2011 : α) (a_1._@.Init.Prelude._hyg.2011 : α) (e_a._@.Init.Prelude._hyg.2011 : Eq.{succ (succ u1)} α a._@.Init.Prelude._hyg.2011 a_1._@.Init.Prelude._hyg.2011) => Eq.rec.{0, succ (succ u1)} α a._@.Init.Prelude._hyg.2011 (fun (a_1._@.Init.Prelude._hyg.2011 : α) (e_a._@.Init.Prelude._hyg.2011 : Eq.{succ (succ u1)} α a._@.Init.Prelude._hyg.2011 a_1._@.Init.Prelude._hyg.2011) => Eq.{1} Prop (LT.lt.{succ u1} α self a._@.Init.Prelude._hyg.2009 a._@.Init.Prelude._hyg.2011) (LT.lt.{succ u1} α self a._@.Init.Prelude._hyg.2009 a_1._@.Init.Prelude._hyg.2011)) (Eq.refl.{1} Prop (LT.lt.{succ u1} α self a._@.Init.Prelude._hyg.2009 a._@.Init.Prelude._hyg.2011)) a_1._@.Init.Prelude._hyg.2011 e_a._@.Init.Prelude._hyg.2011) a_1._@.Init.Prelude._hyg.2009 e_a._@.Init.Prelude._hyg.2009) Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o o (Eq.refl.{succ (succ u1)} Ordinal.{u1} o) (Ordinal.type.{u1} β s _inst_2) (Ordinal.type.{u1} α r _inst_1) (Quotient.sound.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (WellOrder.mk.{u1} β s _inst_2) (WellOrder.mk.{u1} α r _inst_1) (Nonempty.intro.{succ u1} (RelIso.{u1, u1} β α s r) (RelIso.symm.{u1, u1} α β r s f)))) hr))
Case conversion may be inaccurate. Consider using '#align ordinal.rel_iso_enum Ordinal.relIso_enumₓ'. -/
theorem relIso_enum {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] (f : r ≃r s) (o : Ordinal) (hr : o < type r) :
    f (enum r o hr) =
      enum s o
        (by
          convert hr using 1
          apply Quotient.sound
          exact ⟨f.symm⟩) :=
  relIso_enum' _ _ _ _
#align ordinal.rel_iso_enum Ordinal.relIso_enum

#print Ordinal.lt_wf /-
theorem lt_wf : @WellFounded Ordinal (· < ·) :=
  ⟨fun a =>
    inductionOn a fun α r wo =>
      suffices ∀ a, Acc (· < ·) (typein r a) from
        ⟨_, fun o h =>
          let ⟨a, e⟩ := typein_surj r h
          e ▸ this a⟩
      fun a =>
      Acc.recOn (wo.wf.apply a) fun x H IH =>
        ⟨_, fun o h =>
          by
          rcases typein_surj r (lt_trans h (typein_lt_type r _)) with ⟨b, rfl⟩
          exact IH _ ((typein_lt_typein r).1 h)⟩⟩
#align ordinal.lt_wf Ordinal.lt_wf
-/

instance : WellFoundedRelation Ordinal :=
  ⟨(· < ·), lt_wf⟩

#print Ordinal.induction /-
/-- Reformulation of well founded induction on ordinals as a lemma that works with the
`induction` tactic, as in `induction i using ordinal.induction with i IH`. -/
theorem induction {p : Ordinal.{u} → Prop} (i : Ordinal.{u}) (h : ∀ j, (∀ k, k < j → p k) → p j) :
    p i :=
  lt_wf.induction i h
#align ordinal.induction Ordinal.induction
-/

#print Ordinal.typein.principalSeg /-
/-- Principal segment version of the `typein` function, embedding a well order into
  ordinals as a principal segment. -/
def typein.principalSeg {α : Type u} (r : α → α → Prop) [IsWellOrder α r] :
    @PrincipalSeg α Ordinal.{u} r (· < ·) :=
  ⟨RelEmbedding.ofMonotone (typein r) fun a b => (typein_lt_typein r).2, type r, fun b =>
    ⟨fun h => ⟨enum r _ h, typein_enum r h⟩, fun ⟨a, e⟩ => e ▸ typein_lt_type _ _⟩⟩
#align ordinal.typein.principal_seg Ordinal.typein.principalSeg
-/

/- warning: ordinal.typein.principal_seg_coe -> Ordinal.typein.principalSeg_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (r : α -> α -> Prop) [_inst_1 : IsWellOrder.{u1} α r], Eq.{succ (succ u1)} ((fun (_x : PrincipalSeg.{u1, succ u1} α Ordinal.{u1} r (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})))) => α -> Ordinal.{u1}) (Ordinal.typein.principalSeg.{u1} α r _inst_1)) (coeFn.{succ (succ u1), succ (succ u1)} (PrincipalSeg.{u1, succ u1} α Ordinal.{u1} r (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})))) (fun (_x : PrincipalSeg.{u1, succ u1} α Ordinal.{u1} r (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})))) => α -> Ordinal.{u1}) (PrincipalSeg.hasCoeToFun.{u1, succ u1} α Ordinal.{u1} r (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})))) (Ordinal.typein.principalSeg.{u1} α r _inst_1)) (Ordinal.typein.{u1} α r _inst_1)
but is expected to have type
  forall {α : Type.{u1}} (r : α -> α -> Prop) [_inst_1 : IsWellOrder.{u1} α r], Eq.{succ (succ u1)} (forall (a : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Ordinal.{u1}) a) (FunLike.coe.{succ (succ u1), succ u1, succ (succ u1)} (Function.Embedding.{succ u1, succ (succ u1)} α Ordinal.{u1}) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Ordinal.{u1}) _x) (EmbeddingLike.toFunLike.{succ (succ u1), succ u1, succ (succ u1)} (Function.Embedding.{succ u1, succ (succ u1)} α Ordinal.{u1}) α Ordinal.{u1} (Function.instEmbeddingLikeEmbedding.{succ u1, succ (succ u1)} α Ordinal.{u1})) (RelEmbedding.toEmbedding.{u1, succ u1} α Ordinal.{u1} r (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.5885 : Ordinal.{u1}) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.5887 : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.5885 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.5887) (PrincipalSeg.toRelEmbedding.{u1, succ u1} α Ordinal.{u1} r (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.5885 : Ordinal.{u1}) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.5887 : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.5885 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.5887) (Ordinal.typein.principalSeg.{u1} α r _inst_1)))) (Ordinal.typein.{u1} α r _inst_1)
Case conversion may be inaccurate. Consider using '#align ordinal.typein.principal_seg_coe Ordinal.typein.principalSeg_coeₓ'. -/
@[simp]
theorem typein.principalSeg_coe (r : α → α → Prop) [IsWellOrder α r] :
    (typein.principalSeg r : α → Ordinal) = typein r :=
  rfl
#align ordinal.typein.principal_seg_coe Ordinal.typein.principalSeg_coe

/-! ### Cardinality of ordinals -/


#print Ordinal.card /-
/-- The cardinal of an ordinal is the cardinality of any type on which a relation with that order
type is defined. -/
def card : Ordinal → Cardinal :=
  Quotient.map WellOrder.α fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨e⟩ => ⟨e.toEquiv⟩
#align ordinal.card Ordinal.card
-/

#print Ordinal.card_type /-
@[simp]
theorem card_type (r : α → α → Prop) [IsWellOrder α r] : card (type r) = (#α) :=
  rfl
#align ordinal.card_type Ordinal.card_type
-/

#print Ordinal.card_typein /-
@[simp]
theorem card_typein {r : α → α → Prop} [wo : IsWellOrder α r] (x : α) :
    (#{ y // r y x }) = (typein r x).card :=
  rfl
#align ordinal.card_typein Ordinal.card_typein
-/

#print Ordinal.card_le_card /-
theorem card_le_card {o₁ o₂ : Ordinal} : o₁ ≤ o₂ → card o₁ ≤ card o₂ :=
  inductionOn o₁ fun α r _ => inductionOn o₂ fun β s _ ⟨⟨⟨f, _⟩, _⟩⟩ => ⟨f⟩
#align ordinal.card_le_card Ordinal.card_le_card
-/

#print Ordinal.card_zero /-
@[simp]
theorem card_zero : card 0 = 0 :=
  rfl
#align ordinal.card_zero Ordinal.card_zero
-/

#print Ordinal.card_eq_zero /-
@[simp]
theorem card_eq_zero {o} : card o = 0 ↔ o = 0 :=
  ⟨inductionOn o fun α r _ h => by
      haveI := Cardinal.mk_eq_zero_iff.1 h
      apply type_eq_zero_of_empty,
    fun e => by simp only [e, card_zero]⟩
#align ordinal.card_eq_zero Ordinal.card_eq_zero
-/

/- warning: ordinal.card_one -> Ordinal.card_one is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Cardinal.{u1} (Ordinal.card.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))) (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (OfNat.mk.{succ u1} Cardinal.{u1} 1 (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))
but is expected to have type
  Eq.{succ (succ u1)} Cardinal.{u1} (Ordinal.card.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))) (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (One.toOfNat1.{succ u1} Cardinal.{u1} Cardinal.instOneCardinal.{u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.card_one Ordinal.card_oneₓ'. -/
@[simp]
theorem card_one : card 1 = 1 :=
  rfl
#align ordinal.card_one Ordinal.card_one

/-! ### Lifting ordinals to a higher universe -/


#print Ordinal.lift /-
/-- The universe lift operation for ordinals, which embeds `ordinal.{u}` as
  a proper initial segment of `ordinal.{v}` for `v > u`. For the initial segment version,
  see `lift.initial_seg`. -/
def lift (o : Ordinal.{v}) : Ordinal.{max v u} :=
  Quotient.liftOn o (fun w => type <| ULift.down ⁻¹'o w.R) fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨f⟩ =>
    Quot.sound
      ⟨(RelIso.preimage Equiv.ulift r).trans <| f.trans (RelIso.preimage Equiv.ulift s).symm⟩
#align ordinal.lift Ordinal.lift
-/

/- warning: ordinal.type_ulift -> Ordinal.type_uLift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u2}} (r : α -> α -> Prop) [_inst_1 : IsWellOrder.{u2} α r], Eq.{succ (succ (max u2 u1))} Ordinal.{max u2 u1} (Ordinal.type.{max u2 u1} (ULift.{u1, u2} α) (Order.Preimage.{succ (max u2 u1), succ u2} (ULift.{u1, u2} α) α (ULift.down.{u1, u2} α) r) (RelIso.IsWellOrder.ulift.{u2, u1} α r _inst_1)) (Ordinal.lift.{u1, u2} (Ordinal.type.{u2} α r _inst_1))
but is expected to have type
  forall {α : Type.{u1}} (r : α -> α -> Prop) [_inst_1 : IsWellOrder.{u1} α r], Eq.{max (succ (succ u1)) (succ (succ u2))} Ordinal.{max u1 u2} (Ordinal.type.{max u1 u2} (ULift.{u2, u1} α) (Order.Preimage.{succ (max u1 u2), succ u1} (ULift.{u2, u1} α) α (ULift.down.{u2, u1} α) r) (RelIso.IsWellOrder.ulift.{u1, u2} α r _inst_1)) (Ordinal.lift.{u2, u1} (Ordinal.type.{u1} α r _inst_1))
Case conversion may be inaccurate. Consider using '#align ordinal.type_ulift Ordinal.type_uLiftₓ'. -/
@[simp]
theorem type_uLift (r : α → α → Prop) [IsWellOrder α r] :
    type (ULift.down ⁻¹'o r) = lift.{v} (type r) :=
  rfl
#align ordinal.type_ulift Ordinal.type_uLift

#print RelIso.ordinal_lift_type_eq /-
theorem RelIso.ordinal_lift_type_eq {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (f : r ≃r s) : lift.{v} (type r) = lift.{u} (type s) :=
  ((RelIso.preimage Equiv.ulift r).trans <|
      f.trans (RelIso.preimage Equiv.ulift s).symm).ordinal_type_eq
#align rel_iso.ordinal_lift_type_eq RelIso.ordinal_lift_type_eq
-/

#print Ordinal.type_lift_preimage /-
@[simp]
theorem type_lift_preimage {α : Type u} {β : Type v} (r : α → α → Prop) [IsWellOrder α r]
    (f : β ≃ α) : lift.{u} (type (f ⁻¹'o r)) = lift.{v} (type r) :=
  (RelIso.preimage f r).ordinal_lift_type_eq
#align ordinal.type_lift_preimage Ordinal.type_lift_preimage
-/

#print Ordinal.lift_umax /-
/-- `lift.{(max u v) u}` equals `lift.{v u}`. Using `set_option pp.universes true` will make it much
    easier to understand what's happening when using this lemma. -/
@[simp]
theorem lift_umax : lift.{max u v, u} = lift.{v, u} :=
  funext fun a =>
    inductionOn a fun α r _ =>
      Quotient.sound ⟨(RelIso.preimage Equiv.ulift r).trans (RelIso.preimage Equiv.ulift r).symm⟩
#align ordinal.lift_umax Ordinal.lift_umax
-/

#print Ordinal.lift_umax' /-
/-- `lift.{(max v u) u}` equals `lift.{v u}`. Using `set_option pp.universes true` will make it much
    easier to understand what's happening when using this lemma. -/
@[simp]
theorem lift_umax' : lift.{max v u, u} = lift.{v, u} :=
  lift_umax
#align ordinal.lift_umax' Ordinal.lift_umax'
-/

/- warning: ordinal.lift_id' -> Ordinal.lift_id' is a dubious translation:
lean 3 declaration is
  forall (a : Ordinal.{max u1 u2}), Eq.{succ (succ (max u1 u2))} Ordinal.{max u1 u2} (Ordinal.lift.{u1, max u1 u2} a) a
but is expected to have type
  forall (a : Ordinal.{max u2 u1}), Eq.{max (succ (succ u2)) (succ (succ u1))} Ordinal.{max u2 u1} (Ordinal.lift.{u2, max u2 u1} a) a
Case conversion may be inaccurate. Consider using '#align ordinal.lift_id' Ordinal.lift_id'ₓ'. -/
/-- An ordinal lifted to a lower or equal universe equals itself. -/
@[simp]
theorem lift_id' (a : Ordinal) : lift a = a :=
  inductionOn a fun α r _ => Quotient.sound ⟨RelIso.preimage Equiv.ulift r⟩
#align ordinal.lift_id' Ordinal.lift_id'

#print Ordinal.lift_id /-
/-- An ordinal lifted to the same universe equals itself. -/
@[simp]
theorem lift_id : ∀ a, lift.{u, u} a = a :=
  lift_id'.{u, u}
#align ordinal.lift_id Ordinal.lift_id
-/

#print Ordinal.lift_uzero /-
/-- An ordinal lifted to the zero universe equals itself. -/
@[simp]
theorem lift_uzero (a : Ordinal.{u}) : lift.{0} a = a :=
  lift_id'.{0, u} a
#align ordinal.lift_uzero Ordinal.lift_uzero
-/

/- warning: ordinal.lift_lift -> Ordinal.lift_lift is a dubious translation:
lean 3 declaration is
  forall (a : Ordinal.{u3}), Eq.{succ (succ (max (max u3 u1) u2))} Ordinal.{max (max u3 u1) u2} (Ordinal.lift.{u2, max u3 u1} (Ordinal.lift.{u1, u3} a)) (Ordinal.lift.{max u1 u2, u3} a)
but is expected to have type
  forall (a : Ordinal.{u1}), Eq.{max (max (succ (succ u2)) (succ (succ u3))) (succ (succ u1))} Ordinal.{max (max u2 u1) u3} (Ordinal.lift.{u3, max u2 u1} (Ordinal.lift.{u2, u1} a)) (Ordinal.lift.{max u2 u3, u1} a)
Case conversion may be inaccurate. Consider using '#align ordinal.lift_lift Ordinal.lift_liftₓ'. -/
@[simp]
theorem lift_lift (a : Ordinal) : lift.{w} (lift.{v} a) = lift.{max v w} a :=
  inductionOn a fun α r _ =>
    Quotient.sound
      ⟨(RelIso.preimage Equiv.ulift _).trans <|
          (RelIso.preimage Equiv.ulift _).trans (RelIso.preimage Equiv.ulift _).symm⟩
#align ordinal.lift_lift Ordinal.lift_lift

#print Ordinal.lift_type_le /-
theorem lift_type_le {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) ≤ lift.{max u w} (type s) ↔ Nonempty (r ≼i s) :=
  ⟨fun ⟨f⟩ =>
    ⟨(InitialSeg.ofIso (RelIso.preimage Equiv.ulift r).symm).trans <|
        f.trans (InitialSeg.ofIso (RelIso.preimage Equiv.ulift s))⟩,
    fun ⟨f⟩ =>
    ⟨(InitialSeg.ofIso (RelIso.preimage Equiv.ulift r)).trans <|
        f.trans (InitialSeg.ofIso (RelIso.preimage Equiv.ulift s).symm)⟩⟩
#align ordinal.lift_type_le Ordinal.lift_type_le
-/

#print Ordinal.lift_type_eq /-
theorem lift_type_eq {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) = lift.{max u w} (type s) ↔ Nonempty (r ≃r s) :=
  Quotient.eq'.trans
    ⟨fun ⟨f⟩ =>
      ⟨(RelIso.preimage Equiv.ulift r).symm.trans <| f.trans (RelIso.preimage Equiv.ulift s)⟩,
      fun ⟨f⟩ =>
      ⟨(RelIso.preimage Equiv.ulift r).trans <| f.trans (RelIso.preimage Equiv.ulift s).symm⟩⟩
#align ordinal.lift_type_eq Ordinal.lift_type_eq
-/

#print Ordinal.lift_type_lt /-
theorem lift_type_lt {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) < lift.{max u w} (type s) ↔ Nonempty (r ≺i s) := by
  haveI :=
        @RelEmbedding.isWellOrder _ _ (@Equiv.ulift.{max v w} α ⁻¹'o r) r
          (RelIso.preimage Equiv.ulift.{max v w} r) _ <;>
      haveI :=
        @RelEmbedding.isWellOrder _ _ (@Equiv.ulift.{max u w} β ⁻¹'o s) s
          (RelIso.preimage Equiv.ulift.{max u w} s) _ <;>
    exact
      ⟨fun ⟨f⟩ =>
        ⟨(f.equivLT (RelIso.preimage Equiv.ulift r).symm).ltLe
            (InitialSeg.ofIso (RelIso.preimage Equiv.ulift s))⟩,
        fun ⟨f⟩ =>
        ⟨(f.equivLT (RelIso.preimage Equiv.ulift r)).ltLe
            (InitialSeg.ofIso (RelIso.preimage Equiv.ulift s).symm)⟩⟩
#align ordinal.lift_type_lt Ordinal.lift_type_lt
-/

#print Ordinal.lift_le /-
@[simp]
theorem lift_le {a b : Ordinal} : lift.{u, v} a ≤ lift b ↔ a ≤ b :=
  inductionOn a fun α r _ =>
    inductionOn b fun β s _ => by
      rw [← lift_umax]
      exact lift_type_le
#align ordinal.lift_le Ordinal.lift_le
-/

/- warning: ordinal.lift_inj -> Ordinal.lift_inj is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, Iff (Eq.{succ (succ (max u1 u2))} Ordinal.{max u1 u2} (Ordinal.lift.{u2, u1} a) (Ordinal.lift.{u2, u1} b)) (Eq.{succ (succ u1)} Ordinal.{u1} a b)
but is expected to have type
  forall {a : Ordinal.{u2}} {b : Ordinal.{u2}}, Iff (Eq.{max (succ (succ u1)) (succ (succ u2))} Ordinal.{max u2 u1} (Ordinal.lift.{u1, u2} a) (Ordinal.lift.{u1, u2} b)) (Eq.{succ (succ u2)} Ordinal.{u2} a b)
Case conversion may be inaccurate. Consider using '#align ordinal.lift_inj Ordinal.lift_injₓ'. -/
@[simp]
theorem lift_inj {a b : Ordinal} : lift a = lift b ↔ a = b := by
  simp only [le_antisymm_iff, lift_le]
#align ordinal.lift_inj Ordinal.lift_inj

/- warning: ordinal.lift_lt -> Ordinal.lift_lt is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, Iff (LT.lt.{succ (max u1 u2)} Ordinal.{max u1 u2} (Preorder.toLT.{succ (max u1 u2)} Ordinal.{max u1 u2} (PartialOrder.toPreorder.{succ (max u1 u2)} Ordinal.{max u1 u2} Ordinal.partialOrder.{max u1 u2})) (Ordinal.lift.{u2, u1} a) (Ordinal.lift.{u2, u1} b)) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) a b)
but is expected to have type
  forall {a : Ordinal.{u2}} {b : Ordinal.{u2}}, Iff (LT.lt.{max (succ u1) (succ u2)} Ordinal.{max u2 u1} (Preorder.toLT.{max (succ u1) (succ u2)} Ordinal.{max u2 u1} (PartialOrder.toPreorder.{max (succ u1) (succ u2)} Ordinal.{max u2 u1} Ordinal.partialOrder.{max u1 u2})) (Ordinal.lift.{u1, u2} a) (Ordinal.lift.{u1, u2} b)) (LT.lt.{succ u2} Ordinal.{u2} (Preorder.toLT.{succ u2} Ordinal.{u2} (PartialOrder.toPreorder.{succ u2} Ordinal.{u2} Ordinal.partialOrder.{u2})) a b)
Case conversion may be inaccurate. Consider using '#align ordinal.lift_lt Ordinal.lift_ltₓ'. -/
@[simp]
theorem lift_lt {a b : Ordinal} : lift a < lift b ↔ a < b := by
  simp only [lt_iff_le_not_le, lift_le]
#align ordinal.lift_lt Ordinal.lift_lt

/- warning: ordinal.lift_zero -> Ordinal.lift_zero is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ (max u1 u2))} Ordinal.{max u1 u2} (Ordinal.lift.{u2, u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) (OfNat.ofNat.{succ (max u1 u2)} Ordinal.{max u1 u2} 0 (OfNat.mk.{succ (max u1 u2)} Ordinal.{max u1 u2} 0 (Zero.zero.{succ (max u1 u2)} Ordinal.{max u1 u2} Ordinal.hasZero.{max u1 u2})))
but is expected to have type
  Eq.{max (succ (succ u2)) (succ (succ u1))} Ordinal.{max u2 u1} (Ordinal.lift.{u1, u2} (OfNat.ofNat.{succ u2} Ordinal.{u2} 0 (Zero.toOfNat0.{succ u2} Ordinal.{u2} Ordinal.zero.{u2}))) (OfNat.ofNat.{max (succ u2) (succ u1)} Ordinal.{max u2 u1} 0 (Zero.toOfNat0.{max (succ u2) (succ u1)} Ordinal.{max u2 u1} Ordinal.zero.{max u2 u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.lift_zero Ordinal.lift_zeroₓ'. -/
@[simp]
theorem lift_zero : lift 0 = 0 :=
  type_eq_zero_of_empty _
#align ordinal.lift_zero Ordinal.lift_zero

/- warning: ordinal.lift_one -> Ordinal.lift_one is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ (max u1 u2))} Ordinal.{max u1 u2} (Ordinal.lift.{u2, u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))) (OfNat.ofNat.{succ (max u1 u2)} Ordinal.{max u1 u2} 1 (OfNat.mk.{succ (max u1 u2)} Ordinal.{max u1 u2} 1 (One.one.{succ (max u1 u2)} Ordinal.{max u1 u2} Ordinal.hasOne.{max u1 u2})))
but is expected to have type
  Eq.{max (succ (succ u2)) (succ (succ u1))} Ordinal.{max u2 u1} (Ordinal.lift.{u1, u2} (OfNat.ofNat.{succ u2} Ordinal.{u2} 1 (One.toOfNat1.{succ u2} Ordinal.{u2} Ordinal.one.{u2}))) (OfNat.ofNat.{max (succ u2) (succ u1)} Ordinal.{max u2 u1} 1 (One.toOfNat1.{max (succ u2) (succ u1)} Ordinal.{max u2 u1} Ordinal.one.{max u2 u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.lift_one Ordinal.lift_oneₓ'. -/
@[simp]
theorem lift_one : lift 1 = 1 :=
  type_eq_one_of_unique _
#align ordinal.lift_one Ordinal.lift_one

/- warning: ordinal.lift_card -> Ordinal.lift_card is a dubious translation:
lean 3 declaration is
  forall (a : Ordinal.{u1}), Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} (Ordinal.card.{u1} a)) (Ordinal.card.{max u1 u2} (Ordinal.lift.{u2, u1} a))
but is expected to have type
  forall (a : Ordinal.{u2}), Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u2 u1} (Cardinal.lift.{u1, u2} (Ordinal.card.{u2} a)) (Ordinal.card.{max u1 u2} (Ordinal.lift.{u1, u2} a))
Case conversion may be inaccurate. Consider using '#align ordinal.lift_card Ordinal.lift_cardₓ'. -/
@[simp]
theorem lift_card (a) : (card a).lift = card (lift a) :=
  inductionOn a fun α r _ => rfl
#align ordinal.lift_card Ordinal.lift_card

#print Ordinal.lift_down' /-
theorem lift_down' {a : Cardinal.{u}} {b : Ordinal.{max u v}} (h : card b ≤ a.lift) :
    ∃ a', lift a' = b :=
  let ⟨c, e⟩ := Cardinal.lift_down h
  Cardinal.inductionOn c
    (fun α =>
      inductionOn b fun β s _ e' => by
        skip
        rw [card_type, ← Cardinal.lift_id'.{max u v, u} (#β), ← Cardinal.lift_umax.{u, v},
          lift_mk_eq.{u, max u v, max u v}] at e'
        cases' e' with f
        have g := RelIso.preimage f s
        haveI := (g : ⇑f ⁻¹'o s ↪r s).IsWellOrder
        have := lift_type_eq.{u, max u v, max u v}.2 ⟨g⟩
        rw [lift_id, lift_umax.{u, v}] at this
        exact ⟨_, this⟩)
    e
#align ordinal.lift_down' Ordinal.lift_down'
-/

#print Ordinal.lift_down /-
theorem lift_down {a : Ordinal.{u}} {b : Ordinal.{max u v}} (h : b ≤ lift a) : ∃ a', lift a' = b :=
  @lift_down' (card a) _ (by rw [lift_card] <;> exact card_le_card h)
#align ordinal.lift_down Ordinal.lift_down
-/

#print Ordinal.le_lift_iff /-
theorem le_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v}} :
    b ≤ lift a ↔ ∃ a', lift a' = b ∧ a' ≤ a :=
  ⟨fun h =>
    let ⟨a', e⟩ := lift_down h
    ⟨a', e, lift_le.1 <| e.symm ▸ h⟩,
    fun ⟨a', e, h⟩ => e ▸ lift_le.2 h⟩
#align ordinal.le_lift_iff Ordinal.le_lift_iff
-/

#print Ordinal.lt_lift_iff /-
theorem lt_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v}} :
    b < lift a ↔ ∃ a', lift a' = b ∧ a' < a :=
  ⟨fun h =>
    let ⟨a', e⟩ := lift_down (le_of_lt h)
    ⟨a', e, lift_lt.1 <| e.symm ▸ h⟩,
    fun ⟨a', e, h⟩ => e ▸ lift_lt.2 h⟩
#align ordinal.lt_lift_iff Ordinal.lt_lift_iff
-/

#print Ordinal.lift.initialSeg /-
/-- Initial segment version of the lift operation on ordinals, embedding `ordinal.{u}` in
  `ordinal.{v}` as an initial segment when `u ≤ v`. -/
def lift.initialSeg : @InitialSeg Ordinal.{u} Ordinal.{max u v} (· < ·) (· < ·) :=
  ⟨⟨⟨lift.{v}, fun a b => lift_inj.1⟩, fun a b => lift_lt⟩, fun a b h => lift_down (le_of_lt h)⟩
#align ordinal.lift.initial_seg Ordinal.lift.initialSeg
-/

/- warning: ordinal.lift.initial_seg_coe -> Ordinal.lift.initialSeg_coe is a dubious translation:
lean 3 declaration is
  Eq.{max (succ (succ u1)) (succ (succ (max u1 u2)))} ((fun (_x : InitialSeg.{succ u1, succ (max u1 u2)} Ordinal.{u1} Ordinal.{max u1 u2} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}))) (LT.lt.{succ (max u1 u2)} Ordinal.{max u1 u2} (Preorder.toLT.{succ (max u1 u2)} Ordinal.{max u1 u2} (PartialOrder.toPreorder.{succ (max u1 u2)} Ordinal.{max u1 u2} Ordinal.partialOrder.{max u1 u2})))) => Ordinal.{u1} -> Ordinal.{max u1 u2}) Ordinal.lift.initialSeg.{u1, u2}) (coeFn.{max (succ (succ u1)) (succ (succ (max u1 u2))), max (succ (succ u1)) (succ (succ (max u1 u2)))} (InitialSeg.{succ u1, succ (max u1 u2)} Ordinal.{u1} Ordinal.{max u1 u2} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}))) (LT.lt.{succ (max u1 u2)} Ordinal.{max u1 u2} (Preorder.toLT.{succ (max u1 u2)} Ordinal.{max u1 u2} (PartialOrder.toPreorder.{succ (max u1 u2)} Ordinal.{max u1 u2} Ordinal.partialOrder.{max u1 u2})))) (fun (_x : InitialSeg.{succ u1, succ (max u1 u2)} Ordinal.{u1} Ordinal.{max u1 u2} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}))) (LT.lt.{succ (max u1 u2)} Ordinal.{max u1 u2} (Preorder.toLT.{succ (max u1 u2)} Ordinal.{max u1 u2} (PartialOrder.toPreorder.{succ (max u1 u2)} Ordinal.{max u1 u2} Ordinal.partialOrder.{max u1 u2})))) => Ordinal.{u1} -> Ordinal.{max u1 u2}) (FunLike.hasCoeToFun.{max (succ (succ u1)) (succ (succ (max u1 u2))), succ (succ u1), succ (succ (max u1 u2))} (InitialSeg.{succ u1, succ (max u1 u2)} Ordinal.{u1} Ordinal.{max u1 u2} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}))) (LT.lt.{succ (max u1 u2)} Ordinal.{max u1 u2} (Preorder.toLT.{succ (max u1 u2)} Ordinal.{max u1 u2} (PartialOrder.toPreorder.{succ (max u1 u2)} Ordinal.{max u1 u2} Ordinal.partialOrder.{max u1 u2})))) Ordinal.{u1} (fun (_x : Ordinal.{u1}) => Ordinal.{max u1 u2}) (EmbeddingLike.toFunLike.{max (succ (succ u1)) (succ (succ (max u1 u2))), succ (succ u1), succ (succ (max u1 u2))} (InitialSeg.{succ u1, succ (max u1 u2)} Ordinal.{u1} Ordinal.{max u1 u2} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}))) (LT.lt.{succ (max u1 u2)} Ordinal.{max u1 u2} (Preorder.toLT.{succ (max u1 u2)} Ordinal.{max u1 u2} (PartialOrder.toPreorder.{succ (max u1 u2)} Ordinal.{max u1 u2} Ordinal.partialOrder.{max u1 u2})))) Ordinal.{u1} Ordinal.{max u1 u2} (InitialSeg.embeddingLike.{succ u1, succ (max u1 u2)} Ordinal.{u1} Ordinal.{max u1 u2} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}))) (LT.lt.{succ (max u1 u2)} Ordinal.{max u1 u2} (Preorder.toLT.{succ (max u1 u2)} Ordinal.{max u1 u2} (PartialOrder.toPreorder.{succ (max u1 u2)} Ordinal.{max u1 u2} Ordinal.partialOrder.{max u1 u2})))))) Ordinal.lift.initialSeg.{u1, u2}) Ordinal.lift.{u2, u1}
but is expected to have type
  Eq.{max (succ (succ u1)) (succ (succ u2))} (forall (a : Ordinal.{u1}), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Ordinal.{u1}) => Ordinal.{max u1 u2}) a) (FunLike.coe.{max (succ (succ u1)) (succ (succ u2)), succ (succ u1), max (succ (succ u1)) (succ (succ u2))} (InitialSeg.{succ u1, max (succ u1) (succ u2)} Ordinal.{u1} Ordinal.{max u1 u2} (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8469 : Ordinal.{u1}) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8471 : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8469 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8471) (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8484 : Ordinal.{max u1 u2}) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8486 : Ordinal.{max u1 u2}) => LT.lt.{max (succ u1) (succ u2)} Ordinal.{max u1 u2} (Preorder.toLT.{max (succ u1) (succ u2)} Ordinal.{max u1 u2} (PartialOrder.toPreorder.{max (succ u1) (succ u2)} Ordinal.{max u1 u2} Ordinal.partialOrder.{max u1 u2})) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8484 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8486)) Ordinal.{u1} (fun (_x : Ordinal.{u1}) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Ordinal.{u1}) => Ordinal.{max u1 u2}) _x) (EmbeddingLike.toFunLike.{max (succ (succ u1)) (succ (succ u2)), succ (succ u1), max (succ (succ u1)) (succ (succ u2))} (InitialSeg.{succ u1, max (succ u1) (succ u2)} Ordinal.{u1} Ordinal.{max u1 u2} (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8469 : Ordinal.{u1}) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8471 : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8469 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8471) (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8484 : Ordinal.{max u1 u2}) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8486 : Ordinal.{max u1 u2}) => LT.lt.{max (succ u1) (succ u2)} Ordinal.{max u1 u2} (Preorder.toLT.{max (succ u1) (succ u2)} Ordinal.{max u1 u2} (PartialOrder.toPreorder.{max (succ u1) (succ u2)} Ordinal.{max u1 u2} Ordinal.partialOrder.{max u1 u2})) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8484 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8486)) Ordinal.{u1} Ordinal.{max u1 u2} (InitialSeg.instEmbeddingLikeInitialSeg.{succ u1, max (succ u1) (succ u2)} Ordinal.{u1} Ordinal.{max u1 u2} (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8469 : Ordinal.{u1}) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8471 : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8469 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8471) (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8484 : Ordinal.{max u1 u2}) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8486 : Ordinal.{max u1 u2}) => LT.lt.{max (succ u1) (succ u2)} Ordinal.{max u1 u2} (Preorder.toLT.{max (succ u1) (succ u2)} Ordinal.{max u1 u2} (PartialOrder.toPreorder.{max (succ u1) (succ u2)} Ordinal.{max u1 u2} Ordinal.partialOrder.{max u1 u2})) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8484 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.8486))) Ordinal.lift.initialSeg.{u1, u2}) Ordinal.lift.{u2, u1}
Case conversion may be inaccurate. Consider using '#align ordinal.lift.initial_seg_coe Ordinal.lift.initialSeg_coeₓ'. -/
@[simp]
theorem lift.initialSeg_coe : (lift.initialSeg : Ordinal → Ordinal) = lift :=
  rfl
#align ordinal.lift.initial_seg_coe Ordinal.lift.initialSeg_coe

/-! ### The first infinite ordinal `omega` -/


#print Ordinal.omega /-
/-- `ω` is the first infinite ordinal, defined as the order type of `ℕ`. -/
def omega : Ordinal.{u} :=
  lift <| @type ℕ (· < ·) _
#align ordinal.omega Ordinal.omega
-/

-- mathport name: ordinal.omega
scoped notation "ω" => Ordinal.omega

#print Ordinal.type_nat_lt /-
/-- Note that the presence of this lemma makes `simp [omega]` form a loop. -/
@[simp]
theorem type_nat_lt : @type ℕ (· < ·) _ = ω :=
  (lift_id _).symm
#align ordinal.type_nat_lt Ordinal.type_nat_lt
-/

#print Ordinal.card_omega /-
@[simp]
theorem card_omega : card ω = ℵ₀ :=
  rfl
#align ordinal.card_omega Ordinal.card_omega
-/

#print Ordinal.lift_omega /-
@[simp]
theorem lift_omega : lift ω = ω :=
  lift_lift _
#align ordinal.lift_omega Ordinal.lift_omega
-/

/-!
### Definition and first properties of addition on ordinals

In this paragraph, we introduce the addition on ordinals, and prove just enough properties to
deduce that the order on ordinals is total (and therefore well-founded). Further properties of
the addition, together with properties of the other operations, are proved in
`ordinal_arithmetic.lean`.
-/


/-- `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`. -/
instance : Add Ordinal.{u} :=
  ⟨fun o₁ o₂ =>
    Quotient.liftOn₂ o₁ o₂ (fun ⟨α, r, wo⟩ ⟨β, s, wo'⟩ => type (Sum.Lex r s))
      fun ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩ =>
      Quot.sound ⟨RelIso.sumLexCongr f g⟩⟩

instance : AddMonoidWithOne Ordinal.{u}
    where
  add := (· + ·)
  zero := 0
  one := 1
  zero_add o :=
    inductionOn o fun α r _ =>
      Eq.symm <| Quotient.sound ⟨⟨(emptySum PEmpty α).symm, fun a b => Sum.lex_inr_inr⟩⟩
  add_zero o :=
    inductionOn o fun α r _ =>
      Eq.symm <| Quotient.sound ⟨⟨(sumEmpty α PEmpty).symm, fun a b => Sum.lex_inl_inl⟩⟩
  add_assoc o₁ o₂ o₃ :=
    Quotient.induction_on₃ o₁ o₂ o₃ fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ =>
      Quot.sound
        ⟨⟨sumAssoc _ _ _, fun a b => by
            rcases a with (⟨a | a⟩ | a) <;> rcases b with (⟨b | b⟩ | b) <;>
              simp only [sum_assoc_apply_inl_inl, sum_assoc_apply_inl_inr, sum_assoc_apply_inr,
                Sum.lex_inl_inl, Sum.lex_inr_inr, Sum.Lex.sep, Sum.lex_inr_inl]⟩⟩

/- warning: ordinal.card_add -> Ordinal.card_add is a dubious translation:
lean 3 declaration is
  forall (o₁ : Ordinal.{u1}) (o₂ : Ordinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (Ordinal.card.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) o₁ o₂)) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) (Ordinal.card.{u1} o₁) (Ordinal.card.{u1} o₂))
but is expected to have type
  forall (o₁ : Ordinal.{u1}) (o₂ : Ordinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (Ordinal.card.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.add.{u1}) o₁ o₂)) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (Ordinal.card.{u1} o₁) (Ordinal.card.{u1} o₂))
Case conversion may be inaccurate. Consider using '#align ordinal.card_add Ordinal.card_addₓ'. -/
@[simp]
theorem card_add (o₁ o₂ : Ordinal) : card (o₁ + o₂) = card o₁ + card o₂ :=
  inductionOn o₁ fun α r _ => inductionOn o₂ fun β s _ => rfl
#align ordinal.card_add Ordinal.card_add

#print Ordinal.type_sum_lex /-
@[simp]
theorem type_sum_lex {α β : Type u} (r : α → α → Prop) (s : β → β → Prop) [IsWellOrder α r]
    [IsWellOrder β s] : type (Sum.Lex r s) = type r + type s :=
  rfl
#align ordinal.type_sum_lex Ordinal.type_sum_lex
-/

/- warning: ordinal.card_nat -> Ordinal.card_nat is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} (Ordinal.card.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Ordinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Ordinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Ordinal.{u1} (Nat.castCoe.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1})))) n)) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)
but is expected to have type
  forall (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} (Ordinal.card.{u1} (Nat.cast.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1}) n)) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)
Case conversion may be inaccurate. Consider using '#align ordinal.card_nat Ordinal.card_natₓ'. -/
@[simp]
theorem card_nat (n : ℕ) : card.{u} n = n := by
  induction n <;> [rfl, simp only [card_add, card_one, Nat.cast_succ, *]]
#align ordinal.card_nat Ordinal.card_nat

#print Ordinal.add_covariantClass_le /-
instance add_covariantClass_le : CovariantClass Ordinal.{u} Ordinal.{u} (· + ·) (· ≤ ·) :=
  ⟨fun c a b h => by revert h c;
    exact
      induction_on a fun α₁ r₁ _ =>
        induction_on b fun α₂ r₂ _ ⟨⟨⟨f, fo⟩, fi⟩⟩ c =>
          induction_on c fun β s _ =>
            ⟨⟨⟨(embedding.refl _).sum_map f, fun a b =>
                  match a, b with
                  | Sum.inl a, Sum.inl b => sum.lex_inl_inl.trans sum.lex_inl_inl.symm
                  | Sum.inl a, Sum.inr b => by apply iff_of_true <;> apply Sum.Lex.sep
                  | Sum.inr a, Sum.inl b => by apply iff_of_false <;> exact Sum.lex_inr_inl
                  | Sum.inr a, Sum.inr b => sum.lex_inr_inr.trans <| fo.trans sum.lex_inr_inr.symm⟩,
                fun a b H =>
                match a, b, H with
                | _, Sum.inl b, _ => ⟨Sum.inl b, rfl⟩
                | Sum.inl a, Sum.inr b, H => (Sum.lex_inr_inl H).elim
                | Sum.inr a, Sum.inr b, H =>
                  let ⟨w, h⟩ := fi _ _ (Sum.lex_inr_inr.1 H)
                  ⟨Sum.inr w, congr_arg Sum.inr h⟩⟩⟩⟩
#align ordinal.add_covariant_class_le Ordinal.add_covariantClass_le
-/

#print Ordinal.add_swap_covariantClass_le /-
instance add_swap_covariantClass_le :
    CovariantClass Ordinal.{u} Ordinal.{u} (swap (· + ·)) (· ≤ ·) :=
  ⟨fun c a b h => by revert h c;
    exact
      induction_on a fun α₁ r₁ hr₁ =>
        induction_on b fun α₂ r₂ hr₂ ⟨⟨⟨f, fo⟩, fi⟩⟩ c =>
          induction_on c fun β s hs =>
            @RelEmbedding.ordinal_type_le _ _ (Sum.Lex r₁ s) (Sum.Lex r₂ s) _ _
              ⟨f.sum_map (embedding.refl _), fun a b =>
                by
                constructor <;> intro H
                ·
                  cases' a with a a <;> cases' b with b b <;> cases H <;> constructor <;>
                    [rwa [← fo], assumption]
                · cases H <;> constructor <;> [rwa [fo], assumption]⟩⟩
#align ordinal.add_swap_covariant_class_le Ordinal.add_swap_covariantClass_le
-/

#print Ordinal.le_add_right /-
theorem le_add_right (a b : Ordinal) : a ≤ a + b := by
  simpa only [add_zero] using add_le_add_left (Ordinal.zero_le b) a
#align ordinal.le_add_right Ordinal.le_add_right
-/

#print Ordinal.le_add_left /-
theorem le_add_left (a b : Ordinal) : a ≤ b + a := by
  simpa only [zero_add] using add_le_add_right (Ordinal.zero_le b) a
#align ordinal.le_add_left Ordinal.le_add_left
-/

instance : LinearOrder Ordinal :=
  {
    Ordinal.partialOrder with
    le_total := fun a b =>
      match lt_or_eq_of_le (le_add_left b a), lt_or_eq_of_le (le_add_right a b) with
      | Or.inr h, _ => by rw [h] <;> exact Or.inl (le_add_right _ _)
      | _, Or.inr h => by rw [h] <;> exact Or.inr (le_add_left _ _)
      | Or.inl h₁, Or.inl h₂ =>
        inductionOn a
          (fun α₁ r₁ _ =>
            inductionOn b fun α₂ r₂ _ ⟨f⟩ ⟨g⟩ => by
              skip
              rw [← typein_top f, ← typein_top g, le_iff_lt_or_eq, le_iff_lt_or_eq,
                typein_lt_typein, typein_lt_typein]
              rcases trichotomous_of (Sum.Lex r₁ r₂) g.top f.top with (h | h | h) <;>
                [exact Or.inl (Or.inl h),
                · left
                  right
                  rw [h], exact Or.inr (Or.inl h)])
          h₁ h₂
    decidableLe := Classical.decRel _ }

instance : WellFoundedLT Ordinal :=
  ⟨lt_wf⟩

instance : IsWellOrder Ordinal (· < ·) where

instance : ConditionallyCompleteLinearOrderBot Ordinal :=
  IsWellOrder.conditionallyCompleteLinearOrderBot _

/- warning: ordinal.max_zero_left -> Ordinal.max_zero_left is a dubious translation:
lean 3 declaration is
  forall (a : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (LinearOrder.max.{succ u1} Ordinal.{u1} Ordinal.linearOrder.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) a) a
but is expected to have type
  forall (a : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Max.max.{succ u1} Ordinal.{u1} (LinearOrder.toMax.{succ u1} Ordinal.{u1} Ordinal.linearOrder.{u1}) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) a) a
Case conversion may be inaccurate. Consider using '#align ordinal.max_zero_left Ordinal.max_zero_leftₓ'. -/
@[simp]
theorem max_zero_left : ∀ a : Ordinal, max 0 a = a :=
  max_bot_left
#align ordinal.max_zero_left Ordinal.max_zero_left

/- warning: ordinal.max_zero_right -> Ordinal.max_zero_right is a dubious translation:
lean 3 declaration is
  forall (a : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (LinearOrder.max.{succ u1} Ordinal.{u1} Ordinal.linearOrder.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) a
but is expected to have type
  forall (a : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Max.max.{succ u1} Ordinal.{u1} (LinearOrder.toMax.{succ u1} Ordinal.{u1} Ordinal.linearOrder.{u1}) a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1}))) a
Case conversion may be inaccurate. Consider using '#align ordinal.max_zero_right Ordinal.max_zero_rightₓ'. -/
@[simp]
theorem max_zero_right : ∀ a : Ordinal, max a 0 = a :=
  max_bot_right
#align ordinal.max_zero_right Ordinal.max_zero_right

/- warning: ordinal.max_eq_zero -> Ordinal.max_eq_zero is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, Iff (Eq.{succ (succ u1)} Ordinal.{u1} (LinearOrder.max.{succ u1} Ordinal.{u1} Ordinal.linearOrder.{u1} a b) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) (And (Eq.{succ (succ u1)} Ordinal.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) (Eq.{succ (succ u1)} Ordinal.{u1} b (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))))
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, Iff (Eq.{succ (succ u1)} Ordinal.{u1} (Max.max.{succ u1} Ordinal.{u1} (LinearOrder.toMax.{succ u1} Ordinal.{u1} Ordinal.linearOrder.{u1}) a b) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1}))) (And (Eq.{succ (succ u1)} Ordinal.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1}))) (Eq.{succ (succ u1)} Ordinal.{u1} b (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1}))))
Case conversion may be inaccurate. Consider using '#align ordinal.max_eq_zero Ordinal.max_eq_zeroₓ'. -/
@[simp]
theorem max_eq_zero {a b : Ordinal} : max a b = 0 ↔ a = 0 ∧ b = 0 :=
  max_eq_bot
#align ordinal.max_eq_zero Ordinal.max_eq_zero

/- warning: ordinal.Inf_empty -> Ordinal.infₛ_empty is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Ordinal.{u1} (InfSet.infₛ.{succ u1} Ordinal.{u1} (ConditionallyCompleteLattice.toHasInf.{succ u1} Ordinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Ordinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Ordinal.{u1} Ordinal.conditionallyCompleteLinearOrderBot.{u1}))) (EmptyCollection.emptyCollection.{succ u1} (Set.{succ u1} Ordinal.{u1}) (Set.hasEmptyc.{succ u1} Ordinal.{u1}))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))
but is expected to have type
  Eq.{succ (succ u1)} Ordinal.{u1} (InfSet.infₛ.{succ u1} Ordinal.{u1} (ConditionallyCompleteLattice.toInfSet.{succ u1} Ordinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Ordinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Ordinal.{u1} Ordinal.instConditionallyCompleteLinearOrderBotOrdinal.{u1}))) (EmptyCollection.emptyCollection.{succ u1} (Set.{succ u1} Ordinal.{u1}) (Set.instEmptyCollectionSet.{succ u1} Ordinal.{u1}))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.Inf_empty Ordinal.infₛ_emptyₓ'. -/
@[simp]
theorem infₛ_empty : infₛ (∅ : Set Ordinal) = 0 :=
  dif_neg not_nonempty_empty
#align ordinal.Inf_empty Ordinal.infₛ_empty

-- ### Successor order properties
private theorem succ_le_iff' {a b : Ordinal} : a + 1 ≤ b ↔ a < b :=
  ⟨lt_of_lt_of_le
      (inductionOn a fun α r _ =>
        ⟨⟨⟨⟨fun x => Sum.inl x, fun _ _ => Sum.inl.inj⟩, fun _ _ => Sum.lex_inl_inl⟩,
            Sum.inr PUnit.unit, fun b =>
            Sum.recOn b (fun x => ⟨fun _ => ⟨x, rfl⟩, fun _ => Sum.Lex.sep _ _⟩) fun x =>
              Sum.lex_inr_inr.trans ⟨False.elim, fun ⟨x, H⟩ => Sum.inl_ne_inr H⟩⟩⟩),
    inductionOn a fun α r hr =>
      inductionOn b fun β s hs ⟨⟨f, t, hf⟩⟩ => by
        haveI := hs
        refine'
          ⟨⟨@RelEmbedding.ofMonotone (Sum α PUnit) β _ _ _ _ (Sum.rec _ _) fun a b => _, fun a b =>
              _⟩⟩
        · exact f; · exact fun _ => t
        · rcases a with (a | _) <;> rcases b with (b | _)
          · simpa only [Sum.lex_inl_inl] using f.map_rel_iff.2
          · intro
            rw [hf]
            exact ⟨_, rfl⟩
          · exact False.elim ∘ Sum.lex_inr_inl
          · exact False.elim ∘ Sum.lex_inr_inr.1
        · rcases a with (a | _)
          · intro h
            have := @PrincipalSeg.init _ _ _ _ _ ⟨f, t, hf⟩ _ _ h
            cases' this with w h
            exact ⟨Sum.inl w, h⟩
          · intro h
            cases' (hf b).1 h with w h
            exact ⟨Sum.inl w, h⟩⟩
#align ordinal.succ_le_iff' ordinal.succ_le_iff'

instance : NoMaxOrder Ordinal :=
  ⟨fun a => ⟨_, succ_le_iff'.1 le_rfl⟩⟩

instance : SuccOrder Ordinal.{u} :=
  SuccOrder.ofSuccLeIff (fun o => o + 1) fun a b => succ_le_iff'

/- warning: ordinal.add_one_eq_succ -> Ordinal.add_one_eq_succ is a dubious translation:
lean 3 declaration is
  forall (o : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) o (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))) (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} o)
but is expected to have type
  forall (o : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.add.{u1}) o (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))) (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} o)
Case conversion may be inaccurate. Consider using '#align ordinal.add_one_eq_succ Ordinal.add_one_eq_succₓ'. -/
@[simp]
theorem add_one_eq_succ (o : Ordinal) : o + 1 = succ o :=
  rfl
#align ordinal.add_one_eq_succ Ordinal.add_one_eq_succ

/- warning: ordinal.succ_zero -> Ordinal.succ_zero is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Ordinal.{u1} (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))
but is expected to have type
  Eq.{succ (succ u1)} Ordinal.{u1} (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1}))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.succ_zero Ordinal.succ_zeroₓ'. -/
@[simp]
theorem succ_zero : succ (0 : Ordinal) = 1 :=
  zero_add 1
#align ordinal.succ_zero Ordinal.succ_zero

/- warning: ordinal.succ_one -> Ordinal.succ_one is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Ordinal.{u1} (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 2 (OfNat.mk.{succ u1} Ordinal.{u1} 2 (bit0.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1} (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))
but is expected to have type
  Eq.{succ (succ u1)} Ordinal.{u1} (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 2 (instOfNat.{succ u1} Ordinal.{u1} 2 (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1}) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align ordinal.succ_one Ordinal.succ_oneₓ'. -/
@[simp]
theorem succ_one : succ (1 : Ordinal) = 2 :=
  rfl
#align ordinal.succ_one Ordinal.succ_one

#print Ordinal.add_succ /-
theorem add_succ (o₁ o₂ : Ordinal) : o₁ + succ o₂ = succ (o₁ + o₂) :=
  (add_assoc _ _ _).symm
#align ordinal.add_succ Ordinal.add_succ
-/

/- warning: ordinal.one_le_iff_pos -> Ordinal.one_le_iff_pos is a dubious translation:
lean 3 declaration is
  forall {o : Ordinal.{u1}}, Iff (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) o) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) o)
but is expected to have type
  forall {o : Ordinal.{u1}}, Iff (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})) o) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) o)
Case conversion may be inaccurate. Consider using '#align ordinal.one_le_iff_pos Ordinal.one_le_iff_posₓ'. -/
theorem one_le_iff_pos {o : Ordinal} : 1 ≤ o ↔ 0 < o := by rw [← succ_zero, succ_le_iff]
#align ordinal.one_le_iff_pos Ordinal.one_le_iff_pos

/- warning: ordinal.one_le_iff_ne_zero -> Ordinal.one_le_iff_ne_zero is a dubious translation:
lean 3 declaration is
  forall {o : Ordinal.{u1}}, Iff (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) o) (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))))
but is expected to have type
  forall {o : Ordinal.{u1}}, Iff (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})) o) (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})))
Case conversion may be inaccurate. Consider using '#align ordinal.one_le_iff_ne_zero Ordinal.one_le_iff_ne_zeroₓ'. -/
theorem one_le_iff_ne_zero {o : Ordinal} : 1 ≤ o ↔ o ≠ 0 := by
  rw [one_le_iff_pos, Ordinal.pos_iff_ne_zero]
#align ordinal.one_le_iff_ne_zero Ordinal.one_le_iff_ne_zero

#print Ordinal.succ_pos /-
theorem succ_pos (o : Ordinal) : 0 < succ o :=
  bot_lt_succ o
#align ordinal.succ_pos Ordinal.succ_pos
-/

#print Ordinal.succ_ne_zero /-
theorem succ_ne_zero (o : Ordinal) : succ o ≠ 0 :=
  ne_of_gt <| succ_pos o
#align ordinal.succ_ne_zero Ordinal.succ_ne_zero
-/

/- warning: ordinal.lt_one_iff_zero -> Ordinal.lt_one_iff_zero is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}}, Iff (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) a (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))) (Eq.{succ (succ u1)} Ordinal.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))))
but is expected to have type
  forall {a : Ordinal.{u1}}, Iff (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) a (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))) (Eq.{succ (succ u1)} Ordinal.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})))
Case conversion may be inaccurate. Consider using '#align ordinal.lt_one_iff_zero Ordinal.lt_one_iff_zeroₓ'. -/
theorem lt_one_iff_zero {a : Ordinal} : a < 1 ↔ a = 0 := by simpa using @lt_succ_bot_iff _ _ _ a _ _
#align ordinal.lt_one_iff_zero Ordinal.lt_one_iff_zero

/- warning: ordinal.le_one_iff -> Ordinal.le_one_iff is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}}, Iff (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) a (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))) (Or (Eq.{succ (succ u1)} Ordinal.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) (Eq.{succ (succ u1)} Ordinal.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))))
but is expected to have type
  forall {a : Ordinal.{u1}}, Iff (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) a (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))) (Or (Eq.{succ (succ u1)} Ordinal.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1}))) (Eq.{succ (succ u1)} Ordinal.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))))
Case conversion may be inaccurate. Consider using '#align ordinal.le_one_iff Ordinal.le_one_iffₓ'. -/
theorem le_one_iff {a : Ordinal} : a ≤ 1 ↔ a = 0 ∨ a = 1 := by
  simpa using @le_succ_bot_iff _ _ _ a _
#align ordinal.le_one_iff Ordinal.le_one_iff

/- warning: ordinal.card_succ -> Ordinal.card_succ is a dubious translation:
lean 3 declaration is
  forall (o : Ordinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (Ordinal.card.{u1} (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} o)) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) (Ordinal.card.{u1} o) (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (OfNat.mk.{succ u1} Cardinal.{u1} 1 (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1}))))
but is expected to have type
  forall (o : Ordinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (Ordinal.card.{u1} (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} o)) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (Ordinal.card.{u1} o) (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (One.toOfNat1.{succ u1} Cardinal.{u1} Cardinal.instOneCardinal.{u1})))
Case conversion may be inaccurate. Consider using '#align ordinal.card_succ Ordinal.card_succₓ'. -/
@[simp]
theorem card_succ (o : Ordinal) : card (succ o) = card o + 1 := by
  simp only [← add_one_eq_succ, card_add, card_one]
#align ordinal.card_succ Ordinal.card_succ

#print Ordinal.nat_cast_succ /-
theorem nat_cast_succ (n : ℕ) : ↑n.succ = succ (n : Ordinal) :=
  rfl
#align ordinal.nat_cast_succ Ordinal.nat_cast_succ
-/

/- warning: ordinal.unique_Iio_one -> Ordinal.uniqueIioOne is a dubious translation:
lean 3 declaration is
  Unique.{succ (succ u1)} (coeSort.{succ (succ u1), succ (succ (succ u1))} (Set.{succ u1} Ordinal.{u1}) Type.{succ u1} (Set.hasCoeToSort.{succ u1} Ordinal.{u1}) (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))))
but is expected to have type
  Unique.{succ (succ u1)} (Set.Elem.{succ u1} Ordinal.{u1} (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))))
Case conversion may be inaccurate. Consider using '#align ordinal.unique_Iio_one Ordinal.uniqueIioOneₓ'. -/
instance uniqueIioOne : Unique (Iio (1 : Ordinal))
    where
  default := ⟨0, zero_lt_one⟩
  uniq a := Subtype.ext <| lt_one_iff_zero.1 a.Prop
#align ordinal.unique_Iio_one Ordinal.uniqueIioOne

/- warning: ordinal.unique_out_one -> Ordinal.uniqueOutOne is a dubious translation:
lean 3 declaration is
  Unique.{succ u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))))
but is expected to have type
  Unique.{succ u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))))
Case conversion may be inaccurate. Consider using '#align ordinal.unique_out_one Ordinal.uniqueOutOneₓ'. -/
instance uniqueOutOne : Unique (1 : Ordinal).out.α
    where
  default := enum (· < ·) 0 (by simp)
  uniq a := by
    rw [← enum_typein (· < ·) a]
    unfold default
    congr
    rw [← lt_one_iff_zero]
    apply typein_lt_self
#align ordinal.unique_out_one Ordinal.uniqueOutOne

/- warning: ordinal.one_out_eq -> Ordinal.one_out_eq is a dubious translation:
lean 3 declaration is
  forall (x : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))), Eq.{succ u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) x (Ordinal.enum.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (LinearOrder.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (linearOrderOut.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))))))))) (isWellOrder_out_lt.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (Eq.mpr.{0} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (Ordinal.type.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (LinearOrder.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (linearOrderOut.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))))))))) (isWellOrder_out_lt.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))))) True (id_tag Tactic.IdTag.simp (Eq.{1} Prop (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (Ordinal.type.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (LinearOrder.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (linearOrderOut.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))))))))) (isWellOrder_out_lt.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))))) True) (Eq.trans.{1} Prop (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (Ordinal.type.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (LinearOrder.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (linearOrderOut.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))))))))) (isWellOrder_out_lt.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))) True ((fun [self : LT.{succ u1} Ordinal.{u1}] (ᾰ : Ordinal.{u1}) (ᾰ_1 : Ordinal.{u1}) (e_2 : Eq.{succ (succ u1)} Ordinal.{u1} ᾰ ᾰ_1) (ᾰ_2 : Ordinal.{u1}) (ᾰ_3 : Ordinal.{u1}) (e_3 : Eq.{succ (succ u1)} Ordinal.{u1} ᾰ_2 ᾰ_3) => congr.{succ (succ u1), 1} Ordinal.{u1} Prop (LT.lt.{succ u1} Ordinal.{u1} self ᾰ) (LT.lt.{succ u1} Ordinal.{u1} self ᾰ_1) ᾰ_2 ᾰ_3 (congr_arg.{succ (succ u1), succ (succ u1)} Ordinal.{u1} (Ordinal.{u1} -> Prop) ᾰ ᾰ_1 (LT.lt.{succ u1} Ordinal.{u1} self) e_2) e_3) (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (rfl.{succ (succ u1)} Ordinal.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) (Ordinal.type.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (LinearOrder.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (linearOrderOut.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))))))))) (isWellOrder_out_lt.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) (Ordinal.type_lt.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (propext (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))) True ((fun {α : Type.{succ u1}} [_inst_1 : Zero.{succ u1} α] [_inst_2 : One.{succ u1} α] [_inst_3 : PartialOrder.{succ u1} α] [_inst_4 : ZeroLEOneClass.{succ u1} α _inst_1 _inst_2 (Preorder.toLE.{succ u1} α (PartialOrder.toPreorder.{succ u1} α _inst_3))] [_inst_5 : NeZero.{succ u1} α _inst_1 (OfNat.ofNat.{succ u1} α 1 (OfNat.mk.{succ u1} α 1 (One.one.{succ u1} α _inst_2)))] => iff_true_intro (LT.lt.{succ u1} α (Preorder.toLT.{succ u1} α (PartialOrder.toPreorder.{succ u1} α _inst_3)) (OfNat.ofNat.{succ u1} α 0 (OfNat.mk.{succ u1} α 0 (Zero.zero.{succ u1} α _inst_1))) (OfNat.ofNat.{succ u1} α 1 (OfNat.mk.{succ u1} α 1 (One.one.{succ u1} α _inst_2)))) (zero_lt_one.{succ u1} α _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)) Ordinal.{u1} Ordinal.hasZero.{u1} Ordinal.hasOne.{u1} Ordinal.partialOrder.{u1} Ordinal.zeroLeOneClass.{u1} Ordinal.NeZero.one.{u1})))) trivial))
but is expected to have type
  forall (x : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))), Eq.{succ u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) x (Ordinal.enum.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.12708 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.12710 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) => LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (DistribLattice.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (instDistribLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (linearOrderOut.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))))))))) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.12708 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.12710) (isWellOrder_out_lt.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) (of_eq_true (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) (Ordinal.type.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.1293 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.1295 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) => LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (DistribLattice.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (instDistribLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (linearOrderOut.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))))))))) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.1293 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.1295) (isWellOrder_out_lt.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))))) (Eq.trans.{1} Prop (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) (Ordinal.type.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.1293 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.1295 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) => LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (DistribLattice.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (instDistribLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (linearOrderOut.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))))))))) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.1293 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.1295) (isWellOrder_out_lt.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))) True (congrArg.{succ (succ u1), 1} Ordinal.{u1} Prop (Ordinal.type.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.1293 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.1295 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) => LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (DistribLattice.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (instDistribLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (linearOrderOut.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))))))))) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.1293 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.1295) (isWellOrder_out_lt.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1}))) (Ordinal.type_lt.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (Mathlib.Algebra.Order.ZeroLEOne._auxLemma.2.{succ u1} Ordinal.{u1} Ordinal.zero.{u1} Ordinal.one.{u1} Ordinal.partialOrder.{u1} Ordinal.zeroLEOneClass.{u1} Ordinal.NeZero.one.{u1}))))
Case conversion may be inaccurate. Consider using '#align ordinal.one_out_eq Ordinal.one_out_eqₓ'. -/
theorem one_out_eq (x : (1 : Ordinal).out.α) : x = enum (· < ·) 0 (by simp) :=
  Unique.eq_default x
#align ordinal.one_out_eq Ordinal.one_out_eq

/-! ### Extra properties of typein and enum -/


/- warning: ordinal.typein_one_out -> Ordinal.typein_one_out is a dubious translation:
lean 3 declaration is
  forall (x : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.typein.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (LinearOrder.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))) (linearOrderOut.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))))))))) (isWellOrder_out_lt.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))) x) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))
but is expected to have type
  forall (x : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.typein.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.12763 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.12765 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) => LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (DistribLattice.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (instDistribLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))) (linearOrderOut.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))))))))) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.12763 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.12765) (isWellOrder_out_lt.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))) x) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.typein_one_out Ordinal.typein_one_outₓ'. -/
@[simp]
theorem typein_one_out (x : (1 : Ordinal).out.α) : typein (· < ·) x = 0 := by
  rw [one_out_eq x, typein_enum]
#align ordinal.typein_one_out Ordinal.typein_one_out

#print Ordinal.typein_le_typein /-
@[simp]
theorem typein_le_typein (r : α → α → Prop) [IsWellOrder α r] {x x' : α} :
    typein r x ≤ typein r x' ↔ ¬r x' x := by rw [← not_lt, typein_lt_typein]
#align ordinal.typein_le_typein Ordinal.typein_le_typein
-/

#print Ordinal.typein_le_typein' /-
@[simp]
theorem typein_le_typein' (o : Ordinal) {x x' : o.out.α} :
    typein (· < ·) x ≤ typein (· < ·) x' ↔ x ≤ x' :=
  by
  rw [typein_le_typein]
  exact not_lt
#align ordinal.typein_le_typein' Ordinal.typein_le_typein'
-/

#print Ordinal.enum_le_enum /-
@[simp]
theorem enum_le_enum (r : α → α → Prop) [IsWellOrder α r] {o o' : Ordinal} (ho : o < type r)
    (ho' : o' < type r) : ¬r (enum r o' ho') (enum r o ho) ↔ o ≤ o' := by
  rw [← @not_lt _ _ o' o, enum_lt_enum ho']
#align ordinal.enum_le_enum Ordinal.enum_le_enum
-/

#print Ordinal.enum_le_enum' /-
@[simp]
theorem enum_le_enum' (a : Ordinal) {o o' : Ordinal} (ho : o < type (· < ·))
    (ho' : o' < type (· < ·)) : enum (· < ·) o ho ≤ @enum a.out.α (· < ·) _ o' ho' ↔ o ≤ o' := by
  rw [← enum_le_enum (· < ·), ← not_lt]
#align ordinal.enum_le_enum' Ordinal.enum_le_enum'
-/

#print Ordinal.enum_zero_le /-
theorem enum_zero_le {r : α → α → Prop} [IsWellOrder α r] (h0 : 0 < type r) (a : α) :
    ¬r a (enum r 0 h0) := by
  rw [← enum_typein r a, enum_le_enum r]
  apply Ordinal.zero_le
#align ordinal.enum_zero_le Ordinal.enum_zero_le
-/

#print Ordinal.enum_zero_le' /-
theorem enum_zero_le' {o : Ordinal} (h0 : 0 < o) (a : o.out.α) :
    @enum o.out.α (· < ·) _ 0 (by rwa [type_lt]) ≤ a :=
  by
  rw [← not_lt]
  apply enum_zero_le
#align ordinal.enum_zero_le' Ordinal.enum_zero_le'
-/

#print Ordinal.le_enum_succ /-
theorem le_enum_succ {o : Ordinal} (a : (succ o).out.α) :
    a ≤
      @enum (succ o).out.α (· < ·) _ o
        (by
          rw [type_lt]
          exact lt_succ o) :=
  by
  rw [← enum_typein (· < ·) a, enum_le_enum', ← lt_succ_iff]
  apply typein_lt_self
#align ordinal.le_enum_succ Ordinal.le_enum_succ
-/

#print Ordinal.enum_inj /-
@[simp]
theorem enum_inj {r : α → α → Prop} [IsWellOrder α r] {o₁ o₂ : Ordinal} (h₁ : o₁ < type r)
    (h₂ : o₂ < type r) : enum r o₁ h₁ = enum r o₂ h₂ ↔ o₁ = o₂ :=
  ⟨fun h => by
    by_contra hne
    cases' lt_or_gt_of_ne hne with hlt hlt <;> apply (IsWellOrder.isIrrefl r).1
    · rwa [← @enum_lt_enum α r _ o₁ o₂ h₁ h₂, h] at hlt
    · change _ < _ at hlt
      rwa [← @enum_lt_enum α r _ o₂ o₁ h₂ h₁, h] at hlt, fun h => by simp_rw [h]⟩
#align ordinal.enum_inj Ordinal.enum_inj
-/

#print Ordinal.enumIso /-
/-- A well order `r` is order isomorphic to the set of ordinals smaller than `type r`. -/
@[simps]
def enumIso (r : α → α → Prop) [IsWellOrder α r] : Subrel (· < ·) (· < type r) ≃r r
    where
  toFun x := enum r x.1 x.2
  invFun x := ⟨typein r x, typein_lt_type r x⟩
  left_inv := fun ⟨o, h⟩ => Subtype.ext_val (typein_enum _ _)
  right_inv h := enum_typein _ _
  map_rel_iff' := by
    rintro ⟨a, _⟩ ⟨b, _⟩
    apply enum_lt_enum
#align ordinal.enum_iso Ordinal.enumIso
-/

#print Ordinal.enumIsoOut /-
/-- The order isomorphism between ordinals less than `o` and `o.out.α`. -/
@[simps]
noncomputable def enumIsoOut (o : Ordinal) : Set.Iio o ≃o o.out.α
    where
  toFun x :=
    enum (· < ·) x.1 <| by
      rw [type_lt]
      exact x.2
  invFun x := ⟨typein (· < ·) x, typein_lt_self x⟩
  left_inv := fun ⟨o', h⟩ => Subtype.ext_val (typein_enum _ _)
  right_inv h := enum_typein _ _
  map_rel_iff' := by
    rintro ⟨a, _⟩ ⟨b, _⟩
    apply enum_le_enum'
#align ordinal.enum_iso_out Ordinal.enumIsoOut
-/

#print Ordinal.outOrderBotOfPos /-
/-- `o.out.α` is an `order_bot` whenever `0 < o`. -/
def outOrderBotOfPos {o : Ordinal} (ho : 0 < o) : OrderBot o.out.α :=
  ⟨_, enum_zero_le' ho⟩
#align ordinal.out_order_bot_of_pos Ordinal.outOrderBotOfPos
-/

/- warning: ordinal.enum_zero_eq_bot -> Ordinal.enum_zero_eq_bot is a dubious translation:
lean 3 declaration is
  forall {o : Ordinal.{u1}} (ho : LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) o), Eq.{succ u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Ordinal.enum.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (LinearOrder.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (linearOrderOut.{u1} o))))))) (isWellOrder_out_lt.{u1} o) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (Eq.mpr.{0} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (Ordinal.type.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (LinearOrder.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (linearOrderOut.{u1} o))))))) (isWellOrder_out_lt.{u1} o))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) o) (id_tag Tactic.IdTag.rw (Eq.{1} Prop (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (Ordinal.type.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (LinearOrder.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (linearOrderOut.{u1} o))))))) (isWellOrder_out_lt.{u1} o))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) o)) (Eq.ndrec.{0, succ (succ u1)} Ordinal.{u1} (Ordinal.type.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (LinearOrder.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (linearOrderOut.{u1} o))))))) (isWellOrder_out_lt.{u1} o)) (fun (_a : Ordinal.{u1}) => Eq.{1} Prop (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (Ordinal.type.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (LinearOrder.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (linearOrderOut.{u1} o))))))) (isWellOrder_out_lt.{u1} o))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) _a)) (rfl.{1} Prop (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (Ordinal.type.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (LinearOrder.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (linearOrderOut.{u1} o))))))) (isWellOrder_out_lt.{u1} o)))) o (Ordinal.type_lt.{u1} o))) ho)) (Bot.bot.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (OrderBot.toHasBot.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Preorder.toLE.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (LinearOrder.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (linearOrderOut.{u1} o)))))) (Ordinal.outOrderBotOfPos.{u1} o ho)))
but is expected to have type
  forall {o : Ordinal.{u1}} (ho : LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) o), Eq.{succ u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Ordinal.enum.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14239 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14241 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) => LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (DistribLattice.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (instDistribLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (linearOrderOut.{u1} o))))))) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14239 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14241) (isWellOrder_out_lt.{u1} o) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) (Eq.mpr.{0} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) (Ordinal.type.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14239 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14241 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) => LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (DistribLattice.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (instDistribLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (linearOrderOut.{u1} o))))))) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14239 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14241) (isWellOrder_out_lt.{u1} o))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) o) (id.{0} (Eq.{1} Prop (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) (Ordinal.type.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14239 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14241 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) => LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (DistribLattice.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (instDistribLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (linearOrderOut.{u1} o))))))) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14239 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14241) (isWellOrder_out_lt.{u1} o))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) o)) (Eq.ndrec.{0, succ (succ u1)} Ordinal.{u1} (Ordinal.type.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.1293 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.1295 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) => LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (DistribLattice.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (instDistribLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (linearOrderOut.{u1} o))))))) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.1293 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.1295) (isWellOrder_out_lt.{u1} o)) (fun (_a : Ordinal.{u1}) => Eq.{1} Prop (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) (Ordinal.type.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14239 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14241 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) => LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (DistribLattice.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (instDistribLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (linearOrderOut.{u1} o))))))) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14239 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14241) (isWellOrder_out_lt.{u1} o))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) _a)) (Eq.refl.{1} Prop (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) (Ordinal.type.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14239 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14241 : WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) => LT.lt.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Preorder.toLT.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (DistribLattice.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (instDistribLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (linearOrderOut.{u1} o))))))) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14239 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14241) (isWellOrder_out_lt.{u1} o)))) o (Ordinal.type_lt.{u1} o))) ho)) (Bot.bot.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (OrderBot.toBot.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Preorder.toLE.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (PartialOrder.toPreorder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (SemilatticeInf.toPartialOrder.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (Lattice.toSemilatticeInf.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (DistribLattice.toLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (instDistribLattice.{u1} (WellOrder.α.{u1} (Quotient.out.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} o)) (linearOrderOut.{u1} o))))))) (Ordinal.outOrderBotOfPos.{u1} o ho)))
Case conversion may be inaccurate. Consider using '#align ordinal.enum_zero_eq_bot Ordinal.enum_zero_eq_botₓ'. -/
theorem enum_zero_eq_bot {o : Ordinal} (ho : 0 < o) :
    enum (· < ·) 0 (by rwa [type_lt]) =
      haveI H := out_order_bot_of_pos ho
      ⊥ :=
  rfl
#align ordinal.enum_zero_eq_bot Ordinal.enum_zero_eq_bot

/-! ### Universal ordinal -/


#print Ordinal.univ /-
-- intended to be used with explicit universe parameters
/-- `univ.{u v}` is the order type of the ordinals of `Type u` as a member
  of `ordinal.{v}` (when `u < v`). It is an inaccessible cardinal. -/
@[nolint check_univs]
def univ : Ordinal.{max (u + 1) v} :=
  lift.{v, u + 1} (@type Ordinal (· < ·) _)
#align ordinal.univ Ordinal.univ
-/

#print Ordinal.univ_id /-
theorem univ_id : univ.{u, u + 1} = @type Ordinal (· < ·) _ :=
  lift_id _
#align ordinal.univ_id Ordinal.univ_id
-/

#print Ordinal.lift_univ /-
@[simp]
theorem lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w} :=
  lift_lift _
#align ordinal.lift_univ Ordinal.lift_univ
-/

#print Ordinal.univ_umax /-
theorem univ_umax : univ.{u, max (u + 1) v} = univ.{u, v} :=
  congr_fun lift_umax _
#align ordinal.univ_umax Ordinal.univ_umax
-/

#print Ordinal.lift.principalSeg /-
/-- Principal segment version of the lift operation on ordinals, embedding `ordinal.{u}` in
  `ordinal.{v}` as a principal segment when `u < v`. -/
def lift.principalSeg : @PrincipalSeg Ordinal.{u} Ordinal.{max (u + 1) v} (· < ·) (· < ·) :=
  ⟨↑lift.initialSeg.{u, max (u + 1) v}, univ.{u, v},
    by
    refine' fun b => induction_on b _; intro β s _
    rw [univ, ← lift_umax]; constructor <;> intro h
    · rw [← lift_id (type s)] at h⊢
      cases' lift_type_lt.1 h with f
      cases' f with f a hf
      exists a
      revert hf
      apply induction_on a
      intro α r _ hf
      refine'
        lift_type_eq.{u, max (u + 1) v, max (u + 1) v}.2
          ⟨(RelIso.ofSurjective (RelEmbedding.ofMonotone _ _) _).symm⟩
      · exact fun b => enum r (f b) ((hf _).2 ⟨_, rfl⟩)
      · refine' fun a b h => (typein_lt_typein r).1 _
        rw [typein_enum, typein_enum]
        exact f.map_rel_iff.2 h
      · intro a'
        cases' (hf _).1 (typein_lt_type _ a') with b e
        exists b
        simp
        simp [e]
    · cases' h with a e
      rw [← e]
      apply induction_on a
      intro α r _
      exact lift_type_lt.{u, u + 1, max (u + 1) v}.2 ⟨typein.principal_seg r⟩⟩
#align ordinal.lift.principal_seg Ordinal.lift.principalSeg
-/

/- warning: ordinal.lift.principal_seg_coe -> Ordinal.lift.principalSeg_coe is a dubious translation:
lean 3 declaration is
  Eq.{max (succ (succ u1)) (succ (succ (max (succ u1) u2)))} ((fun (_x : PrincipalSeg.{succ u1, succ (max (succ u1) u2)} Ordinal.{u1} Ordinal.{max (succ u1) u2} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}))) (LT.lt.{succ (max (succ u1) u2)} Ordinal.{max (succ u1) u2} (Preorder.toLT.{succ (max (succ u1) u2)} Ordinal.{max (succ u1) u2} (PartialOrder.toPreorder.{succ (max (succ u1) u2)} Ordinal.{max (succ u1) u2} Ordinal.partialOrder.{max (succ u1) u2})))) => Ordinal.{u1} -> Ordinal.{max (succ u1) u2}) Ordinal.lift.principalSeg.{u1, u2}) (coeFn.{max (succ (succ u1)) (succ (succ (max (succ u1) u2))), max (succ (succ u1)) (succ (succ (max (succ u1) u2)))} (PrincipalSeg.{succ u1, succ (max (succ u1) u2)} Ordinal.{u1} Ordinal.{max (succ u1) u2} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}))) (LT.lt.{succ (max (succ u1) u2)} Ordinal.{max (succ u1) u2} (Preorder.toLT.{succ (max (succ u1) u2)} Ordinal.{max (succ u1) u2} (PartialOrder.toPreorder.{succ (max (succ u1) u2)} Ordinal.{max (succ u1) u2} Ordinal.partialOrder.{max (succ u1) u2})))) (fun (_x : PrincipalSeg.{succ u1, succ (max (succ u1) u2)} Ordinal.{u1} Ordinal.{max (succ u1) u2} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}))) (LT.lt.{succ (max (succ u1) u2)} Ordinal.{max (succ u1) u2} (Preorder.toLT.{succ (max (succ u1) u2)} Ordinal.{max (succ u1) u2} (PartialOrder.toPreorder.{succ (max (succ u1) u2)} Ordinal.{max (succ u1) u2} Ordinal.partialOrder.{max (succ u1) u2})))) => Ordinal.{u1} -> Ordinal.{max (succ u1) u2}) (PrincipalSeg.hasCoeToFun.{succ u1, succ (max (succ u1) u2)} Ordinal.{u1} Ordinal.{max (succ u1) u2} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}))) (LT.lt.{succ (max (succ u1) u2)} Ordinal.{max (succ u1) u2} (Preorder.toLT.{succ (max (succ u1) u2)} Ordinal.{max (succ u1) u2} (PartialOrder.toPreorder.{succ (max (succ u1) u2)} Ordinal.{max (succ u1) u2} Ordinal.partialOrder.{max (succ u1) u2})))) Ordinal.lift.principalSeg.{u1, u2}) Ordinal.lift.{max (succ u1) u2, u1}
but is expected to have type
  Eq.{max (succ (succ (succ u1))) (succ (succ u2))} (forall (a : Ordinal.{u1}), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Ordinal.{u1}) => Ordinal.{max (succ u1) u2}) a) (FunLike.coe.{max (succ (succ u1)) (succ (max (succ (succ u1)) (succ u2))), succ (succ u1), succ (max (succ (succ u1)) (succ u2))} (Function.Embedding.{succ (succ u1), succ (max (succ (succ u1)) (succ u2))} Ordinal.{u1} Ordinal.{max (succ u1) u2}) Ordinal.{u1} (fun (_x : Ordinal.{u1}) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Ordinal.{u1}) => Ordinal.{max (succ u1) u2}) _x) (EmbeddingLike.toFunLike.{max (succ (succ u1)) (succ (max (succ (succ u1)) (succ u2))), succ (succ u1), succ (max (succ (succ u1)) (succ u2))} (Function.Embedding.{succ (succ u1), succ (max (succ (succ u1)) (succ u2))} Ordinal.{u1} Ordinal.{max (succ u1) u2}) Ordinal.{u1} Ordinal.{max (succ u1) u2} (Function.instEmbeddingLikeEmbedding.{succ (succ u1), succ (max (succ (succ u1)) (succ u2))} Ordinal.{u1} Ordinal.{max (succ u1) u2})) (RelEmbedding.toEmbedding.{succ u1, max (succ (succ u1)) (succ u2)} Ordinal.{u1} Ordinal.{max (succ u1) u2} (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14480 : Ordinal.{u1}) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14482 : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14480 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14482) (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14495 : Ordinal.{max (succ u1) u2}) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14497 : Ordinal.{max (succ u1) u2}) => LT.lt.{max (succ (succ u1)) (succ u2)} Ordinal.{max (succ u1) u2} (Preorder.toLT.{max (succ (succ u1)) (succ u2)} Ordinal.{max (succ u1) u2} (PartialOrder.toPreorder.{max (succ (succ u1)) (succ u2)} Ordinal.{max (succ u1) u2} Ordinal.partialOrder.{max (succ u1) u2})) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14495 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14497) (PrincipalSeg.toRelEmbedding.{succ u1, max (succ (succ u1)) (succ u2)} Ordinal.{u1} Ordinal.{max (succ u1) u2} (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14480 : Ordinal.{u1}) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14482 : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14480 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14482) (fun (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14495 : Ordinal.{max (succ u1) u2}) (x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14497 : Ordinal.{max (succ u1) u2}) => LT.lt.{max (succ (succ u1)) (succ u2)} Ordinal.{max (succ u1) u2} (Preorder.toLT.{max (succ (succ u1)) (succ u2)} Ordinal.{max (succ u1) u2} (PartialOrder.toPreorder.{max (succ (succ u1)) (succ u2)} Ordinal.{max (succ u1) u2} Ordinal.partialOrder.{max (succ u1) u2})) x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14495 x._@.Mathlib.SetTheory.Ordinal.Basic._hyg.14497) Ordinal.lift.principalSeg.{u1, u2}))) Ordinal.lift.{max (succ u1) u2, u1}
Case conversion may be inaccurate. Consider using '#align ordinal.lift.principal_seg_coe Ordinal.lift.principalSeg_coeₓ'. -/
@[simp]
theorem lift.principalSeg_coe :
    (lift.principalSeg.{u, v} : Ordinal → Ordinal) = lift.{max (u + 1) v} :=
  rfl
#align ordinal.lift.principal_seg_coe Ordinal.lift.principalSeg_coe

#print Ordinal.lift.principalSeg_top /-
@[simp]
theorem lift.principalSeg_top : lift.principalSeg.top = univ :=
  rfl
#align ordinal.lift.principal_seg_top Ordinal.lift.principalSeg_top
-/

#print Ordinal.lift.principalSeg_top' /-
theorem lift.principalSeg_top' : lift.principalSeg.{u, u + 1}.top = @type Ordinal (· < ·) _ := by
  simp only [lift.principal_seg_top, univ_id]
#align ordinal.lift.principal_seg_top' Ordinal.lift.principalSeg_top'
-/

end Ordinal

/-! ### Representing a cardinal with an ordinal -/


namespace Cardinal

open Ordinal

#print Cardinal.mk_ordinal_out /-
@[simp]
theorem mk_ordinal_out (o : Ordinal) : (#o.out.α) = o.card :=
  (Ordinal.card_type _).symm.trans <| by rw [Ordinal.type_lt]
#align cardinal.mk_ordinal_out Cardinal.mk_ordinal_out
-/

#print Cardinal.ord /-
/-- The ordinal corresponding to a cardinal `c` is the least ordinal
  whose cardinal is `c`. For the order-embedding version, see `ord.order_embedding`. -/
def ord (c : Cardinal) : Ordinal :=
  let F := fun α : Type u => ⨅ r : { r // IsWellOrder α r }, @type α r.1 r.2
  Quot.liftOn c F
    (by
      suffices : ∀ {α β}, α ≈ β → F α ≤ F β
      exact fun α β h => (this h).antisymm (this (Setoid.symm h))
      rintro α β ⟨f⟩
      refine' le_cinfᵢ_iff'.2 fun i => _
      haveI := @RelEmbedding.isWellOrder _ _ (f ⁻¹'o i.1) _ (↑(RelIso.preimage f i.1)) i.2
      exact
        (cinfᵢ_le' _
              (Subtype.mk (⇑f ⁻¹'o i.val)
                (@RelEmbedding.isWellOrder _ _ _ _ (↑(RelIso.preimage f i.1)) i.2))).trans_eq
          (Quot.sound ⟨RelIso.preimage f i.1⟩))
#align cardinal.ord Cardinal.ord
-/

/- warning: cardinal.ord_eq_Inf -> Cardinal.ord_eq_Inf is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Cardinal.ord.{u1} (Cardinal.mk.{u1} α)) (infᵢ.{succ u1, succ u1} Ordinal.{u1} (ConditionallyCompleteLattice.toHasInf.{succ u1} Ordinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Ordinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Ordinal.{u1} Ordinal.conditionallyCompleteLinearOrderBot.{u1}))) (Subtype.{succ u1} (α -> α -> Prop) (fun (r : α -> α -> Prop) => IsWellOrder.{u1} α r)) (fun (r : Subtype.{succ u1} (α -> α -> Prop) (fun (r : α -> α -> Prop) => IsWellOrder.{u1} α r)) => Ordinal.type.{u1} α (Subtype.val.{succ u1} (α -> α -> Prop) (fun (r : α -> α -> Prop) => IsWellOrder.{u1} α r) r) (Subtype.property.{succ u1} (α -> α -> Prop) (fun (r : α -> α -> Prop) => IsWellOrder.{u1} α r) r)))
but is expected to have type
  forall (α : Type.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Cardinal.ord.{u1} (Cardinal.mk.{u1} α)) (infᵢ.{succ u1, succ u1} Ordinal.{u1} (ConditionallyCompleteLattice.toInfSet.{succ u1} Ordinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Ordinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Ordinal.{u1} Ordinal.instConditionallyCompleteLinearOrderBotOrdinal.{u1}))) (Subtype.{succ u1} (α -> α -> Prop) (fun (r : α -> α -> Prop) => IsWellOrder.{u1} α r)) (fun (r : Subtype.{succ u1} (α -> α -> Prop) (fun (r : α -> α -> Prop) => IsWellOrder.{u1} α r)) => Ordinal.type.{u1} α (Subtype.val.{succ u1} (α -> α -> Prop) (fun (r : α -> α -> Prop) => IsWellOrder.{u1} α r) r) (Subtype.property.{succ u1} (α -> α -> Prop) (fun (r : α -> α -> Prop) => IsWellOrder.{u1} α r) r)))
Case conversion may be inaccurate. Consider using '#align cardinal.ord_eq_Inf Cardinal.ord_eq_Infₓ'. -/
theorem ord_eq_Inf (α : Type u) : ord (#α) = ⨅ r : { r // IsWellOrder α r }, @type α r.1 r.2 :=
  rfl
#align cardinal.ord_eq_Inf Cardinal.ord_eq_Inf

#print Cardinal.ord_eq /-
theorem ord_eq (α) : ∃ (r : α → α → Prop)(wo : IsWellOrder α r), ord (#α) = @type α r wo :=
  let ⟨r, wo⟩ := cinfᵢ_mem fun r : { r // IsWellOrder α r } => @type α r.1 r.2
  ⟨r.1, r.2, wo.symm⟩
#align cardinal.ord_eq Cardinal.ord_eq
-/

#print Cardinal.ord_le_type /-
theorem ord_le_type (r : α → α → Prop) [h : IsWellOrder α r] : ord (#α) ≤ type r :=
  cinfᵢ_le' _ (Subtype.mk r h)
#align cardinal.ord_le_type Cardinal.ord_le_type
-/

#print Cardinal.ord_le /-
theorem ord_le {c o} : ord c ≤ o ↔ c ≤ o.card :=
  inductionOn c fun α =>
    Ordinal.inductionOn o fun β s _ => by
      let ⟨r, _, e⟩ := ord_eq α
      skip; simp only [card_type]; constructor <;> intro h
      · rw [e] at h
        exact
          let ⟨f⟩ := h
          ⟨f.toEmbedding⟩
      · cases' h with f
        have g := RelEmbedding.preimage f s
        haveI := RelEmbedding.isWellOrder g
        exact le_trans (ord_le_type _) g.ordinal_type_le
#align cardinal.ord_le Cardinal.ord_le
-/

#print Cardinal.gc_ord_card /-
theorem gc_ord_card : GaloisConnection ord card := fun _ _ => ord_le
#align cardinal.gc_ord_card Cardinal.gc_ord_card
-/

#print Cardinal.lt_ord /-
theorem lt_ord {c o} : o < ord c ↔ o.card < c :=
  gc_ord_card.lt_iff_lt
#align cardinal.lt_ord Cardinal.lt_ord
-/

#print Cardinal.card_ord /-
@[simp]
theorem card_ord (c) : (ord c).card = c :=
  Quotient.inductionOn c fun α => by
    let ⟨r, _, e⟩ := ord_eq α
    simp only [mk_def, e, card_type]
#align cardinal.card_ord Cardinal.card_ord
-/

#print Cardinal.gciOrdCard /-
/-- Galois coinsertion between `cardinal.ord` and `ordinal.card`. -/
def gciOrdCard : GaloisCoinsertion ord card :=
  gc_ord_card.toGaloisCoinsertion fun c => c.card_ord.le
#align cardinal.gci_ord_card Cardinal.gciOrdCard
-/

#print Cardinal.ord_card_le /-
theorem ord_card_le (o : Ordinal) : o.card.ord ≤ o :=
  gc_ord_card.l_u_le _
#align cardinal.ord_card_le Cardinal.ord_card_le
-/

/- warning: cardinal.lt_ord_succ_card -> Cardinal.lt_ord_succ_card is a dubious translation:
lean 3 declaration is
  forall (o : Ordinal.{u1}), LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o (Cardinal.ord.{u1} (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.succOrder.{u1} (Ordinal.card.{u1} o)))
but is expected to have type
  forall (o : Ordinal.{u1}), LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o (Cardinal.ord.{u1} (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.instSuccOrderCardinalToPreorderPartialOrder.{u1} (Ordinal.card.{u1} o)))
Case conversion may be inaccurate. Consider using '#align cardinal.lt_ord_succ_card Cardinal.lt_ord_succ_cardₓ'. -/
theorem lt_ord_succ_card (o : Ordinal) : o < (succ o.card).ord :=
  lt_ord.2 <| lt_succ _
#align cardinal.lt_ord_succ_card Cardinal.lt_ord_succ_card

#print Cardinal.ord_strictMono /-
@[mono]
theorem ord_strictMono : StrictMono ord :=
  gciOrdCard.strictMono_l
#align cardinal.ord_strict_mono Cardinal.ord_strictMono
-/

#print Cardinal.ord_mono /-
@[mono]
theorem ord_mono : Monotone ord :=
  gc_ord_card.monotone_l
#align cardinal.ord_mono Cardinal.ord_mono
-/

#print Cardinal.ord_le_ord /-
@[simp]
theorem ord_le_ord {c₁ c₂} : ord c₁ ≤ ord c₂ ↔ c₁ ≤ c₂ :=
  gciOrdCard.l_le_l_iff
#align cardinal.ord_le_ord Cardinal.ord_le_ord
-/

#print Cardinal.ord_lt_ord /-
@[simp]
theorem ord_lt_ord {c₁ c₂} : ord c₁ < ord c₂ ↔ c₁ < c₂ :=
  ord_strictMono.lt_iff_lt
#align cardinal.ord_lt_ord Cardinal.ord_lt_ord
-/

#print Cardinal.ord_zero /-
@[simp]
theorem ord_zero : ord 0 = 0 :=
  gc_ord_card.l_bot
#align cardinal.ord_zero Cardinal.ord_zero
-/

/- warning: cardinal.ord_nat -> Cardinal.ord_nat is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{succ (succ u1)} Ordinal.{u1} (Cardinal.ord.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Ordinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Ordinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Ordinal.{u1} (Nat.castCoe.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1})))) n)
but is expected to have type
  forall (n : Nat), Eq.{succ (succ u1)} Ordinal.{u1} (Cardinal.ord.{u1} (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (Nat.cast.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1}) n)
Case conversion may be inaccurate. Consider using '#align cardinal.ord_nat Cardinal.ord_natₓ'. -/
@[simp]
theorem ord_nat (n : ℕ) : ord n = n :=
  (ord_le.2 (card_nat n).ge).antisymm
    (by
      induction' n with n IH
      · apply Ordinal.zero_le
      · exact succ_le_of_lt (IH.trans_lt <| ord_lt_ord.2 <| nat_cast_lt.2 (Nat.lt_succ_self n)))
#align cardinal.ord_nat Cardinal.ord_nat

/- warning: cardinal.ord_one -> Cardinal.ord_one is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Ordinal.{u1} (Cardinal.ord.{u1} (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (OfNat.mk.{succ u1} Cardinal.{u1} 1 (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))
but is expected to have type
  Eq.{succ (succ u1)} Ordinal.{u1} (Cardinal.ord.{u1} (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (One.toOfNat1.{succ u1} Cardinal.{u1} Cardinal.instOneCardinal.{u1}))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))
Case conversion may be inaccurate. Consider using '#align cardinal.ord_one Cardinal.ord_oneₓ'. -/
@[simp]
theorem ord_one : ord 1 = 1 := by simpa using ord_nat 1
#align cardinal.ord_one Cardinal.ord_one

/- warning: cardinal.lift_ord -> Cardinal.lift_ord is a dubious translation:
lean 3 declaration is
  forall (c : Cardinal.{u1}), Eq.{succ (succ (max u1 u2))} Ordinal.{max u1 u2} (Ordinal.lift.{u2, u1} (Cardinal.ord.{u1} c)) (Cardinal.ord.{max u1 u2} (Cardinal.lift.{u2, u1} c))
but is expected to have type
  forall (c : Cardinal.{u2}), Eq.{max (succ (succ u1)) (succ (succ u2))} Ordinal.{max u2 u1} (Ordinal.lift.{u1, u2} (Cardinal.ord.{u2} c)) (Cardinal.ord.{max u1 u2} (Cardinal.lift.{u1, u2} c))
Case conversion may be inaccurate. Consider using '#align cardinal.lift_ord Cardinal.lift_ordₓ'. -/
@[simp]
theorem lift_ord (c) : (ord c).lift = ord (lift c) :=
  by
  refine' le_antisymm (le_of_forall_lt fun a ha => _) _
  · rcases Ordinal.lt_lift_iff.1 ha with ⟨a, rfl, h⟩
    rwa [lt_ord, ← lift_card, lift_lt, ← lt_ord, ← Ordinal.lift_lt]
  · rw [ord_le, ← lift_card, card_ord]
#align cardinal.lift_ord Cardinal.lift_ord

#print Cardinal.mk_ord_out /-
theorem mk_ord_out (c : Cardinal) : (#c.ord.out.α) = c := by simp
#align cardinal.mk_ord_out Cardinal.mk_ord_out
-/

#print Cardinal.card_typein_lt /-
theorem card_typein_lt (r : α → α → Prop) [IsWellOrder α r] (x : α) (h : ord (#α) = type r) :
    card (typein r x) < (#α) := by
  rw [← lt_ord, h]
  apply typein_lt_type
#align cardinal.card_typein_lt Cardinal.card_typein_lt
-/

#print Cardinal.card_typein_out_lt /-
theorem card_typein_out_lt (c : Cardinal) (x : c.ord.out.α) : card (typein (· < ·) x) < c :=
  by
  rw [← lt_ord]
  apply typein_lt_self
#align cardinal.card_typein_out_lt Cardinal.card_typein_out_lt
-/

#print Cardinal.ord_injective /-
theorem ord_injective : Injective ord := by
  intro c c' h
  rw [← card_ord c, ← card_ord c', h]
#align cardinal.ord_injective Cardinal.ord_injective
-/

#print Cardinal.ord.orderEmbedding /-
/-- The ordinal corresponding to a cardinal `c` is the least ordinal
  whose cardinal is `c`. This is the order-embedding version. For the regular function, see `ord`.
-/
def ord.orderEmbedding : Cardinal ↪o Ordinal :=
  RelEmbedding.orderEmbeddingOfLTEmbedding
    (RelEmbedding.ofMonotone Cardinal.ord fun a b => Cardinal.ord_lt_ord.2)
#align cardinal.ord.order_embedding Cardinal.ord.orderEmbedding
-/

/- warning: cardinal.ord.order_embedding_coe -> Cardinal.ord.orderEmbedding_coe is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} ((fun (_x : RelEmbedding.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1}) (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})))) => Cardinal.{u1} -> Ordinal.{u1}) Cardinal.ord.orderEmbedding.{u1}) (coeFn.{succ (succ u1), succ (succ u1)} (OrderEmbedding.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} Cardinal.hasLe.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}))) (fun (_x : RelEmbedding.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1}) (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})))) => Cardinal.{u1} -> Ordinal.{u1}) (RelEmbedding.hasCoeToFun.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1}) (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})))) Cardinal.ord.orderEmbedding.{u1}) Cardinal.ord.{u1}
but is expected to have type
  Eq.{succ (succ u1)} (forall (a : Cardinal.{u1}), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Cardinal.{u1}) => Ordinal.{u1}) a) (FunLike.coe.{succ (succ u1), succ (succ u1), succ (succ u1)} (Function.Embedding.{succ (succ u1), succ (succ u1)} Cardinal.{u1} Ordinal.{u1}) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Cardinal.{u1}) => Ordinal.{u1}) _x) (EmbeddingLike.toFunLike.{succ (succ u1), succ (succ u1), succ (succ u1)} (Function.Embedding.{succ (succ u1), succ (succ u1)} Cardinal.{u1} Ordinal.{u1}) Cardinal.{u1} Ordinal.{u1} (Function.instEmbeddingLikeEmbedding.{succ (succ u1), succ (succ u1)} Cardinal.{u1} Ordinal.{u1})) (RelEmbedding.toEmbedding.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Cardinal.{u1}) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Cardinal.{u1}) => LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Ordinal.{u1}) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Ordinal.{u1}) => LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) Cardinal.ord.orderEmbedding.{u1})) Cardinal.ord.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.ord.order_embedding_coe Cardinal.ord.orderEmbedding_coeₓ'. -/
@[simp]
theorem ord.orderEmbedding_coe : (ord.orderEmbedding : Cardinal → Ordinal) = ord :=
  rfl
#align cardinal.ord.order_embedding_coe Cardinal.ord.orderEmbedding_coe

#print Cardinal.univ /-
-- intended to be used with explicit universe parameters
/-- The cardinal `univ` is the cardinality of ordinal `univ`, or
  equivalently the cardinal of `ordinal.{u}`, or `cardinal.{u}`,
  as an element of `cardinal.{v}` (when `u < v`). -/
@[nolint check_univs]
def univ :=
  lift.{v, u + 1} (#Ordinal)
#align cardinal.univ Cardinal.univ
-/

#print Cardinal.univ_id /-
theorem univ_id : univ.{u, u + 1} = (#Ordinal) :=
  lift_id _
#align cardinal.univ_id Cardinal.univ_id
-/

#print Cardinal.lift_univ /-
@[simp]
theorem lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w} :=
  lift_lift _
#align cardinal.lift_univ Cardinal.lift_univ
-/

#print Cardinal.univ_umax /-
theorem univ_umax : univ.{u, max (u + 1) v} = univ.{u, v} :=
  congr_fun lift_umax _
#align cardinal.univ_umax Cardinal.univ_umax
-/

#print Cardinal.lift_lt_univ /-
theorem lift_lt_univ (c : Cardinal) : lift.{u + 1, u} c < univ.{u, u + 1} := by
  simpa only [lift.principal_seg_coe, lift_ord, lift_succ, ord_le, succ_le_iff] using
    le_of_lt (lift.principalSeg.{u, u + 1}.lt_top (succ c).ord)
#align cardinal.lift_lt_univ Cardinal.lift_lt_univ
-/

#print Cardinal.lift_lt_univ' /-
theorem lift_lt_univ' (c : Cardinal) : lift.{max (u + 1) v, u} c < univ.{u, v} := by
  simpa only [lift_lift, lift_univ, univ_umax] using lift_lt.{_, max (u + 1) v}.2 (lift_lt_univ c)
#align cardinal.lift_lt_univ' Cardinal.lift_lt_univ'
-/

#print Cardinal.ord_univ /-
@[simp]
theorem ord_univ : ord univ.{u, v} = Ordinal.univ.{u, v} :=
  le_antisymm (ord_card_le _) <|
    le_of_forall_lt fun o h =>
      lt_ord.2
        (by
          rcases lift.principalSeg.{u, v}.down.1
              (by simpa only [lift.principal_seg_coe] using h) with
            ⟨o', rfl⟩
          simp only [lift.principal_seg_coe]; rw [← lift_card]
          apply lift_lt_univ')
#align cardinal.ord_univ Cardinal.ord_univ
-/

#print Cardinal.lt_univ /-
theorem lt_univ {c} : c < univ.{u, u + 1} ↔ ∃ c', c = lift.{u + 1, u} c' :=
  ⟨fun h => by
    have := ord_lt_ord.2 h
    rw [ord_univ] at this
    cases' lift.principalSeg.{u, u + 1}.down.1 (by simpa only [lift.principal_seg_top] ) with o e
    have := card_ord c
    rw [← e, lift.principal_seg_coe, ← lift_card] at this
    exact ⟨_, this.symm⟩, fun ⟨c', e⟩ => e.symm ▸ lift_lt_univ _⟩
#align cardinal.lt_univ Cardinal.lt_univ
-/

#print Cardinal.lt_univ' /-
theorem lt_univ' {c} : c < univ.{u, v} ↔ ∃ c', c = lift.{max (u + 1) v, u} c' :=
  ⟨fun h => by
    let ⟨a, e, h'⟩ := lt_lift_iff.1 h
    rw [← univ_id] at h'
    rcases lt_univ.{u}.1 h' with ⟨c', rfl⟩
    exact ⟨c', by simp only [e.symm, lift_lift]⟩, fun ⟨c', e⟩ => e.symm ▸ lift_lt_univ' _⟩
#align cardinal.lt_univ' Cardinal.lt_univ'
-/

#print Cardinal.small_iff_lift_mk_lt_univ /-
theorem small_iff_lift_mk_lt_univ {α : Type u} :
    Small.{v} α ↔ Cardinal.lift (#α) < univ.{v, max u (v + 1)} :=
  by
  rw [lt_univ']
  constructor
  · rintro ⟨β, e⟩
    exact ⟨#β, lift_mk_eq.{u, _, v + 1}.2 e⟩
  · rintro ⟨c, hc⟩
    exact ⟨⟨c.out, lift_mk_eq.{u, _, v + 1}.1 (hc.trans (congr rfl c.mk_out.symm))⟩⟩
#align cardinal.small_iff_lift_mk_lt_univ Cardinal.small_iff_lift_mk_lt_univ
-/

end Cardinal

namespace Ordinal

#print Ordinal.card_univ /-
@[simp]
theorem card_univ : card univ = Cardinal.univ :=
  rfl
#align ordinal.card_univ Ordinal.card_univ
-/

/- warning: ordinal.nat_le_card -> Ordinal.nat_le_card is a dubious translation:
lean 3 declaration is
  forall {o : Ordinal.{u1}} {n : Nat}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n) (Ordinal.card.{u1} o)) (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Ordinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Ordinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Ordinal.{u1} (Nat.castCoe.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1})))) n) o)
but is expected to have type
  forall {o : Ordinal.{u1}} {n : Nat}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n) (Ordinal.card.{u1} o)) (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (Nat.cast.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1}) n) o)
Case conversion may be inaccurate. Consider using '#align ordinal.nat_le_card Ordinal.nat_le_cardₓ'. -/
@[simp]
theorem nat_le_card {o} {n : ℕ} : (n : Cardinal) ≤ card o ↔ (n : Ordinal) ≤ o := by
  rw [← Cardinal.ord_le, Cardinal.ord_nat]
#align ordinal.nat_le_card Ordinal.nat_le_card

/- warning: ordinal.nat_lt_card -> Ordinal.nat_lt_card is a dubious translation:
lean 3 declaration is
  forall {o : Ordinal.{u1}} {n : Nat}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n) (Ordinal.card.{u1} o)) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Ordinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Ordinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Ordinal.{u1} (Nat.castCoe.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1})))) n) o)
but is expected to have type
  forall {o : Ordinal.{u1}} {n : Nat}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n) (Ordinal.card.{u1} o)) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (Nat.cast.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1}) n) o)
Case conversion may be inaccurate. Consider using '#align ordinal.nat_lt_card Ordinal.nat_lt_cardₓ'. -/
@[simp]
theorem nat_lt_card {o} {n : ℕ} : (n : Cardinal) < card o ↔ (n : Ordinal) < o :=
  by
  rw [← succ_le_iff, ← succ_le_iff, ← nat_succ, nat_le_card]
  rfl
#align ordinal.nat_lt_card Ordinal.nat_lt_card

/- warning: ordinal.card_lt_nat -> Ordinal.card_lt_nat is a dubious translation:
lean 3 declaration is
  forall {o : Ordinal.{u1}} {n : Nat}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (Ordinal.card.{u1} o) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Ordinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Ordinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Ordinal.{u1} (Nat.castCoe.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1})))) n))
but is expected to have type
  forall {o : Ordinal.{u1}} {n : Nat}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (Ordinal.card.{u1} o) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o (Nat.cast.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1}) n))
Case conversion may be inaccurate. Consider using '#align ordinal.card_lt_nat Ordinal.card_lt_natₓ'. -/
@[simp]
theorem card_lt_nat {o} {n : ℕ} : card o < n ↔ o < n :=
  lt_iff_lt_of_le_iff_le nat_le_card
#align ordinal.card_lt_nat Ordinal.card_lt_nat

/- warning: ordinal.card_le_nat -> Ordinal.card_le_nat is a dubious translation:
lean 3 declaration is
  forall {o : Ordinal.{u1}} {n : Nat}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Ordinal.card.{u1} o) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Ordinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Ordinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Ordinal.{u1} (Nat.castCoe.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1})))) n))
but is expected to have type
  forall {o : Ordinal.{u1}} {n : Nat}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Ordinal.card.{u1} o) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o (Nat.cast.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1}) n))
Case conversion may be inaccurate. Consider using '#align ordinal.card_le_nat Ordinal.card_le_natₓ'. -/
@[simp]
theorem card_le_nat {o} {n : ℕ} : card o ≤ n ↔ o ≤ n :=
  le_iff_le_iff_lt_iff_lt.2 nat_lt_card
#align ordinal.card_le_nat Ordinal.card_le_nat

/- warning: ordinal.card_eq_nat -> Ordinal.card_eq_nat is a dubious translation:
lean 3 declaration is
  forall {o : Ordinal.{u1}} {n : Nat}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (Ordinal.card.{u1} o) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) (Eq.{succ (succ u1)} Ordinal.{u1} o ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Ordinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Ordinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Ordinal.{u1} (Nat.castCoe.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1})))) n))
but is expected to have type
  forall {o : Ordinal.{u1}} {n : Nat}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (Ordinal.card.{u1} o) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (Eq.{succ (succ u1)} Ordinal.{u1} o (Nat.cast.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1}) n))
Case conversion may be inaccurate. Consider using '#align ordinal.card_eq_nat Ordinal.card_eq_natₓ'. -/
@[simp]
theorem card_eq_nat {o} {n : ℕ} : card o = n ↔ o = n := by
  simp only [le_antisymm_iff, card_le_nat, nat_le_card]
#align ordinal.card_eq_nat Ordinal.card_eq_nat

#print Ordinal.type_fintype /-
@[simp]
theorem type_fintype (r : α → α → Prop) [IsWellOrder α r] [Fintype α] : type r = Fintype.card α :=
  by rw [← card_eq_nat, card_type, mk_fintype]
#align ordinal.type_fintype Ordinal.type_fintype
-/

#print Ordinal.type_fin /-
theorem type_fin (n : ℕ) : @type (Fin n) (· < ·) _ = n := by simp
#align ordinal.type_fin Ordinal.type_fin
-/

end Ordinal

