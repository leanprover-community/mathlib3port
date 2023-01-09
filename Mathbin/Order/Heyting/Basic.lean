/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.heyting.basic
! leanprover-community/mathlib commit 247a102b14f3cebfee126293341af5f6bed00237
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.PropInstances

/-!
# Heyting algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines Heyting, co-Heyting and bi-Heyting algebras.

An Heyting algebra is a bounded distributive lattice with an implication operation `⇨` such that
`a ≤ b ⇨ c ↔ a ⊓ b ≤ c`. It also comes with a pseudo-complement `ᶜ`, such that `aᶜ = a ⇨ ⊥`.

Co-Heyting algebras are dual to Heyting algebras. They have a difference `\` and a negation `￢`
such that `a \ b ≤ c ↔ a ≤ b ⊔ c` and `￢a = ⊤ \ a`.

Bi-Heyting algebras are Heyting algebras that are also co-Heyting algebras.

From a logic standpoint, Heyting algebras precisely model intuitionistic logic, whereas boolean
algebras model classical logic.

Heyting algebras are the order theoretic equivalent of cartesian-closed categories.

## Main declarations

* `generalized_heyting_algebra`: Heyting algebra without a top element (nor negation).
* `generalized_coheyting_algebra`: Co-Heyting algebra without a bottom element (nor complement).
* `heyting_algebra`: Heyting algebra.
* `coheyting_algebra`: Co-Heyting algebra.
* `biheyting_algebra`: bi-Heyting algebra.

## Notation

* `⇨`: Heyting implication
* `\`: Difference
* `￢`: Heyting negation
* `ᶜ`: (Pseudo-)complement

## References

* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]

## Tags

Heyting, Brouwer, algebra, implication, negation, intuitionistic
-/


open Function OrderDual

universe u

variable {ι α β : Type _}

/-! ### Notation -/


#print HImp /-
/-- Syntax typeclass for Heyting implication `⇨`. -/
@[notation_class]
class HImp (α : Type _) where
  himp : α → α → α
#align has_himp HImp
-/

#print HNot /-
/-- Syntax typeclass for Heyting negation `￢`.

The difference between `has_compl` and `has_hnot` is that the former belongs to Heyting algebras,
while the latter belongs to co-Heyting algebras. They are both pseudo-complements, but `compl`
underestimates while `hnot` overestimates. In boolean algebras, they are equal. See `hnot_eq_compl`.
-/
@[notation_class]
class HNot (α : Type _) where
  hnot : α → α
#align has_hnot HNot
-/

export HImp (himp)

export SDiff (sdiff)

export HNot (hnot)

-- mathport name: «expr ⇨ »
infixr:60 " ⇨ " => himp

-- mathport name: «expr￢ »
prefix:72 "￢" => hnot

instance [HImp α] [HImp β] : HImp (α × β) :=
  ⟨fun a b => (a.1 ⇨ b.1, a.2 ⇨ b.2)⟩

instance [HNot α] [HNot β] : HNot (α × β) :=
  ⟨fun a => (￢a.1, ￢a.2)⟩

instance [SDiff α] [SDiff β] : SDiff (α × β) :=
  ⟨fun a b => (a.1 \ b.1, a.2 \ b.2)⟩

instance [HasCompl α] [HasCompl β] : HasCompl (α × β) :=
  ⟨fun a => (a.1ᶜ, a.2ᶜ)⟩

/- warning: fst_himp -> fst_himp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HImp.{u1} α] [_inst_2 : HImp.{u2} β] (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β), Eq.{succ u1} α (Prod.fst.{u1, u2} α β (HImp.himp.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasHimp.{u1, u2} α β _inst_1 _inst_2) a b)) (HImp.himp.{u1} α _inst_1 (Prod.fst.{u1, u2} α β a) (Prod.fst.{u1, u2} α β b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : HImp.{u2} α] [_inst_2 : HImp.{u1} β] (a : Prod.{u2, u1} α β) (b : Prod.{u2, u1} α β), Eq.{succ u2} α (Prod.fst.{u2, u1} α β (HImp.himp.{max u2 u1} (Prod.{u2, u1} α β) (Prod.himp.{u2, u1} α β _inst_1 _inst_2) a b)) (HImp.himp.{u2} α _inst_1 (Prod.fst.{u2, u1} α β a) (Prod.fst.{u2, u1} α β b))
Case conversion may be inaccurate. Consider using '#align fst_himp fst_himpₓ'. -/
@[simp]
theorem fst_himp [HImp α] [HImp β] (a b : α × β) : (a ⇨ b).1 = a.1 ⇨ b.1 :=
  rfl
#align fst_himp fst_himp

/- warning: snd_himp -> snd_himp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HImp.{u1} α] [_inst_2 : HImp.{u2} β] (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β), Eq.{succ u2} β (Prod.snd.{u1, u2} α β (HImp.himp.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasHimp.{u1, u2} α β _inst_1 _inst_2) a b)) (HImp.himp.{u2} β _inst_2 (Prod.snd.{u1, u2} α β a) (Prod.snd.{u1, u2} α β b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : HImp.{u2} α] [_inst_2 : HImp.{u1} β] (a : Prod.{u2, u1} α β) (b : Prod.{u2, u1} α β), Eq.{succ u1} β (Prod.snd.{u2, u1} α β (HImp.himp.{max u2 u1} (Prod.{u2, u1} α β) (Prod.himp.{u2, u1} α β _inst_1 _inst_2) a b)) (HImp.himp.{u1} β _inst_2 (Prod.snd.{u2, u1} α β a) (Prod.snd.{u2, u1} α β b))
Case conversion may be inaccurate. Consider using '#align snd_himp snd_himpₓ'. -/
@[simp]
theorem snd_himp [HImp α] [HImp β] (a b : α × β) : (a ⇨ b).2 = a.2 ⇨ b.2 :=
  rfl
#align snd_himp snd_himp

/- warning: fst_hnot -> fst_hnot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HNot.{u1} α] [_inst_2 : HNot.{u2} β] (a : Prod.{u1, u2} α β), Eq.{succ u1} α (Prod.fst.{u1, u2} α β (HNot.hnot.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasHnot.{u1, u2} α β _inst_1 _inst_2) a)) (HNot.hnot.{u1} α _inst_1 (Prod.fst.{u1, u2} α β a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : HNot.{u2} α] [_inst_2 : HNot.{u1} β] (a : Prod.{u2, u1} α β), Eq.{succ u2} α (Prod.fst.{u2, u1} α β (HNot.hnot.{max u2 u1} (Prod.{u2, u1} α β) (Prod.hnot.{u2, u1} α β _inst_1 _inst_2) a)) (HNot.hnot.{u2} α _inst_1 (Prod.fst.{u2, u1} α β a))
Case conversion may be inaccurate. Consider using '#align fst_hnot fst_hnotₓ'. -/
@[simp]
theorem fst_hnot [HNot α] [HNot β] (a : α × β) : (￢a).1 = ￢a.1 :=
  rfl
#align fst_hnot fst_hnot

/- warning: snd_hnot -> snd_hnot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HNot.{u1} α] [_inst_2 : HNot.{u2} β] (a : Prod.{u1, u2} α β), Eq.{succ u2} β (Prod.snd.{u1, u2} α β (HNot.hnot.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasHnot.{u1, u2} α β _inst_1 _inst_2) a)) (HNot.hnot.{u2} β _inst_2 (Prod.snd.{u1, u2} α β a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : HNot.{u2} α] [_inst_2 : HNot.{u1} β] (a : Prod.{u2, u1} α β), Eq.{succ u1} β (Prod.snd.{u2, u1} α β (HNot.hnot.{max u2 u1} (Prod.{u2, u1} α β) (Prod.hnot.{u2, u1} α β _inst_1 _inst_2) a)) (HNot.hnot.{u1} β _inst_2 (Prod.snd.{u2, u1} α β a))
Case conversion may be inaccurate. Consider using '#align snd_hnot snd_hnotₓ'. -/
@[simp]
theorem snd_hnot [HNot α] [HNot β] (a : α × β) : (￢a).2 = ￢a.2 :=
  rfl
#align snd_hnot snd_hnot

/- warning: fst_sdiff -> fst_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SDiff.{u1} α] [_inst_2 : SDiff.{u2} β] (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β), Eq.{succ u1} α (Prod.fst.{u1, u2} α β (SDiff.sdiff.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasSdiff.{u1, u2} α β _inst_1 _inst_2) a b)) (SDiff.sdiff.{u1} α _inst_1 (Prod.fst.{u1, u2} α β a) (Prod.fst.{u1, u2} α β b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SDiff.{u2} α] [_inst_2 : SDiff.{u1} β] (a : Prod.{u2, u1} α β) (b : Prod.{u2, u1} α β), Eq.{succ u2} α (Prod.fst.{u2, u1} α β (SDiff.sdiff.{max u2 u1} (Prod.{u2, u1} α β) (Prod.sdiff.{u2, u1} α β _inst_1 _inst_2) a b)) (SDiff.sdiff.{u2} α _inst_1 (Prod.fst.{u2, u1} α β a) (Prod.fst.{u2, u1} α β b))
Case conversion may be inaccurate. Consider using '#align fst_sdiff fst_sdiffₓ'. -/
@[simp]
theorem fst_sdiff [SDiff α] [SDiff β] (a b : α × β) : (a \ b).1 = a.1 \ b.1 :=
  rfl
#align fst_sdiff fst_sdiff

/- warning: snd_sdiff -> snd_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SDiff.{u1} α] [_inst_2 : SDiff.{u2} β] (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β), Eq.{succ u2} β (Prod.snd.{u1, u2} α β (SDiff.sdiff.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasSdiff.{u1, u2} α β _inst_1 _inst_2) a b)) (SDiff.sdiff.{u2} β _inst_2 (Prod.snd.{u1, u2} α β a) (Prod.snd.{u1, u2} α β b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SDiff.{u2} α] [_inst_2 : SDiff.{u1} β] (a : Prod.{u2, u1} α β) (b : Prod.{u2, u1} α β), Eq.{succ u1} β (Prod.snd.{u2, u1} α β (SDiff.sdiff.{max u2 u1} (Prod.{u2, u1} α β) (Prod.sdiff.{u2, u1} α β _inst_1 _inst_2) a b)) (SDiff.sdiff.{u1} β _inst_2 (Prod.snd.{u2, u1} α β a) (Prod.snd.{u2, u1} α β b))
Case conversion may be inaccurate. Consider using '#align snd_sdiff snd_sdiffₓ'. -/
@[simp]
theorem snd_sdiff [SDiff α] [SDiff β] (a b : α × β) : (a \ b).2 = a.2 \ b.2 :=
  rfl
#align snd_sdiff snd_sdiff

/- warning: fst_compl -> fst_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasCompl.{u1} α] [_inst_2 : HasCompl.{u2} β] (a : Prod.{u1, u2} α β), Eq.{succ u1} α (Prod.fst.{u1, u2} α β (HasCompl.compl.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasCompl.{u1, u2} α β _inst_1 _inst_2) a)) (HasCompl.compl.{u1} α _inst_1 (Prod.fst.{u1, u2} α β a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : HasCompl.{u2} α] [_inst_2 : HasCompl.{u1} β] (a : Prod.{u2, u1} α β), Eq.{succ u2} α (Prod.fst.{u2, u1} α β (HasCompl.compl.{max u2 u1} (Prod.{u2, u1} α β) (Prod.hasCompl.{u2, u1} α β _inst_1 _inst_2) a)) (HasCompl.compl.{u2} α _inst_1 (Prod.fst.{u2, u1} α β a))
Case conversion may be inaccurate. Consider using '#align fst_compl fst_complₓ'. -/
@[simp]
theorem fst_compl [HasCompl α] [HasCompl β] (a : α × β) : aᶜ.1 = a.1ᶜ :=
  rfl
#align fst_compl fst_compl

/- warning: snd_compl -> snd_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasCompl.{u1} α] [_inst_2 : HasCompl.{u2} β] (a : Prod.{u1, u2} α β), Eq.{succ u2} β (Prod.snd.{u1, u2} α β (HasCompl.compl.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasCompl.{u1, u2} α β _inst_1 _inst_2) a)) (HasCompl.compl.{u2} β _inst_2 (Prod.snd.{u1, u2} α β a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : HasCompl.{u2} α] [_inst_2 : HasCompl.{u1} β] (a : Prod.{u2, u1} α β), Eq.{succ u1} β (Prod.snd.{u2, u1} α β (HasCompl.compl.{max u2 u1} (Prod.{u2, u1} α β) (Prod.hasCompl.{u2, u1} α β _inst_1 _inst_2) a)) (HasCompl.compl.{u1} β _inst_2 (Prod.snd.{u2, u1} α β a))
Case conversion may be inaccurate. Consider using '#align snd_compl snd_complₓ'. -/
@[simp]
theorem snd_compl [HasCompl α] [HasCompl β] (a : α × β) : aᶜ.2 = a.2ᶜ :=
  rfl
#align snd_compl snd_compl

namespace Pi

variable {π : ι → Type _}

instance [∀ i, HImp (π i)] : HImp (∀ i, π i) :=
  ⟨fun a b i => a i ⇨ b i⟩

instance [∀ i, HNot (π i)] : HNot (∀ i, π i) :=
  ⟨fun a i => ￢a i⟩

#print Pi.himp_def /-
theorem himp_def [∀ i, HImp (π i)] (a b : ∀ i, π i) : a ⇨ b = fun i => a i ⇨ b i :=
  rfl
#align pi.himp_def Pi.himp_def
-/

#print Pi.hnot_def /-
theorem hnot_def [∀ i, HNot (π i)] (a : ∀ i, π i) : ￢a = fun i => ￢a i :=
  rfl
#align pi.hnot_def Pi.hnot_def
-/

#print Pi.himp_apply /-
@[simp]
theorem himp_apply [∀ i, HImp (π i)] (a b : ∀ i, π i) (i : ι) : (a ⇨ b) i = a i ⇨ b i :=
  rfl
#align pi.himp_apply Pi.himp_apply
-/

#print Pi.hnot_apply /-
@[simp]
theorem hnot_apply [∀ i, HNot (π i)] (a : ∀ i, π i) (i : ι) : (￢a) i = ￢a i :=
  rfl
#align pi.hnot_apply Pi.hnot_apply
-/

end Pi

#print GeneralizedHeytingAlgebra /-
/-- A generalized Heyting algebra is a lattice with an additional binary operation `⇨` called
Heyting implication such that `a ⇨` is right adjoint to `a ⊓`.

 This generalizes `heyting_algebra` by not requiring a bottom element. -/
class GeneralizedHeytingAlgebra (α : Type _) extends Lattice α, Top α, HImp α where
  le_top : ∀ a : α, a ≤ ⊤
  le_himp_iff (a b c : α) : a ≤ b ⇨ c ↔ a ⊓ b ≤ c
#align generalized_heyting_algebra GeneralizedHeytingAlgebra
-/

#print GeneralizedCoheytingAlgebra /-
/-- A generalized co-Heyting algebra is a lattice with an additional binary difference operation `\`
such that `\ a` is right adjoint to `⊔ a`.

This generalizes `coheyting_algebra` by not requiring a top element. -/
class GeneralizedCoheytingAlgebra (α : Type _) extends Lattice α, Bot α, SDiff α where
  bot_le : ∀ a : α, ⊥ ≤ a
  sdiff_le_iff (a b c : α) : a \ b ≤ c ↔ a ≤ b ⊔ c
#align generalized_coheyting_algebra GeneralizedCoheytingAlgebra
-/

#print HeytingAlgebra /-
/-- A Heyting algebra is a bounded lattice with an additional binary operation `⇨` called Heyting
implication such that `a ⇨` is right adjoint to `a ⊓`. -/
class HeytingAlgebra (α : Type _) extends GeneralizedHeytingAlgebra α, Bot α, HasCompl α where
  bot_le : ∀ a : α, ⊥ ≤ a
  himp_bot (a : α) : a ⇨ ⊥ = aᶜ
#align heyting_algebra HeytingAlgebra
-/

#print CoheytingAlgebra /-
/-- A co-Heyting algebra is a bounded  lattice with an additional binary difference operation `\`
such that `\ a` is right adjoint to `⊔ a`. -/
class CoheytingAlgebra (α : Type _) extends GeneralizedCoheytingAlgebra α, Top α, HNot α where
  le_top : ∀ a : α, a ≤ ⊤
  top_sdiff (a : α) : ⊤ \ a = ￢a
#align coheyting_algebra CoheytingAlgebra
-/

#print BiheytingAlgebra /-
/-- A bi-Heyting algebra is a Heyting algebra that is also a co-Heyting algebra. -/
class BiheytingAlgebra (α : Type _) extends HeytingAlgebra α, SDiff α, HNot α where
  sdiff_le_iff (a b c : α) : a \ b ≤ c ↔ a ≤ b ⊔ c
  top_sdiff (a : α) : ⊤ \ a = ￢a
#align biheyting_algebra BiheytingAlgebra
-/

#print GeneralizedHeytingAlgebra.toOrderTop /-
-- See note [lower instance priority]
instance (priority := 100) GeneralizedHeytingAlgebra.toOrderTop [GeneralizedHeytingAlgebra α] :
    OrderTop α :=
  { ‹GeneralizedHeytingAlgebra α› with }
#align generalized_heyting_algebra.to_order_top GeneralizedHeytingAlgebra.toOrderTop
-/

#print GeneralizedCoheytingAlgebra.toOrderBot /-
-- See note [lower instance priority]
instance (priority := 100) GeneralizedCoheytingAlgebra.toOrderBot [GeneralizedCoheytingAlgebra α] :
    OrderBot α :=
  { ‹GeneralizedCoheytingAlgebra α› with }
#align generalized_coheyting_algebra.to_order_bot GeneralizedCoheytingAlgebra.toOrderBot
-/

#print HeytingAlgebra.toBoundedOrder /-
-- See note [lower instance priority]
instance (priority := 100) HeytingAlgebra.toBoundedOrder [HeytingAlgebra α] : BoundedOrder α :=
  { ‹HeytingAlgebra α› with }
#align heyting_algebra.to_bounded_order HeytingAlgebra.toBoundedOrder
-/

#print CoheytingAlgebra.toBoundedOrder /-
-- See note [lower instance priority]
instance (priority := 100) CoheytingAlgebra.toBoundedOrder [CoheytingAlgebra α] : BoundedOrder α :=
  { ‹CoheytingAlgebra α› with }
#align coheyting_algebra.to_bounded_order CoheytingAlgebra.toBoundedOrder
-/

#print BiheytingAlgebra.toCoheytingAlgebra /-
-- See note [lower instance priority]
instance (priority := 100) BiheytingAlgebra.toCoheytingAlgebra [BiheytingAlgebra α] :
    CoheytingAlgebra α :=
  { ‹BiheytingAlgebra α› with }
#align biheyting_algebra.to_coheyting_algebra BiheytingAlgebra.toCoheytingAlgebra
-/

#print HeytingAlgebra.ofHImp /-
-- See note [reducible non-instances]
/-- Construct a Heyting algebra from the lattice structure and Heyting implication alone. -/
@[reducible]
def HeytingAlgebra.ofHImp [DistribLattice α] [BoundedOrder α] (himp : α → α → α)
    (le_himp_iff : ∀ a b c, a ≤ himp b c ↔ a ⊓ b ≤ c) : HeytingAlgebra α :=
  { ‹DistribLattice α›, ‹BoundedOrder α› with
    himp
    compl := fun a => himp a ⊥
    le_himp_iff
    himp_bot := fun a => rfl }
#align heyting_algebra.of_himp HeytingAlgebra.ofHImp
-/

#print HeytingAlgebra.ofCompl /-
-- See note [reducible non-instances]
/-- Construct a Heyting algebra from the lattice structure and complement operator alone. -/
@[reducible]
def HeytingAlgebra.ofCompl [DistribLattice α] [BoundedOrder α] (compl : α → α)
    (le_himp_iff : ∀ a b c, a ≤ compl b ⊔ c ↔ a ⊓ b ≤ c) : HeytingAlgebra α :=
  { ‹DistribLattice α›,
    ‹BoundedOrder α› with
    himp := fun a => (· ⊔ ·) (compl a)
    compl
    le_himp_iff
    himp_bot := fun a => sup_bot_eq }
#align heyting_algebra.of_compl HeytingAlgebra.ofCompl
-/

#print CoheytingAlgebra.ofSDiff /-
-- See note [reducible non-instances]
/-- Construct a co-Heyting algebra from the lattice structure and the difference alone. -/
@[reducible]
def CoheytingAlgebra.ofSDiff [DistribLattice α] [BoundedOrder α] (sdiff : α → α → α)
    (sdiff_le_iff : ∀ a b c, sdiff a b ≤ c ↔ a ≤ b ⊔ c) : CoheytingAlgebra α :=
  { ‹DistribLattice α›, ‹BoundedOrder α› with
    sdiff
    hnot := fun a => sdiff ⊤ a
    sdiff_le_iff
    top_sdiff := fun a => rfl }
#align coheyting_algebra.of_sdiff CoheytingAlgebra.ofSDiff
-/

#print CoheytingAlgebra.ofHNot /-
-- See note [reducible non-instances]
/-- Construct a co-Heyting algebra from the difference and Heyting negation alone. -/
@[reducible]
def CoheytingAlgebra.ofHNot [DistribLattice α] [BoundedOrder α] (hnot : α → α)
    (sdiff_le_iff : ∀ a b c, a ⊓ hnot b ≤ c ↔ a ≤ b ⊔ c) : CoheytingAlgebra α :=
  { ‹DistribLattice α›,
    ‹BoundedOrder α› with
    sdiff := fun a b => a ⊓ hnot b
    hnot
    sdiff_le_iff
    top_sdiff := fun a => top_inf_eq }
#align coheyting_algebra.of_hnot CoheytingAlgebra.ofHNot
-/

section GeneralizedHeytingAlgebra

variable [GeneralizedHeytingAlgebra α] {a b c d : α}

/- warning: le_himp_iff -> le_himp_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b c)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b c)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a b) c)
Case conversion may be inaccurate. Consider using '#align le_himp_iff le_himp_iffₓ'. -/
/- In this section, we'll give interpretations of these results in the Heyting algebra model of
intuitionistic logic,- where `≤` can be interpreted as "validates", `⇨` as "implies", `⊓` as "and",
`⊔` as "or", `⊥` as "false" and `⊤` as "true". Note that we confuse `→` and `⊢` because those are
the same in this logic.

See also `Prop.heyting_algebra`. -/
-- `p → q → r ↔ p ∧ q → r`
@[simp]
theorem le_himp_iff : a ≤ b ⇨ c ↔ a ⊓ b ≤ c :=
  GeneralizedHeytingAlgebra.le_himp_iff _ _ _
#align le_himp_iff le_himp_iff

/- warning: le_himp_iff' -> le_himp_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b c)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) b a) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b c)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) b a) c)
Case conversion may be inaccurate. Consider using '#align le_himp_iff' le_himp_iff'ₓ'. -/
-- `p → q → r ↔ q ∧ p → r`
theorem le_himp_iff' : a ≤ b ⇨ c ↔ b ⊓ a ≤ c := by rw [le_himp_iff, inf_comm]
#align le_himp_iff' le_himp_iff'

/- warning: le_himp_comm -> le_himp_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b c)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) b (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b c)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) b (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a c))
Case conversion may be inaccurate. Consider using '#align le_himp_comm le_himp_commₓ'. -/
-- `p → q → r ↔ q → p → r`
theorem le_himp_comm : a ≤ b ⇨ c ↔ b ≤ a ⇨ c := by rw [le_himp_iff, le_himp_iff']
#align le_himp_comm le_himp_comm

/- warning: le_himp -> le_himp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b a)
Case conversion may be inaccurate. Consider using '#align le_himp le_himpₓ'. -/
-- `p → q → p`
theorem le_himp : a ≤ b ⇨ a :=
  le_himp_iff.2 inf_le_left
#align le_himp le_himp

/- warning: le_himp_iff_left -> le_himp_iff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a b)
Case conversion may be inaccurate. Consider using '#align le_himp_iff_left le_himp_iff_leftₓ'. -/
-- `p → p → q ↔ p → q`
@[simp]
theorem le_himp_iff_left : a ≤ a ⇨ b ↔ a ≤ b := by rw [le_himp_iff, inf_idem]
#align le_himp_iff_left le_himp_iff_left

/- warning: himp_self -> himp_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α}, Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a a) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α}, Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a a) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align himp_self himp_selfₓ'. -/
-- `p → p`
@[simp]
theorem himp_self : a ⇨ a = ⊤ :=
  top_le_iff.1 <| le_himp_iff.2 inf_le_right
#align himp_self himp_self

/- warning: himp_inf_le -> himp_inf_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b) a) b
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b) a) b
Case conversion may be inaccurate. Consider using '#align himp_inf_le himp_inf_leₓ'. -/
-- `(p → q) ∧ p → q`
theorem himp_inf_le : (a ⇨ b) ⊓ a ≤ b :=
  le_himp_iff.1 le_rfl
#align himp_inf_le himp_inf_le

/- warning: inf_himp_le -> inf_himp_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b)) b
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b)) b
Case conversion may be inaccurate. Consider using '#align inf_himp_le inf_himp_leₓ'. -/
-- `p ∧ (p → q) → q`
theorem inf_himp_le : a ⊓ (a ⇨ b) ≤ b := by rw [inf_comm, ← le_himp_iff]
#align inf_himp_le inf_himp_le

/- warning: inf_himp -> inf_himp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align inf_himp inf_himpₓ'. -/
-- `p ∧ (p → q) ↔ p ∧ q`
@[simp]
theorem inf_himp (a b : α) : a ⊓ (a ⇨ b) = a ⊓ b :=
  le_antisymm (le_inf inf_le_left <| by rw [inf_comm, ← le_himp_iff]) <| inf_le_inf_left _ le_himp
#align inf_himp inf_himp

/- warning: himp_inf_self -> himp_inf_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b) a) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b) a) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) b a)
Case conversion may be inaccurate. Consider using '#align himp_inf_self himp_inf_selfₓ'. -/
-- `(p → q) ∧ p ↔ q ∧ p`
@[simp]
theorem himp_inf_self (a b : α) : (a ⇨ b) ⊓ a = b ⊓ a := by rw [inf_comm, inf_himp, inf_comm]
#align himp_inf_self himp_inf_self

/- warning: himp_eq_top_iff -> himp_eq_top_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toHasTop.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toTop.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a b)
Case conversion may be inaccurate. Consider using '#align himp_eq_top_iff himp_eq_top_iffₓ'. -/
/-- The **deduction theorem** in the Heyting algebra model of intuitionistic logic:
an implication holds iff the conclusion follows from the hypothesis. -/
@[simp]
theorem himp_eq_top_iff : a ⇨ b = ⊤ ↔ a ≤ b := by rw [← top_le_iff, le_himp_iff, top_inf_eq]
#align himp_eq_top_iff himp_eq_top_iff

/- warning: himp_top -> himp_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α}, Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a (Top.top.{u1} α (GeneralizedHeytingAlgebra.toHasTop.{u1} α _inst_1))) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α}, Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a (Top.top.{u1} α (GeneralizedHeytingAlgebra.toTop.{u1} α _inst_1))) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align himp_top himp_topₓ'. -/
-- `p → true`, `true → p ↔ p`
@[simp]
theorem himp_top : a ⇨ ⊤ = ⊤ :=
  himp_eq_top_iff.2 le_top
#align himp_top himp_top

/- warning: top_himp -> top_himp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α}, Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toHasTop.{u1} α _inst_1)) a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α}, Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toTop.{u1} α _inst_1)) a) a
Case conversion may be inaccurate. Consider using '#align top_himp top_himpₓ'. -/
@[simp]
theorem top_himp : ⊤ ⇨ a = a :=
  eq_of_forall_le_iff fun b => by rw [le_himp_iff, inf_top_eq]
#align top_himp top_himp

/- warning: himp_himp -> himp_himp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b c)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b c)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a b) c)
Case conversion may be inaccurate. Consider using '#align himp_himp himp_himpₓ'. -/
-- `p → q → r ↔ p ∧ q → r`
theorem himp_himp (a b c : α) : a ⇨ b ⇨ c = a ⊓ b ⇨ c :=
  eq_of_forall_le_iff fun d => by simp_rw [le_himp_iff, inf_assoc]
#align himp_himp himp_himp

/- warning: himp_le_himp_himp_himp -> himp_le_himp_himp_himp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b c) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b c) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a c))
Case conversion may be inaccurate. Consider using '#align himp_le_himp_himp_himp himp_le_himp_himp_himpₓ'. -/
-- `(q → r) → (p → q) → q → r`
@[simp]
theorem himp_le_himp_himp_himp : b ⇨ c ≤ (a ⇨ b) ⇨ a ⇨ c :=
  by
  rw [le_himp_iff, le_himp_iff, inf_assoc, himp_inf_self, ← inf_assoc, himp_inf_self, inf_assoc]
  exact inf_le_left
#align himp_le_himp_himp_himp himp_le_himp_himp_himp

/- warning: himp_left_comm -> himp_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b c)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b c)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a c))
Case conversion may be inaccurate. Consider using '#align himp_left_comm himp_left_commₓ'. -/
-- `p → q → r ↔ q → p → r`
theorem himp_left_comm (a b c : α) : a ⇨ b ⇨ c = b ⇨ a ⇨ c := by simp_rw [himp_himp, inf_comm]
#align himp_left_comm himp_left_comm

/- warning: himp_idem -> himp_idem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b a)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b a)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b a)
Case conversion may be inaccurate. Consider using '#align himp_idem himp_idemₓ'. -/
@[simp]
theorem himp_idem : b ⇨ b ⇨ a = b ⇨ a := by rw [himp_himp, inf_idem]
#align himp_idem himp_idem

/- warning: himp_inf_distrib -> himp_inf_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) b c)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) b c)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a c))
Case conversion may be inaccurate. Consider using '#align himp_inf_distrib himp_inf_distribₓ'. -/
theorem himp_inf_distrib (a b c : α) : a ⇨ b ⊓ c = (a ⇨ b) ⊓ (a ⇨ c) :=
  eq_of_forall_le_iff fun d => by simp_rw [le_himp_iff, le_inf_iff, le_himp_iff]
#align himp_inf_distrib himp_inf_distrib

/- warning: sup_himp_distrib -> sup_himp_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) c) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a c) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) c) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a c) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align sup_himp_distrib sup_himp_distribₓ'. -/
theorem sup_himp_distrib (a b c : α) : a ⊔ b ⇨ c = (a ⇨ c) ⊓ (b ⇨ c) :=
  eq_of_forall_le_iff fun d =>
    by
    rw [le_inf_iff, le_himp_comm, sup_le_iff]
    simp_rw [le_himp_comm]
#align sup_himp_distrib sup_himp_distrib

/- warning: himp_le_himp_left -> himp_le_himp_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) c a) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) c a) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) c b))
Case conversion may be inaccurate. Consider using '#align himp_le_himp_left himp_le_himp_leftₓ'. -/
theorem himp_le_himp_left (h : a ≤ b) : c ⇨ a ≤ c ⇨ b :=
  le_himp_iff.2 <| himp_inf_le.trans h
#align himp_le_himp_left himp_le_himp_left

/- warning: himp_le_himp_right -> himp_le_himp_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b c) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b c) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a c))
Case conversion may be inaccurate. Consider using '#align himp_le_himp_right himp_le_himp_rightₓ'. -/
theorem himp_le_himp_right (h : a ≤ b) : b ⇨ c ≤ a ⇨ c :=
  le_himp_iff.2 <| (inf_le_inf_left _ h).trans himp_inf_le
#align himp_le_himp_right himp_le_himp_right

/- warning: himp_le_himp -> himp_le_himp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) c d) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b c) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) c d) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b c) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a d))
Case conversion may be inaccurate. Consider using '#align himp_le_himp himp_le_himpₓ'. -/
theorem himp_le_himp (hab : a ≤ b) (hcd : c ≤ d) : b ⇨ c ≤ a ⇨ d :=
  (himp_le_himp_right hab).trans <| himp_le_himp_left hcd
#align himp_le_himp himp_le_himp

/- warning: sup_himp_self_left -> sup_himp_self_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) a) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) a) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b a)
Case conversion may be inaccurate. Consider using '#align sup_himp_self_left sup_himp_self_leftₓ'. -/
@[simp]
theorem sup_himp_self_left (a b : α) : a ⊔ b ⇨ a = b ⇨ a := by
  rw [sup_himp_distrib, himp_self, top_inf_eq]
#align sup_himp_self_left sup_himp_self_left

/- warning: sup_himp_self_right -> sup_himp_self_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b) b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align sup_himp_self_right sup_himp_self_rightₓ'. -/
@[simp]
theorem sup_himp_self_right (a b : α) : a ⊔ b ⇨ b = a ⇨ b := by
  rw [sup_himp_distrib, himp_self, inf_top_eq]
#align sup_himp_self_right sup_himp_self_right

/- warning: codisjoint.himp_eq_right -> Codisjoint.himp_eq_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b a) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b a) a)
Case conversion may be inaccurate. Consider using '#align codisjoint.himp_eq_right Codisjoint.himp_eq_rightₓ'. -/
theorem Codisjoint.himp_eq_right (h : Codisjoint a b) : b ⇨ a = a :=
  by
  conv_rhs => rw [← @top_himp _ _ a]
  rw [← h.eq_top, sup_himp_self_left]
#align codisjoint.himp_eq_right Codisjoint.himp_eq_right

/- warning: codisjoint.himp_eq_left -> Codisjoint.himp_eq_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b) b)
Case conversion may be inaccurate. Consider using '#align codisjoint.himp_eq_left Codisjoint.himp_eq_leftₓ'. -/
theorem Codisjoint.himp_eq_left (h : Codisjoint a b) : a ⇨ b = b :=
  h.symm.himp_eq_right
#align codisjoint.himp_eq_left Codisjoint.himp_eq_left

/- warning: codisjoint.himp_inf_cancel_right -> Codisjoint.himp_inf_cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b)) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a b)) b)
Case conversion may be inaccurate. Consider using '#align codisjoint.himp_inf_cancel_right Codisjoint.himp_inf_cancel_rightₓ'. -/
theorem Codisjoint.himp_inf_cancel_right (h : Codisjoint a b) : a ⇨ a ⊓ b = b := by
  rw [himp_inf_distrib, himp_self, top_inf_eq, h.himp_eq_left]
#align codisjoint.himp_inf_cancel_right Codisjoint.himp_inf_cancel_right

/- warning: codisjoint.himp_inf_cancel_left -> Codisjoint.himp_inf_cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) a b)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) a b)) a)
Case conversion may be inaccurate. Consider using '#align codisjoint.himp_inf_cancel_left Codisjoint.himp_inf_cancel_leftₓ'. -/
theorem Codisjoint.himp_inf_cancel_left (h : Codisjoint a b) : b ⇨ a ⊓ b = a := by
  rw [himp_inf_distrib, himp_self, inf_top_eq, h.himp_eq_right]
#align codisjoint.himp_inf_cancel_left Codisjoint.himp_inf_cancel_left

/- warning: le_himp_himp -> le_himp_himp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) a (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b) b)
Case conversion may be inaccurate. Consider using '#align le_himp_himp le_himp_himpₓ'. -/
theorem le_himp_himp : a ≤ (a ⇨ b) ⇨ b :=
  le_himp_iff.2 inf_himp_le
#align le_himp_himp le_himp_himp

/- warning: himp_triangle -> himp_triangle is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b c)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b c)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a c)
Case conversion may be inaccurate. Consider using '#align himp_triangle himp_triangleₓ'. -/
theorem himp_triangle (a b c : α) : (a ⇨ b) ⊓ (b ⇨ c) ≤ a ⇨ c :=
  by
  rw [le_himp_iff, inf_right_comm, ← le_himp_iff]
  exact himp_inf_le.trans le_himp_himp
#align himp_triangle himp_triangle

/- warning: himp_inf_himp_cancel -> himp_inf_himp_cancel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) b a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) c b) -> (Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) b c)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α _inst_1) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedHeytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) b a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1))))) c b) -> (Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α _inst_1)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) b c)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α _inst_1) a c))
Case conversion may be inaccurate. Consider using '#align himp_inf_himp_cancel himp_inf_himp_cancelₓ'. -/
theorem himp_inf_himp_cancel (hba : b ≤ a) (hcb : c ≤ b) : (a ⇨ b) ⊓ (b ⇨ c) = a ⇨ c :=
  (himp_triangle _ _ _).antisymm <| le_inf (himp_le_himp_left hcb) (himp_le_himp_right hba)
#align himp_inf_himp_cancel himp_inf_himp_cancel

#print GeneralizedHeytingAlgebra.toDistribLattice /-
-- See note [lower instance priority]
instance (priority := 100) GeneralizedHeytingAlgebra.toDistribLattice : DistribLattice α :=
  DistribLattice.ofInfSupLe fun a b c => by
    simp_rw [@inf_comm _ _ a, ← le_himp_iff, sup_le_iff, le_himp_iff, ← sup_le_iff]
#align generalized_heyting_algebra.to_distrib_lattice GeneralizedHeytingAlgebra.toDistribLattice
-/

instance : GeneralizedCoheytingAlgebra αᵒᵈ :=
  { OrderDual.lattice α,
    OrderDual.orderBot α with
    sdiff := fun a b => toDual (ofDual b ⇨ ofDual a)
    sdiff_le_iff := fun a b c => by
      rw [sup_comm]
      exact le_himp_iff }

#print Prod.generalizedHeytingAlgebra /-
instance Prod.generalizedHeytingAlgebra [GeneralizedHeytingAlgebra β] :
    GeneralizedHeytingAlgebra (α × β) :=
  { Prod.lattice α β, Prod.orderTop α β, Prod.hasHimp, Prod.hasCompl with
    le_himp_iff := fun a b c => and_congr le_himp_iff le_himp_iff }
#align prod.generalized_heyting_algebra Prod.generalizedHeytingAlgebra
-/

#print Pi.generalizedHeytingAlgebra /-
instance Pi.generalizedHeytingAlgebra {α : ι → Type _} [∀ i, GeneralizedHeytingAlgebra (α i)] :
    GeneralizedHeytingAlgebra (∀ i, α i) := by
  pi_instance
  exact fun a b c => forall_congr' fun i => le_himp_iff
#align pi.generalized_heyting_algebra Pi.generalizedHeytingAlgebra
-/

end GeneralizedHeytingAlgebra

section GeneralizedCoheytingAlgebra

variable [GeneralizedCoheytingAlgebra α] {a b c d : α}

/- warning: sdiff_le_iff -> sdiff_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) c) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) c) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b c))
Case conversion may be inaccurate. Consider using '#align sdiff_le_iff sdiff_le_iffₓ'. -/
@[simp]
theorem sdiff_le_iff : a \ b ≤ c ↔ a ≤ b ⊔ c :=
  GeneralizedCoheytingAlgebra.sdiff_le_iff _ _ _
#align sdiff_le_iff sdiff_le_iff

/- warning: sdiff_le_iff' -> sdiff_le_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) c) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) c) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) c b))
Case conversion may be inaccurate. Consider using '#align sdiff_le_iff' sdiff_le_iff'ₓ'. -/
theorem sdiff_le_iff' : a \ b ≤ c ↔ a ≤ c ⊔ b := by rw [sdiff_le_iff, sup_comm]
#align sdiff_le_iff' sdiff_le_iff'

/- warning: sdiff_le_comm -> sdiff_le_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) c) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) c) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a c) b)
Case conversion may be inaccurate. Consider using '#align sdiff_le_comm sdiff_le_commₓ'. -/
theorem sdiff_le_comm : a \ b ≤ c ↔ a \ c ≤ b := by rw [sdiff_le_iff, sdiff_le_iff']
#align sdiff_le_comm sdiff_le_comm

/- warning: sdiff_le -> sdiff_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) a
Case conversion may be inaccurate. Consider using '#align sdiff_le sdiff_leₓ'. -/
theorem sdiff_le : a \ b ≤ a :=
  sdiff_le_iff.2 le_sup_right
#align sdiff_le sdiff_le

/- warning: disjoint.disjoint_sdiff_left -> Disjoint.disjoint_sdiff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toOrderBot.{u1} α _inst_1) a b) -> (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toOrderBot.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toOrderBot.{u1} α _inst_1) a b) -> (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toOrderBot.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a c) b)
Case conversion may be inaccurate. Consider using '#align disjoint.disjoint_sdiff_left Disjoint.disjoint_sdiff_leftₓ'. -/
theorem Disjoint.disjoint_sdiff_left (h : Disjoint a b) : Disjoint (a \ c) b :=
  h.mono_left sdiff_le
#align disjoint.disjoint_sdiff_left Disjoint.disjoint_sdiff_left

/- warning: disjoint.disjoint_sdiff_right -> Disjoint.disjoint_sdiff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toOrderBot.{u1} α _inst_1) a b) -> (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toOrderBot.{u1} α _inst_1) a (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toOrderBot.{u1} α _inst_1) a b) -> (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toOrderBot.{u1} α _inst_1) a (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align disjoint.disjoint_sdiff_right Disjoint.disjoint_sdiff_rightₓ'. -/
theorem Disjoint.disjoint_sdiff_right (h : Disjoint a b) : Disjoint a (b \ c) :=
  h.mono_right sdiff_le
#align disjoint.disjoint_sdiff_right Disjoint.disjoint_sdiff_right

/- warning: sdiff_le_iff_left -> sdiff_le_iff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) b) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) b) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a b)
Case conversion may be inaccurate. Consider using '#align sdiff_le_iff_left sdiff_le_iff_leftₓ'. -/
@[simp]
theorem sdiff_le_iff_left : a \ b ≤ b ↔ a ≤ b := by rw [sdiff_le_iff, sup_idem]
#align sdiff_le_iff_left sdiff_le_iff_left

/- warning: sdiff_self -> sdiff_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a a) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a a) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align sdiff_self sdiff_selfₓ'. -/
@[simp]
theorem sdiff_self : a \ a = ⊥ :=
  le_bot_iff.1 <| sdiff_le_iff.2 le_sup_left
#align sdiff_self sdiff_self

/- warning: le_sup_sdiff -> le_sup_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align le_sup_sdiff le_sup_sdiffₓ'. -/
theorem le_sup_sdiff : a ≤ b ⊔ a \ b :=
  sdiff_le_iff.1 le_rfl
#align le_sup_sdiff le_sup_sdiff

/- warning: le_sdiff_sup -> le_sdiff_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) b)
Case conversion may be inaccurate. Consider using '#align le_sdiff_sup le_sdiff_supₓ'. -/
theorem le_sdiff_sup : a ≤ a \ b ⊔ b := by rw [sup_comm, ← sdiff_le_iff]
#align le_sdiff_sup le_sdiff_sup

/- warning: sup_sdiff_left -> sup_sdiff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b)) a
Case conversion may be inaccurate. Consider using '#align sup_sdiff_left sup_sdiff_leftₓ'. -/
@[simp]
theorem sup_sdiff_left : a ⊔ a \ b = a :=
  sup_of_le_left sdiff_le
#align sup_sdiff_left sup_sdiff_left

/- warning: sup_sdiff_right -> sup_sdiff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) a) a
Case conversion may be inaccurate. Consider using '#align sup_sdiff_right sup_sdiff_rightₓ'. -/
@[simp]
theorem sup_sdiff_right : a \ b ⊔ a = a :=
  sup_of_le_right sdiff_le
#align sup_sdiff_right sup_sdiff_right

/- warning: inf_sdiff_left -> inf_sdiff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) a) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1)) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) a) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align inf_sdiff_left inf_sdiff_leftₓ'. -/
@[simp]
theorem inf_sdiff_left : a \ b ⊓ a = a \ b :=
  inf_of_le_left sdiff_le
#align inf_sdiff_left inf_sdiff_left

/- warning: inf_sdiff_right -> inf_sdiff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b)) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1)) a (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b)) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align inf_sdiff_right inf_sdiff_rightₓ'. -/
@[simp]
theorem inf_sdiff_right : a ⊓ a \ b = a \ b :=
  inf_of_le_right sdiff_le
#align inf_sdiff_right inf_sdiff_right

/- warning: sup_sdiff_self -> sup_sdiff_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b a)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b a)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align sup_sdiff_self sup_sdiff_selfₓ'. -/
@[simp]
theorem sup_sdiff_self (a b : α) : a ⊔ b \ a = a ⊔ b :=
  le_antisymm (sup_le_sup_left sdiff_le _) (sup_le le_sup_left le_sup_sdiff)
#align sup_sdiff_self sup_sdiff_self

/- warning: sdiff_sup_self -> sdiff_sup_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b a) a) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b a) a) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b a)
Case conversion may be inaccurate. Consider using '#align sdiff_sup_self sdiff_sup_selfₓ'. -/
@[simp]
theorem sdiff_sup_self (a b : α) : b \ a ⊔ a = b ⊔ a := by rw [sup_comm, sup_sdiff_self, sup_comm]
#align sdiff_sup_self sdiff_sup_self

alias sdiff_sup_self ← sup_sdiff_self_left

alias sup_sdiff_self ← sup_sdiff_self_right

/- warning: sup_sdiff_eq_sup -> sup_sdiff_eq_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) c a) -> (Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b c)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) c a) -> (Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b c)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align sup_sdiff_eq_sup sup_sdiff_eq_supₓ'. -/
theorem sup_sdiff_eq_sup (h : c ≤ a) : a ⊔ b \ c = a ⊔ b :=
  sup_congr_left (sdiff_le.trans le_sup_right) <| le_sup_sdiff.trans <| sup_le_sup_right h _
#align sup_sdiff_eq_sup sup_sdiff_eq_sup

/- warning: sup_sdiff_cancel' -> sup_sdiff_cancel' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) b c) -> (Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) c a)) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) b c) -> (Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) c a)) c)
Case conversion may be inaccurate. Consider using '#align sup_sdiff_cancel' sup_sdiff_cancel'ₓ'. -/
-- cf. `set.union_diff_cancel'`
theorem sup_sdiff_cancel' (hab : a ≤ b) (hbc : b ≤ c) : b ⊔ c \ a = c := by
  rw [sup_sdiff_eq_sup hab, sup_of_le_right hbc]
#align sup_sdiff_cancel' sup_sdiff_cancel'

/- warning: sup_sdiff_cancel_right -> sup_sdiff_cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b a)) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b a)) b)
Case conversion may be inaccurate. Consider using '#align sup_sdiff_cancel_right sup_sdiff_cancel_rightₓ'. -/
theorem sup_sdiff_cancel_right (h : a ≤ b) : a ⊔ b \ a = b :=
  sup_sdiff_cancel' le_rfl h
#align sup_sdiff_cancel_right sup_sdiff_cancel_right

/- warning: sdiff_sup_cancel -> sdiff_sup_cancel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) b a) -> (Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) b a) -> (Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) b) a)
Case conversion may be inaccurate. Consider using '#align sdiff_sup_cancel sdiff_sup_cancelₓ'. -/
theorem sdiff_sup_cancel (h : b ≤ a) : a \ b ⊔ b = a := by rw [sup_comm, sup_sdiff_cancel_right h]
#align sdiff_sup_cancel sdiff_sup_cancel

/- warning: sup_le_of_le_sdiff_left -> sup_le_of_le_sdiff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) b (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) c a)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) b (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) c a)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) c)
Case conversion may be inaccurate. Consider using '#align sup_le_of_le_sdiff_left sup_le_of_le_sdiff_leftₓ'. -/
theorem sup_le_of_le_sdiff_left (h : b ≤ c \ a) (hac : a ≤ c) : a ⊔ b ≤ c :=
  sup_le hac <| h.trans sdiff_le
#align sup_le_of_le_sdiff_left sup_le_of_le_sdiff_left

/- warning: sup_le_of_le_sdiff_right -> sup_le_of_le_sdiff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) c b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) c b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) c)
Case conversion may be inaccurate. Consider using '#align sup_le_of_le_sdiff_right sup_le_of_le_sdiff_rightₓ'. -/
theorem sup_le_of_le_sdiff_right (h : a ≤ c \ b) (hbc : b ≤ c) : a ⊔ b ≤ c :=
  sup_le (h.trans sdiff_le) hbc
#align sup_le_of_le_sdiff_right sup_le_of_le_sdiff_right

/- warning: sdiff_eq_bot_iff -> sdiff_eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toHasBot.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toBot.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a b)
Case conversion may be inaccurate. Consider using '#align sdiff_eq_bot_iff sdiff_eq_bot_iffₓ'. -/
@[simp]
theorem sdiff_eq_bot_iff : a \ b = ⊥ ↔ a ≤ b := by rw [← le_bot_iff, sdiff_le_iff, sup_bot_eq]
#align sdiff_eq_bot_iff sdiff_eq_bot_iff

/- warning: sdiff_bot -> sdiff_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toHasBot.{u1} α _inst_1))) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toBot.{u1} α _inst_1))) a
Case conversion may be inaccurate. Consider using '#align sdiff_bot sdiff_botₓ'. -/
@[simp]
theorem sdiff_bot : a \ ⊥ = a :=
  eq_of_forall_ge_iff fun b => by rw [sdiff_le_iff, bot_sup_eq]
#align sdiff_bot sdiff_bot

/- warning: bot_sdiff -> bot_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toHasBot.{u1} α _inst_1)) a) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toBot.{u1} α _inst_1)) a) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align bot_sdiff bot_sdiffₓ'. -/
@[simp]
theorem bot_sdiff : ⊥ \ a = ⊥ :=
  sdiff_eq_bot_iff.2 bot_le
#align bot_sdiff bot_sdiff

/- warning: sdiff_sdiff_sdiff_le_sdiff -> sdiff_sdiff_sdiff_le_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a c)) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) c b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a c)) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) c b)
Case conversion may be inaccurate. Consider using '#align sdiff_sdiff_sdiff_le_sdiff sdiff_sdiff_sdiff_le_sdiffₓ'. -/
@[simp]
theorem sdiff_sdiff_sdiff_le_sdiff : (a \ b) \ (a \ c) ≤ c \ b :=
  by
  rw [sdiff_le_iff, sdiff_le_iff, sup_left_comm, sup_sdiff_self, sup_left_comm, sdiff_sup_self,
    sup_left_comm]
  exact le_sup_left
#align sdiff_sdiff_sdiff_le_sdiff sdiff_sdiff_sdiff_le_sdiff

/- warning: sdiff_sdiff -> sdiff_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) c) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) c) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b c))
Case conversion may be inaccurate. Consider using '#align sdiff_sdiff sdiff_sdiffₓ'. -/
theorem sdiff_sdiff (a b c : α) : (a \ b) \ c = a \ (b ⊔ c) :=
  eq_of_forall_ge_iff fun d => by simp_rw [sdiff_le_iff, sup_assoc]
#align sdiff_sdiff sdiff_sdiff

/- warning: sdiff_sdiff_left -> sdiff_sdiff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) c) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) c) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b c))
Case conversion may be inaccurate. Consider using '#align sdiff_sdiff_left sdiff_sdiff_leftₓ'. -/
theorem sdiff_sdiff_left : (a \ b) \ c = a \ (b ⊔ c) :=
  sdiff_sdiff _ _ _
#align sdiff_sdiff_left sdiff_sdiff_left

/- warning: sdiff_right_comm -> sdiff_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) c) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) c) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a c) b)
Case conversion may be inaccurate. Consider using '#align sdiff_right_comm sdiff_right_commₓ'. -/
theorem sdiff_right_comm (a b c : α) : (a \ b) \ c = (a \ c) \ b := by
  simp_rw [sdiff_sdiff, sup_comm]
#align sdiff_right_comm sdiff_right_comm

/- warning: sdiff_sdiff_comm -> sdiff_sdiff_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) c) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) c) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a c) b)
Case conversion may be inaccurate. Consider using '#align sdiff_sdiff_comm sdiff_sdiff_commₓ'. -/
theorem sdiff_sdiff_comm : (a \ b) \ c = (a \ c) \ b :=
  sdiff_right_comm _ _ _
#align sdiff_sdiff_comm sdiff_sdiff_comm

/- warning: sdiff_idem -> sdiff_idem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align sdiff_idem sdiff_idemₓ'. -/
@[simp]
theorem sdiff_idem : (a \ b) \ b = a \ b := by rw [sdiff_sdiff_left, sup_idem]
#align sdiff_idem sdiff_idem

/- warning: sdiff_sdiff_self -> sdiff_sdiff_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) a) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) a) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align sdiff_sdiff_self sdiff_sdiff_selfₓ'. -/
@[simp]
theorem sdiff_sdiff_self : (a \ b) \ a = ⊥ := by rw [sdiff_sdiff_comm, sdiff_self, bot_sdiff]
#align sdiff_sdiff_self sdiff_sdiff_self

/- warning: sup_sdiff_distrib -> sup_sdiff_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a c) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a c) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align sup_sdiff_distrib sup_sdiff_distribₓ'. -/
theorem sup_sdiff_distrib (a b c : α) : (a ⊔ b) \ c = a \ c ⊔ b \ c :=
  eq_of_forall_ge_iff fun d => by simp_rw [sdiff_le_iff, sup_le_iff, sdiff_le_iff]
#align sup_sdiff_distrib sup_sdiff_distrib

/- warning: sdiff_inf_distrib -> sdiff_inf_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b c)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1)) b c)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a c))
Case conversion may be inaccurate. Consider using '#align sdiff_inf_distrib sdiff_inf_distribₓ'. -/
theorem sdiff_inf_distrib (a b c : α) : a \ (b ⊓ c) = a \ b ⊔ a \ c :=
  eq_of_forall_ge_iff fun d =>
    by
    rw [sup_le_iff, sdiff_le_comm, le_inf_iff]
    simp_rw [sdiff_le_comm]
#align sdiff_inf_distrib sdiff_inf_distrib

/- warning: sup_sdiff -> sup_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a c) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a c) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align sup_sdiff sup_sdiffₓ'. -/
theorem sup_sdiff : (a ⊔ b) \ c = a \ c ⊔ b \ c :=
  sup_sdiff_distrib _ _ _
#align sup_sdiff sup_sdiff

/- warning: sup_sdiff_right_self -> sup_sdiff_right_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align sup_sdiff_right_self sup_sdiff_right_selfₓ'. -/
@[simp]
theorem sup_sdiff_right_self : (a ⊔ b) \ b = a \ b := by rw [sup_sdiff, sdiff_self, sup_bot_eq]
#align sup_sdiff_right_self sup_sdiff_right_self

/- warning: sup_sdiff_left_self -> sup_sdiff_left_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) a) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) a) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b a)
Case conversion may be inaccurate. Consider using '#align sup_sdiff_left_self sup_sdiff_left_selfₓ'. -/
@[simp]
theorem sup_sdiff_left_self : (a ⊔ b) \ a = b \ a := by rw [sup_comm, sup_sdiff_right_self]
#align sup_sdiff_left_self sup_sdiff_left_self

/- warning: sdiff_le_sdiff_right -> sdiff_le_sdiff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a c) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a c) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align sdiff_le_sdiff_right sdiff_le_sdiff_rightₓ'. -/
theorem sdiff_le_sdiff_right (h : a ≤ b) : a \ c ≤ b \ c :=
  sdiff_le_iff.2 <| h.trans <| le_sup_sdiff
#align sdiff_le_sdiff_right sdiff_le_sdiff_right

/- warning: sdiff_le_sdiff_left -> sdiff_le_sdiff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) c b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) c b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) c a))
Case conversion may be inaccurate. Consider using '#align sdiff_le_sdiff_left sdiff_le_sdiff_leftₓ'. -/
theorem sdiff_le_sdiff_left (h : a ≤ b) : c \ b ≤ c \ a :=
  sdiff_le_iff.2 <| le_sup_sdiff.trans <| sup_le_sup_right h _
#align sdiff_le_sdiff_left sdiff_le_sdiff_left

/- warning: sdiff_le_sdiff -> sdiff_le_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) c d) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a d) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) c d) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a d) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align sdiff_le_sdiff sdiff_le_sdiffₓ'. -/
theorem sdiff_le_sdiff (hab : a ≤ b) (hcd : c ≤ d) : a \ d ≤ b \ c :=
  (sdiff_le_sdiff_right hab).trans <| sdiff_le_sdiff_left hcd
#align sdiff_le_sdiff sdiff_le_sdiff

/- warning: sdiff_inf -> sdiff_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b c)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1)) b c)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a c))
Case conversion may be inaccurate. Consider using '#align sdiff_inf sdiff_infₓ'. -/
-- cf. `is_compl.inf_sup`
theorem sdiff_inf : a \ (b ⊓ c) = a \ b ⊔ a \ c :=
  sdiff_inf_distrib _ _ _
#align sdiff_inf sdiff_inf

/- warning: sdiff_inf_self_left -> sdiff_inf_self_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1)) a b)) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align sdiff_inf_self_left sdiff_inf_self_leftₓ'. -/
@[simp]
theorem sdiff_inf_self_left (a b : α) : a \ (a ⊓ b) = a \ b := by
  rw [sdiff_inf, sdiff_self, bot_sup_eq]
#align sdiff_inf_self_left sdiff_inf_self_left

/- warning: sdiff_inf_self_right -> sdiff_inf_self_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1)) a b)) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b a)
Case conversion may be inaccurate. Consider using '#align sdiff_inf_self_right sdiff_inf_self_rightₓ'. -/
@[simp]
theorem sdiff_inf_self_right (a b : α) : b \ (a ⊓ b) = b \ a := by
  rw [sdiff_inf, sdiff_self, sup_bot_eq]
#align sdiff_inf_self_right sdiff_inf_self_right

/- warning: disjoint.sdiff_eq_left -> Disjoint.sdiff_eq_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toOrderBot.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toOrderBot.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) a)
Case conversion may be inaccurate. Consider using '#align disjoint.sdiff_eq_left Disjoint.sdiff_eq_leftₓ'. -/
theorem Disjoint.sdiff_eq_left (h : Disjoint a b) : a \ b = a :=
  by
  conv_rhs => rw [← @sdiff_bot _ _ a]
  rw [← h.eq_bot, sdiff_inf_self_left]
#align disjoint.sdiff_eq_left Disjoint.sdiff_eq_left

/- warning: disjoint.sdiff_eq_right -> Disjoint.sdiff_eq_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toOrderBot.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b a) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toOrderBot.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b a) b)
Case conversion may be inaccurate. Consider using '#align disjoint.sdiff_eq_right Disjoint.sdiff_eq_rightₓ'. -/
theorem Disjoint.sdiff_eq_right (h : Disjoint a b) : b \ a = b :=
  h.symm.sdiff_eq_left
#align disjoint.sdiff_eq_right Disjoint.sdiff_eq_right

/- warning: disjoint.sup_sdiff_cancel_left -> Disjoint.sup_sdiff_cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toOrderBot.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) a) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toOrderBot.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) a) b)
Case conversion may be inaccurate. Consider using '#align disjoint.sup_sdiff_cancel_left Disjoint.sup_sdiff_cancel_leftₓ'. -/
theorem Disjoint.sup_sdiff_cancel_left (h : Disjoint a b) : (a ⊔ b) \ a = b := by
  rw [sup_sdiff, sdiff_self, bot_sup_eq, h.sdiff_eq_right]
#align disjoint.sup_sdiff_cancel_left Disjoint.sup_sdiff_cancel_left

/- warning: disjoint.sup_sdiff_cancel_right -> Disjoint.sup_sdiff_cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toOrderBot.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (GeneralizedCoheytingAlgebra.toOrderBot.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b) b) a)
Case conversion may be inaccurate. Consider using '#align disjoint.sup_sdiff_cancel_right Disjoint.sup_sdiff_cancel_rightₓ'. -/
theorem Disjoint.sup_sdiff_cancel_right (h : Disjoint a b) : (a ⊔ b) \ b = a := by
  rw [sup_sdiff, sdiff_self, sup_bot_eq, h.sdiff_eq_left]
#align disjoint.sup_sdiff_cancel_right Disjoint.sup_sdiff_cancel_right

/- warning: sdiff_sdiff_le -> sdiff_sdiff_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b)) b
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b)) b
Case conversion may be inaccurate. Consider using '#align sdiff_sdiff_le sdiff_sdiff_leₓ'. -/
theorem sdiff_sdiff_le : a \ (a \ b) ≤ b :=
  sdiff_le_iff.2 le_sdiff_sup
#align sdiff_sdiff_le sdiff_sdiff_le

/- warning: sdiff_triangle -> sdiff_triangle is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align sdiff_triangle sdiff_triangleₓ'. -/
theorem sdiff_triangle (a b c : α) : a \ c ≤ a \ b ⊔ b \ c :=
  by
  rw [sdiff_le_iff, sup_left_comm, ← sdiff_le_iff]
  exact sdiff_sdiff_le.trans le_sup_sdiff
#align sdiff_triangle sdiff_triangle

/- warning: sdiff_sup_sdiff_cancel -> sdiff_sup_sdiff_cancel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) b a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) c b) -> (Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b c)) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) b a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) c b) -> (Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b c)) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a c))
Case conversion may be inaccurate. Consider using '#align sdiff_sup_sdiff_cancel sdiff_sup_sdiff_cancelₓ'. -/
theorem sdiff_sup_sdiff_cancel (hba : b ≤ a) (hcb : c ≤ b) : a \ b ⊔ b \ c = a \ c :=
  (sdiff_triangle _ _ _).antisymm' <| sup_le (sdiff_le_sdiff_left hcb) (sdiff_le_sdiff_right hba)
#align sdiff_sup_sdiff_cancel sdiff_sup_sdiff_cancel

/- warning: sdiff_le_sdiff_of_sup_le_sup_left -> sdiff_le_sdiff_of_sup_le_sup_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) c a) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) c b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a c) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) c a) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) c b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a c) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align sdiff_le_sdiff_of_sup_le_sup_left sdiff_le_sdiff_of_sup_le_sup_leftₓ'. -/
theorem sdiff_le_sdiff_of_sup_le_sup_left (h : c ⊔ a ≤ c ⊔ b) : a \ c ≤ b \ c :=
  by
  rw [← sup_sdiff_left_self, ← @sup_sdiff_left_self _ _ _ b]
  exact sdiff_le_sdiff_right h
#align sdiff_le_sdiff_of_sup_le_sup_left sdiff_le_sdiff_of_sup_le_sup_left

/- warning: sdiff_le_sdiff_of_sup_le_sup_right -> sdiff_le_sdiff_of_sup_le_sup_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a c) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a c) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align sdiff_le_sdiff_of_sup_le_sup_right sdiff_le_sdiff_of_sup_le_sup_rightₓ'. -/
theorem sdiff_le_sdiff_of_sup_le_sup_right (h : a ⊔ c ≤ b ⊔ c) : a \ c ≤ b \ c :=
  by
  rw [← sup_sdiff_right_self, ← @sup_sdiff_right_self _ _ b]
  exact sdiff_le_sdiff_right h
#align sdiff_le_sdiff_of_sup_le_sup_right sdiff_le_sdiff_of_sup_le_sup_right

/- warning: inf_sdiff_sup_left -> inf_sdiff_sup_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1)) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) a b)) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a c)
Case conversion may be inaccurate. Consider using '#align inf_sdiff_sup_left inf_sdiff_sup_leftₓ'. -/
@[simp]
theorem inf_sdiff_sup_left : a \ c ⊓ (a ⊔ b) = a \ c :=
  inf_of_le_left <| sdiff_le.trans le_sup_left
#align inf_sdiff_sup_left inf_sdiff_sup_left

/- warning: inf_sdiff_sup_right -> inf_sdiff_sup_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b a)) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α _inst_1) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedCoheytingAlgebra.{u1} α] {a : α} {b : α} {c : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1)) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α _inst_1))) b a)) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α _inst_1) a c)
Case conversion may be inaccurate. Consider using '#align inf_sdiff_sup_right inf_sdiff_sup_rightₓ'. -/
@[simp]
theorem inf_sdiff_sup_right : a \ c ⊓ (b ⊔ a) = a \ c :=
  inf_of_le_left <| sdiff_le.trans le_sup_right
#align inf_sdiff_sup_right inf_sdiff_sup_right

#print GeneralizedCoheytingAlgebra.toDistribLattice /-
-- See note [lower instance priority]
instance (priority := 100) GeneralizedCoheytingAlgebra.toDistribLattice : DistribLattice α :=
  { ‹GeneralizedCoheytingAlgebra α› with
    le_sup_inf := fun a b c => by simp_rw [← sdiff_le_iff, le_inf_iff, sdiff_le_iff, ← le_inf_iff] }
#align generalized_coheyting_algebra.to_distrib_lattice GeneralizedCoheytingAlgebra.toDistribLattice
-/

instance : GeneralizedHeytingAlgebra αᵒᵈ :=
  { OrderDual.lattice α,
    OrderDual.orderTop α with
    himp := fun a b => toDual (ofDual b \ ofDual a)
    le_himp_iff := fun a b c => by
      rw [inf_comm]
      exact sdiff_le_iff }

#print Prod.generalizedCoheytingAlgebra /-
instance Prod.generalizedCoheytingAlgebra [GeneralizedCoheytingAlgebra β] :
    GeneralizedCoheytingAlgebra (α × β) :=
  { Prod.lattice α β, Prod.orderBot α β, Prod.hasSdiff, Prod.hasHnot with
    sdiff_le_iff := fun a b c => and_congr sdiff_le_iff sdiff_le_iff }
#align prod.generalized_coheyting_algebra Prod.generalizedCoheytingAlgebra
-/

#print Pi.generalizedCoheytingAlgebra /-
instance Pi.generalizedCoheytingAlgebra {α : ι → Type _} [∀ i, GeneralizedCoheytingAlgebra (α i)] :
    GeneralizedCoheytingAlgebra (∀ i, α i) :=
  by
  pi_instance
  exact fun a b c => forall_congr' fun i => sdiff_le_iff
#align pi.generalized_coheyting_algebra Pi.generalizedCoheytingAlgebra
-/

end GeneralizedCoheytingAlgebra

section HeytingAlgebra

variable [HeytingAlgebra α] {a b c : α}

/- warning: himp_bot -> himp_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a (Bot.bot.{u1} α (HeytingAlgebra.toHasBot.{u1} α _inst_1))) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a (Bot.bot.{u1} α (HeytingAlgebra.toBot.{u1} α _inst_1))) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align himp_bot himp_botₓ'. -/
@[simp]
theorem himp_bot (a : α) : a ⇨ ⊥ = aᶜ :=
  HeytingAlgebra.himp_bot _
#align himp_bot himp_bot

/- warning: bot_himp -> bot_himp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) (Bot.bot.{u1} α (HeytingAlgebra.toHasBot.{u1} α _inst_1)) a) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toHasTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) (Bot.bot.{u1} α (HeytingAlgebra.toBot.{u1} α _inst_1)) a) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align bot_himp bot_himpₓ'. -/
@[simp]
theorem bot_himp (a : α) : ⊥ ⇨ a = ⊤ :=
  himp_eq_top_iff.2 bot_le
#align bot_himp bot_himp

#print compl_sup_distrib /-
theorem compl_sup_distrib (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ := by
  simp_rw [← himp_bot, sup_himp_distrib]
#align compl_sup_distrib compl_sup_distrib
-/

#print compl_sup /-
@[simp]
theorem compl_sup : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ :=
  compl_sup_distrib _ _
#align compl_sup compl_sup
-/

/- warning: compl_le_himp -> compl_le_himp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))))) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))))) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align compl_le_himp compl_le_himpₓ'. -/
theorem compl_le_himp : aᶜ ≤ a ⇨ b :=
  (himp_bot _).ge.trans <| himp_le_himp_left bot_le
#align compl_le_himp compl_le_himp

/- warning: compl_sup_le_himp -> compl_sup_le_himp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a) b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a) b) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align compl_sup_le_himp compl_sup_le_himpₓ'. -/
theorem compl_sup_le_himp : aᶜ ⊔ b ≤ a ⇨ b :=
  sup_le compl_le_himp le_himp
#align compl_sup_le_himp compl_sup_le_himp

/- warning: sup_compl_le_himp -> sup_compl_le_himp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) b (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) b (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align sup_compl_le_himp sup_compl_le_himpₓ'. -/
theorem sup_compl_le_himp : b ⊔ aᶜ ≤ a ⇨ b :=
  sup_le le_himp compl_le_himp
#align sup_compl_le_himp sup_compl_le_himp

/- warning: himp_compl -> himp_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align himp_compl himp_complₓ'. -/
-- `p → ¬ p ↔ ¬ p`
@[simp]
theorem himp_compl (a : α) : a ⇨ aᶜ = aᶜ := by rw [← himp_bot, himp_himp, inf_idem]
#align himp_compl himp_compl

/- warning: himp_compl_comm -> himp_compl_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) b)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) b (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) b)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) b (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a))
Case conversion may be inaccurate. Consider using '#align himp_compl_comm himp_compl_commₓ'. -/
-- `p → ¬ q ↔ q → ¬ p`
theorem himp_compl_comm (a b : α) : a ⇨ bᶜ = b ⇨ aᶜ := by simp_rw [← himp_bot, himp_left_comm]
#align himp_compl_comm himp_compl_comm

#print le_compl_iff_disjoint_right /-
theorem le_compl_iff_disjoint_right : a ≤ bᶜ ↔ Disjoint a b := by
  rw [← himp_bot, le_himp_iff, disjoint_iff_inf_le]
#align le_compl_iff_disjoint_right le_compl_iff_disjoint_right
-/

#print le_compl_iff_disjoint_left /-
theorem le_compl_iff_disjoint_left : a ≤ bᶜ ↔ Disjoint b a :=
  le_compl_iff_disjoint_right.trans Disjoint.comm
#align le_compl_iff_disjoint_left le_compl_iff_disjoint_left
-/

#print le_compl_comm /-
theorem le_compl_comm : a ≤ bᶜ ↔ b ≤ aᶜ := by
  rw [le_compl_iff_disjoint_right, le_compl_iff_disjoint_left]
#align le_compl_comm le_compl_comm
-/

alias le_compl_iff_disjoint_right ↔ _ Disjoint.le_compl_right

alias le_compl_iff_disjoint_left ↔ _ Disjoint.le_compl_left

alias le_compl_comm ← le_compl_iff_le_compl

alias le_compl_comm ↔ le_compl_of_le_compl _

#print disjoint_compl_left /-
theorem disjoint_compl_left : Disjoint (aᶜ) a :=
  disjoint_iff_inf_le.mpr <| le_himp_iff.1 (himp_bot _).ge
#align disjoint_compl_left disjoint_compl_left
-/

#print disjoint_compl_right /-
theorem disjoint_compl_right : Disjoint a (aᶜ) :=
  disjoint_compl_left.symm
#align disjoint_compl_right disjoint_compl_right
-/

#print LE.le.disjoint_compl_left /-
theorem LE.le.disjoint_compl_left (h : b ≤ a) : Disjoint (aᶜ) b :=
  disjoint_compl_left.mono_right h
#align has_le.le.disjoint_compl_left LE.le.disjoint_compl_left
-/

#print LE.le.disjoint_compl_right /-
theorem LE.le.disjoint_compl_right (h : a ≤ b) : Disjoint a (bᶜ) :=
  disjoint_compl_right.mono_left h
#align has_le.le.disjoint_compl_right LE.le.disjoint_compl_right
-/

#print IsCompl.compl_eq /-
theorem IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b :=
  h.1.le_compl_left.antisymm' <| Disjoint.le_of_codisjoint disjoint_compl_left h.2
#align is_compl.compl_eq IsCompl.compl_eq
-/

#print IsCompl.eq_compl /-
theorem IsCompl.eq_compl (h : IsCompl a b) : a = bᶜ :=
  h.1.le_compl_right.antisymm <| Disjoint.le_of_codisjoint disjoint_compl_left h.2.symm
#align is_compl.eq_compl IsCompl.eq_compl
-/

/- warning: compl_unique -> compl_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] {a : α} {b : α}, (Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) a b) (Bot.bot.{u1} α (HeytingAlgebra.toHasBot.{u1} α _inst_1))) -> (Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) a b) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toHasTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) -> (Eq.{succ u1} α (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] {a : α} {b : α}, (Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1))) a b) (Bot.bot.{u1} α (HeytingAlgebra.toBot.{u1} α _inst_1))) -> (Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) a b) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) -> (Eq.{succ u1} α (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a) b)
Case conversion may be inaccurate. Consider using '#align compl_unique compl_uniqueₓ'. -/
theorem compl_unique (h₀ : a ⊓ b = ⊥) (h₁ : a ⊔ b = ⊤) : aᶜ = b :=
  (IsCompl.of_eq h₀ h₁).compl_eq
#align compl_unique compl_unique

/- warning: inf_compl_self -> inf_compl_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) a (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)) (Bot.bot.{u1} α (HeytingAlgebra.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1))) a (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)) (Bot.bot.{u1} α (HeytingAlgebra.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align inf_compl_self inf_compl_selfₓ'. -/
@[simp]
theorem inf_compl_self (a : α) : a ⊓ aᶜ = ⊥ :=
  disjoint_compl_right.eq_bot
#align inf_compl_self inf_compl_self

/- warning: compl_inf_self -> compl_inf_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a) a) (Bot.bot.{u1} α (HeytingAlgebra.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1))) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a) a) (Bot.bot.{u1} α (HeytingAlgebra.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align compl_inf_self compl_inf_selfₓ'. -/
@[simp]
theorem compl_inf_self (a : α) : aᶜ ⊓ a = ⊥ :=
  disjoint_compl_left.eq_bot
#align compl_inf_self compl_inf_self

/- warning: inf_compl_eq_bot -> inf_compl_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] {a : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) a (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)) (Bot.bot.{u1} α (HeytingAlgebra.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] {a : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1))) a (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)) (Bot.bot.{u1} α (HeytingAlgebra.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align inf_compl_eq_bot inf_compl_eq_botₓ'. -/
theorem inf_compl_eq_bot : a ⊓ aᶜ = ⊥ :=
  inf_compl_self _
#align inf_compl_eq_bot inf_compl_eq_bot

/- warning: compl_inf_eq_bot -> compl_inf_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] {a : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a) a) (Bot.bot.{u1} α (HeytingAlgebra.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] {a : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1))) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a) a) (Bot.bot.{u1} α (HeytingAlgebra.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align compl_inf_eq_bot compl_inf_eq_botₓ'. -/
theorem compl_inf_eq_bot : aᶜ ⊓ a = ⊥ :=
  compl_inf_self _
#align compl_inf_eq_bot compl_inf_eq_bot

/- warning: compl_top -> compl_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α], Eq.{succ u1} α (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toHasTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) (Bot.bot.{u1} α (HeytingAlgebra.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α], Eq.{succ u1} α (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) (Bot.bot.{u1} α (HeytingAlgebra.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align compl_top compl_topₓ'. -/
@[simp]
theorem compl_top : (⊤ : α)ᶜ = ⊥ :=
  eq_of_forall_le_iff fun a => by rw [le_compl_iff_disjoint_right, disjoint_top, le_bot_iff]
#align compl_top compl_top

/- warning: compl_bot -> compl_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α], Eq.{succ u1} α (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) (Bot.bot.{u1} α (HeytingAlgebra.toHasBot.{u1} α _inst_1))) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toHasTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α], Eq.{succ u1} α (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) (Bot.bot.{u1} α (HeytingAlgebra.toBot.{u1} α _inst_1))) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align compl_bot compl_botₓ'. -/
@[simp]
theorem compl_bot : (⊥ : α)ᶜ = ⊤ := by rw [← himp_bot, himp_self]
#align compl_bot compl_bot

#print le_compl_compl /-
theorem le_compl_compl : a ≤ aᶜᶜ :=
  disjoint_compl_right.le_compl_right
#align le_compl_compl le_compl_compl
-/

#print compl_anti /-
theorem compl_anti : Antitone (compl : α → α) := fun a b h =>
  le_compl_comm.1 <| h.trans le_compl_compl
#align compl_anti compl_anti
-/

#print compl_le_compl /-
theorem compl_le_compl (h : a ≤ b) : bᶜ ≤ aᶜ :=
  compl_anti h
#align compl_le_compl compl_le_compl
-/

#print compl_compl_compl /-
@[simp]
theorem compl_compl_compl (a : α) : aᶜᶜᶜ = aᶜ :=
  (compl_anti le_compl_compl).antisymm le_compl_compl
#align compl_compl_compl compl_compl_compl
-/

#print disjoint_compl_compl_left_iff /-
@[simp]
theorem disjoint_compl_compl_left_iff : Disjoint (aᶜᶜ) b ↔ Disjoint a b := by
  simp_rw [← le_compl_iff_disjoint_left, compl_compl_compl]
#align disjoint_compl_compl_left_iff disjoint_compl_compl_left_iff
-/

#print disjoint_compl_compl_right_iff /-
@[simp]
theorem disjoint_compl_compl_right_iff : Disjoint a (bᶜᶜ) ↔ Disjoint a b := by
  simp_rw [← le_compl_iff_disjoint_right, compl_compl_compl]
#align disjoint_compl_compl_right_iff disjoint_compl_compl_right_iff
-/

#print compl_sup_compl_le /-
theorem compl_sup_compl_le : aᶜ ⊔ bᶜ ≤ (a ⊓ b)ᶜ :=
  sup_le (compl_anti inf_le_left) <| compl_anti inf_le_right
#align compl_sup_compl_le compl_sup_compl_le
-/

#print compl_compl_inf_distrib /-
theorem compl_compl_inf_distrib (a b : α) : (a ⊓ b)ᶜᶜ = aᶜᶜ ⊓ bᶜᶜ :=
  by
  refine' ((compl_anti compl_sup_compl_le).trans (compl_sup_distrib _ _).le).antisymm _
  rw [le_compl_iff_disjoint_right, disjoint_assoc, disjoint_compl_compl_left_iff,
    disjoint_left_comm, disjoint_compl_compl_left_iff, ← disjoint_assoc, inf_comm]
  exact disjoint_compl_right
#align compl_compl_inf_distrib compl_compl_inf_distrib
-/

/- warning: compl_compl_himp_distrib -> compl_compl_himp_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a b))) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a b))) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a)) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) b)))
Case conversion may be inaccurate. Consider using '#align compl_compl_himp_distrib compl_compl_himp_distribₓ'. -/
theorem compl_compl_himp_distrib (a b : α) : (a ⇨ b)ᶜᶜ = aᶜᶜ ⇨ bᶜᶜ :=
  by
  refine' le_antisymm _ _
  · rw [le_himp_iff, ← compl_compl_inf_distrib]
    exact compl_anti (compl_anti himp_inf_le)
  · refine' le_compl_comm.1 ((compl_anti compl_sup_le_himp).trans _)
    rw [compl_sup_distrib, le_compl_iff_disjoint_right, disjoint_right_comm, ←
      le_compl_iff_disjoint_right]
    exact inf_himp_le
#align compl_compl_himp_distrib compl_compl_himp_distrib

instance : CoheytingAlgebra αᵒᵈ :=
  { OrderDual.lattice α,
    OrderDual.boundedOrder α with
    hnot := to_dual ∘ compl ∘ of_dual
    sdiff := fun a b => toDual (ofDual b ⇨ ofDual a)
    sdiff_le_iff := fun a b c => by
      rw [sup_comm]
      exact le_himp_iff
    top_sdiff := himp_bot }

#print ofDual_hnot /-
@[simp]
theorem ofDual_hnot (a : αᵒᵈ) : ofDual (￢a) = ofDual aᶜ :=
  rfl
#align of_dual_hnot ofDual_hnot
-/

#print toDual_compl /-
@[simp]
theorem toDual_compl (a : α) : toDual (aᶜ) = ￢toDual a :=
  rfl
#align to_dual_compl toDual_compl
-/

#print Prod.heytingAlgebra /-
instance Prod.heytingAlgebra [HeytingAlgebra β] : HeytingAlgebra (α × β) :=
  { Prod.generalizedHeytingAlgebra, Prod.boundedOrder α β, Prod.hasCompl with
    himp_bot := fun a => Prod.ext (himp_bot a.1) (himp_bot a.2) }
#align prod.heyting_algebra Prod.heytingAlgebra
-/

#print Pi.heytingAlgebra /-
instance Pi.heytingAlgebra {α : ι → Type _} [∀ i, HeytingAlgebra (α i)] :
    HeytingAlgebra (∀ i, α i) := by
  pi_instance
  exact fun a b c => forall_congr' fun i => le_himp_iff
#align pi.heyting_algebra Pi.heytingAlgebra
-/

end HeytingAlgebra

section CoheytingAlgebra

variable [CoheytingAlgebra α] {a b c : α}

/- warning: top_sdiff' -> top_sdiff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) (Top.top.{u1} α (CoheytingAlgebra.toHasTop.{u1} α _inst_1)) a) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) (Top.top.{u1} α (CoheytingAlgebra.toTop.{u1} α _inst_1)) a) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align top_sdiff' top_sdiff'ₓ'. -/
@[simp]
theorem top_sdiff' (a : α) : ⊤ \ a = ￢a :=
  CoheytingAlgebra.top_sdiff _
#align top_sdiff' top_sdiff'

/- warning: sdiff_top -> sdiff_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) a (Top.top.{u1} α (CoheytingAlgebra.toHasTop.{u1} α _inst_1))) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toHasBot.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) a (Top.top.{u1} α (CoheytingAlgebra.toTop.{u1} α _inst_1))) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toBot.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align sdiff_top sdiff_topₓ'. -/
@[simp]
theorem sdiff_top (a : α) : a \ ⊤ = ⊥ :=
  sdiff_eq_bot_iff.2 le_top
#align sdiff_top sdiff_top

/- warning: hnot_inf_distrib -> hnot_inf_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) b))
Case conversion may be inaccurate. Consider using '#align hnot_inf_distrib hnot_inf_distribₓ'. -/
theorem hnot_inf_distrib (a b : α) : ￢(a ⊓ b) = ￢a ⊔ ￢b := by
  simp_rw [← top_sdiff', sdiff_inf_distrib]
#align hnot_inf_distrib hnot_inf_distrib

/- warning: sdiff_le_hnot -> sdiff_le_hnot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) a b) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) a b) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) b)
Case conversion may be inaccurate. Consider using '#align sdiff_le_hnot sdiff_le_hnotₓ'. -/
theorem sdiff_le_hnot : a \ b ≤ ￢b :=
  (sdiff_le_sdiff_right le_top).trans_eq <| top_sdiff' _
#align sdiff_le_hnot sdiff_le_hnot

/- warning: sdiff_le_inf_hnot -> sdiff_le_inf_hnot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) a b) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) a b) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) a (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) b))
Case conversion may be inaccurate. Consider using '#align sdiff_le_inf_hnot sdiff_le_inf_hnotₓ'. -/
theorem sdiff_le_inf_hnot : a \ b ≤ a ⊓ ￢b :=
  le_inf sdiff_le sdiff_le_hnot
#align sdiff_le_inf_hnot sdiff_le_inf_hnot

#print CoheytingAlgebra.toDistribLattice /-
-- See note [lower instance priority]
instance (priority := 100) CoheytingAlgebra.toDistribLattice : DistribLattice α :=
  { ‹CoheytingAlgebra α› with
    le_sup_inf := fun a b c => by simp_rw [← sdiff_le_iff, le_inf_iff, sdiff_le_iff, ← le_inf_iff] }
#align coheyting_algebra.to_distrib_lattice CoheytingAlgebra.toDistribLattice
-/

/- warning: hnot_sdiff -> hnot_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a) a) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a) a) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align hnot_sdiff hnot_sdiffₓ'. -/
@[simp]
theorem hnot_sdiff (a : α) : ￢a \ a = ￢a := by rw [← top_sdiff', sdiff_sdiff, sup_idem]
#align hnot_sdiff hnot_sdiff

/- warning: hnot_sdiff_comm -> hnot_sdiff_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a) b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a) b) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) b) a)
Case conversion may be inaccurate. Consider using '#align hnot_sdiff_comm hnot_sdiff_commₓ'. -/
theorem hnot_sdiff_comm (a b : α) : ￢a \ b = ￢b \ a := by simp_rw [← top_sdiff', sdiff_right_comm]
#align hnot_sdiff_comm hnot_sdiff_comm

/- warning: hnot_le_iff_codisjoint_right -> hnot_le_iff_codisjoint_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a) b) (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a) b) (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align hnot_le_iff_codisjoint_right hnot_le_iff_codisjoint_rightₓ'. -/
theorem hnot_le_iff_codisjoint_right : ￢a ≤ b ↔ Codisjoint a b := by
  rw [← top_sdiff', sdiff_le_iff, codisjoint_iff_le_sup]
#align hnot_le_iff_codisjoint_right hnot_le_iff_codisjoint_right

/- warning: hnot_le_iff_codisjoint_left -> hnot_le_iff_codisjoint_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a) b) (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a) b) (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) b a)
Case conversion may be inaccurate. Consider using '#align hnot_le_iff_codisjoint_left hnot_le_iff_codisjoint_leftₓ'. -/
theorem hnot_le_iff_codisjoint_left : ￢a ≤ b ↔ Codisjoint b a :=
  hnot_le_iff_codisjoint_right.trans Codisjoint.comm
#align hnot_le_iff_codisjoint_left hnot_le_iff_codisjoint_left

/- warning: hnot_le_comm -> hnot_le_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a) b) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a) b) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) b) a)
Case conversion may be inaccurate. Consider using '#align hnot_le_comm hnot_le_commₓ'. -/
theorem hnot_le_comm : ￢a ≤ b ↔ ￢b ≤ a := by
  rw [hnot_le_iff_codisjoint_right, hnot_le_iff_codisjoint_left]
#align hnot_le_comm hnot_le_comm

alias hnot_le_iff_codisjoint_right ↔ _ Codisjoint.hnot_le_right

alias hnot_le_iff_codisjoint_left ↔ _ Codisjoint.hnot_le_left

/- warning: codisjoint_hnot_right -> codisjoint_hnot_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α}, Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) a (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α}, Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) a (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align codisjoint_hnot_right codisjoint_hnot_rightₓ'. -/
theorem codisjoint_hnot_right : Codisjoint a (￢a) :=
  codisjoint_iff_le_sup.2 <| sdiff_le_iff.1 (top_sdiff' _).le
#align codisjoint_hnot_right codisjoint_hnot_right

/- warning: codisjoint_hnot_left -> codisjoint_hnot_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α}, Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α}, Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a) a
Case conversion may be inaccurate. Consider using '#align codisjoint_hnot_left codisjoint_hnot_leftₓ'. -/
theorem codisjoint_hnot_left : Codisjoint (￢a) a :=
  codisjoint_hnot_right.symm
#align codisjoint_hnot_left codisjoint_hnot_left

/- warning: has_le.le.codisjoint_hnot_left -> LE.le.codisjoint_hnot_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) a b) -> (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) a b) -> (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a) b)
Case conversion may be inaccurate. Consider using '#align has_le.le.codisjoint_hnot_left LE.le.codisjoint_hnot_leftₓ'. -/
theorem LE.le.codisjoint_hnot_left (h : a ≤ b) : Codisjoint (￢a) b :=
  codisjoint_hnot_left.mono_right h
#align has_le.le.codisjoint_hnot_left LE.le.codisjoint_hnot_left

/- warning: has_le.le.codisjoint_hnot_right -> LE.le.codisjoint_hnot_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) b a) -> (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) a (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) b a) -> (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) a (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) b))
Case conversion may be inaccurate. Consider using '#align has_le.le.codisjoint_hnot_right LE.le.codisjoint_hnot_rightₓ'. -/
theorem LE.le.codisjoint_hnot_right (h : b ≤ a) : Codisjoint a (￢b) :=
  codisjoint_hnot_right.mono_left h
#align has_le.le.codisjoint_hnot_right LE.le.codisjoint_hnot_right

/- warning: is_compl.hnot_eq -> IsCompl.hnot_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, (IsCompl.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, (IsCompl.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1) a b) -> (Eq.{succ u1} α (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a) b)
Case conversion may be inaccurate. Consider using '#align is_compl.hnot_eq IsCompl.hnot_eqₓ'. -/
theorem IsCompl.hnot_eq (h : IsCompl a b) : ￢a = b :=
  h.2.hnot_le_right.antisymm <| Disjoint.le_of_codisjoint h.1.symm codisjoint_hnot_right
#align is_compl.hnot_eq IsCompl.hnot_eq

/- warning: is_compl.eq_hnot -> IsCompl.eq_hnot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, (IsCompl.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1) a b) -> (Eq.{succ u1} α a (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, (IsCompl.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1) a b) -> (Eq.{succ u1} α a (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) b))
Case conversion may be inaccurate. Consider using '#align is_compl.eq_hnot IsCompl.eq_hnotₓ'. -/
theorem IsCompl.eq_hnot (h : IsCompl a b) : a = ￢b :=
  h.2.hnot_le_left.antisymm' <| Disjoint.le_of_codisjoint h.1 codisjoint_hnot_right
#align is_compl.eq_hnot IsCompl.eq_hnot

/- warning: sup_hnot_self -> sup_hnot_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a)) (Top.top.{u1} α (CoheytingAlgebra.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a)) (Top.top.{u1} α (CoheytingAlgebra.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align sup_hnot_self sup_hnot_selfₓ'. -/
@[simp]
theorem sup_hnot_self (a : α) : a ⊔ ￢a = ⊤ :=
  Codisjoint.eq_top codisjoint_hnot_right
#align sup_hnot_self sup_hnot_self

/- warning: hnot_sup_self -> hnot_sup_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a) a) (Top.top.{u1} α (CoheytingAlgebra.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a) a) (Top.top.{u1} α (CoheytingAlgebra.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align hnot_sup_self hnot_sup_selfₓ'. -/
@[simp]
theorem hnot_sup_self (a : α) : ￢a ⊔ a = ⊤ :=
  Codisjoint.eq_top codisjoint_hnot_left
#align hnot_sup_self hnot_sup_self

/- warning: hnot_bot -> hnot_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α], Eq.{succ u1} α (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toHasBot.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (Top.top.{u1} α (CoheytingAlgebra.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α], Eq.{succ u1} α (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toBot.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (Top.top.{u1} α (CoheytingAlgebra.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align hnot_bot hnot_botₓ'. -/
@[simp]
theorem hnot_bot : ￢(⊥ : α) = ⊤ :=
  eq_of_forall_ge_iff fun a => by rw [hnot_le_iff_codisjoint_left, codisjoint_bot, top_le_iff]
#align hnot_bot hnot_bot

/- warning: hnot_top -> hnot_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α], Eq.{succ u1} α (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) (Top.top.{u1} α (CoheytingAlgebra.toHasTop.{u1} α _inst_1))) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toHasBot.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α], Eq.{succ u1} α (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) (Top.top.{u1} α (CoheytingAlgebra.toTop.{u1} α _inst_1))) (Bot.bot.{u1} α (GeneralizedCoheytingAlgebra.toBot.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align hnot_top hnot_topₓ'. -/
@[simp]
theorem hnot_top : ￢(⊤ : α) = ⊥ := by rw [← top_sdiff', sdiff_self]
#align hnot_top hnot_top

/- warning: hnot_hnot_le -> hnot_hnot_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a)) a
Case conversion may be inaccurate. Consider using '#align hnot_hnot_le hnot_hnot_leₓ'. -/
theorem hnot_hnot_le : ￢￢a ≤ a :=
  codisjoint_hnot_right.hnot_le_left
#align hnot_hnot_le hnot_hnot_le

/- warning: hnot_anti -> hnot_anti is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α], Antitone.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α], Antitone.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align hnot_anti hnot_antiₓ'. -/
theorem hnot_anti : Antitone (hnot : α → α) := fun a b h => hnot_le_comm.1 <| hnot_hnot_le.trans h
#align hnot_anti hnot_anti

/- warning: hnot_le_hnot -> hnot_le_hnot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) b) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) b) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a))
Case conversion may be inaccurate. Consider using '#align hnot_le_hnot hnot_le_hnotₓ'. -/
theorem hnot_le_hnot (h : a ≤ b) : ￢b ≤ ￢a :=
  hnot_anti h
#align hnot_le_hnot hnot_le_hnot

/- warning: hnot_hnot_hnot -> hnot_hnot_hnot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α), Eq.{succ u1} α (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align hnot_hnot_hnot hnot_hnot_hnotₓ'. -/
@[simp]
theorem hnot_hnot_hnot (a : α) : ￢￢￢a = ￢a :=
  hnot_hnot_le.antisymm <| hnot_anti hnot_hnot_le
#align hnot_hnot_hnot hnot_hnot_hnot

/- warning: codisjoint_hnot_hnot_left_iff -> codisjoint_hnot_hnot_left_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, Iff (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a)) b) (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, Iff (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a)) b) (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align codisjoint_hnot_hnot_left_iff codisjoint_hnot_hnot_left_iffₓ'. -/
@[simp]
theorem codisjoint_hnot_hnot_left_iff : Codisjoint (￢￢a) b ↔ Codisjoint a b := by
  simp_rw [← hnot_le_iff_codisjoint_right, hnot_hnot_hnot]
#align codisjoint_hnot_hnot_left_iff codisjoint_hnot_hnot_left_iff

/- warning: codisjoint_hnot_hnot_right_iff -> codisjoint_hnot_hnot_right_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, Iff (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) a (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) b))) (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, Iff (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) a (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) b))) (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (CoheytingAlgebra.toBoundedOrder.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align codisjoint_hnot_hnot_right_iff codisjoint_hnot_hnot_right_iffₓ'. -/
@[simp]
theorem codisjoint_hnot_hnot_right_iff : Codisjoint a (￢￢b) ↔ Codisjoint a b := by
  simp_rw [← hnot_le_iff_codisjoint_left, hnot_hnot_hnot]
#align codisjoint_hnot_hnot_right_iff codisjoint_hnot_hnot_right_iff

/- warning: le_hnot_inf_hnot -> le_hnot_inf_hnot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) b))
Case conversion may be inaccurate. Consider using '#align le_hnot_inf_hnot le_hnot_inf_hnotₓ'. -/
theorem le_hnot_inf_hnot : ￢(a ⊔ b) ≤ ￢a ⊓ ￢b :=
  le_inf (hnot_anti le_sup_left) <| hnot_anti le_sup_right
#align le_hnot_inf_hnot le_hnot_inf_hnot

/- warning: hnot_hnot_sup_distrib -> hnot_hnot_sup_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a b))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) b)))
Case conversion may be inaccurate. Consider using '#align hnot_hnot_sup_distrib hnot_hnot_sup_distribₓ'. -/
theorem hnot_hnot_sup_distrib (a b : α) : ￢￢(a ⊔ b) = ￢￢a ⊔ ￢￢b :=
  by
  refine' ((hnot_inf_distrib _ _).ge.trans <| hnot_anti le_hnot_inf_hnot).antisymm' _
  rw [hnot_le_iff_codisjoint_left, codisjoint_assoc, codisjoint_hnot_hnot_left_iff,
    codisjoint_left_comm, codisjoint_hnot_hnot_left_iff, ← codisjoint_assoc, sup_comm]
  exact codisjoint_hnot_right
#align hnot_hnot_sup_distrib hnot_hnot_sup_distrib

/- warning: hnot_hnot_sdiff_distrib -> hnot_hnot_sdiff_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) a b))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toHasSdiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) a)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHasHnot.{u1} α _inst_1) b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CoheytingAlgebra.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) a b))) (SDiff.sdiff.{u1} α (GeneralizedCoheytingAlgebra.toSDiff.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) a)) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) (HNot.hnot.{u1} α (CoheytingAlgebra.toHNot.{u1} α _inst_1) b)))
Case conversion may be inaccurate. Consider using '#align hnot_hnot_sdiff_distrib hnot_hnot_sdiff_distribₓ'. -/
theorem hnot_hnot_sdiff_distrib (a b : α) : ￢￢(a \ b) = ￢￢a \ ￢￢b :=
  by
  refine' le_antisymm _ _
  · refine' hnot_le_comm.1 ((hnot_anti sdiff_le_inf_hnot).trans' _)
    rw [hnot_inf_distrib, hnot_le_iff_codisjoint_right, codisjoint_left_comm, ←
      hnot_le_iff_codisjoint_right]
    exact le_sdiff_sup
  · rw [sdiff_le_iff, ← hnot_hnot_sup_distrib]
    exact hnot_anti (hnot_anti le_sup_sdiff)
#align hnot_hnot_sdiff_distrib hnot_hnot_sdiff_distrib

instance : HeytingAlgebra αᵒᵈ :=
  { OrderDual.lattice α,
    OrderDual.boundedOrder α with
    compl := to_dual ∘ hnot ∘ of_dual
    himp := fun a b => toDual (ofDual b \ ofDual a)
    le_himp_iff := fun a b c => by
      rw [inf_comm]
      exact sdiff_le_iff
    himp_bot := top_sdiff' }

#print ofDual_compl /-
@[simp]
theorem ofDual_compl (a : αᵒᵈ) : ofDual (aᶜ) = ￢ofDual a :=
  rfl
#align of_dual_compl ofDual_compl
-/

#print ofDual_himp /-
@[simp]
theorem ofDual_himp (a b : αᵒᵈ) : ofDual (a ⇨ b) = ofDual b \ ofDual a :=
  rfl
#align of_dual_himp ofDual_himp
-/

#print toDual_hnot /-
@[simp]
theorem toDual_hnot (a : α) : toDual (￢a) = toDual aᶜ :=
  rfl
#align to_dual_hnot toDual_hnot
-/

#print toDual_sdiff /-
@[simp]
theorem toDual_sdiff (a b : α) : toDual (a \ b) = toDual b ⇨ toDual a :=
  rfl
#align to_dual_sdiff toDual_sdiff
-/

#print Prod.coheytingAlgebra /-
instance Prod.coheytingAlgebra [CoheytingAlgebra β] : CoheytingAlgebra (α × β) :=
  { Prod.lattice α β, Prod.boundedOrder α β, Prod.hasSdiff,
    Prod.hasHnot with
    sdiff_le_iff := fun a b c => and_congr sdiff_le_iff sdiff_le_iff
    top_sdiff := fun a => Prod.ext (top_sdiff' a.1) (top_sdiff' a.2) }
#align prod.coheyting_algebra Prod.coheytingAlgebra
-/

#print Pi.coheytingAlgebra /-
instance Pi.coheytingAlgebra {α : ι → Type _} [∀ i, CoheytingAlgebra (α i)] :
    CoheytingAlgebra (∀ i, α i) := by
  pi_instance
  exact fun a b c => forall_congr' fun i => sdiff_le_iff
#align pi.coheyting_algebra Pi.coheytingAlgebra
-/

end CoheytingAlgebra

section BiheytingAlgebra

variable [BiheytingAlgebra α] {a : α}

/- warning: compl_le_hnot -> compl_le_hnot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : BiheytingAlgebra.{u1} α] {a : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α _inst_1))))))) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α _inst_1)) a) (HNot.hnot.{u1} α (BiheytingAlgebra.toHasHnot.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BiheytingAlgebra.{u1} α] {a : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α _inst_1))))))) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α _inst_1)) a) (HNot.hnot.{u1} α (BiheytingAlgebra.toHNot.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align compl_le_hnot compl_le_hnotₓ'. -/
theorem compl_le_hnot : aᶜ ≤ ￢a :=
  (disjoint_compl_left : Disjoint _ a).le_of_codisjoint codisjoint_hnot_right
#align compl_le_hnot compl_le_hnot

end BiheytingAlgebra

/- ./././Mathport/Syntax/Translate/Expr.lean:219:4: warning: unsupported binary notation `«->» -/
#print Prop.heytingAlgebra /-
/-- Propositions form a Heyting algebra with implication as Heyting implication and negation as
complement. -/
instance Prop.heytingAlgebra : HeytingAlgebra Prop :=
  { Prop.hasCompl, Prop.distribLattice,
    Prop.boundedOrder with
    himp := («->» · ·)
    le_himp_iff := fun p q r => and_imp.symm
    himp_bot := fun p => rfl }
#align Prop.heyting_algebra Prop.heytingAlgebra
-/

/- warning: himp_iff_imp -> himp_iff_imp is a dubious translation:
lean 3 declaration is
  forall (p : Prop) (q : Prop), Iff (HImp.himp.{0} Prop (GeneralizedHeytingAlgebra.toHasHimp.{0} Prop (HeytingAlgebra.toGeneralizedHeytingAlgebra.{0} Prop Prop.heytingAlgebra)) p q) (p -> q)
but is expected to have type
  forall (p : Prop) (q : Prop), Iff (HImp.himp.{0} Prop (GeneralizedHeytingAlgebra.toHImp.{0} Prop (HeytingAlgebra.toGeneralizedHeytingAlgebra.{0} Prop Prop.heytingAlgebra)) p q) (p -> q)
Case conversion may be inaccurate. Consider using '#align himp_iff_imp himp_iff_impₓ'. -/
@[simp]
theorem himp_iff_imp (p q : Prop) : p ⇨ q ↔ p → q :=
  Iff.rfl
#align himp_iff_imp himp_iff_imp

#print compl_iff_not /-
@[simp]
theorem compl_iff_not (p : Prop) : pᶜ ↔ ¬p :=
  Iff.rfl
#align compl_iff_not compl_iff_not
-/

#print LinearOrder.toBiheytingAlgebra /-
-- See note [reducible non-instances]
/-- A bounded linear order is a bi-Heyting algebra by setting
* `a ⇨ b = ⊤` if `a ≤ b` and `a ⇨ b = b` otherwise.
* `a \ b = ⊥` if `a ≤ b` and `a \ b = a` otherwise. -/
@[reducible]
def LinearOrder.toBiheytingAlgebra [LinearOrder α] [BoundedOrder α] : BiheytingAlgebra α :=
  { LinearOrder.toLattice,
    ‹BoundedOrder α› with
    himp := fun a b => if a ≤ b then ⊤ else b
    compl := fun a => if a = ⊥ then ⊤ else ⊥
    le_himp_iff := fun a b c => by
      change _ ≤ ite _ _ _ ↔ _
      split_ifs
      · exact iff_of_true le_top (inf_le_of_right_le h)
      · rw [inf_le_iff, or_iff_left h]
    himp_bot := fun a => if_congr le_bot_iff rfl rfl
    sdiff := fun a b => if a ≤ b then ⊥ else a
    hnot := fun a => if a = ⊤ then ⊥ else ⊤
    sdiff_le_iff := fun a b c => by
      change ite _ _ _ ≤ _ ↔ _
      split_ifs
      · exact iff_of_true bot_le (le_sup_of_le_left h)
      · rw [le_sup_iff, or_iff_right h]
    top_sdiff := fun a => if_congr top_le_iff rfl rfl }
#align linear_order.to_biheyting_algebra LinearOrder.toBiheytingAlgebra
-/

section lift

/- warning: function.injective.generalized_heyting_algebra -> Function.Injective.generalizedHeytingAlgebra is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : Top.{u1} α] [_inst_4 : HImp.{u1} α] [_inst_5 : GeneralizedHeytingAlgebra.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (GeneralizedHeytingAlgebra.toLattice.{u2} β _inst_5))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (GeneralizedHeytingAlgebra.toLattice.{u2} β _inst_5))) (f a) (f b))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_3)) (Top.top.{u2} β (GeneralizedHeytingAlgebra.toHasTop.{u2} β _inst_5))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HImp.himp.{u1} α _inst_4 a b)) (HImp.himp.{u2} β (GeneralizedHeytingAlgebra.toHasHimp.{u2} β _inst_5) (f a) (f b))) -> (GeneralizedHeytingAlgebra.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : Top.{u1} α] [_inst_4 : HImp.{u1} α] [_inst_5 : GeneralizedHeytingAlgebra.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (GeneralizedHeytingAlgebra.toLattice.{u2} β _inst_5))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (Lattice.toHasInf.{u2} β (GeneralizedHeytingAlgebra.toLattice.{u2} β _inst_5)) (f a) (f b))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_3)) (Top.top.{u2} β (GeneralizedHeytingAlgebra.toTop.{u2} β _inst_5))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HImp.himp.{u1} α _inst_4 a b)) (HImp.himp.{u2} β (GeneralizedHeytingAlgebra.toHImp.{u2} β _inst_5) (f a) (f b))) -> (GeneralizedHeytingAlgebra.{u1} α)
Case conversion may be inaccurate. Consider using '#align function.injective.generalized_heyting_algebra Function.Injective.generalizedHeytingAlgebraₓ'. -/
-- See note [reducible non-instances]
/-- Pullback a `generalized_heyting_algebra` along an injection. -/
@[reducible]
protected def Function.Injective.generalizedHeytingAlgebra [HasSup α] [HasInf α] [Top α] [HImp α]
    [GeneralizedHeytingAlgebra β] (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b) : GeneralizedHeytingAlgebra α :=
  { hf.Lattice f map_sup map_inf, ‹Top α›,
    ‹HImp
        α› with
    le_top := fun a => by
      change f _ ≤ _
      rw [map_top]
      exact le_top
    le_himp_iff := fun a b c => by
      change f _ ≤ _ ↔ f _ ≤ _
      erw [map_himp, map_inf, le_himp_iff] }
#align function.injective.generalized_heyting_algebra Function.Injective.generalizedHeytingAlgebra

/- warning: function.injective.generalized_coheyting_algebra -> Function.Injective.generalizedCoheytingAlgebra is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : Bot.{u1} α] [_inst_4 : SDiff.{u1} α] [_inst_5 : GeneralizedCoheytingAlgebra.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (GeneralizedCoheytingAlgebra.toLattice.{u2} β _inst_5))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (GeneralizedCoheytingAlgebra.toLattice.{u2} β _inst_5))) (f a) (f b))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_3)) (Bot.bot.{u2} β (GeneralizedCoheytingAlgebra.toHasBot.{u2} β _inst_5))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (SDiff.sdiff.{u1} α _inst_4 a b)) (SDiff.sdiff.{u2} β (GeneralizedCoheytingAlgebra.toHasSdiff.{u2} β _inst_5) (f a) (f b))) -> (GeneralizedCoheytingAlgebra.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : Bot.{u1} α] [_inst_4 : SDiff.{u1} α] [_inst_5 : GeneralizedCoheytingAlgebra.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (GeneralizedCoheytingAlgebra.toLattice.{u2} β _inst_5))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (Lattice.toHasInf.{u2} β (GeneralizedCoheytingAlgebra.toLattice.{u2} β _inst_5)) (f a) (f b))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_3)) (Bot.bot.{u2} β (GeneralizedCoheytingAlgebra.toBot.{u2} β _inst_5))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (SDiff.sdiff.{u1} α _inst_4 a b)) (SDiff.sdiff.{u2} β (GeneralizedCoheytingAlgebra.toSDiff.{u2} β _inst_5) (f a) (f b))) -> (GeneralizedCoheytingAlgebra.{u1} α)
Case conversion may be inaccurate. Consider using '#align function.injective.generalized_coheyting_algebra Function.Injective.generalizedCoheytingAlgebraₓ'. -/
-- See note [reducible non-instances]
/-- Pullback a `generalized_coheyting_algebra` along an injection. -/
@[reducible]
protected def Function.Injective.generalizedCoheytingAlgebra [HasSup α] [HasInf α] [Bot α] [SDiff α]
    [GeneralizedCoheytingAlgebra β] (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_bot : f ⊥ = ⊥) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    GeneralizedCoheytingAlgebra α :=
  { hf.Lattice f map_sup map_inf, ‹Bot α›,
    ‹SDiff
        α› with
    bot_le := fun a => by
      change f _ ≤ _
      rw [map_bot]
      exact bot_le
    sdiff_le_iff := fun a b c => by
      change f _ ≤ _ ↔ f _ ≤ _
      erw [map_sdiff, map_sup, sdiff_le_iff] }
#align
  function.injective.generalized_coheyting_algebra Function.Injective.generalizedCoheytingAlgebra

/- warning: function.injective.heyting_algebra -> Function.Injective.heytingAlgebra is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : Top.{u1} α] [_inst_4 : Bot.{u1} α] [_inst_5 : HasCompl.{u1} α] [_inst_6 : HImp.{u1} α] [_inst_7 : HeytingAlgebra.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (GeneralizedHeytingAlgebra.toLattice.{u2} β (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u2} β _inst_7)))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (GeneralizedHeytingAlgebra.toLattice.{u2} β (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u2} β _inst_7)))) (f a) (f b))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_3)) (Top.top.{u2} β (GeneralizedHeytingAlgebra.toHasTop.{u2} β (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u2} β _inst_7)))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_4)) (Bot.bot.{u2} β (HeytingAlgebra.toHasBot.{u2} β _inst_7))) -> (forall (a : α), Eq.{succ u2} β (f (HasCompl.compl.{u1} α _inst_5 a)) (HasCompl.compl.{u2} β (HeytingAlgebra.toHasCompl.{u2} β _inst_7) (f a))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HImp.himp.{u1} α _inst_6 a b)) (HImp.himp.{u2} β (GeneralizedHeytingAlgebra.toHasHimp.{u2} β (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u2} β _inst_7)) (f a) (f b))) -> (HeytingAlgebra.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : Top.{u1} α] [_inst_4 : Bot.{u1} α] [_inst_5 : HasCompl.{u1} α] [_inst_6 : HImp.{u1} α] [_inst_7 : HeytingAlgebra.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (GeneralizedHeytingAlgebra.toLattice.{u2} β (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u2} β _inst_7)))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (Lattice.toHasInf.{u2} β (GeneralizedHeytingAlgebra.toLattice.{u2} β (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u2} β _inst_7))) (f a) (f b))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_3)) (Top.top.{u2} β (GeneralizedHeytingAlgebra.toTop.{u2} β (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u2} β _inst_7)))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_4)) (Bot.bot.{u2} β (HeytingAlgebra.toBot.{u2} β _inst_7))) -> (forall (a : α), Eq.{succ u2} β (f (HasCompl.compl.{u1} α _inst_5 a)) (HasCompl.compl.{u2} β (HeytingAlgebra.toHasCompl.{u2} β _inst_7) (f a))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HImp.himp.{u1} α _inst_6 a b)) (HImp.himp.{u2} β (GeneralizedHeytingAlgebra.toHImp.{u2} β (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u2} β _inst_7)) (f a) (f b))) -> (HeytingAlgebra.{u1} α)
Case conversion may be inaccurate. Consider using '#align function.injective.heyting_algebra Function.Injective.heytingAlgebraₓ'. -/
-- See note [reducible non-instances]
/-- Pullback a `heyting_algebra` along an injection. -/
@[reducible]
protected def Function.Injective.heytingAlgebra [HasSup α] [HasInf α] [Top α] [Bot α] [HasCompl α]
    [HImp α] [HeytingAlgebra β] (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_compl : ∀ a, f (aᶜ) = f aᶜ)
    (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b) : HeytingAlgebra α :=
  { hf.GeneralizedHeytingAlgebra f map_sup map_inf map_top map_himp, ‹Bot α›,
    ‹HasCompl
        α› with
    bot_le := fun a => by
      change f _ ≤ _
      rw [map_bot]
      exact bot_le
    himp_bot := fun a => hf <| by erw [map_himp, map_compl, map_bot, himp_bot] }
#align function.injective.heyting_algebra Function.Injective.heytingAlgebra

/- warning: function.injective.coheyting_algebra -> Function.Injective.coheytingAlgebra is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : Top.{u1} α] [_inst_4 : Bot.{u1} α] [_inst_5 : HNot.{u1} α] [_inst_6 : SDiff.{u1} α] [_inst_7 : CoheytingAlgebra.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (GeneralizedCoheytingAlgebra.toLattice.{u2} β (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} β _inst_7)))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (GeneralizedCoheytingAlgebra.toLattice.{u2} β (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} β _inst_7)))) (f a) (f b))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_3)) (Top.top.{u2} β (CoheytingAlgebra.toHasTop.{u2} β _inst_7))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_4)) (Bot.bot.{u2} β (GeneralizedCoheytingAlgebra.toHasBot.{u2} β (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} β _inst_7)))) -> (forall (a : α), Eq.{succ u2} β (f (HNot.hnot.{u1} α _inst_5 a)) (HNot.hnot.{u2} β (CoheytingAlgebra.toHasHnot.{u2} β _inst_7) (f a))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (SDiff.sdiff.{u1} α _inst_6 a b)) (SDiff.sdiff.{u2} β (GeneralizedCoheytingAlgebra.toHasSdiff.{u2} β (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} β _inst_7)) (f a) (f b))) -> (CoheytingAlgebra.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : Top.{u1} α] [_inst_4 : Bot.{u1} α] [_inst_5 : HNot.{u1} α] [_inst_6 : SDiff.{u1} α] [_inst_7 : CoheytingAlgebra.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (GeneralizedCoheytingAlgebra.toLattice.{u2} β (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} β _inst_7)))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (Lattice.toHasInf.{u2} β (GeneralizedCoheytingAlgebra.toLattice.{u2} β (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} β _inst_7))) (f a) (f b))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_3)) (Top.top.{u2} β (CoheytingAlgebra.toTop.{u2} β _inst_7))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_4)) (Bot.bot.{u2} β (GeneralizedCoheytingAlgebra.toBot.{u2} β (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} β _inst_7)))) -> (forall (a : α), Eq.{succ u2} β (f (HNot.hnot.{u1} α _inst_5 a)) (HNot.hnot.{u2} β (CoheytingAlgebra.toHNot.{u2} β _inst_7) (f a))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (SDiff.sdiff.{u1} α _inst_6 a b)) (SDiff.sdiff.{u2} β (GeneralizedCoheytingAlgebra.toSDiff.{u2} β (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} β _inst_7)) (f a) (f b))) -> (CoheytingAlgebra.{u1} α)
Case conversion may be inaccurate. Consider using '#align function.injective.coheyting_algebra Function.Injective.coheytingAlgebraₓ'. -/
-- See note [reducible non-instances]
/-- Pullback a `coheyting_algebra` along an injection. -/
@[reducible]
protected def Function.Injective.coheytingAlgebra [HasSup α] [HasInf α] [Top α] [Bot α] [HNot α]
    [SDiff α] [CoheytingAlgebra β] (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_hnot : ∀ a, f (￢a) = ￢f a)
    (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) : CoheytingAlgebra α :=
  { hf.GeneralizedCoheytingAlgebra f map_sup map_inf map_bot map_sdiff, ‹Top α›,
    ‹HNot
        α› with
    le_top := fun a => by
      change f _ ≤ _
      rw [map_top]
      exact le_top
    top_sdiff := fun a => hf <| by erw [map_sdiff, map_hnot, map_top, top_sdiff'] }
#align function.injective.coheyting_algebra Function.Injective.coheytingAlgebra

/- warning: function.injective.biheyting_algebra -> Function.Injective.biheytingAlgebra is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : Top.{u1} α] [_inst_4 : Bot.{u1} α] [_inst_5 : HasCompl.{u1} α] [_inst_6 : HNot.{u1} α] [_inst_7 : HImp.{u1} α] [_inst_8 : SDiff.{u1} α] [_inst_9 : BiheytingAlgebra.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (GeneralizedCoheytingAlgebra.toLattice.{u2} β (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} β (BiheytingAlgebra.toCoheytingAlgebra.{u2} β _inst_9))))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (GeneralizedCoheytingAlgebra.toLattice.{u2} β (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} β (BiheytingAlgebra.toCoheytingAlgebra.{u2} β _inst_9))))) (f a) (f b))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_3)) (Top.top.{u2} β (CoheytingAlgebra.toHasTop.{u2} β (BiheytingAlgebra.toCoheytingAlgebra.{u2} β _inst_9)))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_4)) (Bot.bot.{u2} β (HeytingAlgebra.toHasBot.{u2} β (BiheytingAlgebra.toHeytingAlgebra.{u2} β _inst_9)))) -> (forall (a : α), Eq.{succ u2} β (f (HasCompl.compl.{u1} α _inst_5 a)) (HasCompl.compl.{u2} β (HeytingAlgebra.toHasCompl.{u2} β (BiheytingAlgebra.toHeytingAlgebra.{u2} β _inst_9)) (f a))) -> (forall (a : α), Eq.{succ u2} β (f (HNot.hnot.{u1} α _inst_6 a)) (HNot.hnot.{u2} β (BiheytingAlgebra.toHasHnot.{u2} β _inst_9) (f a))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HImp.himp.{u1} α _inst_7 a b)) (HImp.himp.{u2} β (GeneralizedHeytingAlgebra.toHasHimp.{u2} β (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u2} β (BiheytingAlgebra.toHeytingAlgebra.{u2} β _inst_9))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (SDiff.sdiff.{u1} α _inst_8 a b)) (SDiff.sdiff.{u2} β (BiheytingAlgebra.toHasSdiff.{u2} β _inst_9) (f a) (f b))) -> (BiheytingAlgebra.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : Top.{u1} α] [_inst_4 : Bot.{u1} α] [_inst_5 : HasCompl.{u1} α] [_inst_6 : HNot.{u1} α] [_inst_7 : HImp.{u1} α] [_inst_8 : SDiff.{u1} α] [_inst_9 : BiheytingAlgebra.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (GeneralizedCoheytingAlgebra.toLattice.{u2} β (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} β (BiheytingAlgebra.toCoheytingAlgebra.{u2} β _inst_9))))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (Lattice.toHasInf.{u2} β (GeneralizedCoheytingAlgebra.toLattice.{u2} β (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} β (BiheytingAlgebra.toCoheytingAlgebra.{u2} β _inst_9)))) (f a) (f b))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_3)) (Top.top.{u2} β (CoheytingAlgebra.toTop.{u2} β (BiheytingAlgebra.toCoheytingAlgebra.{u2} β _inst_9)))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_4)) (Bot.bot.{u2} β (HeytingAlgebra.toBot.{u2} β (BiheytingAlgebra.toHeytingAlgebra.{u2} β _inst_9)))) -> (forall (a : α), Eq.{succ u2} β (f (HasCompl.compl.{u1} α _inst_5 a)) (HasCompl.compl.{u2} β (HeytingAlgebra.toHasCompl.{u2} β (BiheytingAlgebra.toHeytingAlgebra.{u2} β _inst_9)) (f a))) -> (forall (a : α), Eq.{succ u2} β (f (HNot.hnot.{u1} α _inst_6 a)) (HNot.hnot.{u2} β (BiheytingAlgebra.toHNot.{u2} β _inst_9) (f a))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HImp.himp.{u1} α _inst_7 a b)) (HImp.himp.{u2} β (GeneralizedHeytingAlgebra.toHImp.{u2} β (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u2} β (BiheytingAlgebra.toHeytingAlgebra.{u2} β _inst_9))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (SDiff.sdiff.{u1} α _inst_8 a b)) (SDiff.sdiff.{u2} β (BiheytingAlgebra.toSDiff.{u2} β _inst_9) (f a) (f b))) -> (BiheytingAlgebra.{u1} α)
Case conversion may be inaccurate. Consider using '#align function.injective.biheyting_algebra Function.Injective.biheytingAlgebraₓ'. -/
-- See note [reducible non-instances]
/-- Pullback a `biheyting_algebra` along an injection. -/
@[reducible]
protected def Function.Injective.biheytingAlgebra [HasSup α] [HasInf α] [Top α] [Bot α] [HasCompl α]
    [HNot α] [HImp α] [SDiff α] [BiheytingAlgebra β] (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_compl : ∀ a, f (aᶜ) = f aᶜ)
    (map_hnot : ∀ a, f (￢a) = ￢f a) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b)
    (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) : BiheytingAlgebra α :=
  { hf.HeytingAlgebra f map_sup map_inf map_top map_bot map_compl map_himp,
    hf.CoheytingAlgebra f map_sup map_inf map_top map_bot map_hnot map_sdiff with }
#align function.injective.biheyting_algebra Function.Injective.biheytingAlgebra

end lift

namespace PUnit

variable (a b : PUnit.{u + 1})

instance : BiheytingAlgebra PUnit := by
  refine_struct
        { PUnit.linearOrder with
          top := star
          bot := star
          sup := fun _ _ => star
          inf := fun _ _ => star
          compl := fun _ => star
          sdiff := fun _ _ => star
          hnot := fun _ => star
          himp := fun _ _ => star } <;>
      intros <;>
    first |trivial|exact Subsingleton.elim _ _

#print PUnit.top_eq /-
@[simp]
theorem top_eq : (⊤ : PUnit) = star :=
  rfl
#align punit.top_eq PUnit.top_eq
-/

#print PUnit.bot_eq /-
@[simp]
theorem bot_eq : (⊥ : PUnit) = star :=
  rfl
#align punit.bot_eq PUnit.bot_eq
-/

#print PUnit.sup_eq /-
@[simp]
theorem sup_eq : a ⊔ b = star :=
  rfl
#align punit.sup_eq PUnit.sup_eq
-/

#print PUnit.inf_eq /-
@[simp]
theorem inf_eq : a ⊓ b = star :=
  rfl
#align punit.inf_eq PUnit.inf_eq
-/

#print PUnit.compl_eq /-
@[simp]
theorem compl_eq : aᶜ = star :=
  rfl
#align punit.compl_eq PUnit.compl_eq
-/

#print PUnit.sdiff_eq /-
@[simp]
theorem sdiff_eq : a \ b = star :=
  rfl
#align punit.sdiff_eq PUnit.sdiff_eq
-/

#print PUnit.hnot_eq /-
@[simp, nolint simp_nf]
theorem hnot_eq : ￢a = star :=
  rfl
#align punit.hnot_eq PUnit.hnot_eq
-/

#print PUnit.himp_eq /-
-- eligible for `dsimp`
@[simp]
theorem himp_eq : a ⇨ b = star :=
  rfl
#align punit.himp_eq PUnit.himp_eq
-/

end PUnit

