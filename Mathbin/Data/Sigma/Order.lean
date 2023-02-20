/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.sigma.order
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Sigma.Lex
import Mathbin.Order.BoundedOrder

/-!
# Orders on a sigma type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines two orders on a sigma type:
* The disjoint sum of orders. `a` is less `b` iff `a` and `b` are in the same summand and `a` is
  less than `b` there.
* The lexicographical order. `a` is less than `b` if its summand is strictly less than the summand
  of `b` or they are in the same summand and `a` is less than `b` there.

We make the disjoint sum of orders the default set of instances. The lexicographic order goes on a
type synonym.

## Notation

* `Σₗ i, α i`: Sigma type equipped with the lexicographic order. Type synonym of `Σ i, α i`.

## See also

Related files are:
* `data.finset.colex`: Colexicographic order on finite sets.
* `data.list.lex`: Lexicographic order on lists.
* `data.pi.lex`: Lexicographic order on `Πₗ i, α i`.
* `data.psigma.order`: Lexicographic order on `Σₗ' i, α i`. Basically a twin of this file.
* `data.prod.lex`: Lexicographic order on `α × β`.

## TODO

Upgrade `equiv.sigma_congr_left`, `equiv.sigma_congr`, `equiv.sigma_assoc`,
`equiv.sigma_prod_of_equiv`, `equiv.sigma_equiv_prod`, ... to order isomorphisms.
-/


namespace Sigma

variable {ι : Type _} {α : ι → Type _}

/-! ### Disjoint sum of orders on `sigma` -/


#print Sigma.le /-
/-- Disjoint sum of orders. `⟨i, a⟩ ≤ ⟨j, b⟩` iff `i = j` and `a ≤ b`. -/
inductive le [∀ i, LE (α i)] : ∀ a b : Σi, α i, Prop
  | fiber (i : ι) (a b : α i) : a ≤ b → le ⟨i, a⟩ ⟨i, b⟩
#align sigma.le Sigma.le
-/

#print Sigma.lt /-
/-- Disjoint sum of orders. `⟨i, a⟩ < ⟨j, b⟩` iff `i = j` and `a < b`. -/
inductive lt [∀ i, LT (α i)] : ∀ a b : Σi, α i, Prop
  | fiber (i : ι) (a b : α i) : a < b → lt ⟨i, a⟩ ⟨i, b⟩
#align sigma.lt Sigma.lt
-/

instance [∀ i, LE (α i)] : LE (Σi, α i) :=
  ⟨le⟩

instance [∀ i, LT (α i)] : LT (Σi, α i) :=
  ⟨lt⟩

#print Sigma.mk_le_mk_iff /-
@[simp]
theorem mk_le_mk_iff [∀ i, LE (α i)] {i : ι} {a b : α i} : (⟨i, a⟩ : Sigma α) ≤ ⟨i, b⟩ ↔ a ≤ b :=
  ⟨fun ⟨_, _, _, h⟩ => h, le.fiber _ _ _⟩
#align sigma.mk_le_mk_iff Sigma.mk_le_mk_iff
-/

#print Sigma.mk_lt_mk_iff /-
@[simp]
theorem mk_lt_mk_iff [∀ i, LT (α i)] {i : ι} {a b : α i} : (⟨i, a⟩ : Sigma α) < ⟨i, b⟩ ↔ a < b :=
  ⟨fun ⟨_, _, _, h⟩ => h, lt.fiber _ _ _⟩
#align sigma.mk_lt_mk_iff Sigma.mk_lt_mk_iff
-/

#print Sigma.le_def /-
theorem le_def [∀ i, LE (α i)] {a b : Σi, α i} : a ≤ b ↔ ∃ h : a.1 = b.1, h.rec a.2 ≤ b.2 :=
  by
  constructor
  · rintro ⟨i, a, b, h⟩
    exact ⟨rfl, h⟩
  · obtain ⟨i, a⟩ := a
    obtain ⟨j, b⟩ := b
    rintro ⟨rfl : i = j, h⟩
    exact le.fiber _ _ _ h
#align sigma.le_def Sigma.le_def
-/

#print Sigma.lt_def /-
theorem lt_def [∀ i, LT (α i)] {a b : Σi, α i} : a < b ↔ ∃ h : a.1 = b.1, h.rec a.2 < b.2 :=
  by
  constructor
  · rintro ⟨i, a, b, h⟩
    exact ⟨rfl, h⟩
  · obtain ⟨i, a⟩ := a
    obtain ⟨j, b⟩ := b
    rintro ⟨rfl : i = j, h⟩
    exact lt.fiber _ _ _ h
#align sigma.lt_def Sigma.lt_def
-/

instance [∀ i, Preorder (α i)] : Preorder (Σi, α i) :=
  { Sigma.hasLe,
    Sigma.hasLt with
    le_refl := fun ⟨i, a⟩ => le.fiber i a a le_rfl
    le_trans := by
      rintro _ _ _ ⟨i, a, b, hab⟩ ⟨_, _, c, hbc⟩
      exact le.fiber i a c (hab.trans hbc)
    lt_iff_le_not_le := fun _ _ => by
      constructor
      · rintro ⟨i, a, b, hab⟩
        rwa [mk_le_mk_iff, mk_le_mk_iff, ← lt_iff_le_not_le]
      · rintro ⟨⟨i, a, b, hab⟩, h⟩
        rw [mk_le_mk_iff] at h
        exact mk_lt_mk_iff.2 (hab.lt_of_not_le h) }

instance [∀ i, PartialOrder (α i)] : PartialOrder (Σi, α i) :=
  { Sigma.preorder with
    le_antisymm := by
      rintro _ _ ⟨i, a, b, hab⟩ ⟨_, _, _, hba⟩
      exact ext rfl (hEq_of_eq <| hab.antisymm hba) }

instance [∀ i, Preorder (α i)] [∀ i, DenselyOrdered (α i)] : DenselyOrdered (Σi, α i) :=
  ⟨by
    rintro ⟨i, a⟩ ⟨_, _⟩ ⟨_, _, b, h⟩
    obtain ⟨c, ha, hb⟩ := exists_between h
    exact ⟨⟨i, c⟩, lt.fiber i a c ha, lt.fiber i c b hb⟩⟩

/-! ### Lexicographical order on `sigma` -/


namespace Lex

-- mathport name: «exprΣₗ , »
notation3"Σₗ "(...)", "r:(scoped p => Lex Sigma p) => r

#print Sigma.Lex.LE /-
/-- The lexicographical `≤` on a sigma type. -/
instance LE [LT ι] [∀ i, LE (α i)] : LE (Σₗ i, α i) :=
  ⟨Lex (· < ·) fun i => (· ≤ ·)⟩
#align sigma.lex.has_le Sigma.Lex.LE
-/

#print Sigma.Lex.LT /-
/-- The lexicographical `<` on a sigma type. -/
instance LT [LT ι] [∀ i, LT (α i)] : LT (Σₗ i, α i) :=
  ⟨Lex (· < ·) fun i => (· < ·)⟩
#align sigma.lex.has_lt Sigma.Lex.LT
-/

/- warning: sigma.lex.le_def -> Sigma.Lex.le_def is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : LT.{u1} ι] [_inst_2 : forall (i : ι), LE.{u2} (α i)] {a : Lex.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))} {b : Lex.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))}, Iff (LE.le.{max u1 u2} (Lex.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Sigma.Lex.LE.{u1, u2} ι (fun (i : ι) => α i) _inst_1 (fun (i : ι) => _inst_2 i)) a b) (Or (LT.lt.{u1} ι _inst_1 (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (Exists.{0} (Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (fun (h : Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) => LE.le.{u2} (α (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (_inst_2 (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (Eq.ndrec.{succ u2, succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) α (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b) h) (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) b))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : LT.{u2} ι] [_inst_2 : forall (i : ι), LE.{u1} (α i)] {a : Lex.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))} {b : Lex.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))}, Iff (LE.le.{max u2 u1} (Lex.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Sigma.Lex.LE.{u2, u1} ι (fun (i : ι) => α i) _inst_1 (fun (i : ι) => _inst_2 i)) a b) (Or (LT.lt.{u2} ι _inst_1 (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (Exists.{0} (Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (fun (h : Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) => LE.le.{u1} (α (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (_inst_2 (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (Eq.rec.{succ u1, succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (fun (x._@.Mathlib.Data.Sigma.Order._hyg.1523 : ι) (x._@.Mathlib.Data.Sigma.Order._hyg.1522 : Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) x._@.Mathlib.Data.Sigma.Order._hyg.1523) => α x._@.Mathlib.Data.Sigma.Order._hyg.1523) (Sigma.snd.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b) h) (Sigma.snd.{u2, u1} ι (fun (i : ι) => α i) b))))
Case conversion may be inaccurate. Consider using '#align sigma.lex.le_def Sigma.Lex.le_defₓ'. -/
theorem le_def [LT ι] [∀ i, LE (α i)] {a b : Σₗ i, α i} :
    a ≤ b ↔ a.1 < b.1 ∨ ∃ h : a.1 = b.1, h.rec a.2 ≤ b.2 :=
  Sigma.lex_iff
#align sigma.lex.le_def Sigma.Lex.le_def

/- warning: sigma.lex.lt_def -> Sigma.Lex.lt_def is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : LT.{u1} ι] [_inst_2 : forall (i : ι), LT.{u2} (α i)] {a : Lex.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))} {b : Lex.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))}, Iff (LT.lt.{max u1 u2} (Lex.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Sigma.Lex.LT.{u1, u2} ι (fun (i : ι) => α i) _inst_1 (fun (i : ι) => _inst_2 i)) a b) (Or (LT.lt.{u1} ι _inst_1 (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (Exists.{0} (Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (fun (h : Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) => LT.lt.{u2} (α (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (_inst_2 (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (Eq.ndrec.{succ u2, succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) α (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b) h) (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) b))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : LT.{u2} ι] [_inst_2 : forall (i : ι), LT.{u1} (α i)] {a : Lex.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))} {b : Lex.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))}, Iff (LT.lt.{max u2 u1} (Lex.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Sigma.Lex.LT.{u2, u1} ι (fun (i : ι) => α i) _inst_1 (fun (i : ι) => _inst_2 i)) a b) (Or (LT.lt.{u2} ι _inst_1 (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (Exists.{0} (Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (fun (h : Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) => LT.lt.{u1} (α (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (_inst_2 (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (Eq.rec.{succ u1, succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (fun (x._@.Mathlib.Data.Sigma.Order._hyg.1623 : ι) (x._@.Mathlib.Data.Sigma.Order._hyg.1622 : Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) x._@.Mathlib.Data.Sigma.Order._hyg.1623) => α x._@.Mathlib.Data.Sigma.Order._hyg.1623) (Sigma.snd.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b) h) (Sigma.snd.{u2, u1} ι (fun (i : ι) => α i) b))))
Case conversion may be inaccurate. Consider using '#align sigma.lex.lt_def Sigma.Lex.lt_defₓ'. -/
theorem lt_def [LT ι] [∀ i, LT (α i)] {a b : Σₗ i, α i} :
    a < b ↔ a.1 < b.1 ∨ ∃ h : a.1 = b.1, h.rec a.2 < b.2 :=
  Sigma.lex_iff
#align sigma.lex.lt_def Sigma.Lex.lt_def

#print Sigma.Lex.preorder /-
/-- The lexicographical preorder on a sigma type. -/
instance preorder [Preorder ι] [∀ i, Preorder (α i)] : Preorder (Σₗ i, α i) :=
  { Lex.LE, Lex.LT with
    le_refl := fun ⟨i, a⟩ => Lex.right a a le_rfl
    le_trans := fun _ _ _ => trans_of (Lex (· < ·) fun _ => (· ≤ ·))
    lt_iff_le_not_le :=
      by
      refine' fun a b => ⟨fun hab => ⟨hab.mono_right fun i a b => le_of_lt, _⟩, _⟩
      · rintro (⟨b, a, hji⟩ | ⟨b, a, hba⟩) <;> obtain ⟨_, _, hij⟩ | ⟨_, _, hab⟩ := hab
        · exact hij.not_lt hji
        · exact lt_irrefl _ hji
        · exact lt_irrefl _ hij
        · exact hab.not_le hba
      · rintro ⟨⟨a, b, hij⟩ | ⟨a, b, hab⟩, hba⟩
        · exact lex.left _ _ hij
        · exact lex.right _ _ (hab.lt_of_not_le fun h => hba <| lex.right _ _ h) }
#align sigma.lex.preorder Sigma.Lex.preorder
-/

#print Sigma.Lex.partialOrder /-
/-- The lexicographical partial order on a sigma type. -/
instance partialOrder [Preorder ι] [∀ i, PartialOrder (α i)] : PartialOrder (Σₗ i, α i) :=
  { Lex.preorder with le_antisymm := fun _ _ => antisymm_of (Lex (· < ·) fun _ => (· ≤ ·)) }
#align sigma.lex.partial_order Sigma.Lex.partialOrder
-/

#print Sigma.Lex.linearOrder /-
/-- The lexicographical linear order on a sigma type. -/
instance linearOrder [LinearOrder ι] [∀ i, LinearOrder (α i)] : LinearOrder (Σₗ i, α i) :=
  { Lex.partialOrder with
    le_total := total_of (Lex (· < ·) fun _ => (· ≤ ·))
    DecidableEq := Sigma.decidableEq
    decidableLe := Lex.decidable _ _ }
#align sigma.lex.linear_order Sigma.Lex.linearOrder
-/

/- warning: sigma.lex.order_bot -> Sigma.Lex.orderBot is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : PartialOrder.{u1} ι] [_inst_2 : OrderBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1))] [_inst_3 : forall (i : ι), Preorder.{u2} (α i)] [_inst_4 : OrderBot.{u2} (α (Bot.bot.{u1} ι (OrderBot.toHasBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2))) (Preorder.toLE.{u2} (α (Bot.bot.{u1} ι (OrderBot.toHasBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2))) (_inst_3 (Bot.bot.{u1} ι (OrderBot.toHasBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2))))], OrderBot.{max u1 u2} (Lex.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Sigma.Lex.LE.{u1, u2} ι (fun (i : ι) => α i) (Preorder.toLT.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) (fun (i : ι) => Preorder.toLE.{u2} (α i) (_inst_3 i)))
but is expected to have type
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : PartialOrder.{u1} ι] [_inst_2 : OrderBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1))] [_inst_3 : forall (i : ι), Preorder.{u2} (α i)] [_inst_4 : OrderBot.{u2} (α (Bot.bot.{u1} ι (OrderBot.toBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2))) (Preorder.toLE.{u2} (α (Bot.bot.{u1} ι (OrderBot.toBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2))) (_inst_3 (Bot.bot.{u1} ι (OrderBot.toBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2))))], OrderBot.{max u2 u1} (Lex.{max u2 u1} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Sigma.Lex.LE.{u1, u2} ι (fun (i : ι) => α i) (Preorder.toLT.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) (fun (i : ι) => Preorder.toLE.{u2} (α i) (_inst_3 i)))
Case conversion may be inaccurate. Consider using '#align sigma.lex.order_bot Sigma.Lex.orderBotₓ'. -/
/-- The lexicographical linear order on a sigma type. -/
instance orderBot [PartialOrder ι] [OrderBot ι] [∀ i, Preorder (α i)] [OrderBot (α ⊥)] :
    OrderBot (Σₗ i, α i) where
  bot := ⟨⊥, ⊥⟩
  bot_le := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_bot_or_bot_lt a
    · exact lex.right _ _ bot_le
    · exact lex.left _ _ ha
#align sigma.lex.order_bot Sigma.Lex.orderBot

/- warning: sigma.lex.order_top -> Sigma.Lex.orderTop is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : PartialOrder.{u1} ι] [_inst_2 : OrderTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1))] [_inst_3 : forall (i : ι), Preorder.{u2} (α i)] [_inst_4 : OrderTop.{u2} (α (Top.top.{u1} ι (OrderTop.toHasTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2))) (Preorder.toLE.{u2} (α (Top.top.{u1} ι (OrderTop.toHasTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2))) (_inst_3 (Top.top.{u1} ι (OrderTop.toHasTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2))))], OrderTop.{max u1 u2} (Lex.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Sigma.Lex.LE.{u1, u2} ι (fun (i : ι) => α i) (Preorder.toLT.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) (fun (i : ι) => Preorder.toLE.{u2} (α i) (_inst_3 i)))
but is expected to have type
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : PartialOrder.{u1} ι] [_inst_2 : OrderTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1))] [_inst_3 : forall (i : ι), Preorder.{u2} (α i)] [_inst_4 : OrderTop.{u2} (α (Top.top.{u1} ι (OrderTop.toTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2))) (Preorder.toLE.{u2} (α (Top.top.{u1} ι (OrderTop.toTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2))) (_inst_3 (Top.top.{u1} ι (OrderTop.toTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2))))], OrderTop.{max u2 u1} (Lex.{max u2 u1} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Sigma.Lex.LE.{u1, u2} ι (fun (i : ι) => α i) (Preorder.toLT.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) (fun (i : ι) => Preorder.toLE.{u2} (α i) (_inst_3 i)))
Case conversion may be inaccurate. Consider using '#align sigma.lex.order_top Sigma.Lex.orderTopₓ'. -/
/-- The lexicographical linear order on a sigma type. -/
instance orderTop [PartialOrder ι] [OrderTop ι] [∀ i, Preorder (α i)] [OrderTop (α ⊤)] :
    OrderTop (Σₗ i, α i) where
  top := ⟨⊤, ⊤⟩
  le_top := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_top_or_lt_top a
    · exact lex.right _ _ le_top
    · exact lex.left _ _ ha
#align sigma.lex.order_top Sigma.Lex.orderTop

/- warning: sigma.lex.bounded_order -> Sigma.Lex.boundedOrder is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : PartialOrder.{u1} ι] [_inst_2 : BoundedOrder.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1))] [_inst_3 : forall (i : ι), Preorder.{u2} (α i)] [_inst_4 : OrderBot.{u2} (α (Bot.bot.{u1} ι (OrderBot.toHasBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) (BoundedOrder.toOrderBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2)))) (Preorder.toLE.{u2} (α (Bot.bot.{u1} ι (OrderBot.toHasBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) (BoundedOrder.toOrderBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2)))) (_inst_3 (Bot.bot.{u1} ι (OrderBot.toHasBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) (BoundedOrder.toOrderBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2)))))] [_inst_5 : OrderTop.{u2} (α (Top.top.{u1} ι (OrderTop.toHasTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) (BoundedOrder.toOrderTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2)))) (Preorder.toLE.{u2} (α (Top.top.{u1} ι (OrderTop.toHasTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) (BoundedOrder.toOrderTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2)))) (_inst_3 (Top.top.{u1} ι (OrderTop.toHasTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) (BoundedOrder.toOrderTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2)))))], BoundedOrder.{max u1 u2} (Lex.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Sigma.Lex.LE.{u1, u2} ι (fun (i : ι) => α i) (Preorder.toLT.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) (fun (i : ι) => Preorder.toLE.{u2} (α i) (_inst_3 i)))
but is expected to have type
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : PartialOrder.{u1} ι] [_inst_2 : BoundedOrder.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1))] [_inst_3 : forall (i : ι), Preorder.{u2} (α i)] [_inst_4 : OrderBot.{u2} (α (Bot.bot.{u1} ι (OrderBot.toBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) (BoundedOrder.toOrderBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2)))) (Preorder.toLE.{u2} (α (Bot.bot.{u1} ι (OrderBot.toBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) (BoundedOrder.toOrderBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2)))) (_inst_3 (Bot.bot.{u1} ι (OrderBot.toBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) (BoundedOrder.toOrderBot.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2)))))] [_inst_5 : OrderTop.{u2} (α (Top.top.{u1} ι (OrderTop.toTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) (BoundedOrder.toOrderTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2)))) (Preorder.toLE.{u2} (α (Top.top.{u1} ι (OrderTop.toTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) (BoundedOrder.toOrderTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2)))) (_inst_3 (Top.top.{u1} ι (OrderTop.toTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) (BoundedOrder.toOrderTop.{u1} ι (Preorder.toLE.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) _inst_2)))))], BoundedOrder.{max u2 u1} (Lex.{max u2 u1} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Sigma.Lex.LE.{u1, u2} ι (fun (i : ι) => α i) (Preorder.toLT.{u1} ι (PartialOrder.toPreorder.{u1} ι _inst_1)) (fun (i : ι) => Preorder.toLE.{u2} (α i) (_inst_3 i)))
Case conversion may be inaccurate. Consider using '#align sigma.lex.bounded_order Sigma.Lex.boundedOrderₓ'. -/
/-- The lexicographical linear order on a sigma type. -/
instance boundedOrder [PartialOrder ι] [BoundedOrder ι] [∀ i, Preorder (α i)] [OrderBot (α ⊥)]
    [OrderTop (α ⊤)] : BoundedOrder (Σₗ i, α i) :=
  { Lex.orderBot, Lex.orderTop with }
#align sigma.lex.bounded_order Sigma.Lex.boundedOrder

#print Sigma.Lex.denselyOrdered /-
instance denselyOrdered [Preorder ι] [DenselyOrdered ι] [∀ i, Nonempty (α i)] [∀ i, Preorder (α i)]
    [∀ i, DenselyOrdered (α i)] : DenselyOrdered (Σₗ i, α i) :=
  ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩)
    · obtain ⟨k, hi, hj⟩ := exists_between h
      obtain ⟨c⟩ : Nonempty (α k) := inferInstance
      exact ⟨⟨k, c⟩, left _ _ hi, left _ _ hj⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩⟩
#align sigma.lex.densely_ordered Sigma.Lex.denselyOrdered
-/

#print Sigma.Lex.denselyOrdered_of_noMaxOrder /-
instance denselyOrdered_of_noMaxOrder [Preorder ι] [∀ i, Preorder (α i)] [∀ i, DenselyOrdered (α i)]
    [∀ i, NoMaxOrder (α i)] : DenselyOrdered (Σₗ i, α i) :=
  ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩)
    · obtain ⟨c, ha⟩ := exists_gt a
      exact ⟨⟨i, c⟩, right _ _ ha, left _ _ h⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩⟩
#align sigma.lex.densely_ordered_of_no_max_order Sigma.Lex.denselyOrdered_of_noMaxOrder
-/

#print Sigma.Lex.denselyOrdered_of_noMinOrder /-
instance denselyOrdered_of_noMinOrder [Preorder ι] [∀ i, Preorder (α i)] [∀ i, DenselyOrdered (α i)]
    [∀ i, NoMinOrder (α i)] : DenselyOrdered (Σₗ i, α i) :=
  ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩)
    · obtain ⟨c, hb⟩ := exists_lt b
      exact ⟨⟨j, c⟩, left _ _ h, right _ _ hb⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩⟩
#align sigma.lex.densely_ordered_of_no_min_order Sigma.Lex.denselyOrdered_of_noMinOrder
-/

#print Sigma.Lex.noMaxOrder_of_nonempty /-
instance noMaxOrder_of_nonempty [Preorder ι] [∀ i, Preorder (α i)] [NoMaxOrder ι]
    [∀ i, Nonempty (α i)] : NoMaxOrder (Σₗ i, α i) :=
  ⟨by
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_gt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩⟩
#align sigma.lex.no_max_order_of_nonempty Sigma.Lex.noMaxOrder_of_nonempty
-/

/- warning: sigma.lex.no_min_order_of_nonempty clashes with [anonymous] -> [anonymous]
warning: sigma.lex.no_min_order_of_nonempty -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : Preorder.{u1} ι] [_inst_2 : forall (i : ι), Preorder.{u2} (α i)] [_inst_3 : NoMaxOrder.{u1} ι (Preorder.toLT.{u1} ι _inst_1)] [_inst_4 : forall (i : ι), Nonempty.{succ u2} (α i)], NoMaxOrder.{max u1 u2} (Lex.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Sigma.Lex.LT.{u1, u2} ι (fun (i : ι) => α i) (Preorder.toLT.{u1} ι _inst_1) (fun (i : ι) => Preorder.toLT.{u2} (α i) (_inst_2 i)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}}, (Nat -> ι -> α) -> Nat -> (List.{u1} ι) -> (List.{u2} α)
Case conversion may be inaccurate. Consider using '#align sigma.lex.no_min_order_of_nonempty [anonymous]ₓ'. -/
instance [anonymous] [Preorder ι] [∀ i, Preorder (α i)] [NoMaxOrder ι] [∀ i, Nonempty (α i)] :
    NoMaxOrder (Σₗ i, α i) :=
  ⟨by
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_gt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩⟩
#align sigma.lex.no_min_order_of_nonempty [anonymous]

#print Sigma.Lex.noMaxOrder /-
instance noMaxOrder [Preorder ι] [∀ i, Preorder (α i)] [∀ i, NoMaxOrder (α i)] :
    NoMaxOrder (Σₗ i, α i) :=
  ⟨by
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_gt a
    exact ⟨⟨i, b⟩, right _ _ h⟩⟩
#align sigma.lex.no_max_order Sigma.Lex.noMaxOrder
-/

#print Sigma.Lex.noMinOrder /-
instance noMinOrder [Preorder ι] [∀ i, Preorder (α i)] [∀ i, NoMinOrder (α i)] :
    NoMinOrder (Σₗ i, α i) :=
  ⟨by
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_lt a
    exact ⟨⟨i, b⟩, right _ _ h⟩⟩
#align sigma.lex.no_min_order Sigma.Lex.noMinOrder
-/

end Lex

end Sigma

