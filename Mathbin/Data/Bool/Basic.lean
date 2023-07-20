/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/

#align_import data.bool.basic from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# booleans

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves various trivial lemmas about booleans and their
relation to decidable propositions.

## Notations

This file introduces the notation `!b` for `bnot b`, the boolean "not".

## Tags
bool, boolean, De Morgan
-/


prefix:90 "!" => not

namespace Bool

-- TODO: duplicate of a lemma in core
theorem coeSort_true : coeSort.{1, 1} true = True :=
  Bool.coe_sort_true
#align bool.coe_sort_tt Bool.coeSort_true

-- TODO: duplicate of a lemma in core
theorem coeSort_false : coeSort.{1, 1} false = False :=
  Bool.coe_sort_false
#align bool.coe_sort_ff Bool.coeSort_false

#print Bool.decide_True /-
-- TODO: duplicate of a lemma in core
theorem decide_True {h} : @decide True h = true :=
  decide_True' h
#align bool.to_bool_true Bool.decide_True
-/

#print Bool.decide_False /-
-- TODO: duplicate of a lemma in core
theorem decide_False {h} : @decide False h = false :=
  decide_False' h
#align bool.to_bool_false Bool.decide_False
-/

#print Bool.decide_coe /-
@[simp]
theorem decide_coe (b : Bool) {h} : @decide b h = b :=
  show _ = decide b by congr.trans (by cases b <;> rfl)
#align bool.to_bool_coe Bool.decide_coe
-/

#print Bool.coe_decide /-
theorem coe_decide (p : Prop) [Decidable p] : decide p ↔ p :=
  Bool.decide_iff _
#align bool.coe_to_bool Bool.coe_decide
-/

#print Bool.of_decide_iff /-
@[simp]
theorem of_decide_iff {p : Prop} [Decidable p] : decide p ↔ p :=
  ⟨Bool.of_decide_true, Bool.decide_true⟩
#align bool.of_to_bool_iff Bool.of_decide_iff
-/

#print Bool.true_eq_decide_iff /-
@[simp]
theorem true_eq_decide_iff {p : Prop} [Decidable p] : true = decide p ↔ p :=
  eq_comm.trans of_decide_iff
#align bool.tt_eq_to_bool_iff Bool.true_eq_decide_iff
-/

#print Bool.false_eq_decide_iff /-
@[simp]
theorem false_eq_decide_iff {p : Prop} [Decidable p] : false = decide p ↔ ¬p :=
  eq_comm.trans (Bool.decide_false_iff _)
#align bool.ff_eq_to_bool_iff Bool.false_eq_decide_iff
-/

#print Bool.decide_not /-
@[simp]
theorem decide_not (p : Prop) [Decidable p] : (decide ¬p) = !decide p := by by_cases p <;> simp [*]
#align bool.to_bool_not Bool.decide_not
-/

#print Bool.decide_and /-
@[simp]
theorem decide_and (p q : Prop) [Decidable p] [Decidable q] : decide (p ∧ q) = (p && q) := by
  by_cases p <;> by_cases q <;> simp [*]
#align bool.to_bool_and Bool.decide_and
-/

#print Bool.decide_or /-
@[simp]
theorem decide_or (p q : Prop) [Decidable p] [Decidable q] : decide (p ∨ q) = (p || q) := by
  by_cases p <;> by_cases q <;> simp [*]
#align bool.to_bool_or Bool.decide_or
-/

#print decide_eq_decide /-
@[simp]
theorem decide_eq_decide {p q : Prop} [Decidable p] [Decidable q] : decide p = decide q ↔ (p ↔ q) :=
  ⟨fun h => (coe_decide p).symm.trans <| by simp [h], Bool.decide_congr⟩
#align bool.to_bool_eq decide_eq_decide
-/

#print Bool.not_false' /-
theorem not_false' : ¬false :=
  false_ne_true
#align bool.not_ff Bool.not_false'
-/

#print Bool.default_bool /-
@[simp]
theorem default_bool : default = false :=
  rfl
#align bool.default_bool Bool.default_bool
-/

#print Bool.dichotomy /-
theorem dichotomy (b : Bool) : b = false ∨ b = true := by cases b <;> simp
#align bool.dichotomy Bool.dichotomy
-/

#print Bool.forall_bool /-
@[simp]
theorem forall_bool {p : Bool → Prop} : (∀ b, p b) ↔ p false ∧ p true :=
  ⟨fun h => by simp [h], fun ⟨h₁, h₂⟩ b => by cases b <;> assumption⟩
#align bool.forall_bool Bool.forall_bool
-/

#print Bool.exists_bool /-
@[simp]
theorem exists_bool {p : Bool → Prop} : (∃ b, p b) ↔ p false ∨ p true :=
  ⟨fun ⟨b, h⟩ => by cases b <;> [exact Or.inl h; exact Or.inr h], fun h => by
    cases h <;> exact ⟨_, h⟩⟩
#align bool.exists_bool Bool.exists_bool
-/

#print Bool.decidableForallBool /-
/-- If `p b` is decidable for all `b : bool`, then `∀ b, p b` is decidable -/
instance decidableForallBool {p : Bool → Prop} [∀ b, Decidable (p b)] : Decidable (∀ b, p b) :=
  decidable_of_decidable_of_iff And.decidable forall_bool.symm
#align bool.decidable_forall_bool Bool.decidableForallBool
-/

#print Bool.decidableExistsBool /-
/-- If `p b` is decidable for all `b : bool`, then `∃ b, p b` is decidable -/
instance decidableExistsBool {p : Bool → Prop} [∀ b, Decidable (p b)] : Decidable (∃ b, p b) :=
  decidable_of_decidable_of_iff Or.decidable exists_bool.symm
#align bool.decidable_exists_bool Bool.decidableExistsBool
-/

#print Bool.cond_false /-
@[simp]
theorem cond_false {α} (t e : α) : cond false t e = e :=
  rfl
#align bool.cond_ff Bool.cond_false
-/

#print Bool.cond_true /-
@[simp]
theorem cond_true {α} (t e : α) : cond true t e = t :=
  rfl
#align bool.cond_tt Bool.cond_true
-/

#print Bool.cond_eq_ite /-
theorem cond_eq_ite {α} (b : Bool) (t e : α) : cond b t e = if b then t else e := by
  cases b <;> simp
#align bool.cond_eq_ite Bool.cond_eq_ite
-/

#print Bool.cond_decide /-
@[simp]
theorem cond_decide {α} (p : Prop) [Decidable p] (t e : α) :
    cond (decide p) t e = if p then t else e := by simp [cond_eq_ite]
#align bool.cond_to_bool Bool.cond_decide
-/

#print Bool.cond_not /-
@[simp]
theorem cond_not {α} (b : Bool) (t e : α) : cond (!b) t e = cond b e t := by cases b <;> rfl
#align bool.cond_bnot Bool.cond_not
-/

#print Bool.not_ne_id /-
theorem not_ne_id : not ≠ id := fun h => false_ne_true <| congr_fun h true
#align bool.bnot_ne_id Bool.not_ne_id
-/

#print Bool.coe_bool_iff /-
theorem coe_bool_iff : ∀ {a b : Bool}, (a ↔ b) ↔ a = b := by decide
#align bool.coe_bool_iff Bool.coe_bool_iff
-/

#print Bool.eq_true_of_ne_false /-
theorem eq_true_of_ne_false : ∀ {a : Bool}, a ≠ false → a = true := by decide
#align bool.eq_tt_of_ne_ff Bool.eq_true_of_ne_false
-/

#print Bool.eq_false_of_ne_true /-
theorem eq_false_of_ne_true : ∀ {a : Bool}, a ≠ true → a = false := by decide
#align bool.eq_ff_of_ne_tt Bool.eq_false_of_ne_true
-/

#print Bool.or_comm /-
theorem or_comm : ∀ a b, (a || b) = (b || a) := by decide
#align bool.bor_comm Bool.or_comm
-/

#print Bool.or_assoc /-
@[simp]
theorem or_assoc : ∀ a b c, (a || b || c) = (a || (b || c)) := by decide
#align bool.bor_assoc Bool.or_assoc
-/

#print Bool.or_left_comm /-
theorem or_left_comm : ∀ a b c, (a || (b || c)) = (b || (a || c)) := by decide
#align bool.bor_left_comm Bool.or_left_comm
-/

#print Bool.or_inl /-
theorem or_inl {a b : Bool} (H : a) : a || b := by simp [H]
#align bool.bor_inl Bool.or_inl
-/

#print Bool.or_inr /-
theorem or_inr {a b : Bool} (H : b) : a || b := by simp [H]
#align bool.bor_inr Bool.or_inr
-/

#print Bool.and_comm /-
theorem and_comm : ∀ a b, (a && b) = (b && a) := by decide
#align bool.band_comm Bool.and_comm
-/

#print Bool.and_assoc /-
@[simp]
theorem and_assoc : ∀ a b c, (a && b && c) = (a && (b && c)) := by decide
#align bool.band_assoc Bool.and_assoc
-/

#print Bool.and_left_comm /-
theorem and_left_comm : ∀ a b c, (a && (b && c)) = (b && (a && c)) := by decide
#align bool.band_left_comm Bool.and_left_comm
-/

#print Bool.and_elim_left /-
theorem and_elim_left : ∀ {a b : Bool}, a && b → a := by decide
#align bool.band_elim_left Bool.and_elim_left
-/

#print Bool.and_intro /-
theorem and_intro : ∀ {a b : Bool}, a → b → a && b := by decide
#align bool.band_intro Bool.and_intro
-/

#print Bool.and_elim_right /-
theorem and_elim_right : ∀ {a b : Bool}, a && b → b := by decide
#align bool.band_elim_right Bool.and_elim_right
-/

#print Bool.and_or_distrib_left /-
theorem and_or_distrib_left (a b c : Bool) : (a && (b || c)) = (a && b || a && c) := by
  cases a <;> simp
#align bool.band_bor_distrib_left Bool.and_or_distrib_left
-/

#print Bool.and_or_distrib_right /-
theorem and_or_distrib_right (a b c : Bool) : ((a || b) && c) = (a && c || b && c) := by
  cases c <;> simp
#align bool.band_bor_distrib_right Bool.and_or_distrib_right
-/

#print Bool.or_and_distrib_left /-
theorem or_and_distrib_left (a b c : Bool) : (a || b && c) = ((a || b) && (a || c)) := by
  cases a <;> simp
#align bool.bor_band_distrib_left Bool.or_and_distrib_left
-/

#print Bool.or_and_distrib_right /-
theorem or_and_distrib_right (a b c : Bool) : (a && b || c) = ((a || c) && (b || c)) := by
  cases c <;> simp
#align bool.bor_band_distrib_right Bool.or_and_distrib_right
-/

#print Bool.not_false /-
@[simp]
theorem not_false : !false = true :=
  rfl
#align bool.bnot_ff Bool.not_false
-/

#print Bool.not_true /-
@[simp]
theorem not_true : !true = false :=
  rfl
#align bool.bnot_tt Bool.not_true
-/

#print Bool.eq_not_iff /-
theorem eq_not_iff : ∀ {a b : Bool}, a = !b ↔ a ≠ b := by decide
#align bool.eq_bnot_iff Bool.eq_not_iff
-/

#print Bool.not_eq_iff /-
theorem not_eq_iff : ∀ {a b : Bool}, !a = b ↔ a ≠ b := by decide
#align bool.bnot_eq_iff Bool.not_eq_iff
-/

#print Bool.not_eq_not /-
@[simp]
theorem not_eq_not : ∀ {a b : Bool}, ¬a = !b ↔ a = b := by decide
#align bool.not_eq_bnot Bool.not_eq_not
-/

#print Bool.not_not_eq /-
@[simp]
theorem not_not_eq : ∀ {a b : Bool}, ¬!a = b ↔ a = b := by decide
#align bool.bnot_not_eq Bool.not_not_eq
-/

#print Bool.ne_not /-
theorem ne_not {a b : Bool} : a ≠ !b ↔ a = b :=
  not_eq_not
#align bool.ne_bnot Bool.ne_not
-/

#print Bool.not_ne /-
theorem not_ne {a b : Bool} : !a ≠ b ↔ a = b :=
  not_not_eq
#align bool.bnot_ne Bool.not_ne
-/

#print Bool.not_ne_self /-
theorem not_ne_self : ∀ b : Bool, !b ≠ b := by decide
#align bool.bnot_ne_self Bool.not_ne_self
-/

#print Bool.self_ne_not /-
theorem self_ne_not : ∀ b : Bool, b ≠ !b := by decide
#align bool.self_ne_bnot Bool.self_ne_not
-/

#print Bool.eq_or_eq_not /-
theorem eq_or_eq_not : ∀ a b, a = b ∨ a = !b := by decide
#align bool.eq_or_eq_bnot Bool.eq_or_eq_not
-/

#print Bool.not_iff_not /-
@[simp]
theorem not_iff_not : ∀ {b : Bool}, !b ↔ ¬b := by decide
#align bool.bnot_iff_not Bool.not_iff_not
-/

#print Bool.eq_true_of_not_eq_false' /-
theorem eq_true_of_not_eq_false' : ∀ {a : Bool}, !a = false → a = true := by decide
#align bool.eq_tt_of_bnot_eq_ff Bool.eq_true_of_not_eq_false'
-/

#print Bool.eq_false_of_not_eq_true' /-
theorem eq_false_of_not_eq_true' : ∀ {a : Bool}, !a = true → a = false := by decide
#align bool.eq_ff_of_bnot_eq_tt Bool.eq_false_of_not_eq_true'
-/

#print Bool.and_not_self /-
@[simp]
theorem and_not_self : ∀ x, (x && !x) = false := by decide
#align bool.band_bnot_self Bool.and_not_self
-/

#print Bool.not_and_self /-
@[simp]
theorem not_and_self : ∀ x, (!x && x) = false := by decide
#align bool.bnot_band_self Bool.not_and_self
-/

#print Bool.or_not_self /-
@[simp]
theorem or_not_self : ∀ x, (x || !x) = true := by decide
#align bool.bor_bnot_self Bool.or_not_self
-/

#print Bool.not_or_self /-
@[simp]
theorem not_or_self : ∀ x, (!x || x) = true := by decide
#align bool.bnot_bor_self Bool.not_or_self
-/

#print Bool.xor_comm /-
theorem xor_comm : ∀ a b, xor a b = xor b a := by decide
#align bool.bxor_comm Bool.xor_comm
-/

#print Bool.xor_assoc /-
@[simp]
theorem xor_assoc : ∀ a b c, xor (xor a b) c = xor a (xor b c) := by decide
#align bool.bxor_assoc Bool.xor_assoc
-/

#print Bool.xor_left_comm /-
theorem xor_left_comm : ∀ a b c, xor a (xor b c) = xor b (xor a c) := by decide
#align bool.bxor_left_comm Bool.xor_left_comm
-/

#print Bool.xor_not_left /-
@[simp]
theorem xor_not_left : ∀ a, xor (!a) a = true := by decide
#align bool.bxor_bnot_left Bool.xor_not_left
-/

#print Bool.xor_not_right /-
@[simp]
theorem xor_not_right : ∀ a, xor a (!a) = true := by decide
#align bool.bxor_bnot_right Bool.xor_not_right
-/

#print Bool.xor_not_not /-
@[simp]
theorem xor_not_not : ∀ a b, xor (!a) (!b) = xor a b := by decide
#align bool.bxor_bnot_bnot Bool.xor_not_not
-/

#print Bool.xor_false_left /-
@[simp]
theorem xor_false_left : ∀ a, xor false a = a := by decide
#align bool.bxor_ff_left Bool.xor_false_left
-/

#print Bool.xor_false_right /-
@[simp]
theorem xor_false_right : ∀ a, xor a false = a := by decide
#align bool.bxor_ff_right Bool.xor_false_right
-/

#print Bool.and_xor_distrib_left /-
theorem and_xor_distrib_left (a b c : Bool) : (a && xor b c) = xor (a && b) (a && c) := by
  cases a <;> simp
#align bool.band_bxor_distrib_left Bool.and_xor_distrib_left
-/

#print Bool.and_xor_distrib_right /-
theorem and_xor_distrib_right (a b c : Bool) : (xor a b && c) = xor (a && c) (b && c) := by
  cases c <;> simp
#align bool.band_bxor_distrib_right Bool.and_xor_distrib_right
-/

#print Bool.xor_iff_ne /-
theorem xor_iff_ne : ∀ {x y : Bool}, xor x y = true ↔ x ≠ y := by decide
#align bool.bxor_iff_ne Bool.xor_iff_ne
-/

/-! ### De Morgan's laws for booleans-/


#print Bool.not_and /-
@[simp]
theorem not_and : ∀ a b : Bool, !(a && b) = (!a || !b) := by decide
#align bool.bnot_band Bool.not_and
-/

#print Bool.not_or /-
@[simp]
theorem not_or : ∀ a b : Bool, !(a || b) = (!a && !b) := by decide
#align bool.bnot_bor Bool.not_or
-/

#print Bool.not_inj /-
theorem not_inj : ∀ {a b : Bool}, !a = !b → a = b := by decide
#align bool.bnot_inj Bool.not_inj
-/

instance : LinearOrder Bool where
  le a b := a = false ∨ b = true
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide
  decidableLe := inferInstance
  DecidableEq := inferInstance
  max := or
  max_def := by funext x y; revert x y; exact by decide
  min := and
  min_def := by funext x y; revert x y; exact by decide

#print Bool.false_le /-
@[simp]
theorem false_le {x : Bool} : false ≤ x :=
  Or.intro_left _ rfl
#align bool.ff_le Bool.false_le
-/

#print Bool.le_true /-
@[simp]
theorem le_true {x : Bool} : x ≤ true :=
  Or.intro_right _ rfl
#align bool.le_tt Bool.le_true
-/

#print Bool.lt_iff /-
theorem lt_iff : ∀ {x y : Bool}, x < y ↔ x = false ∧ y = true := by decide
#align bool.lt_iff Bool.lt_iff
-/

#print Bool.false_lt_true /-
@[simp]
theorem false_lt_true : false < true :=
  lt_iff.2 ⟨rfl, rfl⟩
#align bool.ff_lt_tt Bool.false_lt_true
-/

#print Bool.le_iff_imp /-
theorem le_iff_imp : ∀ {x y : Bool}, x ≤ y ↔ x → y := by decide
#align bool.le_iff_imp Bool.le_iff_imp
-/

#print Bool.and_le_left /-
theorem and_le_left : ∀ x y : Bool, (x && y) ≤ x := by decide
#align bool.band_le_left Bool.and_le_left
-/

#print Bool.and_le_right /-
theorem and_le_right : ∀ x y : Bool, (x && y) ≤ y := by decide
#align bool.band_le_right Bool.and_le_right
-/

#print Bool.le_and /-
theorem le_and : ∀ {x y z : Bool}, x ≤ y → x ≤ z → x ≤ (y && z) := by decide
#align bool.le_band Bool.le_and
-/

#print Bool.left_le_or /-
theorem left_le_or : ∀ x y : Bool, x ≤ (x || y) := by decide
#align bool.left_le_bor Bool.left_le_or
-/

#print Bool.right_le_or /-
theorem right_le_or : ∀ x y : Bool, y ≤ (x || y) := by decide
#align bool.right_le_bor Bool.right_le_or
-/

#print Bool.or_le /-
theorem or_le : ∀ {x y z}, x ≤ z → y ≤ z → (x || y) ≤ z := by decide
#align bool.bor_le Bool.or_le
-/

#print Bool.toNat /-
/-- convert a `bool` to a `ℕ`, `false -> 0`, `true -> 1` -/
def toNat (b : Bool) : ℕ :=
  cond b 1 0
#align bool.to_nat Bool.toNat
-/

#print Bool.ofNat /-
/-- convert a `ℕ` to a `bool`, `0 -> false`, everything else -> `true` -/
def ofNat (n : ℕ) : Bool :=
  decide (n ≠ 0)
#align bool.of_nat Bool.ofNat
-/

#print Bool.ofNat_le_ofNat /-
theorem ofNat_le_ofNat {n m : ℕ} (h : n ≤ m) : ofNat n ≤ ofNat m :=
  by
  simp [of_nat] <;> cases Nat.decidableEq n 0 <;> cases Nat.decidableEq m 0 <;> simp only [to_bool]
  · subst m; have h := le_antisymm h (Nat.zero_le _)
    contradiction
  · left; rfl
#align bool.of_nat_le_of_nat Bool.ofNat_le_ofNat
-/

#print Bool.toNat_le_toNat /-
theorem toNat_le_toNat {b₀ b₁ : Bool} (h : b₀ ≤ b₁) : toNat b₀ ≤ toNat b₁ := by
  cases h <;> subst h <;> [cases b₁; cases b₀] <;> simp [toNat, Nat.zero_le]
#align bool.to_nat_le_to_nat Bool.toNat_le_toNat
-/

#print Bool.ofNat_toNat /-
theorem ofNat_toNat (b : Bool) : ofNat (toNat b) = b := by
  cases b <;> simp only [of_nat, toNat] <;> exact by decide
#align bool.of_nat_to_nat Bool.ofNat_toNat
-/

#print Bool.injective_iff /-
@[simp]
theorem injective_iff {α : Sort _} {f : Bool → α} : Function.Injective f ↔ f false ≠ f true :=
  ⟨fun Hinj Heq => false_ne_true (Hinj Heq), fun H x y hxy => by cases x <;> cases y;
    exacts [rfl, (H hxy).elim, (H hxy.symm).elim, rfl]⟩
#align bool.injective_iff Bool.injective_iff
-/

#print Bool.apply_apply_apply /-
/-- **Kaminski's Equation** -/
theorem apply_apply_apply (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x := by
  cases x <;> cases h₁ : f tt <;> cases h₂ : f ff <;> simp only [h₁, h₂]
#align bool.apply_apply_apply Bool.apply_apply_apply
-/

end Bool

