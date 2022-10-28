/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/

/-!
# booleans

This file proves various trivial lemmas about booleans and their
relation to decidable propositions.

## Notations

This file introduces the notation `!b` for `bnot b`, the boolean "not".

## Tags
bool, boolean, De Morgan
-/


-- mathport name: «expr! »
prefix:90 "!" => not

namespace Bool

-- TODO: duplicate of a lemma in core
theorem coe_sort_tt : coeSort.{1, 1} true = True :=
  coe_sort_tt

-- TODO: duplicate of a lemma in core
theorem coe_sort_ff : coeSort.{1, 1} false = False :=
  coe_sort_ff

-- TODO: duplicate of a lemma in core
theorem to_bool_true {h} : @decide True h = tt :=
  decide_True' h

-- TODO: duplicate of a lemma in core
theorem to_bool_false {h} : @decide False h = ff :=
  decide_False' h

@[simp]
theorem to_bool_coe (b : Bool) {h} : @decide b h = b :=
  show _ = decide b by congr.trans (by cases b <;> rfl)

theorem coe_to_bool (p : Prop) [Decidable p] : decide p ↔ p :=
  to_bool_iff _

@[simp]
theorem of_to_bool_iff {p : Prop} [Decidable p] : decide p ↔ p :=
  ⟨of_to_bool_true, to_bool_true⟩

@[simp]
theorem tt_eq_to_bool_iff {p : Prop} [Decidable p] : tt = decide p ↔ p :=
  eq_comm.trans of_to_bool_iff

@[simp]
theorem ff_eq_to_bool_iff {p : Prop} [Decidable p] : ff = decide p ↔ ¬p :=
  eq_comm.trans (to_bool_ff_iff _)

@[simp]
theorem to_bool_not (p : Prop) [Decidable p] : (decide ¬p) = not (decide p) := by by_cases p <;> simp [*]

@[simp]
theorem to_bool_and (p q : Prop) [Decidable p] [Decidable q] : decide (p ∧ q) = (p && q) := by
  by_cases p <;> by_cases q <;> simp [*]

@[simp]
theorem to_bool_or (p q : Prop) [Decidable p] [Decidable q] : decide (p ∨ q) = (p || q) := by
  by_cases p <;> by_cases q <;> simp [*]

@[simp]
theorem to_bool_eq {p q : Prop} [Decidable p] [Decidable q] : decide p = decide q ↔ (p ↔ q) :=
  ⟨fun h => (coe_to_bool p).symm.trans <| by simp [h], to_bool_congr⟩

theorem not_ff : ¬ff :=
  ff_ne_tt

@[simp]
theorem default_bool : default = ff :=
  rfl

theorem dichotomy (b : Bool) : b = ff ∨ b = tt := by cases b <;> simp

@[simp]
theorem forall_bool {p : Bool → Prop} : (∀ b, p b) ↔ p false ∧ p true :=
  ⟨fun h => by simp [h], fun ⟨h₁, h₂⟩ b => by cases b <;> assumption⟩

@[simp]
theorem exists_bool {p : Bool → Prop} : (∃ b, p b) ↔ p false ∨ p true :=
  ⟨fun ⟨b, h⟩ => by cases b <;> [exact Or.inl h, exact Or.inr h], fun h => by cases h <;> exact ⟨_, h⟩⟩

/-- If `p b` is decidable for all `b : bool`, then `∀ b, p b` is decidable -/
instance decidableForallBool {p : Bool → Prop} [∀ b, Decidable (p b)] : Decidable (∀ b, p b) :=
  decidable_of_decidable_of_iff And.decidable forall_bool.symm

/-- If `p b` is decidable for all `b : bool`, then `∃ b, p b` is decidable -/
instance decidableExistsBool {p : Bool → Prop} [∀ b, Decidable (p b)] : Decidable (∃ b, p b) :=
  decidable_of_decidable_of_iff Or.decidable exists_bool.symm

@[simp]
theorem cond_ff {α} (t e : α) : cond false t e = e :=
  rfl

@[simp]
theorem cond_tt {α} (t e : α) : cond true t e = t :=
  rfl

theorem cond_eq_ite {α} (b : Bool) (t e : α) : cond b t e = if b then t else e := by cases b <;> simp

@[simp]
theorem cond_to_bool {α} (p : Prop) [Decidable p] (t e : α) : cond (decide p) t e = if p then t else e := by
  simp [cond_eq_ite]

@[simp]
theorem cond_bnot {α} (b : Bool) (t e : α) : cond (!b) t e = cond b e t := by cases b <;> rfl

theorem bnot_ne_id : not ≠ id := fun h => ff_ne_tt <| congr_fun h true

theorem coe_bool_iff : ∀ {a b : Bool}, (a ↔ b) ↔ a = b := by decide

theorem eq_tt_of_ne_ff : ∀ {a : Bool}, a ≠ ff → a = tt := by decide

theorem eq_ff_of_ne_tt : ∀ {a : Bool}, a ≠ tt → a = ff := by decide

theorem bor_comm : ∀ a b, (a || b) = (b || a) := by decide

@[simp]
theorem bor_assoc : ∀ a b c, (a || b || c) = (a || (b || c)) := by decide

theorem bor_left_comm : ∀ a b c, (a || (b || c)) = (b || (a || c)) := by decide

theorem bor_inl {a b : Bool} (H : a) : a || b := by simp [H]

theorem bor_inr {a b : Bool} (H : b) : a || b := by simp [H]

theorem band_comm : ∀ a b, (a && b) = (b && a) := by decide

@[simp]
theorem band_assoc : ∀ a b c, (a && b && c) = (a && (b && c)) := by decide

theorem band_left_comm : ∀ a b c, (a && (b && c)) = (b && (a && c)) := by decide

theorem band_elim_left : ∀ {a b : Bool}, a && b → a := by decide

theorem band_intro : ∀ {a b : Bool}, a → b → a && b := by decide

theorem band_elim_right : ∀ {a b : Bool}, a && b → b := by decide

theorem band_bor_distrib_left (a b c : Bool) : (a && (b || c)) = (a && b || a && c) := by cases a <;> simp

theorem band_bor_distrib_right (a b c : Bool) : ((a || b) && c) = (a && c || b && c) := by cases c <;> simp

theorem bor_band_distrib_left (a b c : Bool) : (a || b && c) = ((a || b) && (a || c)) := by cases a <;> simp

theorem bor_band_distrib_right (a b c : Bool) : (a && b || c) = ((a || c) && (b || c)) := by cases c <;> simp

@[simp]
theorem bnot_false : not false = tt :=
  rfl

@[simp]
theorem bnot_true : not true = ff :=
  rfl

@[simp]
theorem not_eq_bnot : ∀ {a b : Bool}, ¬a = !b ↔ a = b := by decide

@[simp]
theorem bnot_not_eq : ∀ {a b : Bool}, ¬!a = b ↔ a = b := by decide

theorem ne_bnot {a b : Bool} : a ≠ !b ↔ a = b :=
  not_eq_bnot

theorem bnot_ne {a b : Bool} : !a ≠ b ↔ a = b :=
  bnot_not_eq

@[simp]
theorem bnot_iff_not : ∀ {b : Bool}, !b ↔ ¬b := by decide

theorem eq_tt_of_bnot_eq_ff : ∀ {a : Bool}, not a = ff → a = tt := by decide

theorem eq_ff_of_bnot_eq_tt : ∀ {a : Bool}, not a = tt → a = ff := by decide

@[simp]
theorem band_bnot_self : ∀ x, (x && !x) = ff := by decide

@[simp]
theorem bnot_band_self : ∀ x, (!x && x) = ff := by decide

@[simp]
theorem bor_bnot_self : ∀ x, (x || !x) = tt := by decide

@[simp]
theorem bnot_bor_self : ∀ x, (!x || x) = tt := by decide

theorem bxor_comm : ∀ a b, xor a b = xor b a := by decide

@[simp]
theorem bxor_assoc : ∀ a b c, xor (xor a b) c = xor a (xor b c) := by decide

theorem bxor_left_comm : ∀ a b c, xor a (xor b c) = xor b (xor a c) := by decide

@[simp]
theorem bxor_bnot_left : ∀ a, xor (!a) a = tt := by decide

@[simp]
theorem bxor_bnot_right : ∀ a, xor a (!a) = tt := by decide

@[simp]
theorem bxor_bnot_bnot : ∀ a b, xor (!a) (!b) = xor a b := by decide

@[simp]
theorem bxor_ff_left : ∀ a, xor false a = a := by decide

@[simp]
theorem bxor_ff_right : ∀ a, xor a false = a := by decide

theorem band_bxor_distrib_left (a b c : Bool) : (a && xor b c) = xor (a && b) (a && c) := by cases a <;> simp

theorem band_bxor_distrib_right (a b c : Bool) : (xor a b && c) = xor (a && c) (b && c) := by cases c <;> simp

theorem bxor_iff_ne : ∀ {x y : Bool}, xor x y = tt ↔ x ≠ y := by decide

/-! ### De Morgan's laws for booleans-/


@[simp]
theorem bnot_band : ∀ a b : Bool, !(a && b) = (!a || !b) := by decide

@[simp]
theorem bnot_bor : ∀ a b : Bool, !(a || b) = (!a && !b) := by decide

theorem bnot_inj : ∀ {a b : Bool}, !a = !b → a = b := by decide

instance : LinearOrder Bool where
  le a b := a = ff ∨ b = tt
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide
  decidableLe := inferInstance
  DecidableEq := inferInstance
  max := or
  max_def := by
    funext x y
    revert x y
    exact by decide
  min := and
  min_def := by
    funext x y
    revert x y
    exact by decide

@[simp]
theorem ff_le {x : Bool} : ff ≤ x :=
  Or.intro_left _ rfl

@[simp]
theorem le_tt {x : Bool} : x ≤ tt :=
  Or.intro_right _ rfl

theorem lt_iff : ∀ {x y : Bool}, x < y ↔ x = ff ∧ y = tt := by decide

@[simp]
theorem ff_lt_tt : ff < tt :=
  lt_iff.2 ⟨rfl, rfl⟩

theorem le_iff_imp : ∀ {x y : Bool}, x ≤ y ↔ x → y := by decide

theorem band_le_left : ∀ x y : Bool, (x && y) ≤ x := by decide

theorem band_le_right : ∀ x y : Bool, (x && y) ≤ y := by decide

theorem le_band : ∀ {x y z : Bool}, x ≤ y → x ≤ z → x ≤ (y && z) := by decide

theorem left_le_bor : ∀ x y : Bool, x ≤ (x || y) := by decide

theorem right_le_bor : ∀ x y : Bool, y ≤ (x || y) := by decide

theorem bor_le : ∀ {x y z}, x ≤ z → y ≤ z → (x || y) ≤ z := by decide

/-- convert a `bool` to a `ℕ`, `false -> 0`, `true -> 1` -/
def toNat (b : Bool) : ℕ :=
  cond b 1 0

/-- convert a `ℕ` to a `bool`, `0 -> false`, everything else -> `true` -/
def ofNat (n : ℕ) : Bool :=
  decide (n ≠ 0)

theorem of_nat_le_of_nat {n m : ℕ} (h : n ≤ m) : ofNat n ≤ ofNat m := by
  simp [of_nat] <;> cases Nat.decidableEq n 0 <;> cases Nat.decidableEq m 0 <;> simp only [to_bool]
  · subst m
    have h := le_antisymm h (Nat.zero_le _)
    contradiction
    
  · left
    rfl
    

theorem to_nat_le_to_nat {b₀ b₁ : Bool} (h : b₀ ≤ b₁) : toNat b₀ ≤ toNat b₁ := by
  cases h <;> subst h <;> [cases b₁, cases b₀] <;> simp [to_nat, Nat.zero_le]

theorem of_nat_to_nat (b : Bool) : ofNat (toNat b) = b := by cases b <;> simp only [of_nat, to_nat] <;> exact by decide

@[simp]
theorem injective_iff {α : Sort _} {f : Bool → α} : Function.Injective f ↔ f false ≠ f true :=
  ⟨fun Hinj Heq => ff_ne_tt (Hinj Heq), fun H x y hxy => by
    cases x <;> cases y
    exacts[rfl, (H hxy).elim, (H hxy.symm).elim, rfl]⟩

/-- **Kaminski's Equation** -/
theorem apply_apply_apply (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x := by
  cases x <;> cases h₁ : f tt <;> cases h₂ : f ff <;> simp only [h₁, h₂]

end Bool

