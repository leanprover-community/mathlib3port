
/-!
# booleans

This file proves various trivial lemmas about booleans and their
relation to decidable propositions.

## Notations

This file introduces the notation `!b` for `bnot b`, the boolean "not".

## Tags
bool, boolean, De Morgan
-/


prefix:90 "!" => bnot

namespace Bool

theorem coe_sort_tt : coeSort.{1, 1} tt = True :=
  coe_sort_tt

theorem coe_sort_ff : coeSort.{1, 1} ff = False :=
  coe_sort_ff

theorem to_bool_true {h} : @to_bool True h = tt :=
  to_bool_true_eq_tt h

theorem to_bool_false {h} : @to_bool False h = ff :=
  to_bool_false_eq_ff h

@[simp]
theorem to_bool_coe (b : Bool) {h} : @to_bool b h = b :=
  show _ = to_bool b by
        congr.trans
    (by
      cases b <;> rfl)

theorem coe_to_bool (p : Prop) [Decidable p] : to_bool p ↔ p :=
  to_bool_iff _

@[simp]
theorem of_to_bool_iff {p : Prop} [Decidable p] : to_bool p ↔ p :=
  ⟨of_to_bool_true, _root_.to_bool_true⟩

@[simp]
theorem tt_eq_to_bool_iff {p : Prop} [Decidable p] : tt = to_bool p ↔ p :=
  eq_comm.trans of_to_bool_iff

@[simp]
theorem ff_eq_to_bool_iff {p : Prop} [Decidable p] : ff = to_bool p ↔ ¬p :=
  eq_comm.trans (to_bool_ff_iff _)

@[simp]
theorem to_bool_not (p : Prop) [Decidable p] : (to_bool ¬p) = bnot (to_bool p) := by
  by_cases' p <;> simp [*]

@[simp]
theorem to_bool_and (p q : Prop) [Decidable p] [Decidable q] : to_bool (p ∧ q) = (p && q) := by
  by_cases' p <;> by_cases' q <;> simp [*]

@[simp]
theorem to_bool_or (p q : Prop) [Decidable p] [Decidable q] : to_bool (p ∨ q) = (p || q) := by
  by_cases' p <;> by_cases' q <;> simp [*]

@[simp]
theorem to_bool_eq {p q : Prop} [Decidable p] [Decidable q] : to_bool p = to_bool q ↔ (p ↔ q) :=
  ⟨fun h =>
    (coe_to_bool p).symm.trans <| by
      simp [h],
    to_bool_congr⟩

theorem not_ff : ¬ff :=
  ff_ne_tt

@[simp]
theorem default_bool : default = ff :=
  rfl

theorem dichotomy (b : Bool) : b = ff ∨ b = tt := by
  cases b <;> simp

@[simp]
theorem forall_bool {p : Bool → Prop} : (∀ b, p b) ↔ p ff ∧ p tt :=
  ⟨fun h => by
    simp [h], fun ⟨h₁, h₂⟩ b => by
    cases b <;> assumption⟩

@[simp]
theorem exists_bool {p : Bool → Prop} : (∃ b, p b) ↔ p ff ∨ p tt :=
  ⟨fun ⟨b, h⟩ => by
    cases b <;> [exact Or.inl h, exact Or.inr h], fun h => by
    cases h <;> exact ⟨_, h⟩⟩

/-- If `p b` is decidable for all `b : bool`, then `∀ b, p b` is decidable -/
instance decidable_forall_bool {p : Bool → Prop} [∀ b, Decidable (p b)] : Decidable (∀ b, p b) :=
  decidableOfDecidableOfIff And.decidable forall_bool.symm

/-- If `p b` is decidable for all `b : bool`, then `∃ b, p b` is decidable -/
instance decidable_exists_bool {p : Bool → Prop} [∀ b, Decidable (p b)] : Decidable (∃ b, p b) :=
  decidableOfDecidableOfIff Or.decidable exists_bool.symm

@[simp]
theorem cond_ff {α} (t e : α) : cond ff t e = e :=
  rfl

@[simp]
theorem cond_tt {α} (t e : α) : cond tt t e = t :=
  rfl

@[simp]
theorem cond_to_bool {α} (p : Prop) [Decidable p] (t e : α) : cond (to_bool p) t e = if p then t else e := by
  by_cases' p <;> simp [*]

@[simp]
theorem cond_bnot {α} (b : Bool) (t e : α) : cond (!b) t e = cond b e t := by
  cases b <;> rfl

theorem coe_bool_iff : ∀ {a b : Bool}, (a ↔ b) ↔ a = b := by
  decide

theorem eq_tt_of_ne_ff : ∀ {a : Bool}, a ≠ ff → a = tt := by
  decide

theorem eq_ff_of_ne_tt : ∀ {a : Bool}, a ≠ tt → a = ff := by
  decide

theorem bor_comm : ∀ a b, (a || b) = (b || a) := by
  decide

@[simp]
theorem bor_assoc : ∀ a b c, (a || b || c) = (a || (b || c)) := by
  decide

theorem bor_left_comm : ∀ a b c, (a || (b || c)) = (b || (a || c)) := by
  decide

theorem bor_inl {a b : Bool} (H : a) : a || b := by
  simp [H]

theorem bor_inr {a b : Bool} (H : b) : a || b := by
  simp [H]

theorem band_comm : ∀ a b, (a && b) = (b && a) := by
  decide

@[simp]
theorem band_assoc : ∀ a b c, (a && b && c) = (a && (b && c)) := by
  decide

theorem band_left_comm : ∀ a b c, (a && (b && c)) = (b && (a && c)) := by
  decide

theorem band_elim_left : ∀ {a b : Bool}, a && b → a := by
  decide

theorem band_intro : ∀ {a b : Bool}, a → b → a && b := by
  decide

theorem band_elim_right : ∀ {a b : Bool}, a && b → b := by
  decide

@[simp]
theorem bnot_false : bnot ff = tt :=
  rfl

@[simp]
theorem bnot_true : bnot tt = ff :=
  rfl

@[simp]
theorem bnot_iff_not : ∀ {b : Bool}, !b ↔ ¬b := by
  decide

theorem eq_tt_of_bnot_eq_ff : ∀ {a : Bool}, bnot a = ff → a = tt := by
  decide

theorem eq_ff_of_bnot_eq_tt : ∀ {a : Bool}, bnot a = tt → a = ff := by
  decide

theorem bxor_comm : ∀ a b, bxor a b = bxor b a := by
  decide

@[simp]
theorem bxor_assoc : ∀ a b c, bxor (bxor a b) c = bxor a (bxor b c) := by
  decide

theorem bxor_left_comm : ∀ a b c, bxor a (bxor b c) = bxor b (bxor a c) := by
  decide

@[simp]
theorem bxor_bnot_left : ∀ a, bxor (!a) a = tt := by
  decide

@[simp]
theorem bxor_bnot_right : ∀ a, bxor a (!a) = tt := by
  decide

@[simp]
theorem bxor_bnot_bnot : ∀ a b, bxor (!a) (!b) = bxor a b := by
  decide

@[simp]
theorem bxor_ff_left : ∀ a, bxor ff a = a := by
  decide

@[simp]
theorem bxor_ff_right : ∀ a, bxor a ff = a := by
  decide

theorem bxor_iff_ne : ∀ {x y : Bool}, bxor x y = tt ↔ x ≠ y := by
  decide

/-! ### De Morgan's laws for booleans-/


@[simp]
theorem bnot_band : ∀ a b : Bool, !(a && b) = (!a || !b) := by
  decide

@[simp]
theorem bnot_bor : ∀ a b : Bool, !(a || b) = (!a && !b) := by
  decide

theorem bnot_inj : ∀ {a b : Bool}, !a = !b → a = b := by
  decide

instance : LinearOrderₓ Bool where
  le := fun a b => a = ff ∨ b = tt
  le_refl := by
    decide
  le_trans := by
    decide
  le_antisymm := by
    decide
  le_total := by
    decide
  decidableLe := inferInstance
  DecidableEq := inferInstance
  decidableLt := inferInstance
  max := bor
  max_def := by
    funext x y
    revert x y
    exact by
      decide
  min := band
  min_def := by
    funext x y
    revert x y
    exact by
      decide

@[simp]
theorem ff_le {x : Bool} : ff ≤ x :=
  Or.intro_left _ rfl

@[simp]
theorem le_tt {x : Bool} : x ≤ tt :=
  Or.intro_rightₓ _ rfl

theorem lt_iff : ∀ {x y : Bool}, x < y ↔ x = ff ∧ y = tt := by
  decide

@[simp]
theorem ff_lt_tt : ff < tt :=
  lt_iff.2 ⟨rfl, rfl⟩

theorem le_iff_imp : ∀ {x y : Bool}, x ≤ y ↔ x → y := by
  decide

theorem band_le_left : ∀ x y : Bool, (x && y) ≤ x := by
  decide

theorem band_le_right : ∀ x y : Bool, (x && y) ≤ y := by
  decide

theorem le_band : ∀ {x y z : Bool}, x ≤ y → x ≤ z → x ≤ (y && z) := by
  decide

theorem left_le_bor : ∀ x y : Bool, x ≤ (x || y) := by
  decide

theorem right_le_bor : ∀ x y : Bool, y ≤ (x || y) := by
  decide

theorem bor_le : ∀ {x y z}, x ≤ z → y ≤ z → (x || y) ≤ z := by
  decide

/-- convert a `bool` to a `ℕ`, `false -> 0`, `true -> 1` -/
def to_nat (b : Bool) : ℕ :=
  cond b 1 0

/-- convert a `ℕ` to a `bool`, `0 -> false`, everything else -> `true` -/
def of_nat (n : ℕ) : Bool :=
  to_bool (n ≠ 0)

theorem of_nat_le_of_nat {n m : ℕ} (h : n ≤ m) : of_nat n ≤ of_nat m := by
  simp [of_nat] <;> cases Nat.decidableEq n 0 <;> cases Nat.decidableEq m 0 <;> simp only [to_bool]
  · subst m
    have h := le_antisymmₓ h (Nat.zero_leₓ _)
    contradiction
    
  · left
    rfl
    

theorem to_nat_le_to_nat {b₀ b₁ : Bool} (h : b₀ ≤ b₁) : to_nat b₀ ≤ to_nat b₁ := by
  cases h <;> subst h <;> [cases b₁, cases b₀] <;> simp [to_nat, Nat.zero_leₓ]

theorem of_nat_to_nat (b : Bool) : of_nat (to_nat b) = b := by
  cases b <;>
    simp only [of_nat, to_nat] <;>
      exact by
        decide

@[simp]
theorem injective_iff {α : Sort _} {f : Bool → α} : Function.Injective f ↔ f ff ≠ f tt :=
  ⟨fun Hinj Heq => ff_ne_tt (Hinj Heq), fun H x y hxy => by
    cases x <;> cases y
    exacts[rfl, (H hxy).elim, (H hxy.symm).elim, rfl]⟩

end Bool

