/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Bryan Gin-ge Chen
-/
import Mathbin.Order.BooleanAlgebra

/-!
# Symmetric difference

The symmetric difference or disjunctive union of sets `A` and `B` is the set of elements that are
in either `A` or `B` but not both. Translated into propositions, the symmetric difference is `xor`.

The symmetric difference operator (`symm_diff`) is defined in this file for any type with `⊔` and
`\` via the formula `(A \ B) ⊔ (B \ A)`, however the theorems proved about it only hold for
`generalized_boolean_algebra`s and `boolean_algebra`s.

The symmetric difference is the addition operator in the Boolean ring structure on Boolean algebras.

## Main declarations

* `symm_diff`: the symmetric difference operator, defined as `(A \ B) ⊔ (B \ A)`

In generalized Boolean algebras, the symmetric difference operator is:

* `symm_diff_comm`: commutative, and
* `symm_diff_assoc`: associative.

## Notations

* `a Δ b`: `symm_diff a b`

## References

The proof of associativity follows the note "Associativity of the Symmetric Difference of Sets: A
Proof from the Book" by John McCuan:

* <https://people.math.gatech.edu/~mccuan/courses/4317/symmetricdifference.pdf>

## Tags
boolean ring, generalized boolean algebra, boolean algebra, symmetric differences
-/


/-- The symmetric difference operator on a type with `⊔` and `\` is `(A \ B) ⊔ (B \ A)`. -/
def symmDiff {α : Type _} [HasSup α] [HasSdiff α] (A B : α) : α :=
  A \ B⊔B \ A

-- mathport name: «expr Δ »
infixl:100 " Δ " => symmDiff

theorem symm_diff_def {α : Type _} [HasSup α] [HasSdiff α] (A B : α) : A Δ B = A \ B⊔B \ A :=
  rfl

theorem symm_diff_eq_xor (p q : Prop) : p Δ q = Xorₓ p q :=
  rfl

section GeneralizedBooleanAlgebra

variable {α : Type _} [GeneralizedBooleanAlgebra α] (a b c : α)

theorem symm_diff_comm : a Δ b = b Δ a := by
  simp only [(· Δ ·), sup_comm]

instance symm_diff_is_comm : IsCommutative α (· Δ ·) :=
  ⟨symm_diff_comm⟩

@[simp]
theorem symm_diff_self : a Δ a = ⊥ := by
  rw [(· Δ ·), sup_idem, sdiff_self]

@[simp]
theorem symm_diff_bot : a Δ ⊥ = a := by
  rw [(· Δ ·), sdiff_bot, bot_sdiff, sup_bot_eq]

@[simp]
theorem bot_symm_diff : ⊥ Δ a = a := by
  rw [symm_diff_comm, symm_diff_bot]

theorem symm_diff_eq_sup_sdiff_inf : a Δ b = (a⊔b) \ (a⊓b) := by
  simp [sup_sdiff, sdiff_inf, sup_comm, (· Δ ·)]

theorem disjoint_symm_diff_inf : Disjoint (a Δ b) (a⊓b) := by
  rw [symm_diff_eq_sup_sdiff_inf]
  exact disjoint_sdiff_self_left

theorem symm_diff_le_sup : a Δ b ≤ a⊔b := by
  rw [symm_diff_eq_sup_sdiff_inf]
  exact sdiff_le

theorem sdiff_symm_diff : c \ a Δ b = c⊓a⊓b⊔c \ a⊓c \ b := by
  simp only [(· Δ ·), sdiff_sdiff_sup_sdiff']

theorem sdiff_symm_diff' : c \ a Δ b = c⊓a⊓b⊔c \ (a⊔b) := by
  rw [sdiff_symm_diff, sdiff_sup, sup_comm]

theorem symm_diff_sdiff : a Δ b \ c = a \ (b⊔c)⊔b \ (a⊔c) := by
  rw [symm_diff_def, sup_sdiff, sdiff_sdiff_left, sdiff_sdiff_left]

@[simp]
theorem symm_diff_sdiff_left : a Δ b \ a = b \ a := by
  rw [symm_diff_def, sup_sdiff, sdiff_idem, sdiff_sdiff_self, bot_sup_eq]

@[simp]
theorem symm_diff_sdiff_right : a Δ b \ b = a \ b := by
  rw [symm_diff_comm, symm_diff_sdiff_left]

@[simp]
theorem sdiff_symm_diff_self : a \ a Δ b = a⊓b := by
  simp [sdiff_symm_diff]

theorem symm_diff_eq_iff_sdiff_eq {a b c : α} (ha : a ≤ c) : a Δ b = c ↔ c \ a = b := by
  constructor <;> intro h
  · have hba : Disjoint (a⊓b) c := by
      rw [← h, Disjoint.comm]
      exact disjoint_symm_diff_inf _ _
    have hca : _ := congr_argₓ (· \ a) h
    rw [symm_diff_sdiff_left] at hca
    rw [← hca, sdiff_eq_self_iff_disjoint]
    exact hba.of_disjoint_inf_of_le ha
    
  · have hd : Disjoint a b := by
      rw [← h]
      exact disjoint_sdiff_self_right
    rw [symm_diff_def, hd.sdiff_eq_left, hd.sdiff_eq_right, ← h, sup_sdiff_cancel_right ha]
    

theorem Disjoint.symm_diff_eq_sup {a b : α} (h : Disjoint a b) : a Δ b = a⊔b := by
  rw [(· Δ ·), h.sdiff_eq_left, h.sdiff_eq_right]

theorem symm_diff_eq_sup : a Δ b = a⊔b ↔ Disjoint a b := by
  constructor <;> intro h
  · rw [symm_diff_eq_sup_sdiff_inf, sdiff_eq_self_iff_disjoint] at h
    exact h.of_disjoint_inf_of_le le_sup_left
    
  · exact h.symm_diff_eq_sup
    

theorem symm_diff_symm_diff_left : a Δ b Δ c = a \ (b⊔c)⊔b \ (a⊔c)⊔c \ (a⊔b)⊔a⊓b⊓c :=
  calc
    a Δ b Δ c = a Δ b \ c⊔c \ a Δ b := symm_diff_def _ _
    _ = a \ (b⊔c)⊔b \ (a⊔c)⊔(c \ (a⊔b)⊔c⊓a⊓b) := by
      rw [sdiff_symm_diff', @sup_comm _ _ (c⊓a⊓b), symm_diff_sdiff]
    _ = a \ (b⊔c)⊔b \ (a⊔c)⊔c \ (a⊔b)⊔a⊓b⊓c := by
      ac_rfl
    

theorem symm_diff_symm_diff_right : a Δ (b Δ c) = a \ (b⊔c)⊔b \ (a⊔c)⊔c \ (a⊔b)⊔a⊓b⊓c :=
  calc
    a Δ (b Δ c) = a \ b Δ c⊔b Δ c \ a := symm_diff_def _ _
    _ = a \ (b⊔c)⊔a⊓b⊓c⊔(b \ (c⊔a)⊔c \ (b⊔a)) := by
      rw [sdiff_symm_diff', @sup_comm _ _ (a⊓b⊓c), symm_diff_sdiff]
    _ = a \ (b⊔c)⊔b \ (a⊔c)⊔c \ (a⊔b)⊔a⊓b⊓c := by
      ac_rfl
    

theorem symm_diff_assoc : a Δ b Δ c = a Δ (b Δ c) := by
  rw [symm_diff_symm_diff_left, symm_diff_symm_diff_right]

instance symm_diff_is_assoc : IsAssociative α (· Δ ·) :=
  ⟨symm_diff_assoc⟩

@[simp]
theorem symm_diff_symm_diff_self : a Δ (a Δ b) = b := by
  simp [← symm_diff_assoc]

@[simp]
theorem symm_diff_symm_diff_self' : a Δ b Δ a = b := by
  rw [symm_diff_comm, ← symm_diff_assoc, symm_diff_self, bot_symm_diff]

@[simp]
theorem symm_diff_right_inj : a Δ b = a Δ c ↔ b = c := by
  constructor <;> intro h
  · have H1 := congr_argₓ ((· Δ ·) a) h
    rwa [symm_diff_symm_diff_self, symm_diff_symm_diff_self] at H1
    
  · rw [h]
    

@[simp]
theorem symm_diff_left_inj : a Δ b = c Δ b ↔ a = c := by
  rw [symm_diff_comm a b, symm_diff_comm c b, symm_diff_right_inj]

@[simp]
theorem symm_diff_eq_left : a Δ b = a ↔ b = ⊥ :=
  calc
    a Δ b = a ↔ a Δ b = a Δ ⊥ := by
      rw [symm_diff_bot]
    _ ↔ b = ⊥ := by
      rw [symm_diff_right_inj]
    

@[simp]
theorem symm_diff_eq_right : a Δ b = b ↔ a = ⊥ := by
  rw [symm_diff_comm, symm_diff_eq_left]

@[simp]
theorem symm_diff_eq_bot : a Δ b = ⊥ ↔ a = b :=
  calc
    a Δ b = ⊥ ↔ a Δ b = a Δ a := by
      rw [symm_diff_self]
    _ ↔ a = b := by
      rw [symm_diff_right_inj, eq_comm]
    

theorem Disjoint.disjoint_symm_diff_of_disjoint {a b c : α} (ha : Disjoint a c) (hb : Disjoint b c) :
    Disjoint (a Δ b) c := by
  rw [symm_diff_eq_sup_sdiff_inf]
  exact (ha.sup_left hb).disjoint_sdiff_left

end GeneralizedBooleanAlgebra

section BooleanAlgebra

variable {α : Type _} [BooleanAlgebra α] (a b c : α)

theorem symm_diff_eq : a Δ b = a⊓bᶜ⊔b⊓aᶜ := by
  simp only [(· Δ ·), sdiff_eq]

@[simp]
theorem symm_diff_top : a Δ ⊤ = aᶜ := by
  simp [symm_diff_eq]

@[simp]
theorem top_symm_diff : ⊤ Δ a = aᶜ := by
  rw [symm_diff_comm, symm_diff_top]

theorem compl_symm_diff : (a Δ b)ᶜ = a⊓b⊔aᶜ⊓bᶜ := by
  simp only [← top_sdiff, sdiff_symm_diff, top_inf_eq]

theorem symm_diff_eq_top_iff : a Δ b = ⊤ ↔ IsCompl a b := by
  rw [symm_diff_eq_iff_sdiff_eq le_top, top_sdiff, compl_eq_iff_is_compl]

theorem IsCompl.symm_diff_eq_top (h : IsCompl a b) : a Δ b = ⊤ :=
  (symm_diff_eq_top_iff a b).2 h

@[simp]
theorem compl_symm_diff_self : aᶜ Δ a = ⊤ := by
  simp only [symm_diff_eq, compl_compl, inf_idem, compl_sup_eq_top]

@[simp]
theorem symm_diff_compl_self : a Δ aᶜ = ⊤ := by
  rw [symm_diff_comm, compl_symm_diff_self]

theorem symm_diff_symm_diff_right' : a Δ (b Δ c) = a⊓b⊓c⊔a⊓bᶜ⊓cᶜ⊔aᶜ⊓b⊓cᶜ⊔aᶜ⊓bᶜ⊓c :=
  calc
    a Δ (b Δ c) = a⊓(b⊓c⊔bᶜ⊓cᶜ)⊔(b⊓cᶜ⊔c⊓bᶜ)⊓aᶜ := by
      rw [symm_diff_eq, compl_symm_diff, symm_diff_eq]
    _ = a⊓b⊓c⊔a⊓bᶜ⊓cᶜ⊔b⊓cᶜ⊓aᶜ⊔c⊓bᶜ⊓aᶜ := by
      rw [inf_sup_left, inf_sup_right, ← sup_assoc, ← inf_assoc, ← inf_assoc]
    _ = a⊓b⊓c⊔a⊓bᶜ⊓cᶜ⊔aᶜ⊓b⊓cᶜ⊔aᶜ⊓bᶜ⊓c := by
      congr 1
      · congr 1
        rw [inf_comm, inf_assoc]
        
      · apply inf_left_right_swap
        
    

end BooleanAlgebra

