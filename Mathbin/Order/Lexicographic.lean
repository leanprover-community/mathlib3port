import Mathbin.Data.Equiv.Basic
import Mathbin.Data.Prod
import Mathbin.Tactic.Basic

/-!
# Lexicographic order

This file defines the lexicographic relation for pairs and dependent pairs of orders, partial orders
and linear orders.

## Main declarations

* `lex α`: A type synonym of `α` to equip it with its lexicographic order.
* `prod.lex.<pre/partial_/linear_>order`: Instances lifting the orders on `α` and `β` to `α ×ₗ β`.

## Notation

* `α ×ₗ β`: `α × β` equipped with the lexicographic order

## See also

Related files are:
* `data.finset.colex`: Colexicographic order on finite sets.
* `data.list.lex`: Lexicographic order on lists.
* `data.psigma.order`: Lexicographic order on `Σ' i, α i`.
* `data.sigma.order`: Lexicographic order on `Σ i, α i`.
-/


universe u v

/-- A type synonym to equip a type with its lexicographic order. -/
def Lex (α : Type u) :=
  α

variable {α : Type u} {β : Type v} {γ : Type _}

/-- `to_lex` is the identity function to the `lex` of a type.  -/
def toLex : α ≃ Lex α :=
  ⟨id, id, fun h => rfl, fun h => rfl⟩

/-- `of_lex` is the identity function from the `lex` of a type.  -/
def ofLex : Lex α ≃ α :=
  toLex.symm

@[simp]
theorem to_lex_symm_eq : (@toLex α).symm = ofLex :=
  rfl

@[simp]
theorem of_lex_symm_eq : (@ofLex α).symm = toLex :=
  rfl

@[simp]
theorem to_lex_of_lex (a : Lex α) : toLex (ofLex a) = a :=
  rfl

@[simp]
theorem of_lex_to_lex (a : α) : ofLex (toLex a) = a :=
  rfl

@[simp]
theorem to_lex_inj {a b : α} : toLex a = toLex b ↔ a = b :=
  Iff.rfl

@[simp]
theorem of_lex_inj {a b : Lex α} : ofLex a = ofLex b ↔ a = b :=
  Iff.rfl

namespace Prod.Lex

notation:35 α " ×ₗ " β:34 => Lex (Prod α β)

unsafe instance [has_to_format α] [has_to_format β] : has_to_format (α ×ₗ β) :=
  prod.has_to_format

instance DecidableEq (α β : Type _) [DecidableEq α] [DecidableEq β] : DecidableEq (α ×ₗ β) :=
  Prod.decidableEq

instance Inhabited (α β : Type _) [Inhabited α] [Inhabited β] : Inhabited (α ×ₗ β) :=
  Prod.inhabited

/-- Dictionary / lexicographic ordering on pairs.  -/
instance LE (α β : Type _) [LT α] [LE β] : LE (α ×ₗ β) where
  le := Prod.Lex (· < ·) (· ≤ ·)

instance LT (α β : Type _) [LT α] [LT β] : LT (α ×ₗ β) where
  lt := Prod.Lex (· < ·) (· < ·)

theorem le_iff [LT α] [LE β] (a b : α ×ₗ β) : a ≤ b ↔ a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2 :=
  Prod.lex_def (· < ·) (· ≤ ·)

theorem lt_iff [LT α] [LT β] (a b : α ×ₗ β) : a < b ↔ a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 < b.2 :=
  Prod.lex_def (· < ·) (· < ·)

/-- Dictionary / lexicographic preorder for pairs. -/
instance Preorderₓ (α β : Type _) [Preorderₓ α] [Preorderₓ β] : Preorderₓ (α ×ₗ β) :=
  { Prod.Lex.hasLe α β, Prod.Lex.hasLt α β with
    le_refl := fun ⟨l, r⟩ => by
      right
      apply le_reflₓ,
    le_trans := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨a₃, b₃⟩ ⟨h₁l, h₁r⟩ ⟨h₂l, h₂r⟩
      · left
        apply lt_transₓ
        repeat'
          assumption
        
      · left
        assumption
        
      · left
        assumption
        
      · right
        apply le_transₓ
        repeat'
          assumption
        ,
    lt_iff_le_not_le := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
      constructor
      · rintro (⟨_, _, _, _, hlt⟩ | ⟨_, _, _, hlt⟩)
        · constructor
          · left
            assumption
            
          · rintro ⟨l, r⟩
            · apply lt_asymmₓ hlt
              assumption
              
            · apply lt_irreflₓ _ hlt
              
            
          
        · constructor
          · right
            rw [lt_iff_le_not_leₓ] at hlt
            exact hlt.1
            
          · rintro ⟨l, r⟩
            · apply lt_irreflₓ a₁
              assumption
              
            · rw [lt_iff_le_not_leₓ] at hlt
              apply hlt.2
              assumption
              
            
          
        
      · rintro ⟨⟨h₁ll, h₁lr⟩, h₂r⟩
        · left
          assumption
          
        · right
          rw [lt_iff_le_not_leₓ]
          constructor
          · assumption
            
          · intro h
            apply h₂r
            right
            exact h
            
          
         }

/-- Dictionary / lexicographic partial_order for pairs. -/
instance PartialOrderₓ (α β : Type _) [PartialOrderₓ α] [PartialOrderₓ β] : PartialOrderₓ (α ×ₗ β) :=
  { Prod.Lex.preorder α β with
    le_antisymm := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (⟨_, _, _, _, hlt₁⟩ | ⟨_, _, _, hlt₁⟩) (⟨_, _, _, _, hlt₂⟩ | ⟨_, _, _, hlt₂⟩)
      · exfalso
        exact lt_irreflₓ a₁ (lt_transₓ hlt₁ hlt₂)
        
      · exfalso
        exact lt_irreflₓ a₁ hlt₁
        
      · exfalso
        exact lt_irreflₓ a₁ hlt₂
        
      · have := le_antisymmₓ hlt₁ hlt₂
        simp [this]
         }

/-- Dictionary / lexicographic linear_order for pairs. -/
instance LinearOrderₓ (α β : Type _) [LinearOrderₓ α] [LinearOrderₓ β] : LinearOrderₓ (α ×ₗ β) :=
  { Prod.Lex.partialOrder α β with
    le_total := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
      obtain ha | ha := le_totalₓ a₁ a₂ <;> cases' lt_or_eq_of_leₓ ha with a_lt a_eq
      · left
        left
        exact a_lt
        
      swap
      · right
        left
        exact a_lt
        
      all_goals
        subst a_eq
        obtain hb | hb := le_totalₓ b₁ b₂
      · left
        right
        exact hb
        
      · right
        right
        exact hb
        
      · left
        right
        exact hb
        
      · right
        right
        exact hb
        ,
    decidableLe := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
      obtain a_lt | a_le := LinearOrderₓ.decidableLe a₁ a₂
      · left
        rw [not_leₓ] at a_lt
        rintro ⟨l, r⟩
        · apply lt_irreflₓ a₂
          apply lt_transₓ
          repeat'
            assumption
          
        · apply lt_irreflₓ a₁
          assumption
          
        
      · by_cases' h : a₁ = a₂
        · rw [h]
          obtain b_lt | b_le := LinearOrderₓ.decidableLe b₁ b₂
          · left
            rw [not_leₓ] at b_lt
            rintro ⟨l, r⟩
            · apply lt_irreflₓ a₂
              assumption
              
            · apply lt_irreflₓ b₂
              apply lt_of_lt_of_leₓ
              repeat'
                assumption
              
            
          · right
            right
            assumption
            
          
        · right
          left
          apply lt_of_le_of_neₓ
          repeat'
            assumption
          
         }

end Prod.Lex

