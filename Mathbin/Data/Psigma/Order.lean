/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Minchao Wu
-/
import Mathbin.Data.Sigma.Lex
import Mathbin.Order.Synonym

/-!
# Lexicographic order on a sigma type

This file defines the lexicographic order on `Σₗ' i, α i`. `a` is less than `b` if its summand is
strictly less than the summand of `b` or they are in the same summand and `a` is less than `b`
there.

## Notation

* `Σₗ' i, α i`: Sigma type equipped with the lexicographic order. A type synonym of `Σ' i, α i`.

## See also

Related files are:
* `data.finset.colex`: Colexicographic order on finite sets.
* `data.list.lex`: Lexicographic order on lists.
* `data.pi.lex`: Lexicographic order on `Πₗ i, α i`.
* `data.sigma.order`: Lexicographic order on `Σₗ i, α i`. Basically a twin of this file.
* `data.prod.lex`: Lexicographic order on `α × β`.

## TODO

Define the disjoint order on `Σ' i, α i`, where `x ≤ y` only if `x.fst = y.fst`.

Prove that a sigma type is a `no_max_order`, `no_min_order`, `densely_ordered` when its summands
are.
-/


variable {ι : Type _} {α : ι → Type _}

namespace PSigma

-- mathport name: «exprΣₗ' , »
notation3"Σₗ' "(...)", "r:(scoped p => Lex PSigma p) => r

/-- The lexicographical `≤` on a sigma type. -/
instance Lex.hasLe [LT ι] [∀ i, LE (α i)] : LE (Σₗ' i, α i) where le := Lex (· < ·) fun i => (· ≤ ·)

/-- The lexicographical `<` on a sigma type. -/
instance Lex.hasLt [LT ι] [∀ i, LT (α i)] : LT (Σₗ' i, α i) where lt := Lex (· < ·) fun i => (· < ·)

instance Lex.preorder [Preorder ι] [∀ i, Preorder (α i)] : Preorder (Σₗ' i, α i) :=
  { Lex.hasLe, Lex.hasLt with le_refl := fun ⟨i, a⟩ => Lex.right _ le_rfl,
    le_trans := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨a₃, b₃⟩ ⟨h₁r⟩ ⟨h₂r⟩
      · left
        apply lt_trans
        repeat' assumption
        
      · left
        assumption
        
      · left
        assumption
        
      · right
        apply le_trans
        repeat' assumption
        ,
    lt_iff_le_not_le := by
      refine' fun a b => ⟨fun hab => ⟨hab.mono_right fun i a b => le_of_lt, _⟩, _⟩
      · rintro (⟨i, a, hji⟩ | ⟨i, hba⟩) <;> obtain ⟨_, _, hij⟩ | ⟨_, hab⟩ := hab
        · exact hij.not_lt hji
          
        · exact lt_irrefl _ hji
          
        · exact lt_irrefl _ hij
          
        · exact hab.not_le hba
          
        
      · rintro ⟨⟨j, b, hij⟩ | ⟨i, hab⟩, hba⟩
        · exact lex.left _ _ hij
          
        · exact lex.right _ (hab.lt_of_not_le fun h => hba <| lex.right _ h)
          
         }

/-- Dictionary / lexicographic partial_order for dependent pairs. -/
instance Lex.partialOrder [PartialOrder ι] [∀ i, PartialOrder (α i)] : PartialOrder (Σₗ' i, α i) :=
  { Lex.preorder with
    le_antisymm := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (⟨_, _, hlt₁⟩ | ⟨_, hlt₁⟩) (⟨_, _, hlt₂⟩ | ⟨_, hlt₂⟩)
      · exact (lt_irrefl a₁ <| hlt₁.trans hlt₂).elim
        
      · exact (lt_irrefl a₁ hlt₁).elim
        
      · exact (lt_irrefl a₁ hlt₂).elim
        
      · rw [hlt₁.antisymm hlt₂]
         }

/-- Dictionary / lexicographic linear_order for pairs. -/
instance Lex.linearOrder [LinearOrder ι] [∀ i, LinearOrder (α i)] : LinearOrder (Σₗ' i, α i) :=
  { Lex.partialOrder with
    le_total := by
      rintro ⟨i, a⟩ ⟨j, b⟩
      obtain hij | rfl | hji := lt_trichotomy i j
      · exact Or.inl (lex.left _ _ hij)
        
      · obtain hab | hba := le_total a b
        · exact Or.inl (lex.right _ hab)
          
        · exact Or.inr (lex.right _ hba)
          
        
      · exact Or.inr (lex.left _ _ hji)
        ,
    DecidableEq := PSigma.decidableEq, decidableLe := Lex.decidable _ _, decidableLt := Lex.decidable _ _ }

end PSigma

