import Mathbin.Data.Sigma.Lex
import Mathbin.Order.BoundedOrder

/-!
# Orders on a sigma type

This file defines two orders on a sigma type:
* The disjoint sum of orders. `a` is less `b` iff `a` and `b` are in the same summand and `a` is
  less than `b` there.
* The lexicographical order. `a` is less than `b` if its summand is strictly less than the summand
  of `b` or they are in the same summand and `a` is less than `b` there.

## Implementation notes

We declare the disjoint sum of orders as the default instances. The lexicographical order can
override it in local by opening locale `lex`.
-/


namespace Sigma

variable {ι : Type _} {α : ι → Type _}

/-! ### Disjoint sum of orders on `sigma` -/


/-- Disjoint sum of orders. `⟨i, a⟩ ≤ ⟨j, b⟩` iff `i = j` and `a ≤ b`. -/
inductive le [∀ i, LE (α i)] : ∀ a b : Σ i, α i, Prop
  | fiber (i : ι) (a b : α i) : a ≤ b → le ⟨i, a⟩ ⟨i, b⟩

instance [∀ i, LE (α i)] : LE (Σ i, α i) :=
  ⟨le⟩

instance [∀ i, Preorderₓ (α i)] : Preorderₓ (Σ i, α i) :=
  { Sigma.hasLe with le_refl := fun ⟨i, a⟩ => le.fiber i a a le_rfl,
    le_trans := by
      rintro _ _ _ ⟨i, a, b, hab⟩ ⟨_, _, c, hbc⟩
      exact le.fiber i a c (hab.trans hbc) }

instance [∀ i, PartialOrderₓ (α i)] : PartialOrderₓ (Σ i, α i) :=
  { Sigma.preorder with
    le_antisymm := by
      rintro _ _ ⟨i, a, b, hab⟩ ⟨_, _, _, hba⟩
      exact ext rfl (heq_of_eq $ hab.antisymm hba) }

/-! ### Lexicographical order on `sigma` -/


namespace Lex

localized [Lex] attribute [-instance] Sigma.hasLe

localized [Lex] attribute [-instance] Sigma.preorder

localized [Lex] attribute [-instance] Sigma.partialOrder

/-- The lexicographical `≤` on a sigma type. Turn this on by opening locale `lex`. -/
protected def LE [LT ι] [∀ i, LE (α i)] : LE (Σ i, α i) :=
  ⟨lex (· < ·) fun i => · ≤ ·⟩

/-- The lexicographical `<` on a sigma type. Turn this on by opening locale `lex`. -/
protected def LT [LT ι] [∀ i, LT (α i)] : LT (Σ i, α i) :=
  ⟨lex (· < ·) fun i => · < ·⟩

localized [Lex] attribute [instance] Sigma.Lex.hasLe

localized [Lex] attribute [instance] Sigma.Lex.hasLt

/-- The lexicographical preorder on a sigma type. Turn this on by opening locale `lex`. -/
protected def Preorderₓ [Preorderₓ ι] [∀ i, Preorderₓ (α i)] : Preorderₓ (Σ i, α i) :=
  { lex.has_le, lex.has_lt with le_refl := fun ⟨i, a⟩ => lex.right a a le_rfl, le_trans := fun _ _ _ => trans,
    lt_iff_le_not_le := by
      refine' fun a b => ⟨fun hab => ⟨hab.mono_right fun i a b => le_of_ltₓ, _⟩, _⟩
      · rintro (⟨j, i, b, a, hji⟩ | ⟨i, b, a, hba⟩) <;> obtain ⟨_, _, _, _, hij⟩ | ⟨_, _, _, hab⟩ := hab
        · exact hij.not_lt hji
          
        · exact lt_irreflₓ _ hji
          
        · exact lt_irreflₓ _ hij
          
        · exact hab.not_le hba
          
        
      · rintro ⟨⟨i, j, a, b, hij⟩ | ⟨i, a, b, hab⟩, hba⟩
        · exact lex.left _ _ hij
          
        · exact lex.right _ _ (hab.lt_of_not_le $ fun h => hba $ lex.right _ _ h)
          
         }

localized [Lex] attribute [instance] Sigma.Lex.preorder

/-- The lexicographical partial order on a sigma type. Turn this on by opening locale `lex`. -/
protected def PartialOrderₓ [Preorderₓ ι] [∀ i, PartialOrderₓ (α i)] : PartialOrderₓ (Σ i, α i) :=
  { lex.preorder with le_antisymm := fun _ _ => antisymm }

localized [Lex] attribute [instance] Sigma.Lex.partialOrder

/-- The lexicographical linear order on a sigma type. Turn this on by opening locale `lex`. -/
protected def LinearOrderₓ [LinearOrderₓ ι] [∀ i, LinearOrderₓ (α i)] : LinearOrderₓ (Σ i, α i) :=
  { lex.partial_order with le_total := total_of _, DecidableEq := Sigma.decidableEq, decidableLe := lex.decidable _ _ }

localized [Lex] attribute [instance] Sigma.Lex.linearOrder

/-- The lexicographical linear order on a sigma type. Turn this on by opening locale `lex`. -/
protected def OrderBot [PartialOrderₓ ι] [OrderBot ι] [∀ i, Preorderₓ (α i)] [OrderBot (α ⊥)] :
    OrderBot (Σ i, α i) where
  bot := ⟨⊥, ⊥⟩
  bot_le := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_bot_or_bot_lt a
    · exact lex.right _ _ bot_le
      
    · exact lex.left _ _ ha
      

localized [Lex] attribute [instance] Sigma.Lex.orderBot

/-- The lexicographical linear order on a sigma type. Turn this on by opening locale `lex`. -/
protected def OrderTop [PartialOrderₓ ι] [OrderTop ι] [∀ i, Preorderₓ (α i)] [OrderTop (α ⊤)] :
    OrderTop (Σ i, α i) where
  top := ⟨⊤, ⊤⟩
  le_top := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_top_or_lt_top a
    · exact lex.right _ _ le_top
      
    · exact lex.left _ _ ha
      

localized [Lex] attribute [instance] Sigma.Lex.orderTop

/-- The lexicographical linear order on a sigma type. Turn this on by opening locale `lex`. -/
protected def BoundedOrder [PartialOrderₓ ι] [BoundedOrder ι] [∀ i, Preorderₓ (α i)] [OrderBot (α ⊥)] [OrderTop (α ⊤)] :
    BoundedOrder (Σ i, α i) :=
  { lex.order_bot, lex.order_top with }

localized [Lex] attribute [instance] Sigma.Lex.boundedOrder

end Lex

end Sigma

