import Mathbin.Order.WellFounded 
import Mathbin.Algebra.Group.Pi 
import Mathbin.Order.MinMax

/-!
# Lexicographic order on Pi types

This file defines the lexicographic relation for Pi types of partial orders and linear orders. We
also provide a `pilex` analog of `pi.ordered_comm_group` (see `algebra.order.pi`).
-/


variable {ι : Type _} {β : ι → Type _} (r : ι → ι → Prop) (s : ∀ {i}, β i → β i → Prop)

/-- The lexicographic relation on `Π i : ι, β i`, where `ι` is ordered by `r`,
  and each `β i` is ordered by `s`. -/
def Pi.Lex (x y : ∀ i, β i) : Prop :=
  ∃ i, (∀ j, r j i → x j = y j) ∧ s (x i) (y i)

/-- The cartesian product of an indexed family, equipped with the lexicographic order. -/
def Pilex (α : Type _) (β : α → Type _) : Type _ :=
  ∀ a, β a

instance [LT ι] [∀ a, LT (β a)] : LT (Pilex ι β) :=
  { lt := Pi.Lex (· < ·) fun _ => · < · }

instance [∀ a, Inhabited (β a)] : Inhabited (Pilex ι β) :=
  by 
    unfold Pilex <;> infer_instance

instance Pilex.is_strict_order [LinearOrderₓ ι] [∀ a, PartialOrderₓ (β a)] : IsStrictOrder (Pilex ι β) (· < ·) :=
  { irrefl := fun a ⟨k, hk₁, hk₂⟩ => lt_irreflₓ (a k) hk₂,
    trans :=
      by 
        rintro a b c ⟨N₁, lt_N₁, a_lt_b⟩ ⟨N₂, lt_N₂, b_lt_c⟩
        rcases lt_trichotomyₓ N₁ N₂ with (H | rfl | H)
        exacts[⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _$ hj.trans H), lt_N₂ _ H ▸ a_lt_b⟩,
          ⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _ hj), a_lt_b.trans b_lt_c⟩,
          ⟨N₂, fun j hj => (lt_N₁ _ (hj.trans H)).trans (lt_N₂ _ hj), (lt_N₁ _ H).symm ▸ b_lt_c⟩] }

instance [LinearOrderₓ ι] [∀ a, PartialOrderₓ (β a)] : PartialOrderₓ (Pilex ι β) :=
  partialOrderOfSO (· < ·)

-- error in Order.Pilex: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem pilex.is_strict_total_order'
[linear_order ι]
(wf : well_founded ((«expr < ») : ι → ι → exprProp()))
[∀ a, linear_order (β a)] : is_strict_total_order' (pilex ι β) ((«expr < »)) :=
{ trichotomous := λ a b, begin
    by_cases [expr h, ":", expr «expr∃ , »((i), «expr ≠ »(a i, b i))],
    { let [ident i] [] [":=", expr wf.min _ h],
      have [ident hlt_i] [":", expr ∀ j «expr < » i, «expr = »(a j, b j)] [],
      { intro [ident j],
        rw ["<-", expr not_imp_not] [],
        exact [expr λ h', wf.not_lt_min _ _ h'] },
      have [] [":", expr «expr ≠ »(a i, b i)] [],
      from [expr wf.min_mem _ h],
      exact [expr this.lt_or_lt.imp (λ h, ⟨i, hlt_i, h⟩) (λ h, or.inr ⟨i, λ j hj, (hlt_i j hj).symm, h⟩)] },
    { push_neg ["at", ident h],
      exact [expr or.inr (or.inl (funext h))] }
  end }

/-- `pilex` is a linear order if the original order is well-founded.
This cannot be an instance, since it depends on the well-foundedness of `<`. -/
protected noncomputable def Pilex.linearOrder [LinearOrderₓ ι] (wf : WellFounded (· < · : ι → ι → Prop))
  [∀ a, LinearOrderₓ (β a)] : LinearOrderₓ (Pilex ι β) :=
  @linearOrderOfSTO' (Pilex ι β) (· < ·) (Pilex.is_strict_total_order' wf) (Classical.decRel _)

-- error in Order.Pilex: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem pilex.le_of_forall_le
[linear_order ι]
(wf : well_founded ((«expr < ») : ι → ι → exprProp()))
[∀ a, linear_order (β a)]
{a b : pilex ι β}
(h : ∀ i, «expr ≤ »(a i, b i)) : «expr ≤ »(a, b) :=
begin
  letI [] [":", expr linear_order (pilex ι β)] [":=", expr pilex.linear_order wf],
  exact [expr le_of_not_lt (λ ⟨i, hi⟩, (h i).not_lt hi.2)]
end

@[toAdditive]
instance [LinearOrderₓ ι] [∀ a, OrderedCommGroup (β a)] : OrderedCommGroup (Pilex ι β) :=
  { Pilex.partialOrder, Pi.commGroup with
    mul_le_mul_left :=
      fun x y hxy z =>
        hxy.elim (fun hxyz => hxyz ▸ le_reflₓ _)
          fun ⟨i, hi⟩ =>
            Or.inr
              ⟨i,
                fun j hji =>
                  show (z j*x j) = z j*y j by 
                    rw [hi.1 j hji],
                mul_lt_mul_left' hi.2 _⟩ }

