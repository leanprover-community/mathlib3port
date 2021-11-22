import Mathbin.Algebra.Order.Pi 
import Mathbin.Order.WellFounded 
import Mathbin.Order.MinMax

/-!
# Lexicographic order on Pi types

This file defines the lexicographic relation for Pi types of partial orders and linear orders. We
also provide a `pilex` analog of `pi.ordered_comm_group` (see `algebra.order.pi`).
-/


variable{ι : Type _}{β : ι → Type _}(r : ι → ι → Prop)(s : ∀ {i}, β i → β i → Prop)

/-- The lexicographic relation on `Π i : ι, β i`, where `ι` is ordered by `r`,
  and each `β i` is ordered by `s`. -/
def Pi.Lex (x y : ∀ i, β i) : Prop :=
  ∃ i, (∀ j, r j i → x j = y j) ∧ s (x i) (y i)

/-- The cartesian product of an indexed family, equipped with the lexicographic order. -/
def Pilex (α : Type _) (β : α → Type _) : Type _ :=
  ∀ a, β a

instance  [LT ι] [∀ a, LT (β a)] : LT (Pilex ι β) :=
  { lt := Pi.Lex (· < ·) fun _ => · < · }

instance  [∀ a, Inhabited (β a)] : Inhabited (Pilex ι β) :=
  by 
    unfold Pilex <;> infer_instance

-- error in Order.Pilex: ././Mathport/Syntax/Translate/Basic.lean:340:40: in exacts: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
instance pilex.is_strict_order
[linear_order ι]
[∀ a, partial_order (β a)] : is_strict_order (pilex ι β) ((«expr < »)) :=
{ irrefl := λ (a) ⟨k, hk₁, hk₂⟩, lt_irrefl (a k) hk₂,
  trans := begin
    rintro [ident a, ident b, ident c, "⟨", ident N₁, ",", ident lt_N₁, ",", ident a_lt_b, "⟩", "⟨", ident N₂, ",", ident lt_N₂, ",", ident b_lt_c, "⟩"],
    rcases [expr lt_trichotomy N₁ N₂, "with", "(", ident H, "|", ident rfl, "|", ident H, ")"],
    exacts ["[", expr ⟨N₁, λ
      j
      hj, (lt_N₁ _ hj).trans «expr $ »(lt_N₂ _, hj.trans H), «expr ▸ »(lt_N₂ _ H, a_lt_b)⟩, ",", expr ⟨N₁, λ
      j
      hj, (lt_N₁ _ hj).trans (lt_N₂ _ hj), a_lt_b.trans b_lt_c⟩, ",", expr ⟨N₂, λ
      j hj, (lt_N₁ _ (hj.trans H)).trans (lt_N₂ _ hj), «expr ▸ »((lt_N₁ _ H).symm, b_lt_c)⟩, "]"]
  end }

instance  [LinearOrderₓ ι] [∀ a, PartialOrderₓ (β a)] : PartialOrderₓ (Pilex ι β) :=
  partialOrderOfSO (· < ·)

protected theorem Pilex.is_strict_total_order' [LinearOrderₓ ι] (wf : WellFounded (· < · : ι → ι → Prop))
  [∀ a, LinearOrderₓ (β a)] : IsStrictTotalOrder' (Pilex ι β) (· < ·) :=
  { trichotomous :=
      fun a b =>
        by 
          byCases' h : ∃ i, a i ≠ b i
          ·
            let i := wf.min _ h 
            have hlt_i : ∀ j _ : j < i, a j = b j
            ·
              intro j 
              rw [←not_imp_not]
              exact fun h' => wf.not_lt_min _ _ h' 
            have  : a i ≠ b i 
            exact wf.min_mem _ h 
            exact this.lt_or_lt.imp (fun h => ⟨i, hlt_i, h⟩) fun h => Or.inr ⟨i, fun j hj => (hlt_i j hj).symm, h⟩
          ·
            pushNeg  at h 
            exact Or.inr (Or.inl (funext h)) }

/-- `pilex` is a linear order if the original order is well-founded.
This cannot be an instance, since it depends on the well-foundedness of `<`. -/
protected noncomputable def Pilex.linearOrder [LinearOrderₓ ι] (wf : WellFounded (· < · : ι → ι → Prop))
  [∀ a, LinearOrderₓ (β a)] : LinearOrderₓ (Pilex ι β) :=
  @linearOrderOfSTO' (Pilex ι β) (· < ·) (Pilex.is_strict_total_order' wf) (Classical.decRel _)

theorem Pilex.le_of_forall_le [LinearOrderₓ ι] (wf : WellFounded (· < · : ι → ι → Prop)) [∀ a, LinearOrderₓ (β a)]
  {a b : Pilex ι β} (h : ∀ i, a i ≤ b i) : a ≤ b :=
  by 
    letI this : LinearOrderₓ (Pilex ι β) := Pilex.linearOrder wf 
    exact le_of_not_ltₓ fun ⟨i, hi⟩ => (h i).not_lt hi.2

@[toAdditive]
instance  [LinearOrderₓ ι] [∀ a, OrderedCommGroup (β a)] : OrderedCommGroup (Pilex ι β) :=
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

