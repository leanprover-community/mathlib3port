/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.Algebra.BigOperators.Ring
import Mathbin.Algebra.BigOperators.Option

/-!
Results about "big operations" over a `fintype`, and consequent
results about cardinalities of certain types.

## Implementation note
This content had previously been in `data.fintype.basic`, but was moved here to avoid
requiring `algebra.big_operators` (and hence many other imports) as a
dependency of `fintype`.

However many of the results here really belong in `algebra.big_operators.basic`
and should be moved at some point.
-/


universe u v

variable {α : Type _} {β : Type _} {γ : Type _}

open BigOperators

namespace Fintypeₓ

@[to_additive]
theorem prod_bool [CommMonoidₓ α] (f : Bool → α) : (∏ b, f b) = f true * f false := by simp

theorem card_eq_sum_ones {α} [Fintypeₓ α] : Fintypeₓ.card α = ∑ a : α, 1 :=
  Finsetₓ.card_eq_sum_ones _

section

open Finsetₓ

variable {ι : Type _} [DecidableEq ι] [Fintypeₓ ι]

@[to_additive]
theorem prod_extend_by_one [CommMonoidₓ α] (s : Finsetₓ ι) (f : ι → α) :
    (∏ i, if i ∈ s then f i else 1) = ∏ i in s, f i := by rw [← prod_filter, filter_mem_eq_inter, univ_inter]

end

section

variable {M : Type _} [Fintypeₓ α] [CommMonoidₓ M]

@[to_additive]
theorem prod_eq_one (f : α → M) (h : ∀ a, f a = 1) : (∏ a, f a) = 1 :=
  Finsetₓ.prod_eq_one fun a ha => h a

@[to_additive]
theorem prod_congr (f g : α → M) (h : ∀ a, f a = g a) : (∏ a, f a) = ∏ a, g a :=
  (Finsetₓ.prod_congr rfl) fun a ha => h a

-- ./././Mathport/Syntax/Translate/Basic.lean:555:2: warning: expanding binder collection (x «expr ≠ » a)
@[to_additive]
theorem prod_eq_single {f : α → M} (a : α) (h : ∀ (x) (_ : x ≠ a), f x = 1) : (∏ x, f x) = f a :=
  (Finsetₓ.prod_eq_single a fun x _ hx => h x hx) fun ha => (ha (Finsetₓ.mem_univ a)).elim

@[to_additive]
theorem prod_eq_mul {f : α → M} (a b : α) (h₁ : a ≠ b) (h₂ : ∀ x, x ≠ a ∧ x ≠ b → f x = 1) : (∏ x, f x) = f a * f b :=
  by apply Finsetₓ.prod_eq_mul a b h₁ fun x _ hx => h₂ x hx <;> exact fun hc => (hc (Finsetₓ.mem_univ _)).elim

/-- If a product of a `finset` of a subsingleton type has a given
value, so do the terms in that product. -/
@[to_additive "If a sum of a `finset` of a subsingleton type has a given\nvalue, so do the terms in that sum."]
theorem eq_of_subsingleton_of_prod_eq {ι : Type _} [Subsingleton ι] {s : Finsetₓ ι} {f : ι → M} {b : M}
    (h : (∏ i in s, f i) = b) : ∀ i ∈ s, f i = b :=
  Finsetₓ.eq_of_card_le_one_of_prod_eq (Finsetₓ.card_le_one_of_subsingleton s) h

end

end Fintypeₓ

open Finsetₓ

section

variable {M : Type _} [Fintypeₓ α] [CommMonoidₓ M]

@[simp, to_additive]
theorem Fintypeₓ.prod_option (f : Option α → M) : (∏ i, f i) = f none * ∏ i, f (some i) :=
  Finsetₓ.prod_insert_none f univ

end

open Finsetₓ

@[simp]
theorem Fintypeₓ.card_sigma {α : Type _} (β : α → Type _) [Fintypeₓ α] [∀ a, Fintypeₓ (β a)] :
    Fintypeₓ.card (Sigma β) = ∑ a, Fintypeₓ.card (β a) :=
  card_sigma _ _

@[simp]
theorem Finsetₓ.card_pi [DecidableEq α] {δ : α → Type _} (s : Finsetₓ α) (t : ∀ a, Finsetₓ (δ a)) :
    (s.pi t).card = ∏ a in s, card (t a) :=
  Multiset.card_pi _ _

@[simp]
theorem Fintypeₓ.card_pi_finset [DecidableEq α] [Fintypeₓ α] {δ : α → Type _} (t : ∀ a, Finsetₓ (δ a)) :
    (Fintypeₓ.piFinset t).card = ∏ a, card (t a) := by simp [Fintypeₓ.piFinset, card_map]

@[simp]
theorem Fintypeₓ.card_pi {β : α → Type _} [DecidableEq α] [Fintypeₓ α] [f : ∀ a, Fintypeₓ (β a)] :
    Fintypeₓ.card (∀ a, β a) = ∏ a, Fintypeₓ.card (β a) :=
  Fintypeₓ.card_pi_finset _

-- FIXME ouch, this should be in the main file.
@[simp]
theorem Fintypeₓ.card_fun [DecidableEq α] [Fintypeₓ α] [Fintypeₓ β] :
    Fintypeₓ.card (α → β) = Fintypeₓ.card β ^ Fintypeₓ.card α := by rw [Fintypeₓ.card_pi, Finsetₓ.prod_const] <;> rfl

@[simp]
theorem card_vector [Fintypeₓ α] (n : ℕ) : Fintypeₓ.card (Vector α n) = Fintypeₓ.card α ^ n := by
  rw [Fintypeₓ.of_equiv_card] <;> simp

@[simp, to_additive]
theorem Finsetₓ.prod_attach_univ [Fintypeₓ α] [CommMonoidₓ β] (f : { a : α // a ∈ @univ α _ } → β) :
    (∏ x in univ.attach, f x) = ∏ x, f ⟨x, mem_univ _⟩ :=
  Fintypeₓ.prod_equiv (Equivₓ.subtypeUnivEquiv fun x => mem_univ _) _ _ fun x => by simp

/-- Taking a product over `univ.pi t` is the same as taking the product over `fintype.pi_finset t`.
  `univ.pi t` and `fintype.pi_finset t` are essentially the same `finset`, but differ
  in the type of their element, `univ.pi t` is a `finset (Π a ∈ univ, t a)` and
  `fintype.pi_finset t` is a `finset (Π a, t a)`. -/
@[to_additive
      "Taking a sum over `univ.pi t` is the same as taking the sum over\n  `fintype.pi_finset t`. `univ.pi t` and `fintype.pi_finset t` are essentially the same `finset`,\n  but differ in the type of their element, `univ.pi t` is a `finset (Π a ∈ univ, t a)` and\n  `fintype.pi_finset t` is a `finset (Π a, t a)`."]
theorem Finsetₓ.prod_univ_pi [DecidableEq α] [Fintypeₓ α] [CommMonoidₓ β] {δ : α → Type _} {t : ∀ a : α, Finsetₓ (δ a)}
    (f : (∀ a : α, a ∈ (univ : Finsetₓ α) → δ a) → β) :
    (∏ x in univ.pi t, f x) = ∏ x in Fintypeₓ.piFinset t, f fun a _ => x a :=
  prod_bij (fun x _ a => x a (mem_univ _)) (by simp) (by simp)
    (by simp (config := { contextual := true }) [Function.funext_iff]) fun x hx => ⟨fun a _ => x a, by simp_all⟩

/-- The product over `univ` of a sum can be written as a sum over the product of sets,
  `fintype.pi_finset`. `finset.prod_sum` is an alternative statement when the product is not
  over `univ` -/
theorem Finsetₓ.prod_univ_sum [DecidableEq α] [Fintypeₓ α] [CommSemiringₓ β] {δ : α → Type u_1}
    [∀ a : α, DecidableEq (δ a)] {t : ∀ a : α, Finsetₓ (δ a)} {f : ∀ a : α, δ a → β} :
    (∏ a, ∑ b in t a, f a b) = ∑ p in Fintypeₓ.piFinset t, ∏ x, f x (p x) := by
  simp only [Finsetₓ.prod_attach_univ, prod_sum, Finsetₓ.sum_univ_pi]

/-- Summing `a^s.card * b^(n-s.card)` over all finite subsets `s` of a fintype of cardinality `n`
gives `(a + b)^n`. The "good" proof involves expanding along all coordinates using the fact that
`x^n` is multilinear, but multilinear maps are only available now over rings, so we give instead
a proof reducing to the usual binomial theorem to have a result over semirings. -/
theorem Fintypeₓ.sum_pow_mul_eq_add_pow (α : Type _) [Fintypeₓ α] {R : Type _} [CommSemiringₓ R] (a b : R) :
    (∑ s : Finsetₓ α, a ^ s.card * b ^ (Fintypeₓ.card α - s.card)) = (a + b) ^ Fintypeₓ.card α :=
  Finsetₓ.sum_pow_mul_eq_add_pow _ _ _

@[to_additive]
theorem Function.Bijective.prod_comp [Fintypeₓ α] [Fintypeₓ β] [CommMonoidₓ γ] {f : α → β} (hf : Function.Bijective f)
    (g : β → γ) : (∏ i, g (f i)) = ∏ i, g i :=
  Fintypeₓ.prod_bijective f hf _ _ fun x => rfl

@[to_additive]
theorem Equivₓ.prod_comp [Fintypeₓ α] [Fintypeₓ β] [CommMonoidₓ γ] (e : α ≃ β) (f : β → γ) :
    (∏ i, f (e i)) = ∏ i, f i :=
  e.Bijective.prod_comp f

@[to_additive]
theorem Equivₓ.prod_comp' [Fintypeₓ α] [Fintypeₓ β] [CommMonoidₓ γ] (e : α ≃ β) (f : α → γ) (g : β → γ)
    (h : ∀ i, f i = g (e i)) : (∏ i, f i) = ∏ i, g i :=
  (show f = g ∘ e from funext h).symm ▸ e.prod_comp _

/-- It is equivalent to sum a function over `fin n` or `finset.range n`. -/
@[to_additive]
theorem Finₓ.prod_univ_eq_prod_range [CommMonoidₓ α] (f : ℕ → α) (n : ℕ) : (∏ i : Finₓ n, f i) = ∏ i in range n, f i :=
  calc
    (∏ i : Finₓ n, f i) = ∏ i : { x // x ∈ range n }, f i :=
      (Finₓ.equivSubtype.trans (Equivₓ.subtypeEquivRight (by simp))).prod_comp' _ _ (by simp)
    _ = ∏ i in range n, f i := by rw [← attach_eq_univ, prod_attach]
    

@[to_additive]
theorem Finsetₓ.prod_fin_eq_prod_range [CommMonoidₓ β] {n : ℕ} (c : Finₓ n → β) :
    (∏ i, c i) = ∏ i in Finsetₓ.range n, if h : i < n then c ⟨i, h⟩ else 1 := by
  rw [← Finₓ.prod_univ_eq_prod_range, Finsetₓ.prod_congr rfl]
  rintro ⟨i, hi⟩ _
  simp only [Finₓ.coe_eq_val, hi, dif_pos]

@[to_additive]
theorem Finsetₓ.prod_to_finset_eq_subtype {M : Type _} [CommMonoidₓ M] [Fintypeₓ α] (p : α → Prop) [DecidablePred p]
    (f : α → M) : (∏ a in { x | p x }.toFinset, f a) = ∏ a : Subtype p, f a := by
  rw [← Finsetₓ.prod_subtype]
  simp

@[to_additive]
theorem Finsetₓ.prod_fiberwise [DecidableEq β] [Fintypeₓ β] [CommMonoidₓ γ] (s : Finsetₓ α) (f : α → β) (g : α → γ) :
    (∏ b : β, ∏ a in s.filter fun a => f a = b, g a) = ∏ a in s, g a :=
  Finsetₓ.prod_fiberwise_of_maps_to (fun x _ => mem_univ _) _

@[to_additive]
theorem Fintypeₓ.prod_fiberwise [Fintypeₓ α] [DecidableEq β] [Fintypeₓ β] [CommMonoidₓ γ] (f : α → β) (g : α → γ) :
    (∏ b : β, ∏ a : { a // f a = b }, g (a : α)) = ∏ a, g a := by
  rw [← (Equivₓ.sigmaFiberEquiv f).prod_comp, ← univ_sigma_univ, prod_sigma]
  rfl

theorem Fintypeₓ.prod_dite [Fintypeₓ α] {p : α → Prop} [DecidablePred p] [CommMonoidₓ β] (f : ∀ (a : α) (ha : p a), β)
    (g : ∀ (a : α) (ha : ¬p a), β) :
    (∏ a, dite (p a) (f a) (g a)) = (∏ a : { a // p a }, f a a.2) * ∏ a : { a // ¬p a }, g a a.2 := by
  simp only [prod_dite, attach_eq_univ]
  congr 1
  · convert (Equivₓ.subtypeEquivRight _).prod_comp fun x : { x // p x } => f x x.2
    simp
    
  · convert (Equivₓ.subtypeEquivRight _).prod_comp fun x : { x // ¬p x } => g x x.2
    simp
    

section

open Finsetₓ

variable {α₁ : Type _} {α₂ : Type _} {M : Type _} [Fintypeₓ α₁] [Fintypeₓ α₂] [CommMonoidₓ M]

@[to_additive]
theorem Fintypeₓ.prod_sum_elim (f : α₁ → M) (g : α₂ → M) : (∏ x, Sum.elim f g x) = (∏ a₁, f a₁) * ∏ a₂, g a₂ := by
  classical
  rw [univ_sum_type, prod_sum_elim]

@[to_additive]
theorem Fintypeₓ.prod_sum_type (f : Sum α₁ α₂ → M) : (∏ x, f x) = (∏ a₁, f (Sum.inl a₁)) * ∏ a₂, f (Sum.inr a₂) := by
  simp only [← Fintypeₓ.prod_sum_elim, Sum.elim_comp_inl_inr]

end

