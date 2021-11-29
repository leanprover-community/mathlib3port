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

open_locale BigOperators

namespace Fintype

@[toAdditive]
theorem prod_bool [CommMonoidₓ α] (f : Bool → α) : (∏b, f b) = f tt*f ff :=
  by 
    simp 

theorem card_eq_sum_ones {α} [Fintype α] : Fintype.card α = ∑a : α, 1 :=
  Finset.card_eq_sum_ones _

section 

open Finset

variable {ι : Type _} [DecidableEq ι] [Fintype ι]

@[toAdditive]
theorem prod_extend_by_one [CommMonoidₓ α] (s : Finset ι) (f : ι → α) : (∏i, if i ∈ s then f i else 1) = ∏i in s, f i :=
  by 
    rw [←prod_filter, filter_mem_eq_inter, univ_inter]

end 

section 

variable {M : Type _} [Fintype α] [CommMonoidₓ M]

@[toAdditive]
theorem prod_eq_one (f : α → M) (h : ∀ a, f a = 1) : (∏a, f a) = 1 :=
  Finset.prod_eq_one$ fun a ha => h a

@[toAdditive]
theorem prod_congr (f g : α → M) (h : ∀ a, f a = g a) : (∏a, f a) = ∏a, g a :=
  Finset.prod_congr rfl$ fun a ha => h a

@[toAdditive]
theorem prod_eq_single {f : α → M} (a : α) (h : ∀ x _ : x ≠ a, f x = 1) : (∏x, f x) = f a :=
  (Finset.prod_eq_single a fun x _ hx => h x hx)$ fun ha => (ha (Finset.mem_univ a)).elim

@[toAdditive]
theorem prod_eq_mul {f : α → M} (a b : α) (h₁ : a ≠ b) (h₂ : ∀ x, x ≠ a ∧ x ≠ b → f x = 1) : (∏x, f x) = f a*f b :=
  by 
    apply Finset.prod_eq_mul a b h₁ fun x _ hx => h₂ x hx <;> exact fun hc => (hc (Finset.mem_univ _)).elim

/-- If a product of a `finset` of a subsingleton type has a given
value, so do the terms in that product. -/
@[toAdditive "If a sum of a `finset` of a subsingleton type has a given\nvalue, so do the terms in that sum."]
theorem eq_of_subsingleton_of_prod_eq {ι : Type _} [Subsingleton ι] {s : Finset ι} {f : ι → M} {b : M}
  (h : (∏i in s, f i) = b) : ∀ i _ : i ∈ s, f i = b :=
  Finset.eq_of_card_le_one_of_prod_eq (Finset.card_le_one_of_subsingleton s) h

end 

end Fintype

open Finset

section 

variable {M : Type _} [Fintype α] [CommMonoidₓ M]

@[simp, toAdditive]
theorem Fintype.prod_option (f : Option α → M) : (∏i, f i) = f none*∏i, f (some i) :=
  Finset.prod_insert_none f univ

end 

@[toAdditive]
theorem Finₓ.prod_univ_def [CommMonoidₓ β] {n : ℕ} (f : Finₓ n → β) : (∏i, f i) = ((List.finRange n).map f).Prod :=
  by 
    simp [Finₓ.univ_def, Finset.finRange]

@[toAdditive]
theorem Finset.prod_range [CommMonoidₓ β] {n : ℕ} (f : ℕ → β) : (∏i in Finset.range n, f i) = ∏i : Finₓ n, f i :=
  by 
    fapply @Finset.prod_bij' _ _ _ _ _ _ 
    exact
      fun k w =>
        ⟨k,
          by 
            simpa using w⟩
    swap 3 
    exact fun a m => a 
    swap 3 
    exact
      fun a m =>
        by 
          simpa using a.2
    all_goals 
      tidy

@[toAdditive]
theorem Finₓ.prod_of_fn [CommMonoidₓ β] {n : ℕ} (f : Finₓ n → β) : (List.ofFn f).Prod = ∏i, f i :=
  by 
    rw [List.of_fn_eq_map, Finₓ.prod_univ_def]

/-- A product of a function `f : fin 0 → β` is `1` because `fin 0` is empty -/
@[toAdditive "A sum of a function `f : fin 0 → β` is `0` because `fin 0` is empty"]
theorem Finₓ.prod_univ_zero [CommMonoidₓ β] (f : Finₓ 0 → β) : (∏i, f i) = 1 :=
  rfl

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f x`, for some `x : fin (n + 1)` times the remaining product -/
@[toAdditive]
theorem Finₓ.prod_univ_succ_above [CommMonoidₓ β] {n : ℕ} (f : Finₓ (n+1) → β) (x : Finₓ (n+1)) :
  (∏i, f i) = f x*∏i : Finₓ n, f (x.succ_above i) :=
  by 
    rw [Fintype.prod_eq_mul_prod_compl x, ←Finₓ.image_succ_above_univ, prod_image]
    exact fun _ _ _ _ h => x.succ_above.injective h

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f 0` plus the remaining product -/
@[toAdditive]
theorem Finₓ.prod_univ_succ [CommMonoidₓ β] {n : ℕ} (f : Finₓ (n+1) → β) : (∏i, f i) = f 0*∏i : Finₓ n, f i.succ :=
  Finₓ.prod_univ_succ_above f 0

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f (fin.last n)` plus the remaining product -/
@[toAdditive]
theorem Finₓ.prod_univ_cast_succ [CommMonoidₓ β] {n : ℕ} (f : Finₓ (n+1) → β) :
  (∏i, f i) = (∏i : Finₓ n, f i.cast_succ)*f (Finₓ.last n) :=
  by 
    simpa [mul_commₓ] using Finₓ.prod_univ_succ_above f (Finₓ.last n)

@[toAdditive sum_univ_one]
theorem Finₓ.prod_univ_one [CommMonoidₓ β] (f : Finₓ 1 → β) : (∏i, f i) = f 0 :=
  by 
    simp 

@[toAdditive]
theorem Finₓ.prod_univ_two [CommMonoidₓ β] (f : Finₓ 2 → β) : (∏i, f i) = f 0*f 1 :=
  by 
    simp [Finₓ.prod_univ_succ]

open Finset

@[simp]
theorem Fintype.card_sigma {α : Type _} (β : α → Type _) [Fintype α] [∀ a, Fintype (β a)] :
  Fintype.card (Sigma β) = ∑a, Fintype.card (β a) :=
  card_sigma _ _

@[simp]
theorem Finset.card_pi [DecidableEq α] {δ : α → Type _} (s : Finset α) (t : ∀ a, Finset (δ a)) :
  (s.pi t).card = ∏a in s, card (t a) :=
  Multiset.card_pi _ _

@[simp]
theorem Fintype.card_pi_finset [DecidableEq α] [Fintype α] {δ : α → Type _} (t : ∀ a, Finset (δ a)) :
  (Fintype.piFinset t).card = ∏a, card (t a) :=
  by 
    simp [Fintype.piFinset, card_map]

@[simp]
theorem Fintype.card_pi {β : α → Type _} [DecidableEq α] [Fintype α] [f : ∀ a, Fintype (β a)] :
  Fintype.card (∀ a, β a) = ∏a, Fintype.card (β a) :=
  Fintype.card_pi_finset _

@[simp]
theorem Fintype.card_fun [DecidableEq α] [Fintype α] [Fintype β] :
  Fintype.card (α → β) = Fintype.card β ^ Fintype.card α :=
  by 
    rw [Fintype.card_pi, Finset.prod_const] <;> rfl

@[simp]
theorem card_vector [Fintype α] (n : ℕ) : Fintype.card (Vector α n) = Fintype.card α ^ n :=
  by 
    rw [Fintype.of_equiv_card] <;> simp 

@[simp, toAdditive]
theorem Finset.prod_attach_univ [Fintype α] [CommMonoidₓ β] (f : { a : α // a ∈ @univ α _ } → β) :
  (∏x in univ.attach, f x) = ∏x, f ⟨x, mem_univ _⟩ :=
  Fintype.prod_equiv (Equiv.subtypeUnivEquiv fun x => mem_univ _) _ _
    fun x =>
      by 
        simp 

-- error in Data.Fintype.Card: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Taking a product over `univ.pi t` is the same as taking the product over `fintype.pi_finset t`.
  `univ.pi t` and `fintype.pi_finset t` are essentially the same `finset`, but differ
  in the type of their element, `univ.pi t` is a `finset (Π a ∈ univ, t a)` and
  `fintype.pi_finset t` is a `finset (Π a, t a)`. -/
@[to_additive #[expr "Taking a sum over `univ.pi t` is the same as taking the sum over\n  `fintype.pi_finset t`. `univ.pi t` and `fintype.pi_finset t` are essentially the same `finset`,\n  but differ in the type of their element, `univ.pi t` is a `finset (Π a ∈ univ, t a)` and\n  `fintype.pi_finset t` is a `finset (Π a, t a)`."]]
theorem finset.prod_univ_pi
[decidable_eq α]
[fintype α]
[comm_monoid β]
{δ : α → Type*}
{t : ∀ a : α, finset (δ a)}
(f : ∀
 a : α, «expr ∈ »(a, (univ : finset α)) → δ a → β) : «expr = »(«expr∏ in , »((x), univ.pi t, f x), «expr∏ in , »((x), fintype.pi_finset t, f (λ
   a _, x a))) :=
prod_bij (λ
 x
 _
 a, x a (mem_univ _)) (by simp [] [] [] [] [] []) (by simp [] [] [] [] [] []) (by simp [] [] [] ["[", expr function.funext_iff, "]"] [] [] { contextual := tt }) (λ
 x hx, ⟨λ a _, x a, by simp [] [] [] ["*"] [] ["at", "*"]⟩)

/-- The product over `univ` of a sum can be written as a sum over the product of sets,
  `fintype.pi_finset`. `finset.prod_sum` is an alternative statement when the product is not
  over `univ` -/
theorem Finset.prod_univ_sum [DecidableEq α] [Fintype α] [CommSemiringₓ β] {δ : α → Type u_1}
  [∀ a : α, DecidableEq (δ a)] {t : ∀ a : α, Finset (δ a)} {f : ∀ a : α, δ a → β} :
  (∏a, ∑b in t a, f a b) = ∑p in Fintype.piFinset t, ∏x, f x (p x) :=
  by 
    simp only [Finset.prod_attach_univ, prod_sum, Finset.sum_univ_pi]

/-- Summing `a^s.card * b^(n-s.card)` over all finite subsets `s` of a fintype of cardinality `n`
gives `(a + b)^n`. The "good" proof involves expanding along all coordinates using the fact that
`x^n` is multilinear, but multilinear maps are only available now over rings, so we give instead
a proof reducing to the usual binomial theorem to have a result over semirings. -/
theorem Fintype.sum_pow_mul_eq_add_pow (α : Type _) [Fintype α] {R : Type _} [CommSemiringₓ R] (a b : R) :
  (∑s : Finset α, (a ^ s.card)*b ^ (Fintype.card α - s.card)) = (a+b) ^ Fintype.card α :=
  Finset.sum_pow_mul_eq_add_pow _ _ _

theorem Finₓ.sum_pow_mul_eq_add_pow {n : ℕ} {R : Type _} [CommSemiringₓ R] (a b : R) :
  (∑s : Finset (Finₓ n), (a ^ s.card)*b ^ (n - s.card)) = (a+b) ^ n :=
  by 
    simpa using Fintype.sum_pow_mul_eq_add_pow (Finₓ n) a b

theorem Finₓ.prod_const [CommMonoidₓ α] (n : ℕ) (x : α) : (∏i : Finₓ n, x) = x ^ n :=
  by 
    simp 

theorem Finₓ.sum_const [AddCommMonoidₓ α] (n : ℕ) (x : α) : (∑i : Finₓ n, x) = n • x :=
  by 
    simp 

@[toAdditive]
theorem Function.Bijective.prod_comp [Fintype α] [Fintype β] [CommMonoidₓ γ] {f : α → β} (hf : Function.Bijective f)
  (g : β → γ) : (∏i, g (f i)) = ∏i, g i :=
  Fintype.prod_bijective f hf _ _ fun x => rfl

@[toAdditive]
theorem Equiv.prod_comp [Fintype α] [Fintype β] [CommMonoidₓ γ] (e : α ≃ β) (f : β → γ) : (∏i, f (e i)) = ∏i, f i :=
  e.bijective.prod_comp f

/-- It is equivalent to sum a function over `fin n` or `finset.range n`. -/
@[toAdditive]
theorem Finₓ.prod_univ_eq_prod_range [CommMonoidₓ α] (f : ℕ → α) (n : ℕ) : (∏i : Finₓ n, f i) = ∏i in range n, f i :=
  calc (∏i : Finₓ n, f i) = ∏i : { x // x ∈ range n }, f i :=
    ((Equiv.finEquivSubtype n).trans (Equiv.subtypeEquivRight fun _ => mem_range.symm)).prod_comp (f ∘ coeₓ)
    _ = ∏i in range n, f i :=
    by 
      rw [←attach_eq_univ, prod_attach]
    

@[toAdditive]
theorem Finset.prod_fin_eq_prod_range [CommMonoidₓ β] {n : ℕ} (c : Finₓ n → β) :
  (∏i, c i) = ∏i in Finset.range n, if h : i < n then c ⟨i, h⟩ else 1 :=
  by 
    rw [←Finₓ.prod_univ_eq_prod_range, Finset.prod_congr rfl]
    rintro ⟨i, hi⟩ _ 
    simp only [Finₓ.coe_eq_val, hi, dif_pos]

@[toAdditive]
theorem Finset.prod_to_finset_eq_subtype {M : Type _} [CommMonoidₓ M] [Fintype α] (p : α → Prop) [DecidablePred p]
  (f : α → M) : (∏a in { x | p x }.toFinset, f a) = ∏a : Subtype p, f a :=
  by 
    rw [←Finset.prod_subtype]
    simp 

@[toAdditive]
theorem Finset.prod_fiberwise [DecidableEq β] [Fintype β] [CommMonoidₓ γ] (s : Finset α) (f : α → β) (g : α → γ) :
  (∏b : β, ∏a in s.filter fun a => f a = b, g a) = ∏a in s, g a :=
  Finset.prod_fiberwise_of_maps_to (fun x _ => mem_univ _) _

@[toAdditive]
theorem Fintype.prod_fiberwise [Fintype α] [DecidableEq β] [Fintype β] [CommMonoidₓ γ] (f : α → β) (g : α → γ) :
  (∏b : β, ∏a : { a // f a = b }, g (a : α)) = ∏a, g a :=
  by 
    rw [←(Equiv.sigmaPreimageEquiv f).prod_comp, ←univ_sigma_univ, prod_sigma]
    rfl

theorem Fintype.prod_dite [Fintype α] {p : α → Prop} [DecidablePred p] [CommMonoidₓ β] (f : ∀ a : α ha : p a, β)
  (g : ∀ a : α ha : ¬p a, β) :
  (∏a, dite (p a) (f a) (g a)) = (∏a : { a // p a }, f a a.2)*∏a : { a // ¬p a }, g a a.2 :=
  by 
    simp only [prod_dite, attach_eq_univ]
    congr 1
    ·
      convert (Equiv.subtypeEquivRight _).prod_comp fun x : { x // p x } => f x x.2
      simp 
    ·
      convert (Equiv.subtypeEquivRight _).prod_comp fun x : { x // ¬p x } => g x x.2
      simp 

section 

open Finset

variable {α₁ : Type _} {α₂ : Type _} {M : Type _} [Fintype α₁] [Fintype α₂] [CommMonoidₓ M]

@[toAdditive]
theorem Fintype.prod_sum_elim (f : α₁ → M) (g : α₂ → M) : (∏x, Sum.elim f g x) = (∏a₁, f a₁)*∏a₂, g a₂ :=
  by 
    classical 
    rw [univ_sum_type, prod_sum_elim]

@[toAdditive]
theorem Fintype.prod_sum_type (f : Sum α₁ α₂ → M) : (∏x, f x) = (∏a₁, f (Sum.inl a₁))*∏a₂, f (Sum.inr a₂) :=
  by 
    simp only [←Fintype.prod_sum_elim, Sum.elim_comp_inl_inr]

end 

namespace List

-- error in Data.Fintype.Card: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_take_of_fn
[comm_monoid α]
{n : exprℕ()}
(f : fin n → α)
(i : exprℕ()) : «expr = »(((of_fn f).take i).prod, «expr∏ in , »((j), finset.univ.filter (λ
   j : fin n, «expr < »(j.val, i)), f j)) :=
begin
  have [ident A] [":", expr ∀ j : fin n, «expr¬ »(«expr < »((j : exprℕ()), 0))] [":=", expr λ j, not_lt_bot],
  induction [expr i] [] ["with", ident i, ident IH] [],
  { simp [] [] [] ["[", expr A, "]"] [] [] },
  by_cases [expr h, ":", expr «expr < »(i, n)],
  { have [] [":", expr «expr < »(i, length (of_fn f))] [],
    by rwa ["[", expr length_of_fn f, "]"] [],
    rw [expr prod_take_succ _ _ this] [],
    have [ident A] [":", expr «expr = »((finset.univ : finset (fin n)).filter (λ
       j, «expr < »(j.val, «expr + »(i, 1))), «expr ∪ »((finset.univ : finset (fin n)).filter (λ
        j, «expr < »(j.val, i)), {(⟨i, h⟩ : fin n)}))] [],
    by { ext [] [ident j] [],
      simp [] [] [] ["[", expr nat.lt_succ_iff_lt_or_eq, ",", expr fin.ext_iff, ",", "-", ident add_comm, "]"] [] [] },
    have [ident B] [":", expr _root_.disjoint (finset.filter (λ
       j : fin n, «expr < »(j.val, i)) finset.univ) (singleton (⟨i, h⟩ : fin n))] [],
    by simp [] [] [] [] [] [],
    rw ["[", expr A, ",", expr finset.prod_union B, ",", expr IH, "]"] [],
    simp [] [] [] [] [] [] },
  { have [ident A] [":", expr «expr = »((of_fn f).take i, (of_fn f).take i.succ)] [],
    { rw ["<-", expr length_of_fn f] ["at", ident h],
      have [] [":", expr «expr ≤ »(length (of_fn f), i)] [":=", expr not_lt.mp h],
      rw ["[", expr take_all_of_le this, ",", expr take_all_of_le (le_trans this (nat.le_succ _)), "]"] [] },
    have [ident B] [":", expr ∀ j : fin n, «expr = »(«expr < »((j : exprℕ()), i.succ), «expr < »((j : exprℕ()), i))] [],
    { assume [binders (j)],
      have [] [":", expr «expr < »((j : exprℕ()), i)] [":=", expr lt_of_lt_of_le j.2 (not_lt.mp h)],
      simp [] [] [] ["[", expr this, ",", expr lt_trans this (nat.lt_succ_self _), "]"] [] [] },
    simp [] [] [] ["[", "<-", expr A, ",", expr B, ",", expr IH, "]"] [] [] }
end

-- error in Data.Fintype.Card: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_of_fn [comm_monoid α] {n : exprℕ()} {f : fin n → α} : «expr = »((of_fn f).prod, «expr∏ , »((i), f i)) :=
begin
  convert [] [expr prod_take_of_fn f n] [],
  { rw ["[", expr take_all_of_le (le_of_eq (length_of_fn f)), "]"] [] },
  { have [] [":", expr ∀ j : fin n, «expr < »((j : exprℕ()), n)] [":=", expr λ j, j.is_lt],
    simp [] [] [] ["[", expr this, "]"] [] [] }
end

theorem alternating_sum_eq_finset_sum {G : Type _} [AddCommGroupₓ G] :
  ∀ L : List G, alternating_sum L = ∑i : Finₓ L.length, (-1 : ℤ) ^ (i : ℕ) • L.nth_le i i.is_lt
| [] =>
  by 
    rw [alternating_sum, Finset.sum_eq_zero]
    rintro ⟨i, ⟨⟩⟩
| g :: [] =>
  by 
    show g = ∑i : Finₓ 1, (-1 : ℤ) ^ (i : ℕ) • [g].nthLe i i.2
    rw [Finₓ.sum_univ_succ]
    simp 
| g :: h :: L =>
  calc ((g+-h)+L.alternating_sum) = (g+-h)+∑i : Finₓ L.length, (-1 : ℤ) ^ (i : ℕ) • L.nth_le i i.2 :=
    congr_argₓ _ (alternating_sum_eq_finset_sum _)
    _ = ∑i : Finₓ (L.length+2), (-1 : ℤ) ^ (i : ℕ) • List.nthLe (g :: h :: L) i _ :=
    by 
      rw [Finₓ.sum_univ_succ, Finₓ.sum_univ_succ, add_assocₓ]
      unfoldCoes 
      simp [Nat.succ_eq_add_one, pow_addₓ]
      rfl
    

@[toAdditive]
theorem alternating_prod_eq_finset_prod {G : Type _} [CommGroupₓ G] :
  ∀ L : List G, alternating_prod L = ∏i : Finₓ L.length, L.nth_le i i.2 ^ (-1 : ℤ) ^ (i : ℕ)
| [] =>
  by 
    rw [alternating_prod, Finset.prod_eq_one]
    rintro ⟨i, ⟨⟩⟩
| g :: [] =>
  by 
    show g = ∏i : Finₓ 1, [g].nthLe i i.2 ^ (-1 : ℤ) ^ (i : ℕ)
    rw [Finₓ.prod_univ_succ]
    simp 
| g :: h :: L =>
  calc ((g*h⁻¹)*L.alternating_prod) = (g*h⁻¹)*∏i : Finₓ L.length, L.nth_le i i.2 ^ (-1 : ℤ) ^ (i : ℕ) :=
    congr_argₓ _ (alternating_prod_eq_finset_prod _)
    _ = ∏i : Finₓ (L.length+2), List.nthLe (g :: h :: L) i _ ^ (-1 : ℤ) ^ (i : ℕ) :=
    by 
      rw [Finₓ.prod_univ_succ, Finₓ.prod_univ_succ, mul_assocₓ]
      unfoldCoes 
      simp [Nat.succ_eq_add_one, pow_addₓ]
      rfl
    

end List

