import Mathbin.Data.List.Basic

/-!
# Sums and products from lists

This file provides basic results about `list.prod` and `list.sum`, which calculate the product and
sum of elements of a list. These are defined in [`data.list.defs`](./data/list/defs).
-/


variable {α β γ : Type _}

namespace List

section Monoidₓ

variable [Monoidₓ α] {l l₁ l₂ : List α} {a : α}

@[simp, toAdditive]
theorem prod_nil : ([] : List α).Prod = 1 :=
  rfl

@[toAdditive]
theorem prod_singleton : [a].Prod = a :=
  one_mulₓ a

@[simp, toAdditive]
theorem prod_cons : (a :: l).Prod = a*l.prod :=
  calc (a :: l).Prod = foldl (·*·) (a*1) l :=
    by 
      simp only [List.prod, foldl_cons, one_mulₓ, mul_oneₓ]
    _ = _ := foldl_assoc
    

@[simp, toAdditive]
theorem prod_append : (l₁ ++ l₂).Prod = l₁.prod*l₂.prod :=
  calc (l₁ ++ l₂).Prod = foldl (·*·) (foldl (·*·) 1 l₁*1) l₂ :=
    by 
      simp [List.prod]
    _ = l₁.prod*l₂.prod := foldl_assoc
    

@[toAdditive]
theorem prod_concat : (l.concat a).Prod = l.prod*a :=
  by 
    rw [concat_eq_append, prod_append, prod_cons, prod_nil, mul_oneₓ]

@[simp, toAdditive]
theorem prod_join {l : List (List α)} : l.join.prod = (l.map List.prod).Prod :=
  by 
    induction l <;> [rfl, simp only [List.join, map, prod_append, prod_cons]]

/-- If zero is an element of a list `L`, then `list.prod L = 0`. If the domain is a nontrivial
monoid with zero with no divisors, then this implication becomes an `iff`, see
`list.prod_eq_zero_iff`. -/
theorem prod_eq_zero {M₀ : Type _} [MonoidWithZeroₓ M₀] {L : List M₀} (h : (0 : M₀) ∈ L) : L.prod = 0 :=
  by 
    induction' L with a L ihL
    ·
      exact absurd h (not_mem_nil _)
    ·
      rw [prod_cons]
      cases' (mem_cons_iff _ _ _).1 h with ha hL 
      exacts[mul_eq_zero_of_left ha.symm _, mul_eq_zero_of_right _ (ihL hL)]

/-- Product of elements of a list `L` equals zero if and only if `0 ∈ L`. See also
`list.prod_eq_zero` for an implication that needs weaker typeclass assumptions. -/
@[simp]
theorem prod_eq_zero_iff {M₀ : Type _} [MonoidWithZeroₓ M₀] [Nontrivial M₀] [NoZeroDivisors M₀] {L : List M₀} :
  L.prod = 0 ↔ (0 : M₀) ∈ L :=
  by 
    induction' L with a L ihL
    ·
      simp 
    ·
      rw [prod_cons, mul_eq_zero, ihL, mem_cons_iff, eq_comm]

theorem prod_ne_zero {M₀ : Type _} [MonoidWithZeroₓ M₀] [Nontrivial M₀] [NoZeroDivisors M₀] {L : List M₀}
  (hL : (0 : M₀) ∉ L) : L.prod ≠ 0 :=
  mt prod_eq_zero_iff.1 hL

@[toAdditive]
theorem prod_eq_foldr : l.prod = foldr (·*·) 1 l :=
  List.recOn l rfl$
    fun a l ihl =>
      by 
        rw [prod_cons, foldr_cons, ihl]

@[toAdditive]
theorem prod_hom_rel {α β γ : Type _} [Monoidₓ β] [Monoidₓ γ] (l : List α) {r : β → γ → Prop} {f : α → β} {g : α → γ}
  (h₁ : r 1 1) (h₂ : ∀ ⦃a b c⦄, r b c → r (f a*b) (g a*c)) : r (l.map f).Prod (l.map g).Prod :=
  List.recOn l h₁
    fun a l hl =>
      by 
        simp only [map_cons, prod_cons, h₂ hl]

@[toAdditive]
theorem prod_hom [Monoidₓ β] (l : List α) (f : α →* β) : (l.map f).Prod = f l.prod :=
  by 
    simp only [Prod, foldl_map, f.map_one.symm]
    exact l.foldl_hom _ _ _ 1 f.map_mul

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (m «expr ∈ » L)
@[toAdditive]
theorem prod_is_unit [Monoidₓ β] : ∀ {L : List β} u : ∀ m _ : m ∈ L, IsUnit m, IsUnit L.prod
| [], _ =>
  by 
    simp 
| h :: t, u =>
  by 
    simp only [List.prod_cons]
    exact IsUnit.mul (u h (mem_cons_self h t)) (prod_is_unit fun m mt => u m (mem_cons_of_mem h mt))

@[simp, toAdditive]
theorem prod_take_mul_prod_drop : ∀ L : List α i : ℕ, ((L.take i).Prod*(L.drop i).Prod) = L.prod
| [], i =>
  by 
    simp 
| L, 0 =>
  by 
    simp 
| h :: t, n+1 =>
  by 
    dsimp 
    rw [prod_cons, prod_cons, mul_assocₓ, prod_take_mul_prod_drop]

@[simp, toAdditive]
theorem prod_take_succ : ∀ L : List α i : ℕ p, (L.take (i+1)).Prod = (L.take i).Prod*L.nth_le i p
| [], i, p =>
  by 
    cases p
| h :: t, 0, _ =>
  by 
    simp 
| h :: t, n+1, _ =>
  by 
    dsimp 
    rw [prod_cons, prod_cons, prod_take_succ, mul_assocₓ]

/-- A list with product not one must have positive length. -/
@[toAdditive]
theorem length_pos_of_prod_ne_one (L : List α) (h : L.prod ≠ 1) : 0 < L.length :=
  by 
    cases L
    ·
      simp  at h 
      cases h
    ·
      simp 

@[toAdditive]
theorem prod_update_nth :
  ∀ L : List α n : ℕ a : α,
    (L.update_nth n a).Prod = ((L.take n).Prod*if n < L.length then a else 1)*(L.drop (n+1)).Prod
| x :: xs, 0, a =>
  by 
    simp [update_nth]
| x :: xs, i+1, a =>
  by 
    simp [update_nth, prod_update_nth xs i a, mul_assocₓ]
| [], _, _ =>
  by 
    simp [update_nth, (Nat.zero_leₓ _).not_lt]

open MulOpposite

theorem _root_.mul_opposite.op_list_prod : ∀ l : List α, op l.prod = (l.map op).reverse.Prod
| [] => rfl
| x :: xs =>
  by 
    rw [List.prod_cons, List.map_consₓ, List.reverse_cons', List.prod_concat, op_mul, _root_.mul_opposite.op_list_prod]

theorem _root_.mul_opposite.unop_list_prod (l : List (αᵐᵒᵖ)) : l.prod.unop = (l.map unop).reverse.Prod :=
  by 
    rw [←op_inj, op_unop, MulOpposite.op_list_prod, map_reverse, map_map, reverse_reverse, op_comp_unop, map_id]

end Monoidₓ

section Groupₓ

variable [Groupₓ α]

/-- This is the `list.prod` version of `mul_inv_rev` -/
@[toAdditive "This is the `list.sum` version of `add_neg_rev`"]
theorem prod_inv_reverse : ∀ L : List α, L.prod⁻¹ = (L.map fun x => x⁻¹).reverse.Prod
| [] =>
  by 
    simp 
| x :: xs =>
  by 
    simp [prod_inv_reverse xs]

/-- A non-commutative variant of `list.prod_reverse` -/
@[toAdditive "A non-commutative variant of `list.sum_reverse`"]
theorem prod_reverse_noncomm : ∀ L : List α, L.reverse.prod = (L.map fun x => x⁻¹).Prod⁻¹ :=
  by 
    simp [prod_inv_reverse]

/-- Counterpart to `list.prod_take_succ` when we have an inverse operation -/
@[simp, toAdditive "Counterpart to `list.sum_take_succ` when we have an negation operation"]
theorem prod_drop_succ : ∀ L : List α i : ℕ p, (L.drop (i+1)).Prod = L.nth_le i p⁻¹*(L.drop i).Prod
| [], i, p => False.elim (Nat.not_lt_zeroₓ _ p)
| x :: xs, 0, p =>
  by 
    simp 
| x :: xs, i+1, p => prod_drop_succ xs i _

end Groupₓ

section CommGroupₓ

variable [CommGroupₓ α]

/-- This is the `list.prod` version of `mul_inv` -/
@[toAdditive "This is the `list.sum` version of `add_neg`"]
theorem prod_inv : ∀ L : List α, L.prod⁻¹ = (L.map fun x => x⁻¹).Prod
| [] =>
  by 
    simp 
| x :: xs =>
  by 
    simp [mul_commₓ, prod_inv xs]

/-- Alternative version of `list.prod_update_nth` when the list is over a group -/
@[toAdditive "Alternative version of `list.sum_update_nth` when the list is over a group"]
theorem prod_update_nth' (L : List α) (n : ℕ) (a : α) :
  (L.update_nth n a).Prod = L.prod*if hn : n < L.length then L.nth_le n hn⁻¹*a else 1 :=
  by 
    refine' (prod_update_nth L n a).trans _ 
    splitIfs with hn hn
    ·
      rw [mul_commₓ _ a, mul_assocₓ a, prod_drop_succ L n hn, mul_commₓ _ (drop n L).Prod, ←mul_assocₓ (take n L).Prod,
        prod_take_mul_prod_drop, mul_commₓ a, mul_assocₓ]
    ·
      simp only [take_all_of_le (le_of_not_ltₓ hn), prod_nil, mul_oneₓ,
        drop_eq_nil_of_le ((le_of_not_ltₓ hn).trans n.le_succ)]

end CommGroupₓ

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (i «expr ≤ » L.length)
theorem eq_of_sum_take_eq [AddLeftCancelMonoid α] {L L' : List α} (h : L.length = L'.length)
  (h' : ∀ i _ : i ≤ L.length, (L.take i).Sum = (L'.take i).Sum) : L = L' :=
  by 
    apply ext_le h fun i h₁ h₂ => _ 
    have  : (L.take (i+1)).Sum = (L'.take (i+1)).Sum := h' _ (Nat.succ_le_of_ltₓ h₁)
    rw [sum_take_succ L i h₁, sum_take_succ L' i h₂, h' i (le_of_ltₓ h₁)] at this 
    exact add_left_cancelₓ this

theorem monotone_sum_take [CanonicallyOrderedAddMonoid α] (L : List α) : Monotone fun i => (L.take i).Sum :=
  by 
    apply monotone_nat_of_le_succ fun n => _ 
    byCases' h : n < L.length
    ·
      rw [sum_take_succ _ _ h]
      exact le_self_add
    ·
      pushNeg  at h 
      simp [take_all_of_le h, take_all_of_le (le_transₓ h (Nat.le_succₓ _))]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » l)
@[toAdditive sum_nonneg]
theorem one_le_prod_of_one_le [OrderedCommMonoid α] {l : List α} (hl₁ : ∀ x _ : x ∈ l, (1 : α) ≤ x) : 1 ≤ l.prod :=
  by 
    induction' l with hd tl ih
    ·
      simp 
    rw [prod_cons]
    exact one_le_mul (hl₁ hd (mem_cons_self hd tl)) (ih fun x h => hl₁ x (mem_cons_of_mem hd h))

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » l)
@[toAdditive sum_pos]
theorem one_lt_prod_of_one_lt [OrderedCommMonoid α] :
  ∀ l : List α hl : ∀ x _ : x ∈ l, (1 : α) < x hl₂ : l ≠ [], 1 < l.prod
| [], _, h => (h rfl).elim
| [b], h, _ =>
  by 
    simpa using h
| a :: b :: l, hl₁, hl₂ =>
  by 
    simp only [forall_eq_or_imp, List.mem_cons_iffₓ _ a] at hl₁ 
    rw [List.prod_cons]
    apply one_lt_mul_of_lt_of_le' hl₁.1
    apply le_of_ltₓ ((b :: l).one_lt_prod_of_one_lt hl₁.2 (l.cons_ne_nil b))

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » l)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » l)
@[toAdditive]
theorem single_le_prod [OrderedCommMonoid α] {l : List α} (hl₁ : ∀ x _ : x ∈ l, (1 : α) ≤ x) :
  ∀ x _ : x ∈ l, x ≤ l.prod :=
  by 
    induction l
    ·
      simp 
    simpRw [prod_cons, forall_mem_cons]  at hl₁⊢
    constructor
    ·
      exact le_mul_of_one_le_right' (one_le_prod_of_one_le hl₁.2)
    ·
      exact fun x H => le_mul_of_one_le_of_le hl₁.1 (l_ih hl₁.right x H)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » l)
@[toAdditive all_zero_of_le_zero_le_of_sum_eq_zero]
theorem all_one_of_le_one_le_of_prod_eq_one [OrderedCommMonoid α] {l : List α} (hl₁ : ∀ x _ : x ∈ l, (1 : α) ≤ x)
  (hl₂ : l.prod = 1) {x : α} (hx : x ∈ l) : x = 1 :=
  le_antisymmₓ (hl₂ ▸ single_le_prod hl₁ _ hx) (hl₁ x hx)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » l)
theorem sum_eq_zero_iff [CanonicallyOrderedAddMonoid α] (l : List α) : l.sum = 0 ↔ ∀ x _ : x ∈ l, x = (0 : α) :=
  ⟨all_zero_of_le_zero_le_of_sum_eq_zero fun _ _ => zero_le _,
    by 
      induction l
      ·
        simp 
      ·
        intro h 
        rw [sum_cons, add_eq_zero_iff]
        rw [forall_mem_cons] at h 
        exact ⟨h.1, l_ih h.2⟩⟩

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (i «expr ∈ » L)
/-- If all elements in a list are bounded below by `1`, then the length of the list is bounded
by the sum of the elements. -/
theorem length_le_sum_of_one_le (L : List ℕ) (h : ∀ i _ : i ∈ L, 1 ≤ i) : L.length ≤ L.sum :=
  by 
    induction' L with j L IH h
    ·
      simp 
    rw [sum_cons, length, add_commₓ]
    exact add_le_add (h _ (Set.mem_insert _ _)) (IH fun i hi => h i (Set.mem_union_right _ hi))

/-- A list with positive sum must have positive length. -/
theorem length_pos_of_sum_pos [OrderedCancelAddCommMonoid α] (L : List α) (h : 0 < L.sum) : 0 < L.length :=
  length_pos_of_sum_ne_zero L h.ne'

theorem sum_le_foldr_max [AddMonoidₓ α] [AddMonoidₓ β] [LinearOrderₓ β] (f : α → β) (h0 : f 0 ≤ 0)
  (hadd : ∀ x y, f (x+y) ≤ max (f x) (f y)) (l : List α) : f l.sum ≤ (l.map f).foldr max 0 :=
  by 
    induction' l with hd tl IH
    ·
      simpa using h0 
    simp only [List.sum_cons, List.foldr_map, le_max_iff, List.foldr] at IH⊢
    cases le_or_ltₓ (f tl.sum) (f hd)
    ·
      left 
      refine' (hadd _ _).trans _ 
      simpa using h
    ·
      right 
      refine' (hadd _ _).trans _ 
      simp only [IH, max_le_iff, and_trueₓ, h.le.trans IH]

@[simp, toAdditive]
theorem prod_erase [DecidableEq α] [CommMonoidₓ α] {a} : ∀ {l : List α}, a ∈ l → (a*(l.erase a).Prod) = l.prod
| b :: l, h =>
  by 
    obtain rfl | ⟨ne, h⟩ := Decidable.List.eq_or_ne_mem_of_mem h
    ·
      simp only [List.eraseₓ, if_pos, prod_cons]
    ·
      simp only [List.eraseₓ, if_neg (mt Eq.symm Ne), prod_cons, prod_erase h, mul_left_commₓ a b]

theorem dvd_prod [CommMonoidₓ α] {a} {l : List α} (ha : a ∈ l) : a ∣ l.prod :=
  let ⟨s, t, h⟩ := mem_split ha 
  by 
    rw [h, prod_append, prod_cons, mul_left_commₓ]
    exact dvd_mul_right _ _

@[simp]
theorem sum_const_nat (m n : ℕ) : Sum (List.repeat m n) = m*n :=
  by 
    induction n <;> [rfl, simp only [repeat_succ, sum_cons, Nat.mul_succ, add_commₓ]]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » l)
theorem dvd_sum [CommSemiringₓ α] {a} {l : List α} (h : ∀ x _ : x ∈ l, a ∣ x) : a ∣ l.sum :=
  by 
    induction' l with x l ih
    ·
      exact dvd_zero _
    ·
      rw [List.sum_cons]
      exact dvd_add (h _ (mem_cons_self _ _)) (ih fun x hx => h x (mem_cons_of_mem _ hx))

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » l)
theorem exists_lt_of_sum_lt [LinearOrderedCancelAddCommMonoid β] {l : List α} (f g : α → β)
  (h : (l.map f).Sum < (l.map g).Sum) : ∃ (x : _)(_ : x ∈ l), f x < g x :=
  by 
    induction' l with x l
    ·
      exact (lt_irreflₓ _ h).elim 
    obtain h' | h' := lt_or_leₓ (f x) (g x)
    ·
      exact ⟨x, mem_cons_self _ _, h'⟩
    simp  at h 
    obtain ⟨y, h1y, h2y⟩ := l_ih (lt_of_add_lt_add_left (h.trans_le$ add_le_add_right h' _))
    exact ⟨y, mem_cons_of_mem x h1y, h2y⟩

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » l)
theorem exists_le_of_sum_le [LinearOrderedCancelAddCommMonoid β] {l : List α} (hl : l ≠ []) (f g : α → β)
  (h : (l.map f).Sum ≤ (l.map g).Sum) : ∃ (x : _)(_ : x ∈ l), f x ≤ g x :=
  by 
    cases' l with x l
    ·
      contradiction 
    obtain h' | h' := le_or_ltₓ (f x) (g x)
    ·
      exact ⟨x, mem_cons_self _ _, h'⟩
    obtain ⟨y, h1y, h2y⟩ := exists_lt_of_sum_lt f g _ 
    exact ⟨y, mem_cons_of_mem x h1y, le_of_ltₓ h2y⟩
    simp  at h 
    exact lt_of_add_lt_add_left (h.trans_lt$ add_lt_add_right h' _)

/-- We'd like to state this as `L.head * L.tail.prod = L.prod`, but because `L.head` relies on an
inhabited instance to return a garbage value on the empty list, this is not possible.
Instead, we write the statement in terms of `(L.nth 0).get_or_else 1` and state the lemma for `ℕ` as
 -/
@[toAdditive]
theorem nth_zero_mul_tail_prod [Monoidₓ α] (l : List α) : ((l.nth 0).getOrElse 1*l.tail.prod) = l.prod :=
  by 
    cases l <;> simp 

/-- Same as `nth_zero_mul_tail_prod`, but avoiding the `list.head` garbage complication by requiring
the list to be nonempty. -/
@[toAdditive]
theorem head_mul_tail_prod_of_ne_nil [Monoidₓ α] [Inhabited α] (l : List α) (h : l ≠ []) :
  (l.head*l.tail.prod) = l.prod :=
  by 
    cases l <;> [contradiction, simp ]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (a «expr ∈ » l)
/-- The product of a list of positive natural numbers is positive,
and likewise for any nontrivial ordered semiring. -/
theorem prod_pos [OrderedSemiring α] [Nontrivial α] (l : List α) (h : ∀ a _ : a ∈ l, (0 : α) < a) : 0 < l.prod :=
  by 
    induction' l with a l ih
    ·
      simp 
    ·
      rw [prod_cons]
      exact mul_pos (h _$ mem_cons_self _ _) (ih$ fun a ha => h a$ mem_cons_of_mem _ ha)

/-!
Several lemmas about sum/head/tail for `list ℕ`.
These are hard to generalize well, as they rely on the fact that `default ℕ = 0`.
If desired, we could add a class stating that `default α = 0`.
-/


/-- This relies on `default ℕ = 0`. -/
theorem head_add_tail_sum (L : List ℕ) : (L.head+L.tail.sum) = L.sum :=
  by 
    cases L
    ·
      simp 
      rfl
    ·
      simp 

/-- This relies on `default ℕ = 0`. -/
theorem head_le_sum (L : List ℕ) : L.head ≤ L.sum :=
  Nat.Le.intro (head_add_tail_sum L)

/-- This relies on `default ℕ = 0`. -/
theorem tail_sum (L : List ℕ) : L.tail.sum = L.sum - L.head :=
  by 
    rw [←head_add_tail_sum L, add_commₓ, add_tsub_cancel_right]

section Alternating

variable {G : Type _} [CommGroupₓ G]

@[simp, toAdditive]
theorem alternating_prod_nil : alternating_prod ([] : List G) = 1 :=
  rfl

@[simp, toAdditive]
theorem alternating_prod_singleton (g : G) : alternating_prod [g] = g :=
  rfl

@[simp, toAdditive alternating_sum_cons_cons']
theorem alternating_prod_cons_cons (g h : G) (l : List G) :
  alternating_prod (g :: h :: l) = (g*h⁻¹)*alternating_prod l :=
  rfl

theorem alternating_sum_cons_cons {G : Type _} [AddCommGroupₓ G] (g h : G) (l : List G) :
  alternating_sum (g :: h :: l) = (g - h)+alternating_sum l :=
  by 
    rw [sub_eq_add_neg, alternating_sum]

end Alternating

@[toAdditive]
theorem _root_.monoid_hom.map_list_prod [Monoidₓ α] [Monoidₓ β] (f : α →* β) (l : List α) : f l.prod = (l.map f).Prod :=
  (l.prod_hom f).symm

open MulOpposite

/-- A morphism into the opposite monoid acts on the product by acting on the reversed elements -/
theorem _root_.monoid_hom.unop_map_list_prod {α β : Type _} [Monoidₓ α] [Monoidₓ β] (f : α →* βᵐᵒᵖ) (l : List α) :
  unop (f l.prod) = (l.map (unop ∘ f)).reverse.Prod :=
  by 
    rw [f.map_list_prod l, unop_list_prod, List.map_mapₓ]

@[toAdditive]
theorem prod_map_hom [Monoidₓ β] [Monoidₓ γ] (L : List α) (f : α → β) (g : β →* γ) :
  (L.map (g ∘ f)).Prod = g (L.map f).Prod :=
  by 
    rw [g.map_list_prod]
    exact congr_argₓ _ (map_map _ _ _).symm

theorem sum_map_mul_left [Semiringₓ α] (L : List β) (f : β → α) (r : α) :
  (L.map fun b => r*f b).Sum = r*(L.map f).Sum :=
  sum_map_hom L f$ AddMonoidHom.mulLeft r

theorem sum_map_mul_right [Semiringₓ α] (L : List β) (f : β → α) (r : α) :
  (L.map fun b => f b*r).Sum = (L.map f).Sum*r :=
  sum_map_hom L f$ AddMonoidHom.mulRight r

end List

