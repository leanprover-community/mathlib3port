/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel
-/
import Mathbin.Data.List.Basic

/-!
# Sums and products from lists

This file provides basic results about `list.prod` and `list.sum`, which calculate the product and
sum of elements of a list. These are defined in [`data.list.defs`](./data/list/defs).
-/


variable {ι M N P M₀ G R : Type _}

namespace List

section Monoidₓ

variable [Monoidₓ M] [Monoidₓ N] [Monoidₓ P] {l l₁ l₂ : List M} {a : M}

@[simp, to_additive]
theorem prod_nil : ([] : List M).Prod = 1 :=
  rfl

@[to_additive]
theorem prod_singleton : [a].Prod = a :=
  one_mulₓ a

@[simp, to_additive]
theorem prod_cons : (a :: l).Prod = a * l.Prod :=
  calc
    (a :: l).Prod = foldlₓ (· * ·) (a * 1) l := by
      simp only [List.prod, foldl_cons, one_mulₓ, mul_oneₓ]
    _ = _ := foldl_assoc
    

@[simp, to_additive]
theorem prod_append : (l₁ ++ l₂).Prod = l₁.Prod * l₂.Prod :=
  calc
    (l₁ ++ l₂).Prod = foldlₓ (· * ·) (foldlₓ (· * ·) 1 l₁ * 1) l₂ := by
      simp [List.prod]
    _ = l₁.Prod * l₂.Prod := foldl_assoc
    

@[to_additive]
theorem prod_concat : (l.concat a).Prod = l.Prod * a := by
  rw [concat_eq_append, prod_append, prod_singleton]

@[simp, to_additive]
theorem prod_join {l : List (List M)} : l.join.Prod = (l.map List.prod).Prod := by
  induction l <;> [rfl, simp only [*, List.join, map, prod_append, prod_cons]]

@[to_additive]
theorem prod_eq_foldr : l.Prod = foldr (· * ·) 1 l :=
  (List.recOn l rfl) fun a l ihl => by
    rw [prod_cons, foldr_cons, ihl]

@[to_additive]
theorem prod_hom_rel (l : List ι) {r : M → N → Prop} {f : ι → M} {g : ι → N} (h₁ : r 1 1)
    (h₂ : ∀ ⦃i a b⦄, r a b → r (f i * a) (g i * b)) : r (l.map f).Prod (l.map g).Prod :=
  List.recOn l h₁ fun a l hl => by
    simp only [map_cons, prod_cons, h₂ hl]

@[to_additive]
theorem prod_hom (l : List M) (f : M →* N) : (l.map f).Prod = f l.Prod := by
  simp only [Prod, foldl_map, f.map_one.symm]
  exact l.foldl_hom _ _ _ 1 f.map_mul

@[to_additive]
theorem prod_hom₂ (l : List ι) (f : M → N → P) (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (hf' : f 1 1 = 1)
    (f₁ : ι → M) (f₂ : ι → N) : (l.map fun i => f (f₁ i) (f₂ i)).Prod = f (l.map f₁).Prod (l.map f₂).Prod := by
  simp only [Prod, foldl_map]
  convert l.foldl_hom₂ (fun a b => f a b) _ _ _ _ _ fun a b i => _
  · exact hf'.symm
    
  · exact hf _ _ _ _
    

@[simp, to_additive]
theorem prod_map_mul {α : Type _} [CommMonoidₓ α] {l : List ι} {f g : ι → α} :
    (l.map fun i => f i * g i).Prod = (l.map f).Prod * (l.map g).Prod :=
  l.prod_hom₂ (· * ·) mul_mul_mul_commₓ (mul_oneₓ _) _ _

@[to_additive]
theorem prod_map_hom (L : List ι) (f : ι → M) (g : M →* N) : (L.map (g ∘ f)).Prod = g (L.map f).Prod := by
  rw [← prod_hom, map_map]

@[to_additive]
theorem prod_is_unit : ∀ {L : List M} u : ∀, ∀ m ∈ L, ∀, IsUnit m, IsUnit L.Prod
  | [], _ => by
    simp
  | h :: t, u => by
    simp only [List.prod_cons]
    exact IsUnit.mul (u h (mem_cons_self h t)) (prod_is_unit fun m mt => u m (mem_cons_of_mem h mt))

@[simp, to_additive]
theorem prod_take_mul_prod_drop : ∀ L : List M i : ℕ, (L.take i).Prod * (L.drop i).Prod = L.Prod
  | [], i => by
    simp
  | L, 0 => by
    simp
  | h :: t, n + 1 => by
    dsimp
    rw [prod_cons, prod_cons, mul_assoc, prod_take_mul_prod_drop]

@[simp, to_additive]
theorem prod_take_succ : ∀ L : List M i : ℕ p, (L.take (i + 1)).Prod = (L.take i).Prod * L.nthLe i p
  | [], i, p => by
    cases p
  | h :: t, 0, _ => by
    simp
  | h :: t, n + 1, _ => by
    dsimp
    rw [prod_cons, prod_cons, prod_take_succ, mul_assoc]

/-- A list with product not one must have positive length. -/
@[to_additive]
theorem length_pos_of_prod_ne_one (L : List M) (h : L.Prod ≠ 1) : 0 < L.length := by
  cases L
  · simp at h
    cases h
    
  · simp
    

@[to_additive]
theorem prod_update_nth :
    ∀ L : List M n : ℕ a : M,
      (L.updateNth n a).Prod = ((L.take n).Prod * if n < L.length then a else 1) * (L.drop (n + 1)).Prod
  | x :: xs, 0, a => by
    simp [update_nth]
  | x :: xs, i + 1, a => by
    simp [update_nth, prod_update_nth xs i a, mul_assoc]
  | [], _, _ => by
    simp [update_nth, (Nat.zero_leₓ _).not_lt]

open MulOpposite

/-- We'd like to state this as `L.head * L.tail.prod = L.prod`, but because `L.head` relies on an
inhabited instance to return a garbage value on the empty list, this is not possible.
Instead, we write the statement in terms of `(L.nth 0).get_or_else 1`.
-/
@[to_additive]
theorem nth_zero_mul_tail_prod (l : List M) : (l.nth 0).getOrElse 1 * l.tail.Prod = l.Prod := by
  cases l <;> simp

/-- Same as `nth_zero_mul_tail_prod`, but avoiding the `list.head` garbage complication by requiring
the list to be nonempty. -/
@[to_additive]
theorem head_mul_tail_prod_of_ne_nil [Inhabited M] (l : List M) (h : l ≠ []) : l.head * l.tail.Prod = l.Prod := by
  cases l <;> [contradiction, simp ]

end Monoidₓ

section MonoidWithZeroₓ

variable [MonoidWithZeroₓ M₀]

/-- If zero is an element of a list `L`, then `list.prod L = 0`. If the domain is a nontrivial
monoid with zero with no divisors, then this implication becomes an `iff`, see
`list.prod_eq_zero_iff`. -/
theorem prod_eq_zero {L : List M₀} (h : (0 : M₀) ∈ L) : L.Prod = 0 := by
  induction' L with a L ihL
  · exact absurd h (not_mem_nil _)
    
  · rw [prod_cons]
    cases' (mem_cons_iff _ _ _).1 h with ha hL
    exacts[mul_eq_zero_of_left ha.symm _, mul_eq_zero_of_right _ (ihL hL)]
    

/-- Product of elements of a list `L` equals zero if and only if `0 ∈ L`. See also
`list.prod_eq_zero` for an implication that needs weaker typeclass assumptions. -/
@[simp]
theorem prod_eq_zero_iff [Nontrivial M₀] [NoZeroDivisors M₀] {L : List M₀} : L.Prod = 0 ↔ (0 : M₀) ∈ L := by
  induction' L with a L ihL
  · simp
    
  · rw [prod_cons, mul_eq_zero, ihL, mem_cons_iff, eq_comm]
    

theorem prod_ne_zero [Nontrivial M₀] [NoZeroDivisors M₀] {L : List M₀} (hL : (0 : M₀) ∉ L) : L.Prod ≠ 0 :=
  mt prod_eq_zero_iff.1 hL

end MonoidWithZeroₓ

section Groupₓ

variable [Groupₓ G]

/-- This is the `list.prod` version of `mul_inv_rev` -/
@[to_additive "This is the `list.sum` version of `add_neg_rev`"]
theorem prod_inv_reverse : ∀ L : List G, L.Prod⁻¹ = (L.map fun x => x⁻¹).reverse.Prod
  | [] => by
    simp
  | x :: xs => by
    simp [prod_inv_reverse xs]

/-- A non-commutative variant of `list.prod_reverse` -/
@[to_additive "A non-commutative variant of `list.sum_reverse`"]
theorem prod_reverse_noncomm : ∀ L : List G, L.reverse.Prod = (L.map fun x => x⁻¹).Prod⁻¹ := by
  simp [prod_inv_reverse]

/-- Counterpart to `list.prod_take_succ` when we have an inverse operation -/
@[simp, to_additive "Counterpart to `list.sum_take_succ` when we have an negation operation"]
theorem prod_drop_succ : ∀ L : List G i : ℕ p, (L.drop (i + 1)).Prod = (L.nthLe i p)⁻¹ * (L.drop i).Prod
  | [], i, p => False.elim (Nat.not_lt_zeroₓ _ p)
  | x :: xs, 0, p => by
    simp
  | x :: xs, i + 1, p => prod_drop_succ xs i _

end Groupₓ

section CommGroupₓ

variable [CommGroupₓ G]

/-- This is the `list.prod` version of `mul_inv` -/
@[to_additive "This is the `list.sum` version of `add_neg`"]
theorem prod_inv : ∀ L : List G, L.Prod⁻¹ = (L.map fun x => x⁻¹).Prod
  | [] => by
    simp
  | x :: xs => by
    simp [mul_comm, prod_inv xs]

/-- Alternative version of `list.prod_update_nth` when the list is over a group -/
@[to_additive "Alternative version of `list.sum_update_nth` when the list is over a group"]
theorem prod_update_nth' (L : List G) (n : ℕ) (a : G) :
    (L.updateNth n a).Prod = L.Prod * if hn : n < L.length then (L.nthLe n hn)⁻¹ * a else 1 := by
  refine' (prod_update_nth L n a).trans _
  split_ifs with hn hn
  · rw [mul_comm _ a, mul_assoc a, prod_drop_succ L n hn, mul_comm _ (drop n L).Prod, ← mul_assoc (take n L).Prod,
      prod_take_mul_prod_drop, mul_comm a, mul_assoc]
    
  · simp only [take_all_of_le (le_of_not_ltₓ hn), prod_nil, mul_oneₓ,
      drop_eq_nil_of_le ((le_of_not_ltₓ hn).trans n.le_succ)]
    

end CommGroupₓ

theorem eq_of_sum_take_eq [AddLeftCancelMonoid M] {L L' : List M} (h : L.length = L'.length)
    (h' : ∀, ∀ i ≤ L.length, ∀, (L.take i).Sum = (L'.take i).Sum) : L = L' := by
  apply ext_le h fun i h₁ h₂ => _
  have : (L.take (i + 1)).Sum = (L'.take (i + 1)).Sum := h' _ (Nat.succ_le_of_ltₓ h₁)
  rw [sum_take_succ L i h₁, sum_take_succ L' i h₂, h' i (le_of_ltₓ h₁)] at this
  exact add_left_cancelₓ this

theorem monotone_sum_take [CanonicallyOrderedAddMonoid M] (L : List M) : Monotone fun i => (L.take i).Sum := by
  apply monotone_nat_of_le_succ fun n => _
  by_cases' h : n < L.length
  · rw [sum_take_succ _ _ h]
    exact le_self_add
    
  · push_neg  at h
    simp [take_all_of_le h, take_all_of_le (le_transₓ h (Nat.le_succₓ _))]
    

@[to_additive sum_nonneg]
theorem one_le_prod_of_one_le [OrderedCommMonoid M] {l : List M} (hl₁ : ∀, ∀ x ∈ l, ∀, (1 : M) ≤ x) : 1 ≤ l.Prod := by
  induction' l with hd tl ih
  · simp
    
  rw [prod_cons]
  exact one_le_mul (hl₁ hd (mem_cons_self hd tl)) (ih fun x h => hl₁ x (mem_cons_of_mem hd h))

@[to_additive sum_pos]
theorem one_lt_prod_of_one_lt [OrderedCommMonoid M] :
    ∀ l : List M hl : ∀, ∀ x ∈ l, ∀, (1 : M) < x hl₂ : l ≠ [], 1 < l.Prod
  | [], _, h => (h rfl).elim
  | [b], h, _ => by
    simpa using h
  | a :: b :: l, hl₁, hl₂ => by
    simp only [forall_eq_or_imp, List.mem_cons_iff _ a] at hl₁
    rw [List.prod_cons]
    apply one_lt_mul_of_lt_of_le' hl₁.1
    apply le_of_ltₓ ((b :: l).one_lt_prod_of_one_lt hl₁.2 (l.cons_ne_nil b))

@[to_additive]
theorem single_le_prod [OrderedCommMonoid M] {l : List M} (hl₁ : ∀, ∀ x ∈ l, ∀, (1 : M) ≤ x) :
    ∀, ∀ x ∈ l, ∀, x ≤ l.Prod := by
  induction l
  · simp
    
  simp_rw [prod_cons, forall_mem_cons]  at hl₁⊢
  constructor
  · exact le_mul_of_one_le_right' (one_le_prod_of_one_le hl₁.2)
    
  · exact fun x H => le_mul_of_one_le_of_le hl₁.1 (l_ih hl₁.right x H)
    

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
theorem all_one_of_le_one_le_of_prod_eq_one [OrderedCommMonoid M] {l : List M} (hl₁ : ∀, ∀ x ∈ l, ∀, (1 : M) ≤ x)
    (hl₂ : l.Prod = 1) {x : M} (hx : x ∈ l) : x = 1 :=
  le_antisymmₓ (hl₂ ▸ single_le_prod hl₁ _ hx) (hl₁ x hx)

@[to_additive]
theorem prod_eq_one_iff [CanonicallyOrderedMonoid M] (l : List M) : l.Prod = 1 ↔ ∀, ∀ x ∈ l, ∀, x = (1 : M) :=
  ⟨all_one_of_le_one_le_of_prod_eq_one fun _ _ => one_le _, by
    induction l
    · simp
      
    · intro h
      rw [prod_cons, mul_eq_one_iff]
      rw [forall_mem_cons] at h
      exact ⟨h.1, l_ih h.2⟩
      ⟩

/-- If all elements in a list are bounded below by `1`, then the length of the list is bounded
by the sum of the elements. -/
theorem length_le_sum_of_one_le (L : List ℕ) (h : ∀, ∀ i ∈ L, ∀, 1 ≤ i) : L.length ≤ L.Sum := by
  induction' L with j L IH h
  · simp
    
  rw [sum_cons, length, add_commₓ]
  exact add_le_add (h _ (Set.mem_insert _ _)) (IH fun i hi => h i (Set.mem_union_right _ hi))

/-- A list with positive sum must have positive length. -/
-- This is an easy consequence of `length_pos_of_sum_ne_zero`, but often useful in applications.
theorem length_pos_of_sum_pos [OrderedCancelAddCommMonoid M] (L : List M) (h : 0 < L.Sum) : 0 < L.length :=
  length_pos_of_sum_ne_zero L h.ne'

-- TODO: develop theory of tropical rings
theorem sum_le_foldr_max [AddMonoidₓ M] [AddMonoidₓ N] [LinearOrderₓ N] (f : M → N) (h0 : f 0 ≤ 0)
    (hadd : ∀ x y, f (x + y) ≤ max (f x) (f y)) (l : List M) : f l.Sum ≤ (l.map f).foldr max 0 := by
  induction' l with hd tl IH
  · simpa using h0
    
  simp only [List.sum_cons, List.foldr_map, le_max_iff, List.foldr] at IH⊢
  cases le_or_ltₓ (f tl.sum) (f hd)
  · left
    refine' (hadd _ _).trans _
    simpa using h
    
  · right
    refine' (hadd _ _).trans _
    simp only [IH, max_le_iff, and_trueₓ, h.le.trans IH]
    

@[simp, to_additive]
theorem prod_erase [DecidableEq M] [CommMonoidₓ M] {a} : ∀ {l : List M}, a ∈ l → a * (l.erase a).Prod = l.Prod
  | b :: l, h => by
    obtain rfl | ⟨ne, h⟩ := Decidable.List.eq_or_ne_mem_of_mem h
    · simp only [List.eraseₓ, if_pos, prod_cons]
      
    · simp only [List.eraseₓ, if_neg (mt Eq.symm Ne), prod_cons, prod_erase h, mul_left_commₓ a b]
      

theorem dvd_prod [CommMonoidₓ M] {a} {l : List M} (ha : a ∈ l) : a ∣ l.Prod := by
  let ⟨s, t, h⟩ := mem_split ha
  rw [h, prod_append, prod_cons, mul_left_commₓ]
  exact dvd_mul_right _ _

@[simp]
theorem sum_const_nat (m n : ℕ) : sum (List.repeat m n) = m * n := by
  induction n <;> [rfl, simp only [*, repeat_succ, sum_cons, Nat.mul_succ, add_commₓ]]

theorem dvd_sum [Semiringₓ R] {a} {l : List R} (h : ∀, ∀ x ∈ l, ∀, a ∣ x) : a ∣ l.Sum := by
  induction' l with x l ih
  · exact dvd_zero _
    
  · rw [List.sum_cons]
    exact dvd_add (h _ (mem_cons_self _ _)) (ih fun x hx => h x (mem_cons_of_mem _ hx))
    

theorem exists_lt_of_sum_lt [LinearOrderedCancelAddCommMonoid M] {l : List ι} (f g : ι → M)
    (h : (l.map f).Sum < (l.map g).Sum) : ∃ x ∈ l, f x < g x := by
  induction' l with x l
  · exact (lt_irreflₓ _ h).elim
    
  obtain h' | h' := lt_or_leₓ (f x) (g x)
  · exact ⟨x, mem_cons_self _ _, h'⟩
    
  simp at h
  obtain ⟨y, h1y, h2y⟩ := l_ih (lt_of_add_lt_add_left (h.trans_le <| add_le_add_right h' _))
  exact ⟨y, mem_cons_of_mem x h1y, h2y⟩

theorem exists_le_of_sum_le [LinearOrderedCancelAddCommMonoid M] {l : List ι} (hl : l ≠ []) (f g : ι → M)
    (h : (l.map f).Sum ≤ (l.map g).Sum) : ∃ x ∈ l, f x ≤ g x := by
  cases' l with x l
  · contradiction
    
  obtain h' | h' := le_or_ltₓ (f x) (g x)
  · exact ⟨x, mem_cons_self _ _, h'⟩
    
  obtain ⟨y, h1y, h2y⟩ := exists_lt_of_sum_lt f g _
  exact ⟨y, mem_cons_of_mem x h1y, le_of_ltₓ h2y⟩
  simp at h
  exact lt_of_add_lt_add_left (h.trans_lt <| add_lt_add_right h' _)

/-- The product of a list of positive natural numbers is positive,
and likewise for any nontrivial ordered semiring. -/
theorem prod_pos [OrderedSemiring R] [Nontrivial R] (l : List R) (h : ∀, ∀ a ∈ l, ∀, (0 : R) < a) : 0 < l.Prod := by
  induction' l with a l ih
  · simp
    
  · rw [prod_cons]
    exact mul_pos (h _ <| mem_cons_self _ _) (ih fun a ha => h a <| mem_cons_of_mem _ ha)
    

/-!
Several lemmas about sum/head/tail for `list ℕ`.
These are hard to generalize well, as they rely on the fact that `default ℕ = 0`.
If desired, we could add a class stating that `default = 0`.
-/


/-- This relies on `default ℕ = 0`. -/
theorem head_add_tail_sum (L : List ℕ) : L.head + L.tail.Sum = L.Sum := by
  cases L
  · simp
    rfl
    
  · simp
    

/-- This relies on `default ℕ = 0`. -/
theorem head_le_sum (L : List ℕ) : L.head ≤ L.Sum :=
  Nat.Le.intro (head_add_tail_sum L)

/-- This relies on `default ℕ = 0`. -/
theorem tail_sum (L : List ℕ) : L.tail.Sum = L.Sum - L.head := by
  rw [← head_add_tail_sum L, add_commₓ, add_tsub_cancel_right]

section Alternating

variable [CommGroupₓ G]

@[simp, to_additive]
theorem alternating_prod_nil : alternatingProd ([] : List G) = 1 :=
  rfl

@[simp, to_additive]
theorem alternating_prod_singleton (g : G) : alternatingProd [g] = g :=
  rfl

@[simp, to_additive alternating_sum_cons_cons']
theorem alternating_prod_cons_cons (g h : G) (l : List G) :
    alternatingProd (g :: h :: l) = g * h⁻¹ * alternatingProd l :=
  rfl

theorem alternating_sum_cons_cons {G : Type _} [AddCommGroupₓ G] (g h : G) (l : List G) :
    alternatingSum (g :: h :: l) = g - h + alternatingSum l := by
  rw [sub_eq_add_neg, alternating_sum]

end Alternating

theorem sum_map_mul_left [Semiringₓ R] (L : List ι) (f : ι → R) (r : R) :
    (L.map fun b => r * f b).Sum = r * (L.map f).Sum :=
  sum_map_hom L f <| AddMonoidHom.mulLeft r

theorem sum_map_mul_right [Semiringₓ R] (L : List ι) (f : ι → R) (r : R) :
    (L.map fun b => f b * r).Sum = (L.map f).Sum * r :=
  sum_map_hom L f <| AddMonoidHom.mulRight r

end List

namespace MulOpposite

open List

variable [Monoidₓ M]

theorem op_list_prod : ∀ l : List M, op l.Prod = (l.map op).reverse.Prod
  | [] => rfl
  | x :: xs => by
    rw [List.prod_cons, List.map_cons, List.reverse_cons', List.prod_concat, op_mul, op_list_prod]

theorem _root_.mul_opposite.unop_list_prod (l : List Mᵐᵒᵖ) : l.Prod.unop = (l.map unop).reverse.Prod := by
  rw [← op_inj, op_unop, MulOpposite.op_list_prod, map_reverse, map_map, reverse_reverse, op_comp_unop, map_id]

end MulOpposite

namespace MonoidHom

variable [Monoidₓ M] [Monoidₓ N]

@[to_additive]
theorem map_list_prod (f : M →* N) (l : List M) : f l.Prod = (l.map f).Prod :=
  (l.prod_hom f).symm

/-- A morphism into the opposite monoid acts on the product by acting on the reversed elements -/
theorem unop_map_list_prod (f : M →* Nᵐᵒᵖ) (l : List M) :
    (f l.Prod).unop = (l.map (MulOpposite.unop ∘ f)).reverse.Prod := by
  rw [f.map_list_prod l, MulOpposite.unop_list_prod, List.map_mapₓ]

end MonoidHom

