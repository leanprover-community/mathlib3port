import Mathbin.Algebra.BigOperators.Basic

/-!
# Products (respectively, sums) over a finset or a multiset.

The regular `finset.prod` and `multiset.prod` require `[comm_monoid α]`.
Often, there are collections `s : finset α` where `[monoid α]` and we know,
in a dependent fashion, that for all the terms `∀ (x ∈ s) (y ∈ s), commute x y`.
This allows to still have a well-defined product over `s`.

## Main definitions

- `finset.noncomm_prod`, requiring a proof of commutativity of held terms
- `multiset.noncomm_prod`, requiring a proof of commutativity of held terms

## Implementation details

While `list.prod` is defined via `list.foldl`, `noncomm_prod` is defined via
`multiset.foldr` for neater proofs and definitions. By the commutativity assumption,
the two must be equal.

-/


variable {α β : Type _} (f : α → β → β) (op : α → α → α)

namespace Multiset

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » s)
/-- Fold of a `s : multiset α` with `f : α → β → β`, given a proof that `left_commutative f`
on all elements `x ∈ s`. -/
def noncomm_foldr (s : Multiset α) (comm : ∀ x _ : x ∈ s y _ : y ∈ s b, f x (f y b) = f y (f x b)) (b : β) : β :=
  s.attach.foldr (f ∘ Subtype.val) (fun ⟨x, hx⟩ ⟨y, hy⟩ => comm x hx y hy) b

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » (l : multiset α))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » (l : multiset α))
@[simp]
theorem noncomm_foldr_coe (l : List α)
  (comm : ∀ x _ : x ∈ (l : Multiset α) y _ : y ∈ (l : Multiset α) b, f x (f y b) = f y (f x b)) (b : β) :
  noncomm_foldr f (l : Multiset α) comm b = l.foldr f b :=
  by 
    simp only [noncomm_foldr, coe_foldr, coe_attach, List.attach]
    rw [←List.foldr_map]
    simp [List.map_pmap, List.pmap_eq_map]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » (0 : multiset α))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » (0 : multiset α))
@[simp]
theorem noncomm_foldr_empty (h : ∀ x _ : x ∈ (0 : Multiset α) y _ : y ∈ (0 : Multiset α) b, f x (f y b) = f y (f x b))
  (b : β) : noncomm_foldr f (0 : Multiset α) h b = b :=
  rfl

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » «expr ::ₘ »(a, s))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » «expr ::ₘ »(a, s))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » s)
theorem noncomm_foldr_cons (s : Multiset α) (a : α)
  (h : ∀ x _ : x ∈ a ::ₘ s y _ : y ∈ a ::ₘ s b, f x (f y b) = f y (f x b))
  (h' : ∀ x _ : x ∈ s y _ : y ∈ s b, f x (f y b) = f y (f x b)) (b : β) :
  noncomm_foldr f (a ::ₘ s) h b = f a (noncomm_foldr f s h' b) :=
  by 
    induction s using Quotientₓ.induction_on 
    simp 

theorem noncomm_foldr_eq_foldr (s : Multiset α) (h : LeftCommutative f) (b : β) :
  noncomm_foldr f s (fun x _ y _ => h x y) b = foldr f h b s :=
  by 
    induction s using Quotientₓ.induction_on 
    simp 

variable [assoc : IsAssociative α op]

include assoc

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » s)
/-- Fold of a `s : multiset α` with an associative `op : α → α → α`, given a proofs that `op`
is commutative on all elements `x ∈ s`. -/
def noncomm_fold (s : Multiset α) (comm : ∀ x _ : x ∈ s y _ : y ∈ s, op x y = op y x) (a : α) : α :=
  noncomm_foldr op s
    (fun x hx y hy b =>
      by 
        rw [←assoc.assoc, comm _ hx _ hy, assoc.assoc])
    a

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » (l : multiset α))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » (l : multiset α))
@[simp]
theorem noncomm_fold_coe (l : List α) (comm : ∀ x _ : x ∈ (l : Multiset α) y _ : y ∈ (l : Multiset α), op x y = op y x)
  (a : α) : noncomm_fold op (l : Multiset α) comm a = l.foldr op a :=
  by 
    simp [noncomm_fold]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » (0 : multiset α))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » (0 : multiset α))
@[simp]
theorem noncomm_fold_empty (h : ∀ x _ : x ∈ (0 : Multiset α) y _ : y ∈ (0 : Multiset α), op x y = op y x) (a : α) :
  noncomm_fold op (0 : Multiset α) h a = a :=
  rfl

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » «expr ::ₘ »(a, s))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » «expr ::ₘ »(a, s))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » s)
theorem noncomm_fold_cons (s : Multiset α) (a : α) (h : ∀ x _ : x ∈ a ::ₘ s y _ : y ∈ a ::ₘ s, op x y = op y x)
  (h' : ∀ x _ : x ∈ s y _ : y ∈ s, op x y = op y x) (x : α) :
  noncomm_fold op (a ::ₘ s) h x = op a (noncomm_fold op s h' x) :=
  by 
    induction s using Quotientₓ.induction_on 
    simp 

theorem noncomm_fold_eq_fold (s : Multiset α) [IsCommutative α op] (a : α) :
  noncomm_fold op s (fun x _ y _ => IsCommutative.comm x y) a = fold op a s :=
  by 
    induction s using Quotientₓ.induction_on 
    simp 

omit assoc

variable [Monoidₓ α]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » s)
/-- Product of a `s : multiset α` with `[monoid α]`, given a proof that `*` commutes
on all elements `x ∈ s`. -/
@[toAdditive
      "Sum of a `s : multiset α` with `[add_monoid α]`, given a proof that `+` commutes\non all elements `x ∈ s`."]
def noncomm_prod (s : Multiset α) (comm : ∀ x _ : x ∈ s y _ : y ∈ s, Commute x y) : α :=
  s.noncomm_fold (·*·) comm 1

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » (l : multiset α))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » (l : multiset α))
@[simp, toAdditive]
theorem noncomm_prod_coe (l : List α) (comm : ∀ x _ : x ∈ (l : Multiset α) y _ : y ∈ (l : Multiset α), Commute x y) :
  noncomm_prod (l : Multiset α) comm = l.prod :=
  by 
    rw [noncomm_prod]
    simp only [noncomm_fold_coe]
    induction' l with hd tl hl
    ·
      simp 
    ·
      rw [List.prod_cons, List.foldr, hl]
      intro x hx y hy 
      exact comm x (List.mem_cons_of_memₓ _ hx) y (List.mem_cons_of_memₓ _ hy)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » (0 : multiset α))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » (0 : multiset α))
@[simp, toAdditive]
theorem noncomm_prod_empty (h : ∀ x _ : x ∈ (0 : Multiset α) y _ : y ∈ (0 : Multiset α), Commute x y) :
  noncomm_prod (0 : Multiset α) h = 1 :=
  rfl

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » «expr ::ₘ »(a, s))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » «expr ::ₘ »(a, s))
@[simp, toAdditive]
theorem noncomm_prod_cons (s : Multiset α) (a : α) (comm : ∀ x _ : x ∈ a ::ₘ s y _ : y ∈ a ::ₘ s, Commute x y) :
  noncomm_prod (a ::ₘ s) comm = a*noncomm_prod s fun x hx y hy => comm _ (mem_cons_of_mem hx) _ (mem_cons_of_mem hy) :=
  by 
    induction s using Quotientₓ.induction_on 
    simp 

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » «expr ::ₘ »(a, s))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » «expr ::ₘ »(a, s))
@[toAdditive]
theorem noncomm_prod_cons' (s : Multiset α) (a : α) (comm : ∀ x _ : x ∈ a ::ₘ s y _ : y ∈ a ::ₘ s, Commute x y) :
  noncomm_prod (a ::ₘ s) comm =
    (noncomm_prod s fun x hx y hy => comm _ (mem_cons_of_mem hx) _ (mem_cons_of_mem hy))*a :=
  by 
    induction' s using Quotientₓ.induction_on with s 
    simp only [quot_mk_to_coe, cons_coe, noncomm_prod_coe, List.prod_cons]
    induction' s with hd tl IH
    ·
      simp 
    ·
      rw [List.prod_cons, mul_assocₓ, ←IH, ←mul_assocₓ, ←mul_assocₓ]
      ·
        congr 1
        apply comm <;> simp 
      ·
        intro x hx y hy 
        simp only [quot_mk_to_coe, List.mem_cons_iffₓ, mem_coe, cons_coe] at hx hy 
        apply comm
        ·
          cases hx <;> simp [hx]
        ·
          cases hy <;> simp [hy]

@[toAdditive]
theorem noncomm_prod_eq_prod {α : Type _} [CommMonoidₓ α] (s : Multiset α) :
  (noncomm_prod s fun _ _ _ _ => Commute.all _ _) = Prod s :=
  by 
    induction s using Quotientₓ.induction_on 
    simp 

end Multiset

namespace Finset

variable [Monoidₓ β]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » s)
/-- Product of a `s : finset α` mapped with `f : α → β` with `[monoid β]`,
given a proof that `*` commutes on all elements `f x` for `x ∈ s`. -/
@[toAdditive
      "Sum of a `s : finset α` mapped with `f : α → β` with `[add_monoid β]`,\ngiven a proof that `+` commutes on all elements `f x` for `x ∈ s`."]
def noncomm_prod (s : Finset α) (f : α → β) (comm : ∀ x _ : x ∈ s y _ : y ∈ s, Commute (f x) (f y)) : β :=
  (s.1.map f).noncommProd
    (by 
      simpa [Multiset.mem_map, ←Finset.mem_def] using comm)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » l.to_finset)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » l.to_finset)
@[simp, toAdditive]
theorem noncomm_prod_to_finset [DecidableEq α] (l : List α) (f : α → β)
  (comm : ∀ x _ : x ∈ l.to_finset y _ : y ∈ l.to_finset, Commute (f x) (f y)) (hl : l.nodup) :
  noncomm_prod l.to_finset f comm = (l.map f).Prod :=
  by 
    rw [←List.erase_dup_eq_self] at hl 
    simp [noncomm_prod, hl]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » («expr∅»() : finset α))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » («expr∅»() : finset α))
@[simp, toAdditive]
theorem noncomm_prod_empty (f : α → β) (h : ∀ x _ : x ∈ (∅ : Finset α) y _ : y ∈ (∅ : Finset α), Commute (f x) (f y)) :
  noncomm_prod (∅ : Finset α) f h = 1 :=
  rfl

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » insert a s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » insert a s)
@[simp, toAdditive]
theorem noncomm_prod_insert_of_not_mem [DecidableEq α] (s : Finset α) (a : α) (f : α → β)
  (comm : ∀ x _ : x ∈ insert a s y _ : y ∈ insert a s, Commute (f x) (f y)) (ha : a ∉ s) :
  noncomm_prod (insert a s) f comm =
    f a*noncomm_prod s f fun x hx y hy => comm _ (mem_insert_of_mem hx) _ (mem_insert_of_mem hy) :=
  by 
    simp [insert_val_of_not_mem ha, noncomm_prod]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » insert a s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » insert a s)
@[toAdditive]
theorem noncomm_prod_insert_of_not_mem' [DecidableEq α] (s : Finset α) (a : α) (f : α → β)
  (comm : ∀ x _ : x ∈ insert a s y _ : y ∈ insert a s, Commute (f x) (f y)) (ha : a ∉ s) :
  noncomm_prod (insert a s) f comm =
    (noncomm_prod s f fun x hx y hy => comm _ (mem_insert_of_mem hx) _ (mem_insert_of_mem hy))*f a :=
  by 
    simp [noncomm_prod, insert_val_of_not_mem ha, Multiset.noncomm_prod_cons']

@[simp, toAdditive]
theorem noncomm_prod_singleton (a : α) (f : α → β) :
  (noncomm_prod ({a} : Finset α) f
      fun x hx y hy =>
        by 
          rw [mem_singleton.mp hx, mem_singleton.mp hy]) =
    f a :=
  by 
    simp [noncomm_prod, Multiset.singleton_eq_cons]

@[toAdditive]
theorem noncomm_prod_eq_prod {β : Type _} [CommMonoidₓ β] (s : Finset α) (f : α → β) :
  (noncomm_prod s f fun _ _ _ _ => Commute.all _ _) = s.prod f :=
  by 
    classical 
    induction' s using Finset.induction_on with a s ha IH
    ·
      simp 
    ·
      simp [ha, IH]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » «expr ∪ »(s, t))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » «expr ∪ »(s, t))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » t)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » t)
@[toAdditive " The non-commutative version of `finset.sum_union` "]
theorem noncomm_prod_union_of_disjoint [DecidableEq α] {s t : Finset α} (h : Disjoint s t) (f : α → β)
  (comm : ∀ x _ : x ∈ s ∪ t y _ : y ∈ s ∪ t, Commute (f x) (f y))
  (scomm : ∀ x _ : x ∈ s y _ : y ∈ s, Commute (f x) (f y) :=
    fun _ hx _ hy => comm _ (mem_union_left _ hx) _ (mem_union_left _ hy))
  (tcomm : ∀ x _ : x ∈ t y _ : y ∈ t, Commute (f x) (f y) :=
    fun _ hx _ hy => comm _ (mem_union_right _ hx) _ (mem_union_right _ hy)) :
  noncomm_prod (s ∪ t) f comm = noncomm_prod s f scomm*noncomm_prod t f tcomm :=
  by 
    obtain ⟨sl, sl', rfl⟩ := exists_list_nodup_eq s 
    obtain ⟨tl, tl', rfl⟩ := exists_list_nodup_eq t 
    rw [List.disjoint_to_finset_iff_disjoint] at h 
    simp [sl', tl', noncomm_prod_to_finset, ←List.prod_append, ←List.to_finset_append,
      List.nodup_append_of_nodup sl' tl' h]

end Finset

