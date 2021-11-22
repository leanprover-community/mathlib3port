import Mathbin.Data.List.Rotate 
import Mathbin.GroupTheory.Perm.Support

/-!
# Permutations from a list

A list `l : list α` can be interpreted as a `equiv.perm α` where each element in the list
is permuted to the next one, defined as `form_perm`. When we have that `nodup l`,
we prove that `equiv.perm.support (form_perm l) = l.to_finset`, and that
`form_perm l` is rotationally invariant, in `form_perm_rotate`.

When there are duplicate elements in `l`, how and in what arrangement with respect to the other
elements they appear in the list determines the formed permutation.
This is because `list.form_perm` is implemented as a product of `equiv.swap`s.
That means that presence of a sublist of two adjacent duplicates like `[..., x, x, ...]`
will produce the same permutation as if the adjacent duplicates were not present.

The `list.form_perm` definition is meant to primarily be used with `nodup l`, so that
the resulting permutation is cyclic (if `l` has at least two elements).
The presence of duplicates in a particular placement can lead `list.form_perm` to produce a
nontrivial permutation that is noncyclic.
-/


namespace List

variable{α β : Type _}

section FormPerm

variable[DecidableEq α](l : List α)

open Equiv Equiv.Perm

/--
A list `l : list α` can be interpreted as a `equiv.perm α` where each element in the list
is permuted to the next one, defined as `form_perm`. When we have that `nodup l`,
we prove that `equiv.perm.support (form_perm l) = l.to_finset`, and that
`form_perm l` is rotationally invariant, in `form_perm_rotate`.
-/
def form_perm : Equiv.Perm α :=
  (zip_with Equiv.swap l l.tail).Prod

@[simp]
theorem form_perm_nil : form_perm ([] : List α) = 1 :=
  rfl

@[simp]
theorem form_perm_singleton (x : α) : form_perm [x] = 1 :=
  rfl

@[simp]
theorem form_perm_cons_cons (x y : α) (l : List α) : form_perm (x :: y :: l) = swap x y*form_perm (y :: l) :=
  prod_cons

theorem form_perm_pair (x y : α) : form_perm [x, y] = swap x y :=
  rfl

theorem form_perm_apply_of_not_mem (x : α) (l : List α) (h : x ∉ l) : form_perm l x = x :=
  by 
    cases' l with y l
    ·
      simp 
    induction' l with z l IH generalizing x y
    ·
      simp 
    ·
      specialize IH x z (mt (mem_cons_of_mem y) h)
      simp only [not_or_distrib, mem_cons_iff] at h 
      simp [IH, swap_apply_of_ne_of_ne, h]

theorem form_perm_apply_mem_of_mem (x : α) (l : List α) (h : x ∈ l) : form_perm l x ∈ l :=
  by 
    cases' l with y l
    ·
      simpa 
    induction' l with z l IH generalizing x y
    ·
      simpa using h
    ·
      byCases' hx : x ∈ z :: l
      ·
        rw [form_perm_cons_cons, mul_apply, swap_apply_def]
        splitIfs <;> simp [IH _ _ hx]
      ·
        replace h : x = y := Or.resolve_right h hx 
        simp [form_perm_apply_of_not_mem _ _ hx, ←h]

@[simp]
theorem form_perm_cons_concat_apply_last (x y : α) (xs : List α) : form_perm (x :: (xs ++ [y])) y = x :=
  by 
    induction' xs with z xs IH generalizing x y
    ·
      simp 
    ·
      simp [IH]

@[simp]
theorem form_perm_apply_last (x : α) (xs : List α) : form_perm (x :: xs) ((x :: xs).last (cons_ne_nil x xs)) = x :=
  by 
    induction' xs using List.reverseRecOn with xs y IH generalizing x <;> simp 

@[simp]
theorem form_perm_apply_nth_le_length (x : α) (xs : List α) :
  form_perm (x :: xs)
      ((x :: xs).nthLe xs.length
        (by 
          simp )) =
    x :=
  by 
    rw [nth_le_cons_length, form_perm_apply_last]

theorem form_perm_apply_head (x y : α) (xs : List α) (h : nodup (x :: y :: xs)) : form_perm (x :: y :: xs) x = y :=
  by 
    simp [form_perm_apply_of_not_mem _ _ (not_mem_of_nodup_cons h)]

theorem form_perm_apply_nth_le_zero (l : List α) (h : nodup l) (hl : 1 < l.length) :
  form_perm l (l.nth_le 0 (zero_lt_one.trans hl)) = l.nth_le 1 hl :=
  by 
    rcases l with (_ | ⟨x, _ | ⟨y, tl⟩⟩)
    ·
      simp 
    ·
      simp 
    ·
      simpa using form_perm_apply_head _ _ _ h

theorem form_perm_eq_head_iff_eq_last (x y : α) : form_perm (y :: l) x = y ↔ x = last (y :: l) (cons_ne_nil _ _) :=
  Iff.trans
    (by 
      rw [form_perm_apply_last])
    (form_perm (y :: l)).Injective.eq_iff

theorem zip_with_swap_prod_support' (l l' : List α) :
  { x | (zip_with swap l l').Prod x ≠ x } ≤ l.to_finset⊔l'.to_finset :=
  by 
    simp only [Set.sup_eq_union, Set.le_eq_subset]
    induction' l with y l hl generalizing l'
    ·
      simp 
    ·
      cases' l' with z l'
      ·
        simp 
      ·
        intro x 
        simp only [Set.union_subset_iff, mem_cons_iff, zip_with_cons_cons, foldr, prod_cons, mul_apply]
        intro hx 
        byCases' h : x ∈ { x | (zip_with swap l l').Prod x ≠ x }
        ·
          specialize hl l' h 
          refine' Set.MemUnion.elim hl (fun hm => _) fun hm => _ <;>
            ·
              simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, to_finset_cons, mem_to_finset] at hm⊢
              simp [hm]
        ·
          simp only [not_not, Set.mem_set_of_eq] at h 
          simp only [h, Set.mem_set_of_eq] at hx 
          rw [swap_apply_ne_self_iff] at hx 
          rcases hx with ⟨hyz, rfl | rfl⟩ <;> simp 

theorem zip_with_swap_prod_support [Fintype α] (l l' : List α) :
  (zip_with swap l l').Prod.support ≤ l.to_finset⊔l'.to_finset :=
  by 
    intro x hx 
    have hx' : x ∈ { x | (zip_with swap l l').Prod x ≠ x } :=
      by 
        simpa using hx 
    simpa using zip_with_swap_prod_support' _ _ hx'

theorem support_form_perm_le' : { x | form_perm l x ≠ x } ≤ l.to_finset :=
  by 
    refine' (zip_with_swap_prod_support' l l.tail).trans _ 
    simpa [Finset.subset_iff] using tail_subset l

theorem support_form_perm_le [Fintype α] : support (form_perm l) ≤ l.to_finset :=
  by 
    intro x hx 
    have hx' : x ∈ { x | form_perm l x ≠ x } :=
      by 
        simpa using hx 
    simpa using support_form_perm_le' _ hx'

theorem form_perm_apply_lt (xs : List α) (h : nodup xs) (n : ℕ) (hn : (n+1) < xs.length) :
  form_perm xs (xs.nth_le n ((Nat.lt_succ_selfₓ n).trans hn)) = xs.nth_le (n+1) hn :=
  by 
    induction' n with n IH generalizing xs
    ·
      simpa using form_perm_apply_nth_le_zero _ h _
    ·
      rcases xs with (_ | ⟨x, _ | ⟨y, l⟩⟩)
      ·
        simp 
      ·
        simp 
      ·
        specialize IH (y :: l) (nodup_of_nodup_cons h) _
        ·
          simpa [Nat.succ_lt_succ_iff] using hn 
        simp only [swap_apply_eq_iff, coe_mul, form_perm_cons_cons, nth_le]
        generalizeProofs  at IH 
        rw [IH, swap_apply_of_ne_of_ne, nth_le] <;>
          ·
            rintro rfl 
            simpa [nth_le_mem _ _ _] using h

theorem form_perm_apply_nth_le (xs : List α) (h : nodup xs) (n : ℕ) (hn : n < xs.length) :
  form_perm xs (xs.nth_le n hn) = xs.nth_le ((n+1) % xs.length) (Nat.mod_ltₓ _ (n.zero_le.trans_lt hn)) :=
  by 
    cases' xs with x xs
    ·
      simp 
    ·
      have  : n ≤ xs.length
      ·
        refine' Nat.le_of_lt_succₓ _ 
        simpa using hn 
      rcases this.eq_or_lt with (rfl | hn')
      ·
        simp 
      ·
        simp [form_perm_apply_lt, h, Nat.mod_eq_of_ltₓ, Nat.succ_lt_succₓ hn']

theorem support_form_perm_of_nodup' (l : List α) (h : nodup l) (h' : ∀ x : α, l ≠ [x]) :
  { x | form_perm l x ≠ x } = l.to_finset :=
  by 
    apply le_antisymmₓ
    ·
      exact support_form_perm_le' l
    ·
      intro x hx 
      simp only [Finset.mem_coe, mem_to_finset] at hx 
      obtain ⟨n, hn, rfl⟩ := nth_le_of_mem hx 
      rw [Set.mem_set_of_eq, form_perm_apply_nth_le _ h]
      intro H 
      rw [nodup_iff_nth_le_inj] at h 
      specialize h _ _ _ _ H 
      cases' (Nat.succ_le_of_ltₓ hn).eq_or_lt with hn' hn'
      ·
        simp only [←hn', Nat.mod_selfₓ] at h 
        refine' not_exists.mpr h' _ 
        simpa [←h, eq_comm, length_eq_one] using hn'
      ·
        simpa [Nat.mod_eq_of_ltₓ hn'] using h

theorem support_form_perm_of_nodup [Fintype α] (l : List α) (h : nodup l) (h' : ∀ x : α, l ≠ [x]) :
  support (form_perm l) = l.to_finset :=
  by 
    rw [←Finset.coe_inj]
    convert support_form_perm_of_nodup' _ h h' 
    simp [Set.ext_iff]

theorem form_perm_rotate_one (l : List α) (h : nodup l) : form_perm (l.rotate 1) = form_perm l :=
  by 
    have h' : nodup (l.rotate 1)
    ·
      simpa using h 
    byCases' hl : ∀ x : α, l ≠ [x]
    ·
      have hl' : ∀ x : α, l.rotate 1 ≠ [x]
      ·
        intro 
        rw [Ne.def, rotate_eq_iff]
        simpa using hl _ 
      ext x 
      byCases' hx : x ∈ l.rotate 1
      ·
        obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx 
        rw [form_perm_apply_nth_le _ h', nth_le_rotate l, nth_le_rotate l, form_perm_apply_nth_le _ h]
        simp 
      ·
        rw [form_perm_apply_of_not_mem _ _ hx, form_perm_apply_of_not_mem]
        simpa using hx
    ·
      pushNeg  at hl 
      obtain ⟨x, rfl⟩ := hl 
      simp 

theorem form_perm_rotate (l : List α) (h : nodup l) (n : ℕ) : form_perm (l.rotate n) = form_perm l :=
  by 
    induction' n with n hn
    ·
      simp 
    ·
      rw [Nat.succ_eq_add_one, ←rotate_rotate, form_perm_rotate_one, hn]
      rwa [is_rotated.nodup_iff]
      exact is_rotated.forall l n

theorem form_perm_eq_of_is_rotated {l l' : List α} (hd : nodup l) (h : l ~r l') : form_perm l = form_perm l' :=
  by 
    obtain ⟨n, rfl⟩ := h 
    exact (form_perm_rotate l hd n).symm

theorem form_perm_reverse (l : List α) (h : nodup l) : form_perm l.reverse = form_perm l⁻¹ :=
  by 
    rw [eq_comm, inv_eq_iff_mul_eq_one]
    ext x 
    rw [mul_apply, one_apply]
    byCases' hx : x ∈ l 
    swap
    ·
      rw [form_perm_apply_of_not_mem x l.reverse, form_perm_apply_of_not_mem _ _ hx]
      simpa using hx
    ·
      obtain ⟨k, hk, rfl⟩ := nth_le_of_mem (mem_reverse.mpr hx)
      rw [form_perm_apply_nth_le l.reverse (nodup_reverse.mpr h), nth_le_reverse', form_perm_apply_nth_le _ h,
        nth_le_reverse']
      ·
        congr 
        rw [length_reverse, ←Nat.succ_le_iff, Nat.succ_eq_add_one] at hk 
        cases' hk.eq_or_lt with hk' hk'
        ·
          simp [←hk']
        ·
          rw [length_reverse, Nat.mod_eq_of_ltₓ hk', tsub_add_eq_add_tsub (Nat.le_pred_of_lt hk'), Nat.mod_eq_of_ltₓ]
          ·
            simp 
          ·
            rw [tsub_add_cancel_of_le]
            refine' tsub_lt_self _ (Nat.zero_lt_succₓ _)
            all_goals 
              simpa using (Nat.zero_leₓ _).trans_lt hk' 
      all_goals 
        rw [←tsub_add_eq_tsub_tsub, ←length_reverse]
        refine' tsub_lt_self _ (zero_lt_one.trans_le (le_add_right le_rfl))
        exact k.zero_le.trans_lt hk

theorem form_perm_pow_apply_nth_le (l : List α) (h : nodup l) (n k : ℕ) (hk : k < l.length) :
  (form_perm l ^ n) (l.nth_le k hk) = l.nth_le ((k+n) % l.length) (Nat.mod_ltₓ _ (k.zero_le.trans_lt hk)) :=
  by 
    induction' n with n hn
    ·
      simp [Nat.mod_eq_of_ltₓ hk]
    ·
      simp [pow_succₓ, mul_apply, hn, form_perm_apply_nth_le _ h, Nat.succ_eq_add_one, ←Nat.add_assoc]

theorem form_perm_pow_apply_head (x : α) (l : List α) (h : nodup (x :: l)) (n : ℕ) :
  (form_perm (x :: l) ^ n) x = (x :: l).nthLe (n % (x :: l).length) (Nat.mod_ltₓ _ (Nat.zero_lt_succₓ _)) :=
  by 
    convert form_perm_pow_apply_nth_le _ h n 0 _ <;> simp 

theorem form_perm_ext_iff {x y x' y' : α} {l l' : List α} (hd : nodup (x :: y :: l)) (hd' : nodup (x' :: y' :: l')) :
  form_perm (x :: y :: l) = form_perm (x' :: y' :: l') ↔ (x :: y :: l) ~r (x' :: y' :: l') :=
  by 
    refine' ⟨fun h => _, fun hr => form_perm_eq_of_is_rotated hd hr⟩
    rw [Equiv.Perm.ext_iff] at h 
    have hx : x' ∈ x :: y :: l
    ·
      have  : x' ∈ { z | form_perm (x :: y :: l) z ≠ z }
      ·
        rw [Set.mem_set_of_eq, h x', form_perm_apply_head _ _ _ hd']
        simp only [mem_cons_iff, nodup_cons] at hd' 
        pushNeg  at hd' 
        exact hd'.left.left.symm 
      simpa using support_form_perm_le' _ this 
    obtain ⟨n, hn, hx'⟩ := nth_le_of_mem hx 
    have hl : (x :: y :: l).length = (x' :: y' :: l').length
    ·
      rw [←erase_dup_eq_self.mpr hd, ←erase_dup_eq_self.mpr hd', ←card_to_finset, ←card_to_finset]
      refine' congr_argₓ Finset.card _ 
      rw [←Finset.coe_inj,
        ←support_form_perm_of_nodup' _ hd
          (by 
            simp ),
        ←support_form_perm_of_nodup' _ hd'
          (by 
            simp )]
      simp only [h]
    use n 
    apply List.ext_le
    ·
      rw [length_rotate, hl]
    ·
      intro k hk hk' 
      rw [nth_le_rotate]
      induction' k with k IH
      ·
        simpRw [Nat.zero_add, Nat.mod_eq_of_ltₓ hn]
        simpa
      ·
        have  : k.succ = (k+1) % (x' :: y' :: l').length
        ·
          rw [←Nat.succ_eq_add_one, Nat.mod_eq_of_ltₓ hk']
        simpRw [this]
        rw [←form_perm_apply_nth_le _ hd' k (k.lt_succ_self.trans hk'), ←IH (k.lt_succ_self.trans hk), ←h,
          form_perm_apply_nth_le _ hd]
        congr 1
        have h1 : 1 = 1 % (x' :: y' :: l').length :=
          by 
            simp 
        rw [hl, Nat.mod_eq_of_ltₓ hk', h1, ←Nat.add_modₓ, Nat.succ_add]

theorem form_perm_apply_mem_eq_self_iff (hl : nodup l) (x : α) (hx : x ∈ l) : form_perm l x = x ↔ length l ≤ 1 :=
  by 
    obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx 
    rw [form_perm_apply_nth_le _ hl, hl.nth_le_inj_iff]
    cases hn : l.length
    ·
      exact absurd k.zero_le (hk.trans_le hn.le).not_le
    ·
      rw [hn] at hk 
      cases' (Nat.le_of_lt_succₓ hk).eq_or_lt with hk' hk'
      ·
        simp [←hk', Nat.succ_le_succ_iff, eq_comm]
      ·
        simpa [Nat.mod_eq_of_ltₓ (Nat.succ_lt_succₓ hk'), Nat.succ_lt_succ_iff] using k.zero_le.trans_lt hk'

theorem form_perm_apply_mem_ne_self_iff (hl : nodup l) (x : α) (hx : x ∈ l) : form_perm l x ≠ x ↔ 2 ≤ l.length :=
  by 
    rw [Ne.def, form_perm_apply_mem_eq_self_iff _ hl x hx, not_leₓ]
    exact ⟨Nat.succ_le_of_ltₓ, Nat.lt_of_succ_leₓ⟩

theorem mem_of_form_perm_ne_self (l : List α) (x : α) (h : form_perm l x ≠ x) : x ∈ l :=
  by 
    suffices  : x ∈ { y | form_perm l y ≠ y }
    ·
      rw [←mem_to_finset]
      exact support_form_perm_le' _ this 
    simpa using h

theorem form_perm_eq_self_of_not_mem (l : List α) (x : α) (h : x ∉ l) : form_perm l x = x :=
  by_contra fun H => h$ mem_of_form_perm_ne_self _ _ H

-- error in GroupTheory.Perm.List: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem form_perm_eq_one_iff (hl : nodup l) : «expr ↔ »(«expr = »(form_perm l, 1), «expr ≤ »(l.length, 1)) :=
begin
  cases [expr l] ["with", ident hd, ident tl],
  { simp [] [] [] [] [] [] },
  { rw ["<-", expr form_perm_apply_mem_eq_self_iff _ hl hd (mem_cons_self _ _)] [],
    split,
    { simp [] [] [] [] [] [] { contextual := tt } },
    { intro [ident h],
      simp [] [] ["only"] ["[", expr [«expr :: »/«expr :: »/«expr :: »](hd, tl).form_perm_apply_mem_eq_self_iff hl hd (mem_cons_self hd tl), ",", expr add_le_iff_nonpos_left, ",", expr length, ",", expr nonpos_iff_eq_zero, ",", expr length_eq_zero, "]"] [] ["at", ident h],
      simp [] [] [] ["[", expr h, "]"] [] [] } }
end

theorem form_perm_eq_form_perm_iff {l l' : List α} (hl : l.nodup) (hl' : l'.nodup) :
  l.form_perm = l'.form_perm ↔ l ~r l' ∨ l.length ≤ 1 ∧ l'.length ≤ 1 :=
  by 
    rcases l with (_ | ⟨x, _ | ⟨y, l⟩⟩)
    ·
      suffices  : l'.length ≤ 1 ↔ l' = nil ∨ l'.length ≤ 1
      ·
        simpa [eq_comm, form_perm_eq_one_iff, hl, hl', length_eq_zero]
      refine' ⟨fun h => Or.inr h, _⟩
      rintro (rfl | h)
      ·
        simp 
      ·
        exact h
    ·
      suffices  : l'.length ≤ 1 ↔ [x] ~r l' ∨ l'.length ≤ 1
      ·
        simpa [eq_comm, form_perm_eq_one_iff, hl, hl', length_eq_zero, le_rfl]
      refine' ⟨fun h => Or.inr h, _⟩
      rintro (h | h)
      ·
        simp [←h.perm.length_eq]
      ·
        exact h
    ·
      rcases l' with (_ | ⟨x', _ | ⟨y', l'⟩⟩)
      ·
        simp [form_perm_eq_one_iff, hl, -form_perm_cons_cons]
      ·
        suffices  : ¬(x :: y :: l) ~r [x']
        ·
          simp [form_perm_eq_one_iff, hl, -form_perm_cons_cons]
        intro h 
        simpa using h.perm.length_eq
      ·
        simp [-form_perm_cons_cons, form_perm_ext_iff hl hl']

theorem form_perm_zpow_apply_mem_imp_mem (l : List α) (x : α) (hx : x ∈ l) (n : ℤ) : (form_perm l ^ n) x ∈ l :=
  by 
    byCases' h : (l.form_perm ^ n) x = x
    ·
      simpa [h] using hx
    ·
      have  : x ∈ { x | (l.form_perm ^ n) x ≠ x } := h 
      rw [←set_support_apply_mem] at this 
      replace this := set_support_zpow_subset _ _ this 
      simpa using support_form_perm_le' _ this

theorem form_perm_pow_length_eq_one_of_nodup (hl : nodup l) : form_perm l ^ length l = 1 :=
  by 
    ext x 
    byCases' hx : x ∈ l
    ·
      obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx 
      simp [form_perm_pow_apply_nth_le _ hl, Nat.mod_eq_of_ltₓ hk]
    ·
      have  : x ∉ { x | (l.form_perm ^ l.length) x ≠ x }
      ·
        intro H 
        refine' hx _ 
        replace H := set_support_zpow_subset l.form_perm l.length H 
        simpa using support_form_perm_le' _ H 
      simpa

end FormPerm

end List

