import Mathbin.Data.List.Perm 
import Mathbin.Data.List.Range

/-!
# List rotation

This file proves basic results about `list.rotate`, the list rotation.

## Main declarations

* `is_rotated l₁ l₂`: States that `l₁` is a rotated version of `l₂`.
* `cyclic_permutations l`: The list of all cyclic permutants of `l`, up to the length of `l`.

## Tags

rotated, rotation, permutation, cycle
-/


universe u

variable {α : Type u}

open Nat

namespace List

theorem rotate_mod (l : List α) (n : ℕ) : l.rotate (n % l.length) = l.rotate n :=
  by 
    simp [rotate]

@[simp]
theorem rotate_nil (n : ℕ) : ([] : List α).rotate n = [] :=
  by 
    cases n <;> simp [rotate]

@[simp]
theorem rotate_zero (l : List α) : l.rotate 0 = l :=
  by 
    simp [rotate]

@[simp]
theorem rotate'_nil (n : ℕ) : ([] : List α).rotate' n = [] :=
  by 
    cases n <;> rfl

@[simp]
theorem rotate'_zero (l : List α) : l.rotate' 0 = l :=
  by 
    cases l <;> rfl

theorem rotate'_cons_succ (l : List α) (a : α) (n : ℕ) : (a :: l : List α).rotate' n.succ = (l ++ [a]).rotate' n :=
  by 
    simp [rotate']

@[simp]
theorem length_rotate' : ∀ l : List α n : ℕ, (l.rotate' n).length = l.length
| [], n => rfl
| a :: l, 0 => rfl
| a :: l, n+1 =>
  by 
    rw [List.rotate', length_rotate' (l ++ [a]) n] <;> simp 

theorem rotate'_eq_drop_append_take : ∀ {l : List α} {n : ℕ}, n ≤ l.length → l.rotate' n = l.drop n ++ l.take n
| [], n, h =>
  by 
    simp [drop_append_of_le_length h]
| l, 0, h =>
  by 
    simp [take_append_of_le_length h]
| a :: l, n+1, h =>
  have hnl : n ≤ l.length := le_of_succ_le_succ h 
  have hnl' : n ≤ (l ++ [a]).length :=
    by 
      rw [length_append, length_cons, List.length, zero_addₓ] <;> exact le_of_succ_le h 
  by 
    rw [rotate'_cons_succ, rotate'_eq_drop_append_take hnl', drop, take, drop_append_of_le_length hnl,
        take_append_of_le_length hnl] <;>
      simp 

theorem rotate'_rotate' : ∀ l : List α n m : ℕ, (l.rotate' n).rotate' m = l.rotate' (n+m)
| a :: l, 0, m =>
  by 
    simp 
| [], n, m =>
  by 
    simp 
| a :: l, n+1, m =>
  by 
    rw [rotate'_cons_succ, rotate'_rotate', add_right_commₓ, rotate'_cons_succ]

@[simp]
theorem rotate'_length (l : List α) : rotate' l l.length = l :=
  by 
    rw [rotate'_eq_drop_append_take (le_reflₓ _)] <;> simp 

@[simp]
theorem rotate'_length_mul (l : List α) : ∀ n : ℕ, l.rotate' (l.length*n) = l
| 0 =>
  by 
    simp 
| n+1 =>
  calc l.rotate' (l.length*n+1) = (l.rotate' (l.length*n)).rotate' (l.rotate' (l.length*n)).length :=
    by 
      simp [-rotate'_length, Nat.mul_succ, rotate'_rotate']
    _ = l :=
    by 
      rw [rotate'_length, rotate'_length_mul]
    

theorem rotate'_mod (l : List α) (n : ℕ) : l.rotate' (n % l.length) = l.rotate' n :=
  calc l.rotate' (n % l.length) = (l.rotate' (n % l.length)).rotate' ((l.rotate' (n % l.length)).length*n / l.length) :=
    by 
      rw [rotate'_length_mul]
    _ = l.rotate' n :=
    by 
      rw [rotate'_rotate', length_rotate', Nat.mod_add_divₓ]
    

theorem rotate_eq_rotate' (l : List α) (n : ℕ) : l.rotate n = l.rotate' n :=
  if h : l.length = 0 then
    by 
      simp_all [length_eq_zero]
  else
    by 
      rw [←rotate'_mod, rotate'_eq_drop_append_take (le_of_ltₓ (Nat.mod_ltₓ _ (Nat.pos_of_ne_zeroₓ h)))] <;>
        simp [rotate]

theorem rotate_cons_succ (l : List α) (a : α) (n : ℕ) : (a :: l : List α).rotate n.succ = (l ++ [a]).rotate n :=
  by 
    rw [rotate_eq_rotate', rotate_eq_rotate', rotate'_cons_succ]

@[simp]
theorem mem_rotate : ∀ {l : List α} {a : α} {n : ℕ}, a ∈ l.rotate n ↔ a ∈ l
| [], _, n =>
  by 
    simp 
| a :: l, _, 0 =>
  by 
    simp 
| a :: l, _, n+1 =>
  by 
    simp [rotate_cons_succ, mem_rotate, Or.comm]

@[simp]
theorem length_rotate (l : List α) (n : ℕ) : (l.rotate n).length = l.length :=
  by 
    rw [rotate_eq_rotate', length_rotate']

theorem rotate_eq_drop_append_take {l : List α} {n : ℕ} : n ≤ l.length → l.rotate n = l.drop n ++ l.take n :=
  by 
    rw [rotate_eq_rotate'] <;> exact rotate'_eq_drop_append_take

theorem rotate_eq_drop_append_take_mod {l : List α} {n : ℕ} :
  l.rotate n = l.drop (n % l.length) ++ l.take (n % l.length) :=
  by 
    cases' l.length.zero_le.eq_or_lt with hl hl
    ·
      simp [eq_nil_of_length_eq_zero hl.symm]
    rw [←rotate_eq_drop_append_take (n.mod_lt hl).le, rotate_mod]

@[simp]
theorem rotate_append_length_eq (l l' : List α) : (l ++ l').rotate l.length = l' ++ l :=
  by 
    rw [rotate_eq_rotate']
    induction l generalizing l'
    ·
      simp 
    ·
      simp [rotate', l_ih]

theorem rotate_rotate (l : List α) (n m : ℕ) : (l.rotate n).rotate m = l.rotate (n+m) :=
  by 
    rw [rotate_eq_rotate', rotate_eq_rotate', rotate_eq_rotate', rotate'_rotate']

@[simp]
theorem rotate_length (l : List α) : rotate l l.length = l :=
  by 
    rw [rotate_eq_rotate', rotate'_length]

@[simp]
theorem rotate_length_mul (l : List α) (n : ℕ) : l.rotate (l.length*n) = l :=
  by 
    rw [rotate_eq_rotate', rotate'_length_mul]

theorem prod_rotate_eq_one_of_prod_eq_one [Groupₓ α] : ∀ {l : List α} hl : l.prod = 1 n : ℕ, (l.rotate n).Prod = 1
| [], _, _ =>
  by 
    simp 
| a :: l, hl, n =>
  have  : n % List.length (a :: l) ≤ List.length (a :: l) :=
    le_of_ltₓ
      (Nat.mod_ltₓ _
        (by 
          decide))
  by 
    rw [←List.take_append_drop (n % List.length (a :: l)) (a :: l)] at hl <;>
      rw [←rotate_mod, rotate_eq_drop_append_take this, List.prod_append, mul_eq_one_iff_inv_eq,
        ←one_mulₓ (List.prod _⁻¹), ←hl, List.prod_append, mul_assocₓ, mul_inv_selfₓ, mul_oneₓ]

theorem rotate_perm (l : List α) (n : ℕ) : l.rotate n ~ l :=
  by 
    rw [rotate_eq_rotate']
    induction' n with n hn generalizing l
    ·
      simp 
    ·
      cases' l with hd tl
      ·
        simp 
      ·
        rw [rotate'_cons_succ]
        exact (hn _).trans (perm_append_singleton _ _)

@[simp]
theorem nodup_rotate {l : List α} {n : ℕ} : nodup (l.rotate n) ↔ nodup l :=
  (rotate_perm l n).nodup_iff

@[simp]
theorem rotate_eq_nil_iff {l : List α} {n : ℕ} : l.rotate n = [] ↔ l = [] :=
  by 
    induction' n with n hn generalizing l
    ·
      simp 
    ·
      cases' l with hd tl
      ·
        simp 
      ·
        simp [rotate_cons_succ, hn]

@[simp]
theorem nil_eq_rotate_iff {l : List α} {n : ℕ} : [] = l.rotate n ↔ [] = l :=
  by 
    rw [eq_comm, rotate_eq_nil_iff, eq_comm]

@[simp]
theorem rotate_singleton (x : α) (n : ℕ) : [x].rotate n = [x] :=
  by 
    induction' n with n hn
    ·
      simp 
    ·
      rwa [rotate_cons_succ]

@[simp]
theorem rotate_eq_singleton_iff {l : List α} {n : ℕ} {x : α} : l.rotate n = [x] ↔ l = [x] :=
  by 
    induction' n with n hn generalizing l
    ·
      simp 
    ·
      cases' l with hd tl
      ·
        simp 
      ·
        simp [rotate_cons_succ, hn, append_eq_cons_iff, and_comm]

@[simp]
theorem singleton_eq_rotate_iff {l : List α} {n : ℕ} {x : α} : [x] = l.rotate n ↔ [x] = l :=
  by 
    rw [eq_comm, rotate_eq_singleton_iff, eq_comm]

theorem zip_with_rotate_distrib {α β γ : Type _} (f : α → β → γ) (l : List α) (l' : List β) (n : ℕ)
  (h : l.length = l'.length) : (zip_with f l l').rotate n = zip_with f (l.rotate n) (l'.rotate n) :=
  by 
    rw [rotate_eq_drop_append_take_mod, rotate_eq_drop_append_take_mod, rotate_eq_drop_append_take_mod, h,
      zip_with_append, ←zip_with_distrib_drop, ←zip_with_distrib_take, List.length_zip_with, h, min_selfₓ]
    rw [length_drop, length_drop, h]

attribute [local simp] rotate_cons_succ

@[simp]
theorem zip_with_rotate_one {β : Type _} (f : α → α → β) (x y : α) (l : List α) :
  zip_with f (x :: y :: l) ((x :: y :: l).rotate 1) = f x y :: zip_with f (y :: l) (l ++ [x]) :=
  by 
    simp 

-- error in Data.List.Rotate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nth_le_rotate_one
(l : list α)
(k : exprℕ())
(hk : «expr < »(k, (l.rotate 1).length)) : «expr = »((l.rotate 1).nth_le k hk, l.nth_le «expr % »(«expr + »(k, 1), l.length) (mod_lt _ «expr ▸ »(length_rotate l 1, k.zero_le.trans_lt hk))) :=
begin
  cases [expr l] ["with", ident hd, ident tl],
  { simp [] [] [] [] [] [] },
  { have [] [":", expr «expr ≤ »(k, tl.length)] [],
    { refine [expr nat.le_of_lt_succ _],
      simpa [] [] [] [] [] ["using", expr hk] },
    rcases [expr this.eq_or_lt, "with", ident rfl, "|", ident hk'],
    { simp [] [] [] ["[", expr nth_le_append_right (le_refl _), "]"] [] [] },
    { simpa [] [] [] ["[", expr nth_le_append _ hk', ",", expr length_cons, ",", expr nat.mod_eq_of_lt (nat.succ_lt_succ hk'), "]"] [] [] } }
end

-- error in Data.List.Rotate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nth_le_rotate
(l : list α)
(n k : exprℕ())
(hk : «expr < »(k, (l.rotate n).length)) : «expr = »((l.rotate n).nth_le k hk, l.nth_le «expr % »(«expr + »(k, n), l.length) (mod_lt _ «expr ▸ »(length_rotate l n, k.zero_le.trans_lt hk))) :=
begin
  induction [expr n] [] ["with", ident n, ident hn] ["generalizing", ident l, ident k],
  { have [ident hk'] [":", expr «expr < »(k, l.length)] [":=", expr by simpa [] [] [] [] [] ["using", expr hk]],
    simp [] [] [] ["[", expr nat.mod_eq_of_lt hk', "]"] [] [] },
  { simp [] [] [] ["[", expr nat.succ_eq_add_one, ",", "<-", expr rotate_rotate, ",", expr nth_le_rotate_one, ",", expr hn l, ",", expr add_comm, ",", expr add_left_comm, "]"] [] [] }
end

-- error in Data.List.Rotate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A variant of `nth_le_rotate` useful for rewrites. -/
theorem nth_le_rotate'
(l : list α)
(n k : exprℕ())
(hk : «expr < »(k, l.length)) : «expr = »((l.rotate n).nth_le «expr % »(«expr + »(«expr - »(l.length, «expr % »(n, l.length)), k), l.length) ((nat.mod_lt _ (k.zero_le.trans_lt hk)).trans_le (length_rotate _ _).ge), l.nth_le k hk) :=
begin
  rw [expr nth_le_rotate] [],
  congr,
  set [] [ident m] [] [":="] [expr l.length] [],
  rw ["[", expr mod_add_mod, ",", expr add_assoc, ",", expr add_left_comm, ",", expr add_comm, ",", expr add_mod, ",", expr add_mod _ n, "]"] [],
  cases [expr «expr % »(n, m).zero_le.eq_or_lt] ["with", ident hn, ident hn],
  { simpa [] [] [] ["[", "<-", expr hn, "]"] [] ["using", expr nat.mod_eq_of_lt hk] },
  { have [ident mpos] [":", expr «expr < »(0, m)] [":=", expr k.zero_le.trans_lt hk],
    have [ident hm] [":", expr «expr < »(«expr - »(m, «expr % »(n, m)), m)] [":=", expr tsub_lt_self mpos hn],
    have [ident hn'] [":", expr «expr < »(«expr % »(n, m), m)] [":=", expr nat.mod_lt _ mpos],
    simpa [] [] [] ["[", expr mod_eq_of_lt hm, ",", expr tsub_add_cancel_of_le hn'.le, "]"] [] ["using", expr nat.mod_eq_of_lt hk] }
end

-- error in Data.List.Rotate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem rotate_injective (n : exprℕ()) : function.injective (λ l : list α, l.rotate n) :=
begin
  rintros [ident l, ident l', "(", ident h, ":", expr «expr = »(l.rotate n, l'.rotate n), ")"],
  have [ident hle] [":", expr «expr = »(l.length, l'.length)] [":=", expr (l.length_rotate n).symm.trans «expr ▸ »(h.symm, l'.length_rotate n)],
  rw ["[", expr rotate_eq_drop_append_take_mod, ",", expr rotate_eq_drop_append_take_mod, "]"] ["at", ident h],
  obtain ["⟨", ident hd, ",", ident ht, "⟩", ":=", expr append_inj h _],
  { rw ["[", "<-", expr take_append_drop _ l, ",", expr ht, ",", expr hd, ",", expr take_append_drop, "]"] [] },
  { rw ["[", expr length_drop, ",", expr length_drop, ",", expr hle, "]"] [] }
end

theorem rotate_eq_rotate {l l' : List α} {n : ℕ} : l.rotate n = l'.rotate n ↔ l = l' :=
  (rotate_injective n).eq_iff

theorem rotate_eq_iff {l l' : List α} {n : ℕ} : l.rotate n = l' ↔ l = l'.rotate (l'.length - n % l'.length) :=
  by 
    rw [←@rotate_eq_rotate _ l _ n, rotate_rotate, ←rotate_mod l', add_mod]
    cases' l'.length.zero_le.eq_or_lt with hl hl
    ·
      rw [eq_nil_of_length_eq_zero hl.symm, rotate_nil, rotate_eq_nil_iff]
    ·
      cases' (Nat.zero_leₓ (n % l'.length)).eq_or_lt with hn hn
      ·
        simp [←hn]
      ·
        rw [mod_eq_of_lt (tsub_lt_self hl hn), tsub_add_cancel_of_le, mod_self, rotate_zero]
        exact (Nat.mod_ltₓ _ hl).le

theorem reverse_rotate (l : List α) (n : ℕ) : (l.rotate n).reverse = l.reverse.rotate (l.length - n % l.length) :=
  by 
    rw [←length_reverse l, ←rotate_eq_iff]
    induction' n with n hn generalizing l
    ·
      simp 
    ·
      cases' l with hd tl
      ·
        simp 
      ·
        rw [rotate_cons_succ, Nat.succ_eq_add_one, ←rotate_rotate, hn]
        simp 

-- error in Data.List.Rotate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem rotate_reverse
(l : list α)
(n : exprℕ()) : «expr = »(l.reverse.rotate n, (l.rotate «expr - »(l.length, «expr % »(n, l.length))).reverse) :=
begin
  rw ["[", "<-", expr reverse_reverse l, "]"] [],
  simp_rw ["[", expr reverse_rotate, ",", expr reverse_reverse, ",", expr rotate_eq_iff, ",", expr rotate_rotate, ",", expr length_rotate, ",", expr length_reverse, "]"] [],
  rw ["[", "<-", expr length_reverse l, "]"] [],
  set [] [ident k] [] [":="] [expr «expr % »(n, l.reverse.length)] ["with", ident hk],
  cases [expr hk', ":", expr k] ["with", ident k'],
  { simp [] [] [] ["[", "-", ident length_reverse, ",", "<-", expr rotate_rotate, "]"] [] [] },
  { cases [expr l] ["with", ident x, ident l],
    { simp [] [] [] [] [] [] },
    { have [] [":", expr «expr < »(k'.succ, «expr :: »(x, l).length)] [],
      { simp [] [] [] ["[", "<-", expr hk', ",", expr hk, ",", expr nat.mod_lt, "]"] [] [] },
      rw ["[", expr nat.mod_eq_of_lt, ",", expr tsub_add_cancel_of_le, ",", expr rotate_length, "]"] [],
      { exact [expr tsub_le_self] },
      { exact [expr tsub_lt_self (by simp [] [] [] [] [] []) nat.succ_pos'] } } }
end

theorem map_rotate {β : Type _} (f : α → β) (l : List α) (n : ℕ) : map f (l.rotate n) = (map f l).rotate n :=
  by 
    induction' n with n hn IH generalizing l
    ·
      simp 
    ·
      cases' l with hd tl
      ·
        simp 
      ·
        simp [hn]

theorem nodup.rotate_eq_self_iff {l : List α} (hl : l.nodup) {n : ℕ} : l.rotate n = l ↔ n % l.length = 0 ∨ l = [] :=
  by 
    split 
    ·
      intro h 
      cases' l.length.zero_le.eq_or_lt with hl' hl'
      ·
        simp [←length_eq_zero, ←hl']
      left 
      rw [nodup_iff_nth_le_inj] at hl 
      refine' hl _ _ (mod_lt _ hl') hl' _ 
      rw [←nth_le_rotate' _ n]
      simpRw [h, tsub_add_cancel_of_le (mod_lt _ hl').le, mod_self]
    ·
      rintro (h | h)
      ·
        rw [←rotate_mod, h]
        exact rotate_zero l
      ·
        simp [h]

-- error in Data.List.Rotate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nodup.rotate_congr
{l : list α}
(hl : l.nodup)
(hn : «expr ≠ »(l, «expr[ , ]»([])))
(i j : exprℕ())
(h : «expr = »(l.rotate i, l.rotate j)) : «expr = »(«expr % »(i, l.length), «expr % »(j, l.length)) :=
begin
  have [ident hi] [":", expr «expr < »(«expr % »(i, l.length), l.length)] [":=", expr mod_lt _ (length_pos_of_ne_nil hn)],
  have [ident hj] [":", expr «expr < »(«expr % »(j, l.length), l.length)] [":=", expr mod_lt _ (length_pos_of_ne_nil hn)],
  refine [expr nodup_iff_nth_le_inj.mp hl _ _ hi hj _],
  rw ["[", "<-", expr nth_le_rotate' l i, ",", "<-", expr nth_le_rotate' l j, "]"] [],
  simp [] [] [] ["[", expr tsub_add_cancel_of_le, ",", expr hi.le, ",", expr hj.le, ",", expr h, "]"] [] []
end

section IsRotated

variable (l l' : List α)

/-- `is_rotated l₁ l₂` or `l₁ ~r l₂` asserts that `l₁` and `l₂` are cyclic permutations
  of each other. This is defined by claiming that `∃ n, l.rotate n = l'`. -/
def is_rotated : Prop :=
  ∃ n, l.rotate n = l'

infixr:1000 " ~r " => is_rotated

variable {l l'}

@[refl]
theorem is_rotated.refl (l : List α) : l ~r l :=
  ⟨0,
    by 
      simp ⟩

@[symm]
theorem is_rotated.symm (h : l ~r l') : l' ~r l :=
  by 
    obtain ⟨n, rfl⟩ := h 
    cases' l with hd tl
    ·
      simp 
    ·
      use ((hd :: tl).length*n) - n 
      rw [rotate_rotate, add_tsub_cancel_of_le, rotate_length_mul]
      exact
        Nat.le_mul_of_pos_left
          (by 
            simp )

theorem is_rotated_comm : l ~r l' ↔ l' ~r l :=
  ⟨is_rotated.symm, is_rotated.symm⟩

@[simp]
protected theorem is_rotated.forall (l : List α) (n : ℕ) : l.rotate n ~r l :=
  is_rotated.symm ⟨n, rfl⟩

@[trans]
theorem is_rotated.trans {l'' : List α} (h : l ~r l') (h' : l' ~r l'') : l ~r l'' :=
  by 
    obtain ⟨n, rfl⟩ := h 
    obtain ⟨m, rfl⟩ := h' 
    rw [rotate_rotate]
    use n+m

theorem is_rotated.eqv : Equivalenceₓ (@is_rotated α) :=
  mk_equivalence _ is_rotated.refl (fun _ _ => is_rotated.symm) fun _ _ _ => is_rotated.trans

/-- The relation `list.is_rotated l l'` forms a `setoid` of cycles. -/
def is_rotated.setoid (α : Type _) : Setoidₓ (List α) :=
  { R := is_rotated, iseqv := is_rotated.eqv }

theorem is_rotated.perm (h : l ~r l') : l ~ l' :=
  Exists.elim h fun _ hl => hl ▸ (rotate_perm _ _).symm

theorem is_rotated.nodup_iff (h : l ~r l') : nodup l ↔ nodup l' :=
  h.perm.nodup_iff

theorem is_rotated.mem_iff (h : l ~r l') {a : α} : a ∈ l ↔ a ∈ l' :=
  h.perm.mem_iff

@[simp]
theorem is_rotated_nil_iff : l ~r [] ↔ l = [] :=
  ⟨fun ⟨n, hn⟩ =>
      by 
        simpa using hn,
    fun h =>
      h ▸
        by 
          rfl⟩

@[simp]
theorem is_rotated_nil_iff' : [] ~r l ↔ [] = l :=
  by 
    rw [is_rotated_comm, is_rotated_nil_iff, eq_comm]

@[simp]
theorem is_rotated_singleton_iff {x : α} : l ~r [x] ↔ l = [x] :=
  ⟨fun ⟨n, hn⟩ =>
      by 
        simpa using hn,
    fun h =>
      h ▸
        by 
          rfl⟩

@[simp]
theorem is_rotated_singleton_iff' {x : α} : [x] ~r l ↔ [x] = l :=
  by 
    rw [is_rotated_comm, is_rotated_singleton_iff, eq_comm]

theorem is_rotated_concat (hd : α) (tl : List α) : (tl ++ [hd]) ~r (hd :: tl) :=
  is_rotated.symm
    ⟨1,
      by 
        simp ⟩

theorem is_rotated_append : (l ++ l') ~r (l' ++ l) :=
  ⟨l.length,
    by 
      simp ⟩

theorem is_rotated.reverse (h : l ~r l') : l.reverse ~r l'.reverse :=
  by 
    obtain ⟨n, rfl⟩ := h 
    exact ⟨_, (reverse_rotate _ _).symm⟩

theorem is_rotated_reverse_comm_iff : l.reverse ~r l' ↔ l ~r l'.reverse :=
  by 
    split  <;>
      ·
        intro h 
        simpa using h.reverse

@[simp]
theorem is_rotated_reverse_iff : l.reverse ~r l'.reverse ↔ l ~r l' :=
  by 
    simp [is_rotated_reverse_comm_iff]

theorem is_rotated_iff_mod : l ~r l' ↔ ∃ (n : _)(_ : n ≤ l.length), l.rotate n = l' :=
  by 
    refine' ⟨fun h => _, fun ⟨n, _, h⟩ => ⟨n, h⟩⟩
    obtain ⟨n, rfl⟩ := h 
    cases' l with hd tl
    ·
      simp 
    ·
      refine' ⟨n % (hd :: tl).length, _, rotate_mod _ _⟩
      refine' (Nat.mod_ltₓ _ _).le 
      simp 

theorem is_rotated_iff_mem_map_range : l ~r l' ↔ l' ∈ (List.range (l.length+1)).map l.rotate :=
  by 
    simpRw [mem_map, mem_range, is_rotated_iff_mod]
    exact ⟨fun ⟨n, hn, h⟩ => ⟨n, Nat.lt_succ_of_leₓ hn, h⟩, fun ⟨n, hn, h⟩ => ⟨n, Nat.le_of_lt_succₓ hn, h⟩⟩

@[congr]
theorem is_rotated.map {β : Type _} {l₁ l₂ : List α} (h : l₁ ~r l₂) (f : α → β) : map f l₁ ~r map f l₂ :=
  by 
    obtain ⟨n, rfl⟩ := h 
    rw [map_rotate]
    use n

/-- List of all cyclic permutations of `l`.
The `cyclic_permutations` of a nonempty list `l` will always contain `list.length l` elements.
This implies that under certain conditions, there are duplicates in `list.cyclic_permutations l`.
The `n`th entry is equal to `l.rotate n`, proven in `list.nth_le_cyclic_permutations`.
The proof that every cyclic permutant of `l` is in the list is `list.mem_cyclic_permutations_iff`.

     cyclic_permutations [1, 2, 3, 2, 4] =
       [[1, 2, 3, 2, 4], [2, 3, 2, 4, 1], [3, 2, 4, 1, 2],
        [2, 4, 1, 2, 3], [4, 1, 2, 3, 2]] -/
def cyclic_permutations : List α → List (List α)
| [] => [[]]
| l@(_ :: _) => init (zip_with (· ++ ·) (tails l) (inits l))

@[simp]
theorem cyclic_permutations_nil : cyclic_permutations ([] : List α) = [[]] :=
  rfl

theorem cyclic_permutations_cons (x : α) (l : List α) :
  cyclic_permutations (x :: l) = init (zip_with (· ++ ·) (tails (x :: l)) (inits (x :: l))) :=
  rfl

theorem cyclic_permutations_of_ne_nil (l : List α) (h : l ≠ []) :
  cyclic_permutations l = init (zip_with (· ++ ·) (tails l) (inits l)) :=
  by 
    obtain ⟨hd, tl, rfl⟩ := exists_cons_of_ne_nil h 
    exact cyclic_permutations_cons _ _

theorem length_cyclic_permutations_cons (x : α) (l : List α) : length (cyclic_permutations (x :: l)) = length l+1 :=
  by 
    simp [cyclic_permutations_of_ne_nil]

@[simp]
theorem length_cyclic_permutations_of_ne_nil (l : List α) (h : l ≠ []) : length (cyclic_permutations l) = length l :=
  by 
    simp [cyclic_permutations_of_ne_nil _ h]

@[simp]
theorem nth_le_cyclic_permutations (l : List α) (n : ℕ) (hn : n < length (cyclic_permutations l)) :
  nth_le (cyclic_permutations l) n hn = l.rotate n :=
  by 
    obtain rfl | h := eq_or_ne l []
    ·
      simp 
    ·
      rw [length_cyclic_permutations_of_ne_nil _ h] at hn 
      simp [init_eq_take, cyclic_permutations_of_ne_nil _ h, nth_le_take', rotate_eq_drop_append_take hn.le]

theorem mem_cyclic_permutations_self (l : List α) : l ∈ cyclic_permutations l :=
  by 
    cases' l with x l
    ·
      simp 
    ·
      rw [mem_iff_nth_le]
      refine'
        ⟨0,
          by 
            simp ,
          _⟩
      simp 

theorem length_mem_cyclic_permutations (l : List α) (h : l' ∈ cyclic_permutations l) : length l' = length l :=
  by 
    obtain ⟨k, hk, rfl⟩ := nth_le_of_mem h 
    simp 

@[simp]
theorem mem_cyclic_permutations_iff {l l' : List α} : l ∈ cyclic_permutations l' ↔ l ~r l' :=
  by 
    split 
    ·
      intro h 
      obtain ⟨k, hk, rfl⟩ := nth_le_of_mem h 
      simp 
    ·
      intro h 
      obtain ⟨k, rfl⟩ := h.symm 
      rw [mem_iff_nth_le]
      simp only [exists_prop, nth_le_cyclic_permutations]
      cases' l' with x l
      ·
        simp 
      ·
        refine' ⟨k % length (x :: l), _, rotate_mod _ _⟩
        simpa using Nat.mod_ltₓ _ (zero_lt_succ _)

@[simp]
theorem cyclic_permutations_eq_nil_iff {l : List α} : cyclic_permutations l = [[]] ↔ l = [] :=
  by 
    refine'
      ⟨fun h => _,
        fun h =>
          by 
            simp [h]⟩
    rw [eq_comm, ←is_rotated_nil_iff', ←mem_cyclic_permutations_iff, h, mem_singleton]

@[simp]
theorem cyclic_permutations_eq_singleton_iff {l : List α} {x : α} : cyclic_permutations l = [[x]] ↔ l = [x] :=
  by 
    refine'
      ⟨fun h => _,
        fun h =>
          by 
            simp [cyclic_permutations, h, init_eq_take]⟩
    rw [eq_comm, ←is_rotated_singleton_iff', ←mem_cyclic_permutations_iff, h, mem_singleton]

/-- If a `l : list α` is `nodup l`, then all of its cyclic permutants are distinct. -/
theorem nodup.cyclic_permutations {l : List α} (hn : nodup l) : nodup (cyclic_permutations l) :=
  by 
    cases' l with x l
    ·
      simp 
    rw [nodup_iff_nth_le_inj]
    intro i j hi hj h 
    simp only [length_cyclic_permutations_cons] at hi hj 
    rw [←mod_eq_of_lt hi, ←mod_eq_of_lt hj, ←length_cons x l]
    apply hn.rotate_congr
    ·
      simp 
    ·
      simpa using h

-- error in Data.List.Rotate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem cyclic_permutations_rotate
(l : list α)
(k : exprℕ()) : «expr = »((l.rotate k).cyclic_permutations, l.cyclic_permutations.rotate k) :=
begin
  have [] [":", expr «expr = »((l.rotate k).cyclic_permutations.length, length (l.cyclic_permutations.rotate k))] [],
  { cases [expr l] [],
    { simp [] [] [] [] [] [] },
    { rw [expr length_cyclic_permutations_of_ne_nil] []; simp [] [] [] [] [] [] } },
  refine [expr ext_le this (λ n hn hn', _)],
  rw ["[", expr nth_le_cyclic_permutations, ",", expr nth_le_rotate, ",", expr nth_le_cyclic_permutations, ",", expr rotate_rotate, ",", "<-", expr rotate_mod, ",", expr add_comm, "]"] [],
  cases [expr l] []; simp [] [] [] [] [] []
end

theorem is_rotated.cyclic_permutations {l l' : List α} (h : l ~r l') :
  l.cyclic_permutations ~r l'.cyclic_permutations :=
  by 
    obtain ⟨k, rfl⟩ := h 
    exact
      ⟨k,
        by 
          simp ⟩

-- error in Data.List.Rotate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem is_rotated_cyclic_permutations_iff
{l l' : list α} : «expr ↔ »(«expr ~r »(l.cyclic_permutations, l'.cyclic_permutations), «expr ~r »(l, l')) :=
begin
  by_cases [expr hl, ":", expr «expr = »(l, «expr[ , ]»([]))],
  { simp [] [] [] ["[", expr hl, ",", expr eq_comm, "]"] [] [] },
  have [ident hl'] [":", expr «expr = »(l.cyclic_permutations.length, l.length)] [":=", expr length_cyclic_permutations_of_ne_nil _ hl],
  refine [expr ⟨λ h, _, is_rotated.cyclic_permutations⟩],
  obtain ["⟨", ident k, ",", ident hk, "⟩", ":=", expr h],
  refine [expr ⟨«expr % »(k, l.length), _⟩],
  have [ident hk'] [":", expr «expr < »(«expr % »(k, l.length), l.length)] [":=", expr mod_lt _ (length_pos_of_ne_nil hl)],
  rw ["[", "<-", expr nth_le_cyclic_permutations _ _ (hk'.trans_le hl'.ge), ",", "<-", expr nth_le_rotate' _ k, "]"] [],
  simp [] [] [] ["[", expr hk, ",", expr hl', ",", expr tsub_add_cancel_of_le hk'.le, "]"] [] []
end

section Decidable

variable [DecidableEq α]

instance is_rotated_decidable (l l' : List α) : Decidable (l ~r l') :=
  decidableOfIff' _ is_rotated_iff_mem_map_range

instance {l l' : List α} : Decidable (@Setoidₓ.R _ (is_rotated.setoid α) l l') :=
  List.isRotatedDecidable _ _

end Decidable

end IsRotated

end List

