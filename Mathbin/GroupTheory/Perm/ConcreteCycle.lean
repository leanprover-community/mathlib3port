import Mathbin.GroupTheory.Perm.List 
import Mathbin.Data.List.Cycle 
import Mathbin.GroupTheory.Perm.CycleType

/-!

# Properties of cyclic permutations constructed from lists/cycles

In the following, `{α : Type*} [fintype α] [decidable_eq α]`.

## Main definitions

* `cycle.form_perm`: the cyclic permutation created by looping over a `cycle α`
* `equiv.perm.to_list`: the list formed by iterating application of a permutation
* `equiv.perm.to_cycle`: the cycle formed by iterating application of a permutation
* `equiv.perm.iso_cycle`: the equivalence between cyclic permutations `f : perm α`
  and the terms of `cycle α` that correspond to them
* `equiv.perm.iso_cycle'`: the same equivalence as `equiv.perm.iso_cycle`
  but with evaluation via choosing over fintypes
* The notation `c[1, 2, 3]` to emulate notation of cyclic permutations `(1 2 3)`
* A `has_repr` instance for any `perm α`, by representing the `finset` of
  `cycle α` that correspond to the cycle factors.

## Main results

* `list.is_cycle_form_perm`: a nontrivial list without duplicates, when interpreted as
  a permutation, is cyclic
* `equiv.perm.is_cycle.exists_unique_cycle`: there is only one nontrivial `cycle α`
  corresponding to each cyclic `f : perm α`

## Implementation details

The forward direction of `equiv.perm.iso_cycle'` uses `fintype.choose` of the uniqueness
result, relying on the `fintype` instance of a `cycle.nodup` subtype.
It is unclear if this works faster than the `equiv.perm.to_cycle`, which relies
on recursion over `finset.univ`.
Running `#eval` on even a simple noncyclic permutation `c[(1 : fin 7), 2, 3] * c[0, 5]`
to show it takes a long time. TODO: is this because computing the cycle factors is slow?

-/


open Equiv Equiv.Perm List

namespace List

variable{α : Type _}[DecidableEq α]{l l' : List α}

-- error in GroupTheory.Perm.ConcreteCycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem form_perm_disjoint_iff
(hl : nodup l)
(hl' : nodup l')
(hn : «expr ≤ »(2, l.length))
(hn' : «expr ≤ »(2, l'.length)) : «expr ↔ »(perm.disjoint (form_perm l) (form_perm l'), l.disjoint l') :=
begin
  rw ["[", expr disjoint_iff_eq_or_eq, ",", expr list.disjoint, "]"] [],
  split,
  { rintro [ident h, ident x, ident hx, ident hx'],
    specialize [expr h x],
    rw ["[", expr form_perm_apply_mem_eq_self_iff _ hl _ hx, ",", expr form_perm_apply_mem_eq_self_iff _ hl' _ hx', "]"] ["at", ident h],
    rcases [expr h, "with", ident hl, "|", ident hl']; linarith [] [] [] },
  { intros [ident h, ident x],
    by_cases [expr hx, ":", expr «expr ∈ »(x, l)]; by_cases [expr hx', ":", expr «expr ∈ »(x, l')],
    { exact [expr (h hx hx').elim] },
    all_goals { have [] [] [":=", expr form_perm_eq_self_of_not_mem _ _ «expr‹ ›»(_)],
      tauto [] } }
end

-- error in GroupTheory.Perm.ConcreteCycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_cycle_form_perm (hl : nodup l) (hn : «expr ≤ »(2, l.length)) : is_cycle (form_perm l) :=
begin
  cases [expr l] ["with", ident x, ident l],
  { norm_num [] ["at", ident hn] },
  induction [expr l] [] ["with", ident y, ident l, ident IH] ["generalizing", ident x],
  { norm_num [] ["at", ident hn] },
  { use [expr x],
    split,
    { rwa [expr form_perm_apply_mem_ne_self_iff _ hl _ (mem_cons_self _ _)] [] },
    { intros [ident w, ident hw],
      have [] [":", expr «expr ∈ »(w, [«expr :: »/«expr :: »/«expr :: »](x, [«expr :: »/«expr :: »/«expr :: »](y, l)))] [":=", expr mem_of_form_perm_ne_self _ _ hw],
      obtain ["⟨", ident k, ",", ident hk, ",", ident rfl, "⟩", ":=", expr nth_le_of_mem this],
      use [expr k],
      simp [] [] ["only"] ["[", expr zpow_coe_nat, ",", expr form_perm_pow_apply_head _ _ hl k, ",", expr nat.mod_eq_of_lt hk, "]"] [] [] } }
end

theorem pairwise_same_cycle_form_perm (hl : nodup l) (hn : 2 ≤ l.length) : Pairwise l.form_perm.same_cycle l :=
  pairwise.imp_mem.mpr
    (pairwise_of_forall
      fun x y hx hy =>
        (is_cycle_form_perm hl hn).SameCycle ((form_perm_apply_mem_ne_self_iff _ hl _ hx).mpr hn)
          ((form_perm_apply_mem_ne_self_iff _ hl _ hy).mpr hn))

theorem cycle_of_form_perm (hl : nodup l) (hn : 2 ≤ l.length) x : cycle_of l.attach.form_perm x = l.attach.form_perm :=
  have hn : 2 ≤ l.attach.length :=
    by 
      rwa [←length_attach] at hn 
  have hl : l.attach.nodup :=
    by 
      rwa [←nodup_attach] at hl
  (is_cycle_form_perm hl hn).cycle_of_eq ((form_perm_apply_mem_ne_self_iff _ hl _ (mem_attach _ _)).mpr hn)

theorem cycle_type_form_perm (hl : nodup l) (hn : 2 ≤ l.length) : cycle_type l.attach.form_perm = {l.length} :=
  by 
    rw [←length_attach] at hn 
    rw [←nodup_attach] at hl 
    rw [cycle_type_eq [l.attach.form_perm]]
    ·
      simp only [map, Function.comp_app]
      rw [support_form_perm_of_nodup _ hl, card_to_finset, erase_dup_eq_self.mpr hl]
      ·
        simpa
      ·
        intro x h 
        simpa [h, Nat.succ_le_succ_iff] using hn
    ·
      simp 
    ·
      simpa using is_cycle_form_perm hl hn
    ·
      simp 

theorem form_perm_apply_mem_eq_next (hl : nodup l) (x : α) (hx : x ∈ l) : form_perm l x = next l x hx :=
  by 
    obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx 
    rw [next_nth_le _ hl, form_perm_apply_nth_le _ hl]

end List

namespace Cycle

variable{α : Type _}[DecidableEq α](s s' : Cycle α)

/--
A cycle `s : cycle α` , given `nodup s` can be interpreted as a `equiv.perm α`
where each element in the list is permuted to the next one, defined as `form_perm`.
-/
def form_perm : ∀ s : Cycle α h : nodup s, Equiv.Perm α :=
  fun s =>
    Quot.hrecOnₓ s (fun l h => form_perm l)
      fun l₁ l₂ h : l₁ ~r l₂ =>
        by 
          ext
          ·
            exact h.nodup_iff
          ·
            intro h₁ h₂ _ 
            exact heq_of_eq (form_perm_eq_of_is_rotated h₁ h)

@[simp]
theorem form_perm_coe (l : List α) (hl : l.nodup) : form_perm (l : Cycle α) hl = l.form_perm :=
  rfl

theorem form_perm_subsingleton (s : Cycle α) (h : Subsingleton s) : form_perm s h.nodup = 1 :=
  by 
    induction s using Quot.induction_on 
    simp only [form_perm_coe, mk_eq_coe]
    simp only [length_subsingleton_iff, length_coe, mk_eq_coe] at h 
    cases' s with hd tl
    ·
      simp 
    ·
      simp only [length_eq_zero, add_le_iff_nonpos_left, List.length, nonpos_iff_eq_zero] at h 
      simp [h]

theorem is_cycle_form_perm (s : Cycle α) (h : nodup s) (hn : Nontrivial s) : is_cycle (form_perm s h) :=
  by 
    induction s using Quot.induction_on 
    exact List.is_cycle_form_perm h (length_nontrivial hn)

theorem support_form_perm [Fintype α] (s : Cycle α) (h : nodup s) (hn : Nontrivial s) :
  support (form_perm s h) = s.to_finset :=
  by 
    induction s using Quot.induction_on 
    refine' support_form_perm_of_nodup s h _ 
    rintro _ rfl 
    simpa [Nat.succ_le_succ_iff] using length_nontrivial hn

theorem form_perm_eq_self_of_not_mem (s : Cycle α) (h : nodup s) (x : α) (hx : x ∉ s) : form_perm s h x = x :=
  by 
    induction s using Quot.induction_on 
    simpa using List.form_perm_eq_self_of_not_mem _ _ hx

theorem form_perm_apply_mem_eq_next (s : Cycle α) (h : nodup s) (x : α) (hx : x ∈ s) :
  form_perm s h x = next s h x hx :=
  by 
    induction s using Quot.induction_on 
    simpa using List.form_perm_apply_mem_eq_next h _ _

theorem form_perm_reverse (s : Cycle α) (h : nodup s) :
  form_perm s.reverse (nodup_reverse_iff.mpr h) = form_perm s h⁻¹ :=
  by 
    induction s using Quot.induction_on 
    simpa using form_perm_reverse _ h

theorem form_perm_eq_form_perm_iff {α : Type _} [DecidableEq α] {s s' : Cycle α} {hs : s.nodup} {hs' : s'.nodup} :
  s.form_perm hs = s'.form_perm hs' ↔ s = s' ∨ s.subsingleton ∧ s'.subsingleton :=
  by 
    rw [Cycle.length_subsingleton_iff, Cycle.length_subsingleton_iff]
    revert s s' 
    intro s s' 
    apply Quotientₓ.induction_on₂' s s' 
    intro l l' 
    simpa using form_perm_eq_form_perm_iff

end Cycle

variable{α : Type _}

namespace Equiv.Perm

variable[Fintype α][DecidableEq α](p : Equiv.Perm α)(x : α)

/--
`equiv.perm.to_list (f : perm α) (x : α)` generates the list `[x, f x, f (f x), ...]`
until looping. That means when `f x = x`, `to_list f x = []`.
-/
def to_list : List α :=
  (List.range (cycle_of p x).support.card).map fun k => (p^k) x

@[simp]
theorem to_list_one : to_list (1 : perm α) x = [] :=
  by 
    simp [to_list, cycle_of_one]

@[simp]
theorem to_list_eq_nil_iff {p : perm α} {x} : to_list p x = [] ↔ x ∉ p.support :=
  by 
    simp [to_list]

@[simp]
theorem length_to_list : length (to_list p x) = (cycle_of p x).support.card :=
  by 
    simp [to_list]

theorem to_list_ne_singleton (y : α) : to_list p x ≠ [y] :=
  by 
    intro H 
    simpa [card_support_ne_one] using congr_argₓ length H

theorem two_le_length_to_list_iff_mem_support {p : perm α} {x : α} : 2 ≤ length (to_list p x) ↔ x ∈ p.support :=
  by 
    simp 

theorem length_to_list_pos_of_mem_support (h : x ∈ p.support) : 0 < length (to_list p x) :=
  zero_lt_two.trans_le (two_le_length_to_list_iff_mem_support.mpr h)

theorem nth_le_to_list (n : ℕ) (hn : n < length (to_list p x)) : nth_le (to_list p x) n hn = (p^n) x :=
  by 
    simp [to_list]

theorem to_list_nth_le_zero (h : x ∈ p.support) : (to_list p x).nthLe 0 (length_to_list_pos_of_mem_support _ _ h) = x :=
  by 
    simp [to_list]

variable{p}{x}

theorem mem_to_list_iff {y : α} : y ∈ to_list p x ↔ same_cycle p x y ∧ x ∈ p.support :=
  by 
    simp only [to_list, mem_range, mem_map]
    split 
    ·
      rintro ⟨n, hx, rfl⟩
      refine' ⟨⟨n, rfl⟩, _⟩
      contrapose! hx 
      rw [←support_cycle_of_eq_nil_iff] at hx 
      simp [hx]
    ·
      rintro ⟨h, hx⟩
      simpa using same_cycle.nat_of_mem_support _ h hx

-- error in GroupTheory.Perm.ConcreteCycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nodup_to_list (p : perm α) (x : α) : nodup (to_list p x) :=
begin
  by_cases [expr hx, ":", expr «expr = »(p x, x)],
  { rw ["[", "<-", expr not_mem_support, ",", "<-", expr to_list_eq_nil_iff, "]"] ["at", ident hx],
    simp [] [] [] ["[", expr hx, "]"] [] [] },
  have [ident hc] [":", expr is_cycle (cycle_of p x)] [":=", expr is_cycle_cycle_of p hx],
  rw [expr nodup_iff_nth_le_inj] [],
  rintros [ident n, ident m, ident hn, ident hm],
  rw ["[", expr length_to_list, ",", "<-", expr order_of_is_cycle hc, "]"] ["at", ident hm, ident hn],
  rw ["[", "<-", expr cycle_of_apply_self, ",", "<-", expr ne.def, ",", "<-", expr mem_support, "]"] ["at", ident hx],
  rw ["[", expr nth_le_to_list, ",", expr nth_le_to_list, ",", "<-", expr cycle_of_pow_apply_self p x n, ",", "<-", expr cycle_of_pow_apply_self p x m, "]"] [],
  cases [expr n] []; cases [expr m] [],
  { simp [] [] [] [] [] [] },
  { rw ["[", "<-", expr hc.mem_support_pos_pow_iff_of_lt_order_of m.zero_lt_succ hm, ",", expr mem_support, ",", expr cycle_of_pow_apply_self, "]"] ["at", ident hx],
    simp [] [] [] ["[", expr hx.symm, "]"] [] [] },
  { rw ["[", "<-", expr hc.mem_support_pos_pow_iff_of_lt_order_of n.zero_lt_succ hn, ",", expr mem_support, ",", expr cycle_of_pow_apply_self, "]"] ["at", ident hx],
    simp [] [] [] ["[", expr hx, "]"] [] [] },
  intro [ident h],
  have [ident hn'] [":", expr «expr¬ »(«expr ∣ »(order_of (p.cycle_of x), n.succ))] [":=", expr nat.not_dvd_of_pos_of_lt n.zero_lt_succ hn],
  have [ident hm'] [":", expr «expr¬ »(«expr ∣ »(order_of (p.cycle_of x), m.succ))] [":=", expr nat.not_dvd_of_pos_of_lt m.zero_lt_succ hm],
  rw ["<-", expr hc.support_pow_eq_iff] ["at", ident hn', ident hm'],
  rw ["[", "<-", expr nat.mod_eq_of_lt hn, ",", "<-", expr nat.mod_eq_of_lt hm, ",", "<-", expr pow_inj_mod, "]"] [],
  refine [expr support_congr _ _],
  { rw ["[", expr hm', ",", expr hn', "]"] [],
    exact [expr finset.subset.refl _] },
  { rw [expr hm'] [],
    intros [ident y, ident hy],
    obtain ["⟨", ident k, ",", ident rfl, "⟩", ":=", expr hc.exists_pow_eq (mem_support.mp hx) (mem_support.mp hy)],
    rw ["[", "<-", expr mul_apply, ",", expr (commute.pow_pow_self _ _ _).eq, ",", expr mul_apply, ",", expr h, ",", "<-", expr mul_apply, ",", "<-", expr mul_apply, ",", expr (commute.pow_pow_self _ _ _).eq, "]"] [] }
end

theorem next_to_list_eq_apply (p : perm α) (x y : α) (hy : y ∈ to_list p x) : next (to_list p x) y hy = p y :=
  by 
    rw [mem_to_list_iff] at hy 
    obtain ⟨k, hk, hk'⟩ := hy.left.nat_of_mem_support _ hy.right 
    rw
      [←nth_le_to_list p x k
        (by 
          simpa using hk)] at
      hk' 
    simpRw [←hk']
    rw [next_nth_le _ (nodup_to_list _ _), nth_le_to_list, nth_le_to_list, ←mul_apply, ←pow_succₓ, length_to_list,
      pow_apply_eq_pow_mod_order_of_cycle_of_apply p (k+1), order_of_is_cycle]
    exact is_cycle_cycle_of _ (mem_support.mp hy.right)

theorem to_list_pow_apply_eq_rotate (p : perm α) (x : α) (k : ℕ) : p.to_list ((p^k) x) = (p.to_list x).rotate k :=
  by 
    apply ext_le
    ·
      simp 
    ·
      intro n hn hn' 
      rw [nth_le_to_list, nth_le_rotate, nth_le_to_list, length_to_list, pow_mod_card_support_cycle_of_self_apply,
        pow_addₓ, mul_apply]

theorem same_cycle.to_list_is_rotated {f : perm α} {x y : α} (h : same_cycle f x y) : to_list f x ~r to_list f y :=
  by 
    byCases' hx : x ∈ f.support
    ·
      obtain ⟨_ | k, hk, hy⟩ := h.nat_of_mem_support _ hx
      ·
        simp only [coe_one, id.def, pow_zeroₓ] at hy 
        simp [hy]
      use k.succ 
      rw [←to_list_pow_apply_eq_rotate, hy]
    ·
      rw [to_list_eq_nil_iff.mpr hx, is_rotated_nil_iff', eq_comm, to_list_eq_nil_iff]
      rwa [←h.mem_support_iff]

theorem pow_apply_mem_to_list_iff_mem_support {n : ℕ} : (p^n) x ∈ p.to_list x ↔ x ∈ p.support :=
  by 
    rw [mem_to_list_iff, and_iff_right_iff_imp]
    refine' fun _ => same_cycle.symm _ 
    rw [same_cycle_pow_left_iff]

theorem to_list_form_perm_nil (x : α) : to_list (form_perm ([] : List α)) x = [] :=
  by 
    simp 

theorem to_list_form_perm_singleton (x y : α) : to_list (form_perm [x]) y = [] :=
  by 
    simp 

-- error in GroupTheory.Perm.ConcreteCycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem to_list_form_perm_nontrivial
(l : list α)
(hl : «expr ≤ »(2, l.length))
(hn : nodup l) : «expr = »(to_list (form_perm l) (l.nth_le 0 (zero_lt_two.trans_le hl)), l) :=
begin
  have [ident hc] [":", expr l.form_perm.is_cycle] [":=", expr list.is_cycle_form_perm hn hl],
  have [ident hs] [":", expr «expr = »(l.form_perm.support, l.to_finset)] [],
  { refine [expr support_form_perm_of_nodup _ hn _],
    rintro ["_", ident rfl],
    simpa [] [] [] ["[", expr nat.succ_le_succ_iff, "]"] [] ["using", expr hl] },
  rw ["[", expr to_list, ",", expr hc.cycle_of_eq (mem_support.mp _), ",", expr hs, ",", expr card_to_finset, ",", expr erase_dup_eq_self.mpr hn, "]"] [],
  { refine [expr list.ext_le (by simp [] [] [] [] [] []) (λ k hk hk', _)],
    simp [] [] [] ["[", expr form_perm_pow_apply_nth_le _ hn, ",", expr nat.mod_eq_of_lt hk', "]"] [] [] },
  { simpa [] [] [] ["[", expr hs, "]"] [] ["using", expr nth_le_mem _ _ _] }
end

-- error in GroupTheory.Perm.ConcreteCycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem to_list_form_perm_is_rotated_self
(l : list α)
(hl : «expr ≤ »(2, l.length))
(hn : nodup l)
(x : α)
(hx : «expr ∈ »(x, l)) : «expr ~r »(to_list (form_perm l) x, l) :=
begin
  obtain ["⟨", ident k, ",", ident hk, ",", ident rfl, "⟩", ":=", expr nth_le_of_mem hx],
  have [ident hr] [":", expr «expr ~r »(l, l.rotate k)] [":=", expr ⟨k, rfl⟩],
  rw [expr form_perm_eq_of_is_rotated hn hr] [],
  rw ["<-", expr nth_le_rotate' l k k] [],
  simp [] [] ["only"] ["[", expr nat.mod_eq_of_lt hk, ",", expr tsub_add_cancel_of_le hk.le, ",", expr nat.mod_self, "]"] [] [],
  rw ["[", expr to_list_form_perm_nontrivial, "]"] [],
  { simp [] [] [] [] [] [] },
  { simpa [] [] [] [] [] ["using", expr hl] },
  { simpa [] [] [] [] [] ["using", expr hn] }
end

theorem form_perm_to_list (f : perm α) (x : α) : form_perm (to_list f x) = f.cycle_of x :=
  by 
    byCases' hx : f x = x
    ·
      rw [(cycle_of_eq_one_iff f).mpr hx, to_list_eq_nil_iff.mpr (not_mem_support.mpr hx), form_perm_nil]
    ext y 
    byCases' hy : same_cycle f x y
    ·
      obtain ⟨k, hk, rfl⟩ := hy.nat_of_mem_support _ (mem_support.mpr hx)
      rw [cycle_of_apply_apply_pow_self, List.form_perm_apply_mem_eq_next (nodup_to_list f x), next_to_list_eq_apply,
        pow_succₓ, mul_apply]
      rw [mem_to_list_iff]
      exact ⟨⟨k, rfl⟩, mem_support.mpr hx⟩
    ·
      rw [cycle_of_apply_of_not_same_cycle hy, form_perm_apply_of_not_mem]
      simp [mem_to_list_iff, hy]

theorem is_cycle.exists_unique_cycle {f : perm α} (hf : is_cycle f) : ∃!s : Cycle α, ∃ h : s.nodup, s.form_perm h = f :=
  by 
    obtain ⟨x, hx, hy⟩ := id hf 
    refine' ⟨f.to_list x, ⟨nodup_to_list f x, _⟩, _⟩
    ·
      simp [form_perm_to_list, hf.cycle_of_eq hx]
    ·
      rintro ⟨l⟩ ⟨hn, rfl⟩
      simp only [Cycle.mk_eq_coe, Cycle.coe_eq_coe, Subtype.coe_mk, Cycle.form_perm_coe]
      refine' (to_list_form_perm_is_rotated_self _ _ hn _ _).symm
      ·
        contrapose! hx 
        suffices  : form_perm l = 1
        ·
          simp [this]
        rw [form_perm_eq_one_iff _ hn]
        exact Nat.le_of_lt_succₓ hx
      ·
        rw [←mem_to_finset]
        refine' support_form_perm_le l _ 
        simpa using hx

theorem is_cycle.exists_unique_cycle_subtype {f : perm α} (hf : is_cycle f) :
  ∃!s : { s : Cycle α // s.nodup }, (s : Cycle α).formPerm s.prop = f :=
  by 
    obtain ⟨s, ⟨hs, rfl⟩, hs'⟩ := hf.exists_unique_cycle 
    refine' ⟨⟨s, hs⟩, rfl, _⟩
    rintro ⟨t, ht⟩ ht' 
    simpa using hs' _ ⟨ht, ht'⟩

theorem is_cycle.exists_unique_cycle_nontrivial_subtype {f : perm α} (hf : is_cycle f) :
  ∃!s : { s : Cycle α // s.nodup ∧ s.nontrivial }, (s : Cycle α).formPerm s.prop.left = f :=
  by 
    obtain ⟨⟨s, hn⟩, hs, hs'⟩ := hf.exists_unique_cycle_subtype 
    refine' ⟨⟨s, hn, _⟩, _, _⟩
    ·
      rw [hn.nontrivial_iff]
      subst f 
      intro H 
      refine' hf.ne_one _ 
      simpa using Cycle.form_perm_subsingleton _ H
    ·
      simpa using hs
    ·
      rintro ⟨t, ht, ht'⟩ ht'' 
      simpa using hs' ⟨t, ht⟩ ht''

-- error in GroupTheory.Perm.ConcreteCycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Given a cyclic `f : perm α`, generate the `cycle α` in the order
of application of `f`. Implemented by finding an element `x : α`
in the support of `f` in `finset.univ`, and iterating on using
`equiv.perm.to_list f x`.
-/ def to_cycle (f : perm α) (hf : is_cycle f) : cycle α :=
multiset.rec_on (finset.univ : finset α).val (quot.mk _ «expr[ , ]»([])) (λ
 x
 s
 l, if «expr = »(f x, x) then l else to_list f x) (by { intros [ident x, ident y, ident m, ident s],
   refine [expr heq_of_eq _],
   split_ifs [] ["with", ident hx, ident hy, ident hy]; try { refl },
   { have [ident hc] [":", expr same_cycle f x y] [":=", expr is_cycle.same_cycle hf hx hy],
     exact [expr quotient.sound' hc.to_list_is_rotated] } })

-- error in GroupTheory.Perm.ConcreteCycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem to_cycle_eq_to_list
(f : perm α)
(hf : is_cycle f)
(x : α)
(hx : «expr ≠ »(f x, x)) : «expr = »(to_cycle f hf, to_list f x) :=
begin
  have [ident key] [":", expr «expr = »((finset.univ : finset α).val, «expr ::ₘ »(x, finset.univ.val.erase x))] [],
  { simp [] [] [] [] [] [] },
  rw ["[", expr to_cycle, ",", expr key, "]"] [],
  simp [] [] [] ["[", expr hx, "]"] [] []
end

theorem nodup_to_cycle (f : perm α) (hf : is_cycle f) : (to_cycle f hf).Nodup :=
  by 
    obtain ⟨x, hx, -⟩ := id hf 
    simpa [to_cycle_eq_to_list f hf x hx] using nodup_to_list _ _

theorem nontrivial_to_cycle (f : perm α) (hf : is_cycle f) : (to_cycle f hf).Nontrivial :=
  by 
    obtain ⟨x, hx, -⟩ := id hf 
    simp [to_cycle_eq_to_list f hf x hx, hx, Cycle.nontrivial_coe_nodup_iff (nodup_to_list _ _)]

-- error in GroupTheory.Perm.ConcreteCycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Any cyclic `f : perm α` is isomorphic to the nontrivial `cycle α`
that corresponds to repeated application of `f`.
The forward direction is implemented by `equiv.perm.to_cycle`.
-/ def iso_cycle : «expr ≃ »({f : perm α // is_cycle f}, {s : cycle α // «expr ∧ »(s.nodup, s.nontrivial)}) :=
{ to_fun := λ f, ⟨to_cycle (f : perm α) f.prop, nodup_to_cycle f f.prop, nontrivial_to_cycle _ f.prop⟩,
  inv_fun := λ s, ⟨(s : cycle α).form_perm s.prop.left, (s : cycle α).is_cycle_form_perm _ s.prop.right⟩,
  left_inv := λ f, by { obtain ["⟨", ident x, ",", ident hx, ",", "-", "⟩", ":=", expr id f.prop],
    simpa [] [] [] ["[", expr to_cycle_eq_to_list (f : perm α) f.prop x hx, ",", expr form_perm_to_list, ",", expr subtype.ext_iff, "]"] [] ["using", expr f.prop.cycle_of_eq hx] },
  right_inv := λ s, by { rcases [expr s, "with", "⟨", "⟨", ident s, "⟩", ",", ident hn, ",", ident ht, "⟩"],
    obtain ["⟨", ident x, ",", "-", ",", "-", ",", ident hx, ",", "-", "⟩", ":=", expr id ht],
    have [ident hl] [":", expr «expr ≤ »(2, s.length)] [":=", expr by simpa [] [] [] [] [] ["using", expr cycle.length_nontrivial ht]],
    simp [] [] ["only"] ["[", expr cycle.mk_eq_coe, ",", expr cycle.nodup_coe_iff, ",", expr cycle.mem_coe_iff, ",", expr subtype.coe_mk, ",", expr cycle.form_perm_coe, "]"] [] ["at", ident hn, ident hx, "⊢"],
    rw [expr to_cycle_eq_to_list _ _ x] [],
    { refine [expr quotient.sound' _],
      exact [expr to_list_form_perm_is_rotated_self _ hl hn _ hx] },
    { rw ["[", "<-", expr mem_support, ",", expr support_form_perm_of_nodup _ hn, "]"] [],
      { simpa [] [] [] [] [] ["using", expr hx] },
      { rintro ["_", ident rfl],
        simpa [] [] [] ["[", expr nat.succ_le_succ_iff, "]"] [] ["using", expr hl] } } } }

/--
Any cyclic `f : perm α` is isomorphic to the nontrivial `cycle α`
that corresponds to repeated application of `f`.
The forward direction is implemented by finding this `cycle α` using `fintype.choose`.
-/
def iso_cycle' : { f : perm α // is_cycle f } ≃ { s : Cycle α // s.nodup ∧ s.nontrivial } :=
  { toFun := fun f => Fintype.choose _ f.prop.exists_unique_cycle_nontrivial_subtype,
    invFun := fun s => ⟨(s : Cycle α).formPerm s.prop.left, (s : Cycle α).is_cycle_form_perm _ s.prop.right⟩,
    left_inv :=
      fun f =>
        by 
          simpa [Subtype.ext_iff] using Fintype.choose_spec _ f.prop.exists_unique_cycle_nontrivial_subtype,
    right_inv :=
      fun ⟨s, hs, ht⟩ =>
        by 
          simp [Subtype.coe_mk]
          convert Fintype.choose_subtype_eq (fun s' : Cycle α => s'.nodup ∧ s'.nontrivial) _ 
          ext ⟨s', hs', ht'⟩
          simp [Cycle.form_perm_eq_form_perm_iff, iff_not_comm.mp hs.nontrivial_iff, iff_not_comm.mp hs'.nontrivial_iff,
            ht] }

-- error in GroupTheory.Perm.ConcreteCycle: ././Mathport/Syntax/Translate/Basic.lean:1096:9: unsupported: advanced notation (l:(foldr `, ` (h t, list.cons h t) list.nil `]`))
notation
`c[`
l:(foldr `, ` (h t, list.cons h t) list.nil `]`) := cycle.form_perm «expr↑ »(l) (cycle.nodup_coe_iff.mpr exprdec_trivial())

instance repr_perm [HasRepr α] : HasRepr (perm α) :=
  ⟨fun f =>
      reprₓ
        (Multiset.pmap (fun g : perm α hg : g.is_cycle => iso_cycle ⟨g, hg⟩) (perm.cycle_factors_finset f).val
          fun g hg => (mem_cycle_factors_finset_iff.mp (Finset.mem_def.mpr hg)).left)⟩

end Equiv.Perm

