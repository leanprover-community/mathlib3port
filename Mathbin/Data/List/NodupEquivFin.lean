import Mathbin.Data.Fin.Basic 
import Mathbin.Data.List.Sort 
import Mathbin.Data.List.Duplicate

/-!
# Equivalence between `fin (length l)` and elements of a list

Given a list `l`,

* if `l` has no duplicates, then `list.nodup.nth_le_equiv` is the equivalence between
  `fin (length l)` and `{x // x ∈ l}` sending `⟨i, hi⟩` to `⟨nth_le l i hi, _⟩` with the inverse
  sending `⟨x, hx⟩` to `⟨index_of x l, _⟩`;

* if `l` has no duplicates and contains every element of a type `α`, then
  `list.nodup.nth_le_equiv_of_forall_mem_list` defines an equivalence between
  `fin (length l)` and `α`;  if `α` does not have decidable equality, then
  there is a bijection `list.nodup.nth_le_bijection_of_forall_mem_list`;

* if `l` is sorted w.r.t. `(<)`, then `list.sorted.nth_le_iso` is the same bijection reinterpreted
  as an `order_iso`.

-/


namespace List

variable{α : Type _}

namespace Nodup

/-- If `l` lists all the elements of `α` without duplicates, then `list.nth_le` defines
a bijection `fin l.length → α`.  See `list.nodup.nth_le_equiv_of_forall_mem_list`
for a version giving an equivalence when there is decidable equality. -/
@[simps]
def nth_le_bijection_of_forall_mem_list (l : List α) (nd : l.nodup) (h : ∀ x : α, x ∈ l) :
  { f : Finₓ l.length → α // Function.Bijective f } :=
  ⟨fun i => l.nth_le i i.property, fun i j h => Finₓ.ext$ (nd.nth_le_inj_iff _ _).1 h,
    fun x =>
      let ⟨i, hi, hl⟩ := List.mem_iff_nth_le.1 (h x)
      ⟨⟨i, hi⟩, hl⟩⟩

variable[DecidableEq α]

/-- If `l` has no duplicates, then `list.nth_le` defines an equivalence between `fin (length l)` and
the set of elements of `l`. -/
@[simps]
def nth_le_equiv (l : List α) (H : nodup l) : Finₓ (length l) ≃ { x // x ∈ l } :=
  { toFun := fun i => ⟨nth_le l i i.2, nth_le_mem l i i.2⟩,
    invFun := fun x => ⟨index_of («expr↑ » x) l, index_of_lt_length.2 x.2⟩,
    left_inv :=
      fun i =>
        by 
          simp [H],
    right_inv :=
      fun x =>
        by 
          simp  }

/-- If `l` lists all the elements of `α` without duplicates, then `list.nth_le` defines
an equivalence between `fin l.length` and `α`.

See `list.nodup.nth_le_bijection_of_forall_mem_list` for a version without
decidable equality. -/
@[simps]
def nth_le_equiv_of_forall_mem_list (l : List α) (nd : l.nodup) (h : ∀ x : α, x ∈ l) : Finₓ l.length ≃ α :=
  { toFun := fun i => l.nth_le i i.2, invFun := fun a => ⟨_, index_of_lt_length.2 (h a)⟩,
    left_inv :=
      fun i =>
        by 
          simp [nd],
    right_inv :=
      fun a =>
        by 
          simp  }

end Nodup

namespace Sorted

variable[Preorderₓ α]{l : List α}

theorem nth_le_mono (h : l.sorted (· ≤ ·)) : Monotone fun i : Finₓ l.length => l.nth_le i i.2 :=
  fun i j => h.rel_nth_le_of_le _ _

theorem nth_le_strict_mono (h : l.sorted (· < ·)) : StrictMono fun i : Finₓ l.length => l.nth_le i i.2 :=
  fun i j => h.rel_nth_le_of_lt _ _

variable[DecidableEq α]

/-- If `l` is a list sorted w.r.t. `(<)`, then `list.nth_le` defines an order isomorphism between
`fin (length l)` and the set of elements of `l`. -/
def nth_le_iso (l : List α) (H : sorted (· < ·) l) : Finₓ (length l) ≃o { x // x ∈ l } :=
  { toEquiv := H.nodup.nth_le_equiv l, map_rel_iff' := fun i j => H.nth_le_strict_mono.le_iff_le }

variable(H : sorted (· < ·) l){x : { x // x ∈ l }}{i : Finₓ l.length}

@[simp]
theorem coe_nth_le_iso_apply : (H.nth_le_iso l i : α) = nth_le l i i.2 :=
  rfl

@[simp]
theorem coe_nth_le_iso_symm_apply : ((H.nth_le_iso l).symm x : ℕ) = index_of («expr↑ » x) l :=
  rfl

end Sorted

section Sublist

-- error in Data.List.NodupEquivFin: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If there is `f`, an order-preserving embedding of `ℕ` into `ℕ` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`,
then `sublist l l'`.
-/
theorem sublist_of_order_embedding_nth_eq
{l l' : list α}
(f : «expr ↪o »(exprℕ(), exprℕ()))
(hf : ∀ ix : exprℕ(), «expr = »(l.nth ix, l'.nth (f ix))) : «expr <+ »(l, l') :=
begin
  induction [expr l] [] ["with", ident hd, ident tl, ident IH] ["generalizing", ident l', ident f],
  { simp [] [] [] [] [] [] },
  have [] [":", expr «expr = »(some hd, _)] [":=", expr hf 0],
  rw ["[", expr eq_comm, ",", expr list.nth_eq_some, "]"] ["at", ident this],
  obtain ["⟨", ident w, ",", ident h, "⟩", ":=", expr this],
  let [ident f'] [":", expr «expr ↪o »(exprℕ(), exprℕ())] [":=", expr order_embedding.of_map_le_iff (λ
    i, «expr - »(f «expr + »(i, 1), «expr + »(f 0, 1))) (λ
    a
    b, by simp [] [] [] ["[", expr tsub_le_tsub_iff_right, ",", expr nat.succ_le_iff, ",", expr nat.lt_succ_iff, "]"] [] [])],
  have [] [":", expr ∀ ix, «expr = »(tl.nth ix, (l'.drop «expr + »(f 0, 1)).nth (f' ix))] [],
  { intro [ident ix],
    simp [] [] [] ["[", expr list.nth_drop, ",", expr add_tsub_cancel_of_le, ",", expr nat.succ_le_iff, ",", "<-", expr hf, "]"] [] [] },
  rw ["[", "<-", expr list.take_append_drop «expr + »(f 0, 1) l', ",", "<-", expr list.singleton_append, "]"] [],
  apply [expr list.sublist.append _ (IH _ this)],
  rw ["[", expr list.singleton_sublist, ",", "<-", expr h, ",", expr l'.nth_le_take _ (nat.lt_succ_self _), "]"] [],
  apply [expr list.nth_le_mem]
end

/--
A `l : list α` is `sublist l l'` for `l' : list α` iff
there is `f`, an order-preserving embedding of `ℕ` into `ℕ` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`.
-/
theorem sublist_iff_exists_order_embedding_nth_eq {l l' : List α} :
  l <+ l' ↔ ∃ f : ℕ ↪o ℕ, ∀ ix : ℕ, l.nth ix = l'.nth (f ix) :=
  by 
    split 
    ·
      intro H 
      induction' H with xs ys y H IH xs ys x H IH
      ·
        simp 
      ·
        obtain ⟨f, hf⟩ := IH 
        refine'
          ⟨f.trans
              (OrderEmbedding.ofStrictMono (·+1)
                fun _ =>
                  by 
                    simp ),
            _⟩
        simpa using hf
      ·
        obtain ⟨f, hf⟩ := IH 
        refine' ⟨OrderEmbedding.ofMapLeIff (fun ix : ℕ => if ix = 0 then 0 else (f ix.pred).succ) _, _⟩
        ·
          rintro ⟨_ | a⟩ ⟨_ | b⟩ <;> simp [Nat.succ_le_succ_iff]
        ·
          rintro ⟨_ | i⟩
          ·
            simp 
          ·
            simpa using hf _
    ·
      rintro ⟨f, hf⟩
      exact sublist_of_order_embedding_nth_eq f hf

-- error in Data.List.NodupEquivFin: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
A `l : list α` is `sublist l l'` for `l' : list α` iff
there is `f`, an order-preserving embedding of `fin l.length` into `fin l'.length` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`.
-/
theorem sublist_iff_exists_fin_order_embedding_nth_le_eq
{l
 l' : list α} : «expr ↔ »(«expr <+ »(l, l'), «expr∃ , »((f : «expr ↪o »(fin l.length, fin l'.length)), ∀
  ix : fin l.length, «expr = »(l.nth_le ix ix.is_lt, l'.nth_le (f ix) (f ix).is_lt))) :=
begin
  rw [expr sublist_iff_exists_order_embedding_nth_eq] [],
  split,
  { rintro ["⟨", ident f, ",", ident hf, "⟩"],
    have [ident h] [":", expr ∀ {i : exprℕ()} (h : «expr < »(i, l.length)), «expr < »(f i, l'.length)] [],
    { intros [ident i, ident hi],
      specialize [expr hf i],
      rw ["[", expr nth_le_nth hi, ",", expr eq_comm, ",", expr nth_eq_some, "]"] ["at", ident hf],
      obtain ["⟨", ident h, ",", "-", "⟩", ":=", expr hf],
      exact [expr h] },
    refine [expr ⟨order_embedding.of_map_le_iff (λ ix, ⟨f ix, h ix.is_lt⟩) _, _⟩],
    { simp [] [] [] [] [] [] },
    { intro [ident i],
      apply [expr option.some_injective],
      simpa [] [] [] ["[", "<-", expr nth_le_nth, "]"] [] ["using", expr hf _] } },
  { rintro ["⟨", ident f, ",", ident hf, "⟩"],
    refine [expr ⟨order_embedding.of_strict_mono (λ
       i, if hi : «expr < »(i, l.length) then f ⟨i, hi⟩ else «expr + »(i, l'.length)) _, _⟩],
    { intros [ident i, ident j, ident h],
      dsimp ["only"] [] [] [],
      split_ifs [] ["with", ident hi, ident hj, ident hj, ident hi],
      { simpa [] [] [] [] [] ["using", expr h] },
      { rw [expr add_comm] [],
        exact [expr lt_add_of_lt_of_pos (fin.is_lt _) (i.zero_le.trans_lt h)] },
      { exact [expr absurd (h.trans hj) hi] },
      { simpa [] [] [] [] [] ["using", expr h] } },
    { intro [ident i],
      simp [] [] ["only"] ["[", expr order_embedding.coe_of_strict_mono, "]"] [] [],
      split_ifs [] ["with", ident hi],
      { rw ["[", expr nth_le_nth hi, ",", expr nth_le_nth, ",", "<-", expr hf, "]"] [],
        simp [] [] [] [] [] [] },
      { rw ["[", expr nth_len_le, ",", expr nth_len_le, "]"] [],
        { simp [] [] [] [] [] [] },
        { simpa [] [] [] [] [] ["using", expr hi] } } } }
end

/--
An element `x : α` of `l : list α` is a duplicate iff it can be found
at two distinct indices `n m : ℕ` inside the list `l`.
-/
theorem duplicate_iff_exists_distinct_nth_le {l : List α} {x : α} :
  l.duplicate x ↔
    ∃ (n : ℕ)(hn : n < l.length)(m : ℕ)(hm : m < l.length)(h : n < m), x = l.nth_le n hn ∧ x = l.nth_le m hm :=
  by 
    classical 
    rw [duplicate_iff_two_le_count, le_count_iff_repeat_sublist, sublist_iff_exists_fin_order_embedding_nth_le_eq]
    split 
    ·
      rintro ⟨f, hf⟩
      refine'
        ⟨f
            ⟨0,
              by 
                simp ⟩,
          Finₓ.is_lt _,
          f
            ⟨1,
              by 
                simp ⟩,
          Finₓ.is_lt _,
          by 
            simp ,
          _, _⟩
      ·
        simpa using
          hf
            ⟨0,
              by 
                simp ⟩
      ·
        simpa using
          hf
            ⟨1,
              by 
                simp ⟩
    ·
      rintro ⟨n, hn, m, hm, hnm, h, h'⟩
      refine' ⟨OrderEmbedding.ofStrictMono (fun i => if (i : ℕ) = 0 then ⟨n, hn⟩ else ⟨m, hm⟩) _, _⟩
      ·
        rintro ⟨⟨_ | i⟩, hi⟩ ⟨⟨_ | j⟩, hj⟩
        ·
          simp 
        ·
          simp [hnm]
        ·
          simp 
        ·
          simp only [Nat.lt_succ_iff, Nat.succ_le_succ_iff, repeat, length, nonpos_iff_eq_zero] at hi hj 
          simp [hi, hj]
      ·
        rintro ⟨⟨_ | i⟩, hi⟩
        ·
          simpa using h
        ·
          simpa using h'

end Sublist

end List

