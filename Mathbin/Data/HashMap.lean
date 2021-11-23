import Mathbin.Data.Array.Lemmas 
import Mathbin.Data.List.Join 
import Mathbin.Data.List.Range 
import Mathbin.Data.Pnat.Basic

/-!
# Hash maps

Defines a hash map data structure, representing a finite key-value map
with a value type that may depend on the key type.  The structure
requires a `nat`-valued hash function to associate keys to buckets.

## Main definitions

* `hash_map`: constructed with `mk_hash_map`.

## Implementation details

A hash map with key type `α` and (dependent) value type `β : α → Type*`
consists of an array of *buckets*, which are lists containing
key/value pairs for that bucket.  The hash function is taken modulo `n`
to assign keys to their respective bucket.  Because of this, some care
should be put into the hash function to ensure it evenly distributes
keys.

The bucket array is an `array`.  These have special VM support for
in-place modification if there is only ever one reference to them.  If
one takes special care to never keep references to old versions of a
hash map alive after updating it, then the hash map will be modified
in-place.  In this documentation, when we say a hash map is modified
in-place, we are assuming the API is being used in this manner.

When inserting (`hash_map.insert`), if the number of stored pairs (the
*size*) is going to exceed the number of buckets, then a new hash map
is first created with double the number of buckets and everything in
the old hash map is reinserted along with the new key/value pair.
Otherwise, the bucket array is modified in-place.  The amortized
running time of inserting $$n$$ elements into a hash map is $$O(n)$$.

When removing (`hash_map.erase`), the hash map is modified in-place.
The implementation does not reduce the number of buckets in the hash
map if the size gets too low.

## Tags

hash map

-/


universe u v w

/-- `bucket_array α β` is the underlying data type for `hash_map α β`,
  an array of linked lists of key-value pairs. -/
def BucketArray (α : Type u) (β : α → Type v) (n : ℕ+) :=
  Arrayₓ n (List (Σa, β a))

/-- Make a hash_map index from a `nat` hash value and a (positive) buffer size -/
def HashMap.mkIdx (n : ℕ+) (i : Nat) : Finₓ n :=
  ⟨i % n, Nat.mod_ltₓ _ n.2⟩

namespace BucketArray

section 

parameter {α : Type u}{β : α → Type v}(hash_fn : α → Nat)

variable{n : ℕ+}(data : BucketArray α β n)

instance  : Inhabited (BucketArray α β n) :=
  ⟨mkArray _ []⟩

/-- Read the bucket corresponding to an element -/
def read (a : α) : List (Σa, β a) :=
  let bidx := HashMap.mkIdx n (hash_fn a)
  data.read bidx

/-- Write the bucket corresponding to an element -/
def write (a : α) (l : List (Σa, β a)) : BucketArray α β n :=
  let bidx := HashMap.mkIdx n (hash_fn a)
  data.write bidx l

/-- Modify (read, apply `f`, and write) the bucket corresponding to an element -/
def modifyₓ (a : α) (f : List (Σa, β a) → List (Σa, β a)) : BucketArray α β n :=
  let bidx := HashMap.mkIdx n (hash_fn a)
  Arrayₓ.write data bidx (f (Arrayₓ.read data bidx))

/-- The list of all key-value pairs in the bucket list -/
def as_list : List (Σa, β a) :=
  data.to_list.join

theorem mem_as_list {a : Σa, β a} : a ∈ data.as_list ↔ ∃ i, a ∈ Arrayₓ.read data i :=
  have  :
    (∃ (l : List (Σa : α, β a))(i : Finₓ n.val), a ∈ l ∧ Arrayₓ.read data i = l) ↔
      ∃ i : Finₓ n.val, a ∈ Arrayₓ.read data i :=
    by 
      rw [exists_swap] <;>
        exact
          exists_congr
            fun i =>
              by 
                simp 
  by 
    simp [as_list] <;> simpa [Arrayₓ.Mem.def, and_comm]

/-- Fold a function `f` over the key-value pairs in the bucket list -/
def foldl {δ : Type w} (d : δ) (f : δ → ∀ a, β a → δ) : δ :=
  data.foldl d fun b d => b.foldl (fun r a => f r a.1 a.2) d

theorem foldl_eq {δ : Type w} (d : δ) (f : δ → ∀ a, β a → δ) :
  data.foldl d f = data.as_list.foldl (fun r a => f r a.1 a.2) d :=
  by 
    rw [foldl, as_list, List.foldl_join, ←Arrayₓ.to_list_foldl]

end 

end BucketArray

namespace HashMap

section 

parameter {α : Type u}{β : α → Type v}(hash_fn : α → Nat)

/-- Insert the pair `⟨a, b⟩` into the correct location in the bucket array
  (without checking for duplication) -/
def reinsert_aux {n} (data : BucketArray α β n) (a : α) (b : β a) : BucketArray α β n :=
  data.modify hash_fn a fun l => ⟨a, b⟩ :: l

theorem mk_as_list (n : ℕ+) : BucketArray.asList (mkArray n [] : BucketArray α β n) = [] :=
  List.eq_nil_iff_forall_not_memₓ.mpr$
    fun x m =>
      let ⟨i, h⟩ := (BucketArray.mem_as_list _).1 m 
      h

parameter [DecidableEq α]

/-- Search a bucket for a key `a` and return the value -/
def find_aux (a : α) : List (Σa, β a) → Option (β a)
| [] => none
| ⟨a', b⟩ :: t => if h : a' = a then some (Eq.recOnₓ h b) else find_aux t

-- error in Data.HashMap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_aux_iff
{a : α}
{b : β a} : ∀
{l : list «exprΣ , »((a), β a)}, (l.map sigma.fst).nodup → «expr ↔ »(«expr = »(find_aux a l, some b), «expr ∈ »(sigma.mk a b, l))
| «expr[ , ]»([]), nd := ⟨λ n, by injection [expr n] [], false.elim⟩
| «expr :: »(⟨a', b'⟩, t), nd := begin
  by_cases [expr «expr = »(a', a)],
  { clear [ident find_aux_iff],
    subst [expr h],
    suffices [] [":", expr «expr ↔ »(«expr = »(b', b), «expr ∨ »(«expr = »(b', b), «expr ∈ »(sigma.mk a' b, t)))],
    { simpa [] [] [] ["[", expr find_aux, ",", expr eq_comm, "]"] [] [] },
    refine [expr (or_iff_left_of_imp (λ m, _)).symm],
    have [] [":", expr «expr ∉ »(a', t.map sigma.fst)] [],
    from [expr list.not_mem_of_nodup_cons nd],
    exact [expr this.elim (list.mem_map_of_mem sigma.fst m)] },
  { have [] [":", expr «expr ≠ »(sigma.mk a b, ⟨a', b'⟩)] [],
    { intro [ident e],
      injection [expr e] ["with", ident e],
      exact [expr h e.symm] },
    simp [] [] [] [] [] ["at", ident nd],
    simp [] [] [] ["[", expr find_aux, ",", expr h, ",", expr ne.symm h, ",", expr find_aux_iff, ",", expr nd, "]"] [] [] }
end

/-- Returns `tt` if the bucket `l` contains the key `a` -/
def contains_aux (a : α) (l : List (Σa, β a)) : Bool :=
  (find_aux a l).isSome

theorem contains_aux_iff {a : α} {l : List (Σa, β a)} (nd : (l.map Sigma.fst).Nodup) :
  contains_aux a l ↔ a ∈ l.map Sigma.fst :=
  by 
    unfold contains_aux 
    cases' h : find_aux a l with b <;> simp 
    ·
      intro (b : β a)(m : Sigma.mk a b ∈ l)
      rw [(find_aux_iff nd).2 m] at h 
      contradiction
    ·
      show ∃ b : β a, Sigma.mk a b ∈ l 
      exact ⟨_, (find_aux_iff nd).1 h⟩

/-- Modify a bucket to replace a value in the list. Leaves the list
 unchanged if the key is not found. -/
def replace_aux (a : α) (b : β a) : List (Σa, β a) → List (Σa, β a)
| [] => []
| ⟨a', b'⟩ :: t => if a' = a then ⟨a, b⟩ :: t else ⟨a', b'⟩ :: replace_aux t

/-- Modify a bucket to remove a key, if it exists. -/
def erase_aux (a : α) : List (Σa, β a) → List (Σa, β a)
| [] => []
| ⟨a', b'⟩ :: t => if a' = a then t else ⟨a', b'⟩ :: erase_aux t

/-- The predicate `valid bkts sz` means that `bkts` satisfies the `hash_map`
  invariants: There are exactly `sz` elements in it, every pair is in the
  bucket determined by its key and the hash function, and no key appears
  multiple times in the list. -/
structure valid{n}(bkts : BucketArray α β n)(sz : Nat) : Prop where 
  len : bkts.as_list.length = sz 
  idx : ∀ {i} {a : Σa, β a}, a ∈ Arrayₓ.read bkts i → mk_idx n (hash_fn a.1) = i 
  Nodup : ∀ i, ((Arrayₓ.read bkts i).map Sigma.fst).Nodup

theorem valid.idx_enum {n} {bkts : BucketArray α β n} {sz : Nat} (v : valid bkts sz) {i l}
  (he : (i, l) ∈ bkts.to_list.enum) {a} {b : β a} (hl : Sigma.mk a b ∈ l) : ∃ h, mk_idx n (hash_fn a) = ⟨i, h⟩ :=
  (Arrayₓ.mem_to_list_enum.mp he).imp
    fun h e =>
      by 
        subst e <;> exact v.idx hl

theorem valid.idx_enum_1 {n} {bkts : BucketArray α β n} {sz : Nat} (v : valid bkts sz) {i l}
  (he : (i, l) ∈ bkts.to_list.enum) {a} {b : β a} (hl : Sigma.mk a b ∈ l) : (mk_idx n (hash_fn a)).1 = i :=
  let ⟨h, e⟩ := v.idx_enum _ he hl 
  by 
    rw [e] <;> rfl

-- error in Data.HashMap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem valid.as_list_nodup
{n}
{bkts : bucket_array α β n}
{sz : nat}
(v : valid bkts sz) : (bkts.as_list.map sigma.fst).nodup :=
begin
  suffices [] [":", expr (bkts.to_list.map (list.map sigma.fst)).pairwise list.disjoint],
  { suffices [] [":", expr ∀ l, array.mem l bkts → (l.map sigma.fst).nodup],
    by simpa [] [] [] ["[", expr bucket_array.as_list, ",", expr list.nodup_join, ",", "*", "]"] [] [],
    rintros [ident l, "⟨", ident i, ",", ident rfl, "⟩"],
    apply [expr v.nodup] },
  rw ["[", "<-", expr list.enum_map_snd bkts.to_list, ",", expr list.pairwise_map, ",", expr list.pairwise_map, "]"] [],
  have [] [":", expr (bkts.to_list.enum.map prod.fst).nodup] [":=", expr by simp [] [] [] ["[", expr list.nodup_range, "]"] [] []],
  refine [expr list.pairwise.imp_of_mem _ ((list.pairwise_map _).1 this)],
  rw [expr prod.forall] [],
  intros [ident i, ident l₁],
  rw [expr prod.forall] [],
  intros [ident j, ident l₂, ident me₁, ident me₂, ident ij],
  simp [] [] [] ["[", expr list.disjoint, "]"] [] [],
  intros [ident a, ident b, ident ml₁, ident b', ident ml₂],
  apply [expr ij],
  rwa ["[", "<-", expr v.idx_enum_1 _ me₁ ml₁, ",", "<-", expr v.idx_enum_1 _ me₂ ml₂, "]"] []
end

theorem mk_valid (n : ℕ+) : @valid n (mkArray n []) 0 :=
  ⟨by 
      simp [mk_as_list],
    fun i a h =>
      by 
        cases h,
    fun i => List.nodup_nil⟩

theorem valid.find_aux_iff {n} {bkts : BucketArray α β n} {sz : Nat} (v : valid bkts sz) {a : α} {b : β a} :
  find_aux a (bkts.read hash_fn a) = some b ↔ Sigma.mk a b ∈ bkts.as_list :=
  (find_aux_iff (v.nodup _)).trans$
    by 
      rw [bkts.mem_as_list] <;> exact ⟨fun h => ⟨_, h⟩, fun ⟨i, h⟩ => (v.idx h).symm ▸ h⟩

theorem valid.contains_aux_iff {n} {bkts : BucketArray α β n} {sz : Nat} (v : valid bkts sz) (a : α) :
  contains_aux a (bkts.read hash_fn a) ↔ a ∈ bkts.as_list.map Sigma.fst :=
  by 
    simp [contains_aux, Option.is_some_iff_exists, v.find_aux_iff hash_fn]

section 

parameter
  {n : ℕ+}{bkts : BucketArray α β n}{bidx : Finₓ n}{f : List (Σa, β a) → List (Σa, β a)}(u v1 v2 w : List (Σa, β a))

local notation "L" => Arrayₓ.read bkts bidx

private def bkts' : BucketArray α β n :=
  Arrayₓ.write bkts bidx (f L)

variable(hl : L = u ++ v1 ++ w)(hfl : f L = u ++ v2 ++ w)

include hl hfl

-- error in Data.HashMap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem append_of_modify : «expr∃ , »((u'
  w'), «expr ∧ »(«expr = »(bkts.as_list, «expr ++ »(«expr ++ »(u', v1), w')), «expr = »(bkts'.as_list, «expr ++ »(«expr ++ »(u', v2), w')))) :=
begin
  unfold [ident bucket_array.as_list] [],
  have [ident h] [":", expr «expr < »((bidx : exprℕ()), bkts.to_list.length)] [],
  { simp [] [] ["only"] ["[", expr bidx.is_lt, ",", expr array.to_list_length, "]"] [] [] },
  refine [expr ⟨«expr ++ »((bkts.to_list.take bidx).join, u), «expr ++ »(w, (bkts.to_list.drop «expr + »(bidx, 1)).join), _, _⟩],
  { conv [] [] { to_lhs,
      rw ["[", "<-", expr list.take_append_drop bidx bkts.to_list, ",", expr list.drop_eq_nth_le_cons h, "]"],
      simp [] ["[", expr hl, "]"] [] },
    simp [] [] [] [] [] [] },
  { conv [] [] { to_lhs,
      rw ["[", expr bkts', ",", expr array.write_to_list, ",", expr list.update_nth_eq_take_cons_drop _ h, "]"],
      simp [] ["[", expr hfl, "]"] [] },
    simp [] [] [] [] [] [] }
end

variable(hvnd :
    (v2.map
        Sigma.fst).Nodup)(hal :
    ∀ a : Σa, β a,
      a ∈ v2 →
        mk_idx n (hash_fn a.1) =
          bidx)(djuv :
    (u.map Sigma.fst).Disjoint (v2.map Sigma.fst))(djwv : (w.map Sigma.fst).Disjoint (v2.map Sigma.fst))

include hvnd hal djuv djwv

-- error in Data.HashMap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem valid.modify
{sz : exprℕ()}
(v : valid bkts sz) : «expr ∧ »(«expr ≤ »(v1.length, «expr + »(sz, v2.length)), valid bkts' «expr - »(«expr + »(sz, v2.length), v1.length)) :=
begin
  rcases [expr append_of_modify u v1 v2 w hl hfl, "with", "⟨", ident u', ",", ident w', ",", ident e₁, ",", ident e₂, "⟩"],
  rw ["[", "<-", expr v.len, ",", expr e₁, "]"] [],
  suffices [] [":", expr valid bkts' «expr ++ »(«expr ++ »(u', v2), w').length],
  { simpa [] [] [] ["[", expr ge, ",", expr add_comm, ",", expr add_left_comm, ",", expr nat.le_add_right, ",", expr add_tsub_cancel_left, "]"] [] [] },
  refine [expr ⟨congr_arg _ e₂, λ i a, _, λ i, _⟩],
  { by_cases [expr «expr = »(bidx, i)],
    { subst [expr i],
      rw ["[", expr bkts', ",", expr array.read_write, ",", expr hfl, "]"] [],
      have [] [] [":=", expr @valid.idx _ _ _ v bidx a],
      simp [] [] ["only"] ["[", expr hl, ",", expr list.mem_append, ",", expr or_imp_distrib, ",", expr forall_and_distrib, "]"] [] ["at", ident this, "⊢"],
      exact [expr ⟨⟨this.1.1, hal _⟩, this.2⟩] },
    { rw ["[", expr bkts', ",", expr array.read_write_of_ne _ _ h, "]"] [],
      apply [expr v.idx] } },
  { by_cases [expr «expr = »(bidx, i)],
    { subst [expr i],
      rw ["[", expr bkts', ",", expr array.read_write, ",", expr hfl, "]"] [],
      have [] [] [":=", expr @valid.nodup _ _ _ v bidx],
      simp [] [] [] ["[", expr hl, ",", expr list.nodup_append, "]"] [] ["at", ident this],
      simp [] [] [] ["[", expr list.nodup_append, ",", expr this, ",", expr hvnd, ",", expr djuv, ",", expr djwv.symm, "]"] [] [] },
    { rw ["[", expr bkts', ",", expr array.read_write_of_ne _ _ h, "]"] [],
      apply [expr v.nodup] } }
end

end 

-- error in Data.HashMap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem valid.replace_aux
(a : α)
(b : β a) : ∀
l : list «exprΣ , »((a), β a), «expr ∈ »(a, l.map sigma.fst) → «expr∃ , »((u w : list «exprΣ , »((a), β a))
 (b'), «expr ∧ »(«expr = »(l, «expr ++ »(«expr ++ »(u, «expr[ , ]»([⟨a, b'⟩])), w)), «expr = »(replace_aux a b l, «expr ++ »(«expr ++ »(u, «expr[ , ]»([⟨a, b⟩])), w))))
| «expr[ , ]»([]) := false.elim
| «expr :: »(⟨a', b'⟩, t) := begin
  by_cases [expr e, ":", expr «expr = »(a', a)],
  { subst [expr a'],
    suffices [] [":", expr «expr∃ , »((u w : list «exprΣ , »((a), β a))
      (b'' : β a), «expr ∧ »(«expr = »(«expr :: »(sigma.mk a b', t), «expr ++ »(u, «expr :: »(⟨a, b''⟩, w))), «expr = »(replace_aux a b «expr :: »(⟨a, b'⟩, t), «expr ++ »(u, «expr :: »(⟨a, b⟩, w)))))],
    { simpa [] [] [] [] [] [] },
    refine [expr ⟨«expr[ , ]»([]), t, b', _⟩],
    simp [] [] [] ["[", expr replace_aux, "]"] [] [] },
  { suffices [] [":", expr ∀
     (x : β a)
     (_ : «expr ∈ »(sigma.mk a x, t)), «expr∃ , »((u w)
      (b'' : β a), «expr ∧ »(«expr = »(«expr :: »(sigma.mk a' b', t), «expr ++ »(u, «expr :: »(⟨a, b''⟩, w))), «expr = »(«expr :: »(sigma.mk a' b', replace_aux a b t), «expr ++ »(u, «expr :: »(⟨a, b⟩, w)))))],
    { simpa [] [] [] ["[", expr replace_aux, ",", expr ne.symm e, ",", expr e, "]"] [] [] },
    intros [ident x, ident m],
    have [ident IH] [":", expr ∀
     (x : β a)
     (_ : «expr ∈ »(sigma.mk a x, t)), «expr∃ , »((u w)
      (b'' : β a), «expr ∧ »(«expr = »(t, «expr ++ »(u, «expr :: »(⟨a, b''⟩, w))), «expr = »(replace_aux a b t, «expr ++ »(u, «expr :: »(⟨a, b⟩, w)))))] [],
    { simpa [] [] [] [] [] ["using", expr valid.replace_aux t] },
    rcases [expr IH x m, "with", "⟨", ident u, ",", ident w, ",", ident b'', ",", ident hl, ",", ident hfl, "⟩"],
    exact [expr ⟨«expr :: »(⟨a', b'⟩, u), w, b'', by simp [] [] [] ["[", expr hl, ",", expr hfl.symm, ",", expr ne.symm e, "]"] [] []⟩] }
end

-- error in Data.HashMap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem valid.replace
{n : «exprℕ+»()}
{bkts : bucket_array α β n}
{sz : exprℕ()}
(a : α)
(b : β a)
(Hc : contains_aux a (bkts.read hash_fn a))
(v : valid bkts sz) : valid (bkts.modify hash_fn a (replace_aux a b)) sz :=
begin
  have [ident nd] [] [":=", expr v.nodup (mk_idx n (hash_fn a))],
  rcases [expr hash_map.valid.replace_aux a b (array.read bkts (mk_idx n (hash_fn a))) ((contains_aux_iff nd).1 Hc), "with", "⟨", ident u, ",", ident w, ",", ident b', ",", ident hl, ",", ident hfl, "⟩"],
  simp [] [] [] ["[", expr hl, ",", expr list.nodup_append, "]"] [] ["at", ident nd],
  refine [expr (v.modify hash_fn u «expr[ , ]»([⟨a, b'⟩]) «expr[ , ]»([⟨a, b⟩]) w hl hfl (list.nodup_singleton _) (λ
     a'
     e, by simp [] [] [] [] [] ["at", ident e]; rw [expr e] []) (λ
     a' e1 e2, _) (λ a' e1 e2, _)).2]; { revert [ident e1],
    simp [] [] [] ["[", "-", ident sigma.exists, "]"] [] ["at", ident e2],
    subst [expr a'],
    simp [] [] [] ["[", expr nd, "]"] [] [] }
end

-- error in Data.HashMap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem valid.insert
{n : «exprℕ+»()}
{bkts : bucket_array α β n}
{sz : exprℕ()}
(a : α)
(b : β a)
(Hnc : «expr¬ »(contains_aux a (bkts.read hash_fn a)))
(v : valid bkts sz) : valid (reinsert_aux bkts a b) «expr + »(sz, 1) :=
begin
  have [ident nd] [] [":=", expr v.nodup (mk_idx n (hash_fn a))],
  refine [expr (v.modify hash_fn «expr[ , ]»([]) «expr[ , ]»([]) «expr[ , ]»([⟨a, b⟩]) (bkts.read hash_fn a) rfl rfl (list.nodup_singleton _) (λ
     a' e, by simp [] [] [] [] [] ["at", ident e]; rw [expr e] []) (λ a', false.elim) (λ a' e1 e2, _)).2],
  simp [] [] [] ["[", "-", ident sigma.exists, "]"] [] ["at", ident e2],
  subst [expr a'],
  exact [expr Hnc ((contains_aux_iff nd).2 e1)]
end

-- error in Data.HashMap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem valid.erase_aux
(a : α) : ∀
l : list «exprΣ , »((a), β a), «expr ∈ »(a, l.map sigma.fst) → «expr∃ , »((u w : list «exprΣ , »((a), β a))
 (b), «expr ∧ »(«expr = »(l, «expr ++ »(«expr ++ »(u, «expr[ , ]»([⟨a, b⟩])), w)), «expr = »(erase_aux a l, «expr ++ »(«expr ++ »(u, «expr[ , ]»([])), w))))
| «expr[ , ]»([]) := false.elim
| «expr :: »(⟨a', b'⟩, t) := begin
  by_cases [expr e, ":", expr «expr = »(a', a)],
  { subst [expr a'],
    simpa [] [] [] ["[", expr erase_aux, ",", expr and_comm, "]"] [] ["using", expr show «expr∃ , »((u w)
      (x : β a), «expr ∧ »(«expr = »(t, «expr ++ »(u, w)), «expr = »(«expr :: »(sigma.mk a b', t), «expr ++ »(u, «expr :: »(⟨a, x⟩, w))))), from ⟨«expr[ , ]»([]), t, b', by simp [] [] [] [] [] []⟩] },
  { simp [] [] [] ["[", expr erase_aux, ",", expr e, ",", expr ne.symm e, "]"] [] [],
    suffices [] [":", expr ∀
     (b : β a)
     (_ : «expr ∈ »(sigma.mk a b, t)), «expr∃ , »((u w)
      (x : β a), «expr ∧ »(«expr = »(«expr :: »(sigma.mk a' b', t), «expr ++ »(u, «expr :: »(⟨a, x⟩, w))), «expr = »(«expr :: »(sigma.mk a' b', erase_aux a t), «expr ++ »(u, w))))],
    { simpa [] [] [] ["[", expr replace_aux, ",", expr ne.symm e, ",", expr e, "]"] [] [] },
    intros [ident b, ident m],
    have [ident IH] [":", expr ∀
     (x : β a)
     (_ : «expr ∈ »(sigma.mk a x, t)), «expr∃ , »((u w)
      (x : β a), «expr ∧ »(«expr = »(t, «expr ++ »(u, «expr :: »(⟨a, x⟩, w))), «expr = »(erase_aux a t, «expr ++ »(u, w))))] [],
    { simpa [] [] [] [] [] ["using", expr valid.erase_aux t] },
    rcases [expr IH b m, "with", "⟨", ident u, ",", ident w, ",", ident b'', ",", ident hl, ",", ident hfl, "⟩"],
    exact [expr ⟨«expr :: »(⟨a', b'⟩, u), w, b'', by simp [] [] [] ["[", expr hl, ",", expr hfl.symm, "]"] [] []⟩] }
end

-- error in Data.HashMap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem valid.erase
{n}
{bkts : bucket_array α β n}
{sz}
(a : α)
(Hc : contains_aux a (bkts.read hash_fn a))
(v : valid bkts sz) : valid (bkts.modify hash_fn a (erase_aux a)) «expr - »(sz, 1) :=
begin
  have [ident nd] [] [":=", expr v.nodup (mk_idx n (hash_fn a))],
  rcases [expr hash_map.valid.erase_aux a (array.read bkts (mk_idx n (hash_fn a))) ((contains_aux_iff nd).1 Hc), "with", "⟨", ident u, ",", ident w, ",", ident b, ",", ident hl, ",", ident hfl, "⟩"],
  refine [expr (v.modify hash_fn u «expr[ , ]»([⟨a, b⟩]) «expr[ , ]»([]) w hl hfl list.nodup_nil _ _ _).2]; simp [] [] [] [] [] []
end

end 

end HashMap

/-- A hash map data structure, representing a finite key-value map
  with key type `α` and value type `β` (which may depend on `α`). -/
structure HashMap(α : Type u)[DecidableEq α](β : α → Type v) where 
  hashFn : α → Nat 
  size : ℕ 
  nbuckets : ℕ+
  buckets : BucketArray α β nbuckets 
  is_valid : HashMap.Valid hash_fn buckets size

/-- Construct an empty hash map with buffer size `nbuckets` (default 8). -/
def mkHashMap {α : Type u} [DecidableEq α] {β : α → Type v} (hash_fn : α → Nat) (nbuckets := 8) : HashMap α β :=
  let n := if nbuckets = 0 then 8 else nbuckets 
  let nz : n > 0 :=
    by 
      abstract 
        cases nbuckets <;> simp [if_pos, Nat.succ_ne_zero]
  { hashFn, size := 0, nbuckets := ⟨n, nz⟩, buckets := mkArray n [], is_valid := HashMap.mk_valid _ _ }

namespace HashMap

variable{α : Type u}{β : α → Type v}[DecidableEq α]

/-- Return the value corresponding to a key, or `none` if not found -/
def find (m : HashMap α β) (a : α) : Option (β a) :=
  find_aux a (m.buckets.read m.hash_fn a)

/-- Return `tt` if the key exists in the map -/
def contains (m : HashMap α β) (a : α) : Bool :=
  (m.find a).isSome

instance  : HasMem α (HashMap α β) :=
  ⟨fun a m => m.contains a⟩

/-- Fold a function over the key-value pairs in the map -/
def fold {δ : Type w} (m : HashMap α β) (d : δ) (f : δ → ∀ a, β a → δ) : δ :=
  m.buckets.foldl d f

/-- The list of key-value pairs in the map -/
def entries (m : HashMap α β) : List (Σa, β a) :=
  m.buckets.as_list

/-- The list of keys in the map -/
def keys (m : HashMap α β) : List α :=
  m.entries.map Sigma.fst

theorem find_iff (m : HashMap α β) (a : α) (b : β a) : m.find a = some b ↔ Sigma.mk a b ∈ m.entries :=
  m.is_valid.find_aux_iff _

theorem contains_iff (m : HashMap α β) (a : α) : m.contains a ↔ a ∈ m.keys :=
  m.is_valid.contains_aux_iff _ _

theorem entries_empty (hash_fn : α → Nat) n : (@mkHashMap α _ β hash_fn n).entries = [] :=
  mk_as_list _

theorem keys_empty (hash_fn : α → Nat) n : (@mkHashMap α _ β hash_fn n).keys = [] :=
  by 
    dsimp [keys] <;> rw [entries_empty] <;> rfl

-- error in Data.HashMap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_empty (hash_fn : α → nat) (n a) : «expr = »((@mk_hash_map α _ β hash_fn n).find a, none) :=
by induction [expr h, ":", expr (@mk_hash_map α _ β hash_fn n).find a] [] [] []; [refl, { have [] [] [":=", expr (find_iff _ _ _).1 h],
   rw [expr entries_empty] ["at", ident this],
   contradiction }]

theorem not_contains_empty (hash_fn : α → Nat) n a : ¬(@mkHashMap α _ β hash_fn n).contains a :=
  by 
    apply bool_iff_false.2 <;> dsimp [contains] <;> rw [find_empty] <;> rfl

-- error in Data.HashMap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem insert_lemma
(hash_fn : α → nat)
{n n'}
{bkts : bucket_array α β n}
{sz}
(v : valid hash_fn bkts sz) : valid hash_fn (bkts.foldl (mk_array _ «expr[ , ]»([]) : bucket_array α β n') (reinsert_aux hash_fn)) sz :=
begin
  suffices [] [":", expr ∀
   (l : list «exprΣ , »((a), β a))
   (t : bucket_array α β n')
   (sz), valid hash_fn t sz → («expr ++ »(l, t.as_list).map sigma.fst).nodup → valid hash_fn (l.foldl (λ
     (r)
     (a : «exprΣ , »((a), β a)), reinsert_aux hash_fn r a.1 a.2) t) «expr + »(sz, l.length)],
  { have [ident p] [] [":=", expr this bkts.as_list _ _ (mk_valid _ _)],
    rw ["[", expr mk_as_list, ",", expr list.append_nil, ",", expr zero_add, ",", expr v.len, "]"] ["at", ident p],
    rw [expr bucket_array.foldl_eq] [],
    exact [expr p (v.as_list_nodup _)] },
  intro [ident l],
  induction [expr l] [] ["with", ident c, ident l, ident IH] []; intros [ident t, ident sz, ident v, ident nd],
  { exact [expr v] },
  rw [expr show «expr = »(«expr + »(sz, «expr :: »(c, l).length), «expr + »(«expr + »(sz, 1), l.length)), by simp [] [] [] ["[", expr add_comm, ",", expr add_assoc, "]"] [] []] [],
  rcases [expr show «expr ∧ »((l.map sigma.fst).nodup, «expr ∧ »(((bucket_array.as_list t).map sigma.fst).nodup, «expr ∧ »(«expr ∉ »(c.fst, l.map sigma.fst), «expr ∧ »(«expr ∉ »(c.fst, (bucket_array.as_list t).map sigma.fst), (l.map sigma.fst).disjoint ((bucket_array.as_list t).map sigma.fst))))), by simpa [] [] [] ["[", expr list.nodup_append, ",", expr not_or_distrib, ",", expr and_comm, ",", expr and.left_comm, "]"] [] ["using", expr nd], "with", "⟨", ident nd1, ",", ident nd2, ",", ident nm1, ",", ident nm2, ",", ident dj, "⟩"],
  have [ident v'] [] [":=", expr v.insert _ _ c.2 (λ Hc, «expr $ »(nm2, (v.contains_aux_iff _ c.1).1 Hc))],
  apply [expr IH _ _ v'],
  suffices [] [":", expr ∀
   {{a : α}}
   (b : β a), «expr ∈ »(sigma.mk a b, l) → ∀
   b' : β a, «expr ∈ »(sigma.mk a b', (reinsert_aux hash_fn t c.1 c.2).as_list) → false],
  { simpa [] [] [] ["[", expr list.nodup_append, ",", expr nd1, ",", expr v'.as_list_nodup _, ",", expr list.disjoint, "]"] [] [] },
  intros [ident a, ident b, ident m1, ident b', ident m2],
  rcases [expr (reinsert_aux hash_fn t c.1 c.2).mem_as_list.1 m2, "with", "⟨", ident i, ",", ident im, "⟩"],
  have [] [":", expr «expr ∉ »(sigma.mk a b', array.read t i)] [],
  { intro [ident m3],
    have [] [":", expr «expr ∈ »(a, list.map sigma.fst t.as_list)] [":=", expr list.mem_map_of_mem sigma.fst (t.mem_as_list.2 ⟨_, m3⟩)],
    exact [expr dj (list.mem_map_of_mem sigma.fst m1) this] },
  by_cases [expr h, ":", expr «expr = »(mk_idx n' (hash_fn c.1), i)],
  { subst [expr h],
    have [ident e] [":", expr «expr = »(sigma.mk a b', ⟨c.1, c.2⟩)] [],
    { simpa [] [] [] ["[", expr reinsert_aux, ",", expr bucket_array.modify, ",", expr array.read_write, ",", expr this, "]"] [] ["using", expr im] },
    injection [expr e] ["with", ident e],
    subst [expr a],
    exact [expr nm1.elim (@list.mem_map_of_mem _ _ sigma.fst _ _ m1)] },
  { apply [expr this],
    simpa [] [] [] ["[", expr reinsert_aux, ",", expr bucket_array.modify, ",", expr array.read_write_of_ne _ _ h, "]"] [] ["using", expr im] }
end

/-- Insert a key-value pair into the map. (Modifies `m` in-place when applicable) -/
def insert : ∀ m : HashMap α β a : α b : β a, HashMap α β
| ⟨hash_fn, size, n, buckets, v⟩, a, b =>
  let bkt := buckets.read hash_fn a 
  if hc : contains_aux a bkt then
    { hashFn, size, nbuckets := n, buckets := buckets.modify hash_fn a (replace_aux a b),
      is_valid := v.replace _ a b hc }
  else
    let size' := size+1
    let buckets' := buckets.modify hash_fn a fun l => ⟨a, b⟩ :: l 
    let valid' := v.insert _ a b hc 
    if size' ≤ n then { hashFn, size := size', nbuckets := n, buckets := buckets', is_valid := valid' } else
      let n' : ℕ+ :=
        ⟨n*2,
          mul_pos n.2
            (by 
              decide)⟩
      let buckets'' : BucketArray α β n' := buckets'.foldl (mkArray _ []) (reinsert_aux hash_fn)
      { hashFn, size := size', nbuckets := n', buckets := buckets'', is_valid := insert_lemma _ valid' }

-- error in Data.HashMap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_insert : ∀
(m : hash_map α β)
(a
 b
 a'
 b'), «expr ↔ »(«expr ∈ »((sigma.mk a' b' : sigma β), (m.insert a b).entries), if «expr = »(a, a') then «expr == »(b, b') else «expr ∈ »(sigma.mk a' b', m.entries))
| ⟨hash_fn, size, n, bkts, v⟩, a, b, a', b' := begin
  let [ident bkt] [] [":=", expr bkts.read hash_fn a],
  have [ident nd] [":", expr (bkt.map sigma.fst).nodup] [":=", expr v.nodup (mk_idx n (hash_fn a))],
  have [ident lem] [":", expr ∀
   (bkts' : bucket_array α β n)
   (v1 u w)
   (hl : «expr = »(bucket_array.as_list bkts, «expr ++ »(«expr ++ »(u, v1), w)))
   (hfl : «expr = »(bucket_array.as_list bkts', «expr ++ »(«expr ++ »(u, «expr[ , ]»([⟨a, b⟩])), w)))
   (veq : «expr ∨ »(«expr ∧ »(«expr = »(v1, «expr[ , ]»([])), «expr¬ »(contains_aux a bkt)), «expr∃ , »((b''), «expr = »(v1, «expr[ , ]»([⟨a, b''⟩]))))), «expr ↔ »(«expr ∈ »(sigma.mk a' b', bkts'.as_list), if «expr = »(a, a') then «expr == »(b, b') else «expr ∈ »(sigma.mk a' b', bkts.as_list))] [],
  { intros [ident bkts', ident v1, ident u, ident w, ident hl, ident hfl, ident veq],
    rw ["[", expr hl, ",", expr hfl, "]"] [],
    by_cases [expr h, ":", expr «expr = »(a, a')],
    { subst [expr a'],
      suffices [] [":", expr «expr ↔ »(«expr ∨ »(«expr = »(b, b'), «expr ∨ »(«expr ∈ »(sigma.mk a b', u), «expr ∈ »(sigma.mk a b', w))), «expr = »(b, b'))],
      { simpa [] [] [] ["[", expr eq_comm, ",", expr or.left_comm, "]"] [] [] },
      refine [expr or_iff_left_of_imp «expr $ »(not.elim, not_or_distrib.2 _)],
      rcases [expr veq, "with", "⟨", ident rfl, ",", ident Hnc, "⟩", "|", "⟨", ident b'', ",", ident rfl, "⟩"],
      { have [ident na] [] [":=", expr «expr $ »(not_iff_not_of_iff, v.contains_aux_iff _ _).1 Hnc],
        simp [] [] [] ["[", expr hl, ",", expr not_or_distrib, "]"] [] ["at", ident na],
        simp [] [] [] ["[", expr na, "]"] [] [] },
      { have [ident nd'] [] [":=", expr v.as_list_nodup _],
        simp [] [] [] ["[", expr hl, ",", expr list.nodup_append, "]"] [] ["at", ident nd'],
        simp [] [] [] ["[", expr nd', "]"] [] [] } },
    { suffices [] [":", expr «expr ∉ »(sigma.mk a' b', v1)],
      { simp [] [] [] ["[", expr h, ",", expr ne.symm h, ",", expr this, "]"] [] [] },
      rcases [expr veq, "with", "⟨", ident rfl, ",", ident Hnc, "⟩", "|", "⟨", ident b'', ",", ident rfl, "⟩"]; simp [] [] [] ["[", expr ne.symm h, "]"] [] [] } },
  by_cases [expr Hc, ":", expr (contains_aux a bkt : exprProp())],
  { rcases [expr hash_map.valid.replace_aux a b (array.read bkts (mk_idx n (hash_fn a))) ((contains_aux_iff nd).1 Hc), "with", "⟨", ident u', ",", ident w', ",", ident b'', ",", ident hl', ",", ident hfl', "⟩"],
    rcases [expr append_of_modify u' «expr[ , ]»([⟨a, b''⟩]) «expr[ , ]»([⟨a, b⟩]) w' hl' hfl', "with", "⟨", ident u, ",", ident w, ",", ident hl, ",", ident hfl, "⟩"],
    simpa [] [] [] ["[", expr insert, ",", expr @dif_pos (contains_aux a bkt) _ Hc, "]"] [] ["using", expr lem _ _ u w hl hfl (or.inr ⟨b'', rfl⟩)] },
  { let [ident size'] [] [":=", expr «expr + »(size, 1)],
    let [ident bkts'] [] [":=", expr bkts.modify hash_fn a (λ l, «expr :: »(⟨a, b⟩, l))],
    have [ident mi] [":", expr «expr ↔ »(«expr ∈ »(sigma.mk a' b', bkts'.as_list), if «expr = »(a, a') then «expr == »(b, b') else «expr ∈ »(sigma.mk a' b', bkts.as_list))] [":=", expr let ⟨u, w, hl, hfl⟩ := append_of_modify «expr[ , ]»([]) «expr[ , ]»([]) «expr[ , ]»([⟨a, b⟩]) _ rfl rfl in
     «expr $ »(lem bkts' _ u w hl hfl, or.inl ⟨rfl, Hc⟩)],
    simp [] [] [] ["[", expr insert, ",", expr @dif_neg (contains_aux a bkt) _ Hc, "]"] [] [],
    by_cases [expr h, ":", expr «expr ≤ »(size', n)],
    { simpa [] [] [] ["[", expr show «expr ≤ »(size', n), from h, "]"] [] ["using", expr mi] },
    { let [ident n'] [":", expr «exprℕ+»()] [":=", expr ⟨«expr * »(n, 2), mul_pos n.2 exprdec_trivial()⟩],
      let [ident bkts''] [":", expr bucket_array α β n'] [":=", expr bkts'.foldl (mk_array _ «expr[ , ]»([])) (reinsert_aux hash_fn)],
      suffices [] [":", expr «expr ↔ »(«expr ∈ »(sigma.mk a' b', bkts''.as_list), «expr ∈ »(sigma.mk a' b', bkts'.as_list.reverse))],
      { simpa [] [] [] ["[", expr show «expr¬ »(«expr ≤ »(size', n)), from h, ",", expr mi, "]"] [] [] },
      rw ["[", expr show «expr = »(bkts'', bkts'.as_list.foldl _ _), from bkts'.foldl_eq _ _, ",", "<-", expr list.foldr_reverse, "]"] [],
      induction [expr bkts'.as_list.reverse] [] ["with", ident a, ident l, ident IH] [],
      { simp [] [] [] ["[", expr mk_as_list, "]"] [] [] },
      { cases [expr a] ["with", ident a'', ident b''],
        let [ident B] [] [":=", expr l.foldr (λ
          (y : sigma β)
          (x : bucket_array α β n'), reinsert_aux hash_fn x y.1 y.2) (mk_array n' «expr[ , ]»([]))],
        rcases [expr append_of_modify «expr[ , ]»([]) «expr[ , ]»([]) «expr[ , ]»([⟨a'', b''⟩]) _ rfl rfl, "with", "⟨", ident u, ",", ident w, ",", ident hl, ",", ident hfl, "⟩"],
        simp [] [] [] ["[", expr IH.symm, ",", expr or.left_comm, ",", expr show «expr = »(B.as_list, _), from hl, ",", expr show «expr = »((reinsert_aux hash_fn B a'' b'').as_list, _), from hfl, "]"] [] [] } } }
end

theorem find_insert_eq (m : HashMap α β) (a : α) (b : β a) : (m.insert a b).find a = some b :=
  (find_iff (m.insert a b) a b).2$
    (mem_insert m a b a b).2$
      by 
        rw [if_pos rfl]

theorem find_insert_ne (m : HashMap α β) (a a' : α) (b : β a) (h : a ≠ a') : (m.insert a b).find a' = m.find a' :=
  Option.eq_of_eq_some$
    fun b' =>
      let t := mem_insert m a b a' b'
      (find_iff _ _ _).trans$
        Iff.trans
          (by 
            rwa [if_neg h] at t)
          (find_iff _ _ _).symm

theorem find_insert (m : HashMap α β) (a' a : α) (b : β a) :
  (m.insert a b).find a' = if h : a = a' then some (Eq.recOnₓ h b) else m.find a' :=
  if h : a = a' then
    by 
      rw [dif_pos h] <;>
        exact
          match a', h with 
          | _, rfl => find_insert_eq m a b
  else
    by 
      rw [dif_neg h] <;> exact find_insert_ne m a a' b h

/-- Insert a list of key-value pairs into the map. (Modifies `m` in-place when applicable) -/
def insert_all (l : List (Σa, β a)) (m : HashMap α β) : HashMap α β :=
  l.foldl (fun m ⟨a, b⟩ => insert m a b) m

/-- Construct a hash map from a list of key-value pairs. -/
def of_list (l : List (Σa, β a)) hash_fn : HashMap α β :=
  insert_all l (mkHashMap hash_fn (2*l.length))

/-- Remove a key from the map. (Modifies `m` in-place when applicable) -/
def erase (m : HashMap α β) (a : α) : HashMap α β :=
  match m with 
  | ⟨hash_fn, size, n, buckets, v⟩ =>
    if hc : contains_aux a (buckets.read hash_fn a) then
      { hashFn, size := size - 1, nbuckets := n, buckets := buckets.modify hash_fn a (erase_aux a),
        is_valid := v.erase _ a hc }
    else m

-- error in Data.HashMap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_erase : ∀
(m : hash_map α β)
(a
 a'
 b'), «expr ↔ »(«expr ∈ »((sigma.mk a' b' : sigma β), (m.erase a).entries), «expr ∧ »(«expr ≠ »(a, a'), «expr ∈ »(sigma.mk a' b', m.entries)))
| ⟨hash_fn, size, n, bkts, v⟩, a, a', b' := begin
  let [ident bkt] [] [":=", expr bkts.read hash_fn a],
  by_cases [expr Hc, ":", expr (contains_aux a bkt : exprProp())],
  { let [ident bkts'] [] [":=", expr bkts.modify hash_fn a (erase_aux a)],
    suffices [] [":", expr «expr ↔ »(«expr ∈ »(sigma.mk a' b', bkts'.as_list), «expr ∧ »(«expr ≠ »(a, a'), «expr ∈ »(sigma.mk a' b', bkts.as_list)))],
    { simpa [] [] [] ["[", expr erase, ",", expr @dif_pos (contains_aux a bkt) _ Hc, "]"] [] [] },
    have [ident nd] [] [":=", expr v.nodup (mk_idx n (hash_fn a))],
    rcases [expr valid.erase_aux a bkt ((contains_aux_iff nd).1 Hc), "with", "⟨", ident u', ",", ident w', ",", ident b, ",", ident hl', ",", ident hfl', "⟩"],
    rcases [expr append_of_modify u' «expr[ , ]»([⟨a, b⟩]) «expr[ , ]»([]) _ hl' hfl', "with", "⟨", ident u, ",", ident w, ",", ident hl, ",", ident hfl, "⟩"],
    suffices [] [":", expr ∀
     _ : «expr ∨ »(«expr ∈ »(sigma.mk a' b', u), «expr ∈ »(sigma.mk a' b', w)), «expr ≠ »(a, a')],
    { have [] [":", expr «expr ↔ »(«expr ∨ »(«expr ∈ »(sigma.mk a' b', u), «expr ∈ »(sigma.mk a' b', w)), «expr ∨ »(«expr ∧ »(«expr ∧ »(«expr¬ »(«expr = »(a, a')), «expr = »(a', a)), «expr == »(b', b)), «expr ∧ »(«expr¬ »(«expr = »(a, a')), «expr ∨ »(«expr ∈ »(sigma.mk a' b', u), «expr ∈ »(sigma.mk a' b', w)))))] [],
      { simp [] [] [] ["[", expr eq_comm, ",", expr not_and_self_iff, ",", expr and_iff_right_of_imp this, "]"] [] [] },
      simpa [] [] [] ["[", expr hl, ",", expr show «expr = »(bkts'.as_list, _), from hfl, ",", expr and_or_distrib_left, ",", expr and_comm, ",", expr and.left_comm, ",", expr or.left_comm, "]"] [] [] },
    intros [ident m, ident e],
    subst [expr a'],
    revert [ident m],
    apply [expr not_or_distrib.2],
    have [ident nd'] [] [":=", expr v.as_list_nodup _],
    simp [] [] [] ["[", expr hl, ",", expr list.nodup_append, "]"] [] ["at", ident nd'],
    simp [] [] [] ["[", expr nd', "]"] [] [] },
  { suffices [] [":", expr ∀ _ : «expr ∈ »(sigma.mk a' b', bucket_array.as_list bkts), «expr ≠ »(a, a')],
    { simp [] [] [] ["[", expr erase, ",", expr @dif_neg (contains_aux a bkt) _ Hc, ",", expr entries, ",", expr and_iff_right_of_imp this, "]"] [] [] },
    intros [ident m, ident e],
    subst [expr a'],
    exact [expr Hc ((v.contains_aux_iff _ _).2 (list.mem_map_of_mem sigma.fst m))] }
end

theorem find_erase_eq (m : HashMap α β) (a : α) : (m.erase a).find a = none :=
  by 
    cases' h : (m.erase a).find a with b
    ·
      rfl 
    exact absurd rfl ((mem_erase m a a b).1 ((find_iff (m.erase a) a b).1 h)).left

theorem find_erase_ne (m : HashMap α β) (a a' : α) (h : a ≠ a') : (m.erase a).find a' = m.find a' :=
  Option.eq_of_eq_some$
    fun b' => (find_iff _ _ _).trans$ (mem_erase m a a' b').trans$ (and_iff_right h).trans (find_iff _ _ _).symm

theorem find_erase (m : HashMap α β) (a' a : α) : (m.erase a).find a' = if a = a' then none else m.find a' :=
  if h : a = a' then
    by 
      subst a' <;> simp [find_erase_eq m a]
  else
    by 
      rw [if_neg h] <;> exact find_erase_ne m a a' h

section Stringₓ

variable[HasToString α][∀ a, HasToString (β a)]

open Prod

private def key_data_to_string (a : α) (b : β a) (first : Bool) : Stringₓ :=
  (if first then "" else ", ") ++ s! "{a } ← {b}"

private def toString (m : HashMap α β) : Stringₓ :=
  "⟨" ++ fst (fold m ("", tt) fun p a b => (fst p ++ key_data_to_string a b (snd p), ff)) ++ "⟩"

instance  : HasToString (HashMap α β) :=
  ⟨toString⟩

end Stringₓ

section Format

open Format Prod

variable[has_to_format α][∀ a, has_to_format (β a)]

private unsafe def format_key_data (a : α) (b : β a) (first : Bool) : format :=
  (if first then to_fmt "" else to_fmt "," ++ line) ++ to_fmt a ++ space ++ to_fmt "←" ++ space ++ to_fmt b

private unsafe def to_format (m : HashMap α β) : format :=
  Groupₓ$
    to_fmt "⟨" ++ nest 1 (fst (fold m (to_fmt "", tt) fun p a b => (fst p ++ format_key_data a b (snd p), ff))) ++
      to_fmt "⟩"

unsafe instance  : has_to_format (HashMap α β) :=
  ⟨to_format⟩

end Format

/-- `hash_map` with key type `nat` and value type that may vary. -/
instance  {β : ℕ → Type _} : Inhabited (HashMap ℕ β) :=
  ⟨mkHashMap id⟩

end HashMap

