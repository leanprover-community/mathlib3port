import Leanbin.Data.Buffer 
import Mathbin.Data.Array.Lemmas 
import Mathbin.Control.Traversable.Instances

namespace Buffer

open Function

variable{α : Type _}{xs : List α}

instance  : Inhabited (Buffer α) :=
  ⟨nil⟩

-- error in Data.Buffer.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[ext #[]] theorem ext : ∀ {b₁ b₂ : buffer α}, «expr = »(to_list b₁, to_list b₂) → «expr = »(b₁, b₂)
| ⟨n₁, a₁⟩, ⟨n₂, a₂⟩, h := begin
  simp [] [] [] ["[", expr to_list, ",", expr to_array, "]"] [] ["at", ident h],
  have [ident e] [":", expr «expr = »(n₁, n₂)] [":=", expr by rw ["[", "<-", expr array.to_list_length a₁, ",", "<-", expr array.to_list_length a₂, ",", expr h, "]"] []],
  subst [expr e],
  have [ident h] [":", expr «expr == »(a₁, a₂.to_list.to_array)] [":=", expr «expr ▸ »(h, a₁.to_list_to_array.symm)],
  rw [expr eq_of_heq (h.trans a₂.to_list_to_array)] []
end

theorem ext_iff {b₁ b₂ : Buffer α} : b₁ = b₂ ↔ to_list b₁ = to_list b₂ :=
  ⟨fun h => h ▸ rfl, ext⟩

theorem size_eq_zero_iff {b : Buffer α} : b.size = 0 ↔ b = nil :=
  by 
    rcases b with ⟨_ | n, ⟨a⟩⟩
    ·
      simp only [size, nil, mkBuffer, true_andₓ, true_iffₓ, eq_self_iff_true, heq_iff_eq, Sigma.mk.inj_iff]
      ext i 
      exact Finₓ.elim0 i
    ·
      simp [size, nil, mkBuffer, Nat.succ_ne_zero]

@[simp]
theorem size_nil : (@nil α).size = 0 :=
  by 
    rw [size_eq_zero_iff]

@[simp]
theorem to_list_nil : to_list (@nil α) = [] :=
  rfl

instance  α [DecidableEq α] : DecidableEq (Buffer α) :=
  by 
    runTac 
      tactic.mk_dec_eq_instance

@[simp]
theorem to_list_append_list {b : Buffer α} : to_list (append_list b xs) = to_list b ++ xs :=
  by 
    induction xs generalizing b <;> simp  <;> cases b <;> simp [to_list, to_array]

@[simp]
theorem append_list_mk_buffer : append_list mkBuffer xs = Arrayₓ.toBuffer (List.toArrayₓ xs) :=
  by 
    ext x : 1 <;>
      simp [Arrayₓ.toBuffer, to_list, to_list_append_list] <;> induction xs <;> [rfl, skip] <;> simp [to_array] <;> rfl

@[simp]
theorem to_buffer_to_list (b : Buffer α) : b.to_list.to_buffer = b :=
  by 
    cases b 
    rw [to_list, to_array, List.toBuffer, append_list_mk_buffer]
    congr
    ·
      simpa
    ·
      apply Arrayₓ.to_list_to_array

@[simp]
theorem to_list_to_buffer (l : List α) : l.to_buffer.to_list = l :=
  by 
    cases l
    ·
      rfl
    ·
      rw [List.toBuffer, to_list_append_list]
      rfl

@[simp]
theorem to_list_to_array (b : Buffer α) : b.to_array.to_list = b.to_list :=
  by 
    cases b 
    simp [to_list]

@[simp]
theorem append_list_nil (b : Buffer α) : b.append_list [] = b :=
  rfl

theorem to_buffer_cons (c : α) (l : List α) : (c :: l).toBuffer = [c].toBuffer.appendList l :=
  by 
    induction' l with hd tl hl
    ·
      simp 
    ·
      apply ext 
      simp [hl]

@[simp]
theorem size_push_back (b : Buffer α) (a : α) : (b.push_back a).size = b.size+1 :=
  by 
    cases b 
    simp [size, push_back]

@[simp]
theorem size_append_list (b : Buffer α) (l : List α) : (b.append_list l).size = b.size+l.length :=
  by 
    induction' l with hd tl hl generalizing b
    ·
      simp 
    ·
      simp [append_list, hl, add_commₓ, add_assocₓ]

-- error in Data.Buffer.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem size_to_buffer (l : list α) : «expr = »(l.to_buffer.size, l.length) :=
begin
  induction [expr l] [] ["with", ident hd, ident tl, ident hl] [],
  { simpa [] [] [] [] [] [] },
  { rw ["[", expr to_buffer_cons, "]"] [],
    have [] [":", expr «expr = »(«expr[ , ]»([hd]).to_buffer.size, 1)] [":=", expr rfl],
    simp [] [] [] ["[", expr add_comm, ",", expr this, "]"] [] [] }
end

@[simp]
theorem length_to_list (b : Buffer α) : b.to_list.length = b.size :=
  by 
    rw [←to_buffer_to_list b, to_list_to_buffer, size_to_buffer]

theorem size_singleton (a : α) : [a].toBuffer.size = 1 :=
  rfl

theorem read_push_back_left (b : Buffer α) (a : α) {i : ℕ} (h : i < b.size) :
  (b.push_back a).read
      ⟨i,
        by 
          convert Nat.lt_succ_of_ltₓ h 
          simp ⟩ =
    b.read ⟨i, h⟩ :=
  by 
    cases b 
    convert Arrayₓ.read_push_back_left _ 
    simp 

@[simp]
theorem read_push_back_right (b : Buffer α) (a : α) :
  (b.push_back a).read
      ⟨b.size,
        by 
          simp ⟩ =
    a :=
  by 
    cases b 
    convert Arrayₓ.read_push_back_right

-- error in Data.Buffer.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem read_append_list_left'
(b : buffer α)
(l : list α)
{i : exprℕ()}
(h : «expr < »(i, (b.append_list l).size))
(h' : «expr < »(i, b.size)) : «expr = »((b.append_list l).read ⟨i, h⟩, b.read ⟨i, h'⟩) :=
begin
  induction [expr l] [] ["with", ident hd, ident tl, ident hl] ["generalizing", ident b],
  { refl },
  { have [ident hb] [":", expr «expr < »(i, ((b.push_back hd).append_list tl).size)] [":=", expr by convert [] [expr h] ["using", 1]],
    have [ident hb'] [":", expr «expr < »(i, (b.push_back hd).size)] [":=", expr by { convert [] [expr nat.lt_succ_of_lt h'] [],
       simp [] [] [] [] [] [] }],
    have [] [":", expr «expr = »((append_list b «expr :: »(hd, tl)).read ⟨i, h⟩, read ((push_back b hd).append_list tl) ⟨i, hb⟩)] [":=", expr rfl],
    simp [] [] [] ["[", expr this, ",", expr hl _ hb hb', ",", expr read_push_back_left _ _ h', "]"] [] [] }
end

theorem read_append_list_left (b : Buffer α) (l : List α) {i : ℕ} (h : i < b.size) :
  (b.append_list l).read
      ⟨i,
        by 
          simpa using Nat.lt_add_rightₓ _ _ _ h⟩ =
    b.read ⟨i, h⟩ :=
  read_append_list_left' b l _ h

-- error in Data.Buffer.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem read_append_list_right
(b : buffer α)
(l : list α)
{i : exprℕ()}
(h : «expr < »(i, l.length)) : «expr = »((b.append_list l).read ⟨«expr + »(b.size, i), by simp [] [] [] ["[", expr h, "]"] [] []⟩, l.nth_le i h) :=
begin
  induction [expr l] [] ["with", ident hd, ident tl, ident hl] ["generalizing", ident b, ident i],
  { exact [expr absurd i.zero_le (not_le_of_lt h)] },
  { convert_to [expr «expr = »(((b.push_back hd).append_list tl).read _, _)] [],
    cases [expr i] [],
    { convert [] [expr read_append_list_left _ _ _] []; simp [] [] [] [] [] [] },
    { rw ["[", expr list.length, ",", expr nat.succ_lt_succ_iff, "]"] ["at", ident h],
      have [] [":", expr «expr = »(«expr + »(b.size, i.succ), «expr + »((b.push_back hd).size, i))] [],
      { simp [] [] [] ["[", expr add_comm, ",", expr add_left_comm, ",", expr nat.succ_eq_add_one, "]"] [] [] },
      convert [] [expr hl (b.push_back hd) h] ["using", 1],
      simpa [] [] [] ["[", expr nat.add_succ, ",", expr nat.succ_add, "]"] [] [] } }
end

-- error in Data.Buffer.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem read_to_buffer'
(l : list α)
{i : exprℕ()}
(h : «expr < »(i, l.to_buffer.size))
(h' : «expr < »(i, l.length)) : «expr = »(l.to_buffer.read ⟨i, h⟩, l.nth_le i h') :=
begin
  cases [expr l] ["with", ident hd, ident tl],
  { simpa [] [] [] [] [] ["using", expr h'] },
  { have [ident hi] [":", expr «expr < »(i, («expr[ , ]»([hd]).to_buffer.append_list tl).size)] [":=", expr by simpa [] [] [] ["[", expr add_comm, "]"] [] ["using", expr h]],
    convert_to [expr «expr = »((«expr[ , ]»([hd]).to_buffer.append_list tl).read ⟨i, hi⟩, _)] [],
    cases [expr i] [],
    { convert [] [expr read_append_list_left _ _ _] [],
      simp [] [] [] [] [] [] },
    { rw [expr list.nth_le] [],
      convert [] [expr read_append_list_right _ _ _] [],
      simp [] [] [] ["[", expr nat.succ_eq_add_one, ",", expr add_comm, "]"] [] [] } }
end

@[simp]
theorem read_to_buffer (l : List α) i :
  l.to_buffer.read i =
    l.nth_le i
      (by 
        convert i.property 
        simp ) :=
  by 
    convert read_to_buffer' _ _ _
    ·
      simp 
    ·
      simpa using i.property

-- error in Data.Buffer.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nth_le_to_list' (b : buffer α) {i : exprℕ()} (h h') : «expr = »(b.to_list.nth_le i h, b.read ⟨i, h'⟩) :=
begin
  have [] [":", expr «expr = »(b.to_list.to_buffer.read ⟨i, by simpa [] [] [] [] [] ["using", expr h']⟩, b.read ⟨i, h'⟩)] [],
  { congr' [1] []; simp [] [] [] ["[", expr fin.heq_ext_iff, "]"] [] [] },
  simp [] [] [] ["[", "<-", expr this, "]"] [] []
end

theorem nth_le_to_list (b : Buffer α) {i : ℕ} h :
  b.to_list.nth_le i h =
    b.read
      ⟨i,
        by 
          simpa using h⟩ :=
  nth_le_to_list' _ _ _

theorem read_eq_nth_le_to_list (b : Buffer α) i :
  b.read i =
    b.to_list.nth_le i
      (by 
        simpa using i.is_lt) :=
  by 
    simp [nth_le_to_list]

theorem read_singleton (c : α) :
  [c].toBuffer.read
      ⟨0,
        by 
          simp ⟩ =
    c :=
  by 
    simp 

/-- The natural equivalence between lists and buffers, using
`list.to_buffer` and `buffer.to_list`. -/
def list_equiv_buffer (α : Type _) : List α ≃ Buffer α :=
  by 
    refine' { toFun := List.toBuffer, invFun := Buffer.toList, .. } <;> simp [left_inverse, Function.RightInverse]

instance  : Traversable Buffer :=
  Equiv.traversable list_equiv_buffer

instance  : IsLawfulTraversable Buffer :=
  Equiv.isLawfulTraversable list_equiv_buffer

/--
A convenience wrapper around `read` that just fails if the index is out of bounds.
-/
unsafe def read_t (b : Buffer α) (i : ℕ) : tactic α :=
  if h : i < b.size then return$ b.read (Finₓ.mk i h) else tactic.fail "invalid buffer access"

end Buffer

