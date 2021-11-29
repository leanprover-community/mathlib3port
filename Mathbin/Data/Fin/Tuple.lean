import Mathbin.Data.Fin.Basic

/-!
# Operation on tuples

We interpret maps `Π i : fin n, α i` as `n`-tuples of elements of possibly varying type `α i`,
`(α 0, …, α (n-1))`. A particular case is `fin n → α` of elements with all the same type.
In this case when `α i` is a constant map, then tuples are isomorphic (but not definitionally equal)
to `vector`s.

We define the following operations:

* `fin.tail` : the tail of an `n+1` tuple, i.e., its last `n` entries;
* `fin.cons` : adding an element at the beginning of an `n`-tuple, to get an `n+1`-tuple;
* `fin.init` : the beginning of an `n+1` tuple, i.e., its first `n` entries;
* `fin.snoc` : adding an element at the end of an `n`-tuple, to get an `n+1`-tuple. The name `snoc`
  comes from `cons` (i.e., adding an element to the left of a tuple) read in reverse order.
* `fin.insert_nth` : insert an element to a tuple at a given position.
* `fin.find p` : returns the first index `n` where `p n` is satisfied, and `none` if it is never
  satisfied.

-/


universe u v

namespace Finₓ

variable{m n : ℕ}

open Function

section Tuple

/-- There is exactly one tuple of size zero. -/
example  (α : Finₓ 0 → Sort u) : Unique (∀ (i : Finₓ 0), α i) :=
  by 
    infer_instance

@[simp]
theorem tuple0_le {α : ∀ (i : Finₓ 0), Type _} [∀ i, Preorderₓ (α i)] (f g : ∀ i, α i) : f ≤ g :=
  finZeroElim

variable{α :
    Finₓ (n+1) → Type u}(x : α 0)(q : ∀ i, α i)(p : ∀ (i : Finₓ n), α i.succ)(i : Finₓ n)(y : α i.succ)(z : α 0)

/-- The tail of an `n+1` tuple, i.e., its last `n` entries. -/
def tail (q : ∀ i, α i) : ∀ (i : Finₓ n), α i.succ :=
  fun i => q i.succ

-- error in Data.Fin.Tuple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem tail_def
{n : exprℕ()}
{α : fin «expr + »(n, 1) → Type*}
{q : ∀ i, α i} : «expr = »(tail (λ k : fin «expr + »(n, 1), q k), λ k : fin n, q k.succ) :=
rfl

/-- Adding an element at the beginning of an `n`-tuple, to get an `n+1`-tuple. -/
def cons (x : α 0) (p : ∀ (i : Finₓ n), α i.succ) : ∀ i, α i :=
  fun j => Finₓ.cases x p j

@[simp]
theorem tail_cons : tail (cons x p) = p :=
  by 
    simp [tail, cons]

@[simp]
theorem cons_succ : cons x p i.succ = p i :=
  by 
    simp [cons]

@[simp]
theorem cons_zero : cons x p 0 = x :=
  by 
    simp [cons]

-- error in Data.Fin.Tuple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Updating a tuple and adding an element at the beginning commute. -/
@[simp]
theorem cons_update : «expr = »(cons x (update p i y), update (cons x p) i.succ y) :=
begin
  ext [] [ident j] [],
  by_cases [expr h, ":", expr «expr = »(j, 0)],
  { rw [expr h] [],
    simp [] [] [] ["[", expr ne.symm (succ_ne_zero i), "]"] [] [] },
  { let [ident j'] [] [":=", expr pred j h],
    have [] [":", expr «expr = »(j'.succ, j)] [":=", expr succ_pred j h],
    rw ["[", "<-", expr this, ",", expr cons_succ, "]"] [],
    by_cases [expr h', ":", expr «expr = »(j', i)],
    { rw [expr h'] [],
      simp [] [] [] [] [] [] },
    { have [] [":", expr «expr ≠ »(j'.succ, i.succ)] [],
      by rwa ["[", expr ne.def, ",", expr succ_inj, "]"] [],
      rw ["[", expr update_noteq h', ",", expr update_noteq this, ",", expr cons_succ, "]"] [] } }
end

-- error in Data.Fin.Tuple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Adding an element at the beginning of a tuple and then updating it amounts to adding it
directly. -/ theorem update_cons_zero : «expr = »(update (cons x p) 0 z, cons z p) :=
begin
  ext [] [ident j] [],
  by_cases [expr h, ":", expr «expr = »(j, 0)],
  { rw [expr h] [],
    simp [] [] [] [] [] [] },
  { simp [] [] ["only"] ["[", expr h, ",", expr update_noteq, ",", expr ne.def, ",", expr not_false_iff, "]"] [] [],
    let [ident j'] [] [":=", expr pred j h],
    have [] [":", expr «expr = »(j'.succ, j)] [":=", expr succ_pred j h],
    rw ["[", "<-", expr this, ",", expr cons_succ, ",", expr cons_succ, "]"] [] }
end

-- error in Data.Fin.Tuple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp]
theorem cons_self_tail : «expr = »(cons (q 0) (tail q), q) :=
begin
  ext [] [ident j] [],
  by_cases [expr h, ":", expr «expr = »(j, 0)],
  { rw [expr h] [],
    simp [] [] [] [] [] [] },
  { let [ident j'] [] [":=", expr pred j h],
    have [] [":", expr «expr = »(j'.succ, j)] [":=", expr succ_pred j h],
    rw ["[", "<-", expr this, ",", expr tail, ",", expr cons_succ, "]"] [] }
end

/-- Updating the first element of a tuple does not change the tail. -/
@[simp]
theorem tail_update_zero : tail (update q 0 z) = tail q :=
  by 
    ext j 
    simp [tail, Finₓ.succ_ne_zero]

/-- Updating a nonzero element and taking the tail commute. -/
@[simp]
theorem tail_update_succ : tail (update q i.succ y) = update (tail q) i y :=
  by 
    ext j 
    byCases' h : j = i
    ·
      rw [h]
      simp [tail]
    ·
      simp [tail, (Finₓ.succ_injective n).Ne h, h]

-- error in Data.Fin.Tuple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem comp_cons
{α : Type*}
{β : Type*}
(g : α → β)
(y : α)
(q : fin n → α) : «expr = »(«expr ∘ »(g, cons y q), cons (g y) «expr ∘ »(g, q)) :=
begin
  ext [] [ident j] [],
  by_cases [expr h, ":", expr «expr = »(j, 0)],
  { rw [expr h] [],
    refl },
  { let [ident j'] [] [":=", expr pred j h],
    have [] [":", expr «expr = »(j'.succ, j)] [":=", expr succ_pred j h],
    rw ["[", "<-", expr this, ",", expr cons_succ, ",", expr comp_app, ",", expr cons_succ, "]"] [] }
end

theorem comp_tail {α : Type _} {β : Type _} (g : α → β) (q : Finₓ n.succ → α) : g ∘ tail q = tail (g ∘ q) :=
  by 
    ext j 
    simp [tail]

theorem le_cons [∀ i, Preorderₓ (α i)] {x : α 0} {q : ∀ i, α i} {p : ∀ (i : Finₓ n), α i.succ} :
  q ≤ cons x p ↔ q 0 ≤ x ∧ tail q ≤ p :=
  forall_fin_succ.trans$
    and_congr Iff.rfl$
      forall_congrₓ$
        fun j =>
          by 
            simp [tail]

theorem cons_le [∀ i, Preorderₓ (α i)] {x : α 0} {q : ∀ i, α i} {p : ∀ (i : Finₓ n), α i.succ} :
  cons x p ≤ q ↔ x ≤ q 0 ∧ p ≤ tail q :=
  @le_cons _ (fun i => OrderDual (α i)) _ x q p

@[simp]
theorem range_cons {α : Type _} {n : ℕ} (x : α) (b : Finₓ n → α) :
  Set.Range (Finₓ.cons x b : Finₓ n.succ → α) = insert x (Set.Range b) :=
  by 
    ext y 
    simp only [Set.mem_range, Set.mem_insert_iff]
    split 
    ·
      rintro ⟨i, rfl⟩
      refine' cases (Or.inl (cons_zero _ _)) (fun i => Or.inr ⟨i, _⟩) i 
      rw [cons_succ]
    ·
      rintro (rfl | ⟨i, hi⟩)
      ·
        exact ⟨0, Finₓ.cons_zero _ _⟩
      ·
        refine' ⟨i.succ, _⟩
        rw [cons_succ, hi]

/-- `fin.append ho u v` appends two vectors of lengths `m` and `n` to produce
one of length `o = m + n`.  `ho` provides control of definitional equality
for the vector length. -/
def append {α : Type _} {o : ℕ} (ho : o = m+n) (u : Finₓ m → α) (v : Finₓ n → α) : Finₓ o → α :=
  fun i =>
    if h : (i : ℕ) < m then u ⟨i, h⟩ else v ⟨(i : ℕ) - m, (tsub_lt_iff_left (le_of_not_ltₓ h)).2 (ho ▸ i.property)⟩

@[simp]
theorem fin_append_apply_zero {α : Type _} {o : ℕ} (ho : (o+1) = (m+1)+n) (u : Finₓ (m+1) → α) (v : Finₓ n → α) :
  Finₓ.append ho u v 0 = u 0 :=
  rfl

end Tuple

section TupleRight

/-! In the previous section, we have discussed inserting or removing elements on the left of a
tuple. In this section, we do the same on the right. A difference is that `fin (n+1)` is constructed
inductively from `fin n` starting from the left, not from the right. This implies that Lean needs
more help to realize that elements belong to the right types, i.e., we need to insert casts at
several places. -/


variable{α :
    Finₓ (n+1) →
      Type
        u}(x :
    α (last n))(q : ∀ i, α i)(p : ∀ (i : Finₓ n), α i.cast_succ)(i : Finₓ n)(y : α i.cast_succ)(z : α (last n))

/-- The beginning of an `n+1` tuple, i.e., its first `n` entries -/
def init (q : ∀ i, α i) (i : Finₓ n) : α i.cast_succ :=
  q i.cast_succ

-- error in Data.Fin.Tuple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem init_def
{n : exprℕ()}
{α : fin «expr + »(n, 1) → Type*}
{q : ∀ i, α i} : «expr = »(init (λ k : fin «expr + »(n, 1), q k), λ k : fin n, q k.cast_succ) :=
rfl

/-- Adding an element at the end of an `n`-tuple, to get an `n+1`-tuple. The name `snoc` comes from
`cons` (i.e., adding an element to the left of a tuple) read in reverse order. -/
def snoc (p : ∀ (i : Finₓ n), α i.cast_succ) (x : α (last n)) (i : Finₓ (n+1)) : α i :=
  if h : i.val < n then
    _root_.cast
      (by 
        rw [Finₓ.cast_succ_cast_lt i h])
      (p (cast_lt i h))
  else
    _root_.cast
      (by 
        rw [eq_last_of_not_lt h])
      x

-- error in Data.Fin.Tuple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem init_snoc : «expr = »(init (snoc p x), p) :=
begin
  ext [] [ident i] [],
  have [ident h'] [] [":=", expr fin.cast_lt_cast_succ i i.is_lt],
  simp [] [] [] ["[", expr init, ",", expr snoc, ",", expr i.is_lt, ",", expr h', "]"] [] [],
  convert [] [expr cast_eq rfl (p i)] []
end

-- error in Data.Fin.Tuple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem snoc_cast_succ : «expr = »(snoc p x i.cast_succ, p i) :=
begin
  have [] [":", expr «expr < »(i.cast_succ.val, n)] [":=", expr i.is_lt],
  have [ident h'] [] [":=", expr fin.cast_lt_cast_succ i i.is_lt],
  simp [] [] [] ["[", expr snoc, ",", expr this, ",", expr h', "]"] [] [],
  convert [] [expr cast_eq rfl (p i)] []
end

@[simp]
theorem snoc_last : snoc p x (last n) = x :=
  by 
    simp [snoc]

-- error in Data.Fin.Tuple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Updating a tuple and adding an element at the end commute. -/
@[simp]
theorem snoc_update : «expr = »(snoc (update p i y) x, update (snoc p x) i.cast_succ y) :=
begin
  ext [] [ident j] [],
  by_cases [expr h, ":", expr «expr < »(j.val, n)],
  { simp [] [] ["only"] ["[", expr snoc, ",", expr h, ",", expr dif_pos, "]"] [] [],
    by_cases [expr h', ":", expr «expr = »(j, cast_succ i)],
    { have [ident C1] [":", expr «expr = »(α i.cast_succ, α j)] [],
      by rw [expr h'] [],
      have [ident E1] [":", expr «expr = »(update (snoc p x) i.cast_succ y j, _root_.cast C1 y)] [],
      { have [] [":", expr «expr = »(update (snoc p x) j (_root_.cast C1 y) j, _root_.cast C1 y)] [],
        by simp [] [] [] [] [] [],
        convert [] [expr this] [],
        { exact [expr h'.symm] },
        { exact [expr heq_of_cast_eq (congr_arg α (eq.symm h')) rfl] } },
      have [ident C2] [":", expr «expr = »(α i.cast_succ, α (cast_succ (cast_lt j h)))] [],
      by rw ["[", expr cast_succ_cast_lt, ",", expr h', "]"] [],
      have [ident E2] [":", expr «expr = »(update p i y (cast_lt j h), _root_.cast C2 y)] [],
      { have [] [":", expr «expr = »(update p (cast_lt j h) (_root_.cast C2 y) (cast_lt j h), _root_.cast C2 y)] [],
        by simp [] [] [] [] [] [],
        convert [] [expr this] [],
        { simp [] [] [] ["[", expr h, ",", expr h', "]"] [] [] },
        { exact [expr heq_of_cast_eq C2 rfl] } },
      rw ["[", expr E1, ",", expr E2, "]"] [],
      exact [expr eq_rec_compose _ _ _] },
    { have [] [":", expr «expr¬ »(«expr = »(cast_lt j h, i))] [],
      by { assume [binders (E)],
        apply [expr h'],
        rw ["[", "<-", expr E, ",", expr cast_succ_cast_lt, "]"] [] },
      simp [] [] [] ["[", expr h', ",", expr this, ",", expr snoc, ",", expr h, "]"] [] [] } },
  { rw [expr eq_last_of_not_lt h] [],
    simp [] [] [] ["[", expr ne.symm (ne_of_lt (cast_succ_lt_last i)), "]"] [] [] }
end

-- error in Data.Fin.Tuple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Adding an element at the beginning of a tuple and then updating it amounts to adding it
directly. -/ theorem update_snoc_last : «expr = »(update (snoc p x) (last n) z, snoc p z) :=
begin
  ext [] [ident j] [],
  by_cases [expr h, ":", expr «expr < »(j.val, n)],
  { have [] [":", expr «expr ≠ »(j, last n)] [":=", expr ne_of_lt h],
    simp [] [] [] ["[", expr h, ",", expr update_noteq, ",", expr this, ",", expr snoc, "]"] [] [] },
  { rw [expr eq_last_of_not_lt h] [],
    simp [] [] [] [] [] [] }
end

-- error in Data.Fin.Tuple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp]
theorem snoc_init_self : «expr = »(snoc (init q) (q (last n)), q) :=
begin
  ext [] [ident j] [],
  by_cases [expr h, ":", expr «expr < »(j.val, n)],
  { have [] [":", expr «expr ≠ »(j, last n)] [":=", expr ne_of_lt h],
    simp [] [] [] ["[", expr h, ",", expr update_noteq, ",", expr this, ",", expr snoc, ",", expr init, ",", expr cast_succ_cast_lt, "]"] [] [],
    have [ident A] [":", expr «expr = »(cast_succ (cast_lt j h), j)] [":=", expr cast_succ_cast_lt _ _],
    rw ["<-", expr cast_eq rfl (q j)] [],
    congr' [1] []; rw [expr A] [] },
  { rw [expr eq_last_of_not_lt h] [],
    simp [] [] [] [] [] [] }
end

/-- Updating the last element of a tuple does not change the beginning. -/
@[simp]
theorem init_update_last : init (update q (last n) z) = init q :=
  by 
    ext j 
    simp [init, ne_of_ltₓ, cast_succ_lt_last]

/-- Updating an element and taking the beginning commute. -/
@[simp]
theorem init_update_cast_succ : init (update q i.cast_succ y) = update (init q) i y :=
  by 
    ext j 
    byCases' h : j = i
    ·
      rw [h]
      simp [init]
    ·
      simp [init, h]

/-- `tail` and `init` commute. We state this lemma in a non-dependent setting, as otherwise it
would involve a cast to convince Lean that the two types are equal, making it harder to use. -/
theorem tail_init_eq_init_tail {β : Type _} (q : Finₓ (n+2) → β) : tail (init q) = init (tail q) :=
  by 
    ext i 
    simp [tail, init, cast_succ_fin_succ]

-- error in Data.Fin.Tuple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `cons` and `snoc` commute. We state this lemma in a non-dependent setting, as otherwise it
would involve a cast to convince Lean that the two types are equal, making it harder to use. -/
theorem cons_snoc_eq_snoc_cons
{β : Type*}
(a : β)
(q : fin n → β)
(b : β) : «expr = »(@cons n.succ (λ i, β) a (snoc q b), snoc (cons a q) b) :=
begin
  ext [] [ident i] [],
  by_cases [expr h, ":", expr «expr = »(i, 0)],
  { rw [expr h] [],
    refl },
  set [] [ident j] [] [":="] [expr pred i h] ["with", ident ji],
  have [] [":", expr «expr = »(i, j.succ)] [],
  by rw ["[", expr ji, ",", expr succ_pred, "]"] [],
  rw ["[", expr this, ",", expr cons_succ, "]"] [],
  by_cases [expr h', ":", expr «expr < »(j.val, n)],
  { set [] [ident k] [] [":="] [expr cast_lt j h'] ["with", ident jk],
    have [] [":", expr «expr = »(j, k.cast_succ)] [],
    by rw ["[", expr jk, ",", expr cast_succ_cast_lt, "]"] [],
    rw ["[", expr this, ",", "<-", expr cast_succ_fin_succ, "]"] [],
    simp [] [] [] [] [] [] },
  rw ["[", expr eq_last_of_not_lt h', ",", expr succ_last, "]"] [],
  simp [] [] [] [] [] []
end

-- error in Data.Fin.Tuple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem comp_snoc
{α : Type*}
{β : Type*}
(g : α → β)
(q : fin n → α)
(y : α) : «expr = »(«expr ∘ »(g, snoc q y), snoc «expr ∘ »(g, q) (g y)) :=
begin
  ext [] [ident j] [],
  by_cases [expr h, ":", expr «expr < »(j.val, n)],
  { have [] [":", expr «expr ≠ »(j, last n)] [":=", expr ne_of_lt h],
    simp [] [] [] ["[", expr h, ",", expr this, ",", expr snoc, ",", expr cast_succ_cast_lt, "]"] [] [] },
  { rw [expr eq_last_of_not_lt h] [],
    simp [] [] [] [] [] [] }
end

theorem comp_init {α : Type _} {β : Type _} (g : α → β) (q : Finₓ n.succ → α) : g ∘ init q = init (g ∘ q) :=
  by 
    ext j 
    simp [init]

end TupleRight

section InsertNth

variable{α : Finₓ (n+1) → Type u}{β : Type v}

/-- Define a function on `fin (n + 1)` from a value on `i : fin (n + 1)` and values on each
`fin.succ_above i j`, `j : fin n`. This version is elaborated as eliminator and works for
propositions, see also `fin.insert_nth` for a version without an `@[elab_as_eliminator]`
attribute. -/
@[elab_as_eliminator]
def succ_above_cases {α : Finₓ (n+1) → Sort u} (i : Finₓ (n+1)) (x : α i) (p : ∀ (j : Finₓ n), α (i.succ_above j))
  (j : Finₓ (n+1)) : α j :=
  if hj : j = i then Eq.ndrec x hj.symm else
    if hlt : j < i then Eq.recOnₓ (succ_above_cast_lt hlt) (p _) else
      Eq.recOnₓ (succ_above_pred$ (Ne.lt_or_lt hj).resolve_left hlt) (p _)

theorem forall_iff_succ_above {p : Finₓ (n+1) → Prop} (i : Finₓ (n+1)) : (∀ j, p j) ↔ p i ∧ ∀ j, p (i.succ_above j) :=
  ⟨fun h => ⟨h _, fun j => h _⟩, fun h => succ_above_cases i h.1 h.2⟩

/-- Insert an element into a tuple at a given position. For `i = 0` see `fin.cons`,
for `i = fin.last n` see `fin.snoc`. See also `fin.succ_above_cases` for a version elaborated
as an eliminator. -/
def insert_nth (i : Finₓ (n+1)) (x : α i) (p : ∀ (j : Finₓ n), α (i.succ_above j)) (j : Finₓ (n+1)) : α j :=
  succ_above_cases i x p j

@[simp]
theorem insert_nth_apply_same (i : Finₓ (n+1)) (x : α i) (p : ∀ j, α (i.succ_above j)) : insert_nth i x p i = x :=
  by 
    simp [insert_nth, succ_above_cases]

@[simp]
theorem insert_nth_apply_succ_above (i : Finₓ (n+1)) (x : α i) (p : ∀ j, α (i.succ_above j)) (j : Finₓ n) :
  insert_nth i x p (i.succ_above j) = p j :=
  by 
    simp only [insert_nth, succ_above_cases, dif_neg (succ_above_ne _ _)]
    byCases' hlt : j.cast_succ < i
    ·
      rw [dif_pos ((succ_above_lt_iff _ _).2 hlt)]
      apply eq_of_heq ((eq_rec_heqₓ _ _).trans _)
      rw [cast_lt_succ_above hlt]
    ·
      rw [dif_neg (mt (succ_above_lt_iff _ _).1 hlt)]
      apply eq_of_heq ((eq_rec_heqₓ _ _).trans _)
      rw [pred_succ_above (le_of_not_ltₓ hlt)]

@[simp]
theorem succ_above_cases_eq_insert_nth : @succ_above_cases.{u + 1} = @insert_nth.{u} :=
  rfl

@[simp]
theorem insert_nth_comp_succ_above (i : Finₓ (n+1)) (x : β) (p : Finₓ n → β) : insert_nth i x p ∘ i.succ_above = p :=
  funext$ insert_nth_apply_succ_above i x p

theorem insert_nth_eq_iff {i : Finₓ (n+1)} {x : α i} {p : ∀ j, α (i.succ_above j)} {q : ∀ j, α j} :
  i.insert_nth x p = q ↔ q i = x ∧ p = fun j => q (i.succ_above j) :=
  by 
    simp [funext_iff, forall_iff_succ_above i, eq_comm]

theorem eq_insert_nth_iff {i : Finₓ (n+1)} {x : α i} {p : ∀ j, α (i.succ_above j)} {q : ∀ j, α j} :
  q = i.insert_nth x p ↔ q i = x ∧ p = fun j => q (i.succ_above j) :=
  eq_comm.trans insert_nth_eq_iff

theorem insert_nth_apply_below {i j : Finₓ (n+1)} (h : j < i) (x : α i) (p : ∀ k, α (i.succ_above k)) :
  i.insert_nth x p j = Eq.recOnₓ (succ_above_cast_lt h) (p$ j.cast_lt _) :=
  by 
    rw [insert_nth, succ_above_cases, dif_neg h.ne, dif_pos h]

theorem insert_nth_apply_above {i j : Finₓ (n+1)} (h : i < j) (x : α i) (p : ∀ k, α (i.succ_above k)) :
  i.insert_nth x p j = Eq.recOnₓ (succ_above_pred h) (p$ j.pred _) :=
  by 
    rw [insert_nth, succ_above_cases, dif_neg h.ne', dif_neg h.not_lt]

theorem insert_nth_zero (x : α 0) (p : ∀ (j : Finₓ n), α (succ_above 0 j)) :
  insert_nth 0 x p = cons x fun j => _root_.cast (congr_argₓ α (congr_funₓ succ_above_zero j)) (p j) :=
  by 
    refine'
      insert_nth_eq_iff.2
        ⟨by 
            simp ,
          _⟩
    ext j 
    convert (cons_succ _ _ _).symm

@[simp]
theorem insert_nth_zero' (x : β) (p : Finₓ n → β) : @insert_nth _ (fun _ => β) 0 x p = cons x p :=
  by 
    simp [insert_nth_zero]

theorem insert_nth_last (x : α (last n)) (p : ∀ (j : Finₓ n), α ((last n).succAbove j)) :
  insert_nth (last n) x p = snoc (fun j => _root_.cast (congr_argₓ α (succ_above_last_apply j)) (p j)) x :=
  by 
    refine'
      insert_nth_eq_iff.2
        ⟨by 
            simp ,
          _⟩
    ext j 
    apply eq_of_heq 
    trans snoc (fun j => _root_.cast (congr_argₓ α (succ_above_last_apply j)) (p j)) x j.cast_succ
    ·
      rw [snoc_cast_succ]
      exact (cast_heq _ _).symm
    ·
      apply congr_arg_heq 
      rw [succ_above_last]

@[simp]
theorem insert_nth_last' (x : β) (p : Finₓ n → β) : @insert_nth _ (fun _ => β) (last n) x p = snoc p x :=
  by 
    simp [insert_nth_last]

@[simp]
theorem insert_nth_zero_right [∀ j, HasZero (α j)] (i : Finₓ (n+1)) (x : α i) : i.insert_nth x 0 = Pi.single i x :=
  insert_nth_eq_iff.2$
    by 
      simp [succ_above_ne, Pi.zero_def]

theorem insert_nth_binop (op : ∀ j, α j → α j → α j) (i : Finₓ (n+1)) (x y : α i) (p q : ∀ j, α (i.succ_above j)) :
  (i.insert_nth (op i x y) fun j => op _ (p j) (q j)) = fun j => op j (i.insert_nth x p j) (i.insert_nth y q j) :=
  insert_nth_eq_iff.2$
    by 
      simp 

@[simp]
theorem insert_nth_mul [∀ j, Mul (α j)] (i : Finₓ (n+1)) (x y : α i) (p q : ∀ j, α (i.succ_above j)) :
  i.insert_nth (x*y) (p*q) = i.insert_nth x p*i.insert_nth y q :=
  insert_nth_binop (fun _ => ·*·) i x y p q

@[simp]
theorem insert_nth_add [∀ j, Add (α j)] (i : Finₓ (n+1)) (x y : α i) (p q : ∀ j, α (i.succ_above j)) :
  i.insert_nth (x+y) (p+q) = i.insert_nth x p+i.insert_nth y q :=
  insert_nth_binop (fun _ => ·+·) i x y p q

@[simp]
theorem insert_nth_div [∀ j, Div (α j)] (i : Finₓ (n+1)) (x y : α i) (p q : ∀ j, α (i.succ_above j)) :
  i.insert_nth (x / y) (p / q) = i.insert_nth x p / i.insert_nth y q :=
  insert_nth_binop (fun _ => · / ·) i x y p q

@[simp]
theorem insert_nth_sub [∀ j, Sub (α j)] (i : Finₓ (n+1)) (x y : α i) (p q : ∀ j, α (i.succ_above j)) :
  i.insert_nth (x - y) (p - q) = i.insert_nth x p - i.insert_nth y q :=
  insert_nth_binop (fun _ => Sub.sub) i x y p q

@[simp]
theorem insert_nth_sub_same [∀ j, AddGroupₓ (α j)] (i : Finₓ (n+1)) (x y : α i) (p : ∀ j, α (i.succ_above j)) :
  i.insert_nth x p - i.insert_nth y p = Pi.single i (x - y) :=
  by 
    simpRw [←insert_nth_sub, ←insert_nth_zero_right, Pi.sub_def, sub_self, Pi.zero_def]

variable[∀ i, Preorderₓ (α i)]

theorem insert_nth_le_iff {i : Finₓ (n+1)} {x : α i} {p : ∀ j, α (i.succ_above j)} {q : ∀ j, α j} :
  i.insert_nth x p ≤ q ↔ x ≤ q i ∧ p ≤ fun j => q (i.succ_above j) :=
  by 
    simp [Pi.le_def, forall_iff_succ_above i]

theorem le_insert_nth_iff {i : Finₓ (n+1)} {x : α i} {p : ∀ j, α (i.succ_above j)} {q : ∀ j, α j} :
  q ≤ i.insert_nth x p ↔ q i ≤ x ∧ (fun j => q (i.succ_above j)) ≤ p :=
  by 
    simp [Pi.le_def, forall_iff_succ_above i]

open Set

theorem insert_nth_mem_Icc {i : Finₓ (n+1)} {x : α i} {p : ∀ j, α (i.succ_above j)} {q₁ q₂ : ∀ j, α j} :
  i.insert_nth x p ∈ Icc q₁ q₂ ↔
    x ∈ Icc (q₁ i) (q₂ i) ∧ p ∈ Icc (fun j => q₁ (i.succ_above j)) fun j => q₂ (i.succ_above j) :=
  by 
    simp only [mem_Icc, insert_nth_le_iff, le_insert_nth_iff, And.assoc, And.left_comm]

theorem preimage_insert_nth_Icc_of_mem {i : Finₓ (n+1)} {x : α i} {q₁ q₂ : ∀ j, α j} (hx : x ∈ Icc (q₁ i) (q₂ i)) :
  i.insert_nth x ⁻¹' Icc q₁ q₂ = Icc (fun j => q₁ (i.succ_above j)) fun j => q₂ (i.succ_above j) :=
  Set.ext$
    fun p =>
      by 
        simp only [mem_preimage, insert_nth_mem_Icc, hx, true_andₓ]

theorem preimage_insert_nth_Icc_of_not_mem {i : Finₓ (n+1)} {x : α i} {q₁ q₂ : ∀ j, α j} (hx : x ∉ Icc (q₁ i) (q₂ i)) :
  i.insert_nth x ⁻¹' Icc q₁ q₂ = ∅ :=
  Set.ext$
    fun p =>
      by 
        simp only [mem_preimage, insert_nth_mem_Icc, hx, false_andₓ, mem_empty_eq]

end InsertNth

section Find

/-- `find p` returns the first index `n` where `p n` is satisfied, and `none` if it is never
satisfied. -/
def find : ∀ {n : ℕ} (p : Finₓ n → Prop) [DecidablePred p], Option (Finₓ n)
| 0, p, _ => none
| n+1, p, _ =>
  by 
    skip <;>
      exact
        Option.casesOn (@find n (fun i => p (i.cast_lt (Nat.lt_succ_of_ltₓ i.2))) _)
          (if h : p (Finₓ.last n) then some (Finₓ.last n) else none) fun i => some (i.cast_lt (Nat.lt_succ_of_ltₓ i.2))

-- error in Data.Fin.Tuple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- If `find p = some i`, then `p i` holds -/
theorem find_spec : ∀
{n : exprℕ()}
(p : fin n → exprProp())
[decidable_pred p]
{i : fin n}
(hi : «expr ∈ »(i, by exactI [expr fin.find p])), p i
| 0, p, I, i, hi := option.no_confusion hi
| «expr + »(n, 1), p, I, i, hi := begin
  dsimp [] ["[", expr find, "]"] [] ["at", ident hi],
  resetI,
  cases [expr h, ":", expr find (λ i : fin n, p (i.cast_lt (nat.lt_succ_of_lt i.2)))] ["with", ident j],
  { rw [expr h] ["at", ident hi],
    dsimp [] [] [] ["at", ident hi],
    split_ifs ["at", ident hi] ["with", ident hl, ident hl],
    { exact [expr «expr ▸ »(option.some_inj.1 hi, hl)] },
    { exact [expr option.no_confusion hi] } },
  { rw [expr h] ["at", ident hi],
    rw ["[", "<-", expr option.some_inj.1 hi, "]"] [],
    exact [expr find_spec _ h] }
end

-- error in Data.Fin.Tuple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `find p` does not return `none` if and only if `p i` holds at some index `i`. -/
theorem is_some_find_iff : ∀
{n : exprℕ()}
{p : fin n → exprProp()}
[decidable_pred p], by exactI [expr «expr ↔ »((find p).is_some, «expr∃ , »((i), p i))]
| 0, p, _ := iff_of_false (λ h, bool.no_confusion h) (λ ⟨i, _⟩, fin_zero_elim i)
| «expr + »(n, 1), p, _ := ⟨λ h, begin
   rw ["[", expr option.is_some_iff_exists, "]"] ["at", ident h],
   cases [expr h] ["with", ident i, ident hi],
   exactI [expr ⟨i, find_spec _ hi⟩]
 end, λ ⟨⟨i, hin⟩, hi⟩, begin
   resetI,
   dsimp [] ["[", expr find, "]"] [] [],
   cases [expr h, ":", expr find (λ i : fin n, p (i.cast_lt (nat.lt_succ_of_lt i.2)))] ["with", ident j],
   { split_ifs [] ["with", ident hl, ident hl],
     { exact [expr option.is_some_some] },
     { have [] [] [":=", expr (@is_some_find_iff n (λ
          x, p (x.cast_lt (nat.lt_succ_of_lt x.2))) _).2 ⟨⟨i, lt_of_le_of_ne (nat.le_of_lt_succ hin) (λ
           h, by clear_aux_decl; cases [expr h] []; exact [expr hl hi])⟩, hi⟩],
       rw [expr h] ["at", ident this],
       exact [expr this] } },
   { simp [] [] [] [] [] [] }
 end⟩

/-- `find p` returns `none` if and only if `p i` never holds. -/
theorem find_eq_none_iff {n : ℕ} {p : Finₓ n → Prop} [DecidablePred p] : find p = none ↔ ∀ i, ¬p i :=
  by 
    rw [←not_exists, ←is_some_find_iff] <;> cases find p <;> simp 

-- error in Data.Fin.Tuple: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `find p` returns `some i`, then `p j` does not hold for `j < i`, i.e., `i` is minimal among
the indices where `p` holds. -/
theorem find_min : ∀
{n : exprℕ()}
{p : fin n → exprProp()}
[decidable_pred p]
{i : fin n}
(hi : «expr ∈ »(i, by exactI [expr fin.find p]))
{j : fin n}
(hj : «expr < »(j, i)), «expr¬ »(p j)
| 0, p, _, i, hi, j, hj, hpj := option.no_confusion hi
| «expr + »(n, 1), p, _, i, hi, ⟨j, hjn⟩, hj, hpj := begin
  resetI,
  dsimp [] ["[", expr find, "]"] [] ["at", ident hi],
  cases [expr h, ":", expr find (λ i : fin n, p (i.cast_lt (nat.lt_succ_of_lt i.2)))] ["with", ident k],
  { rw ["[", expr h, "]"] ["at", ident hi],
    split_ifs ["at", ident hi] ["with", ident hl, ident hl],
    { have [] [] [":=", expr option.some_inj.1 hi],
      subst [expr this],
      rw ["[", expr find_eq_none_iff, "]"] ["at", ident h],
      exact [expr h ⟨j, hj⟩ hpj] },
    { exact [expr option.no_confusion hi] } },
  { rw [expr h] ["at", ident hi],
    dsimp [] [] [] ["at", ident hi],
    have [] [] [":=", expr option.some_inj.1 hi],
    subst [expr this],
    exact [expr find_min h (show «expr < »((⟨j, lt_trans hj k.2⟩ : fin n), k), from hj) hpj] }
end

theorem find_min' {p : Finₓ n → Prop} [DecidablePred p] {i : Finₓ n} (h : i ∈ Finₓ.find p) {j : Finₓ n} (hj : p j) :
  i ≤ j :=
  le_of_not_gtₓ fun hij => find_min h hij hj

theorem nat_find_mem_find {p : Finₓ n → Prop} [DecidablePred p] (h : ∃ i, ∃ hin : i < n, p ⟨i, hin⟩) :
  (⟨Nat.findₓ h, (Nat.find_specₓ h).fst⟩ : Finₓ n) ∈ find p :=
  let ⟨i, hin, hi⟩ := h 
  by 
    cases' hf : find p with f
    ·
      rw [find_eq_none_iff] at hf 
      exact (hf ⟨i, hin⟩ hi).elim
    ·
      refine' Option.some_inj.2 (le_antisymmₓ _ _)
      ·
        exact find_min' hf (Nat.find_specₓ h).snd
      ·
        exact
          Nat.find_min'ₓ _
            ⟨f.2,
              by 
                convert find_spec p hf <;> exact Finₓ.eta _ _⟩

theorem mem_find_iff {p : Finₓ n → Prop} [DecidablePred p] {i : Finₓ n} : i ∈ Finₓ.find p ↔ p i ∧ ∀ j, p j → i ≤ j :=
  ⟨fun hi => ⟨find_spec _ hi, fun _ => find_min' hi⟩,
    by 
      rintro ⟨hpi, hj⟩
      cases hfp : Finₓ.find p
      ·
        rw [find_eq_none_iff] at hfp 
        exact (hfp _ hpi).elim
      ·
        exact Option.some_inj.2 (le_antisymmₓ (find_min' hfp hpi) (hj _ (find_spec _ hfp)))⟩

theorem find_eq_some_iff {p : Finₓ n → Prop} [DecidablePred p] {i : Finₓ n} :
  Finₓ.find p = some i ↔ p i ∧ ∀ j, p j → i ≤ j :=
  mem_find_iff

theorem mem_find_of_unique {p : Finₓ n → Prop} [DecidablePred p] (h : ∀ i j, p i → p j → i = j) {i : Finₓ n}
  (hi : p i) : i ∈ Finₓ.find p :=
  mem_find_iff.2 ⟨hi, fun j hj => le_of_eqₓ$ h i j hi hj⟩

end Find

end Finₓ

