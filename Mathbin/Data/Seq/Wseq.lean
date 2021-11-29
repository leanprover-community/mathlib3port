import Leanbin.Data.Dlist 
import Mathbin.Data.List.Basic 
import Mathbin.Data.Seq.Seq

open Function

universe u v w

/-- Weak sequences.

  While the `seq` structure allows for lists which may not be finite,
  a weak sequence also allows the computation of each element to
  involve an indeterminate amount of computation, including possibly
  an infinite loop. This is represented as a regular `seq` interspersed
  with `none` elements to indicate that computation is ongoing.

  This model is appropriate for Haskell style lazy lists, and is closed
  under most interesting computation patterns on infinite lists,
  but conversely it is difficult to extract elements from it. -/
def Wseq α :=
  Seqₓₓ (Option α)

namespace Wseq

variable{α : Type u}{β : Type v}{γ : Type w}

/-- Turn a sequence into a weak sequence -/
def of_seq : Seqₓₓ α → Wseq α :=
  (· <$> ·) some

/-- Turn a list into a weak sequence -/
def of_list (l : List α) : Wseq α :=
  of_seq l

/-- Turn a stream into a weak sequence -/
def of_stream (l : Streamₓ α) : Wseq α :=
  of_seq l

instance coe_seq : Coe (Seqₓₓ α) (Wseq α) :=
  ⟨of_seq⟩

instance coe_list : Coe (List α) (Wseq α) :=
  ⟨of_list⟩

instance coe_stream : Coe (Streamₓ α) (Wseq α) :=
  ⟨of_stream⟩

/-- The empty weak sequence -/
def nil : Wseq α :=
  Seqₓₓ.nil

instance  : Inhabited (Wseq α) :=
  ⟨nil⟩

/-- Prepend an element to a weak sequence -/
def cons (a : α) : Wseq α → Wseq α :=
  Seqₓₓ.cons (some a)

/-- Compute for one tick, without producing any elements -/
def think : Wseq α → Wseq α :=
  Seqₓₓ.cons none

/-- Destruct a weak sequence, to (eventually possibly) produce either
  `none` for `nil` or `some (a, s)` if an element is produced. -/
def destruct : Wseq α → Computation (Option (α × Wseq α)) :=
  Computation.corec
    fun s =>
      match Seqₓₓ.destruct s with 
      | none => Sum.inl none
      | some (none, s') => Sum.inr s'
      | some (some a, s') => Sum.inl (some (a, s'))

def cases_on {C : Wseq α → Sort v} (s : Wseq α) (h1 : C nil) (h2 : ∀ x s, C (cons x s)) (h3 : ∀ s, C (think s)) : C s :=
  Seqₓₓ.casesOn s h1 fun o => Option.casesOn o h3 h2

protected def mem (a : α) (s : Wseq α) :=
  Seqₓₓ.Mem (some a) s

instance  : HasMem α (Wseq α) :=
  ⟨Wseq.Mem⟩

theorem not_mem_nil (a : α) : a ∉ @nil α :=
  Seqₓₓ.not_mem_nil a

/-- Get the head of a weak sequence. This involves a possibly
  infinite computation. -/
def head (s : Wseq α) : Computation (Option α) :=
  Computation.map ((· <$> ·) Prod.fst) (destruct s)

/-- Encode a computation yielding a weak sequence into additional
  `think` constructors in a weak sequence -/
def flatten : Computation (Wseq α) → Wseq α :=
  Seqₓₓ.corec
    fun c =>
      match Computation.destruct c with 
      | Sum.inl s => Seqₓₓ.omap return (Seqₓₓ.destruct s)
      | Sum.inr c' => some (none, c')

/-- Get the tail of a weak sequence. This doesn't need a `computation`
  wrapper, unlike `head`, because `flatten` allows us to hide this
  in the construction of the weak sequence itself. -/
def tail (s : Wseq α) : Wseq α :=
  flatten$ (fun o => Option.recOn o nil Prod.snd) <$> destruct s

/-- drop the first `n` elements from `s`. -/
def drop (s : Wseq α) : ℕ → Wseq α
| 0 => s
| n+1 => tail (drop n)

attribute [simp] drop

/-- Get the nth element of `s`. -/
def nth (s : Wseq α) (n : ℕ) : Computation (Option α) :=
  head (drop s n)

/-- Convert `s` to a list (if it is finite and completes in finite time). -/
def to_list (s : Wseq α) : Computation (List α) :=
  @Computation.corec (List α) (List α × Wseq α)
    (fun ⟨l, s⟩ =>
      match Seqₓₓ.destruct s with 
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a :: l, s'))
    ([], s)

/-- Get the length of `s` (if it is finite and completes in finite time). -/
def length (s : Wseq α) : Computation ℕ :=
  @Computation.corec ℕ (ℕ × Wseq α)
    (fun ⟨n, s⟩ =>
      match Seqₓₓ.destruct s with 
      | none => Sum.inl n
      | some (none, s') => Sum.inr (n, s')
      | some (some a, s') => Sum.inr (n+1, s'))
    (0, s)

/-- A weak sequence is finite if `to_list s` terminates. Equivalently,
  it is a finite number of `think` and `cons` applied to `nil`. -/
class is_finite(s : Wseq α) : Prop where 
  out : (to_list s).Terminates

instance to_list_terminates (s : Wseq α) [h : is_finite s] : (to_list s).Terminates :=
  h.out

/-- Get the list corresponding to a finite weak sequence. -/
def get (s : Wseq α) [is_finite s] : List α :=
  (to_list s).get

/-- A weak sequence is *productive* if it never stalls forever - there are
 always a finite number of `think`s between `cons` constructors.
 The sequence itself is allowed to be infinite though. -/
class productive(s : Wseq α) : Prop where 
  nth_terminates : ∀ n, (nth s n).Terminates

theorem productive_iff (s : Wseq α) : productive s ↔ ∀ n, (nth s n).Terminates :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

instance nth_terminates (s : Wseq α) [h : productive s] : ∀ n, (nth s n).Terminates :=
  h.nth_terminates

instance head_terminates (s : Wseq α) [productive s] : (head s).Terminates :=
  s.nth_terminates 0

/-- Replace the `n`th element of `s` with `a`. -/
def update_nth (s : Wseq α) (n : ℕ) (a : α) : Wseq α :=
  @Seqₓₓ.corec (Option α) (ℕ × Wseq α)
    (fun ⟨n, s⟩ =>
      match Seqₓₓ.destruct s, n with 
      | none, n => none
      | some (none, s'), n => some (none, n, s')
      | some (some a', s'), 0 => some (some a', 0, s')
      | some (some a', s'), 1 => some (some a, 0, s')
      | some (some a', s'), n+2 => some (some a', n+1, s'))
    (n+1, s)

/-- Remove the `n`th element of `s`. -/
def remove_nth (s : Wseq α) (n : ℕ) : Wseq α :=
  @Seqₓₓ.corec (Option α) (ℕ × Wseq α)
    (fun ⟨n, s⟩ =>
      match Seqₓₓ.destruct s, n with 
      | none, n => none
      | some (none, s'), n => some (none, n, s')
      | some (some a', s'), 0 => some (some a', 0, s')
      | some (some a', s'), 1 => some (none, 0, s')
      | some (some a', s'), n+2 => some (some a', n+1, s'))
    (n+1, s)

/-- Map the elements of `s` over `f`, removing any values that yield `none`. -/
def filter_map (f : α → Option β) : Wseq α → Wseq β :=
  Seqₓₓ.corec
    fun s =>
      match Seqₓₓ.destruct s with 
      | none => none
      | some (none, s') => some (none, s')
      | some (some a, s') => some (f a, s')

/-- Select the elements of `s` that satisfy `p`. -/
def filter (p : α → Prop) [DecidablePred p] : Wseq α → Wseq α :=
  filter_map fun a => if p a then some a else none

/-- Get the first element of `s` satisfying `p`. -/
def find (p : α → Prop) [DecidablePred p] (s : Wseq α) : Computation (Option α) :=
  head$ filter p s

/-- Zip a function over two weak sequences -/
def zip_with (f : α → β → γ) (s1 : Wseq α) (s2 : Wseq β) : Wseq γ :=
  @Seqₓₓ.corec (Option γ) (Wseq α × Wseq β)
    (fun ⟨s1, s2⟩ =>
      match Seqₓₓ.destruct s1, Seqₓₓ.destruct s2 with 
      | some (none, s1'), some (none, s2') => some (none, s1', s2')
      | some (some a1, s1'), some (none, s2') => some (none, s1, s2')
      | some (none, s1'), some (some a2, s2') => some (none, s1', s2)
      | some (some a1, s1'), some (some a2, s2') => some (some (f a1 a2), s1', s2')
      | _, _ => none)
    (s1, s2)

/-- Zip two weak sequences into a single sequence of pairs -/
def zip : Wseq α → Wseq β → Wseq (α × β) :=
  zip_with Prod.mk

/-- Get the list of indexes of elements of `s` satisfying `p` -/
def find_indexes (p : α → Prop) [DecidablePred p] (s : Wseq α) : Wseq ℕ :=
  (zip s (Streamₓ.nats : Wseq ℕ)).filterMap fun ⟨a, n⟩ => if p a then some n else none

/-- Get the index of the first element of `s` satisfying `p` -/
def find_index (p : α → Prop) [DecidablePred p] (s : Wseq α) : Computation ℕ :=
  (fun o => Option.getOrElse o 0) <$> head (find_indexes p s)

/-- Get the index of the first occurrence of `a` in `s` -/
def index_of [DecidableEq α] (a : α) : Wseq α → Computation ℕ :=
  find_index (Eq a)

/-- Get the indexes of occurrences of `a` in `s` -/
def indexes_of [DecidableEq α] (a : α) : Wseq α → Wseq ℕ :=
  find_indexes (Eq a)

/-- `union s1 s2` is a weak sequence which interleaves `s1` and `s2` in
  some order (nondeterministically). -/
def union (s1 s2 : Wseq α) : Wseq α :=
  @Seqₓₓ.corec (Option α) (Wseq α × Wseq α)
    (fun ⟨s1, s2⟩ =>
      match Seqₓₓ.destruct s1, Seqₓₓ.destruct s2 with 
      | none, none => none
      | some (a1, s1'), none => some (a1, s1', nil)
      | none, some (a2, s2') => some (a2, nil, s2')
      | some (none, s1'), some (none, s2') => some (none, s1', s2')
      | some (some a1, s1'), some (none, s2') => some (some a1, s1', s2')
      | some (none, s1'), some (some a2, s2') => some (some a2, s1', s2')
      | some (some a1, s1'), some (some a2, s2') => some (some a1, cons a2 s1', s2'))
    (s1, s2)

/-- Returns `tt` if `s` is `nil` and `ff` if `s` has an element -/
def IsEmpty (s : Wseq α) : Computation Bool :=
  Computation.map Option.isNone$ head s

/-- Calculate one step of computation -/
def compute (s : Wseq α) : Wseq α :=
  match Seqₓₓ.destruct s with 
  | some (none, s') => s'
  | _ => s

/-- Get the first `n` elements of a weak sequence -/
def take (s : Wseq α) (n : ℕ) : Wseq α :=
  @Seqₓₓ.corec (Option α) (ℕ × Wseq α)
    (fun ⟨n, s⟩ =>
      match n, Seqₓₓ.destruct s with 
      | 0, _ => none
      | m+1, none => none
      | m+1, some (none, s') => some (none, m+1, s')
      | m+1, some (some a, s') => some (some a, m, s'))
    (n, s)

/-- Split the sequence at position `n` into a finite initial segment
  and the weak sequence tail -/
def split_at (s : Wseq α) (n : ℕ) : Computation (List α × Wseq α) :=
  @Computation.corec (List α × Wseq α) (ℕ × List α × Wseq α)
    (fun ⟨n, l, s⟩ =>
      match n, Seqₓₓ.destruct s with 
      | 0, _ => Sum.inl (l.reverse, s)
      | m+1, none => Sum.inl (l.reverse, s)
      | m+1, some (none, s') => Sum.inr (n, l, s')
      | m+1, some (some a, s') => Sum.inr (m, a :: l, s'))
    (n, [], s)

-- error in Data.Seq.Wseq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Returns `tt` if any element of `s` satisfies `p` -/ def any (s : wseq α) (p : α → bool) : computation bool :=
computation.corec (λ s : wseq α, match seq.destruct s with
 | none := sum.inl ff
 | some (none, s') := sum.inr s'
 | some (some a, s') := if p a then sum.inl tt else sum.inr s' end) s

-- error in Data.Seq.Wseq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Returns `tt` if every element of `s` satisfies `p` -/ def all (s : wseq α) (p : α → bool) : computation bool :=
computation.corec (λ s : wseq α, match seq.destruct s with
 | none := sum.inl tt
 | some (none, s') := sum.inr s'
 | some (some a, s') := if p a then sum.inr s' else sum.inl ff end) s

/-- Apply a function to the elements of the sequence to produce a sequence
  of partial results. (There is no `scanr` because this would require
  working from the end of the sequence, which may not exist.) -/
def scanl (f : α → β → α) (a : α) (s : Wseq β) : Wseq α :=
  cons a$
    @Seqₓₓ.corec (Option α) (α × Wseq β)
      (fun ⟨a, s⟩ =>
        match Seqₓₓ.destruct s with 
        | none => none
        | some (none, s') => some (none, a, s')
        | some (some b, s') =>
          let a' := f a b 
          some (some a', a', s'))
      (a, s)

/-- Get the weak sequence of initial segments of the input sequence -/
def inits (s : Wseq α) : Wseq (List α) :=
  cons []$
    @Seqₓₓ.corec (Option (List α)) (Dlist α × Wseq α)
      (fun ⟨l, s⟩ =>
        match Seqₓₓ.destruct s with 
        | none => none
        | some (none, s') => some (none, l, s')
        | some (some a, s') =>
          let l' := l.concat a 
          some (some l'.to_list, l', s'))
      (Dlist.empty, s)

/-- Like take, but does not wait for a result. Calculates `n` steps of
  computation and returns the sequence computed so far -/
def collect (s : Wseq α) (n : ℕ) : List α :=
  (Seqₓₓ.take n s).filterMap id

/-- Append two weak sequences. As with `seq.append`, this may not use
  the second sequence if the first one takes forever to compute -/
def append : Wseq α → Wseq α → Wseq α :=
  Seqₓₓ.append

/-- Map a function over a weak sequence -/
def map (f : α → β) : Wseq α → Wseq β :=
  Seqₓₓ.map (Option.map f)

-- error in Data.Seq.Wseq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Flatten a sequence of weak sequences. (Note that this allows
  empty sequences, unlike `seq.join`.) -/ def join (S : wseq (wseq α)) : wseq α :=
seq.join «expr <$> »(λ o : option (wseq α), match o with
 | none := seq1.ret none
 | some s := (none, s) end, S)

/-- Monadic bind operator for weak sequences -/
def bind (s : Wseq α) (f : α → Wseq β) : Wseq β :=
  join (map f s)

@[simp]
def lift_rel_o (R : α → β → Prop) (C : Wseq α → Wseq β → Prop) : Option (α × Wseq α) → Option (β × Wseq β) → Prop
| none, none => True
| some (a, s), some (b, t) => R a b ∧ C s t
| _, _ => False

theorem lift_rel_o.imp {R S : α → β → Prop} {C D : Wseq α → Wseq β → Prop} (H1 : ∀ a b, R a b → S a b)
  (H2 : ∀ s t, C s t → D s t) : ∀ {o p}, lift_rel_o R C o p → lift_rel_o S D o p
| none, none, h => trivialₓ
| some (a, s), some (b, t), h => And.imp (H1 _ _) (H2 _ _) h
| none, some _, h => False.elim h
| some (_, _), none, h => False.elim h

theorem lift_rel_o.imp_right (R : α → β → Prop) {C D : Wseq α → Wseq β → Prop} (H : ∀ s t, C s t → D s t) {o p} :
  lift_rel_o R C o p → lift_rel_o R D o p :=
  lift_rel_o.imp (fun _ _ => id) H

@[simp]
def bisim_o (R : Wseq α → Wseq α → Prop) : Option (α × Wseq α) → Option (α × Wseq α) → Prop :=
  lift_rel_o (· = ·) R

theorem bisim_o.imp {R S : Wseq α → Wseq α → Prop} (H : ∀ s t, R s t → S s t) {o p} : bisim_o R o p → bisim_o S o p :=
  lift_rel_o.imp_right _ H

/-- Two weak sequences are `lift_rel R` related if they are either both empty,
  or they are both nonempty and the heads are `R` related and the tails are
  `lift_rel R` related. (This is a coinductive definition.) -/
def lift_rel (R : α → β → Prop) (s : Wseq α) (t : Wseq β) : Prop :=
  ∃ C : Wseq α → Wseq β → Prop, C s t ∧ ∀ {s t}, C s t → Computation.LiftRel (lift_rel_o R C) (destruct s) (destruct t)

/-- If two sequences are equivalent, then they have the same values and
  the same computational behavior (i.e. if one loops forever then so does
  the other), although they may differ in the number of `think`s needed to
  arrive at the answer. -/
def Equiv : Wseq α → Wseq α → Prop :=
  lift_rel (· = ·)

theorem lift_rel_destruct {R : α → β → Prop} {s : Wseq α} {t : Wseq β} :
  lift_rel R s t → Computation.LiftRel (lift_rel_o R (lift_rel R)) (destruct s) (destruct t)
| ⟨R, h1, h2⟩ =>
  by 
    refine' Computation.LiftRel.imp _ _ _ (h2 h1) <;> apply lift_rel_o.imp_right <;> exact fun s' t' h' => ⟨R, h', @h2⟩

-- error in Data.Seq.Wseq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lift_rel_destruct_iff
{R : α → β → exprProp()}
{s : wseq α}
{t : wseq β} : «expr ↔ »(lift_rel R s t, computation.lift_rel (lift_rel_o R (lift_rel R)) (destruct s) (destruct t)) :=
⟨lift_rel_destruct, λ
 h, ⟨λ
  s
  t, «expr ∨ »(lift_rel R s t, computation.lift_rel (lift_rel_o R (lift_rel R)) (destruct s) (destruct t)), or.inr h, λ
  s t h, begin
    have [ident h] [":", expr computation.lift_rel (lift_rel_o R (lift_rel R)) (destruct s) (destruct t)] [],
    { cases [expr h] ["with", ident h, ident h],
      exact [expr lift_rel_destruct h],
      assumption },
    apply [expr computation.lift_rel.imp _ _ _ h],
    intros [ident a, ident b],
    apply [expr lift_rel_o.imp_right],
    intros [ident s, ident t],
    apply [expr or.inl]
  end⟩⟩

infixl:50 " ~ " => Equiv

theorem destruct_congr {s t : Wseq α} : s ~ t → Computation.LiftRel (bisim_o (· ~ ·)) (destruct s) (destruct t) :=
  lift_rel_destruct

theorem destruct_congr_iff {s t : Wseq α} : s ~ t ↔ Computation.LiftRel (bisim_o (· ~ ·)) (destruct s) (destruct t) :=
  lift_rel_destruct_iff

-- error in Data.Seq.Wseq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem lift_rel.refl (R : α → α → exprProp()) (H : reflexive R) : reflexive (lift_rel R) :=
λ s, begin
  refine [expr ⟨(«expr = »), rfl, λ (s t) (h : «expr = »(s, t)), _⟩],
  rw ["<-", expr h] [],
  apply [expr computation.lift_rel.refl],
  intro [ident a],
  cases [expr a] ["with", ident a],
  simp [] [] [] [] [] [],
  cases [expr a] []; simp [] [] [] [] [] [],
  apply [expr H]
end

theorem lift_rel_o.swap (R : α → β → Prop) C : swap (lift_rel_o R C) = lift_rel_o (swap R) (swap C) :=
  by 
    funext x y <;>
      cases' x with x <;> [skip, cases x] <;>
        ·
          cases' y with y <;> [skip, cases y] <;> rfl

-- error in Data.Seq.Wseq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem lift_rel.swap_lem {R : α → β → exprProp()} {s1 s2} (h : lift_rel R s1 s2) : lift_rel (swap R) s2 s1 :=
begin
  refine [expr ⟨swap (lift_rel R), h, λ (s t) (h : lift_rel R t s), _⟩],
  rw ["[", "<-", expr lift_rel_o.swap, ",", expr computation.lift_rel.swap, "]"] [],
  apply [expr lift_rel_destruct h]
end

theorem lift_rel.swap (R : α → β → Prop) : swap (lift_rel R) = lift_rel (swap R) :=
  funext$ fun x => funext$ fun y => propext ⟨lift_rel.swap_lem, lift_rel.swap_lem⟩

-- error in Data.Seq.Wseq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem lift_rel.symm (R : α → α → exprProp()) (H : symmetric R) : symmetric (lift_rel R) :=
λ
(s1 s2)
(h : swap (lift_rel R) s2 s1), by rwa ["[", expr lift_rel.swap, ",", expr show «expr = »(swap R, R), from «expr $ »(funext, λ
  a, «expr $ »(funext, λ b, «expr $ »(propext, by constructor; apply [expr H]))), "]"] ["at", ident h]

-- error in Data.Seq.Wseq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lift_rel.trans (R : α → α → exprProp()) (H : transitive R) : transitive (lift_rel R) :=
λ s t u h1 h2, begin
  refine [expr ⟨λ s u, «expr∃ , »((t), «expr ∧ »(lift_rel R s t, lift_rel R t u)), ⟨t, h1, h2⟩, λ s u h, _⟩],
  rcases [expr h, "with", "⟨", ident t, ",", ident h1, ",", ident h2, "⟩"],
  have [ident h1] [] [":=", expr lift_rel_destruct h1],
  have [ident h2] [] [":=", expr lift_rel_destruct h2],
  refine [expr computation.lift_rel_def.2 ⟨(computation.terminates_of_lift_rel h1).trans (computation.terminates_of_lift_rel h2), λ
    a c ha hc, _⟩],
  rcases [expr h1.left ha, "with", "⟨", ident b, ",", ident hb, ",", ident t1, "⟩"],
  have [ident t2] [] [":=", expr computation.rel_of_lift_rel h2 hb hc],
  cases [expr a] ["with", ident a]; cases [expr c] ["with", ident c],
  { trivial },
  { cases [expr b] [],
    { cases [expr t2] [] },
    { cases [expr t1] [] } },
  { cases [expr a] [],
    cases [expr b] ["with", ident b],
    { cases [expr t1] [] },
    { cases [expr b] [],
      cases [expr t2] [] } },
  { cases [expr a] ["with", ident a, ident s],
    cases [expr b] ["with", ident b],
    { cases [expr t1] [] },
    cases [expr b] ["with", ident b, ident t],
    cases [expr c] ["with", ident c, ident u],
    cases [expr t1] ["with", ident ab, ident st],
    cases [expr t2] ["with", ident bc, ident tu],
    exact [expr ⟨H ab bc, t, st, tu⟩] }
end

theorem lift_rel.equiv (R : α → α → Prop) : Equivalenceₓ R → Equivalenceₓ (lift_rel R)
| ⟨refl, symm, trans⟩ => ⟨lift_rel.refl R refl, lift_rel.symm R symm, lift_rel.trans R trans⟩

@[refl]
theorem Equiv.refl : ∀ (s : Wseq α), s ~ s :=
  lift_rel.refl (· = ·) Eq.refl

@[symm]
theorem Equiv.symm : ∀ {s t : Wseq α}, s ~ t → t ~ s :=
  lift_rel.symm (· = ·) (@Eq.symm _)

@[trans]
theorem Equiv.trans : ∀ {s t u : Wseq α}, s ~ t → t ~ u → s ~ u :=
  lift_rel.trans (· = ·) (@Eq.trans _)

theorem equiv.equivalence : Equivalenceₓ (@Equiv α) :=
  ⟨@Equiv.refl _, @Equiv.symm _, @Equiv.trans _⟩

open Computation

local notation "return" => Computation.return

@[simp]
theorem destruct_nil : destruct (nil : Wseq α) = return none :=
  Computation.destruct_eq_ret rfl

@[simp]
theorem destruct_cons (a : α) s : destruct (cons a s) = return (some (a, s)) :=
  Computation.destruct_eq_ret$
    by 
      simp [destruct, cons, Computation.rmap]

@[simp]
theorem destruct_think (s : Wseq α) : destruct (think s) = (destruct s).think :=
  Computation.destruct_eq_think$
    by 
      simp [destruct, think, Computation.rmap]

@[simp]
theorem seq_destruct_nil : Seqₓₓ.destruct (nil : Wseq α) = none :=
  Seqₓₓ.destruct_nil

@[simp]
theorem seq_destruct_cons (a : α) s : Seqₓₓ.destruct (cons a s) = some (some a, s) :=
  Seqₓₓ.destruct_cons _ _

@[simp]
theorem seq_destruct_think (s : Wseq α) : Seqₓₓ.destruct (think s) = some (none, s) :=
  Seqₓₓ.destruct_cons _ _

@[simp]
theorem head_nil : head (nil : Wseq α) = return none :=
  by 
    simp [head] <;> rfl

@[simp]
theorem head_cons (a : α) s : head (cons a s) = return (some a) :=
  by 
    simp [head] <;> rfl

@[simp]
theorem head_think (s : Wseq α) : head (think s) = (head s).think :=
  by 
    simp [head] <;> rfl

@[simp]
theorem flatten_ret (s : Wseq α) : flatten (return s) = s :=
  by 
    refine' Seqₓₓ.eq_of_bisim (fun s1 s2 => flatten (return s2) = s1) _ rfl 
    intro s' s h 
    rw [←h]
    simp [flatten]
    cases Seqₓₓ.destruct s
    ·
      simp 
    ·
      cases' val with o s' 
      simp 

@[simp]
theorem flatten_think (c : Computation (Wseq α)) : flatten c.think = think (flatten c) :=
  Seqₓₓ.destruct_eq_cons$
    by 
      simp [flatten, think]

@[simp]
theorem destruct_flatten (c : Computation (Wseq α)) : destruct (flatten c) = c >>= destruct :=
  by 
    refine'
      Computation.eq_of_bisim (fun c1 c2 => c1 = c2 ∨ ∃ c, c1 = destruct (flatten c) ∧ c2 = Computation.bind c destruct)
        _ (Or.inr ⟨c, rfl, rfl⟩)
    intro c1 c2 h 
    exact
      match c1, c2, h with 
      | _, _, Or.inl$ Eq.refl c =>
        by 
          cases c.destruct <;> simp 
      | _, _, Or.inr ⟨c, rfl, rfl⟩ =>
        by 
          apply c.cases_on (fun a => _) fun c' => _ <;>
            repeat' 
              simp 
          ·
            cases (destruct a).destruct <;> simp 
          ·
            exact Or.inr ⟨c', rfl, rfl⟩

theorem head_terminates_iff (s : Wseq α) : terminates (head s) ↔ terminates (destruct s) :=
  terminates_map_iff _ (destruct s)

@[simp]
theorem tail_nil : tail (nil : Wseq α) = nil :=
  by 
    simp [tail]

@[simp]
theorem tail_cons (a : α) s : tail (cons a s) = s :=
  by 
    simp [tail]

@[simp]
theorem tail_think (s : Wseq α) : tail (think s) = (tail s).think :=
  by 
    simp [tail]

@[simp]
theorem dropn_nil n : drop (nil : Wseq α) n = nil :=
  by 
    induction n <;> simp [drop]

@[simp]
theorem dropn_cons (a : α) s n : drop (cons a s) (n+1) = drop s n :=
  by 
    induction n <;> simp [drop]

@[simp]
theorem dropn_think (s : Wseq α) n : drop (think s) n = (drop s n).think :=
  by 
    induction n <;> simp [drop]

theorem dropn_add (s : Wseq α) m : ∀ n, drop s (m+n) = drop (drop s m) n
| 0 => rfl
| n+1 => congr_argₓ tail (dropn_add n)

theorem dropn_tail (s : Wseq α) n : drop (tail s) n = drop s (n+1) :=
  by 
    rw [add_commₓ] <;> symm <;> apply dropn_add

theorem nth_add (s : Wseq α) m n : nth s (m+n) = nth (drop s m) n :=
  congr_argₓ head (dropn_add _ _ _)

theorem nth_tail (s : Wseq α) n : nth (tail s) n = nth s (n+1) :=
  congr_argₓ head (dropn_tail _ _)

@[simp]
theorem join_nil : join nil = (nil : Wseq α) :=
  Seqₓₓ.join_nil

@[simp]
theorem join_think (S : Wseq (Wseq α)) : join (think S) = think (join S) :=
  by 
    simp [think, join]
    unfold Functor.map 
    simp [join, Seq1.ret]

@[simp]
theorem join_cons (s : Wseq α) S : join (cons s S) = think (append s (join S)) :=
  by 
    simp [think, join]
    unfold Functor.map 
    simp [join, cons, append]

@[simp]
theorem nil_append (s : Wseq α) : append nil s = s :=
  Seqₓₓ.nil_append _

@[simp]
theorem cons_append (a : α) s t : append (cons a s) t = cons a (append s t) :=
  Seqₓₓ.cons_append _ _ _

@[simp]
theorem think_append (s t : Wseq α) : append (think s) t = think (append s t) :=
  Seqₓₓ.cons_append _ _ _

@[simp]
theorem append_nil (s : Wseq α) : append s nil = s :=
  Seqₓₓ.append_nil _

@[simp]
theorem append_assoc (s t u : Wseq α) : append (append s t) u = append s (append t u) :=
  Seqₓₓ.append_assoc _ _ _

@[simp]
def tail.aux : Option (α × Wseq α) → Computation (Option (α × Wseq α))
| none => return none
| some (a, s) => destruct s

theorem destruct_tail (s : Wseq α) : destruct (tail s) = destruct s >>= tail.aux :=
  by 
    simp [tail]
    rw [←bind_pure_comp_eq_map, IsLawfulMonad.bind_assoc]
    apply congr_argₓ 
    ext1 (_ | ⟨a, s⟩) <;> apply (@pure_bind Computation _ _ _ _ _ _).trans _ <;> simp 

@[simp]
def drop.aux : ℕ → Option (α × Wseq α) → Computation (Option (α × Wseq α))
| 0 => return
| n+1 => fun a => tail.aux a >>= drop.aux n

theorem drop.aux_none : ∀ n, @drop.aux α n none = return none
| 0 => rfl
| n+1 =>
  show Computation.bind (return none) (drop.aux n) = return none by 
    rw [ret_bind, drop.aux_none]

theorem destruct_dropn : ∀ (s : Wseq α) n, destruct (drop s n) = destruct s >>= drop.aux n
| s, 0 => (bind_ret' _).symm
| s, n+1 =>
  by 
    rw [←dropn_tail, destruct_dropn _ n, destruct_tail, IsLawfulMonad.bind_assoc] <;> rfl

theorem head_terminates_of_head_tail_terminates (s : Wseq α) [T : terminates (head (tail s))] : terminates (head s) :=
  (head_terminates_iff _).2$
    by 
      rcases(head_terminates_iff _).1 T with ⟨⟨a, h⟩⟩
      simp [tail] at h 
      rcases exists_of_mem_bind h with ⟨s', h1, h2⟩
      unfold Functor.map  at h1 
      exact
        let ⟨t, h3, h4⟩ := exists_of_mem_map h1 
        terminates_of_mem h3

-- error in Data.Seq.Wseq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem destruct_some_of_destruct_tail_some
{s : wseq α}
{a}
(h : «expr ∈ »(some a, destruct (tail s))) : «expr∃ , »((a'), «expr ∈ »(some a', destruct s)) :=
begin
  unfold [ident tail, ident functor.map] ["at", ident h],
  simp [] [] [] [] [] ["at", ident h],
  rcases [expr exists_of_mem_bind h, "with", "⟨", ident t, ",", ident tm, ",", ident td, "⟩"],
  clear [ident h],
  rcases [expr exists_of_mem_map tm, "with", "⟨", ident t', ",", ident ht', ",", ident ht2, "⟩"],
  clear [ident tm],
  cases [expr t'] ["with", ident t']; rw ["<-", expr ht2] ["at", ident td]; simp [] [] [] [] [] ["at", ident td],
  { have [] [] [":=", expr mem_unique td (ret_mem _)],
    contradiction },
  { exact [expr ⟨_, ht'⟩] }
end

theorem head_some_of_head_tail_some {s : Wseq α} {a} (h : some a ∈ head (tail s)) : ∃ a', some a' ∈ head s :=
  by 
    unfold head  at h 
    rcases exists_of_mem_map h with ⟨o, md, e⟩
    clear h 
    cases' o with o <;> injection e with h' 
    clear e h' 
    cases' destruct_some_of_destruct_tail_some md with a am 
    exact ⟨_, mem_map ((· <$> ·) (@Prod.fst α (Wseq α))) am⟩

theorem head_some_of_nth_some {s : Wseq α} {a n} (h : some a ∈ nth s n) : ∃ a', some a' ∈ head s :=
  by 
    revert a 
    induction' n with n IH <;> intros 
    exacts[⟨_, h⟩,
      let ⟨a', h'⟩ := head_some_of_head_tail_some h 
      IH h']

instance productive_tail (s : Wseq α) [productive s] : productive (tail s) :=
  ⟨fun n =>
      by 
        rw [nth_tail] <;> infer_instance⟩

instance productive_dropn (s : Wseq α) [productive s] n : productive (drop s n) :=
  ⟨fun m =>
      by 
        rw [←nth_add] <;> infer_instance⟩

-- error in Data.Seq.Wseq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a productive weak sequence, we can collapse all the `think`s to
  produce a sequence. -/ def to_seq (s : wseq α) [productive s] : seq α :=
⟨λ n, (nth s n).get, λ n h, begin
   cases [expr e, ":", expr computation.get (nth s «expr + »(n, 1))] [],
   { assumption },
   have [] [] [":=", expr mem_of_get_eq _ e],
   simp [] [] [] ["[", expr nth, "]"] [] ["at", ident this, ident h],
   cases [expr head_some_of_head_tail_some this] ["with", ident a', ident h'],
   have [] [] [":=", expr mem_unique h' (@mem_of_get_eq _ _ _ _ h)],
   contradiction
 end⟩

theorem nth_terminates_le {s : Wseq α} {m n} (h : m ≤ n) : terminates (nth s n) → terminates (nth s m) :=
  by 
    induction' h with m' h IH <;> [exact id, exact fun T => IH (@head_terminates_of_head_tail_terminates _ _ T)]

theorem head_terminates_of_nth_terminates {s : Wseq α} {n} : terminates (nth s n) → terminates (head s) :=
  nth_terminates_le (Nat.zero_leₓ n)

theorem destruct_terminates_of_nth_terminates {s : Wseq α} {n} (T : terminates (nth s n)) : terminates (destruct s) :=
  (head_terminates_iff _).1$ head_terminates_of_nth_terminates T

theorem mem_rec_on {C : Wseq α → Prop} {a s} (M : a ∈ s) (h1 : ∀ b s', a = b ∨ C s' → C (cons b s'))
  (h2 : ∀ s, C s → C (think s)) : C s :=
  by 
    apply Seqₓₓ.mem_rec_on M 
    intro o s' h 
    cases' o with b
    ·
      apply h2 
      cases h
      ·
        contradiction
      ·
        assumption
    ·
      apply h1 
      apply Or.imp_left _ h 
      intro h 
      injection h

@[simp]
theorem mem_think (s : Wseq α) a : a ∈ think s ↔ a ∈ s :=
  by 
    cases' s with f al 
    change some (some a) ∈ some none :: f ↔ some (some a) ∈ f 
    constructor <;> intro h
    ·
      apply (Streamₓ.eq_or_mem_of_mem_cons h).resolve_left 
      intro 
      injections
    ·
      apply Streamₓ.mem_cons_of_mem _ h

-- error in Data.Seq.Wseq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_or_mem_iff_mem
{s : wseq α}
{a
 a'
 s'} : «expr ∈ »(some (a', s'), destruct s) → «expr ↔ »(«expr ∈ »(a, s), «expr ∨ »(«expr = »(a, a'), «expr ∈ »(a, s'))) :=
begin
  generalize [ident e] [":"] [expr «expr = »(destruct s, c)],
  intro [ident h],
  revert [ident s],
  apply [expr computation.mem_rec_on h _ (λ
    c
    IH, _)]; intro [ident s]; apply [expr s.cases_on _ (λ
    x
    s, _) (λ
    s, _)]; intros [ident m]; have [] [] [":=", expr congr_arg computation.destruct m]; simp [] [] [] [] [] ["at", ident this]; cases [expr this] ["with", ident i1, ident i2],
  { rw ["[", expr i1, ",", expr i2, "]"] [],
    cases [expr s'] ["with", ident f, ident al],
    unfold [ident cons, ident has_mem.mem, ident wseq.mem, ident seq.mem, ident seq.cons] [],
    simp [] [] [] [] [] [],
    have [ident h_a_eq_a'] [":", expr «expr ↔ »(«expr = »(a, a'), «expr = »(some (some a), some (some a')))] [],
    { simp [] [] [] [] [] [] },
    rw ["[", expr h_a_eq_a', "]"] [],
    refine [expr ⟨stream.eq_or_mem_of_mem_cons, λ o, _⟩],
    { cases [expr o] ["with", ident e, ident m],
      { rw [expr e] [],
        apply [expr stream.mem_cons] },
      { exact [expr stream.mem_cons_of_mem _ m] } } },
  { simp [] [] [] [] [] [],
    exact [expr IH this] }
end

@[simp]
theorem mem_cons_iff (s : Wseq α) b {a} : a ∈ cons b s ↔ a = b ∨ a ∈ s :=
  eq_or_mem_iff_mem$
    by 
      simp [ret_mem]

theorem mem_cons_of_mem {s : Wseq α} b {a} (h : a ∈ s) : a ∈ cons b s :=
  (mem_cons_iff _ _).2 (Or.inr h)

theorem mem_cons (s : Wseq α) a : a ∈ cons a s :=
  (mem_cons_iff _ _).2 (Or.inl rfl)

-- error in Data.Seq.Wseq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_of_mem_tail {s : wseq α} {a} : «expr ∈ »(a, tail s) → «expr ∈ »(a, s) :=
begin
  intro [ident h],
  have [] [] [":=", expr h],
  cases [expr h] ["with", ident n, ident e],
  revert [ident s],
  simp [] [] [] ["[", expr stream.nth, "]"] [] [],
  induction [expr n] [] ["with", ident n, ident IH] []; intro [ident s]; apply [expr s.cases_on _ (λ
    x s, _) (λ s, _)]; repeat { simp [] [] [] [] [] [] }; intros [ident m, ident e]; injections [],
  { exact [expr or.inr m] },
  { exact [expr or.inr m] },
  { apply [expr IH m],
    rw [expr e] [],
    cases [expr tail s] [],
    refl }
end

theorem mem_of_mem_dropn {s : Wseq α} {a} : ∀ {n}, a ∈ drop s n → a ∈ s
| 0, h => h
| n+1, h => @mem_of_mem_dropn n (mem_of_mem_tail h)

-- error in Data.Seq.Wseq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nth_mem {s : wseq α} {a n} : «expr ∈ »(some a, nth s n) → «expr ∈ »(a, s) :=
begin
  revert [ident s],
  induction [expr n] [] ["with", ident n, ident IH] []; intros [ident s, ident h],
  { rcases [expr exists_of_mem_map h, "with", "⟨", ident o, ",", ident h1, ",", ident h2, "⟩"],
    cases [expr o] ["with", ident o]; injection [expr h2] ["with", ident h'],
    cases [expr o] ["with", ident a', ident s'],
    exact [expr (eq_or_mem_iff_mem h1).2 (or.inl h'.symm)] },
  { have [] [] [":=", expr @IH (tail s)],
    rw [expr nth_tail] ["at", ident this],
    exact [expr mem_of_mem_tail (this h)] }
end

theorem exists_nth_of_mem {s : Wseq α} {a} (h : a ∈ s) : ∃ n, some a ∈ nth s n :=
  by 
    apply mem_rec_on h
    ·
      intro a' s' h 
      cases' h with h h
      ·
        exists 0
        simp [nth]
        rw [h]
        apply ret_mem
      ·
        cases' h with n h 
        exists n+1
        simp [nth]
        exact h
    ·
      intro s' h 
      cases' h with n h 
      exists n 
      simp [nth]
      apply think_mem h

-- error in Data.Seq.Wseq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_dropn_of_mem
{s : wseq α}
{a}
(h : «expr ∈ »(a, s)) : «expr∃ , »((n s'), «expr ∈ »(some (a, s'), destruct (drop s n))) :=
let ⟨n, h⟩ := exists_nth_of_mem h in
⟨n, begin
   rcases [expr (head_terminates_iff _).1 ⟨⟨_, h⟩⟩, "with", "⟨", "⟨", ident o, ",", ident om, "⟩", "⟩"],
   have [] [] [":=", expr mem_unique (mem_map _ om) h],
   cases [expr o] ["with", ident o]; injection [expr this] ["with", ident i],
   cases [expr o] ["with", ident a', ident s'],
   dsimp [] [] [] ["at", ident i],
   rw [expr i] ["at", ident om],
   exact [expr ⟨_, om⟩]
 end⟩

theorem lift_rel_dropn_destruct {R : α → β → Prop} {s t} (H : lift_rel R s t) :
  ∀ n, Computation.LiftRel (lift_rel_o R (lift_rel R)) (destruct (drop s n)) (destruct (drop t n))
| 0 => lift_rel_destruct H
| n+1 =>
  by 
    simp [destruct_tail]
    apply lift_rel_bind 
    apply lift_rel_dropn_destruct n 
    exact
      fun a b o =>
        match a, b, o with 
        | none, none, _ =>
          by 
            simp 
        | some (a, s), some (b, t), ⟨h1, h2⟩ =>
          by 
            simp [tail.aux] <;> apply lift_rel_destruct h2

theorem exists_of_lift_rel_left {R : α → β → Prop} {s t} (H : lift_rel R s t) {a} (h : a ∈ s) : ∃ b, b ∈ t ∧ R a b :=
  let ⟨n, h⟩ := exists_nth_of_mem h 
  let ⟨some (_, s'), sd, rfl⟩ := exists_of_mem_map h 
  let ⟨some (b, t'), td, ⟨ab, _⟩⟩ := (lift_rel_dropn_destruct H n).left sd
  ⟨b, nth_mem (mem_map ((· <$> ·) Prod.fst.{v, v}) td), ab⟩

theorem exists_of_lift_rel_right {R : α → β → Prop} {s t} (H : lift_rel R s t) {b} (h : b ∈ t) : ∃ a, a ∈ s ∧ R a b :=
  by 
    rw [←lift_rel.swap] at H <;> exact exists_of_lift_rel_left H h

theorem head_terminates_of_mem {s : Wseq α} {a} (h : a ∈ s) : terminates (head s) :=
  let ⟨n, h⟩ := exists_nth_of_mem h 
  head_terminates_of_nth_terminates ⟨⟨_, h⟩⟩

theorem of_mem_append {s₁ s₂ : Wseq α} {a : α} : a ∈ append s₁ s₂ → a ∈ s₁ ∨ a ∈ s₂ :=
  Seqₓₓ.of_mem_append

theorem mem_append_left {s₁ s₂ : Wseq α} {a : α} : a ∈ s₁ → a ∈ append s₁ s₂ :=
  Seqₓₓ.mem_append_left

theorem exists_of_mem_map {f} {b : β} : ∀ {s : Wseq α}, b ∈ map f s → ∃ a, a ∈ s ∧ f a = b
| ⟨g, al⟩, h =>
  let ⟨o, om, oe⟩ := Seqₓₓ.exists_of_mem_map h 
  by 
    cases' o with a <;> injection oe with h' <;> exact ⟨a, om, h'⟩

@[simp]
theorem lift_rel_nil (R : α → β → Prop) : lift_rel R nil nil :=
  by 
    rw [lift_rel_destruct_iff] <;> simp 

@[simp]
theorem lift_rel_cons (R : α → β → Prop) a b s t : lift_rel R (cons a s) (cons b t) ↔ R a b ∧ lift_rel R s t :=
  by 
    rw [lift_rel_destruct_iff] <;> simp 

@[simp]
theorem lift_rel_think_left (R : α → β → Prop) s t : lift_rel R (think s) t ↔ lift_rel R s t :=
  by 
    rw [lift_rel_destruct_iff, lift_rel_destruct_iff] <;> simp 

@[simp]
theorem lift_rel_think_right (R : α → β → Prop) s t : lift_rel R s (think t) ↔ lift_rel R s t :=
  by 
    rw [lift_rel_destruct_iff, lift_rel_destruct_iff] <;> simp 

theorem cons_congr {s t : Wseq α} (a : α) (h : s ~ t) : cons a s ~ cons a t :=
  by 
    unfold Equiv <;> simp  <;> exact h

theorem think_equiv (s : Wseq α) : think s ~ s :=
  by 
    unfold Equiv <;> simp  <;> apply Equiv.refl

theorem think_congr {s t : Wseq α} (a : α) (h : s ~ t) : think s ~ think t :=
  by 
    unfold Equiv <;> simp  <;> exact h

theorem head_congr : ∀ {s t : Wseq α}, s ~ t → head s ~ head t :=
  suffices ∀ {s t : Wseq α}, s ~ t → ∀ {o}, o ∈ head s → o ∈ head t from fun s t h o => ⟨this h, this h.symm⟩
  by 
    intro s t h o ho 
    rcases@Computation.exists_of_mem_map _ _ _ _ (destruct s) ho with ⟨ds, dsm, dse⟩
    rw [←dse]
    cases' destruct_congr h with l r 
    rcases l dsm with ⟨dt, dtm, dst⟩
    cases' ds with a <;> cases' dt with b
    ·
      apply mem_map _ dtm
    ·
      cases b 
      cases dst
    ·
      cases a 
      cases dst
    ·
      cases' a with a s' 
      cases' b with b t' 
      rw [dst.left]
      exact @mem_map _ _ (@Functor.map _ _ (α × Wseq α) _ Prod.fst) _ (destruct t) dtm

theorem flatten_equiv {c : Computation (Wseq α)} {s} (h : s ∈ c) : flatten c ~ s :=
  by 
    apply Computation.memRecOn h
    ·
      simp 
    ·
      intro s' 
      apply Equiv.trans 
      simp [think_equiv]

theorem lift_rel_flatten {R : α → β → Prop} {c1 : Computation (Wseq α)} {c2 : Computation (Wseq β)}
  (h : c1.lift_rel (lift_rel R) c2) : lift_rel R (flatten c1) (flatten c2) :=
  let S := fun s t => ∃ c1 c2, s = flatten c1 ∧ t = flatten c2 ∧ Computation.LiftRel (lift_rel R) c1 c2
  ⟨S, ⟨c1, c2, rfl, rfl, h⟩,
    fun s t h =>
      match s, t, h with 
      | _, _, ⟨c1, c2, rfl, rfl, h⟩ =>
        by 
          simp 
          apply lift_rel_bind _ _ h 
          intro a b ab 
          apply Computation.LiftRel.imp _ _ _ (lift_rel_destruct ab)
          intro a b 
          apply lift_rel_o.imp_right 
          intro s t h 
          refine' ⟨return s, return t, _, _, _⟩ <;> simp [h]⟩

theorem flatten_congr {c1 c2 : Computation (Wseq α)} : Computation.LiftRel Equiv c1 c2 → flatten c1 ~ flatten c2 :=
  lift_rel_flatten

theorem tail_congr {s t : Wseq α} (h : s ~ t) : tail s ~ tail t :=
  by 
    apply flatten_congr 
    unfold Functor.map 
    rw [←bind_ret, ←bind_ret]
    apply lift_rel_bind _ _ (destruct_congr h)
    intro a b h 
    simp 
    cases' a with a <;> cases' b with b
    ·
      trivial
    ·
      cases h
    ·
      cases a 
      cases h
    ·
      cases' a with a s' 
      cases' b with b t' 
      exact h.right

theorem dropn_congr {s t : Wseq α} (h : s ~ t) n : drop s n ~ drop t n :=
  by 
    induction n <;> simp [tail_congr]

theorem nth_congr {s t : Wseq α} (h : s ~ t) n : nth s n ~ nth t n :=
  head_congr (dropn_congr h _)

theorem mem_congr {s t : Wseq α} (h : s ~ t) a : a ∈ s ↔ a ∈ t :=
  suffices ∀ {s t : Wseq α}, s ~ t → a ∈ s → a ∈ t from ⟨this h, this h.symm⟩
  fun s t h as =>
    let ⟨n, hn⟩ := exists_nth_of_mem as 
    nth_mem ((nth_congr h _ _).1 hn)

theorem productive_congr {s t : Wseq α} (h : s ~ t) : productive s ↔ productive t :=
  by 
    simp only [productive_iff] <;> exact forall_congrₓ fun n => terminates_congr$ nth_congr h _

theorem Equiv.ext {s t : Wseq α} (h : ∀ n, nth s n ~ nth t n) : s ~ t :=
  ⟨fun s t => ∀ n, nth s n ~ nth t n, h,
    fun s t h =>
      by 
        refine' lift_rel_def.2 ⟨_, _⟩
        ·
          rw [←head_terminates_iff, ←head_terminates_iff]
          exact terminates_congr (h 0)
        ·
          intro a b ma mb 
          cases' a with a <;> cases' b with b
          ·
            trivial
          ·
            injection mem_unique (mem_map _ ma) ((h 0 _).2 (mem_map _ mb))
          ·
            injection mem_unique (mem_map _ ma) ((h 0 _).2 (mem_map _ mb))
          ·
            cases' a with a s' 
            cases' b with b t' 
            injection mem_unique (mem_map _ ma) ((h 0 _).2 (mem_map _ mb)) with ab 
            refine' ⟨ab, fun n => _⟩
            refine'
              (nth_congr (flatten_equiv (mem_map _ ma)) n).symm.trans
                ((_ : nth (tail s) n ~ nth (tail t) n).trans (nth_congr (flatten_equiv (mem_map _ mb)) n))
            rw [nth_tail, nth_tail]
            apply h⟩

theorem length_eq_map (s : Wseq α) : length s = Computation.map List.length (to_list s) :=
  by 
    refine'
      eq_of_bisim
        (fun c1 c2 =>
          ∃ (l : List α)(s : Wseq α),
            c1 = corec length._match_2 (l.length, s) ∧ c2 = Computation.map List.length (corec to_list._match_2 (l, s)))
        _ ⟨[], s, rfl, rfl⟩
    intro s1 s2 h 
    rcases h with ⟨l, s, h⟩
    rw [h.left, h.right]
    apply s.cases_on _ (fun a s => _) fun s => _ <;>
      repeat' 
        simp [to_list, nil, cons, think, length]
    ·
      refine' ⟨a :: l, s, _, _⟩ <;> simp 
    ·
      refine' ⟨l, s, _, _⟩ <;> simp 

@[simp]
theorem of_list_nil : of_list [] = (nil : Wseq α) :=
  rfl

@[simp]
theorem of_list_cons (a : α) l : of_list (a :: l) = cons a (of_list l) :=
  show Seqₓₓ.map some (Seqₓₓ.ofList (a :: l)) = Seqₓₓ.cons (some a) (Seqₓₓ.map some (Seqₓₓ.ofList l))by 
    simp 

@[simp]
theorem to_list'_nil (l : List α) : corec to_list._match_2 (l, nil) = return l.reverse :=
  destruct_eq_ret rfl

@[simp]
theorem to_list'_cons (l : List α) (s : Wseq α) (a : α) :
  corec to_list._match_2 (l, cons a s) = (corec to_list._match_2 (a :: l, s)).think :=
  destruct_eq_think$
    by 
      simp [to_list, cons]

@[simp]
theorem to_list'_think (l : List α) (s : Wseq α) :
  corec to_list._match_2 (l, think s) = (corec to_list._match_2 (l, s)).think :=
  destruct_eq_think$
    by 
      simp [to_list, think]

theorem to_list'_map (l : List α) (s : Wseq α) : corec to_list._match_2 (l, s) = (· ++ ·) l.reverse <$> to_list s :=
  by 
    refine'
      eq_of_bisim
        (fun c1 c2 =>
          ∃ (l' : List α)(s : Wseq α),
            c1 = corec to_list._match_2 (l' ++ l, s) ∧
              c2 = Computation.map ((· ++ ·) l.reverse) (corec to_list._match_2 (l', s)))
        _ ⟨[], s, rfl, rfl⟩
    intro s1 s2 h 
    rcases h with ⟨l', s, h⟩
    rw [h.left, h.right]
    apply s.cases_on _ (fun a s => _) fun s => _ <;>
      repeat' 
        simp [to_list, nil, cons, think, length]
    ·
      refine' ⟨a :: l', s, _, _⟩ <;> simp 
    ·
      refine' ⟨l', s, _, _⟩ <;> simp 

@[simp]
theorem to_list_cons (a : α) s : to_list (cons a s) = (List.cons a <$> to_list s).think :=
  destruct_eq_think$
    by 
      unfold to_list <;> simp  <;> rw [to_list'_map] <;> simp  <;> rfl

@[simp]
theorem to_list_nil : to_list (nil : Wseq α) = return [] :=
  destruct_eq_ret rfl

theorem to_list_of_list (l : List α) : l ∈ to_list (of_list l) :=
  by 
    induction' l with a l IH <;> simp [ret_mem] <;> exact think_mem (mem_map _ IH)

@[simp]
theorem destruct_of_seq (s : Seqₓₓ α) : destruct (of_seq s) = return (s.head.map$ fun a => (a, of_seq s.tail)) :=
  destruct_eq_ret$
    by 
      simp [of_seq, head, destruct, Seqₓₓ.destruct, Seqₓₓ.head]
      rw
        [show Seqₓₓ.nth (some <$> s) 0 = some <$> Seqₓₓ.nth s 0 by 
          apply Seqₓₓ.map_nth]
      cases' Seqₓₓ.nth s 0 with a
      ·
        rfl 
      unfold Functor.map 
      simp [destruct]

@[simp]
theorem head_of_seq (s : Seqₓₓ α) : head (of_seq s) = return s.head :=
  by 
    simp [head] <;> cases Seqₓₓ.head s <;> rfl

@[simp]
theorem tail_of_seq (s : Seqₓₓ α) : tail (of_seq s) = of_seq s.tail :=
  by 
    simp [tail]
    apply s.cases_on _ fun x s => _ <;> simp [of_seq]
    ·
      rfl 
    rw [Seqₓₓ.head_cons, Seqₓₓ.tail_cons]
    rfl

@[simp]
theorem dropn_of_seq (s : Seqₓₓ α) : ∀ n, drop (of_seq s) n = of_seq (s.drop n)
| 0 => rfl
| n+1 =>
  by 
    dsimp [drop] <;> rw [dropn_of_seq, tail_of_seq]

theorem nth_of_seq (s : Seqₓₓ α) n : nth (of_seq s) n = return (Seqₓₓ.nth s n) :=
  by 
    dsimp [nth] <;> rw [dropn_of_seq, head_of_seq, Seqₓₓ.head_dropn]

instance productive_of_seq (s : Seqₓₓ α) : productive (of_seq s) :=
  ⟨fun n =>
      by 
        rw [nth_of_seq] <;> infer_instance⟩

theorem to_seq_of_seq (s : Seqₓₓ α) : to_seq (of_seq s) = s :=
  by 
    apply Subtype.eq 
    funext n 
    dsimp [to_seq]
    apply get_eq_of_mem 
    rw [nth_of_seq]
    apply ret_mem

/-- The monadic `return a` is a singleton list containing `a`. -/
def ret (a : α) : Wseq α :=
  of_list [a]

@[simp]
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl

@[simp]
theorem map_cons (f : α → β) a s : map f (cons a s) = cons (f a) (map f s) :=
  Seqₓₓ.map_cons _ _ _

@[simp]
theorem map_think (f : α → β) s : map f (think s) = think (map f s) :=
  Seqₓₓ.map_cons _ _ _

@[simp]
theorem map_id (s : Wseq α) : map id s = s :=
  by 
    simp [map]

@[simp]
theorem map_ret (f : α → β) a : map f (ret a) = ret (f a) :=
  by 
    simp [ret]

@[simp]
theorem map_append (f : α → β) s t : map f (append s t) = append (map f s) (map f t) :=
  Seqₓₓ.map_append _ _ _

theorem map_comp (f : α → β) (g : β → γ) (s : Wseq α) : map (g ∘ f) s = map g (map f s) :=
  by 
    dsimp [map]
    rw [←Seqₓₓ.map_comp]
    apply congr_funₓ 
    apply congr_argₓ 
    ext ⟨⟩ <;> rfl

theorem mem_map (f : α → β) {a : α} {s : Wseq α} : a ∈ s → f a ∈ map f s :=
  Seqₓₓ.mem_map (Option.map f)

-- error in Data.Seq.Wseq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_of_mem_join
{a : α} : ∀ {S : wseq (wseq α)}, «expr ∈ »(a, join S) → «expr∃ , »((s), «expr ∧ »(«expr ∈ »(s, S), «expr ∈ »(a, s))) :=
suffices ∀
ss : wseq α, «expr ∈ »(a, ss) → ∀
s
S, «expr = »(append s (join S), ss) → «expr ∈ »(a, append s (join S)) → «expr ∨ »(«expr ∈ »(a, s), «expr∃ , »((s), «expr ∧ »(«expr ∈ »(s, S), «expr ∈ »(a, s)))), from λ
S
h, (this _ h nil S (by simp [] [] [] [] [] []) (by simp [] [] [] ["[", expr h, "]"] [] [])).resolve_left (not_mem_nil _),
begin
  intros [ident ss, ident h],
  apply [expr mem_rec_on h (λ b ss o, _) (λ ss IH, _)]; intros [ident s, ident S],
  { refine [expr s.cases_on (S.cases_on _ (λ
       s
       S, _) (λ
       S, _)) (λ
      b'
      s, _) (λ
      s, _)]; intros [ident ej, ident m]; simp [] [] [] [] [] ["at", ident ej]; have [] [] [":=", expr congr_arg seq.destruct ej]; simp [] [] [] [] [] ["at", ident this]; try { cases [expr this] [] }; try { contradiction },
    substs [ident b', ident ss],
    simp [] [] [] [] [] ["at", ident m, "⊢"],
    cases [expr o] ["with", ident e, ident IH],
    { simp [] [] [] ["[", expr e, "]"] [] [] },
    cases [expr m] ["with", ident e, ident m],
    { simp [] [] [] ["[", expr e, "]"] [] [] },
    exact [expr or.imp_left or.inr (IH _ _ rfl m)] },
  { refine [expr s.cases_on (S.cases_on _ (λ
       s
       S, _) (λ
       S, _)) (λ
      b'
      s, _) (λ
      s, _)]; intros [ident ej, ident m]; simp [] [] [] [] [] ["at", ident ej]; have [] [] [":=", expr congr_arg seq.destruct ej]; simp [] [] [] [] [] ["at", ident this]; try { try { have [] [] [":=", expr this.1] },
      contradiction }; subst [expr ss],
    { apply [expr or.inr],
      simp [] [] [] [] [] ["at", ident m, "⊢"],
      cases [expr IH s S rfl m] ["with", ident as, ident ex],
      { exact [expr ⟨s, or.inl rfl, as⟩] },
      { rcases [expr ex, "with", "⟨", ident s', ",", ident sS, ",", ident as, "⟩"],
        exact [expr ⟨s', or.inr sS, as⟩] } },
    { apply [expr or.inr],
      simp [] [] [] [] [] ["at", ident m],
      rcases [expr (IH nil S (by simp [] [] [] [] [] []) (by simp [] [] [] ["[", expr m, "]"] [] [])).resolve_left (not_mem_nil _), "with", "⟨", ident s, ",", ident sS, ",", ident as, "⟩"],
      exact [expr ⟨s, by simp [] [] [] ["[", expr sS, "]"] [] [], as⟩] },
    { simp [] [] [] [] [] ["at", ident m, ident IH, "⊢"],
      apply [expr IH _ _ rfl m] } }
end

theorem exists_of_mem_bind {s : Wseq α} {f : α → Wseq β} {b} (h : b ∈ bind s f) : ∃ (a : _)(_ : a ∈ s), b ∈ f a :=
  let ⟨t, tm, bt⟩ := exists_of_mem_join h 
  let ⟨a, as, e⟩ := exists_of_mem_map tm
  ⟨a, as,
    by 
      rwa [e]⟩

theorem destruct_map (f : α → β) (s : Wseq α) :
  destruct (map f s) = Computation.map (Option.map (Prod.mapₓ f (map f))) (destruct s) :=
  by 
    apply
      eq_of_bisim
        fun c1 c2 => ∃ s, c1 = destruct (map f s) ∧ c2 = Computation.map (Option.map (Prod.mapₓ f (map f))) (destruct s)
    ·
      intro c1 c2 h 
      cases' h with s h 
      rw [h.left, h.right]
      apply s.cases_on _ (fun a s => _) fun s => _ <;> simp 
      exact ⟨s, rfl, rfl⟩
    ·
      exact ⟨s, rfl, rfl⟩

theorem lift_rel_map {δ} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : Wseq α} {s2 : Wseq β} {f1 : α → γ} {f2 : β → δ}
  (h1 : lift_rel R s1 s2) (h2 : ∀ {a b}, R a b → S (f1 a) (f2 b)) : lift_rel S (map f1 s1) (map f2 s2) :=
  ⟨fun s1 s2 => ∃ s t, s1 = map f1 s ∧ s2 = map f2 t ∧ lift_rel R s t, ⟨s1, s2, rfl, rfl, h1⟩,
    fun s1 s2 h =>
      match s1, s2, h with 
      | _, _, ⟨s, t, rfl, rfl, h⟩ =>
        by 
          simp [destruct_map]
          apply Computation.lift_rel_map _ _ (lift_rel_destruct h)
          intro o p h 
          cases' o with a <;> cases' p with b <;> simp 
          ·
            cases b <;> cases h
          ·
            cases a <;> cases h
          ·
            cases' a with a s <;> cases' b with b t 
            cases' h with r h 
            exact ⟨h2 r, s, rfl, t, rfl, h⟩⟩

theorem map_congr (f : α → β) {s t : Wseq α} (h : s ~ t) : map f s ~ map f t :=
  lift_rel_map _ _ h fun _ _ => congr_argₓ _

@[simp]
def destruct_append.aux (t : Wseq α) : Option (α × Wseq α) → Computation (Option (α × Wseq α))
| none => destruct t
| some (a, s) => return (some (a, append s t))

theorem destruct_append (s t : Wseq α) : destruct (append s t) = (destruct s).bind (destruct_append.aux t) :=
  by 
    apply
      eq_of_bisim (fun c1 c2 => ∃ s t, c1 = destruct (append s t) ∧ c2 = (destruct s).bind (destruct_append.aux t)) _
        ⟨s, t, rfl, rfl⟩
    intro c1 c2 h 
    rcases h with ⟨s, t, h⟩
    rw [h.left, h.right]
    apply s.cases_on _ (fun a s => _) fun s => _ <;> simp 
    ·
      apply t.cases_on _ (fun b t => _) fun t => _ <;> simp 
      ·
        refine' ⟨nil, t, _, _⟩ <;> simp 
    ·
      exact ⟨s, t, rfl, rfl⟩

@[simp]
def destruct_join.aux : Option (Wseq α × Wseq (Wseq α)) → Computation (Option (α × Wseq α))
| none => return none
| some (s, S) => (destruct (append s (join S))).think

theorem destruct_join (S : Wseq (Wseq α)) : destruct (join S) = (destruct S).bind destruct_join.aux :=
  by 
    apply
      eq_of_bisim (fun c1 c2 => c1 = c2 ∨ ∃ S, c1 = destruct (join S) ∧ c2 = (destruct S).bind destruct_join.aux) _
        (Or.inr ⟨S, rfl, rfl⟩)
    intro c1 c2 h 
    exact
      match c1, c2, h with 
      | _, _, Or.inl$ Eq.refl c =>
        by 
          cases c.destruct <;> simp 
      | _, _, Or.inr ⟨S, rfl, rfl⟩ =>
        by 
          apply S.cases_on _ (fun s S => _) fun S => _ <;> simp 
          ·
            refine' Or.inr ⟨S, rfl, rfl⟩

theorem lift_rel_append (R : α → β → Prop) {s1 s2 : Wseq α} {t1 t2 : Wseq β} (h1 : lift_rel R s1 t1)
  (h2 : lift_rel R s2 t2) : lift_rel R (append s1 s2) (append t1 t2) :=
  ⟨fun s t => lift_rel R s t ∨ ∃ s1 t1, s = append s1 s2 ∧ t = append t1 t2 ∧ lift_rel R s1 t1,
    Or.inr ⟨s1, t1, rfl, rfl, h1⟩,
    fun s t h =>
      match s, t, h with 
      | s, t, Or.inl h =>
        by 
          apply Computation.LiftRel.imp _ _ _ (lift_rel_destruct h)
          intro a b 
          apply lift_rel_o.imp_right 
          intro s t 
          apply Or.inl
      | _, _, Or.inr ⟨s1, t1, rfl, rfl, h⟩ =>
        by 
          simp [destruct_append]
          apply Computation.lift_rel_bind _ _ (lift_rel_destruct h)
          intro o p h 
          cases' o with a <;> cases' p with b
          ·
            simp 
            apply Computation.LiftRel.imp _ _ _ (lift_rel_destruct h2)
            intro a b 
            apply lift_rel_o.imp_right 
            intro s t 
            apply Or.inl
          ·
            cases b <;> cases h
          ·
            cases a <;> cases h
          ·
            cases' a with a s <;> cases' b with b t 
            cases' h with r h 
            simp 
            exact ⟨r, Or.inr ⟨s, rfl, t, rfl, h⟩⟩⟩

theorem lift_rel_join.lem (R : α → β → Prop) {S T} {U : Wseq α → Wseq β → Prop} (ST : lift_rel (lift_rel R) S T)
  (HU :
    ∀ s1 s2,
      (∃ s t S T, s1 = append s (join S) ∧ s2 = append t (join T) ∧ lift_rel R s t ∧ lift_rel (lift_rel R) S T) →
        U s1 s2)
  {a} (ma : a ∈ destruct (join S)) : ∃ b, b ∈ destruct (join T) ∧ lift_rel_o R U a b :=
  by 
    cases' exists_results_of_mem ma with n h 
    clear ma 
    revert a S T 
    apply Nat.strong_induction_onₓ n _ 
    intro n IH a S T ST ra 
    simp [destruct_join] at ra 
    exact
      let ⟨o, m, k, rs1, rs2, en⟩ := of_results_bind ra 
      let ⟨p, mT, rop⟩ := Computation.exists_of_lift_rel_left (lift_rel_destruct ST) rs1.mem 
      by 
        exact
          match o, p, rop, rs1, rs2, mT with 
          | none, none, _, rs1, rs2, mT =>
            by 
              simp only [destruct_join] <;>
                exact
                  ⟨none, mem_bind mT (ret_mem _),
                    by 
                      rw [eq_of_ret_mem rs2.mem] <;> trivial⟩
          | some (s, S'), some (t, T'), ⟨st, ST'⟩, rs1, rs2, mT =>
            by 
              simp [destruct_append] at rs2 <;>
                exact
                  let ⟨k1, rs3, ek⟩ := of_results_think rs2 
                  let ⟨o', m1, n1, rs4, rs5, ek1⟩ := of_results_bind rs3 
                  let ⟨p', mt, rop'⟩ := Computation.exists_of_lift_rel_left (lift_rel_destruct st) rs4.mem 
                  by 
                    exact
                      match o', p', rop', rs4, rs5, mt with 
                      | none, none, _, rs4, rs5', mt =>
                        have  : n1 < n :=
                          by 
                            rw [en, ek, ek1]
                            apply lt_of_lt_of_leₓ _ (Nat.le_add_rightₓ _ _)
                            apply Nat.lt_succ_of_leₓ (Nat.le_add_rightₓ _ _)
                        let ⟨ob, mb, rob⟩ := IH _ this ST' rs5' 
                        by 
                          refine' ⟨ob, _, rob⟩ <;>
                            ·
                              simp [destruct_join]
                              apply mem_bind mT 
                              simp [destruct_append]
                              apply think_mem 
                              apply mem_bind mt 
                              exact mb
                      | some (a, s'), some (b, t'), ⟨ab, st'⟩, rs4, rs5, mt =>
                        by 
                          simp  at rs5 
                          refine' ⟨some (b, append t' (join T')), _, _⟩
                          ·
                            simp [destruct_join]
                            apply mem_bind mT 
                            simp [destruct_append]
                            apply think_mem 
                            apply mem_bind mt 
                            apply ret_mem 
                          rw [eq_of_ret_mem rs5.mem]
                          exact ⟨ab, HU _ _ ⟨s', t', S', T', rfl, rfl, st', ST'⟩⟩

theorem lift_rel_join (R : α → β → Prop) {S : Wseq (Wseq α)} {T : Wseq (Wseq β)} (h : lift_rel (lift_rel R) S T) :
  lift_rel R (join S) (join T) :=
  ⟨fun s1 s2 => ∃ s t S T, s1 = append s (join S) ∧ s2 = append t (join T) ∧ lift_rel R s t ∧ lift_rel (lift_rel R) S T,
    ⟨nil, nil, S, T,
      by 
        simp ,
      by 
        simp ,
      by 
        simp ,
      h⟩,
    fun s1 s2 ⟨s, t, S, T, h1, h2, st, ST⟩ =>
      by 
        clear _fun_match _x 
        rw [h1, h2]
        rw [destruct_append, destruct_append]
        apply Computation.lift_rel_bind _ _ (lift_rel_destruct st)
        exact
          fun o p h =>
            match o, p, h with 
            | some (a, s), some (b, t), ⟨h1, h2⟩ =>
              by 
                simp  <;> exact ⟨h1, s, t, S, rfl, T, rfl, h2, ST⟩
            | none, none, _ =>
              by 
                dsimp [destruct_append.aux, Computation.LiftRel]
                constructor
                ·
                  intro 
                  apply lift_rel_join.lem _ ST fun _ _ => id
                ·
                  intro b mb 
                  rw [←lift_rel_o.swap]
                  apply lift_rel_join.lem (swap R)
                  ·
                    rw [←lift_rel.swap R, ←lift_rel.swap]
                    apply ST
                  ·
                    rw [←lift_rel.swap R, ←lift_rel.swap (lift_rel R)]
                    exact fun s1 s2 ⟨s, t, S, T, h1, h2, st, ST⟩ => ⟨t, s, T, S, h2, h1, st, ST⟩
                  ·
                    exact mb⟩

theorem join_congr {S T : Wseq (Wseq α)} (h : lift_rel Equiv S T) : join S ~ join T :=
  lift_rel_join _ h

theorem lift_rel_bind {δ} (R : α → β → Prop) (S : γ → δ → Prop) {s1 : Wseq α} {s2 : Wseq β} {f1 : α → Wseq γ}
  {f2 : β → Wseq δ} (h1 : lift_rel R s1 s2) (h2 : ∀ {a b}, R a b → lift_rel S (f1 a) (f2 b)) :
  lift_rel S (bind s1 f1) (bind s2 f2) :=
  lift_rel_join _ (lift_rel_map _ _ h1 @h2)

theorem bind_congr {s1 s2 : Wseq α} {f1 f2 : α → Wseq β} (h1 : s1 ~ s2) (h2 : ∀ a, f1 a ~ f2 a) :
  bind s1 f1 ~ bind s2 f2 :=
  lift_rel_bind _ _ h1
    fun a b h =>
      by 
        rw [h] <;> apply h2

@[simp]
theorem join_ret (s : Wseq α) : join (ret s) ~ s :=
  by 
    simp [ret] <;> apply think_equiv

-- error in Data.Seq.Wseq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem join_map_ret (s : wseq α) : [«expr ~ »/«expr ~ »](join (map ret s), s) :=
begin
  refine [expr ⟨λ s1 s2, «expr = »(join (map ret s2), s1), rfl, _⟩],
  intros [ident s', ident s, ident h],
  rw ["<-", expr h] [],
  apply [expr lift_rel_rec (λ
    c1 c2, «expr∃ , »((s), «expr ∧ »(«expr = »(c1, destruct (join (map ret s))), «expr = »(c2, destruct s))))],
  { exact [expr λ c1 c2 h, match c1, c2, h with
     | ._, ._, ⟨s, rfl, rfl⟩ := begin
       clear [ident h, ident _match],
       have [] [":", expr ∀
        s, «expr∃ , »((s' : wseq α), «expr ∧ »(«expr = »((map ret s).join.destruct, (map ret s').join.destruct), «expr = »(destruct s, s'.destruct)))] [],
       from [expr λ s, ⟨s, rfl, rfl⟩],
       apply [expr s.cases_on _ (λ
         a
         s, _) (λ
         s, _)]; simp [] [] [] ["[", expr ret, ",", expr ret_mem, ",", expr this, ",", expr option.exists, "]"] [] []
     end
     end] },
  { exact [expr ⟨s, rfl, rfl⟩] }
end

@[simp]
theorem join_append (S T : Wseq (Wseq α)) : join (append S T) ~ append (join S) (join T) :=
  by 
    refine'
      ⟨fun s1 s2 => ∃ s S T, s1 = append s (join (append S T)) ∧ s2 = append s (append (join S) (join T)),
        ⟨nil, S, T,
          by 
            simp ,
          by 
            simp ⟩,
        _⟩
    intro s1 s2 h 
    apply
      lift_rel_rec
        (fun c1 c2 =>
          ∃ (s : Wseq α)(S T : _),
            c1 = destruct (append s (join (append S T))) ∧ c2 = destruct (append s (append (join S) (join T))))
        _ _ _
        (let ⟨s, S, T, h1, h2⟩ := h
        ⟨s, S, T, congr_argₓ destruct h1, congr_argₓ destruct h2⟩)
    intro c1 c2 h 
    exact
      match c1, c2, h with 
      | _, _, ⟨s, S, T, rfl, rfl⟩ =>
        by 
          clear _match h h 
          apply Wseq.casesOn s _ (fun a s => _) fun s => _ <;> simp 
          ·
            apply Wseq.casesOn S _ (fun s S => _) fun S => _ <;> simp 
            ·
              apply Wseq.casesOn T _ (fun s T => _) fun T => _ <;> simp 
              ·
                refine' ⟨s, nil, T, _, _⟩ <;> simp 
              ·
                refine' ⟨nil, nil, T, _, _⟩ <;> simp 
            ·
              exact ⟨s, S, T, rfl, rfl⟩
            ·
              refine' ⟨nil, S, T, _, _⟩ <;> simp 
          ·
            exact ⟨s, S, T, rfl, rfl⟩
          ·
            exact ⟨s, S, T, rfl, rfl⟩

@[simp]
theorem bind_ret (f : α → β) s : bind s (ret ∘ f) ~ map f s :=
  by 
    dsimp [bind]
    change fun x => ret (f x) with ret ∘ f 
    rw [map_comp]
    apply join_map_ret

@[simp]
theorem ret_bind (a : α) (f : α → Wseq β) : bind (ret a) f ~ f a :=
  by 
    simp [bind]

@[simp]
theorem map_join (f : α → β) S : map f (join S) = join (map (map f) S) :=
  by 
    apply Seqₓₓ.eq_of_bisim fun s1 s2 => ∃ s S, s1 = append s (map f (join S)) ∧ s2 = append s (join (map (map f) S))
    ·
      intro s1 s2 h 
      exact
        match s1, s2, h with 
        | _, _, ⟨s, S, rfl, rfl⟩ =>
          by 
            apply Wseq.casesOn s _ (fun a s => _) fun s => _ <;> simp 
            ·
              apply Wseq.casesOn S _ (fun s S => _) fun S => _ <;> simp 
              ·
                exact ⟨map f s, S, rfl, rfl⟩
              ·
                refine' ⟨nil, S, _, _⟩ <;> simp 
            ·
              exact ⟨_, _, rfl, rfl⟩
            ·
              exact ⟨_, _, rfl, rfl⟩
    ·
      refine' ⟨nil, S, _, _⟩ <;> simp 

@[simp]
theorem join_join (SS : Wseq (Wseq (Wseq α))) : join (join SS) ~ join (map join SS) :=
  by 
    refine'
      ⟨fun s1 s2 =>
          ∃ s S SS, s1 = append s (join (append S (join SS))) ∧ s2 = append s (append (join S) (join (map join SS))),
        ⟨nil, nil, SS,
          by 
            simp ,
          by 
            simp ⟩,
        _⟩
    intro s1 s2 h 
    apply
      lift_rel_rec
        (fun c1 c2 =>
          ∃ s S SS,
            c1 = destruct (append s (join (append S (join SS)))) ∧
              c2 = destruct (append s (append (join S) (join (map join SS)))))
        _ (destruct s1) (destruct s2)
        (let ⟨s, S, SS, h1, h2⟩ := h
        ⟨s, S, SS,
          by 
            simp [h1],
          by 
            simp [h2]⟩)
    intro c1 c2 h 
    exact
      match c1, c2, h with 
      | _, _, ⟨s, S, SS, rfl, rfl⟩ =>
        by 
          clear _match h h 
          apply Wseq.casesOn s _ (fun a s => _) fun s => _ <;> simp 
          ·
            apply Wseq.casesOn S _ (fun s S => _) fun S => _ <;> simp 
            ·
              apply Wseq.casesOn SS _ (fun S SS => _) fun SS => _ <;> simp 
              ·
                refine' ⟨nil, S, SS, _, _⟩ <;> simp 
              ·
                refine' ⟨nil, nil, SS, _, _⟩ <;> simp 
            ·
              exact ⟨s, S, SS, rfl, rfl⟩
            ·
              refine' ⟨nil, S, SS, _, _⟩ <;> simp 
          ·
            exact ⟨s, S, SS, rfl, rfl⟩
          ·
            exact ⟨s, S, SS, rfl, rfl⟩

-- error in Data.Seq.Wseq: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp]
theorem bind_assoc
(s : wseq α)
(f : α → wseq β)
(g : β → wseq γ) : [«expr ~ »/«expr ~ »](bind (bind s f) g, bind s (λ x : α, bind (f x) g)) :=
begin
  simp [] [] [] ["[", expr bind, "]"] [] [],
  rw ["[", "<-", expr map_comp f (map g), ",", expr map_comp «expr ∘ »(map g, f) join, "]"] [],
  apply [expr join_join]
end

instance  : Monadₓ Wseq :=
  { map := @map, pure := @ret, bind := @bind }

end Wseq

