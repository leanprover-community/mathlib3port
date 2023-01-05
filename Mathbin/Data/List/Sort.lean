/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

! This file was ported from Lean 3 source module data.list.sort
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.OfFn
import Mathbin.Data.List.Perm

/-!
# Sorting algorithms on lists

In this file we define `list.sorted r l` to be an alias for `pairwise r l`. This alias is preferred
in the case that `r` is a `<` or `≤`-like relation. Then we define two sorting algorithms:
`list.insertion_sort` and `list.merge_sort`, and prove their correctness.
-/


open List.Perm

universe uu

namespace List

/-!
### The predicate `list.sorted`
-/


section Sorted

variable {α : Type uu} {r : α → α → Prop} {a : α} {l : List α}

/-- `sorted r l` is the same as `pairwise r l`, preferred in the case that `r`
  is a `<` or `≤`-like relation (transitive and antisymmetric or asymmetric) -/
def Sorted :=
  @Pairwise
#align list.sorted List.Sorted

instance decidableSorted [DecidableRel r] (l : List α) : Decidable (Sorted r l) :=
  List.instDecidablePairwise _
#align list.decidable_sorted List.decidableSorted

@[simp]
theorem sorted_nil : Sorted r [] :=
  pairwise.nil
#align list.sorted_nil List.sorted_nil

theorem Sorted.of_cons : Sorted r (a :: l) → Sorted r l :=
  pairwise.of_cons
#align list.sorted.of_cons List.Sorted.of_cons

theorem Sorted.tail {r : α → α → Prop} {l : List α} (h : Sorted r l) : Sorted r l.tail :=
  h.tail
#align list.sorted.tail List.Sorted.tail

theorem rel_of_sorted_cons {a : α} {l : List α} : Sorted r (a :: l) → ∀ b ∈ l, r a b :=
  rel_of_pairwise_cons
#align list.rel_of_sorted_cons List.rel_of_sorted_cons

@[simp]
theorem sorted_cons {a : α} {l : List α} : Sorted r (a :: l) ↔ (∀ b ∈ l, r a b) ∧ Sorted r l :=
  pairwise_cons
#align list.sorted_cons List.sorted_cons

protected theorem Sorted.nodup {r : α → α → Prop} [IsIrrefl α r] {l : List α} (h : Sorted r l) :
    Nodup l :=
  h.Nodup
#align list.sorted.nodup List.Sorted.nodup

theorem eq_of_perm_of_sorted [IsAntisymm α r] {l₁ l₂ : List α} (p : l₁ ~ l₂) (s₁ : Sorted r l₁)
    (s₂ : Sorted r l₂) : l₁ = l₂ :=
  by
  induction' s₁ with a l₁ h₁ s₁ IH generalizing l₂
  · exact p.nil_eq
  · have : a ∈ l₂ := p.subset (mem_cons_self _ _)
    rcases mem_split this with ⟨u₂, v₂, rfl⟩
    have p' := (perm_cons a).1 (p.trans perm_middle)
    obtain rfl := IH p' (s₂.sublist <| by simp)
    change a :: u₂ ++ v₂ = u₂ ++ ([a] ++ v₂)
    rw [← append_assoc]
    congr
    have : ∀ (x : α) (h : x ∈ u₂), x = a := fun x m =>
      antisymm ((pairwise_append.1 s₂).2.2 _ m a (mem_cons_self _ _)) (h₁ _ (by simp [m]))
    rw [(@eq_repeat _ a (length u₂ + 1) (a :: u₂)).2,
          (@eq_repeat _ a (length u₂ + 1) (u₂ ++ [a])).2] <;>
        constructor <;>
      simp [iff_true_intro this, or_comm']
#align list.eq_of_perm_of_sorted List.eq_of_perm_of_sorted

theorem sublist_of_subperm_of_sorted [IsAntisymm α r] {l₁ l₂ : List α} (p : l₁ <+~ l₂)
    (s₁ : l₁.Sorted r) (s₂ : l₂.Sorted r) : l₁ <+ l₂ :=
  by
  let ⟨_, h, h'⟩ := p
  rwa [← eq_of_perm_of_sorted h (s₂.sublist h') s₁]
#align list.sublist_of_subperm_of_sorted List.sublist_of_subperm_of_sorted

@[simp]
theorem sorted_singleton (a : α) : Sorted r [a] :=
  pairwise_singleton _ _
#align list.sorted_singleton List.sorted_singleton

theorem Sorted.rel_nth_le_of_lt {l : List α} (h : l.Sorted r) {a b : ℕ} (ha : a < l.length)
    (hb : b < l.length) (hab : a < b) : r (l.nthLe a ha) (l.nthLe b hb) :=
  List.pairwise_iff_nth_le.1 h a b hb hab
#align list.sorted.rel_nth_le_of_lt List.Sorted.rel_nth_le_of_lt

theorem Sorted.rel_nth_le_of_le [IsRefl α r] {l : List α} (h : l.Sorted r) {a b : ℕ}
    (ha : a < l.length) (hb : b < l.length) (hab : a ≤ b) : r (l.nthLe a ha) (l.nthLe b hb) :=
  by
  cases' eq_or_lt_of_le hab with H H
  · subst H
    exact refl _
  · exact h.rel_nth_le_of_lt _ _ H
#align list.sorted.rel_nth_le_of_le List.Sorted.rel_nth_le_of_le

theorem Sorted.rel_of_mem_take_of_mem_drop {l : List α} (h : List.Sorted r l) {k : ℕ} {x y : α}
    (hx : x ∈ List.take k l) (hy : y ∈ List.drop k l) : r x y :=
  by
  obtain ⟨iy, hiy, rfl⟩ := nth_le_of_mem hy
  obtain ⟨ix, hix, rfl⟩ := nth_le_of_mem hx
  rw [nth_le_take', nth_le_drop']
  rw [length_take] at hix
  exact h.rel_nth_le_of_lt _ _ (ix.lt_add_right _ _ (lt_min_iff.mp hix).left)
#align list.sorted.rel_of_mem_take_of_mem_drop List.Sorted.rel_of_mem_take_of_mem_drop

end Sorted

section Monotone

variable {n : ℕ} {α : Type uu} [Preorder α] {f : Fin n → α}

/-- A tuple is monotone if and only if the list obtained from it is sorted. -/
theorem monotone_iff_of_fn_sorted : Monotone f ↔ (ofFn f).Sorted (· ≤ ·) :=
  by
  simp_rw [sorted, pairwise_iff_nth_le, length_of_fn, nth_le_of_fn', monotone_iff_forall_lt]
  exact ⟨fun h i j hj hij => h <| fin.mk_lt_mk.mpr hij, fun h ⟨i, _⟩ ⟨j, hj⟩ hij => h i j hj hij⟩
#align list.monotone_iff_of_fn_sorted List.monotone_iff_of_fn_sorted

/-- The list obtained from a monotone tuple is sorted. -/
theorem Monotone.of_fn_sorted (h : Monotone f) : (ofFn f).Sorted (· ≤ ·) :=
  monotone_iff_of_fn_sorted.1 h
#align list.monotone.of_fn_sorted List.Monotone.of_fn_sorted

end Monotone

section Sort

variable {α : Type uu} (r : α → α → Prop) [DecidableRel r]

-- mathport name: «expr ≼ »
local infixl:50 " ≼ " => r

/-! ### Insertion sort -/


section InsertionSort

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`ordered_insert a l` inserts `a` into `l` at such that\n  `ordered_insert a l` is sorted if `l` is. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `orderedInsert [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`a] [":" `α] [] ")")]
       [(Term.typeSpec ":" (Term.arrow (Term.app `List [`α]) "→" (Term.app `List [`α])))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[(«term[_]» "[" [] "]")]] "=>" («term[_]» "[" [`a] "]"))
          (Term.matchAlt
           "|"
           [[(«term_::_» `b "::" `l)]]
           "=>"
           (termIfThenElse
            "if"
            (List.Data.List.Sort.«term_≼_» `a " ≼ " `b)
            "then"
            («term_::_» `a "::" («term_::_» `b "::" `l))
            "else"
            («term_::_» `b "::" (Term.app `ordered_insert [`l]))))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termIfThenElse
       "if"
       (List.Data.List.Sort.«term_≼_» `a " ≼ " `b)
       "then"
       («term_::_» `a "::" («term_::_» `b "::" `l))
       "else"
       («term_::_» `b "::" (Term.app `ordered_insert [`l])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `b "::" (Term.app `ordered_insert [`l]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ordered_insert [`l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ordered_insert
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `a "::" («term_::_» `b "::" `l))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `b "::" `l)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 67 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Sort.«term_≼_» `a " ≼ " `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Sort.«term_≼_»', expected 'List.Data.List.Sort.term_≼_._@.Data.List.Sort._hyg.14'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      `ordered_insert a l` inserts `a` into `l` at such that
        `ordered_insert a l` is sorted if `l` is. -/
    @[ simp ]
  def
    orderedInsert
    ( a : α ) : List α → List α
    | [ ] => [ a ] | b :: l => if a ≼ b then a :: b :: l else b :: ordered_insert l
#align list.ordered_insert List.orderedInsert

/-- `insertion_sort l` returns `l` sorted using the insertion sort algorithm. -/
@[simp]
def insertionSort : List α → List α
  | [] => []
  | b :: l => orderedInsert r b (insertion_sort l)
#align list.insertion_sort List.insertionSort

@[simp]
theorem ordered_insert_nil (a : α) : [].orderedInsert r a = [a] :=
  rfl
#align list.ordered_insert_nil List.ordered_insert_nil

theorem ordered_insert_length : ∀ (L : List α) (a : α), (L.orderedInsert r a).length = L.length + 1
  | [], a => rfl
  | hd :: tl, a => by
    dsimp [ordered_insert]
    split_ifs <;> simp [ordered_insert_length]
#align list.ordered_insert_length List.ordered_insert_length

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "An alternative definition of `ordered_insert` using `take_while` and `drop_while`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `ordered_insert_eq_take_drop [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `α] [] ")")]
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [`l]
         [(Term.typeSpec ":" (Term.app `List [`α]))]
         ","
         («term_=_»
          (Term.app (Term.proj `l "." `orderedInsert) [`r `a])
          "="
          («term_++_»
           (Term.app
            (Term.proj `l "." `takeWhile)
            [(Term.fun
              "fun"
              (Term.basicFun
               [`b]
               []
               "=>"
               («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))])
           "++"
           («term_::_»
            `a
            "::"
            (Term.app
             (Term.proj `l "." `dropWhile)
             [(Term.fun
               "fun"
               (Term.basicFun
                [`b]
                []
                "=>"
                («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))])))))))
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[(«term[_]» "[" [] "]")]] "=>" `rfl)
          (Term.matchAlt
           "|"
           [[(«term_::_» `b "::" `l)]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.dsimp
                "dsimp"
                []
                []
                ["only"]
                ["[" [(Tactic.simpLemma [] [] `ordered_insert)] "]"]
                [])
               []
               (Tactic.«tactic_<;>_»
                (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                "<;>"
                (Tactic.simp
                 "simp"
                 []
                 []
                 []
                 ["["
                  [(Tactic.simpLemma [] [] `take_while)
                   ","
                   (Tactic.simpLemma [] [] `drop_while)
                   ","
                   (Tactic.simpStar "*")]
                  "]"]
                 []))]))))])
        []))
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.dsimp
           "dsimp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `ordered_insert)] "]"]
           [])
          []
          (Tactic.«tactic_<;>_»
           (Mathlib.Tactic.splitIfs "split_ifs" [] [])
           "<;>"
           (Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma [] [] `take_while)
              ","
              (Tactic.simpLemma [] [] `drop_while)
              ","
              (Tactic.simpStar "*")]
             "]"]
            []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Mathlib.Tactic.splitIfs "split_ifs" [] [])
       "<;>"
       (Tactic.simp
        "simp"
        []
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `take_while)
          ","
          (Tactic.simpLemma [] [] `drop_while)
          ","
          (Tactic.simpStar "*")]
         "]"]
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `take_while)
         ","
         (Tactic.simpLemma [] [] `drop_while)
         ","
         (Tactic.simpStar "*")]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `drop_while
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `take_while
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Mathlib.Tactic.splitIfs "split_ifs" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `ordered_insert)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ordered_insert
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `b "::" `l)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [`l]
       [(Term.typeSpec ":" (Term.app `List [`α]))]
       ","
       («term_=_»
        (Term.app (Term.proj `l "." `orderedInsert) [`r `a])
        "="
        («term_++_»
         (Term.app
          (Term.proj `l "." `takeWhile)
          [(Term.fun
            "fun"
            (Term.basicFun
             [`b]
             []
             "=>"
             («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))])
         "++"
         («term_::_»
          `a
          "::"
          (Term.app
           (Term.proj `l "." `dropWhile)
           [(Term.fun
             "fun"
             (Term.basicFun
              [`b]
              []
              "=>"
              («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app (Term.proj `l "." `orderedInsert) [`r `a])
       "="
       («term_++_»
        (Term.app
         (Term.proj `l "." `takeWhile)
         [(Term.fun
           "fun"
           (Term.basicFun
            [`b]
            []
            "=>"
            («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))])
        "++"
        («term_::_»
         `a
         "::"
         (Term.app
          (Term.proj `l "." `dropWhile)
          [(Term.fun
            "fun"
            (Term.basicFun
             [`b]
             []
             "=>"
             («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_++_»
       (Term.app
        (Term.proj `l "." `takeWhile)
        [(Term.fun
          "fun"
          (Term.basicFun [`b] [] "=>" («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))])
       "++"
       («term_::_»
        `a
        "::"
        (Term.app
         (Term.proj `l "." `dropWhile)
         [(Term.fun
           "fun"
           (Term.basicFun
            [`b]
            []
            "=>"
            («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_»
       `a
       "::"
       (Term.app
        (Term.proj `l "." `dropWhile)
        [(Term.fun
          "fun"
          (Term.basicFun
           [`b]
           []
           "=>"
           («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `l "." `dropWhile)
       [(Term.fun
         "fun"
         (Term.basicFun [`b] [] "=>" («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`b] [] "=>" («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Sort.«term_≼_» `a " ≼ " `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Sort.«term_≼_»', expected 'List.Data.List.Sort.term_≼_._@.Data.List.Sort._hyg.14'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- An alternative definition of `ordered_insert` using `take_while` and `drop_while`. -/
  theorem
    ordered_insert_eq_take_drop
    ( a : α )
      :
        ∀
          l
          : List α
          ,
          l . orderedInsert r a
            =
            l . takeWhile fun b => ¬ a ≼ b ++ a :: l . dropWhile fun b => ¬ a ≼ b
    | [ ] => rfl
      |
        b :: l
        =>
        by dsimp only [ ordered_insert ] split_ifs <;> simp [ take_while , drop_while , * ]
#align list.ordered_insert_eq_take_drop List.ordered_insert_eq_take_drop

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `insertion_sort_cons_eq_take_drop [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `α] [] ")")
        (Term.explicitBinder "(" [`l] [":" (Term.app `List [`α])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `insertionSort [`r («term_::_» `a "::" `l)])
         "="
         («term_++_»
          (Term.app
           (Term.proj (Term.app `insertionSort [`r `l]) "." `takeWhile)
           [(Term.fun
             "fun"
             (Term.basicFun
              [`b]
              []
              "=>"
              («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))])
          "++"
          («term_::_»
           `a
           "::"
           (Term.app
            (Term.proj (Term.app `insertionSort [`r `l]) "." `dropWhile)
            [(Term.fun
              "fun"
              (Term.basicFun
               [`b]
               []
               "=>"
               («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))]))))))
      (Command.declValSimple
       ":="
       (Term.app `ordered_insert_eq_take_drop [`r `a (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ordered_insert_eq_take_drop [`r `a (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ordered_insert_eq_take_drop
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `insertionSort [`r («term_::_» `a "::" `l)])
       "="
       («term_++_»
        (Term.app
         (Term.proj (Term.app `insertionSort [`r `l]) "." `takeWhile)
         [(Term.fun
           "fun"
           (Term.basicFun
            [`b]
            []
            "=>"
            («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))])
        "++"
        («term_::_»
         `a
         "::"
         (Term.app
          (Term.proj (Term.app `insertionSort [`r `l]) "." `dropWhile)
          [(Term.fun
            "fun"
            (Term.basicFun
             [`b]
             []
             "=>"
             («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_++_»
       (Term.app
        (Term.proj (Term.app `insertionSort [`r `l]) "." `takeWhile)
        [(Term.fun
          "fun"
          (Term.basicFun [`b] [] "=>" («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))])
       "++"
       («term_::_»
        `a
        "::"
        (Term.app
         (Term.proj (Term.app `insertionSort [`r `l]) "." `dropWhile)
         [(Term.fun
           "fun"
           (Term.basicFun
            [`b]
            []
            "=>"
            («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_»
       `a
       "::"
       (Term.app
        (Term.proj (Term.app `insertionSort [`r `l]) "." `dropWhile)
        [(Term.fun
          "fun"
          (Term.basicFun
           [`b]
           []
           "=>"
           («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `insertionSort [`r `l]) "." `dropWhile)
       [(Term.fun
         "fun"
         (Term.basicFun [`b] [] "=>" («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`b] [] "=>" («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term¬_» "¬" (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Sort.«term_≼_» `a " ≼ " `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Sort.«term_≼_»', expected 'List.Data.List.Sort.term_≼_._@.Data.List.Sort._hyg.14'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  insertion_sort_cons_eq_take_drop
  ( a : α ) ( l : List α )
    :
      insertionSort r a :: l
        =
        insertionSort r l . takeWhile fun b => ¬ a ≼ b
          ++
          a :: insertionSort r l . dropWhile fun b => ¬ a ≼ b
  := ordered_insert_eq_take_drop r a _
#align list.insertion_sort_cons_eq_take_drop List.insertion_sort_cons_eq_take_drop

section Correctness

open Perm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `perm_ordered_insert [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [] [] ")")]
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [`l]
         [(Term.typeSpec ":" (Term.app `List [`α]))]
         ","
         (List.Data.List.Perm.list.perm
          (Term.app `orderedInsert [`r `a `l])
          " ~ "
          («term_::_» `a "::" `l)))))
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(«term[_]» "[" [] "]")]]
           "=>"
           (Term.app `Perm.refl [(Term.hole "_")]))
          (Term.matchAlt
           "|"
           [[(«term_::_» `b "::" `l)]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.seq_focus
                (Classical.«tacticBy_cases_:_»
                 "by_cases"
                 []
                 (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))
                "<;>"
                "["
                [(Tactic.simp
                  "simp"
                  []
                  []
                  []
                  ["["
                   [(Tactic.simpLemma [] [] `ordered_insert) "," (Tactic.simpLemma [] [] `h)]
                   "]"]
                  [])
                 ","
                 (Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest
                   []
                   []
                   []
                   [(Tactic.simpArgs
                     "["
                     [(Tactic.simpLemma [] [] `ordered_insert) "," (Tactic.simpLemma [] [] `h)]
                     "]")]
                   ["using"
                    (Term.app
                     (Term.proj
                      (Term.app
                       (Term.proj (Term.app `perm_ordered_insert [`l]) "." `cons)
                       [(Term.hole "_")])
                      "."
                      `trans)
                     [(Term.app `perm.swap [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])]))]
                "]")]))))])
        []))
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.seq_focus
           (Classical.«tacticBy_cases_:_» "by_cases" [] (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))
           "<;>"
           "["
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] `ordered_insert) "," (Tactic.simpLemma [] [] `h)] "]"]
             [])
            ","
            (Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              []
              [(Tactic.simpArgs
                "["
                [(Tactic.simpLemma [] [] `ordered_insert) "," (Tactic.simpLemma [] [] `h)]
                "]")]
              ["using"
               (Term.app
                (Term.proj
                 (Term.app
                  (Term.proj (Term.app `perm_ordered_insert [`l]) "." `cons)
                  [(Term.hole "_")])
                 "."
                 `trans)
                [(Term.app `perm.swap [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])]))]
           "]")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.seq_focus
       (Classical.«tacticBy_cases_:_» "by_cases" [] (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))
       "<;>"
       "["
       [(Tactic.simp
         "simp"
         []
         []
         []
         ["[" [(Tactic.simpLemma [] [] `ordered_insert) "," (Tactic.simpLemma [] [] `h)] "]"]
         [])
        ","
        (Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest
          []
          []
          []
          [(Tactic.simpArgs
            "["
            [(Tactic.simpLemma [] [] `ordered_insert) "," (Tactic.simpLemma [] [] `h)]
            "]")]
          ["using"
           (Term.app
            (Term.proj
             (Term.app (Term.proj (Term.app `perm_ordered_insert [`l]) "." `cons) [(Term.hole "_")])
             "."
             `trans)
            [(Term.app `perm.swap [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])]))]
       "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `ordered_insert) "," (Tactic.simpLemma [] [] `h)]
          "]")]
        ["using"
         (Term.app
          (Term.proj
           (Term.app (Term.proj (Term.app `perm_ordered_insert [`l]) "." `cons) [(Term.hole "_")])
           "."
           `trans)
          [(Term.app `perm.swap [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app (Term.proj (Term.app `perm_ordered_insert [`l]) "." `cons) [(Term.hole "_")])
        "."
        `trans)
       [(Term.app `perm.swap [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `perm.swap [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `perm.swap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `perm.swap [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app (Term.proj (Term.app `perm_ordered_insert [`l]) "." `cons) [(Term.hole "_")])
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj (Term.app `perm_ordered_insert [`l]) "." `cons) [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `perm_ordered_insert [`l]) "." `cons)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `perm_ordered_insert [`l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `perm_ordered_insert
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `perm_ordered_insert [`l])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `perm_ordered_insert [`l]) ")") "." `cons)
      [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ordered_insert
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] `ordered_insert) "," (Tactic.simpLemma [] [] `h)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ordered_insert
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Classical.«tacticBy_cases_:_» "by_cases" [] (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Sort.«term_≼_» `a " ≼ " `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Sort.«term_≼_»', expected 'List.Data.List.Sort.term_≼_._@.Data.List.Sort._hyg.14'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  perm_ordered_insert
  ( a ) : ∀ l : List α , orderedInsert r a l ~ a :: l
  | [ ] => Perm.refl _
    |
      b :: l
      =>
      by
        by_cases a ≼ b
          <;>
          [
          simp [ ordered_insert , h ]
            ,
            simpa
              [ ordered_insert , h ] using perm_ordered_insert l . cons _ . trans perm.swap _ _ _
          ]
#align list.perm_ordered_insert List.perm_ordered_insert

theorem ordered_insert_count [DecidableEq α] (L : List α) (a b : α) :
    count a (L.orderedInsert r b) = count a L + if a = b then 1 else 0 :=
  by
  rw [(L.perm_ordered_insert r b).count_eq, count_cons]
  split_ifs <;> simp only [Nat.succ_eq_add_one, add_zero]
#align list.ordered_insert_count List.ordered_insert_count

theorem perm_insertion_sort : ∀ l : List α, insertionSort r l ~ l
  | [] => Perm.nil
  | b :: l => by
    simpa [insertion_sort] using (perm_ordered_insert _ _ _).trans ((perm_insertion_sort l).cons b)
#align list.perm_insertion_sort List.perm_insertion_sort

variable {r}

/-- If `l` is already `list.sorted` with respect to `r`, then `insertion_sort` does not change
it. -/
theorem Sorted.insertion_sort_eq : ∀ {l : List α} (h : Sorted r l), insertionSort r l = l
  | [], _ => rfl
  | [a], _ => rfl
  | a :: b :: l, h =>
    by
    rw [insertion_sort, sorted.insertion_sort_eq, ordered_insert, if_pos]
    exacts[rel_of_sorted_cons h _ (Or.inl rfl), h.tail]
#align list.sorted.insertion_sort_eq List.Sorted.insertion_sort_eq

section TotalAndTransitive

variable [IsTotal α r] [IsTrans α r]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Sorted.ordered_insert [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `α] [] ")")]
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [`l]
         []
         ","
         (Term.arrow
          (Term.app `Sorted [`r `l])
          "→"
          (Term.app `Sorted [`r (Term.app `orderedInsert [`r `a `l])])))))
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(«term[_]» "[" [] "]") "," `h]]
           "=>"
           (Term.app `sorted_singleton [`a]))
          (Term.matchAlt
           "|"
           [[(«term_::_» `b "::" `l) "," `h]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Classical.«tacticBy_cases_:_»
                "by_cases"
                [`h' ":"]
                (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest
                   []
                   []
                   []
                   [(Tactic.simpArgs
                     "["
                     [(Tactic.simpLemma [] [] `ordered_insert)
                      ","
                      (Tactic.simpLemma [] [] `h')
                      ","
                      (Tactic.simpLemma [] [] `h)]
                     "]")]
                   ["using"
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`b' `bm]
                      []
                      "=>"
                      (Term.app
                       `trans
                       [`h' (Term.app `rel_of_sorted_cons [`h (Term.hole "_") `bm])])))]))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.tacticSuffices_
                  "suffices"
                  (Term.sufficesDecl
                   []
                   (Term.forall
                    "∀"
                    [`b']
                    [(Term.typeSpec ":" `α)]
                    ","
                    (Term.arrow
                     («term_∈_» `b' "∈" (Term.app `ordered_insert [`r `a `l]))
                     "→"
                     (Term.app `r [`b `b'])))
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Std.Tactic.Simpa.simpa
                        "simpa"
                        []
                        []
                        (Std.Tactic.Simpa.simpaArgsRest
                         []
                         []
                         []
                         [(Tactic.simpArgs
                           "["
                           [(Tactic.simpLemma [] [] `ordered_insert)
                            ","
                            (Tactic.simpLemma [] [] `h')
                            ","
                            (Tactic.simpLemma [] [] (Term.app `h.of_cons.ordered_insert [`l]))]
                           "]")]
                         []))])))))
                 []
                 (Tactic.intro "intro" [`b' `bm])
                 []
                 (Tactic.cases'
                  "cases'"
                  [(Tactic.casesTarget
                    []
                    (Term.show
                     "show"
                     («term_∨_» («term_=_» `b' "=" `a) "∨" («term_∈_» `b' "∈" `l))
                     (Term.byTactic'
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Std.Tactic.Simpa.simpa
                          "simpa"
                          []
                          []
                          (Std.Tactic.Simpa.simpaArgsRest
                           []
                           []
                           []
                           []
                           ["using"
                            (Term.app
                             (Term.proj
                              (Term.app
                               `perm_ordered_insert
                               [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                              "."
                              `Subset)
                             [`bm])]))])))))]
                  []
                  ["with" [(Lean.binderIdent `be) (Lean.binderIdent `bm)]])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.subst "subst" [`b'])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.app
                     (Term.proj
                      (Term.app `total_of [`r (Term.hole "_") (Term.hole "_")])
                      "."
                      `resolve_left)
                     [`h']))])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact
                    "exact"
                    (Term.app `rel_of_sorted_cons [`h (Term.hole "_") `bm]))])])]))))])
        []))
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Classical.«tacticBy_cases_:_»
           "by_cases"
           [`h' ":"]
           (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              []
              [(Tactic.simpArgs
                "["
                [(Tactic.simpLemma [] [] `ordered_insert)
                 ","
                 (Tactic.simpLemma [] [] `h')
                 ","
                 (Tactic.simpLemma [] [] `h)]
                "]")]
              ["using"
               (Term.fun
                "fun"
                (Term.basicFun
                 [`b' `bm]
                 []
                 "=>"
                 (Term.app
                  `trans
                  [`h' (Term.app `rel_of_sorted_cons [`h (Term.hole "_") `bm])])))]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticSuffices_
             "suffices"
             (Term.sufficesDecl
              []
              (Term.forall
               "∀"
               [`b']
               [(Term.typeSpec ":" `α)]
               ","
               (Term.arrow
                («term_∈_» `b' "∈" (Term.app `ordered_insert [`r `a `l]))
                "→"
                (Term.app `r [`b `b'])))
              (Term.byTactic'
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.Simpa.simpa
                   "simpa"
                   []
                   []
                   (Std.Tactic.Simpa.simpaArgsRest
                    []
                    []
                    []
                    [(Tactic.simpArgs
                      "["
                      [(Tactic.simpLemma [] [] `ordered_insert)
                       ","
                       (Tactic.simpLemma [] [] `h')
                       ","
                       (Tactic.simpLemma [] [] (Term.app `h.of_cons.ordered_insert [`l]))]
                      "]")]
                    []))])))))
            []
            (Tactic.intro "intro" [`b' `bm])
            []
            (Tactic.cases'
             "cases'"
             [(Tactic.casesTarget
               []
               (Term.show
                "show"
                («term_∨_» («term_=_» `b' "=" `a) "∨" («term_∈_» `b' "∈" `l))
                (Term.byTactic'
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Std.Tactic.Simpa.simpa
                     "simpa"
                     []
                     []
                     (Std.Tactic.Simpa.simpaArgsRest
                      []
                      []
                      []
                      []
                      ["using"
                       (Term.app
                        (Term.proj
                         (Term.app
                          `perm_ordered_insert
                          [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                         "."
                         `Subset)
                        [`bm])]))])))))]
             []
             ["with" [(Lean.binderIdent `be) (Lean.binderIdent `bm)]])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.subst "subst" [`b'])
              []
              (Tactic.exact
               "exact"
               (Term.app
                (Term.proj
                 (Term.app `total_of [`r (Term.hole "_") (Term.hole "_")])
                 "."
                 `resolve_left)
                [`h']))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact "exact" (Term.app `rel_of_sorted_cons [`h (Term.hole "_") `bm]))])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          (Term.forall
           "∀"
           [`b']
           [(Term.typeSpec ":" `α)]
           ","
           (Term.arrow
            («term_∈_» `b' "∈" (Term.app `ordered_insert [`r `a `l]))
            "→"
            (Term.app `r [`b `b'])))
          (Term.byTactic'
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest
                []
                []
                []
                [(Tactic.simpArgs
                  "["
                  [(Tactic.simpLemma [] [] `ordered_insert)
                   ","
                   (Tactic.simpLemma [] [] `h')
                   ","
                   (Tactic.simpLemma [] [] (Term.app `h.of_cons.ordered_insert [`l]))]
                  "]")]
                []))])))))
        []
        (Tactic.intro "intro" [`b' `bm])
        []
        (Tactic.cases'
         "cases'"
         [(Tactic.casesTarget
           []
           (Term.show
            "show"
            («term_∨_» («term_=_» `b' "=" `a) "∨" («term_∈_» `b' "∈" `l))
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Std.Tactic.Simpa.simpa
                 "simpa"
                 []
                 []
                 (Std.Tactic.Simpa.simpaArgsRest
                  []
                  []
                  []
                  []
                  ["using"
                   (Term.app
                    (Term.proj
                     (Term.app
                      `perm_ordered_insert
                      [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                     "."
                     `Subset)
                    [`bm])]))])))))]
         []
         ["with" [(Lean.binderIdent `be) (Lean.binderIdent `bm)]])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.subst "subst" [`b'])
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj (Term.app `total_of [`r (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
            [`h']))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact "exact" (Term.app `rel_of_sorted_cons [`h (Term.hole "_") `bm]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `rel_of_sorted_cons [`h (Term.hole "_") `bm]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `rel_of_sorted_cons [`h (Term.hole "_") `bm]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `rel_of_sorted_cons [`h (Term.hole "_") `bm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rel_of_sorted_cons
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.subst "subst" [`b'])
        []
        (Tactic.exact
         "exact"
         (Term.app
          (Term.proj (Term.app `total_of [`r (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
          [`h']))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj (Term.app `total_of [`r (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
        [`h']))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `total_of [`r (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
       [`h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `total_of [`r (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `total_of [`r (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `total_of
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `total_of [`r (Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.subst "subst" [`b'])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget
         []
         (Term.show
          "show"
          («term_∨_» («term_=_» `b' "=" `a) "∨" («term_∈_» `b' "∈" `l))
          (Term.byTactic'
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest
                []
                []
                []
                []
                ["using"
                 (Term.app
                  (Term.proj
                   (Term.app `perm_ordered_insert [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                   "."
                   `Subset)
                  [`bm])]))])))))]
       []
       ["with" [(Lean.binderIdent `be) (Lean.binderIdent `bm)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_∨_» («term_=_» `b' "=" `a) "∨" («term_∈_» `b' "∈" `l))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             []
             []
             ["using"
              (Term.app
               (Term.proj
                (Term.app `perm_ordered_insert [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                "."
                `Subset)
               [`bm])]))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        []
        ["using"
         (Term.app
          (Term.proj
           (Term.app `perm_ordered_insert [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
           "."
           `Subset)
          [`bm])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app `perm_ordered_insert [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
        "."
        `Subset)
       [`bm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app `perm_ordered_insert [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
       "."
       `Subset)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `perm_ordered_insert [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `perm_ordered_insert
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `perm_ordered_insert [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_∨_» («term_=_» `b' "=" `a) "∨" («term_∈_» `b' "∈" `l))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `b' "∈" `l)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `b'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 30 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 30, term))
      («term_=_» `b' "=" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `b'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 31 >? 50, (some 51, term) <=? (some 30, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 30, (some 30,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`b' `bm])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticSuffices_
       "suffices"
       (Term.sufficesDecl
        []
        (Term.forall
         "∀"
         [`b']
         [(Term.typeSpec ":" `α)]
         ","
         (Term.arrow
          («term_∈_» `b' "∈" (Term.app `ordered_insert [`r `a `l]))
          "→"
          (Term.app `r [`b `b'])))
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              []
              [(Tactic.simpArgs
                "["
                [(Tactic.simpLemma [] [] `ordered_insert)
                 ","
                 (Tactic.simpLemma [] [] `h')
                 ","
                 (Tactic.simpLemma [] [] (Term.app `h.of_cons.ordered_insert [`l]))]
                "]")]
              []))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `ordered_insert)
           ","
           (Tactic.simpLemma [] [] `h')
           ","
           (Tactic.simpLemma [] [] (Term.app `h.of_cons.ordered_insert [`l]))]
          "]")]
        []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h.of_cons.ordered_insert [`l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h.of_cons.ordered_insert
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ordered_insert
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [`b']
       [(Term.typeSpec ":" `α)]
       ","
       (Term.arrow
        («term_∈_» `b' "∈" (Term.app `ordered_insert [`r `a `l]))
        "→"
        (Term.app `r [`b `b'])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_∈_» `b' "∈" (Term.app `ordered_insert [`r `a `l]))
       "→"
       (Term.app `r [`b `b']))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `r [`b `b'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      («term_∈_» `b' "∈" (Term.app `ordered_insert [`r `a `l]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ordered_insert [`r `a `l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ordered_insert
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `b'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest
          []
          []
          []
          [(Tactic.simpArgs
            "["
            [(Tactic.simpLemma [] [] `ordered_insert)
             ","
             (Tactic.simpLemma [] [] `h')
             ","
             (Tactic.simpLemma [] [] `h)]
            "]")]
          ["using"
           (Term.fun
            "fun"
            (Term.basicFun
             [`b' `bm]
             []
             "=>"
             (Term.app `trans [`h' (Term.app `rel_of_sorted_cons [`h (Term.hole "_") `bm])])))]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `ordered_insert)
           ","
           (Tactic.simpLemma [] [] `h')
           ","
           (Tactic.simpLemma [] [] `h)]
          "]")]
        ["using"
         (Term.fun
          "fun"
          (Term.basicFun
           [`b' `bm]
           []
           "=>"
           (Term.app `trans [`h' (Term.app `rel_of_sorted_cons [`h (Term.hole "_") `bm])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`b' `bm]
        []
        "=>"
        (Term.app `trans [`h' (Term.app `rel_of_sorted_cons [`h (Term.hole "_") `bm])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `trans [`h' (Term.app `rel_of_sorted_cons [`h (Term.hole "_") `bm])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `rel_of_sorted_cons [`h (Term.hole "_") `bm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rel_of_sorted_cons
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `rel_of_sorted_cons [`h (Term.hole "_") `bm])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ordered_insert
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Classical.«tacticBy_cases_:_»
       "by_cases"
       [`h' ":"]
       (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Sort.«term_≼_» `a " ≼ " `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Sort.«term_≼_»', expected 'List.Data.List.Sort.term_≼_._@.Data.List.Sort._hyg.14'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  Sorted.ordered_insert
  ( a : α ) : ∀ l , Sorted r l → Sorted r orderedInsert r a l
  | [ ] , h => sorted_singleton a
    |
      b :: l , h
      =>
      by
        by_cases h' : a ≼ b
          · simpa [ ordered_insert , h' , h ] using fun b' bm => trans h' rel_of_sorted_cons h _ bm
          ·
            suffices
                ∀ b' : α , b' ∈ ordered_insert r a l → r b b'
                  by simpa [ ordered_insert , h' , h.of_cons.ordered_insert l ]
              intro b' bm
              cases'
                show b' = a ∨ b' ∈ l by simpa using perm_ordered_insert _ _ _ . Subset bm
                with be bm
              · subst b' exact total_of r _ _ . resolve_left h'
              · exact rel_of_sorted_cons h _ bm
#align list.sorted.ordered_insert List.Sorted.ordered_insert

variable (r)

/-- The list `list.insertion_sort r l` is `list.sorted` with respect to `r`. -/
theorem sorted_insertion_sort : ∀ l, Sorted r (insertionSort r l)
  | [] => sorted_nil
  | a :: l => (sorted_insertion_sort l).orderedInsert a _
#align list.sorted_insertion_sort List.sorted_insertion_sort

end TotalAndTransitive

end Correctness

end InsertionSort

/-! ### Merge sort -/


section MergeSort

-- TODO(Jeremy): observation: if instead we write (a :: (split l).1, b :: (split l).2), the
-- equation compiler can't prove the third equation
/-- Split `l` into two lists of approximately equal length.

     split [1, 2, 3, 4, 5] = ([1, 3, 5], [2, 4]) -/
@[simp]
def split : List α → List α × List α
  | [] => ([], [])
  | a :: l =>
    let (l₁, l₂) := split l
    (a :: l₂, l₁)
#align list.split List.split

theorem split_cons_of_eq (a : α) {l l₁ l₂ : List α} (h : split l = (l₁, l₂)) :
    split (a :: l) = (a :: l₂, l₁) := by rw [split, h] <;> rfl
#align list.split_cons_of_eq List.split_cons_of_eq

theorem length_split_le :
    ∀ {l l₁ l₂ : List α}, split l = (l₁, l₂) → length l₁ ≤ length l ∧ length l₂ ≤ length l
  | [], _, _, rfl => ⟨Nat.le_refl 0, Nat.le_refl 0⟩
  | a :: l, l₁', l₂', h => by
    cases' e : split l with l₁ l₂
    injection (split_cons_of_eq _ e).symm.trans h; substs l₁' l₂'
    cases' length_split_le e with h₁ h₂
    exact ⟨Nat.succ_le_succ h₂, Nat.le_succ_of_le h₁⟩
#align list.length_split_le List.length_split_le

theorem length_split_lt {a b} {l l₁ l₂ : List α} (h : split (a :: b :: l) = (l₁, l₂)) :
    length l₁ < length (a :: b :: l) ∧ length l₂ < length (a :: b :: l) :=
  by
  cases' e : split l with l₁' l₂'
  injection (split_cons_of_eq _ (split_cons_of_eq _ e)).symm.trans h; substs l₁ l₂
  cases' length_split_le e with h₁ h₂
  exact ⟨Nat.succ_le_succ (Nat.succ_le_succ h₁), Nat.succ_le_succ (Nat.succ_le_succ h₂)⟩
#align list.length_split_lt List.length_split_lt

theorem perm_split : ∀ {l l₁ l₂ : List α}, split l = (l₁, l₂) → l ~ l₁ ++ l₂
  | [], _, _, rfl => Perm.refl _
  | a :: l, l₁', l₂', h => by
    cases' e : split l with l₁ l₂
    injection (split_cons_of_eq _ e).symm.trans h; substs l₁' l₂'
    exact ((perm_split e).trans perm_append_comm).cons a
#align list.perm_split List.perm_split

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Merge two sorted lists into one in linear time.\n\n     merge [1, 2, 4, 5] [0, 1, 3, 4] = [0, 1, 1, 2, 3, 4, 4, 5] -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `merge [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app `List [`α])
          "→"
          (Term.arrow (Term.app `List [`α]) "→" (Term.app `List [`α]))))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[(«term[_]» "[" [] "]") "," `l']] "=>" `l')
          (Term.matchAlt "|" [[`l "," («term[_]» "[" [] "]")]] "=>" `l)
          (Term.matchAlt
           "|"
           [[(«term_::_» `a "::" `l) "," («term_::_» `b "::" `l')]]
           "=>"
           (termIfThenElse
            "if"
            (List.Data.List.Sort.«term_≼_» `a " ≼ " `b)
            "then"
            («term_::_» `a "::" (Term.app `merge [`l («term_::_» `b "::" `l')]))
            "else"
            («term_::_» `b "::" (Term.app `merge [(«term_::_» `a "::" `l) `l']))))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termIfThenElse
       "if"
       (List.Data.List.Sort.«term_≼_» `a " ≼ " `b)
       "then"
       («term_::_» `a "::" (Term.app `merge [`l («term_::_» `b "::" `l')]))
       "else"
       («term_::_» `b "::" (Term.app `merge [(«term_::_» `a "::" `l) `l'])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `b "::" (Term.app `merge [(«term_::_» `a "::" `l) `l']))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `merge [(«term_::_» `a "::" `l) `l'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_::_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_::_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_::_» `a "::" `l)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 67, (some 67, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_::_» `a "::" `l) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `merge
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `a "::" (Term.app `merge [`l («term_::_» `b "::" `l')]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `merge [`l («term_::_» `b "::" `l')])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_::_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_::_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `b "::" `l')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l'
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_::_» `b "::" `l') ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `merge
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Sort.«term_≼_» `a " ≼ " `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Sort.«term_≼_»', expected 'List.Data.List.Sort.term_≼_._@.Data.List.Sort._hyg.14'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Merge two sorted lists into one in linear time.
    
         merge [1, 2, 4, 5] [0, 1, 3, 4] = [0, 1, 1, 2, 3, 4, 4, 5] -/
  def
    merge
    : List α → List α → List α
    | [ ] , l' => l'
      | l , [ ] => l
      | a :: l , b :: l' => if a ≼ b then a :: merge l b :: l' else b :: merge a :: l l'
#align list.merge List.merge

include r

/-- Implementation of a merge sort algorithm to sort a list. -/
def mergeSort : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: l => by
    cases' e : split (a :: b :: l) with l₁ l₂
    cases' length_split_lt e with h₁ h₂
    exact merge r (merge_sort l₁) (merge_sort l₂)termination_by'
  ⟨_, InvImage.wf length Nat.lt_wfRel⟩
#align list.merge_sort List.mergeSort

theorem merge_sort_cons_cons {a b} {l l₁ l₂ : List α} (h : split (a :: b :: l) = (l₁, l₂)) :
    mergeSort r (a :: b :: l) = merge r (mergeSort r l₁) (mergeSort r l₂) :=
  by
  suffices
    ∀ (L : List α) (h1),
      @And.ndrec (fun a a (_ : length l₁ < length l + 1 + 1 ∧ length l₂ < length l + 1 + 1) => L) h1
          h1 =
        L
    by
    simp [merge_sort, h]
    apply this
  intros
  cases h1
  rfl
#align list.merge_sort_cons_cons List.merge_sort_cons_cons

section Correctness

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `perm_merge [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [`l `l']
         [(Term.typeSpec ":" (Term.app `List [`α]))]
         ","
         (List.Data.List.Perm.list.perm
          (Term.app `merge [`r `l `l'])
          " ~ "
          («term_++_» `l "++" `l')))))
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]")]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `merge)] "]"] [])]))))
          (Term.matchAlt
           "|"
           [[(«term[_]» "[" [] "]") "," («term_::_» `b "::" `l')]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `merge)] "]"] [])]))))
          (Term.matchAlt
           "|"
           [[(«term_::_» `a "::" `l) "," («term[_]» "[" [] "]")]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `merge)] "]"] [])]))))
          (Term.matchAlt
           "|"
           [[(«term_::_» `a "::" `l) "," («term_::_» `b "::" `l')]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Classical.«tacticBy_cases_:_»
                "by_cases"
                []
                (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest
                   []
                   []
                   []
                   [(Tactic.simpArgs
                     "["
                     [(Tactic.simpLemma [] [] `merge) "," (Tactic.simpLemma [] [] `h)]
                     "]")]
                   ["using" (Term.app `perm_merge [(Term.hole "_") (Term.hole "_")])]))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.tacticSuffices_
                  "suffices"
                  (Term.sufficesDecl
                   []
                   (List.Data.List.Perm.list.perm
                    («term_::_» `b "::" (Term.app `merge [`r («term_::_» `a "::" `l) `l']))
                    " ~ "
                    («term_::_» `a "::" («term_++_» `l "++" («term_::_» `b "::" `l'))))
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Std.Tactic.Simpa.simpa
                        "simpa"
                        []
                        []
                        (Std.Tactic.Simpa.simpaArgsRest
                         []
                         []
                         []
                         [(Tactic.simpArgs
                           "["
                           [(Tactic.simpLemma [] [] `merge) "," (Tactic.simpLemma [] [] `h)]
                           "]")]
                         []))])))))
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   (Term.proj
                    (Term.app
                     (Term.proj (Term.app `perm_merge [(Term.hole "_") (Term.hole "_")]) "." `cons)
                     [(Term.hole "_")])
                    "."
                    `trans)
                   [(Term.app
                     (Term.proj
                      (Term.app `swap [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                      "."
                      `trans)
                     [(Term.app `perm_middle.symm.cons [(Term.hole "_")])])]))])]))))])
        []))
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Classical.«tacticBy_cases_:_» "by_cases" [] (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              []
              [(Tactic.simpArgs
                "["
                [(Tactic.simpLemma [] [] `merge) "," (Tactic.simpLemma [] [] `h)]
                "]")]
              ["using" (Term.app `perm_merge [(Term.hole "_") (Term.hole "_")])]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticSuffices_
             "suffices"
             (Term.sufficesDecl
              []
              (List.Data.List.Perm.list.perm
               («term_::_» `b "::" (Term.app `merge [`r («term_::_» `a "::" `l) `l']))
               " ~ "
               («term_::_» `a "::" («term_++_» `l "++" («term_::_» `b "::" `l'))))
              (Term.byTactic'
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.Simpa.simpa
                   "simpa"
                   []
                   []
                   (Std.Tactic.Simpa.simpaArgsRest
                    []
                    []
                    []
                    [(Tactic.simpArgs
                      "["
                      [(Tactic.simpLemma [] [] `merge) "," (Tactic.simpLemma [] [] `h)]
                      "]")]
                    []))])))))
            []
            (Tactic.exact
             "exact"
             (Term.app
              (Term.proj
               (Term.app
                (Term.proj (Term.app `perm_merge [(Term.hole "_") (Term.hole "_")]) "." `cons)
                [(Term.hole "_")])
               "."
               `trans)
              [(Term.app
                (Term.proj
                 (Term.app `swap [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                 "."
                 `trans)
                [(Term.app `perm_middle.symm.cons [(Term.hole "_")])])]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          (List.Data.List.Perm.list.perm
           («term_::_» `b "::" (Term.app `merge [`r («term_::_» `a "::" `l) `l']))
           " ~ "
           («term_::_» `a "::" («term_++_» `l "++" («term_::_» `b "::" `l'))))
          (Term.byTactic'
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest
                []
                []
                []
                [(Tactic.simpArgs
                  "["
                  [(Tactic.simpLemma [] [] `merge) "," (Tactic.simpLemma [] [] `h)]
                  "]")]
                []))])))))
        []
        (Tactic.exact
         "exact"
         (Term.app
          (Term.proj
           (Term.app
            (Term.proj (Term.app `perm_merge [(Term.hole "_") (Term.hole "_")]) "." `cons)
            [(Term.hole "_")])
           "."
           `trans)
          [(Term.app
            (Term.proj
             (Term.app `swap [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
             "."
             `trans)
            [(Term.app `perm_middle.symm.cons [(Term.hole "_")])])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj
         (Term.app
          (Term.proj (Term.app `perm_merge [(Term.hole "_") (Term.hole "_")]) "." `cons)
          [(Term.hole "_")])
         "."
         `trans)
        [(Term.app
          (Term.proj (Term.app `swap [(Term.hole "_") (Term.hole "_") (Term.hole "_")]) "." `trans)
          [(Term.app `perm_middle.symm.cons [(Term.hole "_")])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         (Term.proj (Term.app `perm_merge [(Term.hole "_") (Term.hole "_")]) "." `cons)
         [(Term.hole "_")])
        "."
        `trans)
       [(Term.app
         (Term.proj (Term.app `swap [(Term.hole "_") (Term.hole "_") (Term.hole "_")]) "." `trans)
         [(Term.app `perm_middle.symm.cons [(Term.hole "_")])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `swap [(Term.hole "_") (Term.hole "_") (Term.hole "_")]) "." `trans)
       [(Term.app `perm_middle.symm.cons [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `perm_middle.symm.cons [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `perm_middle.symm.cons
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `perm_middle.symm.cons [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `swap [(Term.hole "_") (Term.hole "_") (Term.hole "_")]) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `swap [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `swap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `swap [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren "(" (Term.app `swap [(Term.hole "_") (Term.hole "_") (Term.hole "_")]) ")")
       "."
       `trans)
      [(Term.paren "(" (Term.app `perm_middle.symm.cons [(Term.hole "_")]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        (Term.proj (Term.app `perm_merge [(Term.hole "_") (Term.hole "_")]) "." `cons)
        [(Term.hole "_")])
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.app `perm_merge [(Term.hole "_") (Term.hole "_")]) "." `cons)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `perm_merge [(Term.hole "_") (Term.hole "_")]) "." `cons)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `perm_merge [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `perm_merge
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `perm_merge [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren "(" (Term.app `perm_merge [(Term.hole "_") (Term.hole "_")]) ")")
       "."
       `cons)
      [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticSuffices_
       "suffices"
       (Term.sufficesDecl
        []
        (List.Data.List.Perm.list.perm
         («term_::_» `b "::" (Term.app `merge [`r («term_::_» `a "::" `l) `l']))
         " ~ "
         («term_::_» `a "::" («term_++_» `l "++" («term_::_» `b "::" `l'))))
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              []
              [(Tactic.simpArgs
                "["
                [(Tactic.simpLemma [] [] `merge) "," (Tactic.simpLemma [] [] `h)]
                "]")]
              []))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `merge) "," (Tactic.simpLemma [] [] `h)]
          "]")]
        []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `merge
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (List.Data.List.Perm.list.perm
       («term_::_» `b "::" (Term.app `merge [`r («term_::_» `a "::" `l) `l']))
       " ~ "
       («term_::_» `a "::" («term_++_» `l "++" («term_::_» `b "::" `l'))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `a "::" («term_++_» `l "++" («term_::_» `b "::" `l')))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_++_» `l "++" («term_::_» `b "::" `l'))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `b "::" `l')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l'
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 67 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_++_» `l "++" («term_::_» `b "::" `l'))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_::_» `b "::" (Term.app `merge [`r («term_::_» `a "::" `l) `l']))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `merge [`r («term_::_» `a "::" `l) `l'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_::_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_::_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_::_» `a "::" `l)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 67, (some 67, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_::_» `a "::" `l) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `merge
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 50 >? 67, (some 67, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest
          []
          []
          []
          [(Tactic.simpArgs
            "["
            [(Tactic.simpLemma [] [] `merge) "," (Tactic.simpLemma [] [] `h)]
            "]")]
          ["using" (Term.app `perm_merge [(Term.hole "_") (Term.hole "_")])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `merge) "," (Tactic.simpLemma [] [] `h)]
          "]")]
        ["using" (Term.app `perm_merge [(Term.hole "_") (Term.hole "_")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `perm_merge [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `perm_merge
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `merge
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Classical.«tacticBy_cases_:_» "by_cases" [] (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Sort.«term_≼_» `a " ≼ " `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Sort.«term_≼_»', expected 'List.Data.List.Sort.term_≼_._@.Data.List.Sort._hyg.14'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  perm_merge
  : ∀ l l' : List α , merge r l l' ~ l ++ l'
  | [ ] , [ ] => by simp [ merge ]
    | [ ] , b :: l' => by simp [ merge ]
    | a :: l , [ ] => by simp [ merge ]
    |
      a :: l , b :: l'
      =>
      by
        by_cases a ≼ b
          · simpa [ merge , h ] using perm_merge _ _
          ·
            suffices b :: merge r a :: l l' ~ a :: l ++ b :: l' by simpa [ merge , h ]
              exact perm_merge _ _ . cons _ . trans swap _ _ _ . trans perm_middle.symm.cons _
#align list.perm_merge List.perm_merge

theorem perm_merge_sort : ∀ l : List α, mergeSort r l ~ l
  | [] => by simp [merge_sort]
  | [a] => by simp [merge_sort]
  | a :: b :: l => by
    cases' e : split (a :: b :: l) with l₁ l₂
    cases' length_split_lt e with h₁ h₂
    rw [merge_sort_cons_cons r e]
    apply (perm_merge r _ _).trans
    exact
      ((perm_merge_sort l₁).append (perm_merge_sort l₂)).trans (perm_split e).symm termination_by'
  ⟨_, InvImage.wf length Nat.lt_wfRel⟩
#align list.perm_merge_sort List.perm_merge_sort

@[simp]
theorem length_merge_sort (l : List α) : (mergeSort r l).length = l.length :=
  (perm_merge_sort r _).length_eq
#align list.length_merge_sort List.length_merge_sort

section TotalAndTransitive

variable {r} [IsTotal α r] [IsTrans α r]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Sorted.merge [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [(Term.implicitBinder "{" [`l `l'] [":" (Term.app `List [`α])] "}")]
         []
         ","
         (Term.arrow
          (Term.app `Sorted [`r `l])
          "→"
          (Term.arrow
           (Term.app `Sorted [`r `l'])
           "→"
           (Term.app `Sorted [`r (Term.app `merge [`r `l `l'])]))))))
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(«term[_]» "[" [] "]") "," («term[_]» "[" [] "]") "," `h₁ "," `h₂]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `merge)] "]"] [])]))))
          (Term.matchAlt
           "|"
           [[(«term[_]» "[" [] "]") "," («term_::_» `b "::" `l') "," `h₁ "," `h₂]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest
                 []
                 []
                 []
                 [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `merge)] "]")]
                 ["using" `h₂]))]))))
          (Term.matchAlt
           "|"
           [[(«term_::_» `a "::" `l) "," («term[_]» "[" [] "]") "," `h₁ "," `h₂]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest
                 []
                 []
                 []
                 [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `merge)] "]")]
                 ["using" `h₁]))]))))
          (Term.matchAlt
           "|"
           [[(«term_::_» `a "::" `l) "," («term_::_» `b "::" `l') "," `h₁ "," `h₂]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Classical.«tacticBy_cases_:_»
                "by_cases"
                []
                (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.tacticSuffices_
                  "suffices"
                  (Term.sufficesDecl
                   []
                   (Term.forall
                    "∀"
                    [(Term.explicitBinder "(" [`b'] [":" `α] [] ")")
                     (Term.explicitBinder
                      "("
                      [(Term.hole "_")]
                      [":" («term_∈_» `b' "∈" (Term.app `merge [`r `l («term_::_» `b "::" `l')]))]
                      []
                      ")")]
                    []
                    ","
                    (Term.app `r [`a `b']))
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Std.Tactic.Simpa.simpa
                        "simpa"
                        []
                        []
                        (Std.Tactic.Simpa.simpaArgsRest
                         []
                         []
                         []
                         [(Tactic.simpArgs
                           "["
                           [(Tactic.simpLemma [] [] `merge)
                            ","
                            (Tactic.simpLemma [] [] `h)
                            ","
                            (Tactic.simpLemma [] [] (Term.app `h₁.of_cons.merge [`h₂]))]
                           "]")]
                         []))])))))
                 []
                 (Tactic.intro "intro" [`b' `bm])
                 []
                 (Std.Tactic.rcases
                  "rcases"
                  [(Tactic.casesTarget
                    []
                    (Term.show
                     "show"
                     («term_∨_»
                      («term_=_» `b' "=" `b)
                      "∨"
                      («term_∨_» («term_∈_» `b' "∈" `l) "∨" («term_∈_» `b' "∈" `l')))
                     (Term.byTactic'
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Std.Tactic.Simpa.simpa
                          "simpa"
                          []
                          []
                          (Std.Tactic.Simpa.simpaArgsRest
                           []
                           []
                           []
                           [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `or_left_comm)] "]")]
                           ["using"
                            (Term.app
                             (Term.proj
                              (Term.app
                               `perm_merge
                               [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                              "."
                              `Subset)
                             [`bm])]))])))))]
                  ["with"
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.paren
                       "("
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.one `be)
                          "|"
                          (Std.Tactic.RCases.rcasesPat.one `bl)
                          "|"
                          (Std.Tactic.RCases.rcasesPat.one `bl')])
                        [])
                       ")")])
                    [])])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.subst "subst" [`b']) [] (Tactic.assumption "assumption")])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact "exact" (Term.app `rel_of_sorted_cons [`h₁ (Term.hole "_") `bl]))])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact
                    "exact"
                    (Term.app
                     `trans
                     [`h (Term.app `rel_of_sorted_cons [`h₂ (Term.hole "_") `bl'])]))])])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.tacticSuffices_
                  "suffices"
                  (Term.sufficesDecl
                   []
                   (Term.forall
                    "∀"
                    [(Term.explicitBinder "(" [`b'] [":" `α] [] ")")
                     (Term.explicitBinder
                      "("
                      [(Term.hole "_")]
                      [":" («term_∈_» `b' "∈" (Term.app `merge [`r («term_::_» `a "::" `l) `l']))]
                      []
                      ")")]
                    []
                    ","
                    (Term.app `r [`b `b']))
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Std.Tactic.Simpa.simpa
                        "simpa"
                        []
                        []
                        (Std.Tactic.Simpa.simpaArgsRest
                         []
                         []
                         []
                         [(Tactic.simpArgs
                           "["
                           [(Tactic.simpLemma [] [] `merge)
                            ","
                            (Tactic.simpLemma [] [] `h)
                            ","
                            (Tactic.simpLemma [] [] (Term.app `h₁.merge [`h₂.of_cons]))]
                           "]")]
                         []))])))))
                 []
                 (Tactic.intro "intro" [`b' `bm])
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`ba []]
                    [(Term.typeSpec ":" (List.Data.List.Sort.«term_≼_» `b " ≼ " `a))]
                    ":="
                    (Term.app
                     (Term.proj
                      (Term.app `total_of [`r (Term.hole "_") (Term.hole "_")])
                      "."
                      `resolve_left)
                     [`h]))))
                 []
                 (Std.Tactic.rcases
                  "rcases"
                  [(Tactic.casesTarget
                    []
                    (Term.show
                     "show"
                     («term_∨_»
                      («term_=_» `b' "=" `a)
                      "∨"
                      («term_∨_» («term_∈_» `b' "∈" `l) "∨" («term_∈_» `b' "∈" `l')))
                     (Term.byTactic'
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Std.Tactic.Simpa.simpa
                          "simpa"
                          []
                          []
                          (Std.Tactic.Simpa.simpaArgsRest
                           []
                           []
                           []
                           []
                           ["using"
                            (Term.app
                             (Term.proj
                              (Term.app
                               `perm_merge
                               [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                              "."
                              `Subset)
                             [`bm])]))])))))]
                  ["with"
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.paren
                       "("
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.one `be)
                          "|"
                          (Std.Tactic.RCases.rcasesPat.one `bl)
                          "|"
                          (Std.Tactic.RCases.rcasesPat.one `bl')])
                        [])
                       ")")])
                    [])])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.subst "subst" [`b']) [] (Tactic.assumption "assumption")])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact
                    "exact"
                    (Term.app
                     `trans
                     [`ba (Term.app `rel_of_sorted_cons [`h₁ (Term.hole "_") `bl])]))])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact
                    "exact"
                    (Term.app `rel_of_sorted_cons [`h₂ (Term.hole "_") `bl']))])])]))))])
        []))
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Classical.«tacticBy_cases_:_» "by_cases" [] (List.Data.List.Sort.«term_≼_» `a " ≼ " `b))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticSuffices_
             "suffices"
             (Term.sufficesDecl
              []
              (Term.forall
               "∀"
               [(Term.explicitBinder "(" [`b'] [":" `α] [] ")")
                (Term.explicitBinder
                 "("
                 [(Term.hole "_")]
                 [":" («term_∈_» `b' "∈" (Term.app `merge [`r `l («term_::_» `b "::" `l')]))]
                 []
                 ")")]
               []
               ","
               (Term.app `r [`a `b']))
              (Term.byTactic'
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.Simpa.simpa
                   "simpa"
                   []
                   []
                   (Std.Tactic.Simpa.simpaArgsRest
                    []
                    []
                    []
                    [(Tactic.simpArgs
                      "["
                      [(Tactic.simpLemma [] [] `merge)
                       ","
                       (Tactic.simpLemma [] [] `h)
                       ","
                       (Tactic.simpLemma [] [] (Term.app `h₁.of_cons.merge [`h₂]))]
                      "]")]
                    []))])))))
            []
            (Tactic.intro "intro" [`b' `bm])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.show
                "show"
                («term_∨_»
                 («term_=_» `b' "=" `b)
                 "∨"
                 («term_∨_» («term_∈_» `b' "∈" `l) "∨" («term_∈_» `b' "∈" `l')))
                (Term.byTactic'
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Std.Tactic.Simpa.simpa
                     "simpa"
                     []
                     []
                     (Std.Tactic.Simpa.simpaArgsRest
                      []
                      []
                      []
                      [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `or_left_comm)] "]")]
                      ["using"
                       (Term.app
                        (Term.proj
                         (Term.app `perm_merge [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                         "."
                         `Subset)
                        [`bm])]))])))))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.paren
                  "("
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.one `be)
                     "|"
                     (Std.Tactic.RCases.rcasesPat.one `bl)
                     "|"
                     (Std.Tactic.RCases.rcasesPat.one `bl')])
                   [])
                  ")")])
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.subst "subst" [`b']) [] (Tactic.assumption "assumption")])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact "exact" (Term.app `rel_of_sorted_cons [`h₁ (Term.hole "_") `bl]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact
               "exact"
               (Term.app `trans [`h (Term.app `rel_of_sorted_cons [`h₂ (Term.hole "_") `bl'])]))])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticSuffices_
             "suffices"
             (Term.sufficesDecl
              []
              (Term.forall
               "∀"
               [(Term.explicitBinder "(" [`b'] [":" `α] [] ")")
                (Term.explicitBinder
                 "("
                 [(Term.hole "_")]
                 [":" («term_∈_» `b' "∈" (Term.app `merge [`r («term_::_» `a "::" `l) `l']))]
                 []
                 ")")]
               []
               ","
               (Term.app `r [`b `b']))
              (Term.byTactic'
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.Simpa.simpa
                   "simpa"
                   []
                   []
                   (Std.Tactic.Simpa.simpaArgsRest
                    []
                    []
                    []
                    [(Tactic.simpArgs
                      "["
                      [(Tactic.simpLemma [] [] `merge)
                       ","
                       (Tactic.simpLemma [] [] `h)
                       ","
                       (Tactic.simpLemma [] [] (Term.app `h₁.merge [`h₂.of_cons]))]
                      "]")]
                    []))])))))
            []
            (Tactic.intro "intro" [`b' `bm])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`ba []]
               [(Term.typeSpec ":" (List.Data.List.Sort.«term_≼_» `b " ≼ " `a))]
               ":="
               (Term.app
                (Term.proj
                 (Term.app `total_of [`r (Term.hole "_") (Term.hole "_")])
                 "."
                 `resolve_left)
                [`h]))))
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.show
                "show"
                («term_∨_»
                 («term_=_» `b' "=" `a)
                 "∨"
                 («term_∨_» («term_∈_» `b' "∈" `l) "∨" («term_∈_» `b' "∈" `l')))
                (Term.byTactic'
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Std.Tactic.Simpa.simpa
                     "simpa"
                     []
                     []
                     (Std.Tactic.Simpa.simpaArgsRest
                      []
                      []
                      []
                      []
                      ["using"
                       (Term.app
                        (Term.proj
                         (Term.app `perm_merge [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                         "."
                         `Subset)
                        [`bm])]))])))))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.paren
                  "("
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.one `be)
                     "|"
                     (Std.Tactic.RCases.rcasesPat.one `bl)
                     "|"
                     (Std.Tactic.RCases.rcasesPat.one `bl')])
                   [])
                  ")")])
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.subst "subst" [`b']) [] (Tactic.assumption "assumption")])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact
               "exact"
               (Term.app `trans [`ba (Term.app `rel_of_sorted_cons [`h₁ (Term.hole "_") `bl])]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact
               "exact"
               (Term.app `rel_of_sorted_cons [`h₂ (Term.hole "_") `bl']))])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          (Term.forall
           "∀"
           [(Term.explicitBinder "(" [`b'] [":" `α] [] ")")
            (Term.explicitBinder
             "("
             [(Term.hole "_")]
             [":" («term_∈_» `b' "∈" (Term.app `merge [`r («term_::_» `a "::" `l) `l']))]
             []
             ")")]
           []
           ","
           (Term.app `r [`b `b']))
          (Term.byTactic'
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest
                []
                []
                []
                [(Tactic.simpArgs
                  "["
                  [(Tactic.simpLemma [] [] `merge)
                   ","
                   (Tactic.simpLemma [] [] `h)
                   ","
                   (Tactic.simpLemma [] [] (Term.app `h₁.merge [`h₂.of_cons]))]
                  "]")]
                []))])))))
        []
        (Tactic.intro "intro" [`b' `bm])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`ba []]
           [(Term.typeSpec ":" (List.Data.List.Sort.«term_≼_» `b " ≼ " `a))]
           ":="
           (Term.app
            (Term.proj (Term.app `total_of [`r (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
            [`h]))))
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget
           []
           (Term.show
            "show"
            («term_∨_»
             («term_=_» `b' "=" `a)
             "∨"
             («term_∨_» («term_∈_» `b' "∈" `l) "∨" («term_∈_» `b' "∈" `l')))
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Std.Tactic.Simpa.simpa
                 "simpa"
                 []
                 []
                 (Std.Tactic.Simpa.simpaArgsRest
                  []
                  []
                  []
                  []
                  ["using"
                   (Term.app
                    (Term.proj
                     (Term.app `perm_merge [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                     "."
                     `Subset)
                    [`bm])]))])))))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.paren
              "("
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.one `be)
                 "|"
                 (Std.Tactic.RCases.rcasesPat.one `bl)
                 "|"
                 (Std.Tactic.RCases.rcasesPat.one `bl')])
               [])
              ")")])
           [])])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.subst "subst" [`b']) [] (Tactic.assumption "assumption")])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact
           "exact"
           (Term.app `trans [`ba (Term.app `rel_of_sorted_cons [`h₁ (Term.hole "_") `bl])]))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact "exact" (Term.app `rel_of_sorted_cons [`h₂ (Term.hole "_") `bl']))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `rel_of_sorted_cons [`h₂ (Term.hole "_") `bl']))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `rel_of_sorted_cons [`h₂ (Term.hole "_") `bl']))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `rel_of_sorted_cons [`h₂ (Term.hole "_") `bl'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bl'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rel_of_sorted_cons
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app `trans [`ba (Term.app `rel_of_sorted_cons [`h₁ (Term.hole "_") `bl])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `trans [`ba (Term.app `rel_of_sorted_cons [`h₁ (Term.hole "_") `bl])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `trans [`ba (Term.app `rel_of_sorted_cons [`h₁ (Term.hole "_") `bl])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `rel_of_sorted_cons [`h₁ (Term.hole "_") `bl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rel_of_sorted_cons
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `rel_of_sorted_cons [`h₁ (Term.hole "_") `bl])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ba
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.subst "subst" [`b']) [] (Tactic.assumption "assumption")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.assumption "assumption")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.subst "subst" [`b'])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.show
          "show"
          («term_∨_»
           («term_=_» `b' "=" `a)
           "∨"
           («term_∨_» («term_∈_» `b' "∈" `l) "∨" («term_∈_» `b' "∈" `l')))
          (Term.byTactic'
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest
                []
                []
                []
                []
                ["using"
                 (Term.app
                  (Term.proj
                   (Term.app `perm_merge [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                   "."
                   `Subset)
                  [`bm])]))])))))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.paren
            "("
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.one `be)
               "|"
               (Std.Tactic.RCases.rcasesPat.one `bl)
               "|"
               (Std.Tactic.RCases.rcasesPat.one `bl')])
             [])
            ")")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_∨_»
        («term_=_» `b' "=" `a)
        "∨"
        («term_∨_» («term_∈_» `b' "∈" `l) "∨" («term_∈_» `b' "∈" `l')))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             []
             []
             ["using"
              (Term.app
               (Term.proj
                (Term.app `perm_merge [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                "."
                `Subset)
               [`bm])]))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        []
        ["using"
         (Term.app
          (Term.proj
           (Term.app `perm_merge [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
           "."
           `Subset)
          [`bm])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app `perm_merge [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
        "."
        `Subset)
       [`bm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app `perm_merge [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
       "."
       `Subset)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `perm_merge [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `perm_merge
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `perm_merge [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_∨_»
       («term_=_» `b' "=" `a)
       "∨"
       («term_∨_» («term_∈_» `b' "∈" `l) "∨" («term_∈_» `b' "∈" `l')))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_» («term_∈_» `b' "∈" `l) "∨" («term_∈_» `b' "∈" `l'))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `b' "∈" `l')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `b'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 30 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 30, term))
      («term_∈_» `b' "∈" `l)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `b'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 31 >? 50, (some 51, term) <=? (some 30, term)
[PrettyPrinter.parenthesize] ...precedences are 30 >? 30, (some 30, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 30, term))
      («term_=_» `b' "=" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `b'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 31 >? 50, (some 51, term) <=? (some 30, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 30, (some 30,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`ba []]
         [(Term.typeSpec ":" (List.Data.List.Sort.«term_≼_» `b " ≼ " `a))]
         ":="
         (Term.app
          (Term.proj (Term.app `total_of [`r (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
          [`h]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `total_of [`r (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
       [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `total_of [`r (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `total_of [`r (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `total_of
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `total_of [`r (Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (List.Data.List.Sort.«term_≼_» `b " ≼ " `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'List.Data.List.Sort.«term_≼_»', expected 'List.Data.List.Sort.term_≼_._@.Data.List.Sort._hyg.14'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  Sorted.merge
  : ∀ { l l' : List α } , Sorted r l → Sorted r l' → Sorted r merge r l l'
  | [ ] , [ ] , h₁ , h₂ => by simp [ merge ]
    | [ ] , b :: l' , h₁ , h₂ => by simpa [ merge ] using h₂
    | a :: l , [ ] , h₁ , h₂ => by simpa [ merge ] using h₁
    |
      a :: l , b :: l' , h₁ , h₂
      =>
      by
        by_cases a ≼ b
          ·
            suffices
                ∀ ( b' : α ) ( _ : b' ∈ merge r l b :: l' ) , r a b'
                  by simpa [ merge , h , h₁.of_cons.merge h₂ ]
              intro b' bm
              rcases
                show
                  b' = b ∨ b' ∈ l ∨ b' ∈ l'
                  by simpa [ or_left_comm ] using perm_merge _ _ _ . Subset bm
                with ( be | bl | bl' )
              · subst b' assumption
              · exact rel_of_sorted_cons h₁ _ bl
              · exact trans h rel_of_sorted_cons h₂ _ bl'
          ·
            suffices
                ∀ ( b' : α ) ( _ : b' ∈ merge r a :: l l' ) , r b b'
                  by simpa [ merge , h , h₁.merge h₂.of_cons ]
              intro b' bm
              have ba : b ≼ a := total_of r _ _ . resolve_left h
              rcases
                show b' = a ∨ b' ∈ l ∨ b' ∈ l' by simpa using perm_merge _ _ _ . Subset bm
                with ( be | bl | bl' )
              · subst b' assumption
              · exact trans ba rel_of_sorted_cons h₁ _ bl
              · exact rel_of_sorted_cons h₂ _ bl'
#align list.sorted.merge List.Sorted.merge

variable (r)

theorem sorted_merge_sort : ∀ l : List α, Sorted r (mergeSort r l)
  | [] => by simp [merge_sort]
  | [a] => by simp [merge_sort]
  | a :: b :: l => by
    cases' e : split (a :: b :: l) with l₁ l₂
    cases' length_split_lt e with h₁ h₂
    rw [merge_sort_cons_cons r e]
    exact (sorted_merge_sort l₁).merge (sorted_merge_sort l₂)termination_by'
  ⟨_, InvImage.wf length Nat.lt_wfRel⟩
#align list.sorted_merge_sort List.sorted_merge_sort

theorem merge_sort_eq_self [IsAntisymm α r] {l : List α} : Sorted r l → mergeSort r l = l :=
  eq_of_perm_of_sorted (perm_merge_sort _ _) (sorted_merge_sort _ _)
#align list.merge_sort_eq_self List.merge_sort_eq_self

theorem merge_sort_eq_insertion_sort [IsAntisymm α r] (l : List α) :
    mergeSort r l = insertionSort r l :=
  eq_of_perm_of_sorted ((perm_merge_sort r l).trans (perm_insertion_sort r l).symm)
    (sorted_merge_sort r l) (sorted_insertion_sort r l)
#align list.merge_sort_eq_insertion_sort List.merge_sort_eq_insertion_sort

end TotalAndTransitive

end Correctness

@[simp]
theorem merge_sort_nil : [].mergeSort r = [] := by rw [List.mergeSort]
#align list.merge_sort_nil List.merge_sort_nil

@[simp]
theorem merge_sort_singleton (a : α) : [a].mergeSort r = [a] := by rw [List.mergeSort]
#align list.merge_sort_singleton List.merge_sort_singleton

end MergeSort

end Sort

-- try them out! 
--#eval insertion_sort (λ m n : ℕ, m ≤ n) [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12]
--#eval merge_sort     (λ m n : ℕ, m ≤ n) [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12]
end List

