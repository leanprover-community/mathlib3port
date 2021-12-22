import Mathbin.Order.CompleteLattice

namespace OldConv

open Tactic Monadₓ

unsafe instance : MonadFail old_conv :=
  { old_conv.monad with fail := fun α s => (fun r e => tactic.fail (to_fmt s) : old_conv α) }

unsafe instance : HasMonadLift tactic old_conv :=
  ⟨fun α => lift_tactic⟩

unsafe instance (α : Type) : Coe (tactic α) (old_conv α) :=
  ⟨monad_lift⟩

unsafe def current_relation : old_conv Name := fun r lhs => return ⟨r, lhs, none⟩

unsafe def head_beta : old_conv Unit := fun r e => do
  let n ← tactic.head_beta e
  return ⟨(), n, none⟩

unsafe def congr_argₓ : old_conv Unit → old_conv Unit :=
  congr_core (return ())

unsafe def congr_funₓ : old_conv Unit → old_conv Unit := fun c => congr_core c (return ())

unsafe def congr_rule (congr : expr) (cs : List (List expr → old_conv Unit)) : old_conv Unit := fun r lhs => do
  let meta_rhs ← infer_type lhs >>= mk_meta_var
  let t ← mk_app r [lhs, meta_rhs]
  let ((), meta_pr) ←
    solve_aux t do
        apply congr
        focus $
            cs.map $ fun c => do
              let xs ← intros
              conversion (head_beta >> c xs)
        done
  let rhs ← instantiate_mvars meta_rhs
  let pr ← instantiate_mvars meta_pr
  return ⟨(), rhs, some pr⟩

unsafe def congr_binder (congr : Name) (cs : expr → old_conv Unit) : old_conv Unit := do
  let e ← mk_const congr
  congr_rule e
      [fun bs => do
        let [b] ← return bs
        cs b]

unsafe def funext' : (expr → old_conv Unit) → old_conv Unit :=
  congr_binder `` _root_.funext

unsafe def propext' {α : Type} (c : old_conv α) : old_conv α := fun r lhs =>
  (do
      guardₓ (r = `iff)
      c r lhs) <|>
    do
    guardₓ (r = `eq)
    let ⟨res, rhs, pr⟩ ← c `iff lhs
    match pr with
      | some pr => return ⟨res, rhs, (expr.const `propext [] : expr) lhs rhs pr⟩
      | none => return ⟨res, rhs, none⟩

unsafe def apply (pr : expr) : old_conv Unit := fun r e => do
  let sl ← simp_lemmas.mk.add pr
  apply_lemmas sl r e

unsafe def applyc (n : Name) : old_conv Unit := fun r e => do
  let sl ← simp_lemmas.mk.add_simp n
  apply_lemmas sl r e

unsafe def apply' (n : Name) : old_conv Unit := do
  let e ← mk_const n
  congr_rule e []

end OldConv

open Expr Tactic OldConv

unsafe structure binder_eq_elim where
  match_binder : expr → tactic (expr × expr)
  adapt_rel : old_conv Unit → old_conv Unit
  apply_comm : old_conv Unit
  apply_congr : (expr → old_conv Unit) → old_conv Unit
  apply_elim_eq : old_conv Unit

unsafe def binder_eq_elim.check_eq (b : binder_eq_elim) (x : expr) : expr → tactic Unit
  | quote.1 (@Eq (%%ₓβ) (%%ₓl) (%%ₓr)) => guardₓ (l = x ∧ ¬x.occurs r ∨ r = x ∧ ¬x.occurs l)
  | _ => fail "no match"

unsafe def binder_eq_elim.pull (b : binder_eq_elim) (x : expr) : old_conv Unit := do
  let (β, f) ← lhs >>= lift_tactic ∘ b.match_binder
  guardₓ ¬x.occurs β <|>
      b.check_eq x β <|> do
        b.apply_congr $ fun x => binder_eq_elim.pull
        b.apply_comm

unsafe def binder_eq_elim.push (b : binder_eq_elim) : old_conv Unit :=
  b.apply_elim_eq <|>
    (do
        b.apply_comm
        b.apply_congr $ fun x => binder_eq_elim.push) <|>
      do
      b.apply_congr $ b.pull
      binder_eq_elim.push

unsafe def binder_eq_elim.check (b : binder_eq_elim) (x : expr) : expr → tactic Unit
  | e => do
    let (β, f) ← b.match_binder e
    b.check_eq x β <|> do
        let lam n bi d bd ← return f
        let x ← mk_local' n bi d
        binder_eq_elim.check $ bd.instantiate_var x

unsafe def binder_eq_elim.old_conv (b : binder_eq_elim) : old_conv Unit := do
  let (β, f) ← lhs >>= lift_tactic ∘ b.match_binder
  let lam n bi d bd ← return f
  let x ← mk_local' n bi d
  b.check x (bd.instantiate_var x)
  b.adapt_rel b.push

theorem exists_elim_eq_left.{u, v} {α : Sort u} (a : α) (p : ∀ a' : α, a' = a → Prop) :
    (∃ (a' : α)(h : a' = a), p a' h) ↔ p a rfl :=
  ⟨fun ⟨a', ⟨h, p_h⟩⟩ =>
    match a', h, p_h with
    | _, rfl, h => h,
    fun h => ⟨a, rfl, h⟩⟩

theorem exists_elim_eq_right.{u, v} {α : Sort u} (a : α) (p : ∀ a' : α, a = a' → Prop) :
    (∃ (a' : α)(h : a = a'), p a' h) ↔ p a rfl :=
  ⟨fun ⟨a', ⟨h, p_h⟩⟩ =>
    match a', h, p_h with
    | _, rfl, h => h,
    fun h => ⟨a, rfl, h⟩⟩

unsafe def exists_eq_elim : binder_eq_elim :=
  { match_binder := fun e => do
      let quote.1 (@Exists (%%ₓβ) (%%ₓf)) ← return e
      return (β, f),
    adapt_rel := propext', apply_comm := applyc `` exists_comm, apply_congr := congr_binder `` exists_congr,
    apply_elim_eq := apply' `` exists_elim_eq_left <|> apply' `` exists_elim_eq_right }

theorem forall_comm.{u, v} {α : Sort u} {β : Sort v} (p : α → β → Prop) : (∀ a b, p a b) ↔ ∀ b a, p a b :=
  ⟨fun h b a => h a b, fun h b a => h a b⟩

theorem forall_elim_eq_left.{u, v} {α : Sort u} (a : α) (p : ∀ a' : α, a' = a → Prop) :
    (∀ a' : α h : a' = a, p a' h) ↔ p a rfl :=
  ⟨fun h => h a rfl, fun h a' h_eq =>
    match a', h_eq with
    | _, rfl => h⟩

theorem forall_elim_eq_right.{u, v} {α : Sort u} (a : α) (p : ∀ a' : α, a = a' → Prop) :
    (∀ a' : α h : a = a', p a' h) ↔ p a rfl :=
  ⟨fun h => h a rfl, fun h a' h_eq =>
    match a', h_eq with
    | _, rfl => h⟩

unsafe def forall_eq_elim : binder_eq_elim :=
  { match_binder := fun e => do
      let expr.pi n bi d bd ← return e
      return (d, expr.lam n bi d bd),
    adapt_rel := propext', apply_comm := applyc `` forall_comm, apply_congr := congr_binder `` forall_congrₓ,
    apply_elim_eq := apply' `` forall_elim_eq_left <|> apply' `` forall_elim_eq_right }

unsafe def supr_eq_elim : binder_eq_elim :=
  { match_binder := fun e => do
      let quote.1 (@supr (%%ₓα) (%%ₓcl) (%%ₓβ) (%%ₓf)) ← return e
      return (β, f),
    adapt_rel := fun c => do
      let r ← current_relation
      guardₓ (r = `eq)
      c,
    apply_comm := applyc `` supr_comm, apply_congr := congr_argₓ ∘ funext',
    apply_elim_eq := applyc `` supr_supr_eq_left <|> applyc `` supr_supr_eq_right }

unsafe def infi_eq_elim : binder_eq_elim :=
  { match_binder := fun e => do
      let quote.1 (@infi (%%ₓα) (%%ₓcl) (%%ₓβ) (%%ₓf)) ← return e
      return (β, f),
    adapt_rel := fun c => do
      let r ← current_relation
      guardₓ (r = `eq)
      c,
    apply_comm := applyc `` infi_comm, apply_congr := congr_argₓ ∘ funext',
    apply_elim_eq := applyc `` infi_infi_eq_left <|> applyc `` infi_infi_eq_right }

universe u v w w₂

variable {α : Type u} {β : Type v} {ι : Sort w} {ι₂ : Sort w₂} {s t : Set α} {a : α}

section

variable [CompleteLattice α]

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (a «expr ∈ » s)
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.example
  "example"
  (Command.declSig
   [(Term.implicitBinder "{" [`s] [":" (Term.app `Set [`β])] "}")
    (Term.implicitBinder "{" [`f] [":" (Term.arrow `β "→" `α)] "}")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `Inf [(Term.app `Set.Image [`f `s])])
     "="
     (Order.CompleteLattice.«term⨅_,_»
      "⨅"
      (Lean.explicitBinders
       [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `a)] ":" (Term.hole "_") ")")
        (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `a " ∈ " `s) ")")])
      ", "
      (Term.app `f [`a])))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.simp
         "simp"
         []
         []
         ["[" [(Tactic.simpLemma [] [] `Inf_eq_infi) "," (Tactic.simpLemma [] [] `infi_and)] "]"]
         [])
        [])
       (group
        (Mathlib.RunTac.tacticRun_tac_
         "run_tac"
         (Term.doSeqIndent
          [(Term.doSeqItem (Term.doExpr (Term.app `conversion [(Term.proj `infi_eq_elim "." `old_conv)])) [])]))
        [])])))
   [])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        []
        ["[" [(Tactic.simpLemma [] [] `Inf_eq_infi) "," (Tactic.simpLemma [] [] `infi_and)] "]"]
        [])
       [])
      (group
       (Mathlib.RunTac.tacticRun_tac_
        "run_tac"
        (Term.doSeqIndent
         [(Term.doSeqItem (Term.doExpr (Term.app `conversion [(Term.proj `infi_eq_elim "." `old_conv)])) [])]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Mathlib.RunTac.tacticRun_tac_
   "run_tac"
   (Term.doSeqIndent
    [(Term.doSeqItem (Term.doExpr (Term.app `conversion [(Term.proj `infi_eq_elim "." `old_conv)])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.RunTac.tacticRun_tac_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqIndent.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqItem', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqItem', expected 'Lean.Parser.Term.doSeqItem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doExpr', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doExpr', expected 'Lean.Parser.Term.doExpr.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `conversion [(Term.proj `infi_eq_elim "." `old_conv)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `infi_eq_elim "." `old_conv)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `infi_eq_elim
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `conversion
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `Inf_eq_infi) "," (Tactic.simpLemma [] [] `infi_and)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `infi_and
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Inf_eq_infi
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app `Inf [(Term.app `Set.Image [`f `s])])
   "="
   (Order.CompleteLattice.«term⨅_,_»
    "⨅"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `a)] ":" (Term.hole "_") ")")
      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `a " ∈ " `s) ")")])
    ", "
    (Term.app `f [`a])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.CompleteLattice.«term⨅_,_»
   "⨅"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `a)] ":" (Term.hole "_") ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `a " ∈ " `s) ")")])
   ", "
   (Term.app `f [`a]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨅_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
example
  { s : Set β } { f : β → α } : Inf Set.Image f s = ⨅ ( a : _ ) ( _ : a ∈ s ) , f a
  := by simp [ Inf_eq_infi , infi_and ] run_tac conversion infi_eq_elim . old_conv

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (a «expr ∈ » s)
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.example
  "example"
  (Command.declSig
   [(Term.implicitBinder "{" [`s] [":" (Term.app `Set [`β])] "}")
    (Term.implicitBinder "{" [`f] [":" (Term.arrow `β "→" `α)] "}")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `Sup [(Term.app `Set.Image [`f `s])])
     "="
     (Order.CompleteLattice.«term⨆_,_»
      "⨆"
      (Lean.explicitBinders
       [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `a)] ":" (Term.hole "_") ")")
        (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `a " ∈ " `s) ")")])
      ", "
      (Term.app `f [`a])))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.simp
         "simp"
         []
         []
         ["[" [(Tactic.simpLemma [] [] `Sup_eq_supr) "," (Tactic.simpLemma [] [] `supr_and)] "]"]
         [])
        [])
       (group
        (Mathlib.RunTac.tacticRun_tac_
         "run_tac"
         (Term.doSeqIndent
          [(Term.doSeqItem (Term.doExpr (Term.app `conversion [(Term.proj `supr_eq_elim "." `old_conv)])) [])]))
        [])])))
   [])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        []
        ["[" [(Tactic.simpLemma [] [] `Sup_eq_supr) "," (Tactic.simpLemma [] [] `supr_and)] "]"]
        [])
       [])
      (group
       (Mathlib.RunTac.tacticRun_tac_
        "run_tac"
        (Term.doSeqIndent
         [(Term.doSeqItem (Term.doExpr (Term.app `conversion [(Term.proj `supr_eq_elim "." `old_conv)])) [])]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Mathlib.RunTac.tacticRun_tac_
   "run_tac"
   (Term.doSeqIndent
    [(Term.doSeqItem (Term.doExpr (Term.app `conversion [(Term.proj `supr_eq_elim "." `old_conv)])) [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.RunTac.tacticRun_tac_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqIndent.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqItem', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqItem', expected 'Lean.Parser.Term.doSeqItem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doExpr', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doExpr', expected 'Lean.Parser.Term.doExpr.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `conversion [(Term.proj `supr_eq_elim "." `old_conv)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `supr_eq_elim "." `old_conv)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `supr_eq_elim
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `conversion
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `Sup_eq_supr) "," (Tactic.simpLemma [] [] `supr_and)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `supr_and
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Sup_eq_supr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app `Sup [(Term.app `Set.Image [`f `s])])
   "="
   (Order.CompleteLattice.«term⨆_,_»
    "⨆"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `a)] ":" (Term.hole "_") ")")
      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `a " ∈ " `s) ")")])
    ", "
    (Term.app `f [`a])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.CompleteLattice.«term⨆_,_»
   "⨆"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `a)] ":" (Term.hole "_") ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `a " ∈ " `s) ")")])
   ", "
   (Term.app `f [`a]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨆_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.example', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
example
  { s : Set β } { f : β → α } : Sup Set.Image f s = ⨆ ( a : _ ) ( _ : a ∈ s ) , f a
  := by simp [ Sup_eq_supr , supr_and ] run_tac conversion supr_eq_elim . old_conv

end

