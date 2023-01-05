/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module tactic.generalize_proofs
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.DocCommands

/-!
# `generalize_proofs`

A simple tactic to find and replace all occurrences of proof terms in the
context and goal with new variables.
-/


open Interactive Interactive.Types Lean.Parser

namespace Tactic

private unsafe def collect_proofs_in :
    expr → List expr → List Name × List expr → tactic (List Name × List expr)
  | e, ctx, (ns, hs) =>
    let go (tac : List Name × List expr → tactic (List Name × List expr)) :
      tactic (List Name × List expr) := do
      let t ← infer_type e
      condM (is_prop t)
          (do
            first
                  (hs fun h => do
                    let t' ← infer_type h
                    is_def_eq t t'
                    let g ← target
                    change <| g fun a n => if a = e then some h else none
                    return (ns, hs)) <|>
                (let (n, ns) :=
                    (match ns with
                      | [] => (`_x, [])
                      | n :: ns => (n, ns) :
                      Name × List Name)
                  do
                  generalize e n
                  let h ← intro n
                  return (ns, h :: hs)) <|>
                  return (ns, hs))
          (tac (ns, hs))
    match e with
    | expr.const _ _ => go return
    | expr.local_const _ _ _ _ => do
      let t ← infer_type e
      collect_proofs_in t ctx (ns, hs)
    | expr.mvar _ _ _ => do
      let e ← instantiate_mvars e
      match e with
        | expr.mvar _ _ _ => do
          let t ← infer_type e
          collect_proofs_in t ctx (ns, hs)
        | _ => collect_proofs_in e ctx (ns, hs)
    | expr.app f x => go fun nh => collect_proofs_in f ctx nh >>= collect_proofs_in x ctx
    | expr.lam n b d e =>
      go fun nh => do
        let nh ← collect_proofs_in d ctx nh
        let var ← mk_local' n b d
        collect_proofs_in (expr.instantiate_var e var) (var :: ctx) nh
    | expr.pi n b d e => do
      let nh ← collect_proofs_in d ctx (ns, hs)
      let var ← mk_local' n b d
      collect_proofs_in (expr.instantiate_var e var) (var :: ctx) nh
    | expr.elet n t d e =>
      go fun nh => do
        let nh ← collect_proofs_in t ctx nh
        let nh ← collect_proofs_in d ctx nh
        collect_proofs_in (expr.instantiate_var e d) ctx nh
    | expr.macro m l => go fun nh => foldlM (fun x e => collect_proofs_in e ctx x) nh l
    | _ => return (ns, hs)
#align tactic.collect_proofs_in tactic.collect_proofs_in

/-- Generalize proofs in the goal, naming them with the provided list. -/
unsafe def generalize_proofs (ns : List Name) (loc : Interactive.Loc) : tactic Unit := do
  intros_dep
  let hs ← local_context >>= filterM is_proof
  let n ← loc.get_locals >>= revert_lst
  let t ← target
  collect_proofs_in t [] (ns, hs)
  intron n <|> intros $> ()
#align tactic.generalize_proofs tactic.generalize_proofs

-- mathport name: parser.many
local postfix:1024 "*" => many

namespace Interactive

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Generalize proofs in the goal, naming them with the provided list.\n\nFor example:\n```lean\nexample : list.nth_le [1, 2] 1 dec_trivial = 2 :=\nbegin\n  -- ⊢ [1, 2].nth_le 1 _ = 2\n  generalize_proofs h,\n  -- h : 1 < [1, 2].length\n  -- ⊢ [1, 2].nth_le 1 h = 2\nend\n```\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `generalize_proofs [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app `parse [(Tactic.Tactic.GeneralizeProofs.parser.many `ident_ "*")])
          "→"
          (Term.arrow (Term.app `parse [`location]) "→" (Term.app `tactic [`Unit]))))])
      (Command.declValSimple ":=" `tactic.generalize_proofs [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tactic.generalize_proofs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app `parse [(Tactic.Tactic.GeneralizeProofs.parser.many `ident_ "*")])
       "→"
       (Term.arrow (Term.app `parse [`location]) "→" (Term.app `tactic [`Unit])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (Term.app `parse [`location]) "→" (Term.app `tactic [`Unit]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tactic [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `parse [`location])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `location
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `parse
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `parse [(Tactic.Tactic.GeneralizeProofs.parser.many `ident_ "*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.GeneralizeProofs.parser.many', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.GeneralizeProofs.parser.many', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.Tactic.GeneralizeProofs.parser.many `ident_ "*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.GeneralizeProofs.parser.many', expected 'Tactic.Tactic.GeneralizeProofs.parser.many._@.Tactic.GeneralizeProofs._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Generalize proofs in the goal, naming them with the provided list.
      
      For example:
      ```lean
      example : list.nth_le [1, 2] 1 dec_trivial = 2 :=
      begin
        -- ⊢ [1, 2].nth_le 1 _ = 2
        generalize_proofs h,
        -- h : 1 < [1, 2].length
        -- ⊢ [1, 2].nth_le 1 h = 2
      end
      ```
      -/
    unsafe
  def generalize_proofs : parse ident_ * → parse location → tactic Unit := tactic.generalize_proofs
#align tactic.interactive.generalize_proofs tactic.interactive.generalize_proofs

end Interactive

add_tactic_doc
  { Name := "generalize_proofs"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.generalize_proofs]
    tags := ["context management"] }

end Tactic

