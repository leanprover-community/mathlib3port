import Mathbin.Tactic.Explode 
import Mathbin.Tactic.InteractiveExpr

/-!
# `#explode_widget` command

Render a widget that displays an `#explode` proof, providing more
interactivity such as jumping to definitions and exploding constants
occurring in the exploded proofs.
-/


open Widget Tactic Tactic.Explode

unsafe instance widget.string_to_html {α} : Coe Stringₓ (html α) :=
  ⟨fun s => s⟩

namespace Tactic

namespace ExplodeWidget

open WidgetOverride.InteractiveExpression

open TaggedFormat

open Widget.Html Widget.Attr

/-- Redefine some of the style attributes for better formatting. -/
unsafe def get_block_attrs {γ} : sf → tactic (sf × List (attr γ))
| sf.block i a =>
  do 
    let s : attr γ := style [("display", "inline-block"), ("white-space", "pre-wrap"), ("vertical-align", "top")]
    let (a, rest) ← get_block_attrs a 
    pure (a, s :: rest)
| sf.highlight c a =>
  do 
    let (a, rest) ← get_block_attrs a 
    pure (a, cn c.to_string :: rest)
| a => pure (a, [])

/-- Explode button for subsequent exploding. -/
unsafe def insert_explode {γ} : expr → tactic (List (html (action γ)))
| expr.const n _ =>
  (do 
      pure$
          [h "button"
              [cn "pointer ba br3 mr1",
                on_click fun _ => action.effect$ widget.effect.insert_text ("#explode_widget " ++ n.to_string),
                attr.val "title" "explode"]
              ["💥"]]) <|>
    pure []
| e => pure []

/--
Render a subexpression as a list of html elements.
-/
unsafe def view {γ} (tooltip_component : Tc subexpr (action γ)) (click_address : Option Expr.Address)
  (select_address : Option Expr.Address) : subexpr → sf → tactic (List (html (action γ)))
| ⟨ce, current_address⟩, sf.tag_expr ea e m =>
  do 
    let new_address := current_address ++ ea 
    let select_attrs : List (attr (action γ)) :=
      if some new_address = select_address then [className "highlight"] else []
    let click_attrs : List (attr (action γ)) ←
      if some new_address = click_address then
          do 
            let content ← tc.to_html tooltip_component (e, new_address)
            let efmt : Stringₓ ← format.to_string <$> tactic.pp e 
            let gd_btn ← goto_def_button e 
            let epld_btn ← insert_explode e 
            pure
                [tooltip$
                    h "div" []
                      [h "div" [cn "fr"]
                          (gd_btn ++ epld_btn ++
                            [h "button"
                                [cn "pointer ba br3 mr1", on_click fun _ => action.effect$ widget.effect.copy_text efmt,
                                  attr.val "title" "copy expression to clipboard"]
                                ["📋"],
                              h "button"
                                [cn "pointer ba br3", on_click fun _ => action.on_close_tooltip,
                                  attr.val "title" "close"]
                                ["×"]]),
                        content]]
        else pure []
    let (m, block_attrs) ← get_block_attrs m 
    let as := [className "expr-boundary", key ea] ++ select_attrs ++ click_attrs ++ block_attrs 
    let inner ← view (e, new_address) m 
    pure [h "span" as inner]
| ca, sf.compose x y => pure (· ++ ·) <*> view ca x <*> view ca y
| ca, sf.of_string s =>
  pure
    [h "span" [on_mouse_enter fun _ => action.on_mouse_enter ca, on_click fun _ => action.on_click ca, key s]
        [html.of_string s]]
| ca, b@(sf.block _ _) =>
  do 
    let (a, attrs) ← get_block_attrs b 
    let inner ← view ca a 
    pure [h "span" attrs inner]
| ca, b@(sf.highlight _ _) =>
  do 
    let (a, attrs) ← get_block_attrs b 
    let inner ← view ca a 
    pure [h "span" attrs inner]

-- error in Tactic.ExplodeWidget: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Make an interactive expression. -/ meta def mk {γ} (tooltip : tc subexpr γ) : tc expr γ :=
let tooltip_comp := «expr $ »(component.with_should_update (λ
      x
      y : «expr × »(tactic_state, «expr × »(expr, expr.address)), «expr ≠ »(x.2.2, y.2.2)), component.map_action action.on_tooltip_action tooltip) in
«expr $ »(component.filter_map_action (λ
  (_)
  (a : «expr ⊕ »(γ, widget.effect)), sum.cases_on a some (λ
   _, none)), «expr $ »(component.with_effects (λ (_) (a : «expr ⊕ »(γ, widget.effect)), match a with
   | sum.inl g := «expr[ , ]»([])
   | sum.inr s := «expr[ , ]»([s])
   end), tc.mk_simple (action γ) «expr × »(option subexpr, option subexpr) (λ
   e, «expr $ »(pure, (none, none))) (λ (e) ⟨ca, sa⟩ (act), «expr $ »(pure, match act with
    | action.on_mouse_enter ⟨e, ea⟩ := ((ca, some (e, ea)), none)
    | action.on_mouse_leave_all := ((ca, none), none)
    | action.on_click ⟨e, ea⟩ := if «expr = »(some (e, ea), ca) then ((none, sa), none) else ((some (e, ea), sa), none)
    | action.on_tooltip_action g := ((none, sa), «expr $ »(some, sum.inl g))
    | action.on_close_tooltip := ((none, sa), none)
    | action.effect e := ((ca, sa), «expr $ »(some, «expr $ »(sum.inr, e)))
    end)) (λ (e) ⟨ca, sa⟩, do {
   m ← «expr <$> »(sf.of_eformat, tactic.pp_tagged e),
     let m := m.elim_part_apps,
     let m := m.flatten,
     let m := m.tag_expr «expr[ , ]»([]) e,
     v ← view tooltip_comp «expr <$> »(prod.snd, ca) «expr <$> »(prod.snd, sa) ⟨e, «expr[ , ]»([])⟩ m,
     «expr $ »(pure, «expr[ , ]»([«expr $ »(h "span" «expr[ , ]»([className "expr", key e.hash, on_mouse_leave (λ
            _, action.on_mouse_leave_all)]), v)])) })))

/-- Render the implicit arguments for an expression in fancy, little pills. -/
unsafe def implicit_arg_list (tooltip : Tc subexpr Empty) (e : expr) : tactic$ html Empty :=
  do 
    let fn ← mk tooltip$ expr.get_app_fn e 
    let args ← List.mmap (mk tooltip)$ expr.get_app_args e 
    pure$
        h "div" []
          (h "span" [className "bg-blue br3 ma1 ph2 white"] [fn] ::
            List.map (fun a => h "span" [className "bg-gray br3 ma1 ph2 white"] [a]) args)

/--
Component for the type tooltip.
-/
unsafe def type_tooltip : Tc subexpr Empty :=
  tc.stateless
    fun ⟨e, ea⟩ =>
      do 
        let y ← tactic.infer_type e 
        let y_comp ← mk type_tooltip y 
        let implicit_args ← implicit_arg_list type_tooltip e 
        pure [h "div" [style [("minWidth", "12rem")]] [h "div" [cn "pl1"] [y_comp], h "hr" [] [], implicit_args]]

/--
Component that shows a type.
-/
unsafe def show_type_component : Tc expr Empty :=
  tc.stateless
    fun x =>
      do 
        let y ← infer_type x 
        let y_comp ← mk type_tooltip$ y 
        pure y_comp

/--
Component that shows a constant.
-/
unsafe def show_constant_component : Tc expr Empty :=
  tc.stateless
    fun x =>
      do 
        let y_comp ← mk type_tooltip x 
        pure y_comp

/--
Search for an entry that has the specified line number.
-/
unsafe def lookup_lines : entries → Nat → entry
| ⟨_, []⟩, n => ⟨default _, 0, 0, status.sintro, thm.string "", []⟩
| ⟨rb, hd :: tl⟩, n => if hd.line = n then hd else lookup_lines ⟨rb, tl⟩ n

/--
Render a row that shows a goal.
-/
unsafe def goal_row (e : expr) (show_expr := tt) : tactic (List (html Empty)) :=
  do 
    let t ← explode_widget.show_type_component e 
    return$
        [h "td" [cn "ba bg-dark-green tc"] "Goal",
          h "td" [cn "ba tc"] (if show_expr then [html.of_name e.local_pp_name, " : ", t] else t)]

/--
Render a row that shows the ID of a goal.
-/
unsafe def id_row {γ} (l : Nat) : tactic (List (html γ)) :=
  return$ [h "td" [cn "ba bg-dark-green tc"] "ID", h "td" [cn "ba tc"] (toString l)]

/--
Render a row that shows the rule or theorem being applied.
-/
unsafe def rule_row : thm → tactic (List (html Empty))
| thm.expr e =>
  do 
    let t ← explode_widget.show_constant_component e 
    return$ [h "td" [cn "ba bg-dark-green tc"] "Rule", h "td" [cn "ba tc"] t]
| t => return$ [h "td" [cn "ba bg-dark-green tc"] "Rule", h "td" [cn "ba tc"] t.to_string]

/--
Render a row that contains the sub-proofs, i.e., the proofs of the
arguments.
-/
unsafe def proof_row {γ} (args : List (html γ)) : List (html γ) :=
  [h "td" [cn "ba bg-dark-green tc"] "Proofs",
    h "td" [cn "ba tc"] [h "details" []$ h "summary" [attr.style [("color", "orange")]] "Details" :: args]]

/--
Combine the goal row, id row, rule row and proof row to make them a table.
-/
unsafe def assemble_table {γ} gr ir rr : List (html γ) → html γ
| [] => h "table" [cn "collapse"] [h "tbody" [] [h "tr" [] gr, h "tr" [] ir, h "tr" [] rr]]
| pr => h "table" [cn "collapse"] [h "tbody" [] [h "tr" [] gr, h "tr" [] ir, h "tr" [] rr, h "tr" [] pr]]

/--
Render a table for a given entry.
-/
unsafe def assemble (es : entries) : entry → tactic (html Empty)
| ⟨e, l, d, status.sintro, t, ref⟩ =>
  do 
    let gr ← goal_row e 
    let ir ← id_row l 
    let rr ← rule_row$ thm.string "Assumption"
    return$ assemble_table gr ir rr []
| ⟨e, l, d, status.intro, t, ref⟩ =>
  do 
    let gr ← goal_row e 
    let ir ← id_row l 
    let rr ← rule_row$ thm.string "Assumption"
    return$ assemble_table gr ir rr []
| ⟨e, l, d, st, t, ref⟩ =>
  do 
    let gr ← goal_row e ff 
    let ir ← id_row l 
    let rr ← rule_row t 
    let el : List entry := List.map (lookup_lines es) ref 
    let ls ← Monadₓ.mapm assemble el 
    let pr := proof_row$ ls.intersperse (h "br" [] [])
    return$ assemble_table gr ir rr pr

/--
Render a widget from given entries.
-/
unsafe def explode_component (es : entries) : tactic (html Empty) :=
  let concl := lookup_lines es (es.l.length - 1)
  assemble es concl

/--
Explode a theorem and return entries.
-/
unsafe def explode_entries (n : Name) (hide_non_prop := tt) : tactic entries :=
  do 
    let expr.const n _ ← resolve_name n | fail "cannot resolve name"
    let d ← get_decl n 
    let v ←
      match d with 
        | declaration.defn _ _ _ v _ _ => return v
        | declaration.thm _ _ _ v => return v.get
        | _ => fail "not a definition"
    let t ← pp d.type 
    explode_expr v hide_non_prop

end ExplodeWidget

open ExplodeWidget

setup_tactic_parser

/--
User command of the explode widget.
-/
@[user_command]
unsafe def explode_widget_cmd (_ : parse$ tk "#explode_widget") : lean.parser Unit :=
  do 
    let ⟨li, co⟩ ← cur_pos 
    let n ← ident 
    let es ← explode_entries n 
    let comp ←
      parser.of_tactic
          do 
            let html ← explode_component es 
            let c ← pure$ component.stateless fun _ => [html]
            pure$ component.ignore_props$ component.ignore_action$ c 
    save_widget ⟨li, co - "#explode_widget".length - 1⟩ comp 
    trace "successfully rendered widget"
    skip

end Tactic

