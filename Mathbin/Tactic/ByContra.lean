import Mathbin.Tactic.Core 
import Mathbin.Tactic.PushNeg

/-!
# by_contra'

`by_contra'` is a tactic for proving propositions by contradiction.
It is similar to `by_contra` except that it also uses `push_neg` to normalize negations.
-/


namespace Tactic

namespace Interactive

setup_tactic_parser

/--
If the target of the main goal is a proposition `p`,
`by_contra'` reduces the goal to proving `false` using the additional hypothesis `h : ¬ p`.
`by_contra' h` can be used to name the hypothesis `h : ¬ p`.
The hypothesis `¬ p` will be negation normalized using `push_neg`.
For instance, `¬ a < b` will be changed to `b ≤ a`.
`by_contra' h : q` will normalize negations in `¬ p`, normalize negations in `q`,
and then check that the two normalized forms are equal.
The resulting hypothesis is the pre-normalized form, `q`.

If the name `h` is not explicitly provided, then `this` will be used as name.

This tactic uses classical reasoning.
It is a variant on the tactic `by_contra` (`tactic.interactive.by_contra`).

Examples:

```lean
example : 1 < 2 :=
begin
  by_contra' h,
  -- h : 2 ≤ 1 ⊢ false
end

example : 1 < 2 :=
begin
  by_contra' h : ¬ 1 < 2,
  -- h : ¬ 1 < 2 ⊢ false
end
```
-/
unsafe def by_contra' (h : parse (ident)?) (t : parse (tk ":" *> texpr)?) : tactic Unit :=
  do 
    let h := h.get_or_else `this 
    let tgt ← target 
    mk_mapp `classical.by_contradiction [some tgt] >>= tactic.eapply 
    let h₁ ← tactic.intro h 
    let t' ← infer_type h₁ 
    let (e', pr') ← push_neg.normalize_negations t' <|> refl_conv t' 
    match t with 
      | none => () <$ replace_hyp h₁ e' pr'
      | some t =>
        do 
          let t ← to_expr (pquote.1 (%%ₓt : Prop))
          let (e, pr) ← push_neg.normalize_negations t <|> refl_conv t 
          unify e e'
          () <$ (mk_eq_symm pr >>= mk_eq_trans pr' >>= replace_hyp h₁ t)

add_tactic_doc
  { Name := "by_contra'", category := DocCategory.tactic, declNames := [`tactic.interactive.by_contra'],
    tags := ["logic"] }

end Interactive

end Tactic

