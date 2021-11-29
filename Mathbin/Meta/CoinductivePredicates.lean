import Mathbin.Tactic.Core

section 

universe u

@[user_attribute]
unsafe def monotonicity : user_attribute :=
  { Name := `monotonicity, descr := "Monotonicity rules for predicates" }

theorem Monotonicity.pi {α : Sort u} {p q : α → Prop} (h : ∀ a, Implies (p a) (q a)) : Implies (∀ a, p a) (∀ a, q a) :=
  fun h' a => h a (h' a)

theorem Monotonicity.imp {p p' q q' : Prop} (h₁ : Implies p' q') (h₂ : Implies q p) : Implies (p → p') (q → q') :=
  fun h => h₁ ∘ h ∘ h₂

@[monotonicity]
theorem Monotonicity.const (p : Prop) : Implies p p :=
  id

@[monotonicity]
theorem Monotonicity.true (p : Prop) : Implies p True :=
  fun _ => trivialₓ

@[monotonicity]
theorem Monotonicity.false (p : Prop) : Implies False p :=
  False.elim

@[monotonicity]
theorem Monotonicity.exists {α : Sort u} {p q : α → Prop} (h : ∀ a, Implies (p a) (q a)) :
  Implies (∃ a, p a) (∃ a, q a) :=
  exists_imp_exists h

@[monotonicity]
theorem Monotonicity.and {p p' q q' : Prop} (hp : Implies p p') (hq : Implies q q') : Implies (p ∧ q) (p' ∧ q') :=
  And.imp hp hq

@[monotonicity]
theorem Monotonicity.or {p p' q q' : Prop} (hp : Implies p p') (hq : Implies q q') : Implies (p ∨ q) (p' ∨ q') :=
  Or.imp hp hq

@[monotonicity]
theorem Monotonicity.not {p q : Prop} (h : Implies p q) : Implies (¬q) ¬p :=
  mt h

end 

namespace Tactic

open Expr Tactic

private unsafe def mono_aux (ns : List Name) (hs : List expr) : tactic Unit :=
  do 
    intros
    (do 
          let quote.1 (Implies (%%ₓp) (%%ₓq)) ← target
          (do 
                is_def_eq p q 
                eapplyc `monotone.const) <|>
              do 
                let expr.pi pn pbi pd pb ← whnf p 
                let expr.pi qn qbi qd qb ← whnf q 
                let sort u ← infer_type pd
                (do 
                      is_def_eq pd qd 
                      let p' := expr.lam pn pbi pd pb 
                      let q' := expr.lam qn qbi qd qb 
                      eapply ((const `monotonicity.pi [u] : expr) pd p' q')
                      skip) <|>
                    do 
                      guardₓ$ u = level.zero ∧ is_arrow p ∧ is_arrow q 
                      let p' := pb.lower_vars 0 1
                      let q' := qb.lower_vars 0 1 
                      eapply ((const `monotonicity.imp [] : expr) pd p' qd q')
                      skip) <|>
        first
            (hs.map$ fun h => apply_core h { md := transparency.none, NewGoals := new_goals.non_dep_only } >> skip) <|>
          first
            (ns.map$
              fun n =>
                do 
                  let c ← mk_const n 
                  apply_core c { md := transparency.none, NewGoals := new_goals.non_dep_only }
                  skip)
    all_goals' mono_aux

unsafe def mono (e : expr) (hs : List expr) : tactic Unit :=
  do 
    let t ← target 
    let t' ← infer_type e 
    let ns ← attribute.get_instances `monotonicity 
    let ((), p) ← solve_aux (quote.1 (Implies (%%ₓt') (%%ₓt))) (mono_aux ns hs)
    exact (p e)

end Tactic

namespace Tactic

open Level Expr Tactic

namespace AddCoinductivePredicate

unsafe structure coind_rule : Type where 
  orig_nm : Name 
  func_nm : Name 
  type : expr 
  loc_type : expr 
  args : List expr 
  loc_args : List expr 
  concl : expr 
  insts : List expr

unsafe structure coind_pred : Type where 
  u_names : List Name 
  params : List expr 
  pd_name : Name 
  type : expr 
  intros : List coind_rule 
  locals : List expr
  (f₁ f₂ : expr)
  u_f : level

namespace CoindPred

unsafe def u_params (pd : coind_pred) : List level :=
  pd.u_names.map param

unsafe def f₁_l (pd : coind_pred) : expr :=
  pd.f₁.app_of_list pd.locals

unsafe def f₂_l (pd : coind_pred) : expr :=
  pd.f₂.app_of_list pd.locals

unsafe def pred (pd : coind_pred) : expr :=
  const pd.pd_name pd.u_params

unsafe def func (pd : coind_pred) : expr :=
  const (pd.pd_name ++ "functional") pd.u_params

unsafe def func_g (pd : coind_pred) : expr :=
  pd.func.app_of_list$ pd.params

unsafe def pred_g (pd : coind_pred) : expr :=
  pd.pred.app_of_list$ pd.params

unsafe def impl_locals (pd : coind_pred) : List expr :=
  pd.locals.map to_implicit_binder

unsafe def impl_params (pd : coind_pred) : List expr :=
  pd.params.map to_implicit_binder

unsafe def le (pd : coind_pred) (f₁ f₂ : expr) : expr :=
  (imp (f₁.app_of_list pd.locals) (f₂.app_of_list pd.locals)).pis pd.impl_locals

unsafe def corec_functional (pd : coind_pred) : expr :=
  const (pd.pd_name ++ "corec_functional") pd.u_params

unsafe def mono (pd : coind_pred) : expr :=
  const (pd.func.const_name ++ "mono") pd.u_params

unsafe def rec' (pd : coind_pred) : tactic expr :=
  do 
    let c := pd.func.const_name ++ "rec"
    let env ← get_env 
    let decl ← env.get c 
    let num := decl.univ_params.length 
    return (const c$ if num = pd.u_params.length then pd.u_params else level.zero :: pd.u_params)

unsafe def construct (pd : coind_pred) : expr :=
  const (pd.pd_name ++ "construct") pd.u_params

unsafe def destruct (pd : coind_pred) : expr :=
  const (pd.pd_name ++ "destruct") pd.u_params

unsafe def add_theorem (pd : coind_pred) (n : Name) (type : expr) (tac : tactic Unit) : tactic expr :=
  add_theorem_by n pd.u_names type tac

end CoindPred

end AddCoinductivePredicate

open AddCoinductivePredicate

-- error in Meta.CoinductivePredicates: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- compact_relation bs as_ps: Product a relation of the form:
  R := λ as, ∃ bs, Λ_i a_i = p_i[bs]
This relation is user visible, so we compact it by removing each `b_j` where a `p_i = b_j`, and
hence `a_i = b_j`. We need to take care when there are `p_i` and `p_j` with `p_i = p_j = b_k`. -/
meta
def compact_relation : list expr → list «expr × »(expr, expr) → «expr × »(list expr, list «expr × »(expr, expr))
| «expr[ , ]»([]), ps := («expr[ , ]»([]), ps)
| list.cons b bs, ps := match ps.span (λ ap : «expr × »(expr, expr), «expr¬ »(«expr =ₐ »(ap.2, b))) with
| (_, «expr[ , ]»([])) := let (bs, ps) := compact_relation bs ps in
(«expr :: »(b, bs), ps)
| (ps₁, list.cons (a, _) ps₂) := let i := a.instantiate_local b.local_uniq_name in
compact_relation (bs.map i) («expr ++ »(ps₁, ps₂).map (λ ⟨a, p⟩, (a, i p)))
end

-- error in Meta.CoinductivePredicates: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
meta
def add_coinductive_predicate
(u_names : list name)
(params : list expr)
(preds : «expr $ »(list, «expr × »(expr, list expr))) : exprcommand() :=
do {
let params_names := params.map local_pp_name,
  let u_params := u_names.map param,
  pre_info ← preds.mmap (λ ⟨c, is⟩, do {
   (ls, t) ← open_pis c.local_type,
     «expr <|> »(is_def_eq t (`(exprProp())), fail «expr ++ »(«exprformat! »(format_macro "Type of {c.local_pp_name} is not Prop. Currently only " [[expr c.local_pp_name]]), "coinductive predicates are supported.")),
     let n := if «expr = »(preds.length, 1) then "" else «expr ++ »("_", c.local_pp_name.last_string),
     f₁ ← mk_local_def «expr $ »(mk_simple_name, «expr ++ »("C", n)) c.local_type,
     f₂ ← mk_local_def «expr $ »(mk_simple_name, «expr ++ »("C₂", n)) c.local_type,
     return (ls, (f₁, f₂)) }),
  let fs := pre_info.map prod.snd,
  let fs₁ := fs.map prod.fst,
  let fs₂ := fs.map prod.snd,
  pds ← (preds.zip pre_info).mmap (λ ⟨⟨c, is⟩, ls, f₁, f₂⟩, do {
   sort u_f ← «expr >>= »(infer_type f₁, infer_type),
     let pred_g := λ c : expr, (const c.local_uniq_name u_params : expr).app_of_list params,
     intros ← is.mmap (λ i, do {
      (args, t') ← open_pis i.local_type,
        name.mk_string sub p ← return i.local_uniq_name,
        let loc_args := «expr $ »(args.map, λ
         e, (fs₁.zip preds).foldl (λ (e : expr) ⟨f, c, _⟩, e.replace_with (pred_g c) f) e),
        let t' := t'.replace_with (pred_g c) f₂,
        return { tactic.add_coinductive_predicate.coind_rule .
          orig_nm := i.local_uniq_name,
          func_nm := «expr ++ »(«expr ++ »(p, "functional"), sub),
          type := i.local_type,
          loc_type := t'.pis loc_args,
          concl := t',
          loc_args := loc_args,
          args := args,
          insts := t'.get_app_args } }),
     return { tactic.add_coinductive_predicate.coind_pred .
       pd_name := c.local_uniq_name,
       type := c.local_type,
       f₁ := f₁,
       f₂ := f₂,
       u_f := u_f,
       intros := intros,
       locals := ls,
       params := params,
       u_names := u_names } }),
  pds.mmap' (λ pd : coind_pred, do {
   let func_f₁ := «expr $ »(pd.func_g.app_of_list, fs₁),
     let func_f₂ := «expr $ »(pd.func_g.app_of_list, fs₂),
     func_intros ← pd.intros.mmap (λ r : coind_rule, do {
      let t := instantiate_local pd.f₂.local_uniq_name (pd.func_g.app_of_list fs₁) r.loc_type,
        return (r.func_nm, r.orig_nm, «expr $ »(t.pis, «expr ++ »(params, fs₁))) }),
     add_inductive pd.func.const_name u_names «expr + »(params.length, preds.length) «expr $ »(pd.type.pis, «expr ++ »(params, fs₁)) «expr $ »(func_intros.map, λ
      ⟨t, _, r⟩, (t, r)),
     mono_params ← pds.mmap (λ pd, do {
      h ← «expr $ »(mk_local_def (`h), pd.le pd.f₁ pd.f₂),
        return «expr[ , ]»([pd.f₁, pd.f₂, h]) }),
     pd.add_theorem «expr ++ »(pd.func.const_name, "mono") «expr $ »((pd.le func_f₁ func_f₂).pis, «expr ++ »(params, mono_params.join)) (do {
      ps ← «expr $ »(intro_lst, params.map expr.local_pp_name),
        fs ← pds.mmap (λ pd, do {
         «expr[ , ]»([f₁, f₂, h]) ← intro_lst «expr[ , ]»([pd.f₁.local_pp_name, pd.f₂.local_pp_name, `h]),
           let h' := «expr $ »(local_const h.local_uniq_name h.local_pp_name h.local_binding_info, «expr $ »((((const (`implies) «expr[ , ]»([]) : expr) (f₁.app_of_list pd.locals) (f₂.app_of_list pd.locals)).pis pd.locals).instantiate_locals, «expr $ »((ps.zip params).map, λ
              ⟨lv, p⟩, (p.local_uniq_name, lv)))),
           return (f₂, h') }),
        m ← pd.rec',
        «expr $ »(eapply, m.app_of_list ps),
        func_intros.mmap' (λ
         ⟨n, pp_n, t⟩, «expr $ »(solve1, do {
          bs ← intros,
            ms ← apply_core «expr $ »((const n u_params).app_of_list, «expr ++ »(ps, fs.map prod.fst)) { new_goals := new_goals.all },
            params ← (ms.zip bs).enum.mfilter (λ ⟨n, m, d⟩, «expr <$> »(bnot, is_assigned m.2)),
            params.mmap' (λ
             ⟨n, m, d⟩, «expr <|> »(mono d (fs.map prod.snd), fail «exprformat! »(format_macro "failed to prove montonoicity of {n+1}. parameter of intro-rule {pp_n}" [[expr «expr + »(n, 1)], [expr pp_n]]))) })) }) }),
  pds.mmap' (λ pd, do {
   let func_f := λ pd : coind_pred, «expr $ »(pd.func_g.app_of_list, pds.map coind_pred.f₁),
     pred_body ← «expr $ »(mk_exists_lst (pds.map coind_pred.f₁), «expr $ »(mk_and_lst, «expr ++ »(«expr $ »(pds.map, λ
         pd, pd.le pd.f₁ (func_f pd)), «expr[ , ]»([pd.f₁.app_of_list pd.locals])))),
     «expr $ »(add_decl, «expr $ »(mk_definition pd.pd_name u_names «expr $ »(pd.type.pis, params), «expr $ »(pred_body.lambdas, «expr ++ »(params, pd.locals)))),
     hs ← «expr $ »(pds.mmap, λ pd : coind_pred, «expr $ »(mk_local_def (`hc), pd.le pd.f₁ (func_f pd))),
     pd.add_theorem «expr ++ »(pd.pred.const_name, "corec_functional") «expr $ »((pd.le pd.f₁ pd.pred_g).pis, «expr ++ »(«expr ++ »(params, fs₁), hs)) (do {
      «expr $ »(intro_lst, params.map local_pp_name),
        fs ← «expr $ »(intro_lst, fs₁.map local_pp_name),
        hs ← «expr $ »(intro_lst, hs.map local_pp_name),
        ls ← «expr $ »(intro_lst, pd.locals.map local_pp_name),
        h ← intro (`h),
        whnf_target,
        fs.mmap' existsi,
        hs.mmap' (λ f, «expr >> »(econstructor, exact f)),
        exact h }) }),
  let func_f := λ pd : coind_pred, «expr $ »(pd.func_g.app_of_list, pds.map coind_pred.pred_g),
  pds.enum.mmap' (λ ⟨n, pd⟩, do {
   let destruct := pd.le pd.pred_g (func_f pd),
     pd.add_theorem «expr ++ »(pd.pred.const_name, "destruct") (destruct.pis params) (do {
      ps ← «expr $ »(intro_lst, params.map local_pp_name),
        ls ← «expr $ »(intro_lst, pd.locals.map local_pp_name),
        h ← intro (`h),
        (fs, h, _) ← elim_gen_prod pds.length h «expr[ , ]»([]) «expr[ , ]»([]),
        (hs, h, _) ← elim_gen_prod pds.length h «expr[ , ]»([]) «expr[ , ]»([]),
        «expr $ »(eapply, pd.mono.app_of_list ps),
        pds.mmap' (λ
         pd : coind_pred, «expr $ »(focus1, do {
          «expr $ »(eapply, pd.corec_functional),
            «expr $ »(focus, hs.map exact) })),
        some h' ← «expr $ »(return, hs.nth n),
        eapply h',
        exact h }) }),
  pds.mmap' (λ
   pd, pd.add_theorem «expr ++ »(pd.pred.const_name, "construct") ((pd.le (func_f pd) pd.pred_g).pis params) (do {
    ps ← «expr $ »(intro_lst, params.map local_pp_name),
      let func_pred_g := λ
      pd : coind_pred, «expr $ »(pd.func.app_of_list, «expr ++ »(ps, pds.map (λ
         pd : coind_pred, pd.pred.app_of_list ps))),
      «expr $ »(eapply, «expr $ »(pd.corec_functional.app_of_list, «expr ++ »(ps, pds.map func_pred_g))),
      pds.mmap' (λ
       pd : coind_pred, «expr $ »(solve1, do {
        «expr $ »(eapply, pd.mono.app_of_list ps),
          pds.mmap' (λ pd, «expr $ »(solve1, «expr >> »(eapply (pd.destruct.app_of_list ps), skip))) })) })),
  pds.mmap' (λ pd, do {
   let C := pd.f₁.to_implicit_binder,
     h ← «expr $ »(mk_local_def (`h), pd.pred_g.app_of_list pd.locals),
     rules ← pd.intros.mmap (λ r : coind_rule, do {
      «expr $ »(mk_local_def (mk_simple_name r.orig_nm.last_string), (C.app_of_list r.insts).pis r.args) }),
     cases_on ← pd.add_theorem «expr ++ »(pd.pred.const_name, "cases_on") «expr $ »((C.app_of_list pd.locals).pis, «expr ++ »(«expr ++ »(«expr ++ »(«expr ++ »(params, «expr[ , ]»([C])), pd.impl_locals), «expr[ , ]»([h])), rules)) (do {
      ps ← «expr $ »(intro_lst, params.map local_pp_name),
        C ← intro (`C),
        ls ← «expr $ »(intro_lst, pd.locals.map local_pp_name),
        h ← intro (`h),
        rules ← «expr $ »(intro_lst, rules.map local_pp_name),
        func_rec ← pd.rec',
        «expr $ »(eapply, «expr $ »(func_rec.app_of_list, «expr ++ »(«expr ++ »(«expr ++ »(ps, pds.map (λ
              pd, pd.pred.app_of_list ps)), «expr[ , ]»([C])), rules))),
        «expr $ »(eapply, pd.destruct),
        exact h }),
     set_basic_attribute (`elab_as_eliminator) cases_on.const_name }),
  pds.mmap' (λ pd, do {
   rules ← pds.mmap (λ pd, do {
      intros ← pd.intros.mmap (λ r, do {
         let (bs, eqs) := «expr $ »(compact_relation r.loc_args, pd.locals.zip r.insts),
           eqs ← eqs.mmap (λ ⟨l, i⟩, do {
            sort u ← infer_type l.local_type,
              «expr $ »(return, (const (`eq) «expr[ , ]»([u]) : expr) l.local_type i l) }),
           match bs, eqs with
           | «expr[ , ]»([]), «expr[ , ]»([]) := return ((0, 0), mk_true)
           | _, «expr[ , ]»([]) := «expr <$> »(prod.mk (bs.length, 0), mk_exists_lst bs.init bs.ilast.local_type)
           | _, _ := «expr <$> »(prod.mk (bs.length, eqs.length), mk_exists_lst bs (mk_and_lst eqs)) end }),
        let shape := intros.map prod.fst,
        let intros := intros.map prod.snd,
        «expr <$> »(prod.mk shape, mk_local_def «expr $ »(mk_simple_name, «expr ++ »("h_", pd.pd_name.last_string)) (((pd.f₁.app_of_list pd.locals).imp (mk_or_lst intros)).pis pd.locals)) }),
     let shape := rules.map prod.fst,
     let rules := rules.map prod.snd,
     h ← «expr $ »(mk_local_def (`h), pd.f₁.app_of_list pd.locals),
     pd.add_theorem «expr ++ »(pd.pred.const_name, "corec_on") «expr $ »(«expr $ »(pd.pred_g.app_of_list, pd.locals).pis, «expr ++ »(«expr ++ »(«expr ++ »(«expr ++ »(params, fs₁), pd.impl_locals), «expr[ , ]»([h])), rules)) (do {
      ps ← «expr $ »(intro_lst, params.map local_pp_name),
        fs ← «expr $ »(intro_lst, fs₁.map local_pp_name),
        ls ← «expr $ »(intro_lst, pd.locals.map local_pp_name),
        h ← intro (`h),
        rules ← «expr $ »(intro_lst, rules.map local_pp_name),
        «expr $ »(eapply, «expr $ »(pd.corec_functional.app_of_list, «expr ++ »(ps, fs))),
        «expr $ »(pds.zip, rules.zip shape).mmap (λ
         ⟨pd, hr, s⟩, «expr $ »(solve1, do {
          ls ← «expr $ »(intro_lst, pd.locals.map local_pp_name),
            h' ← intro (`h),
            h' ← «expr $ »(note (`h') none, hr.app_of_list ls h'),
            match s.length with
            | 0 := «expr >> »(induction h', skip)
            | «expr + »(n, 1) := do {
            hs ← elim_gen_sum n h',
              «expr $ »(hs.zip, pd.intros.zip s).mmap' (λ
               ⟨h, r, n_bs, n_eqs⟩, «expr $ »(solve1, do {
                (as, h, _) ← elim_gen_prod «expr - »(n_bs, if «expr = »(n_eqs, 0) then 1 else 0) h «expr[ , ]»([]) «expr[ , ]»([]),
                  if «expr > »(n_eqs, 0) then do {
                  (eqs, eq', _) ← elim_gen_prod «expr - »(n_eqs, 1) h «expr[ , ]»([]) «expr[ , ]»([]),
                    «expr ++ »(eqs, «expr[ , ]»([eq'])).mmap' subst } else skip,
                  eapply «expr $ »((const r.func_nm u_params).app_of_list, «expr ++ »(ps, fs)),
                  iterate assumption })) }
            end })),
        exact h }) }),
  pds.mmap' (λ
   pd, pd.intros.mmap' (λ
    r, «expr $ »(pd.add_theorem r.orig_nm (r.type.pis params), do {
     ps ← «expr $ »(intro_lst, params.map local_pp_name),
       bs ← intros,
       «expr $ »(eapply, pd.construct),
       «expr $ »(exact, «expr $ »((const r.func_nm u_params).app_of_list, «expr ++ »(«expr ++ »(ps, pds.map (λ
            pd, pd.pred.app_of_list ps)), bs))) }))),
  pds.mmap' (λ pd : coind_pred, set_basic_attribute (`irreducible) pd.pd_name),
  try triv }

setup_tactic_parser

@[user_command]
unsafe def coinductive_predicate (meta_info : decl_meta_info) (_ : parse$ tk "coinductive") : lean.parser Unit :=
  do 
    let decl ← inductive_decl.parse meta_info 
    add_coinductive_predicate decl.u_names decl.params$ decl.decls.map$ fun d => (d.sig, d.intros)
    decl.decls.mmap'$
        fun d =>
          do 
            get_env >>= fun env => set_env$ env.add_namespace d.name 
            meta_info.attrs.apply d.name 
            d.attrs.apply d.name 
            let some doc_string ← pure meta_info.doc_string | skip 
            add_doc_string d.name doc_string

-- error in Meta.CoinductivePredicates: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Prepares coinduction proofs. This tactic constructs the coinduction invariant from
the quantifiers in the current goal.

Current version: do not support mutual inductive rules -/
meta
def coinduction (rule : expr) (ns : list name) : tactic unit :=
«expr $ »(focus1, do {
 ctxts' ← intros,
   ctxts ← ctxts'.mmap (λ
    v, «expr <$> »(local_const v.local_uniq_name v.local_pp_name v.local_binding_info, infer_type v)),
   mvars ← apply_core rule { approx := ff, new_goals := new_goals.all },
   g ← «expr <$> »(list.head, get_goals),
   list.cons _ m_is ← «expr $ »(return, mvars.drop_while (λ v, «expr ≠ »(v.2, g))),
   tgt ← target,
   (is, ty) ← open_pis tgt,
   (bs, eqs) ← «expr <$> »(compact_relation ctxts, (is.zip m_is).mmap (λ
     ⟨i, m⟩, «expr <$> »(prod.mk i, instantiate_mvars m.2))),
   solve1 (do {
    eqs ← «expr <|> »(«expr <$> »(mk_and_lst, eqs.mmap (λ
         ⟨i, m⟩, «expr >>= »(mk_app (`eq) «expr[ , ]»([m, i]), instantiate_mvars))), do
       x ← mk_psigma (eqs.map prod.fst),
         y ← mk_psigma (eqs.map prod.snd),
         t ← infer_type x,
         mk_mapp (`eq) «expr[ , ]»([t, x, y])),
      rel ← mk_exists_lst bs eqs,
      exact (rel.lambdas is) }),
   solve1 (do {
    «expr >>= »(«expr >>= »(target, instantiate_mvars), change),
      bs.mmap existsi,
      iterate' «expr >> »(econstructor, skip) }),
   all_goals' (do {
    ctxts'.reverse.mmap clear,
      «expr >>= »(«expr >>= »(target, instantiate_mvars), change),
      is ← «expr $ »(intro_lst, is.map expr.local_pp_name),
      h ← intro1,
      (_, h, ns) ← elim_gen_prod «expr - »(bs.length, if «expr = »(eqs.length, 0) then 1 else 0) h «expr[ , ]»([]) ns,
      match eqs with
      | «expr[ , ]»([]) := clear h
      | «expr :: »(e, eqs) := do {
      (hs, h, ns) ← elim_gen_prod eqs.length h «expr[ , ]»([]) ns,
        («expr :: »(h, hs.reverse) : list _).mfoldl (λ (hs : list name) (h : expr), do {
         «expr[ , ]»([(_, hs', σ)]) ← cases_core h hs,
           clear (h.instantiate_locals σ),
           «expr $ »(pure, hs.drop hs'.length) }) ns,
        skip }
      end }) })

namespace Interactive

open Interactive Interactive.Types Expr Lean.Parser

local postfix:9001 "?" => optionalₓ

local postfix:9001 "*" => many

unsafe def coinduction (corec_name : parse ident) (ns : parse with_ident_list)
  (revert : parse$ (tk "generalizing" *> (ident)*)?) : tactic Unit :=
  do 
    let rule ← mk_const corec_name 
    let locals ← mmap tactic.get_local$ revert.get_or_else []
    revert_lst locals 
    tactic.coinduction rule ns 
    skip

end Interactive

end Tactic

