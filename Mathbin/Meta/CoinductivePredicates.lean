import Mathbin.Tactic.Core

section

universe u

@[user_attribute]
unsafe def monotonicity : user_attribute where
  Name := `monotonicity
  descr := "Monotonicity rules for predicates"

theorem Monotonicity.pi {α : Sort u} {p q : α → Prop} (h : ∀ a, Implies (p a) (q a)) : Implies (∀ a, p a) (∀ a, q a) :=
  fun h' a => h a (h' a)

theorem Monotonicity.imp {p p' q q' : Prop} (h₁ : Implies p' q') (h₂ : Implies q p) : Implies (p → p') (q → q') :=
  fun h => h₁ ∘ h ∘ h₂

@[monotonicity]
theorem Monotonicity.const (p : Prop) : Implies p p :=
  id

@[monotonicity]
theorem Monotonicity.true (p : Prop) : Implies p True := fun _ => trivialₓ

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

private unsafe def mono_aux (ns : List Name) (hs : List expr) : tactic Unit := do
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
                guardₓ $ u = level.zero ∧ is_arrow p ∧ is_arrow q
                let p' := pb.lower_vars 0 1
                let q' := qb.lower_vars 0 1
                eapply ((const `monotonicity.imp [] : expr) pd p' qd q')
                skip) <|>
      first (hs.map $ fun h => apply_core h { md := transparency.none, NewGoals := new_goals.non_dep_only } >> skip) <|>
        first
          (ns.map $ fun n => do
            let c ← mk_const n
            apply_core c { md := transparency.none, NewGoals := new_goals.non_dep_only }
            skip)
  all_goals' mono_aux

unsafe def mono (e : expr) (hs : List expr) : tactic Unit := do
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
  pd.func.app_of_list $ pd.params

unsafe def pred_g (pd : coind_pred) : expr :=
  pd.pred.app_of_list $ pd.params

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

unsafe def rec' (pd : coind_pred) : tactic expr := do
  let c := pd.func.const_name ++ "rec"
  let env ← get_env
  let decl ← env.get c
  let num := decl.univ_params.length
  return (const c $ if num = pd.u_params.length then pd.u_params else level.zero :: pd.u_params)

unsafe def construct (pd : coind_pred) : expr :=
  const (pd.pd_name ++ "construct") pd.u_params

unsafe def destruct (pd : coind_pred) : expr :=
  const (pd.pd_name ++ "destruct") pd.u_params

unsafe def add_theorem (pd : coind_pred) (n : Name) (type : expr) (tac : tactic Unit) : tactic expr :=
  add_theorem_by n pd.u_names type tac

end CoindPred

end AddCoinductivePredicate

open AddCoinductivePredicate

/-- compact_relation bs as_ps: Product a relation of the form:
  R := λ as, ∃ bs, Λ_i a_i = p_i[bs]
This relation is user visible, so we compact it by removing each `b_j` where a `p_i = b_j`, and
hence `a_i = b_j`. We need to take care when there are `p_i` and `p_j` with `p_i = p_j = b_k`. -/
unsafe def compact_relation : List expr → List (expr × expr) → List expr × List (expr × expr)
  | [], ps => ([], ps)
  | List.cons b bs, ps =>
    match ps.span fun ap : expr × expr => ¬ap.2 =ₐ b with
    | (_, []) =>
      let (bs, ps) := compact_relation bs ps
      (b :: bs, ps)
    | (ps₁, List.cons (a, _) ps₂) =>
      let i := a.instantiate_local b.local_uniq_name
      compact_relation (bs.map i) ((ps₁ ++ ps₂).map fun ⟨a, p⟩ => (a, i p))

unsafe def add_coinductive_predicate (u_names : List Name) (params : List expr) (preds : List $ expr × List expr) :
    command := do
  let params_names := params.map local_pp_name
  let u_params := u_names.map param
  let pre_info ←
    preds.mmap fun ⟨c, is⟩ => do
        let (ls, t) ← open_pis c.local_type
        is_def_eq t (quote.1 Prop) <|>
            fail
              ((f! "Type of {c.local_pp_name} is not Prop. Currently only ") ++ "coinductive predicates are supported.")
        let n := if preds.length = 1 then "" else "_" ++ c.local_pp_name.last_string
        let f₁ ← mk_local_def (mkSimpleName $ "C" ++ n) c.local_type
        let f₂ ← mk_local_def (mkSimpleName $ "C₂" ++ n) c.local_type
        return (ls, (f₁, f₂))
  let fs := pre_info.map Prod.snd
  let fs₁ := fs.map Prod.fst
  let fs₂ := fs.map Prod.snd
  let pds ←
    (preds.zip pre_info).mmap fun ⟨⟨c, is⟩, ls, f₁, f₂⟩ => do
        let sort u_f ← infer_type f₁ >>= infer_type
        let pred_g := fun c : expr => (const c.local_uniq_name u_params : expr).app_of_list params
        let intros ←
          is.mmap fun i => do
              let (args, t') ← open_pis i.local_type
              let Name.mk_string sub p ← return i.local_uniq_name
              let loc_args :=
                args.map $ fun e => (fs₁.zip preds).foldl (fun e : expr ⟨f, c, _⟩ => e.replace_with (pred_g c) f) e
              let t' := t'.replace_with (pred_g c) f₂
              return
                  { orig_nm := i.local_uniq_name, func_nm := p ++ "functional" ++ sub, type := i.local_type,
                    loc_type := t'.pis loc_args, concl := t', loc_args, args, insts := t'.get_app_args }
        return
            { pd_name := c.local_uniq_name, type := c.local_type, f₁, f₂, u_f, intros, locals := ls, params, u_names }
  pds.mmap' fun pd : coind_pred => do
      let func_f₁ := pd.func_g.app_of_list $ fs₁
      let func_f₂ := pd.func_g.app_of_list $ fs₂
      let func_intros ←
        pd.intros.mmap fun r : coind_rule => do
            let t := instantiate_local pd.f₂.local_uniq_name (pd.func_g.app_of_list fs₁) r.loc_type
            return (r.func_nm, r.orig_nm, t.pis $ params ++ fs₁)
      add_inductive pd.func.const_name u_names (params.length + preds.length) (pd.type.pis $ params ++ fs₁)
          (func_intros.map $ fun ⟨t, _, r⟩ => (t, r))
      let mono_params ←
        pds.mmap fun pd => do
            let h ← mk_local_def `h $ pd.le pd.f₁ pd.f₂
            return [pd.f₁, pd.f₂, h]
      pd.add_theorem (pd.func.const_name ++ "mono") ((pd.le func_f₁ func_f₂).pis $ params ++ mono_params.join) do
          let ps ← intro_lst $ params.map expr.local_pp_name
          let fs ←
            pds.mmap fun pd => do
                let [f₁, f₂, h] ← intro_lst [pd.f₁.local_pp_name, pd.f₂.local_pp_name, `h]
                let h' :=
                  local_const h.local_uniq_name h.local_pp_name h.local_binding_info $
                    (((const `implies [] : expr) (f₁.app_of_list pd.locals) (f₂.app_of_list pd.locals)).pis
                          pd.locals).instantiate_locals $
                      (ps.zip params).map $ fun ⟨lv, p⟩ => (p.local_uniq_name, lv)
                return (f₂, h')
          let m ← pd.rec'
          eapply $ m.app_of_list ps
          func_intros.mmap' fun ⟨n, pp_n, t⟩ =>
              solve1 $ do
                let bs ← intros
                let ms ←
                  apply_core ((const n u_params).app_of_list $ ps ++ fs.map Prod.fst) { NewGoals := new_goals.all }
                let params ← (ms.zip bs).enum.mfilter fun ⟨n, m, d⟩ => bnot <$> is_assigned m.2
                params.mmap' fun ⟨n, m, d⟩ =>
                    mono d (fs.map Prod.snd) <|>
                      fail f!"failed to prove montonoicity of {(n + 1)}. parameter of intro-rule {pp_n}"
  pds.mmap' fun pd => do
      let func_f := fun pd : coind_pred => pd.func_g.app_of_list $ pds.map coind_pred.f₁
      let pred_body ←
        mk_exists_lst (pds.map coind_pred.f₁) $
            mk_and_lst $ (pds.map $ fun pd => pd.le pd.f₁ (func_f pd)) ++ [pd.f₁.app_of_list pd.locals]
      add_decl $ mk_definition pd.pd_name u_names (pd.type.pis $ params) $ pred_body.lambdas $ params ++ pd.locals
      let hs ← pds.mmap $ fun pd : coind_pred => mk_local_def `hc $ pd.le pd.f₁ (func_f pd)
      pd.add_theorem (pd.pred.const_name ++ "corec_functional") ((pd.le pd.f₁ pd.pred_g).pis $ params ++ fs₁ ++ hs) do
          intro_lst $ params.map local_pp_name
          let fs ← intro_lst $ fs₁.map local_pp_name
          let hs ← intro_lst $ hs.map local_pp_name
          let ls ← intro_lst $ pd.locals.map local_pp_name
          let h ← intro `h
          whnf_target
          fs.mmap' existsi
          hs.mmap' fun f => econstructor >> exact f
          exact h
  let func_f := fun pd : coind_pred => pd.func_g.app_of_list $ pds.map coind_pred.pred_g
  pds.enum.mmap' fun ⟨n, pd⟩ => do
      let destruct := pd.le pd.pred_g (func_f pd)
      pd.add_theorem (pd.pred.const_name ++ "destruct") (destruct.pis params) do
          let ps ← intro_lst $ params.map local_pp_name
          let ls ← intro_lst $ pd.locals.map local_pp_name
          let h ← intro `h
          let (fs, h, _) ← elim_gen_prod pds.length h [] []
          let (hs, h, _) ← elim_gen_prod pds.length h [] []
          eapply $ pd.mono.app_of_list ps
          pds.mmap' fun pd : coind_pred =>
              focus1 $ do
                eapply $ pd.corec_functional
                focus $ hs.map exact
          let some h' ← return $ hs.nth n
          eapply h'
          exact h
  pds.mmap' fun pd =>
      pd.add_theorem (pd.pred.const_name ++ "construct") ((pd.le (func_f pd) pd.pred_g).pis params) do
        let ps ← intro_lst $ params.map local_pp_name
        let func_pred_g := fun pd : coind_pred =>
          pd.func.app_of_list $ ps ++ pds.map fun pd : coind_pred => pd.pred.app_of_list ps
        eapply $ pd.corec_functional.app_of_list $ ps ++ pds.map func_pred_g
        pds.mmap' fun pd : coind_pred =>
            solve1 $ do
              eapply $ pd.mono.app_of_list ps
              pds.mmap' fun pd => solve1 $ eapply (pd.destruct.app_of_list ps) >> skip
  pds.mmap' fun pd => do
      let C := pd.f₁.to_implicit_binder
      let h ← mk_local_def `h $ pd.pred_g.app_of_list pd.locals
      let rules ←
        pd.intros.mmap fun r : coind_rule => do
            mk_local_def (mkSimpleName r.orig_nm.last_string) $ (C.app_of_list r.insts).pis r.args
      let cases_on ←
        pd.add_theorem (pd.pred.const_name ++ "cases_on")
            ((C.app_of_list pd.locals).pis $ params ++ [C] ++ pd.impl_locals ++ [h] ++ rules) do
            let ps ← intro_lst $ params.map local_pp_name
            let C ← intro `C
            let ls ← intro_lst $ pd.locals.map local_pp_name
            let h ← intro `h
            let rules ← intro_lst $ rules.map local_pp_name
            let func_rec ← pd.rec'
            eapply $ func_rec.app_of_list $ (ps ++ pds.map fun pd => pd.pred.app_of_list ps) ++ [C] ++ rules
            eapply $ pd.destruct
            exact h
      set_basic_attribute `elab_as_eliminator cases_on.const_name
  pds.mmap' fun pd => do
      let rules ←
        pds.mmap fun pd => do
            let intros ←
              pd.intros.mmap fun r => do
                  let (bs, eqs) := compact_relation r.loc_args $ pd.locals.zip r.insts
                  let eqs ←
                    eqs.mmap fun ⟨l, i⟩ => do
                        let sort u ← infer_type l.local_type
                        return $ (const `eq [u] : expr) l.local_type i l
                  match bs, eqs with
                    | [], [] => return ((0, 0), mk_true)
                    | _, [] => Prod.mk (bs.length, 0) <$> mk_exists_lst bs.init bs.ilast.local_type
                    | _, _ => Prod.mk (bs.length, eqs.length) <$> mk_exists_lst bs (mk_and_lst eqs)
            let shape := intros.map Prod.fst
            let intros := intros.map Prod.snd
            Prod.mk shape <$>
                mk_local_def (mkSimpleName $ "h_" ++ pd.pd_name.last_string)
                  (((pd.f₁.app_of_list pd.locals).imp (mk_or_lst intros)).pis pd.locals)
      let shape := rules.map Prod.fst
      let rules := rules.map Prod.snd
      let h ← mk_local_def `h $ pd.f₁.app_of_list pd.locals
      pd.add_theorem (pd.pred.const_name ++ "corec_on")
          ((pd.pred_g.app_of_list $ pd.locals).pis $ params ++ fs₁ ++ pd.impl_locals ++ [h] ++ rules) do
          let ps ← intro_lst $ params.map local_pp_name
          let fs ← intro_lst $ fs₁.map local_pp_name
          let ls ← intro_lst $ pd.locals.map local_pp_name
          let h ← intro `h
          let rules ← intro_lst $ rules.map local_pp_name
          eapply $ pd.corec_functional.app_of_list $ ps ++ fs
          (pds.zip $ rules.zip shape).mmap fun ⟨pd, hr, s⟩ =>
              solve1 $ do
                let ls ← intro_lst $ pd.locals.map local_pp_name
                let h' ← intro `h
                let h' ← note `h' none $ hr.app_of_list ls h'
                match s.length with
                  | 0 => induction h' >> skip
                  | n + 1 => do
                    let hs ← elim_gen_sum n h'
                    (hs.zip $ pd.intros.zip s).mmap' fun ⟨h, r, n_bs, n_eqs⟩ =>
                        solve1 $ do
                          let (as, h, _) ← elim_gen_prod (n_bs - if n_eqs = 0 then 1 else 0) h [] []
                          if n_eqs > 0 then do
                              let (eqs, eq', _) ← elim_gen_prod (n_eqs - 1) h [] []
                              (eqs ++ [eq']).mmap' subst
                            else skip
                          eapply ((const r.func_nm u_params).app_of_list $ ps ++ fs)
                          iterate assumption
          exact h
  pds.mmap' fun pd =>
      pd.intros.mmap' fun r =>
        pd.add_theorem r.orig_nm (r.type.pis params) $ do
          let ps ← intro_lst $ params.map local_pp_name
          let bs ← intros
          eapply $ pd.construct
          exact $ (const r.func_nm u_params).app_of_list $ (ps ++ pds.map fun pd => pd.pred.app_of_list ps) ++ bs
  pds.mmap' fun pd : coind_pred => set_basic_attribute `irreducible pd.pd_name
  try triv

setup_tactic_parser

@[user_command]
unsafe def coinductive_predicate (meta_info : decl_meta_info) (_ : parse $ tk "coinductive") : lean.parser Unit := do
  let decl ← inductive_decl.parse meta_info
  add_coinductive_predicate decl.u_names decl.params $ decl.decls.map $ fun d => (d.sig, d.intros)
  decl.decls.mmap' $ fun d => do
      get_env >>= fun env => set_env $ env.add_namespace d.name
      meta_info.attrs.apply d.name
      d.attrs.apply d.name
      let some doc_string ← pure meta_info.doc_string | skip
      add_doc_string d.name doc_string

/-- Prepares coinduction proofs. This tactic constructs the coinduction invariant from
the quantifiers in the current goal.

Current version: do not support mutual inductive rules -/
unsafe def coinduction (rule : expr) (ns : List Name) : tactic Unit :=
  focus1 $ do
    let ctxts' ← intros
    let ctxts ← ctxts'.mmap fun v => local_const v.local_uniq_name v.local_pp_name v.local_binding_info <$> infer_type v
    let mvars ← apply_core rule { approx := ff, NewGoals := new_goals.all }
    let g ← List.headₓ <$> get_goals
    let List.cons _ m_is ← return $ mvars.drop_while fun v => v.2 ≠ g
    let tgt ← target
    let (is, ty) ← open_pis tgt
    let (bs, eqs) ← compact_relation ctxts <$> (is.zip m_is).mmap fun ⟨i, m⟩ => Prod.mk i <$> instantiate_mvars m.2
    solve1 do
        let eqs ←
          (mk_and_lst <$> eqs.mmap fun ⟨i, m⟩ => mk_app `eq [m, i] >>= instantiate_mvars) <|> do
              let x ← mk_psigma (eqs.map Prod.fst)
              let y ← mk_psigma (eqs.map Prod.snd)
              let t ← infer_type x
              mk_mapp `eq [t, x, y]
        let rel ← mk_exists_lst bs eqs
        exact (rel.lambdas is)
    solve1 do
        target >>= instantiate_mvars >>= change
        bs.mmap existsi
        iterate' (econstructor >> skip)
    all_goals' do
        ctxts'.reverse.mmap clear
        target >>= instantiate_mvars >>= change
        let is ← intro_lst $ is.map expr.local_pp_name
        let h ← intro1
        let (_, h, ns) ← elim_gen_prod (bs.length - if eqs.length = 0 then 1 else 0) h [] ns
        match eqs with
          | [] => clear h
          | e :: eqs => do
            let (hs, h, ns) ← elim_gen_prod eqs.length h [] ns
            (h :: hs.reverse : List _).mfoldl
                (fun hs : List Name h : expr => do
                  let [(_, hs', σ)] ← cases_core h hs
                  clear (h.instantiate_locals σ)
                  pure $ hs.drop hs'.length)
                ns
            skip

namespace Interactive

open Interactive Interactive.Types Expr Lean.Parser

local postfix:9001 "?" => optionalₓ

local postfix:9001 "*" => many

unsafe def coinduction (corec_name : parse ident) (ns : parse with_ident_list)
    (revert : parse $ (tk "generalizing" *> (ident)*)?) : tactic Unit := do
  let rule ← mk_const corec_name
  let locals ← mmap tactic.get_local $ revert.get_or_else []
  revert_lst locals
  tactic.coinduction rule ns
  skip

end Interactive

end Tactic

