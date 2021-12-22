import Mathbin.Data.Nat.Prime
import Mathbin.Dynamics.FixedPoints.Basic
import Mathbin.Data.Pnat.Basic
import Mathbin.Data.Set.Lattice

/-!
# Periodic points

A point `x : α` is a periodic point of `f : α → α` of period `n` if `f^[n] x = x`.

## Main definitions

* `is_periodic_pt f n x` : `x` is a periodic point of `f` of period `n`, i.e. `f^[n] x = x`.
  We do not require `n > 0` in the definition.
* `pts_of_period f n` : the set `{x | is_periodic_pt f n x}`. Note that `n` is not required to
  be the minimal period of `x`.
* `periodic_pts f` : the set of all periodic points of `f`.
* `minimal_period f x` : the minimal period of a point `x` under an endomorphism `f` or zero
  if `x` is not a periodic point of `f`.

## Main statements

We provide “dot syntax”-style operations on terms of the form `h : is_periodic_pt f n x` including
arithmetic operations on `n` and `h.map (hg : semiconj_by g f f')`. We also prove that `f`
is bijective on each set `pts_of_period f n` and on `periodic_pts f`. Finally, we prove that `x`
is a periodic point of `f` of period `n` if and only if `minimal_period f x | n`.

## References

* https://en.wikipedia.org/wiki/Periodic_point

-/


open Set

namespace Function

variable {α : Type _} {β : Type _} {f fa : α → α} {fb : β → β} {x y : α} {m n : ℕ}

/--  A point `x` is a periodic point of `f : α → α` of period `n` if `f^[n] x = x`.
Note that we do not require `0 < n` in this definition. Many theorems about periodic points
need this assumption. -/
def is_periodic_pt (f : α → α) (n : ℕ) (x : α) :=
  is_fixed_pt (f^[n]) x

/--  A fixed point of `f` is a periodic point of `f` of any prescribed period. -/
theorem is_fixed_pt.is_periodic_pt (hf : is_fixed_pt f x) (n : ℕ) : is_periodic_pt f n x :=
  hf.iterate n

/--  For the identity map, all points are periodic. -/
theorem is_periodic_id (n : ℕ) (x : α) : is_periodic_pt id n x :=
  (is_fixed_pt_id x).IsPeriodicPt n

/--  Any point is a periodic point of period `0`. -/
theorem is_periodic_pt_zero (f : α → α) (x : α) : is_periodic_pt f 0 x :=
  is_fixed_pt_id x

namespace IsPeriodicPt

instance [DecidableEq α] {f : α → α} {n : ℕ} {x : α} : Decidable (is_periodic_pt f n x) :=
  is_fixed_pt.decidable

protected theorem is_fixed_pt (hf : is_periodic_pt f n x) : is_fixed_pt (f^[n]) x :=
  hf

protected theorem map (hx : is_periodic_pt fa n x) {g : α → β} (hg : semiconj g fa fb) : is_periodic_pt fb n (g x) :=
  hx.map (hg.iterate_right n)

theorem apply_iterate (hx : is_periodic_pt f n x) (m : ℕ) : is_periodic_pt f n ((f^[m]) x) :=
  hx.map $ commute.iterate_self f m

protected theorem apply (hx : is_periodic_pt f n x) : is_periodic_pt f n (f x) :=
  hx.apply_iterate 1

protected theorem add (hn : is_periodic_pt f n x) (hm : is_periodic_pt f m x) : is_periodic_pt f (n+m) x := by
  rw [is_periodic_pt, iterate_add]
  exact hn.comp hm

theorem left_of_add (hn : is_periodic_pt f (n+m) x) (hm : is_periodic_pt f m x) : is_periodic_pt f n x := by
  rw [is_periodic_pt, iterate_add] at hn
  exact hn.left_of_comp hm

theorem right_of_add (hn : is_periodic_pt f (n+m) x) (hm : is_periodic_pt f n x) : is_periodic_pt f m x := by
  rw [add_commₓ] at hn
  exact hn.left_of_add hm

protected theorem sub (hm : is_periodic_pt f m x) (hn : is_periodic_pt f n x) : is_periodic_pt f (m - n) x := by
  cases' le_totalₓ n m with h h
  ·
    refine' left_of_add _ hn
    rwa [tsub_add_cancel_of_le h]
  ·
    rw [tsub_eq_zero_iff_le.mpr h]
    apply is_periodic_pt_zero

protected theorem mul_const (hm : is_periodic_pt f m x) (n : ℕ) : is_periodic_pt f (m*n) x := by
  simp only [is_periodic_pt, iterate_mul, hm.is_fixed_pt.iterate n]

protected theorem const_mul (hm : is_periodic_pt f m x) (n : ℕ) : is_periodic_pt f (n*m) x := by
  simp only [mul_commₓ n, hm.mul_const n]

theorem trans_dvd (hm : is_periodic_pt f m x) {n : ℕ} (hn : m ∣ n) : is_periodic_pt f n x :=
  let ⟨k, hk⟩ := hn
  hk.symm ▸ hm.mul_const k

protected theorem iterate (hf : is_periodic_pt f n x) (m : ℕ) : is_periodic_pt (f^[m]) n x := by
  rw [is_periodic_pt, ← iterate_mul, mul_commₓ, iterate_mul]
  exact hf.is_fixed_pt.iterate m

theorem comp {g : α → α} (hco : Commute f g) (hf : is_periodic_pt f n x) (hg : is_periodic_pt g n x) :
    is_periodic_pt (f ∘ g) n x := by
  rw [is_periodic_pt, hco.comp_iterate]
  exact hf.comp hg

theorem comp_lcm {g : α → α} (hco : Commute f g) (hf : is_periodic_pt f m x) (hg : is_periodic_pt g n x) :
    is_periodic_pt (f ∘ g) (Nat.lcmₓ m n) x :=
  (hf.trans_dvd $ Nat.dvd_lcm_leftₓ _ _).comp hco (hg.trans_dvd $ Nat.dvd_lcm_rightₓ _ _)

theorem left_of_comp {g : α → α} (hco : Commute f g) (hfg : is_periodic_pt (f ∘ g) n x) (hg : is_periodic_pt g n x) :
    is_periodic_pt f n x := by
  rw [is_periodic_pt, hco.comp_iterate] at hfg
  exact hfg.left_of_comp hg

theorem iterate_mod_apply (h : is_periodic_pt f n x) (m : ℕ) : (f^[m % n]) x = (f^[m]) x := by
  conv_rhs => rw [← Nat.mod_add_divₓ m n, iterate_add_apply, (h.mul_const _).Eq]

protected theorem mod (hm : is_periodic_pt f m x) (hn : is_periodic_pt f n x) : is_periodic_pt f (m % n) x :=
  (hn.iterate_mod_apply m).trans hm

protected theorem gcd (hm : is_periodic_pt f m x) (hn : is_periodic_pt f n x) : is_periodic_pt f (m.gcd n) x := by
  revert hm hn
  refine' Nat.gcdₓ.induction m n (fun n h0 hn => _) fun m n hm ih hm hn => _
  ·
    rwa [Nat.gcd_zero_leftₓ]
  ·
    rw [Nat.gcd_recₓ]
    exact ih (hn.mod hm) hm

/--  If `f` sends two periodic points `x` and `y` of the same positive period to the same point,
then `x = y`. For a similar statement about points of different periods see `eq_of_apply_eq`. -/
theorem eq_of_apply_eq_same (hx : is_periodic_pt f n x) (hy : is_periodic_pt f n y) (hn : 0 < n) (h : f x = f y) :
    x = y := by
  rw [← hx.eq, ← hy.eq, ← iterate_pred_comp_of_pos f hn, comp_app, h]

/--  If `f` sends two periodic points `x` and `y` of positive periods to the same point,
then `x = y`. -/
theorem eq_of_apply_eq (hx : is_periodic_pt f m x) (hy : is_periodic_pt f n y) (hm : 0 < m) (hn : 0 < n)
    (h : f x = f y) : x = y :=
  (hx.mul_const n).eq_of_apply_eq_same (hy.const_mul m) (mul_pos hm hn) h

end IsPeriodicPt

/--  The set of periodic points of a given (possibly non-minimal) period. -/
def pts_of_period (f : α → α) (n : ℕ) : Set α :=
  { x : α | is_periodic_pt f n x }

@[simp]
theorem mem_pts_of_period : x ∈ pts_of_period f n ↔ is_periodic_pt f n x :=
  Iff.rfl

theorem semiconj.maps_to_pts_of_period {g : α → β} (h : semiconj g fa fb) (n : ℕ) :
    maps_to g (pts_of_period fa n) (pts_of_period fb n) :=
  (h.iterate_right n).maps_to_fixed_pts

theorem bij_on_pts_of_period (f : α → α) {n : ℕ} (hn : 0 < n) : bij_on f (pts_of_period f n) (pts_of_period f n) :=
  ⟨(Commute.refl f).maps_to_pts_of_period n, fun x hx y hy hxy => hx.eq_of_apply_eq_same hy hn hxy, fun x hx =>
    ⟨(f^[n.pred]) x, hx.apply_iterate _, by
      rw [← comp_app f, comp_iterate_pred_of_pos f hn, hx.eq]⟩⟩

theorem directed_pts_of_period_pnat (f : α → α) : Directed (· ⊆ ·) fun n : ℕ+ => pts_of_period f n := fun m n =>
  ⟨m*n, fun x hx => hx.mul_const n, fun x hx => hx.const_mul m⟩

/--  The set of periodic points of a map `f : α → α`. -/
def periodic_pts (f : α → α) : Set α :=
  { x : α | ∃ n > 0, is_periodic_pt f n x }

theorem mk_mem_periodic_pts (hn : 0 < n) (hx : is_periodic_pt f n x) : x ∈ periodic_pts f :=
  ⟨n, hn, hx⟩

theorem mem_periodic_pts : x ∈ periodic_pts f ↔ ∃ n > 0, is_periodic_pt f n x :=
  Iff.rfl

variable (f)

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (n «expr > » 0)
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `bUnion_pts_of_period [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_=_»
     (Set.Data.Set.Lattice.«term⋃_,_»
      "⋃"
      (Lean.explicitBinders
       [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `n)] ":" (Term.hole "_") ")")
        (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" («term_>_» `n ">" (numLit "0")) ")")])
      ", "
      (Term.app `pts_of_period [`f `n]))
     "="
     (Term.app `periodic_pts [`f]))))
  (Command.declValSimple
   ":="
   («term_$__»
    `Set.ext
    "$"
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`x] [])]
      "=>"
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `mem_periodic_pts)] "]"] []) [])]))))))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   `Set.ext
   "$"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`x] [])]
     "=>"
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `mem_periodic_pts)] "]"] []) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `mem_periodic_pts)] "]"] []) [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `mem_periodic_pts)] "]"] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `mem_periodic_pts)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_periodic_pts
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `Set.ext
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Set.Data.Set.Lattice.«term⋃_,_»
    "⋃"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `n)] ":" (Term.hole "_") ")")
      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" («term_>_» `n ">" (numLit "0")) ")")])
    ", "
    (Term.app `pts_of_period [`f `n]))
   "="
   (Term.app `periodic_pts [`f]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `periodic_pts [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `periodic_pts
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Set.Data.Set.Lattice.«term⋃_,_»
   "⋃"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `n)] ":" (Term.hole "_") ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" («term_>_» `n ">" (numLit "0")) ")")])
   ", "
   (Term.app `pts_of_period [`f `n]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `pts_of_period [`f `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `pts_of_period
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  bUnion_pts_of_period
  : ⋃ ( n : _ ) ( _ : n > 0 ) , pts_of_period f n = periodic_pts f
  := Set.ext $ fun x => by simp [ mem_periodic_pts ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `Union_pnat_pts_of_period [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_=_»
     (Set.Data.Set.Lattice.«term⋃_,_»
      "⋃"
      (Lean.explicitBinders
       (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (Data.Pnat.Basic.«termℕ+» "ℕ+")]))
      ", "
      (Term.app `pts_of_period [`f `n]))
     "="
     (Term.app `periodic_pts [`f]))))
  (Command.declValSimple
   ":="
   («term_$__» (Term.proj `supr_subtype "." `trans) "$" (Term.app `bUnion_pts_of_period [`f]))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__» (Term.proj `supr_subtype "." `trans) "$" (Term.app `bUnion_pts_of_period [`f]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `bUnion_pts_of_period [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `bUnion_pts_of_period
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.proj `supr_subtype "." `trans)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `supr_subtype
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Set.Data.Set.Lattice.«term⋃_,_»
    "⋃"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (Data.Pnat.Basic.«termℕ+» "ℕ+")]))
    ", "
    (Term.app `pts_of_period [`f `n]))
   "="
   (Term.app `periodic_pts [`f]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `periodic_pts [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `periodic_pts
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Set.Data.Set.Lattice.«term⋃_,_»
   "⋃"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (Data.Pnat.Basic.«termℕ+» "ℕ+")]))
   ", "
   (Term.app `pts_of_period [`f `n]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `pts_of_period [`f `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `pts_of_period
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  Union_pnat_pts_of_period
  : ⋃ n : ℕ+ , pts_of_period f n = periodic_pts f
  := supr_subtype . trans $ bUnion_pts_of_period f

theorem bij_on_periodic_pts : bij_on f (periodic_pts f) (periodic_pts f) :=
  Union_pnat_pts_of_period f ▸
    bij_on_Union_of_directed (directed_pts_of_period_pnat f) fun i => bij_on_pts_of_period f i.pos

variable {f}

theorem semiconj.maps_to_periodic_pts {g : α → β} (h : semiconj g fa fb) :
    maps_to g (periodic_pts fa) (periodic_pts fb) := fun x ⟨n, hn, hx⟩ => ⟨n, hn, hx.map h⟩

open_locale Classical

noncomputable section

/--  Minimal period of a point `x` under an endomorphism `f`. If `x` is not a periodic point of `f`,
then `minimal_period f x = 0`. -/
def minimal_period (f : α → α) (x : α) :=
  if h : x ∈ periodic_pts f then Nat.findₓ h else 0

theorem is_periodic_pt_minimal_period (f : α → α) (x : α) : is_periodic_pt f (minimal_period f x) x := by
  delta' minimal_period
  split_ifs with hx
  ·
    exact (Nat.find_specₓ hx).snd
  ·
    exact is_periodic_pt_zero f x

theorem iterate_eq_mod_minimal_period : (f^[n]) x = (f^[n % minimal_period f x]) x :=
  ((is_periodic_pt_minimal_period f x).iterate_mod_apply n).symm

theorem minimal_period_pos_of_mem_periodic_pts (hx : x ∈ periodic_pts f) : 0 < minimal_period f x := by
  simp only [minimal_period, dif_pos hx, (Nat.find_specₓ hx).fst.lt]

theorem is_periodic_pt.minimal_period_pos (hn : 0 < n) (hx : is_periodic_pt f n x) : 0 < minimal_period f x :=
  minimal_period_pos_of_mem_periodic_pts $ mk_mem_periodic_pts hn hx

theorem minimal_period_pos_iff_mem_periodic_pts : 0 < minimal_period f x ↔ x ∈ periodic_pts f :=
  ⟨not_imp_not.1 $ fun h => by
      simp only [minimal_period, dif_neg h, lt_irreflₓ 0, not_false_iff],
    minimal_period_pos_of_mem_periodic_pts⟩

theorem is_periodic_pt.minimal_period_le (hn : 0 < n) (hx : is_periodic_pt f n x) : minimal_period f x ≤ n := by
  rw [minimal_period, dif_pos (mk_mem_periodic_pts hn hx)]
  exact Nat.find_min'ₓ (mk_mem_periodic_pts hn hx) ⟨hn, hx⟩

theorem minimal_period_id : minimal_period id x = 1 :=
  ((is_periodic_id _ _).minimal_period_le Nat.one_posₓ).antisymm
    (Nat.succ_le_of_ltₓ ((is_periodic_id _ _).minimal_period_pos Nat.one_posₓ))

theorem is_fixed_point_iff_minimal_period_eq_one : minimal_period f x = 1 ↔ is_fixed_pt f x := by
  refine' ⟨fun h => _, fun h => _⟩
  ·
    rw [← iterate_one f]
    refine' Function.IsPeriodicPt.is_fixed_pt _
    rw [← h]
    exact is_periodic_pt_minimal_period f x
  ·
    exact
      ((h.is_periodic_pt 1).minimal_period_le Nat.one_posₓ).antisymm
        (Nat.succ_le_of_ltₓ ((h.is_periodic_pt 1).minimal_period_pos Nat.one_posₓ))

theorem is_periodic_pt.eq_zero_of_lt_minimal_period (hx : is_periodic_pt f n x) (hn : n < minimal_period f x) : n = 0 :=
  Eq.symm $ (eq_or_lt_of_le $ n.zero_le).resolve_right $ fun hn0 => not_ltₓ.2 (hx.minimal_period_le hn0) hn

theorem not_is_periodic_pt_of_pos_of_lt_minimal_period :
    ∀ {n : ℕ} n0 : n ≠ 0 hn : n < minimal_period f x, ¬is_periodic_pt f n x
  | 0, n0, _ => (n0 rfl).elim
  | n+1, _, hn => fun hp => Nat.succ_ne_zero _ (hp.eq_zero_of_lt_minimal_period hn)

theorem is_periodic_pt.minimal_period_dvd (hx : is_periodic_pt f n x) : minimal_period f x ∣ n :=
  ((eq_or_lt_of_le $ n.zero_le).elim fun hn0 => hn0 ▸ dvd_zero _) $ fun hn0 =>
    (Nat.dvd_iff_mod_eq_zeroₓ _ _).2 $
      (hx.mod $ is_periodic_pt_minimal_period f x).eq_zero_of_lt_minimal_period $
        Nat.mod_ltₓ _ $ hx.minimal_period_pos hn0

theorem is_periodic_pt_iff_minimal_period_dvd : is_periodic_pt f n x ↔ minimal_period f x ∣ n :=
  ⟨is_periodic_pt.minimal_period_dvd, fun h => (is_periodic_pt_minimal_period f x).trans_dvd h⟩

open Nat

theorem minimal_period_eq_minimal_period_iff {g : β → β} {y : β} :
    minimal_period f x = minimal_period g y ↔ ∀ n, is_periodic_pt f n x ↔ is_periodic_pt g n y := by
  simp_rw [is_periodic_pt_iff_minimal_period_dvd, dvd_right_iff_eq]

theorem minimal_period_eq_prime {p : ℕ} [hp : Fact p.prime] (hper : is_periodic_pt f p x) (hfix : ¬is_fixed_pt f x) :
    minimal_period f x = p :=
  (hp.out.2 _ hper.minimal_period_dvd).resolve_left (mt is_fixed_point_iff_minimal_period_eq_one.1 hfix)

theorem minimal_period_eq_prime_pow {p k : ℕ} [hp : Fact p.prime] (hk : ¬is_periodic_pt f (p ^ k) x)
    (hk1 : is_periodic_pt f (p ^ k+1) x) : minimal_period f x = p ^ k+1 := by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow hp.out <;> rwa [← is_periodic_pt_iff_minimal_period_dvd]

theorem commute.minimal_period_of_comp_dvd_lcm {g : α → α} (h : Function.Commute f g) :
    minimal_period (f ∘ g) x ∣ Nat.lcmₓ (minimal_period f x) (minimal_period g x) := by
  rw [← is_periodic_pt_iff_minimal_period_dvd]
  exact (is_periodic_pt_minimal_period f x).comp_lcm h (is_periodic_pt_minimal_period g x)

theorem commute.minimal_period_of_comp_dvd_mul {g : α → α} (h : Function.Commute f g) :
    minimal_period (f ∘ g) x ∣ minimal_period f x*minimal_period g x :=
  dvd_trans h.minimal_period_of_comp_dvd_lcm (lcm_dvd_mul _ _)

theorem commute.minimal_period_of_comp_eq_mul_of_coprime {g : α → α} (h : Function.Commute f g)
    (hco : coprime (minimal_period f x) (minimal_period g x)) :
    minimal_period (f ∘ g) x = minimal_period f x*minimal_period g x := by
  apply dvd_antisymm h.minimal_period_of_comp_dvd_mul
  suffices :
    ∀ {f g : α → α},
      Commute f g → coprime (minimal_period f x) (minimal_period g x) → minimal_period f x ∣ minimal_period (f ∘ g) x
  exact hco.mul_dvd_of_dvd_of_dvd (this h hco) (h.comp_eq.symm ▸ this h.symm hco.symm)
  clear hco h f g
  intro f g h hco
  refine' hco.dvd_of_dvd_mul_left (is_periodic_pt.left_of_comp h _ _).minimal_period_dvd
  ·
    exact (is_periodic_pt_minimal_period _ _).const_mul _
  ·
    exact (is_periodic_pt_minimal_period _ _).mul_const _

private theorem minimal_period_iterate_eq_div_gcd_aux (h : 0 < gcd (minimal_period f x) n) :
    minimal_period (f^[n]) x = minimal_period f x / Nat.gcdₓ (minimal_period f x) n := by
  apply Nat.dvd_antisymm
  ·
    apply is_periodic_pt.minimal_period_dvd
    rw [is_periodic_pt, is_fixed_pt, ← iterate_mul, ← Nat.mul_div_assocₓ _ (gcd_dvd_left _ _), mul_commₓ,
      Nat.mul_div_assocₓ _ (gcd_dvd_right _ _), mul_commₓ, iterate_mul]
    exact (is_periodic_pt_minimal_period f x).iterate _
  ·
    apply coprime.dvd_of_dvd_mul_right (coprime_div_gcd_div_gcd h)
    apply dvd_of_mul_dvd_mul_right h
    rw [Nat.div_mul_cancelₓ (gcd_dvd_left _ _), mul_assocₓ, Nat.div_mul_cancelₓ (gcd_dvd_right _ _), mul_commₓ]
    apply is_periodic_pt.minimal_period_dvd
    rw [is_periodic_pt, is_fixed_pt, iterate_mul]
    exact is_periodic_pt_minimal_period _ _

theorem minimal_period_iterate_eq_div_gcd (h : n ≠ 0) :
    minimal_period (f^[n]) x = minimal_period f x / Nat.gcdₓ (minimal_period f x) n :=
  minimal_period_iterate_eq_div_gcd_aux $ gcd_pos_of_pos_right _ (Nat.pos_of_ne_zeroₓ h)

theorem minimal_period_iterate_eq_div_gcd' (h : x ∈ periodic_pts f) :
    minimal_period (f^[n]) x = minimal_period f x / Nat.gcdₓ (minimal_period f x) n :=
  minimal_period_iterate_eq_div_gcd_aux $ gcd_pos_of_pos_left n (minimal_period_pos_iff_mem_periodic_pts.mpr h)

end Function

