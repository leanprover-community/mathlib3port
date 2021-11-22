import Mathbin.Tactic.Hint

/-!

# Intuitionistic tautology (`itauto`) decision procedure

The `itauto` tactic will prove any intuitionistic tautology. It implements the well known
`G4ip` algorithm:
[Dyckhoff, *Contraction-free sequent calculi for intuitionistic logic*][dyckhoff_1992].

All built in propositional connectives are supported: `true`, `false`, `and`, `or`, `implies`,
`not`, `iff`, `xor`, as well as `eq` and `ne` on propositions. Anything else, including definitions
and predicate logical connectives (`forall` and `exists`), are not supported, and will have to be
simplified or instantiated before calling this tactic.

The resulting proofs will never use any axioms except possibly `propext`, and `propext` is only
used if the input formula contains an equality of propositions `p = q`.

## Implementation notes

The core logic of the prover is in three functions:

* `prove : context → prop → state_t ℕ option proof`: The main entry point.
  Gets a context and a goal, and returns a `proof` object or fails, using `state_t ℕ` for the name
  generator.
* `search : context → prop → state_t ℕ option proof`: Same meaning as `proof`, called during the
  search phase (see below).
* `context.add : prop → proof → context → except (prop → proof) context`: Adds a proposition with
  its proof into the context, but it also does some simplifications on the spot while doing so.
  It will either return the new context, or if it happens to notice a proof of false, it will
  return a function to compute a proof of any proposition in the original context.

The intuitionistic logic rules are separated into three groups:

* level 1: No splitting, validity preserving: apply whenever you can.
  Left rules in `context.add`, right rules in `prove`.
  * `context.add`:
    * simplify `Γ, ⊤ ⊢ B` to `Γ ⊢ B`
    * `Γ, ⊥ ⊢ B` is true
    * simplify `Γ, A ∧ B ⊢ C` to `Γ, A, B ⊢ C`
    * simplify `Γ, ⊥ → A ⊢ B` to `Γ ⊢ B`
    * simplify `Γ, ⊤ → A ⊢ B` to `Γ, A ⊢ B`
    * simplify `Γ, A ∧ B → C ⊢ D` to `Γ, A → B → C ⊢ D`
    * simplify `Γ, A ∨ B → C ⊢ D` to `Γ, A → C, B → C ⊢ D`
  * `prove`:
    * `Γ ⊢ ⊤` is true
    * simplify `Γ ⊢ A → B` to `Γ, A ⊢ B`
  * `search`:
    * `Γ, P ⊢ P` is true
    * simplify `Γ, P, P → A ⊢ B` to `Γ, P, A ⊢ B`
* level 2: Splitting rules, validity preserving: apply after level 1 rules. Done in `prove`
  * simplify `Γ ⊢ A ∧ B` to `Γ ⊢ A` and `Γ ⊢ B`
  * simplify `Γ, A ∨ B ⊢ C` to `Γ, A ⊢ C` and `Γ, B ⊢ C`
* level 3: Splitting rules, not validity preserving: apply only if nothing else applies.
  Done in `search`
  * `Γ ⊢ A ∨ B` follows from `Γ ⊢ A`
  * `Γ ⊢ A ∨ B` follows from `Γ ⊢ B`
  * `Γ, (A₁ → A₂) → C ⊢ B` follows from `Γ, A₂ → C, A₁ ⊢ A₂` and `Γ, C ⊢ B`

This covers the core algorithm, which only handles `true`, `false`, `and`, `or`, and `implies`.
For `iff` and `eq`, we treat them essentially the same as `(p → q) ∧ (q → p)`, although we use
a different `prop` representation because we have to remember to apply different theorems during
replay. For definitions like `not` and `xor`, we just eagerly unfold them. (This could potentially
cause a blowup issue for `xor`, but it isn't used very often anyway. We could add it to the `prop`
grammar if it matters.)

## Tags

propositional logic, intuitionistic logic, decision procedure
-/


namespace Tactic

namespace Itauto

-- error in Tactic.Itauto: ././Mathport/Syntax/Translate/Basic.lean:702:9: unsupported derive handler has_reflect
/-- Different propositional constructors that are variants of "and" for the purposes of the
theorem prover. -/ @[derive #["[", expr has_reflect, ",", expr decidable_eq, "]"]] inductive and_kind
| and
| iff
| eq

instance  : Inhabited and_kind :=
  ⟨and_kind.and⟩

-- error in Tactic.Itauto: ././Mathport/Syntax/Translate/Basic.lean:702:9: unsupported derive handler has_reflect
/-- A reified inductive type for propositional logic. -/
@[derive #["[", expr has_reflect, ",", expr decidable_eq, "]"]]
inductive prop : Type
| var : exprℕ() → prop
| true : prop
| false : prop
| and' : and_kind → prop → prop → prop
| or : prop → prop → prop
| imp : prop → prop → prop

/-- Constructor for `p ∧ q`. -/
@[matchPattern]
def prop.and : prop → prop → prop :=
  prop.and' and_kind.and

/-- Constructor for `p ↔ q`. -/
@[matchPattern]
def prop.iff : prop → prop → prop :=
  prop.and' and_kind.iff

/-- Constructor for `p = q`. -/
@[matchPattern]
def prop.eq : prop → prop → prop :=
  prop.and' and_kind.eq

/-- Constructor for `¬ p`. -/
@[matchPattern]
def prop.not (a : prop) : prop :=
  a.imp prop.false

/-- Constructor for `xor p q`. -/
@[matchPattern]
def prop.xor (a b : prop) : prop :=
  (a.and b.not).Or (b.and a.not)

instance  : Inhabited prop :=
  ⟨prop.true⟩

/-- Given the contents of an `and` variant, return the two conjuncts. -/
def and_kind.sides : and_kind → prop → prop → prop × prop
| and_kind.and, A, B => (A, B)
| _, A, B => (A.imp B, B.imp A)

/-- Debugging printer for propositions. -/
unsafe def prop.to_format : prop → format
| prop.var i => f! "v{i}"
| prop.true => f!"⊤"
| prop.false => f!"⊥"
| prop.and p q => f! "({p.to_format } ∧ {q.to_format})"
| prop.iff p q => f! "({p.to_format } ↔ {q.to_format})"
| prop.eq p q => f! "({p.to_format } = {q.to_format})"
| prop.or p q => f! "({p.to_format } ∨ {q.to_format})"
| prop.imp p q => f! "({p.to_format } → {q.to_format})"

unsafe instance  : has_to_format prop :=
  ⟨prop.to_format⟩

section 

open Ordering

-- error in Tactic.Itauto: ././Mathport/Syntax/Translate/Basic.lean:340:40: in exacts: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- A comparator for `and_kind`. (There should really be a derive handler for this.) -/
def and_kind.cmp (p q : and_kind) : ordering :=
by { cases [expr p] []; cases [expr q] [],
  exacts ["[", expr eq, ",", expr lt, ",", expr lt, ",", expr gt, ",", expr eq, ",", expr lt, ",", expr gt, ",", expr gt, ",", expr eq, "]"] }

-- error in Tactic.Itauto: ././Mathport/Syntax/Translate/Basic.lean:340:40: in exacts: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- A comparator for propositions. (There should really be a derive handler for this.) -/
def prop.cmp (p q : prop) : ordering :=
begin
  induction [expr p] [] ["with", "_", ident ap, "_", "_", ident p₁, ident p₂, "_", "_", ident p₁, ident p₂, "_", "_", ident p₁, ident p₂, "_", "_", ident p₁, ident p₂] ["generalizing", ident q]; cases [expr q] [],
  case [ident var, ident var] { exact [expr cmp p q] },
  case [ident true, ident true] { exact [expr eq] },
  case [ident false, ident false] { exact [expr eq] },
  case [ident and', ident and', ":", ident aq, ident q₁, ident q₂] { exact [expr (ap.cmp aq).or_else ((p₁ q₁).or_else (p₂ q₂))] },
  case [ident or, ident or, ":", ident q₁, ident q₂] { exact [expr (p₁ q₁).or_else (p₂ q₂)] },
  case [ident imp, ident imp, ":", ident q₁, ident q₂] { exact [expr (p₁ q₁).or_else (p₂ q₂)] },
  exacts ["[", expr lt, ",", expr lt, ",", expr lt, ",", expr lt, ",", expr lt, ",", expr gt, ",", expr lt, ",", expr lt, ",", expr lt, ",", expr lt, ",", expr gt, ",", expr gt, ",", expr lt, ",", expr lt, ",", expr lt, ",", expr gt, ",", expr gt, ",", expr gt, ",", expr lt, ",", expr lt, ",", expr gt, ",", expr gt, ",", expr gt, ",", expr gt, ",", expr lt, ",", expr gt, ",", expr gt, ",", expr gt, ",", expr gt, ",", expr gt, "]"]
end

instance  : LT prop :=
  ⟨fun p q => p.cmp q = lt⟩

instance  : DecidableRel (@LT.lt prop _) :=
  fun _ _ => Ordering.decidableEq _ _

end 

-- error in Tactic.Itauto: ././Mathport/Syntax/Translate/Basic.lean:702:9: unsupported derive handler has_reflect
/-- A reified inductive proof type for intuitionistic propositional logic. -/
@[derive #[expr has_reflect]]
inductive proof
| hyp (n : name) : proof
| triv : proof
| exfalso' (p : proof) : proof
| intro (x : name) (p : proof) : proof
| and_left (ak : and_kind) (p : proof) : proof
| and_right (ak : and_kind) (p : proof) : proof
| and_intro (ak : and_kind) (p₁ p₂ : proof) : proof
| curry (ak : and_kind) (p : proof) : proof
| curry₂ (ak : and_kind) (p q : proof) : proof
| app' : proof → proof → proof
| or_imp_left (p : proof) : proof
| or_imp_right (p : proof) : proof
| or_inl (p : proof) : proof
| or_inr (p : proof) : proof
| or_elim (p₁ : proof) (x : name) (p₂ p₃ : proof) : proof
| imp_imp_simp (x : name) (p : proof) : proof

instance  : Inhabited proof :=
  ⟨proof.triv⟩

/-- Debugging printer for proof objects. -/
unsafe def proof.to_format : proof → format
| proof.hyp i => to_fmt i
| proof.triv => "triv"
| proof.exfalso' p => f! "(exfalso {p.to_format})"
| proof.intro x p => f! "(λ {x }, {p.to_format})"
| proof.and_left _ p => f! "{p.to_format} .1"
| proof.and_right _ p => f! "{p.to_format} .2"
| proof.and_intro _ p q => f! "⟨{p.to_format }, {q.to_format}⟩"
| proof.curry _ p => f! "(curry {p.to_format})"
| proof.curry₂ _ p q => f! "(curry {p.to_format } {q.to_format})"
| proof.app' p q => f! "({p.to_format } {q.to_format})"
| proof.or_imp_left p => f! "(or_imp_left {p.to_format})"
| proof.or_imp_right p => f! "(or_imp_right {p.to_format})"
| proof.or_inl p => f! "(or.inl {p.to_format})"
| proof.or_inr p => f! "(or.inr {p.to_format})"
| proof.or_elim p x q r => f! "({p.to_format }.elim (λ {x }, {q.to_format }) (λ {x }, {r.to_format})"
| proof.imp_imp_simp _ p => f! "(imp_imp_simp {p.to_format})"

unsafe instance  : has_to_format proof :=
  ⟨proof.to_format⟩

/-- A variant on `proof.exfalso'` that performs opportunistic simplification. -/
unsafe def proof.exfalso : prop → proof → proof
| prop.false, p => p
| A, p => proof.exfalso' p

/-- A variant on `proof.app'` that performs opportunistic simplification.
(This doesn't do full normalization because we don't want the proof size to blow up.) -/
unsafe def proof.app : proof → proof → proof
| proof.curry ak p, q => proof.curry₂ ak p q
| proof.curry₂ ak p q, r => p.app (q.and_intro ak r)
| proof.or_imp_left p, q => p.app q.or_inl
| proof.or_imp_right p, q => p.app q.or_inr
| proof.imp_imp_simp x p, q => p.app (proof.intro x q)
| p, q => p.app' q

/-- Get a new name in the pattern `h0, h1, h2, ...` -/
@[inline]
unsafe def fresh_name {m} [Monadₓ m] : StateTₓ ℕ m Name :=
  ⟨fun n => pure (mkSimpleName ("h" ++ toString n), n+1)⟩

/-- The context during proof search is a map from propositions to proof values. -/
unsafe def context :=
  native.rb_map prop proof

/-- Debug printer for the context. -/
unsafe def context.to_format (Γ : context) : format :=
  Γ.fold ""$ fun P p f => P.to_format ++ " := " ++ p.to_format ++ ",\n" ++ f

unsafe instance  : has_to_format context :=
  ⟨context.to_format⟩

/-- Insert a proposition and its proof into the context, as in `have : A := p`. This will eagerly
apply all level 1 rules on the spot, which are rules that don't split the goal and are validity
preserving: specifically, we drop `⊤` and `A → ⊤` hypotheses, close the goal if we find a `⊥`
hypothesis, split all conjunctions, and also simplify `⊥ → A` (drop), `⊤ → A` (simplify to `A`),
`A ∧ B → C` (curry to `A → B → C`) and `A ∨ B → C` (rewrite to `(A → C) ∧ (B → C)` and split). -/
unsafe def context.add : prop → proof → context → Except (prop → proof) context
| prop.true, p, Γ => pure Γ
| prop.false, p, Γ => Except.error fun A => proof.exfalso A p
| prop.and' ak A B, p, Γ =>
  do 
    let (A, B) := ak.sides A B 
    let Γ ← Γ.add A (p.and_left ak)
    Γ.add B (p.and_right ak)
| prop.imp prop.false A, p, Γ => pure Γ
| prop.imp prop.true A, p, Γ => Γ.add A (p.app proof.triv)
| prop.imp (prop.and' ak A B) C, p, Γ =>
  let (A, B) := ak.sides A B 
  Γ.add (prop.imp A (B.imp C)) (p.curry ak)
| prop.imp (prop.or A B) C, p, Γ =>
  do 
    let Γ ← Γ.add (A.imp C) p.or_imp_left 
    Γ.add (B.imp C) p.or_imp_right
| prop.imp A prop.true, p, Γ => pure Γ
| A, p, Γ => pure (Γ.insert A p)

/-- Add `A` to the context `Γ` with proof `p`. This version of `context.add` takes a continuation
and a target proposition `B`, so that in the case that `⊥` is found we can skip the continuation
and just prove `B` outright. -/
@[inline]
unsafe def context.with_add {m} [Monadₓ m] (Γ : context) (A : prop) (p : proof) (B : prop)
  (f : context → prop → m proof) : m proof :=
  match Γ.add A p with 
  | Except.ok Γ_A => f Γ_A B
  | Except.error p => pure (p B)

/-- The search phase, which deals with the level 3 rules, which are rules that are not validity
preserving and so require proof search. One obvious one is the or-introduction rule: we prove
`A ∨ B` by proving `A` or `B`, and we might have to try one and backtrack.

There are two rules dealing with implication in this category: `p, p -> C ⊢ B` where `p` is an
atom (which is safe if we can find it but often requires the right search to expose the `p`
assumption), and `(A₁ → A₂) → C ⊢ B`. We decompose the double implication into two subgoals: one to
prove `A₁ → A₂`, which can be written `A₂ → C, A₁ ⊢ A₂` (where we used `A₁` to simplify
`(A₁ → A₂) → C`), and one to use the consequent, `C ⊢ B`. The search here is that there are
potentially many implications to split like this, and we have to try all of them if we want to be
complete. -/
unsafe def search (prove : context → prop → StateTₓ ℕ Option proof) : context → prop → StateTₓ ℕ Option proof
| Γ, B =>
  match Γ.find B with 
  | some p => pure p
  | none =>
    match B with 
    | prop.or B₁ B₂ => proof.or_inl <$> prove Γ B₁ <|> proof.or_inr <$> prove Γ B₂
    | _ =>
      ⟨fun n =>
          Γ.fold none$
            fun A p r =>
              r <|>
                match A with 
                | prop.imp A' C =>
                  match Γ.find A' with 
                  | some q => (context.with_add (Γ.erase A) C (p.app q) B prove).1 n
                  | none =>
                    match A' with 
                    | prop.imp A₁ A₂ =>
                      (do 
                            let Γ : context := Γ.erase A 
                            let a ← fresh_name 
                            let p₁ ←
                              Γ.with_add A₁ (proof.hyp a) A₂$
                                  fun Γ_A₁ A₂ => Γ_A₁.with_add (prop.imp A₂ C) (proof.imp_imp_simp a p) A₂ prove 
                            Γ.with_add C (p.app (proof.intro a p₁)) B prove :
                          StateTₓ ℕ Option proof).1
                        n
                    | _ => none
                | _ => none⟩

/-- The main prover. This receives a context of proven or assumed lemmas and a target proposition,
and returns a proof or `none` (with state for the fresh variable generator).
The intuitionistic logic rules are separated into three groups:

* level 1: No splitting, validity preserving: apply whenever you can.
  Left rules in `context.add`, right rules in `prove`
* level 2: Splitting rules, validity preserving: apply after level 1 rules. Done in `prove`
* level 3: Splitting rules, not validity preserving: apply only if nothing else applies.
  Done in `search`

The level 1 rules on the right of the turnstile are `Γ ⊢ ⊤` and `Γ ⊢ A → B`, these are easy to
handle. The rule `Γ ⊢ A ∧ B` is a level 2 rule, also handled here. If none of these apply, we try
the level 2 rule `A ∨ B ⊢ C` by searching the context and splitting all ors we find. Finally, if
we don't make any more progress, we go to the search phase.
-/
unsafe def prove : context → prop → StateTₓ ℕ Option proof
| Γ, prop.true => pure proof.triv
| Γ, prop.imp A B =>
  do 
    let a ← fresh_name 
    proof.intro a <$> Γ.with_add A (proof.hyp a) B prove
| Γ, prop.and' ak A B =>
  do 
    let (A, B) := ak.sides A B 
    let p ← prove Γ A 
    let q ← prove Γ B 
    pure (p.and_intro ak q)
| Γ, B =>
  Γ.fold (fun b Γ => cond b prove (search prove) Γ B)
    (fun A p IH b Γ =>
      match A with 
      | prop.or A₁ A₂ =>
        do 
          let Γ : context := Γ.erase A 
          let a ← fresh_name 
          let p₁ ← Γ.with_add A₁ (proof.hyp a) B fun Γ _ => IH tt Γ 
          let p₂ ← Γ.with_add A₂ (proof.hyp a) B fun Γ _ => IH tt Γ 
          pure (proof.or_elim p a p₁ p₂)
      | _ => IH b Γ)
    ff Γ

/-- Reifies an atomic or otherwise unrecognized proposition. If it is defeq to a proposition we
have already allocated, we reuse it, otherwise we name it with a new index. -/
unsafe def reify_atom (atoms : ref (Buffer expr)) (e : expr) : tactic prop :=
  do 
    let vec ← read_ref atoms 
    let o ← try_core$ vec.iterate failure fun i e' r => r <|> is_def_eq e e' >> pure i.1
    match o with 
      | none => write_ref atoms (vec.push_back e) $> prop.var vec.size
      | some i => pure$ prop.var i

/-- Reify an `expr` into a `prop`, allocating anything non-propositional as an atom in the
`atoms` list. -/
unsafe def reify (atoms : ref (Buffer expr)) : expr → tactic prop
| quote True => pure prop.true
| quote False => pure prop.false
| quote ¬%%a => prop.not <$> reify a
| quote (%%a) ∧ %%b => prop.and <$> reify a <*> reify b
| quote (%%a) ∨ %%b => prop.or <$> reify a <*> reify b
| quote (%%a) ↔ %%b => prop.iff <$> reify a <*> reify b
| quote Xorₓ (%%a) (%%b) => prop.xor <$> reify a <*> reify b
| quote @Eq Prop (%%a) (%%b) => prop.eq <$> reify a <*> reify b
| quote @Ne Prop (%%a) (%%b) => prop.not <$> (prop.eq <$> reify a <*> reify b)
| quote Implies (%%a) (%%b) => prop.imp <$> reify a <*> reify b
| e@(quote (%%a) → %%b) => if b.has_var then reify_atom atoms e else prop.imp <$> reify a <*> reify b
| e => reify_atom atoms e

/-- Once we have a proof object, we have to apply it to the goal. (Some of these cases are a bit
annoying because `applyc` gets the arguments wrong sometimes so we have to use `to_expr` instead.)
-/
unsafe def apply_proof : name_map expr → proof → tactic Unit
| Γ, proof.hyp n =>
  do 
    let e ← Γ.find n 
    exact e
| Γ, proof.triv => triv
| Γ, proof.exfalso' p =>
  do 
    let t ← mk_mvar 
    to_expr (pquote False.elim (%%t)) tt ff >>= exact 
    let gs ← get_goals 
    set_goals (t :: gs)
    apply_proof Γ p
| Γ, proof.intro x p =>
  do 
    let e ← intro_core x 
    apply_proof (Γ.insert x e) p
| Γ, proof.and_left and_kind.and p =>
  do 
    let t ← mk_mvar 
    to_expr (pquote And.left (%%t)) tt ff >>= exact 
    let gs ← get_goals 
    set_goals (t :: gs)
    apply_proof Γ p
| Γ, proof.and_left and_kind.iff p =>
  do 
    let t ← mk_mvar 
    to_expr (pquote Iff.mp (%%t)) tt ff >>= exact 
    let gs ← get_goals 
    set_goals (t :: gs)
    apply_proof Γ p
| Γ, proof.and_left and_kind.eq p =>
  do 
    let t ← mk_mvar 
    to_expr (pquote cast (%%t)) tt ff >>= exact 
    let gs ← get_goals 
    set_goals (t :: gs)
    apply_proof Γ p
| Γ, proof.and_right and_kind.and p =>
  do 
    let t ← mk_mvar 
    to_expr (pquote And.right (%%t)) tt ff >>= exact 
    let gs ← get_goals 
    set_goals (t :: gs)
    apply_proof Γ p
| Γ, proof.and_right and_kind.iff p =>
  do 
    let t ← mk_mvar 
    to_expr (pquote Iff.mpr (%%t)) tt ff >>= exact 
    let gs ← get_goals 
    set_goals (t :: gs)
    apply_proof Γ p
| Γ, proof.and_right and_kind.eq p =>
  do 
    let t ← mk_mvar 
    to_expr (pquote cast (Eq.symm (%%t))) tt ff >>= exact 
    let gs ← get_goals 
    set_goals (t :: gs)
    apply_proof Γ p
| Γ, proof.and_intro and_kind.and p q =>
  do 
    let t₁ ← mk_mvar 
    let t₂ ← mk_mvar 
    to_expr (pquote And.intro (%%t₁) (%%t₂)) tt ff >>= exact 
    let gs ← get_goals 
    set_goals (t₁ :: t₂ :: gs)
    apply_proof Γ p >> apply_proof Γ q
| Γ, proof.and_intro and_kind.iff p q =>
  do 
    let t₁ ← mk_mvar 
    let t₂ ← mk_mvar 
    to_expr (pquote Iff.intro (%%t₁) (%%t₂)) tt ff >>= exact 
    let gs ← get_goals 
    set_goals (t₁ :: t₂ :: gs)
    apply_proof Γ p >> apply_proof Γ q
| Γ, proof.and_intro and_kind.eq p q =>
  do 
    let t₁ ← mk_mvar 
    let t₂ ← mk_mvar 
    to_expr (pquote propext (Iff.intro (%%t₁) (%%t₂))) tt ff >>= exact 
    let gs ← get_goals 
    set_goals (t₁ :: t₂ :: gs)
    apply_proof Γ p >> apply_proof Γ q
| Γ, proof.curry ak p =>
  do 
    let e ← intro_core `_ 
    let n := e.local_uniq_name 
    apply_proof (Γ.insert n e) (proof.curry₂ ak p (proof.hyp n))
| Γ, proof.curry₂ ak p q =>
  do 
    let e ← intro_core `_ 
    let n := e.local_uniq_name 
    apply_proof (Γ.insert n e) (p.app (q.and_intro ak (proof.hyp n)))
| Γ, proof.app' p q =>
  do 
    let A ← mk_meta_var (expr.sort level.zero)
    let B ← mk_meta_var (expr.sort level.zero)
    let g₁ ← mk_meta_var (quote (%%A : Prop) → (%%B : Prop))
    let g₂ ← mk_meta_var A 
    let g :: gs ← get_goals 
    unify (g₁ g₂) g 
    set_goals (g₁ :: g₂ :: gs) >> apply_proof Γ p >> apply_proof Γ q
| Γ, proof.or_imp_left p =>
  do 
    let e ← intro_core `_ 
    let n := e.local_uniq_name 
    apply_proof (Γ.insert n e) (p.app (proof.hyp n).or_inl)
| Γ, proof.or_imp_right p =>
  do 
    let e ← intro_core `_ 
    let n := e.local_uniq_name 
    apply_proof (Γ.insert n e) (p.app (proof.hyp n).or_inr)
| Γ, proof.or_inl p =>
  do 
    let t ← mk_mvar 
    to_expr (pquote Or.inl (%%t)) tt ff >>= exact 
    let gs ← get_goals 
    set_goals (t :: gs)
    apply_proof Γ p
| Γ, proof.or_inr p =>
  do 
    let t ← mk_mvar 
    to_expr (pquote Or.inr (%%t)) tt ff >>= exact 
    let gs ← get_goals 
    set_goals (t :: gs)
    apply_proof Γ p
| Γ, proof.or_elim p x p₁ p₂ =>
  do 
    let t₁ ← mk_mvar 
    let t₂ ← mk_mvar 
    let t₃ ← mk_mvar 
    to_expr (pquote Or.elim (%%t₁) (%%t₂) (%%t₃)) tt ff >>= exact 
    let gs ← get_goals 
    set_goals (t₁ :: t₂ :: t₃ :: gs)
    apply_proof Γ p 
    let e ← intro_core x 
    apply_proof (Γ.insert x e) p₁ 
    let e ← intro_core x 
    apply_proof (Γ.insert x e) p₂
| Γ, proof.imp_imp_simp x p =>
  do 
    let e ← intro_core `_ 
    let n := e.local_uniq_name 
    apply_proof (Γ.insert n e) (p.app (proof.intro x (proof.hyp n)))

end Itauto

namespace Interactive

open Itauto

/-- A decision procedure for intuitionistic propositional logic. Unlike `finish` and `tauto!` this
tactic never uses the law of excluded middle, and the proof search is tailored for this use case.

```lean
example (p : Prop) : ¬ (p ↔ ¬ p) := by itauto
```
-/
unsafe def itauto : tactic Unit :=
  using_new_ref mkBuffer$
    fun atoms =>
      using_new_ref mk_name_map$
        fun hs =>
          do 
            let t ← target 
            let t ← mcond (is_prop t) (reify atoms t) (tactic.exfalso $> prop.false)
            let hyps ← local_context 
            let Γ ←
              hyps.mfoldl
                  (fun Γ : Except (prop → proof) context h =>
                    do 
                      let e ← infer_type h 
                      mcond (is_prop e)
                          (do 
                            let A ← reify atoms e 
                            let n := h.local_uniq_name 
                            read_ref hs >>= fun Γ => write_ref hs (Γ.insert n h)
                            pure (Γ >>= fun Γ' => Γ'.add A (proof.hyp n)))
                          (pure Γ))
                  (Except.ok (native.rb_map.mk _ _))
            let o :=
              StateTₓ.run
                (match Γ with 
                | Except.ok Γ => prove Γ t
                | Except.error p => pure (p t))
                0
            match o with 
              | none => fail "itauto failed"
              | some (p, _) =>
                do 
                  let hs ← read_ref hs 
                  apply_proof hs p

add_hint_tactic itauto

add_tactic_doc
  { Name := "itauto", category := DocCategory.tactic, declNames := [`tactic.interactive.itauto],
    tags := ["logic", "propositional logic", "intuitionistic logic", "decision procedure"] }

end Interactive

end Tactic

