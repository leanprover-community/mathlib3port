import Mathbin.Data.Fin.Fin2 
import Mathbin.Data.Pfun 
import Mathbin.Data.Vector3 
import Mathbin.NumberTheory.Pell

/-!
# Diophantine functions and Matiyasevic's theorem

Hilbert's tenth problem asked whether there exists an algorithm which for a given integer polynomial
determines whether this polynomial has integer solutions. It was answered in the negative in 1970,
the final step being completed by Matiyasevic who showed that the power function is Diophantine.

Here a function is called Diophantine if its graph is Diophantine as a set. A subset `S ⊆ ℕ ^ α` in
turn is called Diophantine if there exists an integer polynomial on `α ⊕ β` such that `v ∈ S` iff
there exists `t : ℕ^β` with `p (v, t) = 0`.

## Main definitions

* `is_poly`: a predicate stating that a function is a multivariate integer polynomial.
* `poly`: the type of multivariate integer polynomial functions.
* `dioph`: a predicate stating that a set `S ⊆ ℕ^α` is Diophantine, i.e. that
* `dioph_fn`: a predicate on a function stating that it is Diophantine in the sense that its graph
  is Diophantine as a set.

## Main statements

* `pell_dioph` states that solutions to Pell's equation form a Diophantine set.
* `pow_dioph` states that the power function is Diophantine, a version of Matiyasevic's theorem.

## References

* [M. Carneiro, _A Lean formalization of Matiyasevic's theorem_][carneiro2018matiyasevic]
* [M. Davis, _Hilbert's tenth problem is unsolvable_][MR317916]

## Tags

Matiyasevic's theorem, Hilbert's tenth problem

## TODO

* Finish the solution of Hilbert's tenth problem.
* Connect `poly` to `mv_polynomial`
-/


universe u

open Nat Function

namespace Int

theorem eq_nat_abs_iff_mul x n : nat_abs x = n ↔ ((x - n)*x+n) = 0 :=
  by 
    refine' Iff.trans _ mul_eq_zero.symm 
    refine' Iff.trans _ (or_congr sub_eq_zero add_eq_zero_iff_eq_neg).symm 
    exact
      ⟨fun e =>
          by 
            rw [←e] <;> apply nat_abs_eq,
        fun o =>
          by 
            cases o <;> subst x <;> simp [nat_abs_of_nat]⟩

end Int

open Fin2

/-- `list_all p l` is equivalent to `∀ a ∈ l, p a`, but unfolds directly to a conjunction,
  i.e. `list_all p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
@[simp]
def ListAll {α} (p : α → Prop) : List α → Prop
| [] => True
| x :: [] => p x
| x :: l => p x ∧ ListAll l

@[simp]
theorem list_all_cons {α} (p : α → Prop) (x : α) : ∀ (l : List α), ListAll p (x :: l) ↔ p x ∧ ListAll p l
| [] => (and_trueₓ _).symm
| x :: l => Iff.rfl

theorem list_all_iff_forall {α} (p : α → Prop) : ∀ (l : List α), ListAll p l ↔ ∀ x (_ : x ∈ l), p x
| [] => (iff_true_intro$ List.ball_nil _).symm
| x :: l =>
  by 
    rw [List.ball_consₓ, ←list_all_iff_forall l] <;> simp 

theorem ListAll.imp {α} {p q : α → Prop} (h : ∀ x, p x → q x) : ∀ {l : List α}, ListAll p l → ListAll q l
| [] => id
| x :: l =>
  by 
    simpa using And.imp (h x) ListAll.imp

@[simp]
theorem list_all_map {α β} {p : β → Prop} (f : α → β) {l : List α} : ListAll p (l.map f) ↔ ListAll (p ∘ f) l :=
  by 
    induction l <;> simp 

theorem list_all_congr {α} {p q : α → Prop} (h : ∀ x, p x ↔ q x) {l : List α} : ListAll p l ↔ ListAll q l :=
  ⟨ListAll.imp fun x => (h x).1, ListAll.imp fun x => (h x).2⟩

instance decidableListAll {α} (p : α → Prop) [DecidablePred p] (l : List α) : Decidable (ListAll p l) :=
  decidableOfDecidableOfIff
    (by 
      infer_instance)
    (list_all_iff_forall _ _).symm

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A predicate asserting that a function is a multivariate integer polynomial.
  (We are being a bit lazy here by allowing many representations for multiplication,
  rather than only allowing monomials and addition, but the definition is equivalent
  and this is easier to use.) -/ inductive is_poly {α} : ((α → exprℕ()) → exprℤ()) → exprProp()
| proj : ∀ i, is_poly (λ x : α → exprℕ(), x i)
| const : ∀ n : exprℤ(), is_poly (λ x : α → exprℕ(), n)
| sub : ∀ {f g : (α → exprℕ()) → exprℤ()}, is_poly f → is_poly g → is_poly (λ x, «expr - »(f x, g x))
| mul : ∀ {f g : (α → exprℕ()) → exprℤ()}, is_poly f → is_poly g → is_poly (λ x, «expr * »(f x, g x))

/-- The type of multivariate integer polynomials -/
def Poly (α : Type u) :=
  { f : (α → ℕ) → ℤ // IsPoly f }

namespace Poly

section 

parameter {α : Type u}

instance  : CoeFun (Poly α) fun _ => (α → ℕ) → ℤ :=
  ⟨fun f => f.1⟩

/-- The underlying function of a `poly` is a polynomial -/
theorem isp (f : Poly α) : IsPoly f :=
  f.2

/-- Extensionality for `poly α` -/
theorem ext {f g : Poly α} (e : ∀ x, f x = g x) : f = g :=
  Subtype.eq (funext e)

/-- Construct a `poly` given an extensionally equivalent `poly`. -/
def subst (f : Poly α) (g : (α → ℕ) → ℤ) (e : ∀ x, f x = g x) : Poly α :=
  ⟨g,
    by 
      rw [←(funext e : coeFn f = g)] <;> exact f.isp⟩

@[simp]
theorem subst_eval f g e x : subst f g e x = g x :=
  rfl

/-- The `i`th projection function, `x_i`. -/
def proj i : Poly α :=
  ⟨_, IsPoly.proj i⟩

@[simp]
theorem proj_eval i x : proj i x = x i :=
  rfl

/-- The constant function with value `n : ℤ`. -/
def const n : Poly α :=
  ⟨_, IsPoly.const n⟩

@[simp]
theorem const_eval n x : const n x = n :=
  rfl

/-- The zero polynomial -/
def zero : Poly α :=
  const 0

instance  : HasZero (Poly α) :=
  ⟨Poly.zero⟩

@[simp]
theorem zero_eval x : (0 : Poly α) x = 0 :=
  rfl

/-- The zero polynomial -/
def one : Poly α :=
  const 1

instance  : HasOne (Poly α) :=
  ⟨Poly.one⟩

@[simp]
theorem one_eval x : (1 : Poly α) x = 1 :=
  rfl

/-- Subtraction of polynomials -/
def sub : Poly α → Poly α → Poly α
| ⟨f, pf⟩, ⟨g, pg⟩ => ⟨_, IsPoly.sub pf pg⟩

instance  : Sub (Poly α) :=
  ⟨Poly.sub⟩

@[simp]
theorem sub_eval : ∀ f g x, (f - g : Poly α) x = f x - g x
| ⟨f, pf⟩, ⟨g, pg⟩, x => rfl

/-- Negation of a polynomial -/
def neg (f : Poly α) : Poly α :=
  0 - f

instance  : Neg (Poly α) :=
  ⟨Poly.neg⟩

@[simp]
theorem neg_eval f x : (-f : Poly α) x = -f x :=
  show (0 - f) x = _ by 
    simp 

/-- Addition of polynomials -/
def add : Poly α → Poly α → Poly α
| ⟨f, pf⟩, ⟨g, pg⟩ =>
  subst (⟨f, pf⟩ - -⟨g, pg⟩) _
    fun x =>
      show f x - (0 - g x) = f x+g x by 
        simp 

instance  : Add (Poly α) :=
  ⟨Poly.add⟩

@[simp]
theorem add_eval : ∀ f g x, (f+g : Poly α) x = f x+g x
| ⟨f, pf⟩, ⟨g, pg⟩, x => rfl

/-- Multiplication of polynomials -/
def mul : Poly α → Poly α → Poly α
| ⟨f, pf⟩, ⟨g, pg⟩ => ⟨_, IsPoly.mul pf pg⟩

instance  : Mul (Poly α) :=
  ⟨Poly.mul⟩

@[simp]
theorem mul_eval : ∀ f g x, (f*g : Poly α) x = f x*g x
| ⟨f, pf⟩, ⟨g, pg⟩, x => rfl

instance  : CommRingₓ (Poly α) :=
  by 
    refineStruct
        { add := (·+· : Poly α → Poly α → Poly α), zero := 0, neg := (Neg.neg : Poly α → Poly α), mul := ·*·, one := 1,
          sub := Sub.sub, npow := @npowRec _ ⟨(1 : Poly α)⟩ ⟨·*·⟩, nsmul := @nsmulRec _ ⟨(0 : Poly α)⟩ ⟨·+·⟩,
          zsmul := @zsmulRec _ ⟨(0 : Poly α)⟩ ⟨·+·⟩ ⟨neg⟩ } <;>
      intros  <;>
        try 
            rfl <;>
          refine' ext fun _ => _ <;> simp [sub_eq_add_neg, mul_addₓ, mul_left_commₓ, mul_commₓ, add_commₓ, add_assocₓ]

theorem induction {C : Poly α → Prop} (H1 : ∀ i, C (proj i)) (H2 : ∀ n, C (const n)) (H3 : ∀ f g, C f → C g → C (f - g))
  (H4 : ∀ f g, C f → C g → C (f*g)) (f : Poly α) : C f :=
  by 
    cases' f with f pf 
    induction' pf with i n f g pf pg ihf ihg f g pf pg ihf ihg 
    apply H1 
    apply H2 
    apply H3 _ _ ihf ihg 
    apply H4 _ _ ihf ihg

/-- The sum of squares of a list of polynomials. This is relevant for
  Diophantine equations, because it means that a list of equations
  can be encoded as a single equation: `x = 0 ∧ y = 0 ∧ z = 0` is
  equivalent to `x^2 + y^2 + z^2 = 0`. -/
def sumsq : List (Poly α) → Poly α
| [] => 0
| p :: ps => (p*p)+sumsq ps

theorem sumsq_nonneg x : ∀ l, 0 ≤ sumsq l x
| [] => le_reflₓ 0
| p :: ps =>
  by 
    rw [sumsq] <;> simp [-add_commₓ] <;> exact add_nonneg (mul_self_nonneg _) (sumsq_nonneg ps)

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sumsq_eq_zero (x) : ∀ l, «expr ↔ »(«expr = »(sumsq l x, 0), list_all (λ a : poly α, «expr = »(a x, 0)) l)
| «expr[ , ]»([]) := eq_self_iff_true _
| [«expr :: »/«expr :: »/«expr :: »/«expr :: »](p, ps) := by rw ["[", expr list_all_cons, ",", "<-", expr sumsq_eq_zero ps, "]"] []; rw [expr sumsq] []; simp [] [] [] ["[", "-", ident add_comm, "]"] [] []; exact [expr ⟨λ
  h : «expr = »(«expr + »(«expr * »(p x, p x), sumsq ps x), 0), have «expr = »(p x, 0), from «expr $ »(eq_zero_of_mul_self_eq_zero, le_antisymm (by rw ["<-", expr h] []; have [ident t] [] [":=", expr add_le_add_left (sumsq_nonneg x ps) «expr * »(p x, p x)]; rwa ["[", expr add_zero, "]"] ["at", ident t]) (mul_self_nonneg _)),
  ⟨this, by simp [] [] [] ["[", expr this, "]"] [] ["at", ident h]; exact [expr h]⟩, λ
  ⟨h1, h2⟩, by rw ["[", expr h1, ",", expr h2, "]"] []; refl⟩]

end 

/-- Map the index set of variables, replacing `x_i` with `x_(f i)`. -/
def remap {α β} (f : α → β) (g : Poly α) : Poly β :=
  ⟨fun v => g$ (v ∘ f),
    g.induction
      (fun i =>
        by 
          simp  <;> apply IsPoly.proj)
      (fun n =>
        by 
          simp  <;> apply IsPoly.const)
      (fun f g pf pg =>
        by 
          simp  <;> apply IsPoly.sub pf pg)
      fun f g pf pg =>
        by 
          simp  <;> apply IsPoly.mul pf pg⟩

@[simp]
theorem remap_eval {α β} (f : α → β) (g : Poly α) v : remap f g v = g (v ∘ f) :=
  rfl

end Poly

namespace Sum

/-- combine two functions into a function on the disjoint union -/
def join {α β γ} (f : α → γ) (g : β → γ) : Sum α β → γ :=
  by 
    refine' Sum.rec _ _ 
    exacts[f, g]

end Sum

local infixr:65 " ⊗ " => Sum.join

open Sum

namespace Option

/-- Functions from `option` can be combined similarly to `vector.cons` -/
def cons {α β} (a : β) (v : α → β) : Option α → β :=
  by 
    refine' Option.rec _ _ 
    exacts[a, v]

@[simp]
theorem cons_head_tail {α β} (v : Option α → β) : v none :: (v ∘ some) = v :=
  funext$
    fun o =>
      by 
        cases o <;> rfl

end Option

/-- A set `S ⊆ ℕ^α` is Diophantine if there exists a polynomial on
  `α ⊕ β` such that `v ∈ S` iff there exists `t : ℕ^β` with `p (v, t) = 0`. -/
def Dioph {α : Type u} (S : Set (α → ℕ)) : Prop :=
  ∃ (β : Type u)(p : Poly (Sum α β)), ∀ (v : α → ℕ), S v ↔ ∃ t, p (v ⊗ t) = 0

namespace Dioph

section 

variable{α β γ : Type u}

theorem ext {S S' : Set (α → ℕ)} (d : Dioph S) (H : ∀ v, S v ↔ S' v) : Dioph S' :=
  Eq.ndrec d$ show S = S' from Set.ext H

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem of_no_dummies
(S : set (α → exprℕ()))
(p : poly α)
(h : ∀ v : α → exprℕ(), «expr ↔ »(S v, «expr = »(p v, 0))) : dioph S :=
⟨ulift empty, p.remap inl, λ
 v, (h v).trans ⟨λ
  h, ⟨λ
   t, empty.rec _ t.down, by simp [] [] [] [] [] []; rw ["[", expr show «expr = »(«expr ∘ »(«expr ⊗ »(v, λ
       t : ulift empty, empty.rec _ t.down), inl), v), from rfl, ",", expr h, "]"] []⟩, λ
  ⟨t, ht⟩, by simp [] [] [] [] [] ["at", ident ht]; rwa ["[", expr show «expr = »(«expr ∘ »(«expr ⊗ »(v, t), inl), v), from rfl, "]"] ["at", ident ht]⟩⟩

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem inject_dummies_lem
(f : β → γ)
(g : γ → option β)
(inv : ∀ x, «expr = »(g (f x), some x))
(p : poly «expr ⊕ »(α, β))
(v : α → exprℕ()) : «expr ↔ »(«expr∃ , »((t), «expr = »(p «expr ⊗ »(v, t), 0)), «expr∃ , »((t), «expr = »(p.remap «expr ⊗ »(inl, «expr ∘ »(inr, f)) «expr ⊗ »(v, t), 0))) :=
begin
  simp [] [] [] [] [] [],
  refine [expr ⟨λ t, _, λ t, _⟩]; cases [expr t] ["with", ident t, ident ht],
  { have [] [":", expr «expr = »(«expr ∘ »(«expr ⊗ »(v, «expr ∘ »([«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](0, t), g)), «expr ⊗ »(inl, «expr ∘ »(inr, f))), «expr ⊗ »(v, t))] [":=", expr funext (λ
      s, by cases [expr s] ["with", ident a, ident b]; dsimp [] ["[", expr join, ",", expr («expr ∘ »), "]"] [] []; try { rw [expr inv] [] }; refl)],
    exact [expr ⟨«expr ∘ »([«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](0, t), g), by rwa [expr this] []⟩] },
  { have [] [":", expr «expr = »(«expr ⊗ »(v, «expr ∘ »(t, f)), «expr ∘ »(«expr ⊗ »(v, t), «expr ⊗ »(inl, «expr ∘ »(inr, f))))] [":=", expr funext (λ
      s, by cases [expr s] ["with", ident a, ident b]; refl)],
    exact [expr ⟨«expr ∘ »(t, f), by rwa [expr this] []⟩] }
end

theorem inject_dummies {S : Set (α → ℕ)} (f : β → γ) (g : γ → Option β) (inv : ∀ x, g (f x) = some x)
  (p : Poly (Sum α β)) (h : ∀ (v : α → ℕ), S v ↔ ∃ t, p (v ⊗ t) = 0) :
  ∃ q : Poly (Sum α γ), ∀ (v : α → ℕ), S v ↔ ∃ t, q (v ⊗ t) = 0 :=
  ⟨p.remap (inl ⊗ (inr ∘ f)), fun v => (h v).trans$ inject_dummies_lem f g inv _ _⟩

theorem reindex_dioph {S : Set (α → ℕ)} : ∀ (d : Dioph S) (f : α → β), Dioph fun v => S (v ∘ f)
| ⟨γ, p, pe⟩, f =>
  ⟨γ, p.remap ((inl ∘ f) ⊗ inr),
    fun v =>
      (pe _).trans$
        exists_congr$
          fun t =>
            suffices (v ∘ f) ⊗ t = (v ⊗ t ∘ (inl ∘ f) ⊗ inr)by 
              simp [this]
            funext$
              fun s =>
                by 
                  cases' s with a b <;> rfl⟩

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem dioph_list_all (l) (d : list_all dioph l) : dioph (λ v, list_all (λ S : set (α → exprℕ()), S v) l) :=
suffices «expr∃ , »((β)
 (pl : list (poly «expr ⊕ »(α, β))), ∀
 v, «expr ↔ »(list_all (λ
   S : set _, S v) l, «expr∃ , »((t), list_all (λ
    p : poly «expr ⊕ »(α, β), «expr = »(p «expr ⊗ »(v, t), 0)) pl))), from let ⟨β, pl, h⟩ := this in
⟨β, poly.sumsq pl, λ v, «expr $ »((h v).trans, «expr $ »(exists_congr, λ t, (poly.sumsq_eq_zero _ _).symm))⟩,
begin
  induction [expr l] [] ["with", ident S, ident l, ident IH] [],
  exact [expr ⟨ulift empty, «expr[ , ]»([]), λ
    v, by simp [] [] [] [] [] []; exact [expr ⟨λ ⟨t⟩, empty.rec _ t, trivial⟩]⟩],
  simp [] [] [] [] [] ["at", ident d],
  exact [expr let ⟨⟨β, p, pe⟩, dl⟩ := d, ⟨γ, pl, ple⟩ := IH dl in
   ⟨«expr ⊕ »(β, γ), [«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](p.remap «expr ⊗ »(inl, «expr ∘ »(inr, inl)), pl.map (λ
      q, q.remap «expr ⊗ »(inl, «expr ∘ »(inr, inr)))), λ
    v, by simp [] [] [] [] [] []; exact [expr iff.trans (and_congr (pe v) (ple v)) ⟨λ
      ⟨⟨m, hm⟩, ⟨n, hn⟩⟩, ⟨«expr ⊗ »(m, n), by rw ["[", expr show «expr = »(«expr ∘ »(«expr ⊗ »(v, «expr ⊗ »(m, n)), «expr ⊗ »(inl, «expr ∘ »(inr, inl))), «expr ⊗ »(v, m)), from «expr $ »(funext, λ
         s, by cases [expr s] ["with", ident a, ident b]; refl), "]"] []; exact [expr hm], by { refine [expr list_all.imp (λ
           q hq, _) hn],
         dsimp [] ["[", expr («expr ∘ »), "]"] [] [],
         rw ["[", expr show «expr = »(λ
           x : «expr ⊕ »(α, γ), «expr ⊗ »(v, «expr ⊗ »(m, n)) («expr ⊗ »(inl, λ
             x : γ, inr (inr x)) x), «expr ⊗ »(v, n)), from «expr $ »(funext, λ
           s, by cases [expr s] ["with", ident a, ident b]; refl), "]"] []; exact [expr hq] }⟩, λ
      ⟨t, hl, hr⟩, ⟨⟨«expr ∘ »(t, inl), by rwa ["[", expr show «expr = »(«expr ∘ »(«expr ⊗ »(v, t), «expr ⊗ »(inl, «expr ∘ »(inr, inl))), «expr ⊗ »(v, «expr ∘ »(t, inl))), from «expr $ »(funext, λ
          s, by cases [expr s] ["with", ident a, ident b]; refl), "]"] ["at", ident hl]⟩, ⟨«expr ∘ »(t, inr), by { refine [expr list_all.imp (λ
            q hq, _) hr],
          dsimp [] ["[", expr («expr ∘ »), "]"] [] ["at", ident hq],
          rwa ["[", expr show «expr = »(λ
            x : «expr ⊕ »(α, γ), «expr ⊗ »(v, t) («expr ⊗ »(inl, λ
              x : γ, inr (inr x)) x), «expr ⊗ »(v, «expr ∘ »(t, inr))), from «expr $ »(funext, λ
            s, by cases [expr s] ["with", ident a, ident b]; refl), "]"] ["at", ident hq] }⟩⟩⟩]⟩]
end

theorem and_dioph {S S' : Set (α → ℕ)} (d : Dioph S) (d' : Dioph S') : Dioph fun v => S v ∧ S' v :=
  dioph_list_all [S, S'] ⟨d, d'⟩

theorem or_dioph {S S' : Set (α → ℕ)} : ∀ (d : Dioph S) (d' : Dioph S'), Dioph fun v => S v ∨ S' v
| ⟨β, p, pe⟩, ⟨γ, q, qe⟩ =>
  ⟨Sum β γ, p.remap (inl ⊗ (inr ∘ inl))*q.remap (inl ⊗ (inr ∘ inr)),
    fun v =>
      by 
        refine'
          Iff.trans (or_congr ((pe v).trans _) ((qe v).trans _))
            (exists_or_distrib.symm.trans
              (exists_congr$
                fun t => (@mul_eq_zero _ _ _ (p (v ⊗ t ∘ inl ⊗ (inr ∘ inl))) (q (v ⊗ t ∘ inl ⊗ (inr ∘ inr)))).symm))
        exact inject_dummies_lem _ (some ⊗ fun _ => none) (fun x => rfl) _ _ 
        exact inject_dummies_lem _ ((fun _ => none) ⊗ some) (fun x => rfl) _ _⟩

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A partial function is Diophantine if its graph is Diophantine. -/
def dioph_pfun (f : «expr →. »(α → exprℕ(), exprℕ())) :=
dioph (λ v : option α → exprℕ(), f.graph («expr ∘ »(v, some), v none))

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A function is Diophantine if its graph is Diophantine. -/ def dioph_fn (f : (α → exprℕ()) → exprℕ()) :=
dioph (λ v : option α → exprℕ(), «expr = »(f «expr ∘ »(v, some), v none))

theorem reindex_dioph_fn {f : (α → ℕ) → ℕ} (d : dioph_fn f) (g : α → β) : dioph_fn fun v => f (v ∘ g) :=
  reindex_dioph d (Functor.map g)

theorem ex_dioph {S : Set (Sum α β → ℕ)} : Dioph S → Dioph fun v => ∃ x, S (v ⊗ x)
| ⟨γ, p, pe⟩ =>
  ⟨Sum β γ, p.remap ((inl ⊗ (inr ∘ inl)) ⊗ (inr ∘ inr)),
    fun v =>
      ⟨fun ⟨x, hx⟩ =>
          let ⟨t, ht⟩ := (pe _).1 hx
          ⟨x ⊗ t,
            by 
              simp  <;>
                rw
                    [show (v ⊗ x ⊗ t ∘ (inl ⊗ (inr ∘ inl)) ⊗ (inr ∘ inr)) = (v ⊗ x) ⊗ t from
                      funext$
                        fun s =>
                          by 
                            cases' s with a b <;>
                              try 
                                  cases a <;>
                                rfl] <;>
                  exact ht⟩,
        fun ⟨t, ht⟩ =>
          ⟨t ∘ inl,
            (pe _).2
              ⟨t ∘ inr,
                by 
                  simp  at ht <;>
                    rwa
                      [show (v ⊗ t ∘ (inl ⊗ (inr ∘ inl)) ⊗ (inr ∘ inr)) = (v ⊗ (t ∘ inl)) ⊗ (t ∘ inr) from
                        funext$
                          fun s =>
                            by 
                              cases' s with a b <;>
                                try 
                                    cases a <;>
                                  rfl] at
                      ht⟩⟩⟩⟩

theorem ex1_dioph {S : Set (Option α → ℕ)} : Dioph S → Dioph fun v => ∃ x, S (x :: v)
| ⟨β, p, pe⟩ =>
  ⟨Option β, p.remap (inr none :: inl ⊗ (inr ∘ some)),
    fun v =>
      ⟨fun ⟨x, hx⟩ =>
          let ⟨t, ht⟩ := (pe _).1 hx
          ⟨x :: t,
            by 
              simp  <;>
                rw
                    [show (v ⊗ x :: t ∘ inr none :: inl ⊗ (inr ∘ some)) = x :: v ⊗ t from
                      funext$
                        fun s =>
                          by 
                            cases' s with a b <;>
                              try 
                                  cases a <;>
                                rfl] <;>
                  exact ht⟩,
        fun ⟨t, ht⟩ =>
          ⟨t none,
            (pe _).2
              ⟨t ∘ some,
                by 
                  simp  at ht <;>
                    rwa
                      [show (v ⊗ t ∘ inr none :: inl ⊗ (inr ∘ some)) = t none :: v ⊗ (t ∘ some) from
                        funext$
                          fun s =>
                            by 
                              cases' s with a b <;>
                                try 
                                    cases a <;>
                                  rfl] at
                      ht⟩⟩⟩⟩

theorem dom_dioph {f : (α → ℕ) →. ℕ} (d : dioph_pfun f) : Dioph f.dom :=
  cast (congr_argₓ Dioph$ Set.ext$ fun v => (Pfun.dom_iff_graph _ _).symm) (ex1_dioph d)

theorem dioph_fn_iff_pfun (f : (α → ℕ) → ℕ) : dioph_fn f = @dioph_pfun α f :=
  by 
    refine' congr_argₓ Dioph (Set.ext$ fun v => _) <;> exact pfun.lift_graph.symm

theorem abs_poly_dioph (p : Poly α) : dioph_fn fun v => (p v).natAbs :=
  by 
    refine' of_no_dummies _ ((p.remap some - Poly.proj none)*p.remap some+Poly.proj none) fun v => _ <;>
      apply Int.eq_nat_abs_iff_mul

theorem proj_dioph (i : α) : dioph_fn fun v => v i :=
  abs_poly_dioph (Poly.proj i)

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem dioph_pfun_comp1
{S : set (option α → exprℕ())}
(d : dioph S)
{f}
(df : dioph_pfun f) : dioph (λ
 v : α → exprℕ(), «expr∃ , »((h : f.dom v), S [«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](f.fn v h, v))) :=
«expr $ »(ext (ex1_dioph (and_dioph d df)), λ
 v, ⟨λ
  ⟨x, hS, (h : Exists _)⟩, by rw ["[", expr show «expr = »(«expr ∘ »([«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](x, v), some), v), from «expr $ »(funext, λ
    s, rfl), "]"] ["at", ident h]; cases [expr h] ["with", ident hf, ident h]; refine [expr ⟨hf, _⟩]; rw ["[", expr pfun.fn, ",", expr h, "]"] []; exact [expr hS], λ
  ⟨x, hS⟩, ⟨f.fn v x, hS, show Exists _, by rw ["[", expr show «expr = »(«expr ∘ »([«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](f.fn v x, v), some), v), from «expr $ »(funext, λ
     s, rfl), "]"] []; exact [expr ⟨x, rfl⟩]⟩⟩)

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem dioph_fn_comp1
{S : set (option α → exprℕ())}
(d : dioph S)
{f : (α → exprℕ()) → exprℕ()}
(df : dioph_fn f) : dioph (λ v : α → exprℕ(), S [«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](f v, v)) :=
«expr $ »(ext (dioph_pfun_comp1 d (cast (dioph_fn_iff_pfun f) df)), λ v, ⟨λ ⟨_, h⟩, h, λ h, ⟨trivial, h⟩⟩)

end 

section 

variable{α β γ : Type}

open Vector3

open_locale Vector3

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem dioph_fn_vec_comp1
{n}
{S : set (vector3 exprℕ() (succ n))}
(d : dioph S)
{f : vector3 exprℕ() n → exprℕ()}
(df : dioph_fn f) : dioph (λ v : vector3 exprℕ() n, S (cons (f v) v)) :=
«expr $ »(ext (dioph_fn_comp1 (reindex_dioph d [«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](none, some)) df), λ
 v, by rw ["[", expr show «expr = »(«expr ∘ »(option.cons (f v) v, cons none some), [«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](f v, v)), from «expr $ »(funext, λ
   s, by cases [expr s] ["with", ident a, ident b]; refl), "]"] [])

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem vec_ex1_dioph
(n)
{S : set (vector3 exprℕ() (succ n))}
(d : dioph S) : dioph (λ
 v : vector3 exprℕ() n, «expr∃ , »((x), S [«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](x, v))) :=
«expr $ »(ext «expr $ »(ex1_dioph, reindex_dioph d [«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](none, some)), λ
 v, «expr $ »(exists_congr, λ
  x, by rw ["[", expr show «expr = »(«expr ∘ »(option.cons x v, cons none some), [«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](x, v)), from «expr $ »(funext, λ
    s, by cases [expr s] ["with", ident a, ident b]; refl), "]"] []))

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem dioph_fn_vec
{n}
(f : vector3 exprℕ() n → exprℕ()) : «expr ↔ »(dioph_fn f, dioph (λ
  v : vector3 exprℕ() (succ n), «expr = »(f «expr ∘ »(v, fs), v fz))) :=
⟨λ
 h, reindex_dioph h [«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](fz, fs), λ
 h, reindex_dioph h [«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](none, some)⟩

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem dioph_pfun_vec
{n}
(f : «expr →. »(vector3 exprℕ() n, exprℕ())) : «expr ↔ »(dioph_pfun f, dioph (λ
  v : vector3 exprℕ() (succ n), f.graph («expr ∘ »(v, fs), v fz))) :=
⟨λ
 h, reindex_dioph h [«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](fz, fs), λ
 h, reindex_dioph h [«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](none, some)⟩

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem dioph_fn_compn
{α : Type} : ∀
{n}
{S : set («expr ⊕ »(α, fin2 n) → exprℕ())}
(d : dioph S)
{f : vector3 ((α → exprℕ()) → exprℕ()) n}
(df : vector_allp dioph_fn f), dioph (λ v : α → exprℕ(), S «expr ⊗ »(v, λ i, f i v))
| 0, S, d, f := λ
df, «expr $ »(ext (reindex_dioph d «expr ⊗ »(id, fin2.elim0)), λ
 v, by refine [expr eq.to_iff «expr $ »(congr_arg S, «expr $ »(funext, λ
    s, _))]; { cases [expr s] ["with", ident a, ident b],
   refl,
   cases [expr b] [] })
| succ n, S, d, f := «expr $ »(f.cons_elim, λ
 f
 fl, by simp [] [] [] [] [] []; exact [expr λ
  df
  dfl, have dioph (λ
   v, S «expr ⊗ »(«expr ∘ »(v, inl), [«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](f «expr ∘ »(v, inl), «expr ∘ »(v, inr)))), from «expr $ »(ext (dioph_fn_comp1 (reindex_dioph d «expr ⊗ »(«expr ∘ »(some, inl), [«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](none, «expr ∘ »(some, inr)))) (reindex_dioph_fn df inl)), λ
   v, by { refine [expr eq.to_iff «expr $ »(congr_arg S, «expr $ »(funext, λ
        s, _))]; cases [expr s] ["with", ident a, ident b],
     refl,
     cases [expr b] []; refl }),
  have dioph (λ
   v, S «expr ⊗ »(v, [«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](f v, λ
     i : fin2 n, fl i v))), from @dioph_fn_compn n (λ
   v, S «expr ⊗ »(«expr ∘ »(v, inl), [«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](f «expr ∘ »(v, inl), «expr ∘ »(v, inr)))) this _ dfl,
  «expr $ »(ext this, λ
   v, by rw ["[", expr show «expr = »(cons (f v) (λ
      i : fin2 n, fl i v), λ
     i : fin2 (succ n), [«expr :: »/«expr :: »/«expr :: »/«expr :: »/«expr :: »](f, fl) i v), from «expr $ »(funext, λ
     s, by cases [expr s] ["with", ident a, ident b]; refl), "]"] [])])

theorem dioph_comp {n} {S : Set (Vector3 ℕ n)} (d : Dioph S) (f : Vector3 ((α → ℕ) → ℕ) n)
  (df : VectorAllp dioph_fn f) : Dioph fun v => S fun i => f i v :=
  dioph_fn_compn (reindex_dioph d inr) df

theorem dioph_fn_comp {n} {f : Vector3 ℕ n → ℕ} (df : dioph_fn f) (g : Vector3 ((α → ℕ) → ℕ) n)
  (dg : VectorAllp dioph_fn g) : dioph_fn fun v => f fun i => g i v :=
  dioph_comp ((dioph_fn_vec _).1 df) ((fun v => v none) :: fun i v => g i (v ∘ some))$
    by 
      simp  <;>
        exact
          ⟨proj_dioph none,
            (vector_allp_iff_forall _ _).2$ fun i => reindex_dioph_fn ((vector_allp_iff_forall _ _).1 dg _) _⟩

localized [Dioph] notation:35 x " D∧ " y => Dioph.and_dioph x y

localized [Dioph] notation:35 x " D∨ " y => Dioph.or_dioph x y

localized [Dioph] notation:30 "D∃" => Dioph.vec_ex1_dioph

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:1266:43: in localized: ././Mathport/Syntax/Translate/Basic.lean:265:9: unsupported: advanced prec syntax
localized [expr "prefix `&`:max := of_nat'", [command <some 4>], "in", ident dioph]

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem proj_dioph_of_nat {n : exprℕ()} (m : exprℕ()) [is_lt m n] : dioph_fn (λ v : vector3 exprℕ() n, v «expr& »(m)) :=
proj_dioph «expr& »(m)

localized [Dioph] prefix:100 "D&" => Dioph.proj_dioph_of_nat

theorem const_dioph (n : ℕ) : dioph_fn (const (α → ℕ) n) :=
  abs_poly_dioph (Poly.const n)

localized [Dioph] prefix:100 "D." => Dioph.const_dioph

variable{f g : (α → ℕ) → ℕ}(df : dioph_fn f)(dg : dioph_fn g)

include df dg

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem dioph_comp2
{S : exprℕ() → exprℕ() → exprProp()}
(d : dioph (λ v : vector3 exprℕ() 2, S (v «expr& »(0)) (v «expr& »(1)))) : dioph (λ v, S (f v) (g v)) :=
dioph_comp d «expr[ , ]»([f, g]) (by exact [expr ⟨df, dg⟩])

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem dioph_fn_comp2
{h : exprℕ() → exprℕ() → exprℕ()}
(d : dioph_fn (λ v : vector3 exprℕ() 2, h (v «expr& »(0)) (v «expr& »(1)))) : dioph_fn (λ v, h (f v) (g v)) :=
dioph_fn_comp d «expr[ , ]»([f, g]) (by exact [expr ⟨df, dg⟩])

theorem eq_dioph : Dioph fun v => f v = g v :=
  dioph_comp2 df dg$
    of_no_dummies _ (Poly.proj («expr& » 0) - Poly.proj («expr& » 1))
      fun v =>
        (Int.coe_nat_eq_coe_nat_iff _ _).symm.trans
          ⟨@sub_eq_zero_of_eq ℤ _ (v («expr& » 0)) (v («expr& » 1)), eq_of_sub_eq_zero⟩

localized [Dioph] infixl:50 " D= " => Dioph.eq_dioph

theorem add_dioph : dioph_fn fun v => f v+g v :=
  dioph_fn_comp2 df dg$ abs_poly_dioph (Poly.proj («expr& » 0)+Poly.proj («expr& » 1))

localized [Dioph] infixl:80 " D+ " => Dioph.add_dioph

theorem mul_dioph : dioph_fn fun v => f v*g v :=
  dioph_fn_comp2 df dg$ abs_poly_dioph (Poly.proj («expr& » 0)*Poly.proj («expr& » 1))

localized [Dioph] infixl:90 " D* " => Dioph.mul_dioph

theorem le_dioph : Dioph fun v => f v ≤ g v :=
  dioph_comp2 df dg$ ext ((D∃) 2$ D&1 D+ D&0 D= D&2) fun v => ⟨fun ⟨x, hx⟩ => le.intro hx, le.dest⟩

localized [Dioph] infixl:50 " D≤ " => Dioph.le_dioph

theorem lt_dioph : Dioph fun v => f v < g v :=
  df D+ D.1 D≤ dg

localized [Dioph] infixl:50 " D< " => Dioph.lt_dioph

theorem ne_dioph : Dioph fun v => f v ≠ g v :=
  ext (df D< dg D∨ dg D< df)$ fun v => ne_iff_lt_or_gtₓ.symm

localized [Dioph] infixl:50 " D≠ " => Dioph.ne_dioph

theorem sub_dioph : dioph_fn fun v => f v - g v :=
  dioph_fn_comp2 df dg$
    (dioph_fn_vec _).2$
      ext (D&1 D= D&0 D+ D&2 D∨ D&1 D≤ D&2 D∧ D&0 D= D.0)$
        (vector_all_iff_forall _).1$
          fun x y z =>
            show (y = x+z) ∨ y ≤ z ∧ x = 0 ↔ y - z = x from
              ⟨fun o =>
                  by 
                    rcases o with (ae | ⟨yz, x0⟩)
                    ·
                      rw [ae, add_tsub_cancel_right]
                    ·
                      rw [x0, tsub_eq_zero_iff_le.mpr yz],
                fun h =>
                  by 
                    subst x 
                    cases' le_totalₓ y z with yz zy
                    ·
                      exact Or.inr ⟨yz, tsub_eq_zero_iff_le.mpr yz⟩
                    ·
                      exact Or.inl (tsub_add_cancel_of_le zy).symm⟩

localized [Dioph] infixl:80 " D- " => Dioph.sub_dioph

theorem dvd_dioph : Dioph fun v => f v ∣ g v :=
  dioph_comp ((D∃) 2$ D&2 D= D&1 D* D&0) [f, g]
    (by 
      exact ⟨df, dg⟩)

localized [Dioph] infixl:50 " D∣ " => Dioph.dvd_dioph

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem mod_dioph : dioph_fn (λ v, «expr % »(f v, g v)) :=
have dioph (λ
 v : vector3 exprℕ() 3, «expr ∧ »(«expr ∨ »(«expr = »(v «expr& »(2), 0), «expr < »(v «expr& »(0), v «expr& »(2))), «expr∃ , »((x : exprℕ()), «expr = »(«expr + »(v «expr& »(0), «expr * »(v «expr& »(2), x)), v «expr& »(1))))), from «expr D∧ »(«expr D∨ »(«expr D= »(«exprD& »(2), «exprD. »(0)), «expr D< »(«exprD& »(0), «exprD& »(2))), «expr $ »(«exprD∃»() 3, «expr D= »(«expr D+ »(«exprD& »(1), «expr D* »(«exprD& »(3), «exprD& »(0))), «exprD& »(2)))),
«expr $ »(dioph_fn_comp2 df dg, «expr $ »((dioph_fn_vec _).2, «expr $ »(ext this, «expr $ »((vector_all_iff_forall _).1, λ
    z
    x
    y, show «expr ↔ »(«expr ∧ »(«expr ∨ »(«expr = »(y, 0), «expr < »(z, y)), «expr∃ , »((c), «expr = »(«expr + »(z, «expr * »(y, c)), x))), «expr = »(«expr % »(x, y), z)), from ⟨λ
     ⟨h, c, hc⟩, begin
       rw ["<-", expr hc] []; simp [] [] [] [] [] []; cases [expr h] ["with", ident x0, ident hl],
       rw ["[", expr x0, ",", expr mod_zero, "]"] [],
       exact [expr mod_eq_of_lt hl]
     end, λ
     e, by rw ["<-", expr e] []; exact [expr ⟨«expr $ »(or_iff_not_imp_left.2, λ
        h, mod_lt _ (nat.pos_of_ne_zero h)), «expr / »(x, y), mod_add_div _ _⟩]⟩))))

localized [Dioph] infixl:80 " D% " => Dioph.mod_dioph

theorem modeq_dioph {h : (α → ℕ) → ℕ} (dh : dioph_fn h) : Dioph fun v => f v ≡ g v [MOD h v] :=
  df D% dh D= dg D% dh

localized [Dioph] notation "D≡" => Dioph.modeq_dioph

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem div_dioph : dioph_fn (λ v, «expr / »(f v, g v)) :=
have dioph (λ
 v : vector3 exprℕ() 3, «expr ∨ »(«expr ∧ »(«expr = »(v «expr& »(2), 0), «expr = »(v «expr& »(0), 0)), «expr ∧ »(«expr ≤ »(«expr * »(v «expr& »(0), v «expr& »(2)), v «expr& »(1)), «expr < »(v «expr& »(1), «expr * »(«expr + »(v «expr& »(0), 1), v «expr& »(2)))))), from «expr D∨ »(«expr D∧ »(«expr D= »(«exprD& »(2), «exprD. »(0)), «expr D= »(«exprD& »(0), «exprD. »(0))), «expr D∧ »(«expr D≤ »(«expr D* »(«exprD& »(0), «exprD& »(2)), «exprD& »(1)), «expr D< »(«exprD& »(1), «expr D* »(«expr D+ »(«exprD& »(0), «exprD. »(1)), «exprD& »(2))))),
«expr $ »(dioph_fn_comp2 df dg, «expr $ »((dioph_fn_vec _).2, «expr $ »(ext this, «expr $ »((vector_all_iff_forall _).1, λ
    z
    x
    y, show «expr ↔ »(«expr ∨ »(«expr ∧ »(«expr = »(y, 0), «expr = »(z, 0)), «expr ∧ »(«expr ≤ »(«expr * »(z, y), x), «expr < »(x, «expr * »(«expr + »(z, 1), y)))), «expr = »(«expr / »(x, y), z)), by refine [expr iff.trans _ eq_comm]; exact [expr y.eq_zero_or_pos.elim (λ
      y0, by rw ["[", expr y0, ",", expr nat.div_zero, "]"] []; exact [expr ⟨λ
        o, «expr $ »(o.resolve_right, λ
         ⟨_, h2⟩, nat.not_lt_zero _ h2).right, λ
        z0, or.inl ⟨rfl, z0⟩⟩]) (λ
      ypos, iff.trans ⟨λ
       o, «expr $ »(o.resolve_left, λ
        ⟨h1, _⟩, ne_of_gt ypos h1), or.inr⟩ «expr $ »(le_antisymm_iff.trans, «expr $ »(and_congr (nat.le_div_iff_mul_le _ _ ypos), iff.trans ⟨lt_succ_of_le, le_of_lt_succ⟩ (div_lt_iff_lt_mul _ _ ypos))).symm)]))))

localized [Dioph] infixl:80 " D/ " => Dioph.div_dioph

omit df dg

open Pell

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem pell_dioph : dioph (λ
 v : vector3 exprℕ() 4, «expr∃ , »((h : «expr < »(1, v «expr& »(0))), «expr ∧ »(«expr = »(xn h (v «expr& »(1)), v «expr& »(2)), «expr = »(yn h (v «expr& »(1)), v «expr& »(3))))) :=
have dioph {v : vector3 exprℕ() 4 | «expr ∧ »(«expr < »(1, v «expr& »(0)), «expr ∧ »(«expr ≤ »(v «expr& »(1), v «expr& »(3)), «expr ∨ »(«expr ∧ »(«expr = »(v «expr& »(2), 1), «expr = »(v «expr& »(3), 0)), «expr∃ , »((u
     w
     s
     t
     b : exprℕ()), «expr ∧ »(«expr = »(«expr - »(«expr * »(v «expr& »(2), v «expr& »(2)), «expr * »(«expr * »(«expr - »(«expr * »(v «expr& »(0), v «expr& »(0)), 1), v «expr& »(3)), v «expr& »(3))), 1), «expr ∧ »(«expr = »(«expr - »(«expr * »(u, u), «expr * »(«expr * »(«expr - »(«expr * »(v «expr& »(0), v «expr& »(0)), 1), w), w)), 1), «expr ∧ »(«expr = »(«expr - »(«expr * »(s, s), «expr * »(«expr * »(«expr - »(«expr * »(b, b), 1), t), t)), 1), «expr ∧ »(«expr < »(1, b), «expr ∧ »(«expr ≡ [MOD ]»(b, 1, «expr * »(4, v «expr& »(3))), «expr ∧ »(«expr ≡ [MOD ]»(b, v «expr& »(0), u), «expr ∧ »(«expr < »(0, w), «expr ∧ »(«expr ∣ »(«expr * »(v «expr& »(3), v «expr& »(3)), w), «expr ∧ »(«expr ≡ [MOD ]»(s, v «expr& »(2), u), «expr ≡ [MOD ]»(t, v «expr& »(1), «expr * »(4, v «expr& »(3))))))))))))))))}, from «expr D∧ »(«expr D< »(«exprD. »(1), «exprD& »(0)), «expr D∧ »(«expr D≤ »(«exprD& »(1), «exprD& »(3)), «expr D∨ »(«expr D∧ »(«expr D= »(«exprD& »(2), «exprD. »(1)), «expr D= »(«exprD& »(3), «exprD. »(0))), «expr $ »(«exprD∃»() 4, «expr $ »(«exprD∃»() 5, «expr $ »(«exprD∃»() 6, «expr $ »(«exprD∃»() 7, «expr $ »(«exprD∃»() 8, «expr D∧ »(«expr D= »(«expr D- »(«expr D* »(«exprD& »(7), «exprD& »(7)), «expr D* »(«expr D* »(«expr D- »(«expr D* »(«exprD& »(5), «exprD& »(5)), «exprD. »(1)), «exprD& »(8)), «exprD& »(8))), «exprD. »(1)), «expr D∧ »(«expr D= »(«expr D- »(«expr D* »(«exprD& »(4), «exprD& »(4)), «expr D* »(«expr D* »(«expr D- »(«expr D* »(«exprD& »(5), «exprD& »(5)), «exprD. »(1)), «exprD& »(3)), «exprD& »(3))), «exprD. »(1)), «expr D∧ »(«expr D= »(«expr D- »(«expr D* »(«exprD& »(2), «exprD& »(2)), «expr D* »(«expr D* »(«expr D- »(«expr D* »(«exprD& »(0), «exprD& »(0)), «exprD. »(1)), «exprD& »(1)), «exprD& »(1))), «exprD. »(1)), «expr D∧ »(«expr D< »(«exprD. »(1), «exprD& »(0)), «expr D∧ »(«exprD≡»() «exprD& »(0) «exprD. »(1) «expr D* »(«exprD. »(4), «exprD& »(8)), «expr D∧ »(«exprD≡»() «exprD& »(0) «exprD& »(5) «exprD& »(4), «expr D∧ »(«expr D< »(«exprD. »(0), «exprD& »(3)), «expr D∧ »(«expr D∣ »(«expr D* »(«exprD& »(8), «exprD& »(8)), «exprD& »(3)), «expr D∧ »(«exprD≡»() «exprD& »(2) «exprD& »(7) «exprD& »(4), «exprD≡»() «exprD& »(1) «exprD& »(6) «expr D* »(«exprD. »(4), «exprD& »(8))))))))))))))))))),
«expr $ »(dioph.ext this, λ v, matiyasevic.symm)

-- error in NumberTheory.Dioph: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem xn_dioph : dioph_pfun (λ v : vector3 exprℕ() 2, ⟨«expr < »(1, v «expr& »(0)), λ h, xn h (v «expr& »(1))⟩) :=
have dioph (λ
 v : vector3 exprℕ() 3, «expr∃ , »((y), «expr∃ , »((h : «expr < »(1, v «expr& »(1))), «expr ∧ »(«expr = »(xn h (v «expr& »(2)), v «expr& »(0)), «expr = »(yn h (v «expr& »(2)), y))))), from let D_pell := @reindex_dioph _ (fin2 4) _ pell_dioph «expr[ , ]»([«expr& »(2), «expr& »(3), «expr& »(1), «expr& »(0)]) in
«exprD∃»() 3 D_pell,
«expr $ »((dioph_pfun_vec _).2, «expr $ »(dioph.ext this, λ v, ⟨λ ⟨y, h, xe, ye⟩, ⟨h, xe⟩, λ ⟨h, xe⟩, ⟨_, h, xe, rfl⟩⟩))

include df dg

/-- A version of **Matiyasevic's theorem** -/
theorem pow_dioph : dioph_fn fun v => f v ^ g v :=
  have  :
    Dioph
      { v:Vector3 ℕ 3 |
        v («expr& » 2) = 0 ∧ v («expr& » 0) = 1 ∨
          0 < v («expr& » 2) ∧
            (v («expr& » 1) = 0 ∧ v («expr& » 0) = 0 ∨
              0 < v («expr& » 1) ∧
                ∃ w a t z x y : ℕ,
                  (∃ a1 : 1 < a, xn a1 (v («expr& » 2)) = x ∧ yn a1 (v («expr& » 2)) = y) ∧
                    x ≡ (y*a - v («expr& » 1))+v («expr& » 0) [MOD t] ∧
                      (((2*a)*v («expr& » 1)) = t+(v («expr& » 1)*v («expr& » 1))+1) ∧
                        v («expr& » 0) < t ∧
                          v («expr& » 1) ≤ w ∧ v («expr& » 2) ≤ w ∧ ((a*a) - ((((w+1)*w+1) - 1)*w*z)*w*z) = 1) } :=
    let D_pell := @reindex_dioph _ (Fin2 9) _ pell_dioph [«expr& » 4, «expr& » 8, «expr& » 1, «expr& » 0]
    (D&2 D= D.0 D∧ D&0 D= D.1) D∨
      D.0 D< D&2 D∧
        (D&1 D= D.0 D∧ D&0 D= D.0) D∨
          D.0 D< D&1 D∧
            (D∃) 3$
              (D∃) 4$
                (D∃) 5$
                  (D∃) 6$
                    (D∃) 7$
                      (D∃) 8$
                        D_pell D∧
                          D≡ (D&1) (D&0 D* (D&4 D- D&7) D+ D&6) (D&3) D∧
                            D.2 D* D&4 D* D&7 D= D&3 D+ (D&7 D* D&7 D+ D.1) D∧
                              D&6 D< D&3 D∧
                                D&7 D≤ D&5 D∧
                                  D&8 D≤ D&5 D∧
                                    D&4 D* D&4 D-
                                        ((D&5 D+ D.1) D* (D&5 D+ D.1) D- D.1) D* (D&5 D* D&2) D* (D&5 D* D&2) D=
                                      D.1
  dioph_fn_comp2 df dg$
    (dioph_fn_vec _).2$
      Dioph.ext this$
        fun v =>
          Iff.symm$
            eq_pow_of_pell.trans$
              or_congr Iff.rfl$
                and_congr Iff.rfl$
                  or_congr Iff.rfl$
                    and_congr Iff.rfl$
                      ⟨fun ⟨w, a, t, z, a1, h⟩ => ⟨w, a, t, z, _, _, ⟨a1, rfl, rfl⟩, h⟩,
                        fun ⟨w, a, t, z, _, _, ⟨a1, rfl, rfl⟩, h⟩ => ⟨w, a, t, z, a1, h⟩⟩

end 

end Dioph

