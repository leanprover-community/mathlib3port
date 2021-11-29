import Mathbin.Data.Pfunctor.Multivariate.Basic 
import Mathbin.Data.Pfunctor.Univariate.M

/-!
# The M construction as a multivariate polynomial functor.

M types are potentially infinite tree-like structures. They are defined
as the greatest fixpoint of a polynomial functor.

## Main definitions

 * `M.mk`     - constructor
 * `M.dest`   - destructor
 * `M.corec`  - corecursor: useful for formulating infinite, productive computations
 * `M.bisim`  - bisimulation: proof technique to show the equality of infinite objects

## Implementation notes

Dual view of M-types:

 * `Mp`: polynomial functor
 * `M`: greatest fixed point of a polynomial functor

Specifically, we define the polynomial functor `Mp` as:

 * A := a possibly infinite tree-like structure without information in the nodes
 * B := given the tree-like structure `t`, `B t` is a valid path
   from the root of `t` to any given node.

As a result `Mp.obj α` is made of a dataless tree and a function from
its valid paths to values of `α`

The difference with the polynomial functor of an initial algebra is
that `A` is a possibly infinite tree.

## Reference

 * [Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/


universe u

open_locale Mvfunctor

namespace Mvpfunctor

open Typevec

variable{n : ℕ}(P : Mvpfunctor.{u} (n+1))

/-- A path from the root of a tree to one of its node -/
inductive M.path : P.last.M → Fin2 n → Type u
  | root (x : P.last.M) (a : P.A) (f : P.last.B a → P.last.M) (h : Pfunctor.M.dest x = ⟨a, f⟩) (i : Fin2 n)
  (c : P.drop.B a i) : M.path x i
  | child (x : P.last.M) (a : P.A) (f : P.last.B a → P.last.M) (h : Pfunctor.M.dest x = ⟨a, f⟩) (j : P.last.B a)
  (i : Fin2 n) (c : M.path (f j) i) : M.path x i

instance M.path.inhabited (x : P.last.M) {i} [Inhabited (P.drop.B x.head i)] : Inhabited (M.path P x i) :=
  ⟨M.path.root _ (Pfunctor.M.head x) (Pfunctor.M.children x)
      (Pfunctor.M.casesOn' x$
        by 
          intros  <;> simp [Pfunctor.M.dest_mk] <;> ext <;> rw [Pfunctor.M.children_mk] <;> rfl)
      _ (default _)⟩

/-- Polynomial functor of the M-type of `P`. `A` is a data-less
possibly infinite tree whereas, for a given `a : A`, `B a` is a valid
path in tree `a` so that `Wp.obj α` is made of a tree and a function
from its valid paths to the values it contains -/
def Mp : Mvpfunctor n :=
  { A := P.last.M, B := M.path P }

/-- `n`-ary M-type for `P` -/
def M (α : Typevec n) : Type _ :=
  P.Mp.obj α

instance mvfunctor_M : Mvfunctor P.M :=
  by 
    delta' M <;> infer_instance

instance inhabited_M {α : Typevec _} [I : Inhabited P.A] [∀ (i : Fin2 n), Inhabited (α i)] : Inhabited (P.M α) :=
  @obj.inhabited _ (Mp P) _ (@Pfunctor.M.inhabited P.last I) _

/-- construct through corecursion the shape of an M-type
without its contents -/
def M.corec_shape {β : Type u} (g₀ : β → P.A) (g₂ : ∀ (b : β), P.last.B (g₀ b) → β) : β → P.last.M :=
  Pfunctor.M.corec fun b => ⟨g₀ b, g₂ b⟩

/-- Proof of type equality as an arrow -/
def cast_dropB {a a' : P.A} (h : a = a') : P.drop.B a ⟹ P.drop.B a' :=
  fun i b => Eq.recOnₓ h b

/-- Proof of type equality as a function -/
def cast_lastB {a a' : P.A} (h : a = a') : P.last.B a → P.last.B a' :=
  fun b => Eq.recOnₓ h b

/-- Using corecursion, construct the contents of an M-type -/
def M.corec_contents {α : Typevec.{u} n} {β : Type u} (g₀ : β → P.A) (g₁ : ∀ (b : β), P.drop.B (g₀ b) ⟹ α)
  (g₂ : ∀ (b : β), P.last.B (g₀ b) → β) : ∀ x b, x = M.corec_shape P g₀ g₂ b → M.path P x ⟹ α
| _, b, h, _, M.path.root x a f h' i c =>
  have  : a = g₀ b :=
    by 
      rw [h, M.corec_shape, Pfunctor.M.dest_corec] at h' 
      cases h' 
      rfl 
  g₁ b i (P.cast_dropB this i c)
| _, b, h, _, M.path.child x a f h' j i c =>
  have h₀ : a = g₀ b :=
    by 
      rw [h, M.corec_shape, Pfunctor.M.dest_corec] at h' 
      cases h' 
      rfl 
  have h₁ : f j = M.corec_shape P g₀ g₂ (g₂ b (cast_lastB P h₀ j)) :=
    by 
      rw [h, M.corec_shape, Pfunctor.M.dest_corec] at h' 
      cases h' 
      rfl 
  M.corec_contents (f j) (g₂ b (P.cast_lastB h₀ j)) h₁ i c

/-- Corecursor for M-type of `P` -/
def M.corec' {α : Typevec n} {β : Type u} (g₀ : β → P.A) (g₁ : ∀ (b : β), P.drop.B (g₀ b) ⟹ α)
  (g₂ : ∀ (b : β), P.last.B (g₀ b) → β) : β → P.M α :=
  fun b => ⟨M.corec_shape P g₀ g₂ b, M.corec_contents P g₀ g₁ g₂ _ _ rfl⟩

/-- Corecursor for M-type of `P` -/
def M.corec {α : Typevec n} {β : Type u} (g : β → P.obj (α.append1 β)) : β → P.M α :=
  M.corec' P (fun b => (g b).fst) (fun b => drop_fun (g b).snd) fun b => last_fun (g b).snd

/-- Implementation of destructor for M-type of `P` -/
def M.path_dest_left {α : Typevec n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M}
  (h : Pfunctor.M.dest x = ⟨a, f⟩) (f' : M.path P x ⟹ α) : P.drop.B a ⟹ α :=
  fun i c => f' i (M.path.root x a f h i c)

/-- Implementation of destructor for M-type of `P` -/
def M.path_dest_right {α : Typevec n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M}
  (h : Pfunctor.M.dest x = ⟨a, f⟩) (f' : M.path P x ⟹ α) : ∀ (j : P.last.B a), M.path P (f j) ⟹ α :=
  fun j i c => f' i (M.path.child x a f h j i c)

/-- Destructor for M-type of `P` -/
def M.dest' {α : Typevec n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M} (h : Pfunctor.M.dest x = ⟨a, f⟩)
  (f' : M.path P x ⟹ α) : P.obj (α.append1 (P.M α)) :=
  ⟨a, split_fun (M.path_dest_left P h f') fun x => ⟨f x, M.path_dest_right P h f' x⟩⟩

/-- Destructor for M-types -/
def M.dest {α : Typevec n} (x : P.M α) : P.obj (α ::: P.M α) :=
  M.dest' P (Sigma.eta$ Pfunctor.M.dest x.fst).symm x.snd

/-- Constructor for M-types -/
def M.mk {α : Typevec n} : P.obj (α.append1 (P.M α)) → P.M α :=
  M.corec _ fun i => append_fun id (M.dest P) <$$> i

theorem M.dest'_eq_dest' {α : Typevec n} {x : P.last.M} {a₁ : P.A} {f₁ : P.last.B a₁ → P.last.M}
  (h₁ : Pfunctor.M.dest x = ⟨a₁, f₁⟩) {a₂ : P.A} {f₂ : P.last.B a₂ → P.last.M} (h₂ : Pfunctor.M.dest x = ⟨a₂, f₂⟩)
  (f' : M.path P x ⟹ α) : M.dest' P h₁ f' = M.dest' P h₂ f' :=
  by 
    cases h₁.symm.trans h₂ <;> rfl

theorem M.dest_eq_dest' {α : Typevec n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M}
  (h : Pfunctor.M.dest x = ⟨a, f⟩) (f' : M.path P x ⟹ α) : M.dest P ⟨x, f'⟩ = M.dest' P h f' :=
  M.dest'_eq_dest' _ _ _ _

theorem M.dest_corec' {α : Typevec.{u} n} {β : Type u} (g₀ : β → P.A) (g₁ : ∀ (b : β), P.drop.B (g₀ b) ⟹ α)
  (g₂ : ∀ (b : β), P.last.B (g₀ b) → β) (x : β) :
  M.dest P (M.corec' P g₀ g₁ g₂ x) = ⟨g₀ x, split_fun (g₁ x) (M.corec' P g₀ g₁ g₂ ∘ g₂ x)⟩ :=
  rfl

theorem M.dest_corec {α : Typevec n} {β : Type u} (g : β → P.obj (α.append1 β)) (x : β) :
  M.dest P (M.corec P g x) = append_fun id (M.corec P g) <$$> g x :=
  by 
    trans 
    apply M.dest_corec' 
    cases' g x with a f 
    dsimp 
    rw [Mvpfunctor.map_eq]
    congr 
    conv  => toRHS rw [←split_drop_fun_last_fun f, append_fun_comp_split_fun]
    rfl

-- error in Data.Pfunctor.Multivariate.M: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem M.bisim_lemma
{α : typevec n}
{a₁ : (Mp P).A}
{f₁ : «expr ⟹ »((Mp P).B a₁, α)}
{a' : P.A}
{f' : «expr ⟹ »((P.B a').drop, α)}
{f₁' : (P.B a').last → M P α}
(e₁ : «expr = »(M.dest P ⟨a₁, f₁⟩, ⟨a', split_fun f' f₁'⟩)) : «expr∃ , »((g₁')
 (e₁' : «expr = »(pfunctor.M.dest a₁, ⟨a', g₁'⟩)), «expr ∧ »(«expr = »(f', M.path_dest_left P e₁' f₁), «expr = »(f₁', λ
   x : (last P).B a', ⟨g₁' x, M.path_dest_right P e₁' f₁ x⟩))) :=
begin
  generalize_hyp [ident ef] [":"] [expr «expr = »(@split_fun n _ (append1 α (M P α)) f' f₁', ff)] ["at", ident e₁],
  cases [expr e₁', ":", expr pfunctor.M.dest a₁] ["with", ident a₁', ident g₁'],
  rw [expr M.dest_eq_dest' _ e₁'] ["at", ident e₁],
  cases [expr e₁] [],
  exact [expr ⟨_, e₁', split_fun_inj ef⟩]
end

-- error in Data.Pfunctor.Multivariate.M: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem M.bisim
{α : typevec n}
(R : P.M α → P.M α → exprProp())
(h : ∀
 x
 y, R x y → «expr∃ , »((a
   f
   f₁
   f₂), «expr ∧ »(«expr = »(M.dest P x, ⟨a, split_fun f f₁⟩), «expr ∧ »(«expr = »(M.dest P y, ⟨a, split_fun f f₂⟩), ∀
    i, R (f₁ i) (f₂ i)))))
(x y)
(r : R x y) : «expr = »(x, y) :=
begin
  cases [expr x] ["with", ident a₁, ident f₁],
  cases [expr y] ["with", ident a₂, ident f₂],
  dsimp [] ["[", expr Mp, "]"] [] ["at", "*"],
  have [] [":", expr «expr = »(a₁, a₂)] [],
  { refine [expr pfunctor.M.bisim (λ
      a₁
      a₂, «expr∃ , »((x
        y), «expr ∧ »(R x y, «expr ∧ »(«expr = »(x.1, a₁), «expr = »(y.1, a₂))))) _ _ _ ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩],
    rintro ["_", "_", "⟨", "⟨", ident a₁, ",", ident f₁, "⟩", ",", "⟨", ident a₂, ",", ident f₂, "⟩", ",", ident r, ",", ident rfl, ",", ident rfl, "⟩"],
    rcases [expr h _ _ r, "with", "⟨", ident a', ",", ident f', ",", ident f₁', ",", ident f₂', ",", ident e₁, ",", ident e₂, ",", ident h', "⟩"],
    rcases [expr M.bisim_lemma P e₁, "with", "⟨", ident g₁', ",", ident e₁', ",", ident rfl, ",", ident rfl, "⟩"],
    rcases [expr M.bisim_lemma P e₂, "with", "⟨", ident g₂', ",", ident e₂', ",", "_", ",", ident rfl, "⟩"],
    rw ["[", expr e₁', ",", expr e₂', "]"] [],
    exact [expr ⟨_, _, _, rfl, rfl, λ b, ⟨_, _, h' b, rfl, rfl⟩⟩] },
  subst [expr this],
  congr' [] ["with", ident i, ident p],
  induction [expr p] [] ["with", ident x, ident a, ident f, ident h', ident i, ident c, ident x, ident a, ident f, ident h', ident i, ident c, ident p, ident IH] ["generalizing", ident f₁, ident f₂]; try { rcases [expr h _ _ r, "with", "⟨", ident a', ",", ident f', ",", ident f₁', ",", ident f₂', ",", ident e₁, ",", ident e₂, ",", ident h'', "⟩"],
    rcases [expr M.bisim_lemma P e₁, "with", "⟨", ident g₁', ",", ident e₁', ",", ident rfl, ",", ident rfl, "⟩"],
    rcases [expr M.bisim_lemma P e₂, "with", "⟨", ident g₂', ",", ident e₂', ",", ident e₃, ",", ident rfl, "⟩"],
    cases [expr h'.symm.trans e₁'] [],
    cases [expr h'.symm.trans e₂'] [] },
  { exact [expr (congr_fun (congr_fun e₃ i) c : _)] },
  { exact [expr IH _ _ (h'' _)] }
end

-- error in Data.Pfunctor.Multivariate.M: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem M.bisim₀
{α : typevec n}
(R : P.M α → P.M α → exprProp())
(h₀ : equivalence R)
(h : ∀
 x
 y, R x y → «expr = »(«expr <$$> »([«expr ::: »/«expr ::: »](id, quot.mk R), M.dest _ x), «expr <$$> »([«expr ::: »/«expr ::: »](id, quot.mk R), M.dest _ y)))
(x y)
(r : R x y) : «expr = »(x, y) :=
begin
  apply [expr M.bisim P R _ _ _ r],
  clear [ident r, ident x, ident y],
  introv [ident Hr],
  specialize [expr h _ _ Hr],
  clear [ident Hr],
  rcases [expr M.dest P x, "with", "⟨", ident ax, ",", ident fx, "⟩"],
  rcases [expr M.dest P y, "with", "⟨", ident ay, ",", ident fy, "⟩"],
  intro [ident h],
  rw ["[", expr map_eq, ",", expr map_eq, "]"] ["at", ident h],
  injection [expr h] ["with", ident h₀, ident h₁],
  subst [expr ay],
  simp [] [] [] [] [] ["at", ident h₁],
  clear [ident h],
  have [ident Hdrop] [":", expr «expr = »(drop_fun fx, drop_fun fy)] [],
  { replace [ident h₁] [] [":=", expr congr_arg drop_fun h₁],
    simpa [] [] [] [] [] ["using", expr h₁] },
  existsi ["[", expr ax, ",", expr drop_fun fx, ",", expr last_fun fx, ",", expr last_fun fy, "]"],
  rw ["[", expr split_drop_fun_last_fun, ",", expr Hdrop, ",", expr split_drop_fun_last_fun, "]"] [],
  simp [] [] [] [] [] [],
  intro [ident i],
  replace [ident h₁] [] [":=", expr congr_fun (congr_fun h₁ fin2.fz) i],
  simp [] [] [] ["[", expr («expr ⊚ »), ",", expr append_fun, ",", expr split_fun, "]"] [] ["at", ident h₁],
  replace [ident h₁] [] [":=", expr quot.exact _ h₁],
  rw [expr h₀.eqv_gen_iff] ["at", ident h₁],
  exact [expr h₁]
end

-- error in Data.Pfunctor.Multivariate.M: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem M.bisim'
{α : typevec n}
(R : P.M α → P.M α → exprProp())
(h : ∀
 x
 y, R x y → «expr = »(«expr <$$> »([«expr ::: »/«expr ::: »](id, quot.mk R), M.dest _ x), «expr <$$> »([«expr ::: »/«expr ::: »](id, quot.mk R), M.dest _ y)))
(x y)
(r : R x y) : «expr = »(x, y) :=
begin
  have [] [] [":=", expr M.bisim₀ P (eqv_gen R) _ _],
  { solve_by_elim [] [] ["[", expr eqv_gen.rel, "]"] [] },
  { apply [expr eqv_gen.is_equivalence] },
  { clear [ident r, ident x, ident y],
    introv [ident Hr],
    have [] [":", expr ∀ x y, R x y → eqv_gen R x y] [":=", expr @eqv_gen.rel _ R],
    induction [expr Hr] [] [] [],
    { rw ["<-", expr quot.factor_mk_eq R (eqv_gen R) this] [],
      rwa ["[", expr append_fun_comp_id, ",", "<-", expr mvfunctor.map_map, ",", "<-", expr mvfunctor.map_map, ",", expr h, "]"] [] },
    all_goals { cc } }
end

theorem M.dest_map {α β : Typevec n} (g : α ⟹ β) (x : P.M α) :
  M.dest P (g <$$> x) = (append_fun g fun x => g <$$> x) <$$> M.dest P x :=
  by 
    cases' x with a f 
    rw [map_eq]
    conv  => toRHS rw [M.dest, M.dest', map_eq, append_fun_comp_split_fun]
    rfl

theorem M.map_dest {α β : Typevec n} (g : (α ::: P.M α) ⟹ (β ::: P.M β)) (x : P.M α)
  (h : ∀ (x : P.M α), last_fun g x = (drop_fun g <$$> x : P.M β)) : g <$$> M.dest P x = M.dest P (drop_fun g <$$> x) :=
  by 
    rw [M.dest_map]
    congr 
    apply eq_of_drop_last_eq <;> simp 
    ext1 
    apply h

end Mvpfunctor

