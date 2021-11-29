import Mathbin.Data.Pfunctor.Univariate.Basic

/-!
# M-types

M types are potentially infinite tree-like structures. They are defined
as the greatest fixpoint of a polynomial functor.
-/


universe u v w

open Nat Function

open List hiding head'

variable(F : Pfunctor.{u})

-- error in Data.Pfunctor.Univariate.M: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
local prefix `♯`:0 := cast (by simp [] [] [] ["[", "*", "]"] [] [] <|> cc <|> solve_by_elim [] [] [] [])

namespace Pfunctor

namespace Approx

/-- `cofix_a F n` is an `n` level approximation of a M-type -/
inductive cofix_a : ℕ → Type u
  | continue : cofix_a 0
  | intro {n} : ∀ a, (F.B a → cofix_a n) → cofix_a (succ n)

/-- default inhabitant of `cofix_a` -/
protected def cofix_a.default [Inhabited F.A] : ∀ n, cofix_a F n
| 0 => cofix_a.continue
| succ n => cofix_a.intro (default _)$ fun _ => cofix_a.default n

instance  [Inhabited F.A] {n} : Inhabited (cofix_a F n) :=
  ⟨cofix_a.default F n⟩

theorem cofix_a_eq_zero : ∀ (x y : cofix_a F 0), x = y
| cofix_a.continue, cofix_a.continue => rfl

variable{F}

/--
The label of the root of the tree for a non-trivial
approximation of the cofix of a pfunctor.
-/
def head' : ∀ {n}, cofix_a F (succ n) → F.A
| n, cofix_a.intro i _ => i

/-- for a non-trivial approximation, return all the subtrees of the root -/
def children' : ∀ {n} (x : cofix_a F (succ n)), F.B (head' x) → cofix_a F n
| n, cofix_a.intro a f => f

theorem approx_eta {n : ℕ} (x : cofix_a F (n+1)) : x = cofix_a.intro (head' x) (children' x) :=
  by 
    cases x <;> rfl

/-- Relation between two approximations of the cofix of a pfunctor
that state they both contain the same data until one of them is truncated -/
inductive agree : ∀ {n : ℕ}, cofix_a F n → cofix_a F (n+1) → Prop
  | continue (x : cofix_a F 0) (y : cofix_a F 1) : agree x y
  | intro {n} {a} (x : F.B a → cofix_a F n) (x' : F.B a → cofix_a F (n+1)) :
  (∀ (i : F.B a), agree (x i) (x' i)) → agree (cofix_a.intro a x) (cofix_a.intro a x')

/--
Given an infinite series of approximations `approx`,
`all_agree approx` states that they are all consistent with each other.
-/
def all_agree (x : ∀ n, cofix_a F n) :=
  ∀ n, agree (x n) (x (succ n))

@[simp]
theorem agree_trival {x : cofix_a F 0} {y : cofix_a F 1} : agree x y :=
  by 
    constructor

theorem agree_children {n : ℕ} (x : cofix_a F (succ n)) (y : cofix_a F (succ n+1)) {i j} (h₀ : HEq i j)
  (h₁ : agree x y) : agree (children' x i) (children' y j) :=
  by 
    cases' h₁ with _ _ _ _ _ _ hagree 
    cases h₀ 
    apply hagree

/-- `truncate a` turns `a` into a more limited approximation -/
def truncate : ∀ {n : ℕ}, cofix_a F (n+1) → cofix_a F n
| 0, cofix_a.intro _ _ => cofix_a.continue
| succ n, cofix_a.intro i f => cofix_a.intro i$ truncate ∘ f

theorem truncate_eq_of_agree {n : ℕ} (x : cofix_a F n) (y : cofix_a F (succ n)) (h : agree x y) : truncate y = x :=
  by 
    induction n generalizing x y <;> cases x <;> cases y
    ·
      rfl
    ·
      cases' h with _ _ _ _ _ h₀ h₁ 
      cases h 
      simp only [truncate, Function.comp, true_andₓ, eq_self_iff_true, heq_iff_eq]
      ext y 
      apply n_ih 
      apply h₁

variable{X : Type w}

variable(f : X → F.obj X)

/-- `s_corec f i n` creates an approximation of height `n`
of the final coalgebra of `f` -/
def s_corec : ∀ (i : X) n, cofix_a F n
| _, 0 => cofix_a.continue
| j, succ n => cofix_a.intro (f j).1 fun i => s_corec ((f j).2 i) _

theorem P_corec (i : X) (n : ℕ) : agree (s_corec f i n) (s_corec f i (succ n)) :=
  by 
    induction' n with n generalizing i 
    constructor 
    cases' h : f i with y g 
    constructor 
    introv 
    apply n_ih

/-- `path F` provides indices to access internal nodes in `corec F` -/
def path (F : Pfunctor.{u}) :=
  List F.Idx

instance path.inhabited : Inhabited (path F) :=
  ⟨[]⟩

open List Nat

instance  : Subsingleton (cofix_a F 0) :=
  ⟨by 
      intros 
      casesM* cofix_a F 0
      rfl⟩

-- error in Data.Pfunctor.Univariate.M: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem head_succ'
(n m : exprℕ())
(x : ∀ n, cofix_a F n)
(Hconsistent : all_agree x) : «expr = »(head' (x (succ n)), head' (x (succ m))) :=
begin
  suffices [] [":", expr ∀ n, «expr = »(head' (x (succ n)), head' (x 1))],
  { simp [] [] [] ["[", expr this, "]"] [] [] },
  clear [ident m, ident n],
  intro [],
  cases [expr h₀, ":", expr x (succ n)] ["with", "_", ident i₀, ident f₀],
  cases [expr h₁, ":", expr x 1] ["with", "_", ident i₁, ident f₁],
  dsimp ["only"] ["[", expr head', "]"] [] [],
  induction [expr n] [] ["with", ident n] [],
  { rw [expr h₁] ["at", ident h₀],
    cases [expr h₀] [],
    trivial },
  { have [ident H] [] [":=", expr Hconsistent (succ n)],
    cases [expr h₂, ":", expr x (succ n)] ["with", "_", ident i₂, ident f₂],
    rw ["[", expr h₀, ",", expr h₂, "]"] ["at", ident H],
    apply [expr n_ih «expr ∘ »(truncate, f₀)],
    rw [expr h₂] [],
    cases [expr H] ["with", "_", "_", "_", "_", "_", "_", ident hagree],
    congr,
    funext [ident j],
    dsimp ["only"] ["[", expr comp_app, "]"] [] [],
    rw [expr truncate_eq_of_agree] [],
    apply [expr hagree] }
end

end Approx

open Approx

/-- Internal definition for `M`. It is needed to avoid name clashes
between `M.mk` and `M.cases_on` and the declarations generated for
the structure -/
structure M_intl where 
  approx : ∀ n, cofix_a F n 
  consistent : all_agree approx

/-- For polynomial functor `F`, `M F` is its final coalgebra -/
def M :=
  M_intl F

theorem M.default_consistent [Inhabited F.A] : ∀ n, agree (default (cofix_a F n)) (default (cofix_a F (succ n)))
| 0 => agree.continue _ _
| succ n => agree.intro _ _$ fun _ => M.default_consistent n

instance M.inhabited [Inhabited F.A] : Inhabited (M F) :=
  ⟨{ approx := fun n => default _, consistent := M.default_consistent _ }⟩

instance M_intl.inhabited [Inhabited F.A] : Inhabited (M_intl F) :=
  show Inhabited (M F)by 
    infer_instance

namespace M

theorem ext' (x y : M F) (H : ∀ (i : ℕ), x.approx i = y.approx i) : x = y :=
  by 
    cases x 
    cases y 
    congr with n 
    apply H

variable{X : Type _}

variable(f : X → F.obj X)

variable{F}

/-- Corecursor for the M-type defined by `F`. -/
protected def corec (i : X) : M F :=
  { approx := s_corec f i, consistent := P_corec _ _ }

variable{F}

/-- given a tree generated by `F`, `head` gives us the first piece of data
it contains -/
def head (x : M F) :=
  head' (x.1 1)

-- error in Data.Pfunctor.Univariate.M: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- return all the subtrees of the root of a tree `x : M F` -/ def children (x : M F) (i : F.B (head x)) : M F :=
let H := λ n : exprℕ(), @head_succ' _ n 0 x.1 x.2 in
{ approx := λ
  n, children' (x.1 _) (cast «expr $ »(congr_arg _, by simp [] [] ["only"] ["[", expr head, ",", expr H, "]"] [] []; refl) i),
  consistent := begin
    intro [],
    have [ident P'] [] [":=", expr x.2 (succ n)],
    apply [expr agree_children _ _ _ P'],
    transitivity [expr i],
    apply [expr cast_heq],
    symmetry,
    apply [expr cast_heq]
  end }

/-- select a subtree using a `i : F.Idx` or return an arbitrary tree if
`i` designates no subtree of `x` -/
def ichildren [Inhabited (M F)] [DecidableEq F.A] (i : F.Idx) (x : M F) : M F :=
  if H' : i.1 = head x then
    children x
      (cast
        (congr_argₓ _$
          by 
            simp only [head, H'] <;> rfl)
        i.2)
  else default _

theorem head_succ (n m : ℕ) (x : M F) : head' (x.approx (succ n)) = head' (x.approx (succ m)) :=
  head_succ' n m _ x.consistent

theorem head_eq_head' : ∀ (x : M F) (n : ℕ), head x = head' (x.approx$ n+1)
| ⟨x, h⟩, n => head_succ' _ _ _ h

theorem head'_eq_head : ∀ (x : M F) (n : ℕ), head' (x.approx$ n+1) = head x
| ⟨x, h⟩, n => head_succ' _ _ _ h

theorem truncate_approx (x : M F) (n : ℕ) : truncate (x.approx$ n+1) = x.approx n :=
  truncate_eq_of_agree _ _ (x.consistent _)

/-- unfold an M-type -/
def dest : M F → F.obj (M F)
| x => ⟨head x, fun i => children x i⟩

namespace Approx

/-- generates the approximations needed for `M.mk` -/
protected def s_mk (x : F.obj$ M F) : ∀ n, cofix_a F n
| 0 => cofix_a.continue
| succ n => cofix_a.intro x.1 fun i => (x.2 i).approx n

protected theorem P_mk (x : F.obj$ M F) : all_agree (approx.s_mk x)
| 0 =>
  by 
    constructor
| succ n =>
  by 
    constructor 
    introv 
    apply (x.2 i).consistent

end Approx

/-- constructor for M-types -/
protected def mk (x : F.obj$ M F) : M F :=
  { approx := approx.s_mk x, consistent := approx.P_mk x }

/-- `agree' n` relates two trees of type `M F` that
are the same up to dept `n` -/
inductive agree' : ℕ → M F → M F → Prop
  | trivialₓ (x y : M F) : agree' 0 x y
  | step {n : ℕ} {a} (x y : F.B a → M F) {x' y'} :
  x' = M.mk ⟨a, x⟩ → y' = M.mk ⟨a, y⟩ → (∀ i, agree' n (x i) (y i)) → agree' (succ n) x' y'

@[simp]
theorem dest_mk (x : F.obj$ M F) : dest (M.mk x) = x :=
  by 
    funext i 
    dsimp only [M.mk, dest]
    cases' x with x ch 
    congr with i 
    cases h : ch i 
    simp only [children, M.approx.s_mk, children', cast_eq]
    dsimp only [M.approx.s_mk, children']
    congr 
    rw [h]

-- error in Data.Pfunctor.Univariate.M: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem mk_dest (x : M F) : «expr = »(M.mk (dest x), x) :=
begin
  apply [expr ext'],
  intro [ident n],
  dsimp ["only"] ["[", expr M.mk, "]"] [] [],
  induction [expr n] [] ["with", ident n] [],
  { apply [expr subsingleton.elim] },
  dsimp ["only"] ["[", expr approx.s_mk, ",", expr dest, ",", expr head, "]"] [] [],
  cases [expr h, ":", expr x.approx (succ n)] ["with", "_", ident hd, ident ch],
  have [ident h'] [":", expr «expr = »(hd, head' (x.approx 1))] [],
  { rw ["[", "<-", expr head_succ' n, ",", expr h, ",", expr head', "]"] [],
    apply [expr x.consistent] },
  revert [ident ch],
  rw [expr h'] [],
  intros [],
  congr,
  { ext [] [ident a] [],
    dsimp ["only"] ["[", expr children, "]"] [] [],
    h_generalize ["!"] [ident hh] [":"] [expr «expr == »(a, a'')] [],
    rw [expr h] [],
    intros [],
    cases [expr hh] [],
    refl }
end

theorem mk_inj {x y : F.obj$ M F} (h : M.mk x = M.mk y) : x = y :=
  by 
    rw [←dest_mk x, h, dest_mk]

-- error in Data.Pfunctor.Univariate.M: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- destructor for M-types -/
protected
def cases {r : M F → Sort w} (f : ∀ x : «expr $ »(F.obj, M F), r (M.mk x)) (x : M F) : r x :=
suffices r (M.mk (dest x)), by { haveI [] [] [":=", expr classical.prop_decidable],
  haveI [] [] [":=", expr inhabited.mk x],
  rw ["[", "<-", expr mk_dest x, "]"] [],
  exact [expr this] },
f _

/-- destructor for M-types -/
protected def cases_on {r : M F → Sort w} (x : M F) (f : ∀ (x : F.obj$ M F), r (M.mk x)) : r x :=
  M.cases f x

/-- destructor for M-types, similar to `cases_on` but also
gives access directly to the root and subtrees on an M-type -/
protected def cases_on' {r : M F → Sort w} (x : M F) (f : ∀ a f, r (M.mk ⟨a, f⟩)) : r x :=
  M.cases_on x fun ⟨a, g⟩ => f a _

theorem approx_mk (a : F.A) (f : F.B a → M F) (i : ℕ) :
  (M.mk ⟨a, f⟩).approx (succ i) = cofix_a.intro a fun j => (f j).approx i :=
  rfl

@[simp]
theorem agree'_refl {n : ℕ} (x : M F) : agree' n x x :=
  by 
    induction n generalizing x <;>
      induction x using Pfunctor.M.casesOn' <;>
        constructor <;>
          try 
            rfl 
    intros 
    apply n_ih

-- error in Data.Pfunctor.Univariate.M: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem agree_iff_agree'
{n : exprℕ()}
(x y : M F) : «expr ↔ »(agree (x.approx n) «expr $ »(y.approx, «expr + »(n, 1)), agree' n x y) :=
begin
  split; intros [ident h],
  { induction [expr n] [] [] ["generalizing", ident x, ident y],
    constructor,
    { induction [expr x] ["using", ident pfunctor.M.cases_on'] [] [],
      induction [expr y] ["using", ident pfunctor.M.cases_on'] [] [],
      simp [] [] ["only"] ["[", expr approx_mk, "]"] [] ["at", ident h],
      cases [expr h] ["with", "_", "_", "_", "_", "_", "_", ident hagree],
      constructor; try { refl },
      intro [ident i],
      apply [expr n_ih],
      apply [expr hagree] } },
  { induction [expr n] [] [] ["generalizing", ident x, ident y],
    constructor,
    { cases [expr h] [],
      induction [expr x] ["using", ident pfunctor.M.cases_on'] [] [],
      induction [expr y] ["using", ident pfunctor.M.cases_on'] [] [],
      simp [] [] ["only"] ["[", expr approx_mk, "]"] [] [],
      have [ident h_a_1] [] [":=", expr mk_inj «expr‹ ›»(«expr = »(M.mk ⟨x_a, x_f⟩, M.mk ⟨h_a, h_x⟩))],
      cases [expr h_a_1] [],
      replace [ident h_a_2] [] [":=", expr mk_inj «expr‹ ›»(«expr = »(M.mk ⟨y_a, y_f⟩, M.mk ⟨h_a, h_y⟩))],
      cases [expr h_a_2] [],
      constructor,
      intro [ident i],
      apply [expr n_ih],
      simp [] [] [] ["*"] [] [] } }
end

@[simp]
theorem cases_mk {r : M F → Sort _} (x : F.obj$ M F) (f : ∀ (x : F.obj$ M F), r (M.mk x)) :
  Pfunctor.M.cases f (M.mk x) = f x :=
  by 
    dsimp only [M.mk, Pfunctor.M.cases, dest, head, approx.s_mk, head']
    cases x 
    dsimp only [approx.s_mk]
    apply eq_of_heq 
    apply rec_heq_of_heq 
    congr with x 
    dsimp only [children, approx.s_mk, children']
    cases h : x_snd x 
    dsimp only [head]
    congr with n 
    change (x_snd x).approx n = _ 
    rw [h]

@[simp]
theorem cases_on_mk {r : M F → Sort _} (x : F.obj$ M F) (f : ∀ (x : F.obj$ M F), r (M.mk x)) :
  Pfunctor.M.casesOn (M.mk x) f = f x :=
  cases_mk x f

@[simp]
theorem cases_on_mk' {r : M F → Sort _} {a} (x : F.B a → M F) (f : ∀ a (f : F.B a → M F), r (M.mk ⟨a, f⟩)) :
  Pfunctor.M.casesOn' (M.mk ⟨a, x⟩) f = f a x :=
  cases_mk ⟨_, x⟩ _

/-- `is_path p x` tells us if `p` is a valid path through `x` -/
inductive is_path : path F → M F → Prop
  | nil (x : M F) : is_path [] x
  | cons (xs : path F) {a} (x : M F) (f : F.B a → M F) (i : F.B a) :
  x = M.mk ⟨a, f⟩ → is_path xs (f i) → is_path (⟨a, i⟩ :: xs) x

theorem is_path_cons {xs : path F} {a a'} {f : F.B a → M F} {i : F.B a'} (h : is_path (⟨a', i⟩ :: xs) (M.mk ⟨a, f⟩)) :
  a = a' :=
  by 
    revert h 
    generalize h : M.mk ⟨a, f⟩ = x 
    intro h' 
    cases h' 
    subst x 
    cases mk_inj ‹_›
    rfl

-- error in Data.Pfunctor.Univariate.M: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_path_cons'
{xs : path F}
{a}
{f : F.B a → M F}
{i : F.B a}
(h : is_path [«expr :: »/«expr :: »/«expr :: »](⟨a, i⟩, xs) (M.mk ⟨a, f⟩)) : is_path xs (f i) :=
begin
  revert [ident h],
  generalize [ident h] [":"] [expr «expr = »(M.mk ⟨a, f⟩, x)],
  intros [ident h'],
  cases [expr h'] [],
  subst [expr x],
  have [] [] [":=", expr mk_inj «expr‹ ›»(_)],
  cases [expr this] [],
  cases [expr this] [],
  assumption
end

/-- follow a path through a value of `M F` and return the subtree
found at the end of the path if it is a valid path for that value and
return a default tree -/
def isubtree [DecidableEq F.A] [Inhabited (M F)] : path F → M F → M F
| [], x => x
| ⟨a, i⟩ :: ps, x =>
  Pfunctor.M.casesOn' x
    fun a' f =>
      (if h : a = a' then
        isubtree ps
          (f$
            cast
              (by 
                rw [h])
              i)
      else default (M F) :
      (fun x => M F) (M.mk ⟨a', f⟩))

-- error in Data.Pfunctor.Univariate.M: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- similar to `isubtree` but returns the data at the end of the path instead
of the whole subtree -/ def iselect [decidable_eq F.A] [inhabited (M F)] (ps : path F) : M F → F.A :=
λ x : M F, «expr $ »(head, isubtree ps x)

theorem iselect_eq_default [DecidableEq F.A] [Inhabited (M F)] (ps : path F) (x : M F) (h : ¬is_path ps x) :
  iselect ps x = head (default$ M F) :=
  by 
    induction ps generalizing x
    ·
      exfalso 
      apply h 
      constructor
    ·
      cases' ps_hd with a i 
      induction x using Pfunctor.M.casesOn' 
      simp only [iselect, isubtree] at ps_ih⊢
      byCases' h'' : a = x_a 
      subst x_a
      ·
        simp only [dif_pos, eq_self_iff_true, cases_on_mk']
        rw [ps_ih]
        intro h' 
        apply h 
        constructor <;>
          try 
            rfl 
        apply h'
      ·
        simp 

@[simp]
theorem head_mk (x : F.obj (M F)) : head (M.mk x) = x.1 :=
  Eq.symm$
    calc x.1 = (dest (M.mk x)).1 :=
      by 
        rw [dest_mk]
      _ = head (M.mk x) :=
      by 
        rfl
      

theorem children_mk {a} (x : F.B a → M F) (i : F.B (head (M.mk ⟨a, x⟩))) :
  children (M.mk ⟨a, x⟩) i =
    x
      (cast
        (by 
          rw [head_mk])
        i) :=
  by 
    apply ext' <;> intro n <;> rfl

@[simp]
theorem ichildren_mk [DecidableEq F.A] [Inhabited (M F)] (x : F.obj (M F)) (i : F.Idx) :
  ichildren i (M.mk x) = x.iget i :=
  by 
    dsimp only [ichildren, Pfunctor.Obj.iget]
    congr with h 
    apply ext' 
    dsimp only [children', M.mk, approx.s_mk]
    intros 
    rfl

@[simp]
theorem isubtree_cons [DecidableEq F.A] [Inhabited (M F)] (ps : path F) {a} (f : F.B a → M F) {i : F.B a} :
  isubtree (⟨_, i⟩ :: ps) (M.mk ⟨a, f⟩) = isubtree ps (f i) :=
  by 
    simp only [isubtree, ichildren_mk, Pfunctor.Obj.iget, dif_pos, isubtree, M.cases_on_mk'] <;> rfl

@[simp]
theorem iselect_nil [DecidableEq F.A] [Inhabited (M F)] {a} (f : F.B a → M F) : iselect nil (M.mk ⟨a, f⟩) = a :=
  by 
    rfl

@[simp]
theorem iselect_cons [DecidableEq F.A] [Inhabited (M F)] (ps : path F) {a} (f : F.B a → M F) {i} :
  iselect (⟨a, i⟩ :: ps) (M.mk ⟨a, f⟩) = iselect ps (f i) :=
  by 
    simp only [iselect, isubtree_cons]

theorem corec_def {X} (f : X → F.obj X) (x₀ : X) : M.corec f x₀ = M.mk (M.corec f <$> f x₀) :=
  by 
    dsimp only [M.corec, M.mk]
    congr with n 
    cases' n with n
    ·
      dsimp only [s_corec, approx.s_mk]
      rfl
    ·
      dsimp only [s_corec, approx.s_mk]
      cases h : f x₀ 
      dsimp only [· <$> ·, Pfunctor.map]
      congr

-- error in Data.Pfunctor.Univariate.M: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
theorem ext_aux
[inhabited (M F)]
[decidable_eq F.A]
{n : exprℕ()}
(x y z : M F)
(hx : agree' n z x)
(hy : agree' n z y)
(hrec : ∀
 ps : path F, «expr = »(n, ps.length) → «expr = »(iselect ps x, iselect ps y)) : «expr = »(x.approx «expr + »(n, 1), y.approx «expr + »(n, 1)) :=
begin
  induction [expr n] [] ["with", ident n] ["generalizing", ident x, ident y, ident z],
  { specialize [expr hrec «expr[ , ]»([]) rfl],
    induction [expr x] ["using", ident pfunctor.M.cases_on'] [] [],
    induction [expr y] ["using", ident pfunctor.M.cases_on'] [] [],
    simp [] [] ["only"] ["[", expr iselect_nil, "]"] [] ["at", ident hrec],
    subst [expr hrec],
    simp [] [] ["only"] ["[", expr approx_mk, ",", expr true_and, ",", expr eq_self_iff_true, ",", expr heq_iff_eq, "]"] [] [],
    apply [expr subsingleton.elim] },
  { cases [expr hx] [],
    cases [expr hy] [],
    induction [expr x] ["using", ident pfunctor.M.cases_on'] [] [],
    induction [expr y] ["using", ident pfunctor.M.cases_on'] [] [],
    subst [expr z],
    iterate [3] { have [] [] [":=", expr mk_inj «expr‹ ›»(_)],
      repeat { cases [expr this] [] } },
    simp [] [] ["only"] ["[", expr approx_mk, ",", expr true_and, ",", expr eq_self_iff_true, ",", expr heq_iff_eq, "]"] [] [],
    ext [] [ident i] [],
    apply [expr n_ih],
    { solve_by_elim [] [] [] [] },
    { solve_by_elim [] [] [] [] },
    introv [ident h],
    specialize [expr hrec [«expr :: »/«expr :: »/«expr :: »](⟨_, i⟩, ps) (congr_arg _ h)],
    simp [] [] ["only"] ["[", expr iselect_cons, "]"] [] ["at", ident hrec],
    exact [expr hrec] }
end

open Pfunctor.Approx

variable{F}

attribute [local instance] Classical.propDecidable

-- error in Data.Pfunctor.Univariate.M: ././Mathport/Syntax/Translate/Basic.lean:179:15: failed to format: format: uncaught backtrack exception
theorem ext
[inhabited (M F)]
(x y : M F)
(H : ∀ ps : path F, «expr = »(iselect ps x, iselect ps y)) : «expr = »(x, y) :=
begin
  apply [expr ext'],
  intro [ident i],
  induction [expr i] [] ["with", ident i] [],
  { cases [expr x.approx 0] [],
    cases [expr y.approx 0] [],
    constructor },
  { apply [expr ext_aux x y x],
    { rw ["<-", expr agree_iff_agree'] [],
      apply [expr x.consistent] },
    { rw ["[", "<-", expr agree_iff_agree', ",", expr i_ih, "]"] [],
      apply [expr y.consistent] },
    introv [ident H'],
    dsimp ["only"] ["[", expr iselect, "]"] [] ["at", ident H],
    cases [expr H'] [],
    apply [expr H ps] }
end

section Bisim

variable(R : M F → M F → Prop)

local infixl:50 " ~ " => R

/-- Bisimulation is the standard proof technique for equality between
infinite tree-like structures -/
structure is_bisimulation : Prop where 
  head : ∀ {a a'} {f f'}, M.mk ⟨a, f⟩ ~ M.mk ⟨a', f'⟩ → a = a' 
  tail : ∀ {a} {f f' : F.B a → M F}, M.mk ⟨a, f⟩ ~ M.mk ⟨a, f'⟩ → ∀ (i : F.B a), f i ~ f' i

-- error in Data.Pfunctor.Univariate.M: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nth_of_bisim
[inhabited (M F)]
(bisim : is_bisimulation R)
(s₁ s₂)
(ps : path F) : «expr ~ »(s₁, s₂) → «expr ∨ »(is_path ps s₁, is_path ps s₂) → «expr ∧ »(«expr = »(iselect ps s₁, iselect ps s₂), «expr∃ , »((a)
  (f
   f' : F.B a → M F), «expr ∧ »(«expr = »(isubtree ps s₁, M.mk ⟨a, f⟩), «expr ∧ »(«expr = »(isubtree ps s₂, M.mk ⟨a, f'⟩), ∀
    i : F.B a, «expr ~ »(f i, f' i))))) :=
begin
  intros [ident h₀, ident hh],
  induction [expr s₁] ["using", ident pfunctor.M.cases_on'] ["with", ident a, ident f] [],
  induction [expr s₂] ["using", ident pfunctor.M.cases_on'] ["with", ident a', ident f'] [],
  have [] [":", expr «expr = »(a, a')] [":=", expr bisim.head h₀],
  subst [expr a'],
  induction [expr ps] [] ["with", ident i, ident ps] ["generalizing", ident a, ident f, ident f'],
  { existsi ["[", expr rfl, ",", expr a, ",", expr f, ",", expr f', ",", expr rfl, ",", expr rfl, "]"],
    apply [expr bisim.tail h₀] },
  cases [expr i] ["with", ident a', ident i],
  have [] [":", expr «expr = »(a, a')] [],
  { cases [expr hh] []; cases [expr is_path_cons hh] []; refl },
  subst [expr a'],
  dsimp ["only"] ["[", expr iselect, "]"] [] ["at", ident ps_ih, "⊢"],
  have [ident h₁] [] [":=", expr bisim.tail h₀ i],
  induction [expr h, ":", expr f i] ["using", ident pfunctor.M.cases_on'] ["with", ident a₀, ident f₀] [],
  induction [expr h', ":", expr f' i] ["using", ident pfunctor.M.cases_on'] ["with", ident a₁, ident f₁] [],
  simp [] [] ["only"] ["[", expr h, ",", expr h', ",", expr isubtree_cons, "]"] [] ["at", ident ps_ih, "⊢"],
  rw ["[", expr h, ",", expr h', "]"] ["at", ident h₁],
  have [] [":", expr «expr = »(a₀, a₁)] [":=", expr bisim.head h₁],
  subst [expr a₁],
  apply [expr ps_ih _ _ _ h₁],
  rw ["[", "<-", expr h, ",", "<-", expr h', "]"] [],
  apply [expr or_of_or_of_imp_of_imp hh is_path_cons' is_path_cons']
end

-- error in Data.Pfunctor.Univariate.M: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_of_bisim [nonempty (M F)] (bisim : is_bisimulation R) : ∀ s₁ s₂, «expr ~ »(s₁, s₂) → «expr = »(s₁, s₂) :=
begin
  inhabit [expr M F] [],
  introv [ident Hr],
  apply [expr ext],
  introv [],
  by_cases [expr h, ":", expr «expr ∨ »(is_path ps s₁, is_path ps s₂)],
  { have [ident H] [] [":=", expr nth_of_bisim R bisim _ _ ps Hr h],
    exact [expr H.left] },
  { rw [expr not_or_distrib] ["at", ident h],
    cases [expr h] ["with", ident h₀, ident h₁],
    simp [] [] ["only"] ["[", expr iselect_eq_default, ",", "*", ",", expr not_false_iff, "]"] [] [] }
end

end Bisim

universe u' v'

/-- corecursor for `M F` with swapped arguments -/
def corec_on {X : Type _} (x₀ : X) (f : X → F.obj X) : M F :=
  M.corec f x₀

variable{P : Pfunctor.{u}}{α : Type u}

theorem dest_corec (g : α → P.obj α) (x : α) : M.dest (M.corec g x) = M.corec g <$> g x :=
  by 
    rw [corec_def, dest_mk]

-- error in Data.Pfunctor.Univariate.M: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem bisim
(R : M P → M P → exprProp())
(h : ∀
 x
 y, R x y → «expr∃ , »((a
   f
   f'), «expr ∧ »(«expr = »(M.dest x, ⟨a, f⟩), «expr ∧ »(«expr = »(M.dest y, ⟨a, f'⟩), ∀
    i, R (f i) (f' i))))) : ∀ x y, R x y → «expr = »(x, y) :=
begin
  introv [ident h'],
  haveI [] [] [":=", expr inhabited.mk x.head],
  apply [expr eq_of_bisim R _ _ _ h'],
  clear [ident h', ident x, ident y],
  split; introv [ident ih]; rcases [expr h _ _ ih, "with", "⟨", ident a'', ",", ident g, ",", ident g', ",", ident h₀, ",", ident h₁, ",", ident h₂, "⟩"]; clear [ident h],
  { replace [ident h₀] [] [":=", expr congr_arg sigma.fst h₀],
    replace [ident h₁] [] [":=", expr congr_arg sigma.fst h₁],
    simp [] [] ["only"] ["[", expr dest_mk, "]"] [] ["at", ident h₀, ident h₁],
    rw ["[", expr h₀, ",", expr h₁, "]"] [] },
  { simp [] [] ["only"] ["[", expr dest_mk, "]"] [] ["at", ident h₀, ident h₁],
    cases [expr h₀] [],
    cases [expr h₁] [],
    apply [expr h₂] }
end

-- error in Data.Pfunctor.Univariate.M: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem bisim'
{α : Type*}
(Q : α → exprProp())
(u v : α → M P)
(h : ∀
 x, Q x → «expr∃ , »((a
   f
   f'), «expr ∧ »(«expr = »(M.dest (u x), ⟨a, f⟩), «expr ∧ »(«expr = »(M.dest (v x), ⟨a, f'⟩), ∀
    i, «expr∃ , »((x'), «expr ∧ »(Q x', «expr ∧ »(«expr = »(f i, u x'), «expr = »(f' i, v x')))))))) : ∀
x, Q x → «expr = »(u x, v x) :=
λ x Qx, let R := λ w z : M P, «expr∃ , »((x'), «expr ∧ »(Q x', «expr ∧ »(«expr = »(w, u x'), «expr = »(z, v x')))) in
@M.bisim P R (λ (x y) ⟨x', Qx', xeq, yeq⟩, let ⟨a, f, f', ux'eq, vx'eq, h'⟩ := h x' Qx' in
 ⟨a, f, f', «expr ▸ »(xeq.symm, ux'eq), «expr ▸ »(yeq.symm, vx'eq), h'⟩) _ _ ⟨x, Qx, rfl, rfl⟩

theorem bisim_equiv (R : M P → M P → Prop)
  (h : ∀ x y, R x y → ∃ a f f', M.dest x = ⟨a, f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ ∀ i, R (f i) (f' i)) : ∀ x y, R x y → x = y :=
  fun x y Rxy =>
    let Q : M P × M P → Prop := fun p => R p.fst p.snd 
    bisim' Q Prod.fst Prod.snd
      (fun p Qp =>
        let ⟨a, f, f', hx, hy, h'⟩ := h p.fst p.snd Qp
        ⟨a, f, f', hx, hy, fun i => ⟨⟨f i, f' i⟩, h' i, rfl, rfl⟩⟩)
      ⟨x, y⟩ Rxy

-- error in Data.Pfunctor.Univariate.M: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem corec_unique
(g : α → P.obj α)
(f : α → M P)
(hyp : ∀ x, «expr = »(M.dest (f x), «expr <$> »(f, g x))) : «expr = »(f, M.corec g) :=
begin
  ext [] [ident x] [],
  apply [expr bisim' (λ x, true) _ _ _ _ trivial],
  clear [ident x],
  intros [ident x, "_"],
  cases [expr gxeq, ":", expr g x] ["with", ident a, ident f'],
  have [ident h₀] [":", expr «expr = »(M.dest (f x), ⟨a, «expr ∘ »(f, f')⟩)] [],
  { rw ["[", expr hyp, ",", expr gxeq, ",", expr pfunctor.map_eq, "]"] [] },
  have [ident h₁] [":", expr «expr = »(M.dest (M.corec g x), ⟨a, «expr ∘ »(M.corec g, f')⟩)] [],
  { rw ["[", expr dest_corec, ",", expr gxeq, ",", expr pfunctor.map_eq, "]"] [] },
  refine [expr ⟨_, _, _, h₀, h₁, _⟩],
  intro [ident i],
  exact [expr ⟨f' i, trivial, rfl, rfl⟩]
end

/-- corecursor where the state of the computation can be sent downstream
in the form of a recursive call -/
def corec₁ {α : Type u} (F : ∀ X, (α → X) → α → P.obj X) : α → M P :=
  M.corec (F _ id)

-- error in Data.Pfunctor.Univariate.M: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- corecursor where it is possible to return a fully formed value at any point
of the computation -/
def corec' {α : Type u} (F : ∀ {X : Type u}, (α → X) → α → «expr ⊕ »(M P, P.obj X)) (x : α) : M P :=
corec₁ (λ (X rec) (a : «expr ⊕ »(M P, α)), let y := «expr >>= »(a, F «expr ∘ »(rec, sum.inr)) in
 match y with
 | sum.inr y := y
 | sum.inl y := «expr <$> »(«expr ∘ »(rec, sum.inl), M.dest y) end) (@sum.inr (M P) _ x)

end M

end Pfunctor

