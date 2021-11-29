import Mathbin.Tactic.Ring 
import Mathbin.Data.Num.Lemmas 
import Mathbin.Data.Tree

/-!
# ring2

An experimental variant on the `ring` tactic that uses computational
reflection instead of proof generation. Useful for kernel benchmarking.
-/


namespace Tree

/-- `(reflect' t u α)` quasiquotes a tree `(t: tree expr)` of quoted
values of type `α` at level `u` into an `expr` which reifies to a `tree α`
containing the reifications of the `expr`s from the original `t`. -/
protected unsafe def reflect' (u : level) (α : expr) : Tree expr → expr
| Tree.nil => (expr.const `` Tree.nil [u] : expr) α
| Tree.node a t₁ t₂ => (expr.const `` Tree.node [u] : expr) α a t₁.reflect' t₂.reflect'

/-- Returns an element indexed by `n`, or zero if `n` isn't a valid index.
See `tree.get`. -/
protected def get_or_zero {α} [HasZero α] (t : Tree α) (n : PosNum) : α :=
  t.get_or_else n 0

end Tree

namespace Tactic.Ring2

-- error in Tactic.Ring2: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler has_reflect
/-- A reflected/meta representation of an expression in a commutative
semiring. This representation is a direct translation of such
expressions - see `horner_expr` for a normal form. -/ @[derive #[expr has_reflect]] inductive csring_expr
| atom : pos_num → csring_expr
| const : num → csring_expr
| add : csring_expr → csring_expr → csring_expr
| mul : csring_expr → csring_expr → csring_expr
| pow : csring_expr → num → csring_expr

namespace CsringExpr

instance : Inhabited csring_expr :=
  ⟨const 0⟩

/-- Evaluates a reflected `csring_expr` into an element of the
original `comm_semiring` type `α`, retrieving opaque elements
(atoms) from the tree `t`. -/
def eval {α} [CommSemiringₓ α] (t : Tree α) : csring_expr → α
| atom n => t.get_or_zero n
| const n => n
| add x y => eval x+eval y
| mul x y => eval x*eval y
| pow x n => eval x ^ (n : ℕ)

end CsringExpr

-- error in Tactic.Ring2: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler decidable_eq
/-- An efficient representation of expressions in a commutative
semiring using the sparse Horner normal form. This type admits
non-optimal instantiations (e.g. `P` can be represented as `P+0+0`),
so to get good performance out of it, care must be taken to maintain
an optimal, *canonical* form. -/ @[derive #[expr decidable_eq]] inductive horner_expr
| const : znum → horner_expr
| horner : horner_expr → pos_num → num → horner_expr → horner_expr

namespace HornerExpr

/-- True iff the `horner_expr` argument is a valid `csring_expr`.
For that to be the case, all its constants must be non-negative. -/
def is_cs : horner_expr → Prop
| const n => ∃ m : Num, n = m.to_znum
| horner a x n b => is_cs a ∧ is_cs b

instance : HasZero horner_expr :=
  ⟨const 0⟩

instance : HasOne horner_expr :=
  ⟨const 1⟩

instance : Inhabited horner_expr :=
  ⟨0⟩

/-- Represent a `csring_expr.atom` in Horner form. -/
def atom (n : PosNum) : horner_expr :=
  horner 1 n 1 0

def toString : horner_expr → Stringₓ
| const n => _root_.repr n
| horner a x n b => "(" ++ toString a ++ ") * x" ++ _root_.repr x ++ "^" ++ _root_.repr n ++ " + " ++ toString b

instance : HasToString horner_expr :=
  ⟨toString⟩

/-- Alternative constructor for (horner a x n b) which maintains canonical
form by simplifying special cases of `a`. -/
def horner' (a : horner_expr) (x : PosNum) (n : Num) (b : horner_expr) : horner_expr :=
  match a with 
  | const q => if q = 0 then b else horner a x n b
  | horner a₁ x₁ n₁ b₁ => if x₁ = x ∧ b₁ = 0 then horner a₁ x (n₁+n) b else horner a x n b

def add_const (k : Znum) (e : horner_expr) : horner_expr :=
  if k = 0 then e else
    by 
      induction' e with n a x n b A B
      ·
        exact const (k+n)
      ·
        exact horner a x n B

def add_aux (a₁ : horner_expr) (A₁ : horner_expr → horner_expr) (x₁ : PosNum) :
  horner_expr → Num → horner_expr → (horner_expr → horner_expr) → horner_expr
| const n₂, n₁, b₁, B₁ => add_const n₂ (horner a₁ x₁ n₁ b₁)
| horner a₂ x₂ n₂ b₂, n₁, b₁, B₁ =>
  let e₂ := horner a₂ x₂ n₂ b₂ 
  match PosNum.cmp x₁ x₂ with 
  | Ordering.lt => horner a₁ x₁ n₁ (B₁ e₂)
  | Ordering.gt => horner a₂ x₂ n₂ (add_aux b₂ n₁ b₁ B₁)
  | Ordering.eq =>
    match Num.sub' n₁ n₂ with 
    | Znum.zero => horner' (A₁ a₂) x₁ n₁ (B₁ b₂)
    | Znum.pos k => horner (add_aux a₂ k 0 id) x₁ n₂ (B₁ b₂)
    | Znum.neg k => horner (A₁ (horner a₂ x₁ k 0)) x₁ n₁ (B₁ b₂)

def add : horner_expr → horner_expr → horner_expr
| const n₁, e₂ => add_const n₁ e₂
| horner a₁ x₁ n₁ b₁, e₂ => add_aux a₁ (add a₁) x₁ e₂ n₁ b₁ (add b₁)

def neg (e : horner_expr) : horner_expr :=
  by 
    induction' e with n a x n b A B
    ·
      exact const (-n)
    ·
      exact horner A x n B

def mul_const (k : Znum) (e : horner_expr) : horner_expr :=
  if k = 0 then 0 else
    if k = 1 then e else
      by 
        induction' e with n a x n b A B
        ·
          exact const (n*k)
        ·
          exact horner A x n B

def mul_aux a₁ x₁ n₁ b₁ (A₁ B₁ : horner_expr → horner_expr) : horner_expr → horner_expr
| const n₂ => mul_const n₂ (horner a₁ x₁ n₁ b₁)
| e₂@(horner a₂ x₂ n₂ b₂) =>
  match PosNum.cmp x₁ x₂ with 
  | Ordering.lt => horner (A₁ e₂) x₁ n₁ (B₁ e₂)
  | Ordering.gt => horner (mul_aux a₂) x₂ n₂ (mul_aux b₂)
  | Ordering.eq =>
    let haa := horner' (mul_aux a₂) x₁ n₂ 0
    if b₂ = 0 then haa else haa.add (horner (A₁ b₂) x₁ n₁ (B₁ b₂))

def mul : horner_expr → horner_expr → horner_expr
| const n₁ => mul_const n₁
| horner a₁ x₁ n₁ b₁ => mul_aux a₁ x₁ n₁ b₁ (mul a₁) (mul b₁)

instance : Add horner_expr :=
  ⟨add⟩

instance : Neg horner_expr :=
  ⟨neg⟩

instance : Mul horner_expr :=
  ⟨mul⟩

def pow (e : horner_expr) : Num → horner_expr
| 0 => 1
| Num.pos p =>
  by 
    induction' p with p ep p ep
    ·
      exact e
    ·
      exact (ep.mul ep).mul e
    ·
      exact ep.mul ep

def inv (e : horner_expr) : horner_expr :=
  0

/-- Brings expressions into Horner normal form. -/
def of_csexpr : csring_expr → horner_expr
| csring_expr.atom n => atom n
| csring_expr.const n => const n.to_znum
| csring_expr.add x y => (of_csexpr x).add (of_csexpr y)
| csring_expr.mul x y => (of_csexpr x).mul (of_csexpr y)
| csring_expr.pow x n => (of_csexpr x).pow n

/-- Evaluates a reflected `horner_expr` - see `csring_expr.eval`. -/
def cseval {α} [CommSemiringₓ α] (t : Tree α) : horner_expr → α
| const n => n.abs
| horner a x n b => Tactic.Ring.hornerₓ (cseval a) (t.get_or_zero x) n (cseval b)

theorem cseval_atom {α} [CommSemiringₓ α] (t : Tree α) (n : PosNum) :
  (atom n).IsCs ∧ cseval t (atom n) = t.get_or_zero n :=
  ⟨⟨⟨1, rfl⟩, ⟨0, rfl⟩⟩, (Tactic.Ring.horner_atomₓ _).symm⟩

theorem cseval_add_const {α} [CommSemiringₓ α] (t : Tree α) (k : Num) {e : horner_expr} (cs : e.is_cs) :
  (add_const k.to_znum e).IsCs ∧ cseval t (add_const k.to_znum e) = k+cseval t e :=
  by 
    simp [add_const]
    cases k <;> simp 
    simp
      [show Znum.pos k ≠ 0 from
        by 
          decide]
    induction' e with n a x n b A B <;> simp 
    ·
      rcases cs with ⟨n, rfl⟩
      refine'
        ⟨⟨n+Num.pos k,
            by 
              simp [add_commₓ] <;> rfl⟩,
          _⟩
      cases n <;> simp 
    ·
      rcases B cs.2 with ⟨csb, h⟩
      simp [cs.1]
      rw [←Tactic.Ring.horner_add_constₓ, add_commₓ]
      rw [add_commₓ]

theorem cseval_horner' {α} [CommSemiringₓ α] (t : Tree α) a x n b (h₁ : is_cs a) (h₂ : is_cs b) :
  (horner' a x n b).IsCs ∧
    cseval t (horner' a x n b) = Tactic.Ring.hornerₓ (cseval t a) (t.get_or_zero x) n (cseval t b) :=
  by 
    cases' a with n₁ a₁ x₁ n₁ b₁ <;> simp [horner'] <;> splitIfs
    ·
      simp [Tactic.Ring.hornerₓ]
    ·
      exact ⟨⟨h₁, h₂⟩, rfl⟩
    ·
      refine' ⟨⟨h₁.1, h₂⟩, Eq.symm _⟩
      simp 
      apply Tactic.Ring.horner_hornerₓ 
      simp 
    ·
      exact ⟨⟨h₁, h₂⟩, rfl⟩

-- error in Tactic.Ring2: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cseval_add
{α}
[comm_semiring α]
(t : tree α)
{e₁ e₂ : horner_expr}
(cs₁ : e₁.is_cs)
(cs₂ : e₂.is_cs) : «expr ∧ »((add e₁ e₂).is_cs, «expr = »(cseval t (add e₁ e₂), «expr + »(cseval t e₁, cseval t e₂))) :=
begin
  induction [expr e₁] [] ["with", ident n₁, ident a₁, ident x₁, ident n₁, ident b₁, ident A₁, ident B₁] ["generalizing", ident e₂]; simp ["!"] [] [] [] [] [],
  { rcases [expr cs₁, "with", "⟨", ident n₁, ",", ident rfl, "⟩"],
    simpa [] [] [] [] [] ["using", expr cseval_add_const t n₁ cs₂] },
  induction [expr e₂] [] ["with", ident n₂, ident a₂, ident x₂, ident n₂, ident b₂, ident A₂, ident B₂] ["generalizing", ident n₁, ident b₁],
  { rcases [expr cs₂, "with", "⟨", ident n₂, ",", ident rfl, "⟩"],
    simp ["!"] [] [] ["[", expr cseval_add_const t n₂ cs₁, ",", expr add_comm, "]"] [] [] },
  cases [expr cs₁] ["with", ident csa₁, ident csb₁],
  cases [expr id cs₂] ["with", ident csa₂, ident csb₂],
  simp ["!"] [] [] [] [] [],
  have [ident C] [] [":=", expr pos_num.cmp_to_nat x₁ x₂],
  cases [expr pos_num.cmp x₁ x₂] []; simp ["!"] [] [] [] [] [],
  { rcases [expr B₁ csb₁ cs₂, "with", "⟨", ident csh, ",", ident h, "⟩"],
    refine [expr ⟨⟨csa₁, csh⟩, eq.symm _⟩],
    apply [expr tactic.ring.horner_add_const],
    exact [expr h.symm] },
  { cases [expr C] [],
    have [ident B0] [":", expr is_cs 0 → ∀
     {e₂ : horner_expr}, is_cs e₂ → «expr ∧ »(is_cs (add 0 e₂), «expr = »(cseval t (add 0 e₂), «expr + »(cseval t 0, cseval t e₂)))] [":=", expr λ
     _ e₂ c, ⟨c, (zero_add _).symm⟩],
    cases [expr e, ":", expr num.sub' n₁ n₂] ["with", ident k, ident k]; simp ["!"] [] [] [] [] [],
    { have [] [":", expr «expr = »(n₁, n₂)] [],
      { have [] [] [":=", expr congr_arg (coe : znum → exprℤ()) e],
        simp [] [] [] [] [] ["at", ident this],
        have [] [] [":=", expr sub_eq_zero.1 this],
        rw ["[", "<-", expr num.to_nat_to_int, ",", "<-", expr num.to_nat_to_int, "]"] ["at", ident this],
        exact [expr num.to_nat_inj.1 (int.coe_nat_inj this)] },
      subst [expr n₂],
      rcases [expr cseval_horner' _ _ _ _ _ _ _, "with", "⟨", ident csh, ",", ident h, "⟩"],
      { refine [expr ⟨csh, h.trans (eq.symm _)⟩],
        simp [] [] [] ["*"] [] [],
        apply [expr tactic.ring.horner_add_horner_eq]; try { refl } },
      all_goals { simp ["!"] [] [] ["*"] [] [] } },
    { simp [] [] [] ["[", expr B₁ csb₁ csb₂, ",", expr add_comm, "]"] [] [],
      rcases [expr A₂ csa₂ _ _ B0 ⟨csa₁, 0, rfl⟩, "with", "⟨", ident csh, ",", ident h, "⟩"],
      refine [expr ⟨csh, eq.symm _⟩],
      rw ["[", expr show «expr = »(id, add 0), from rfl, ",", expr h, "]"] [],
      apply [expr tactic.ring.horner_add_horner_gt],
      { change [expr «expr = »((«expr + »(_, k) : exprℕ()), _)] [] [],
        rw ["[", "<-", expr int.coe_nat_inj', ",", expr int.coe_nat_add, ",", expr eq_comm, ",", "<-", expr sub_eq_iff_eq_add', "]"] [],
        simpa [] [] [] [] [] ["using", expr congr_arg (coe : znum → exprℤ()) e] },
      { refl },
      { apply [expr add_comm] } },
    { have [] [":", expr (horner a₂ x₁ (num.pos k) 0).is_cs] [":=", expr ⟨csa₂, 0, rfl⟩],
      simp [] [] [] ["[", expr B₁ csb₁ csb₂, ",", expr A₁ csa₁ this, "]"] [] [],
      symmetry,
      apply [expr tactic.ring.horner_add_horner_lt],
      { change [expr «expr = »((«expr + »(_, k) : exprℕ()), _)] [] [],
        rw ["[", "<-", expr int.coe_nat_inj', ",", expr int.coe_nat_add, ",", expr eq_comm, ",", "<-", expr sub_eq_iff_eq_add', ",", "<-", expr neg_inj, ",", expr neg_sub, "]"] [],
        simpa [] [] [] [] [] ["using", expr congr_arg (coe : znum → exprℤ()) e] },
      all_goals { refl } } },
  { rcases [expr B₂ csb₂ _ _ B₁ ⟨csa₁, csb₁⟩, "with", "⟨", ident csh, ",", ident h, "⟩"],
    refine [expr ⟨⟨csa₂, csh⟩, eq.symm _⟩],
    apply [expr tactic.ring.const_add_horner],
    simp [] [] [] ["[", expr h, "]"] [] [] }
end

theorem cseval_mul_const {α} [CommSemiringₓ α] (t : Tree α) (k : Num) {e : horner_expr} (cs : e.is_cs) :
  (mul_const k.to_znum e).IsCs ∧ cseval t (mul_const k.to_znum e) = cseval t e*k :=
  by 
    simp [mul_const]
    splitIfs with h h
    ·
      cases (Num.to_znum_inj.1 h : k = 0)
      exact ⟨⟨0, rfl⟩, (mul_zero _).symm⟩
    ·
      cases (Num.to_znum_inj.1 h : k = 1)
      exact ⟨cs, (mul_oneₓ _).symm⟩
    induction' e with n a x n b A B <;> simp 
    ·
      rcases cs with ⟨n, rfl⟩
      suffices 
      refine' ⟨⟨n*k, this⟩, _⟩
      swap
      ·
        cases n <;> cases k <;> rfl 
      rw [show _ from this]
      simp 
    ·
      cases cs 
      simp 
      symm 
      apply Tactic.Ring.horner_mul_constₓ <;> rfl

-- error in Tactic.Ring2: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cseval_mul
{α}
[comm_semiring α]
(t : tree α)
{e₁ e₂ : horner_expr}
(cs₁ : e₁.is_cs)
(cs₂ : e₂.is_cs) : «expr ∧ »((mul e₁ e₂).is_cs, «expr = »(cseval t (mul e₁ e₂), «expr * »(cseval t e₁, cseval t e₂))) :=
begin
  induction [expr e₁] [] ["with", ident n₁, ident a₁, ident x₁, ident n₁, ident b₁, ident A₁, ident B₁] ["generalizing", ident e₂]; simp ["!"] [] [] [] [] [],
  { rcases [expr cs₁, "with", "⟨", ident n₁, ",", ident rfl, "⟩"],
    simpa [] [] [] ["[", expr mul_comm, "]"] [] ["using", expr cseval_mul_const t n₁ cs₂] },
  induction [expr e₂] [] ["with", ident n₂, ident a₂, ident x₂, ident n₂, ident b₂, ident A₂, ident B₂] [],
  { rcases [expr cs₂, "with", "⟨", ident n₂, ",", ident rfl, "⟩"],
    simpa ["!"] [] [] [] [] ["using", expr cseval_mul_const t n₂ cs₁] },
  cases [expr cs₁] ["with", ident csa₁, ident csb₁],
  cases [expr id cs₂] ["with", ident csa₂, ident csb₂],
  simp ["!"] [] [] [] [] [],
  have [ident C] [] [":=", expr pos_num.cmp_to_nat x₁ x₂],
  cases [expr A₂ csa₂] ["with", ident csA₂, ident hA₂],
  cases [expr pos_num.cmp x₁ x₂] []; simp ["!"] [] [] [] [] [],
  { simp [] [] [] ["[", expr A₁ csa₁ cs₂, ",", expr B₁ csb₁ cs₂, "]"] [] [],
    symmetry,
    apply [expr tactic.ring.horner_mul_const]; refl },
  { cases [expr cseval_horner' t _ x₁ n₂ 0 csA₂ ⟨0, rfl⟩] ["with", ident csh₁, ident h₁],
    cases [expr C] [],
    split_ifs [] [],
    { subst [expr b₂],
      refine [expr ⟨csh₁, h₁.trans (eq.symm _)⟩],
      apply [expr tactic.ring.horner_mul_horner_zero]; try { refl },
      simp ["!"] [] [] ["[", expr hA₂, "]"] [] [] },
    { cases [expr A₁ csa₁ csb₂] ["with", ident csA₁, ident hA₁],
      cases [expr cseval_add t csh₁ _] ["with", ident csh₂, ident h₂],
      { refine [expr ⟨csh₂, h₂.trans (eq.symm _)⟩],
        apply [expr tactic.ring.horner_mul_horner]; try { refl },
        simp ["!"] [] [] ["*"] [] [] },
      exact [expr ⟨csA₁, (B₁ csb₁ csb₂).1⟩] } },
  { simp [] [] [] ["[", expr A₂ csa₂, ",", expr B₂ csb₂, "]"] [] [],
    rw ["[", expr mul_comm, ",", expr eq_comm, "]"] [],
    apply [expr tactic.ring.horner_const_mul],
    { apply [expr mul_comm] },
    { refl } }
end

theorem cseval_pow {α} [CommSemiringₓ α] (t : Tree α) {x : horner_expr} (cs : x.is_cs) :
  ∀ n : Num, (pow x n).IsCs ∧ cseval t (pow x n) = cseval t x ^ (n : ℕ)
| 0 => ⟨⟨1, rfl⟩, (pow_zeroₓ _).symm⟩
| Num.pos p =>
  by 
    simp [pow]
    induction' p with p ep p ep
    ·
      simp 
    ·
      simp [pow_bit1]
      cases' cseval_mul t ep.1 ep.1 with cs₀ h₀ 
      cases' cseval_mul t cs₀ cs with cs₁ h₁ 
      simp 
    ·
      simp [pow_bit0]
      cases' cseval_mul t ep.1 ep.1 with cs₀ h₀ 
      simp 

/-- For any given tree `t` of atoms and any reflected expression `r`,
the Horner form of `r` is a valid csring expression, and under `t`,
the Horner form evaluates to the same thing as `r`. -/
theorem cseval_of_csexpr {α} [CommSemiringₓ α] (t : Tree α) :
  ∀ r : csring_expr, (of_csexpr r).IsCs ∧ cseval t (of_csexpr r) = r.eval t
| csring_expr.atom n => cseval_atom _ _
| csring_expr.const n =>
  ⟨⟨n, rfl⟩,
    by 
      cases n <;> rfl⟩
| csring_expr.add x y =>
  let ⟨cs₁, h₁⟩ := cseval_of_csexpr x 
  let ⟨cs₂, h₂⟩ := cseval_of_csexpr y 
  let ⟨cs, h⟩ := cseval_add t cs₁ cs₂
  ⟨cs,
    by 
      simp [h]⟩
| csring_expr.mul x y =>
  let ⟨cs₁, h₁⟩ := cseval_of_csexpr x 
  let ⟨cs₂, h₂⟩ := cseval_of_csexpr y 
  let ⟨cs, h⟩ := cseval_mul t cs₁ cs₂
  ⟨cs,
    by 
      simp [h]⟩
| csring_expr.pow x n =>
  let ⟨cs, h⟩ := cseval_of_csexpr x 
  let ⟨cs, h⟩ := cseval_pow t cs n
  ⟨cs,
    by 
      simp [h]⟩

end HornerExpr

/-- The main proof-by-reflection theorem. Given reflected csring expressions
`r₁` and `r₂` plus a storage `t` of atoms, if both expressions go to the
same Horner normal form, then the original non-reflected expressions are
equal. `H` follows from kernel reduction and is therefore `rfl`. -/
theorem correctness {α} [CommSemiringₓ α] (t : Tree α) (r₁ r₂ : csring_expr)
  (H : horner_expr.of_csexpr r₁ = horner_expr.of_csexpr r₂) : r₁.eval t = r₂.eval t :=
  by 
    repeat' 
        rw [←(horner_expr.cseval_of_csexpr t _).2] <;>
      rw [H]

/-- Reflects a csring expression into a `csring_expr`, together
with a dlist of atoms, i.e. opaque variables over which the
expression is a polynomial. -/
unsafe def reflect_expr : expr → csring_expr × Dlist expr
| quote.1 ((%%ₓe₁)+%%ₓe₂) =>
  let (r₁, l₁) := reflect_expr e₁ 
  let (r₂, l₂) := reflect_expr e₂
  (r₁.add r₂, l₁ ++ l₂)
| quote.1 ((%%ₓe₁)*%%ₓe₂) =>
  let (r₁, l₁) := reflect_expr e₁ 
  let (r₂, l₂) := reflect_expr e₂
  (r₁.mul r₂, l₁ ++ l₂)
| e@(quote.1 ((%%ₓe₁) ^ %%ₓe₂)) =>
  match reflect_expr e₁, expr.to_nat e₂ with 
  | (r₁, l₁), some n₂ => (r₁.pow (Num.ofNat' n₂), l₁)
  | (r₁, l₁), none => (csring_expr.atom 1, Dlist.singleton e)
| e =>
  match expr.to_nat e with 
  | some n => (csring_expr.const (Num.ofNat' n), Dlist.empty)
  | none => (csring_expr.atom 1, Dlist.singleton e)

/-- In the output of `reflect_expr`, `atom`s are initialized with incorrect indices.
The indices cannot be computed until the whole tree is built, so another pass over
the expressions is needed - this is what `replace` does. The computation (expressed
in the state monad) fixes up `atom`s to match their positions in the atom tree.
The initial state is a list of all atom occurrences in the goal, left-to-right. -/
unsafe def csring_expr.replace (t : Tree expr) : csring_expr → StateTₓ (List expr) Option csring_expr
| csring_expr.atom _ =>
  do 
    let e ← get 
    let p ← monad_lift (t.index_of (· < ·) e.head)
    put e.tail 
    pure (csring_expr.atom p)
| csring_expr.const n => pure (csring_expr.const n)
| csring_expr.add x y => (csring_expr.add <$> x.replace)<*>y.replace
| csring_expr.mul x y => (csring_expr.mul <$> x.replace)<*>y.replace
| csring_expr.pow x n => (fun x => csring_expr.pow x n) <$> x.replace

end Tactic.Ring2

namespace Tactic

namespace Interactive

open Interactive Interactive.Types Lean.Parser

open Tactic.Ring2

local postfix:9001 "?" => optionalₓ

/-- `ring2` solves equations in the language of rings.

It supports only the commutative semiring operations, i.e. it does not normalize subtraction or
division.

  This variant on the `ring` tactic uses kernel computation instead
  of proof generation. In general, you should use `ring` instead of `ring2`. -/
unsafe def ring2 : tactic Unit :=
  do 
    sorry 
    let quote.1 ((%%ₓe₁) = %%ₓe₂) ← target | fail "ring2 tactic failed: the goal is not an equality"
    let α ← infer_type e₁ 
    let expr.sort (level.succ u) ← infer_type α 
    let (r₁, l₁) := reflect_expr e₁ 
    let (r₂, l₂) := reflect_expr e₂ 
    let L := (l₁ ++ l₂).toList 
    let s := Tree.ofRbnode (rbtreeOf L).1
    let (r₁, L) ← (StateTₓ.run (r₁.replace s) L : Option _)
    let (r₂, _) ← (StateTₓ.run (r₂.replace s) L : Option _)
    let se : expr := s.reflect' u α 
    let er₁ : expr := reflect r₁ 
    let er₂ : expr := reflect r₂ 
    let cs ← mk_app `` CommSemiringₓ [α] >>= mk_instance 
    let e ←
      to_expr (pquote.1 (correctness (%%ₓse) (%%ₓer₁) (%%ₓer₂) rfl)) <|>
          fail
            ("ring2 tactic failed, cannot show equality:\n" ++ toString (horner_expr.of_csexpr r₁) ++ "\n  =?=\n" ++
              toString (horner_expr.of_csexpr r₂))
    tactic.exact e

add_tactic_doc
  { Name := "ring2", category := DocCategory.tactic, declNames := [`tactic.interactive.ring2],
    tags := ["arithmetic", "simplification", "decision procedure"] }

end Interactive

end Tactic

namespace Conv.Interactive

open Conv

unsafe def ring2 : conv Unit :=
  discharge_eq_lhs tactic.interactive.ring2

end Conv.Interactive

