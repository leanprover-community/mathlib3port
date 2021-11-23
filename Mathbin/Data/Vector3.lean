import Mathbin.Data.Fin.Fin2 
import Mathbin.Tactic.Localized

/-!
# Alternate definition of `vector` in terms of `fin2`

This file provides a locale `vector3` which overrides `[a, b, c]` notation to create `vector3` not
`list`.

The `::` notation is overloaded by this file to mean `vector3.cons`.
-/


universe u

open Fin2 Nat

/-- Alternate definition of `vector` based on `fin2`. -/
def Vector3 (α : Type u) (n : ℕ) : Type u :=
  Fin2 n → α

namespace Vector3

/-- The empty vector -/
@[matchPattern]
def nil {α} : Vector3 α 0 :=
  fun.

/-- The vector cons operation -/
@[matchPattern]
def cons {α} {n} (a : α) (v : Vector3 α n) : Vector3 α (succ n) :=
  fun i =>
    by 
      refine' i.cases' _ _ 
      exact a 
      exact v

-- error in Data.Vector3: ././Mathport/Syntax/Translate/Basic.lean:1266:43: in localized: ././Mathport/Syntax/Translate/Basic.lean:1096:9: unsupported: advanced notation (l:(foldr `, ` (h t, vector3.cons h t) nil `]`))
localized [expr "notation `[` l:(foldr `, ` (h t, vector3.cons h t) nil `]`) := l", [command <some 0>], "in", ident vector3]

@[simp]
theorem cons_fz {α} {n} (a : α) (v : Vector3 α n) : (a :: v) fz = a :=
  rfl

@[simp]
theorem cons_fs {α} {n} (a : α) (v : Vector3 α n) i : (a :: v) (fs i) = v i :=
  rfl

/-- Get the `i`th element of a vector -/
@[reducible]
def nth {α} {n} (i : Fin2 n) (v : Vector3 α n) : α :=
  v i

/-- Construct a vector from a function on `fin2`. -/
@[reducible]
def of_fn {α} {n} (f : Fin2 n → α) : Vector3 α n :=
  f

/-- Get the head of a nonempty vector. -/
def head {α} {n} (v : Vector3 α (succ n)) : α :=
  v fz

/-- Get the tail of a nonempty vector. -/
def tail {α} {n} (v : Vector3 α (succ n)) : Vector3 α n :=
  fun i => v (fs i)

theorem eq_nil {α} (v : Vector3 α 0) : v = [] :=
  funext$ fun i => nomatch i

theorem cons_head_tail {α} {n} (v : Vector3 α (succ n)) : head v :: tail v = v :=
  funext$ fun i => Fin2.cases' rfl (fun _ => rfl) i

def nil_elim {α} {C : Vector3 α 0 → Sort u} (H : C []) (v : Vector3 α 0) : C v :=
  by 
    rw [eq_nil v] <;> apply H

def cons_elim {α n} {C : Vector3 α (succ n) → Sort u} (H : ∀ a : α t : Vector3 α n, C (a :: t))
  (v : Vector3 α (succ n)) : C v :=
  by 
    rw [←cons_head_tail v] <;> apply H

@[simp]
theorem cons_elim_cons {α n C H a t} : @cons_elim α n C H (a :: t) = H a t :=
  rfl

@[elab_as_eliminator]
protected def rec_on {α} {C : ∀ {n}, Vector3 α n → Sort u} {n} (v : Vector3 α n) (H0 : C [])
  (Hs : ∀ {n} a w : Vector3 α n, C w → C (a :: w)) : C v :=
  Nat.recOn n (fun v => v.nil_elim H0) (fun n IH v => v.cons_elim fun a t => Hs _ _ (IH _)) v

@[simp]
theorem rec_on_nil {α C H0 Hs} : @Vector3.recOn α (@C) 0 [] H0 @Hs = H0 :=
  rfl

@[simp]
theorem rec_on_cons {α C H0 Hs n a v} :
  @Vector3.recOn α (@C) (succ n) (a :: v) H0 @Hs = Hs a v (@Vector3.recOn α (@C) n v H0 @Hs) :=
  rfl

/-- Append two vectors -/
def append {α} {m} (v : Vector3 α m) {n} (w : Vector3 α n) : Vector3 α (n+m) :=
  Nat.recOn m (fun _ => w) (fun m IH v => v.cons_elim$ fun a t => @Fin2.cases' (n+m) (fun _ => α) a (IH t)) v

local infixl:65 " +-+ " => Vector3.append

@[simp]
theorem append_nil {α} {n} (w : Vector3 α n) : [] +-+ w = w :=
  rfl

@[simp]
theorem append_cons {α} (a : α) {m} (v : Vector3 α m) {n} (w : Vector3 α n) : a :: v +-+ w = a :: (v +-+ w) :=
  rfl

@[simp]
theorem append_left {α} : ∀ {m} i : Fin2 m v : Vector3 α m {n} w : Vector3 α n, (v +-+ w) (left n i) = v i
| _, @fz m, v, n, w =>
  v.cons_elim
    fun a t =>
      by 
        simp [left]
| _, @fs m i, v, n, w =>
  v.cons_elim
    fun a t =>
      by 
        simp [left]

@[simp]
theorem append_add {α} : ∀ {m} v : Vector3 α m {n} w : Vector3 α n i : Fin2 n, (v +-+ w) (add i m) = w i
| 0, v, n, w, i => rfl
| succ m, v, n, w, i =>
  v.cons_elim
    fun a t =>
      by 
        simp [add]

/-- Insert `a` into `v` at index `i`. -/
def insert {α} (a : α) {n} (v : Vector3 α n) (i : Fin2 (succ n)) : Vector3 α (succ n) :=
  fun j => (a :: v) (insert_perm i j)

@[simp]
theorem insert_fz {α} (a : α) {n} (v : Vector3 α n) : insert a v fz = a :: v :=
  by 
    refine' funext fun j => j.cases' _ _ <;> intros  <;> rfl

@[simp]
theorem insert_fs {α} (a : α) {n} (b : α) (v : Vector3 α n) (i : Fin2 (succ n)) :
  insert a (b :: v) (fs i) = b :: insert a v i :=
  funext$
    fun j =>
      by 
        refine' j.cases' _ fun j => _ <;> simp [insert, insert_perm]
        refine' Fin2.cases' _ _ (insert_perm i j) <;> simp [insert_perm]

-- error in Data.Vector3: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem append_insert
{α}
(a : α)
{k}
(t : vector3 α k)
{n}
(v : vector3 α n)
(i : fin2 (succ n))
(e : «expr = »(«expr + »(succ n, k), succ «expr + »(n, k))) : «expr = »(insert a «expr +-+ »(t, v) (eq.rec_on e (i.add k)), eq.rec_on e «expr +-+ »(t, insert a v i)) :=
begin
  refine [expr vector3.rec_on t (λ e, _) (λ k b t IH e, _) e],
  refl,
  have [ident e'] [] [":=", expr succ_add n k],
  change [expr «expr = »(insert a [«expr :: »/«expr :: »](b, «expr +-+ »(t, v)) (eq.rec_on (congr_arg succ e') (fs (add i k))), eq.rec_on (congr_arg succ e') [«expr :: »/«expr :: »](b, «expr +-+ »(t, insert a v i)))] [] [],
  rw ["<-", expr (eq.drec_on e' rfl : «expr = »(fs (eq.rec_on e' (i.add k) : fin2 (succ «expr + »(n, k))), eq.rec_on (congr_arg succ e') (fs (i.add k))))] [],
  simp [] [] [] [] [] [],
  rw [expr IH] [],
  exact [expr eq.drec_on e' rfl]
end

end Vector3

section Vector3

open Vector3

open_locale Vector3

/-- "Curried" exists, i.e. ∃ x1 ... xn, f [x1, ..., xn] -/
def VectorEx {α} : ∀ k, (Vector3 α k → Prop) → Prop
| 0, f => f []
| succ k, f => ∃ x : α, VectorEx k fun v => f (x :: v)

/-- "Curried" forall, i.e. ∀ x1 ... xn, f [x1, ..., xn] -/
def VectorAll {α} : ∀ k, (Vector3 α k → Prop) → Prop
| 0, f => f []
| succ k, f => ∀ x : α, VectorAll k fun v => f (x :: v)

theorem exists_vector_zero {α} (f : Vector3 α 0 → Prop) : Exists f ↔ f [] :=
  ⟨fun ⟨v, fv⟩ =>
      by 
        rw [←eq_nil v] <;> exact fv,
    fun f0 => ⟨[], f0⟩⟩

theorem exists_vector_succ {α n} (f : Vector3 α (succ n) → Prop) : Exists f ↔ ∃ x v, f (x :: v) :=
  ⟨fun ⟨v, fv⟩ =>
      ⟨_, _,
        by 
          rw [cons_head_tail v] <;> exact fv⟩,
    fun ⟨x, v, fxv⟩ => ⟨_, fxv⟩⟩

theorem vector_ex_iff_exists {α} : ∀ {n} f : Vector3 α n → Prop, VectorEx n f ↔ Exists f
| 0, f => (exists_vector_zero f).symm
| succ n, f => Iff.trans (exists_congr fun x => vector_ex_iff_exists _) (exists_vector_succ f).symm

theorem vector_all_iff_forall {α} : ∀ {n} f : Vector3 α n → Prop, VectorAll n f ↔ ∀ v, f v
| 0, f => ⟨fun f0 v => v.nil_elim f0, fun al => al []⟩
| succ n, f =>
  (forall_congrₓ fun x => vector_all_iff_forall fun v => f (x :: v)).trans
    ⟨fun al v => v.cons_elim al, fun al x v => al (x :: v)⟩

/-- `vector_allp p v` is equivalent to `∀ i, p (v i)`, but unfolds directly to a conjunction,
  i.e. `vector_allp p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
def VectorAllp {α} (p : α → Prop) {n} (v : Vector3 α n) : Prop :=
  Vector3.recOn v True fun n a v IH => @Vector3.recOn _ (fun n v => Prop) _ v (p a) fun n b v' _ => p a ∧ IH

@[simp]
theorem vector_allp_nil {α} (p : α → Prop) : VectorAllp p [] = True :=
  rfl

@[simp]
theorem vector_allp_singleton {α} (p : α → Prop) (x : α) : VectorAllp p [x] = p x :=
  rfl

@[simp]
theorem vector_allp_cons {α} (p : α → Prop) {n} (x : α) (v : Vector3 α n) :
  VectorAllp p (x :: v) ↔ p x ∧ VectorAllp p v :=
  Vector3.recOn v (and_trueₓ _).symm fun n a v IH => Iff.rfl

-- error in Data.Vector3: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem vector_allp_iff_forall
{α}
(p : α → exprProp())
{n}
(v : vector3 α n) : «expr ↔ »(vector_allp p v, ∀ i, p (v i)) :=
begin
  refine [expr v.rec_on _ _],
  { exact [expr ⟨λ _, fin2.elim0, λ _, trivial⟩] },
  { simp [] [] [] [] [] [],
    refine [expr λ
     n
     a
     v
     IH, (and_congr_right (λ
       _, IH)).trans ⟨λ ⟨pa, h⟩ (i), by { refine [expr i.cases' _ _],
        exacts ["[", expr pa, ",", expr h, "]"] }, λ h, ⟨_, λ i, _⟩⟩],
    { have [ident h0] [] [":=", expr h fz],
      simp [] [] [] [] [] ["at", ident h0],
      exact [expr h0] },
    { have [ident hs] [] [":=", expr h (fs i)],
      simp [] [] [] [] [] ["at", ident hs],
      exact [expr hs] } }
end

theorem VectorAllp.imp {α} {p q : α → Prop} (h : ∀ x, p x → q x) {n} {v : Vector3 α n} (al : VectorAllp p v) :
  VectorAllp q v :=
  (vector_allp_iff_forall _ _).2 fun i => h _$ (vector_allp_iff_forall _ _).1 al _

end Vector3

