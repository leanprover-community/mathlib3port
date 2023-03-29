/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module computability.primrec
! leanprover-community/mathlib commit 959c3b69db8a8b404d5813421f2e6ca8660d19e5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Equiv.Array
import Mathbin.Logic.Equiv.List
import Mathbin.Logic.Function.Iterate

/-!
# The primitive recursive functions

The primitive recursive functions are the least collection of functions
`nat → nat` which are closed under projections (using the mkpair
pairing function), composition, zero, successor, and primitive recursion
(i.e. nat.rec where the motive is C n := nat).

We can extend this definition to a large class of basic types by
using canonical encodings of types as natural numbers (Gödel numbering),
which we implement through the type class `encodable`. (More precisely,
we need that the composition of encode with decode yields a
primitive recursive function, so we have the `primcodable` type class
for this.)

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/


open Denumerable Encodable Function

namespace Nat

/- warning: nat.elim -> Nat.rec is a dubious translation:
lean 3 declaration is
  forall {C : Sort.{u1}}, C -> (Nat -> C -> C) -> Nat -> C
but is expected to have type
  forall {C : Nat -> Sort.{u1}}, (C Nat.zero) -> (forall (ᾰ : Nat), (C ᾰ) -> (C (Nat.succ ᾰ))) -> (forall (ᾰ : Nat), C ᾰ)
Case conversion may be inaccurate. Consider using '#align nat.elim Nat.recₓ'. -/
/-- The non-dependent recursor on naturals. -/
def rec {C : Sort _} : C → (ℕ → C → C) → ℕ → C :=
  @Nat.rec fun _ => C
#align nat.elim Nat.rec

/- warning: nat.elim_zero clashes with nat.rec_zero -> Nat.rec_zero
warning: nat.elim_zero -> Nat.rec_zero is a dubious translation:
lean 3 declaration is
  forall {C : Sort.{u1}} (a : C) (f : Nat -> C -> C), Eq.{u1} C (Nat.rec.{u1} C a f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) a
but is expected to have type
  forall {C : Nat -> Sort.{u1}} (a : C (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (f : forall (ᾰ : Nat), (C ᾰ) -> (C (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) ᾰ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))), Eq.{u1} (C (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) ((fun (t : Nat) => Nat.rec.{u1} (fun (x._@.Mathlib.Data.Nat.Basic._hyg.2994 : Nat) => C x._@.Mathlib.Data.Nat.Basic._hyg.2994) a f t) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) a
Case conversion may be inaccurate. Consider using '#align nat.elim_zero Nat.rec_zeroₓ'. -/
@[simp]
theorem rec_zero {C} (a f) : @Nat.rec C a f 0 = a :=
  rfl
#align nat.elim_zero Nat.rec_zero

/- warning: nat.elim_succ clashes with nat.rec_add_one -> Nat.rec_add_one
warning: nat.elim_succ -> Nat.rec_add_one is a dubious translation:
lean 3 declaration is
  forall {C : Sort.{u1}} (a : C) (f : Nat -> C -> C) (n : Nat), Eq.{u1} C (Nat.rec.{u1} C a f (Nat.succ n)) (f n (Nat.rec.{u1} C a f n))
but is expected to have type
  forall {C : Nat -> Sort.{u1}} (a : C (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (f : forall (ᾰ : Nat), (C ᾰ) -> (C (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) ᾰ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (n : Nat), Eq.{u1} (C (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) ((fun (t : Nat) => Nat.rec.{u1} (fun (x._@.Mathlib.Data.Nat.Basic._hyg.3047 : Nat) => C x._@.Mathlib.Data.Nat.Basic._hyg.3047) a f t) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (f n ((fun (t : Nat) => Nat.rec.{u1} (fun (x._@.Mathlib.Data.Nat.Basic._hyg.3070 : Nat) => C x._@.Mathlib.Data.Nat.Basic._hyg.3070) a f t) n))
Case conversion may be inaccurate. Consider using '#align nat.elim_succ Nat.rec_add_oneₓ'. -/
@[simp]
theorem rec_add_one {C} (a f n) : @Nat.rec C a f (succ n) = f n (Nat.rec a f n) :=
  rfl
#align nat.elim_succ Nat.rec_add_one

/- warning: nat.cases -> Nat.casesOn is a dubious translation:
lean 3 declaration is
  forall {C : Sort.{u1}}, C -> (Nat -> C) -> Nat -> C
but is expected to have type
  forall {C : Nat -> Sort.{u1}} (a : Nat), (C Nat.zero) -> (forall (n : Nat), C (Nat.succ n)) -> (C a)
Case conversion may be inaccurate. Consider using '#align nat.cases Nat.casesOnₓ'. -/
/-- Cases on whether the input is 0 or a successor. -/
def casesOn {C : Sort _} (a : C) (f : ℕ → C) : ℕ → C :=
  Nat.rec a fun n _ => f n
#align nat.cases Nat.casesOn

/- warning: nat.cases_zero clashes with nat.rec_zero -> Nat.rec_zero
warning: nat.cases_zero -> Nat.rec_zero is a dubious translation:
lean 3 declaration is
  forall {C : Sort.{u1}} (a : C) (f : Nat -> C), Eq.{u1} C (Nat.casesOn.{u1} C a f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) a
but is expected to have type
  forall {C : Nat -> Sort.{u1}} (a : C (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (f : forall (ᾰ : Nat), (C ᾰ) -> (C (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) ᾰ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))), Eq.{u1} (C (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) ((fun (t : Nat) => Nat.rec.{u1} (fun (x._@.Mathlib.Data.Nat.Basic._hyg.2994 : Nat) => C x._@.Mathlib.Data.Nat.Basic._hyg.2994) a f t) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) a
Case conversion may be inaccurate. Consider using '#align nat.cases_zero Nat.rec_zeroₓ'. -/
@[simp]
theorem rec_zero {C} (a f) : @Nat.casesOn C a f 0 = a :=
  rfl
#align nat.cases_zero Nat.rec_zero

/- warning: nat.cases_succ clashes with nat.rec_add_one -> Nat.rec_add_one
warning: nat.cases_succ -> Nat.rec_add_one is a dubious translation:
lean 3 declaration is
  forall {C : Sort.{u1}} (a : C) (f : Nat -> C) (n : Nat), Eq.{u1} C (Nat.casesOn.{u1} C a f (Nat.succ n)) (f n)
but is expected to have type
  forall {C : Nat -> Sort.{u1}} (a : C (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (f : forall (ᾰ : Nat), (C ᾰ) -> (C (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) ᾰ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (n : Nat), Eq.{u1} (C (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) ((fun (t : Nat) => Nat.rec.{u1} (fun (x._@.Mathlib.Data.Nat.Basic._hyg.3047 : Nat) => C x._@.Mathlib.Data.Nat.Basic._hyg.3047) a f t) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (f n ((fun (t : Nat) => Nat.rec.{u1} (fun (x._@.Mathlib.Data.Nat.Basic._hyg.3070 : Nat) => C x._@.Mathlib.Data.Nat.Basic._hyg.3070) a f t) n))
Case conversion may be inaccurate. Consider using '#align nat.cases_succ Nat.rec_add_oneₓ'. -/
@[simp]
theorem rec_add_one {C} (a f n) : @Nat.casesOn C a f (succ n) = f n :=
  rfl
#align nat.cases_succ Nat.rec_add_one

#print Nat.unpaired /-
/-- Calls the given function on a pair of entries `n`, encoded via the pairing function. -/
@[simp, reducible]
def unpaired {α} (f : ℕ → ℕ → α) (n : ℕ) : α :=
  f n.unpair.1 n.unpair.2
#align nat.unpaired Nat.unpaired
-/

#print Nat.Primrec /-
/-- The primitive recursive functions `ℕ → ℕ`. -/
inductive Primrec : (ℕ → ℕ) → Prop
  | zero : Primrec fun n => 0
  | succ : Primrec succ
  | left : Primrec fun n => n.unpair.1
  | right : Primrec fun n => n.unpair.2
  | pair {f g} : Primrec f → Primrec g → Primrec fun n => pair (f n) (g n)
  | comp {f g} : Primrec f → Primrec g → Primrec fun n => f (g n)
  |
  prec {f g} :
    Primrec f →
      Primrec g → Primrec (unpaired fun z n => n.elim (f z) fun y IH => g <| pair z <| pair y IH)
#align nat.primrec Nat.Primrec
-/

namespace Primrec

#print Nat.Primrec.of_eq /-
theorem of_eq {f g : ℕ → ℕ} (hf : Primrec f) (H : ∀ n, f n = g n) : Primrec g :=
  (funext H : f = g) ▸ hf
#align nat.primrec.of_eq Nat.Primrec.of_eq
-/

#print Nat.Primrec.const /-
theorem const : ∀ n : ℕ, Primrec fun _ => n
  | 0 => zero
  | n + 1 => succ.comp (const n)
#align nat.primrec.const Nat.Primrec.const
-/

#print Nat.Primrec.id /-
protected theorem id : Primrec id :=
  (left.pair right).of_eq fun n => by simp
#align nat.primrec.id Nat.Primrec.id
-/

#print Nat.Primrec.prec1 /-
theorem prec1 {f} (m : ℕ) (hf : Primrec f) : Primrec fun n => n.elim m fun y IH => f <| pair y IH :=
  ((prec (const m) (hf.comp right)).comp (zero.pair Primrec.id)).of_eq fun n => by simp
#align nat.primrec.prec1 Nat.Primrec.prec1
-/

#print Nat.Primrec.cases1 /-
theorem cases1 {f} (m : ℕ) (hf : Primrec f) : Primrec (Nat.casesOn m f) :=
  (prec1 m (hf.comp left)).of_eq <| by simp [cases]
#align nat.primrec.cases1 Nat.Primrec.cases1
-/

#print Nat.Primrec.cases /-
theorem cases {f g} (hf : Primrec f) (hg : Primrec g) :
    Primrec (unpaired fun z n => n.cases (f z) fun y => g <| pair z y) :=
  (prec hf (hg.comp (pair left (left.comp right)))).of_eq <| by simp [cases]
#align nat.primrec.cases Nat.Primrec.cases
-/

#print Nat.Primrec.swap /-
protected theorem swap : Primrec (unpaired (swap pair)) :=
  (pair right left).of_eq fun n => by simp
#align nat.primrec.swap Nat.Primrec.swap
-/

#print Nat.Primrec.swap' /-
theorem swap' {f} (hf : Primrec (unpaired f)) : Primrec (unpaired (swap f)) :=
  (hf.comp Primrec.swap).of_eq fun n => by simp
#align nat.primrec.swap' Nat.Primrec.swap'
-/

#print Nat.Primrec.pred /-
theorem pred : Primrec pred :=
  (cases1 0 Primrec.id).of_eq fun n => by cases n <;> simp [*]
#align nat.primrec.pred Nat.Primrec.pred
-/

#print Nat.Primrec.add /-
theorem add : Primrec (unpaired (· + ·)) :=
  (prec Primrec.id ((succ.comp right).comp right)).of_eq fun p => by
    simp <;> induction p.unpair.2 <;> simp [*, -add_comm, add_succ]
#align nat.primrec.add Nat.Primrec.add
-/

#print Nat.Primrec.sub /-
theorem sub : Primrec (unpaired Sub.sub) :=
  (prec Primrec.id ((pred.comp right).comp right)).of_eq fun p => by
    simp <;> induction p.unpair.2 <;> simp [*, -add_comm, sub_succ]
#align nat.primrec.sub Nat.Primrec.sub
-/

#print Nat.Primrec.mul /-
theorem mul : Primrec (unpaired (· * ·)) :=
  (prec zero (add.comp (pair left (right.comp right)))).of_eq fun p => by
    simp <;> induction p.unpair.2 <;> simp [*, mul_succ, add_comm]
#align nat.primrec.mul Nat.Primrec.mul
-/

#print Nat.Primrec.pow /-
theorem pow : Primrec (unpaired (· ^ ·)) :=
  (prec (const 1) (mul.comp (pair (right.comp right) left))).of_eq fun p => by
    simp <;> induction p.unpair.2 <;> simp [*, pow_succ']
#align nat.primrec.pow Nat.Primrec.pow
-/

end Primrec

end Nat

#print Primcodable /-
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`prim] [] -/
/-- A `primcodable` type is an `encodable` type for which
  the encode/decode functions are primitive recursive. -/
class Primcodable (α : Type _) extends Encodable α where
  prim : Nat.Primrec fun n => Encodable.encode (decode n)
#align primcodable Primcodable
-/

namespace Primcodable

open Nat.Primrec

#print Primcodable.ofDenumerable /-
instance (priority := 10) ofDenumerable (α) [Denumerable α] : Primcodable α :=
  ⟨succ.of_eq <| by simp⟩
#align primcodable.of_denumerable Primcodable.ofDenumerable
-/

#print Primcodable.ofEquiv /-
/-- Builds a `primcodable` instance from an equivalence to a `primcodable` type. -/
def ofEquiv (α) {β} [Primcodable α] (e : β ≃ α) : Primcodable β :=
  { Encodable.ofEquiv α e with
    prim :=
      (Primcodable.prim α).of_eq fun n =>
        show
          encode (decode α n) =
            (Option.casesOn (Option.map e.symm (decode α n)) 0 fun a => Nat.succ (encode (e a)) : ℕ)
          by cases decode α n <;> dsimp <;> simp }
#align primcodable.of_equiv Primcodable.ofEquiv
-/

#print Primcodable.empty /-
instance empty : Primcodable Empty :=
  ⟨zero⟩
#align primcodable.empty Primcodable.empty
-/

#print Primcodable.unit /-
instance unit : Primcodable PUnit :=
  ⟨(cases1 1 zero).of_eq fun n => by cases n <;> simp⟩
#align primcodable.unit Primcodable.unit
-/

#print Primcodable.option /-
instance option {α : Type _} [h : Primcodable α] : Primcodable (Option α) :=
  ⟨(cases1 1 ((cases1 0 (succ.comp succ)).comp (Primcodable.prim α))).of_eq fun n => by
      cases n <;> simp <;> cases decode α n <;> rfl⟩
#align primcodable.option Primcodable.option
-/

#print Primcodable.bool /-
instance bool : Primcodable Bool :=
  ⟨(cases1 1 (cases1 2 zero)).of_eq fun n => by
      cases n; · rfl; cases n; · rfl
      rw [decode_ge_two]; · rfl
      exact by decide⟩
#align primcodable.bool Primcodable.bool
-/

end Primcodable

#print Primrec /-
/-- `primrec f` means `f` is primitive recursive (after
  encoding its input and output as natural numbers). -/
def Primrec {α β} [Primcodable α] [Primcodable β] (f : α → β) : Prop :=
  Nat.Primrec fun n => encode ((decode α n).map f)
#align primrec Primrec
-/

namespace Primrec

variable {α : Type _} {β : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Nat.Primrec

#print Primrec.encode /-
protected theorem encode : Primrec (@encode α _) :=
  (Primcodable.prim α).of_eq fun n => by cases decode α n <;> rfl
#align primrec.encode Primrec.encode
-/

#print Primrec.decode /-
protected theorem decode : Primrec (decode α) :=
  succ.comp (Primcodable.prim α)
#align primrec.decode Primrec.decode
-/

/- warning: primrec.dom_denumerable -> Primrec.dom_denumerable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_4 : Denumerable.{u1} α] [_inst_5 : Primcodable.{u2} β] {f : α -> β}, Iff (Primrec.{u1, u2} α β (Primcodable.ofDenumerable.{u1} α _inst_4) _inst_5 f) (Nat.Primrec (fun (n : Nat) => Encodable.encode.{u2} β (Primcodable.toEncodable.{u2} β _inst_5) (f (Denumerable.ofNat.{u1} α _inst_4 n))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : Denumerable.{u2} α] [_inst_5 : Primcodable.{u1} β] {f : α -> β}, Iff (Primrec.{u2, u1} α β (Primcodable.ofDenumerable.{u2} α _inst_4) _inst_5 f) (Nat.Primrec (fun (n : Nat) => Encodable.encode.{u1} β (Primcodable.toEncodable.{u1} β _inst_5) (f (Denumerable.ofNat.{u2} α _inst_4 n))))
Case conversion may be inaccurate. Consider using '#align primrec.dom_denumerable Primrec.dom_denumerableₓ'. -/
theorem dom_denumerable {α β} [Denumerable α] [Primcodable β] {f : α → β} :
    Primrec f ↔ Nat.Primrec fun n => encode (f (ofNat α n)) :=
  ⟨fun h => (pred.comp h).of_eq fun n => by simp <;> rfl, fun h =>
    (succ.comp h).of_eq fun n => by simp <;> rfl⟩
#align primrec.dom_denumerable Primrec.dom_denumerable

#print Primrec.nat_iff /-
theorem nat_iff {f : ℕ → ℕ} : Primrec f ↔ Nat.Primrec f :=
  dom_denumerable
#align primrec.nat_iff Primrec.nat_iff
-/

#print Primrec.encdec /-
theorem encdec : Primrec fun n => encode (decode α n) :=
  nat_iff.2 (Primcodable.prim α)
#align primrec.encdec Primrec.encdec
-/

#print Primrec.option_some /-
theorem option_some : Primrec (@some α) :=
  ((cases1 0 (succ.comp succ)).comp (Primcodable.prim α)).of_eq fun n => by
    cases decode α n <;> simp
#align primrec.option_some Primrec.option_some
-/

/- warning: primrec.of_eq -> Primrec.of_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_3 : Primcodable.{u2} σ] {f : α -> σ} {g : α -> σ}, (Primrec.{u1, u2} α σ _inst_1 _inst_3 f) -> (forall (n : α), Eq.{succ u2} σ (f n) (g n)) -> (Primrec.{u1, u2} α σ _inst_1 _inst_3 g)
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_3 : Primcodable.{u1} σ] {f : α -> σ} {g : α -> σ}, (Primrec.{u2, u1} α σ _inst_1 _inst_3 f) -> (forall (n : α), Eq.{succ u1} σ (f n) (g n)) -> (Primrec.{u2, u1} α σ _inst_1 _inst_3 g)
Case conversion may be inaccurate. Consider using '#align primrec.of_eq Primrec.of_eqₓ'. -/
theorem of_eq {f g : α → σ} (hf : Primrec f) (H : ∀ n, f n = g n) : Primrec g :=
  (funext H : f = g) ▸ hf
#align primrec.of_eq Primrec.of_eq

/- warning: primrec.const -> Primrec.const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_3 : Primcodable.{u2} σ] (x : σ), Primrec.{u1, u2} α σ _inst_1 _inst_3 (fun (a : α) => x)
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_3 : Primcodable.{u1} σ] (x : σ), Primrec.{u2, u1} α σ _inst_1 _inst_3 (fun (a : α) => x)
Case conversion may be inaccurate. Consider using '#align primrec.const Primrec.constₓ'. -/
theorem const (x : σ) : Primrec fun a : α => x :=
  ((cases1 0 (const (encode x).succ)).comp (Primcodable.prim α)).of_eq fun n => by
    cases decode α n <;> rfl
#align primrec.const Primrec.const

#print Primrec.id /-
protected theorem id : Primrec (@id α) :=
  (Primcodable.prim α).of_eq <| by simp
#align primrec.id Primrec.id
-/

/- warning: primrec.comp -> Primrec.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} σ] {f : β -> σ} {g : α -> β}, (Primrec.{u2, u3} β σ _inst_2 _inst_3 f) -> (Primrec.{u1, u2} α β _inst_1 _inst_2 g) -> (Primrec.{u1, u3} α σ _inst_1 _inst_3 (fun (a : α) => f (g a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u3} β] [_inst_3 : Primcodable.{u2} σ] {f : β -> σ} {g : α -> β}, (Primrec.{u3, u2} β σ _inst_2 _inst_3 f) -> (Primrec.{u1, u3} α β _inst_1 _inst_2 g) -> (Primrec.{u1, u2} α σ _inst_1 _inst_3 (fun (a : α) => f (g a)))
Case conversion may be inaccurate. Consider using '#align primrec.comp Primrec.compₓ'. -/
theorem comp {f : β → σ} {g : α → β} (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f (g a) :=
  ((cases1 0 (hf.comp <| pred.comp hg)).comp (Primcodable.prim α)).of_eq fun n =>
    by
    cases decode α n; · rfl
    simp [encodek]
#align primrec.comp Primrec.comp

#print Primrec.succ /-
theorem succ : Primrec Nat.succ :=
  nat_iff.2 Nat.Primrec.succ
#align primrec.succ Primrec.succ
-/

#print Primrec.pred /-
theorem pred : Primrec Nat.pred :=
  nat_iff.2 Nat.Primrec.pred
#align primrec.pred Primrec.pred
-/

/- warning: primrec.encode_iff -> Primrec.encode_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_3 : Primcodable.{u2} σ] {f : α -> σ}, Iff (Primrec.{u1, 0} α Nat _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (fun (a : α) => Encodable.encode.{u2} σ (Primcodable.toEncodable.{u2} σ _inst_3) (f a))) (Primrec.{u1, u2} α σ _inst_1 _inst_3 f)
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_3 : Primcodable.{u1} σ] {f : α -> σ}, Iff (Primrec.{u2, 0} α Nat _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (fun (a : α) => Encodable.encode.{u1} σ (Primcodable.toEncodable.{u1} σ _inst_3) (f a))) (Primrec.{u2, u1} α σ _inst_1 _inst_3 f)
Case conversion may be inaccurate. Consider using '#align primrec.encode_iff Primrec.encode_iffₓ'. -/
theorem encode_iff {f : α → σ} : (Primrec fun a => encode (f a)) ↔ Primrec f :=
  ⟨fun h => Nat.Primrec.of_eq h fun n => by cases decode α n <;> rfl, Primrec.encode.comp⟩
#align primrec.encode_iff Primrec.encode_iff

/- warning: primrec.of_nat_iff -> Primrec.ofNat_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_4 : Denumerable.{u1} α] [_inst_5 : Primcodable.{u2} β] {f : α -> β}, Iff (Primrec.{u1, u2} α β (Primcodable.ofDenumerable.{u1} α _inst_4) _inst_5 f) (Primrec.{0, u2} Nat β (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) _inst_5 (fun (n : Nat) => f (Denumerable.ofNat.{u1} α _inst_4 n)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : Denumerable.{u2} α] [_inst_5 : Primcodable.{u1} β] {f : α -> β}, Iff (Primrec.{u2, u1} α β (Primcodable.ofDenumerable.{u2} α _inst_4) _inst_5 f) (Primrec.{0, u1} Nat β (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) _inst_5 (fun (n : Nat) => f (Denumerable.ofNat.{u2} α _inst_4 n)))
Case conversion may be inaccurate. Consider using '#align primrec.of_nat_iff Primrec.ofNat_iffₓ'. -/
theorem ofNat_iff {α β} [Denumerable α] [Primcodable β] {f : α → β} :
    Primrec f ↔ Primrec fun n => f (ofNat α n) :=
  dom_denumerable.trans <| nat_iff.symm.trans encode_iff
#align primrec.of_nat_iff Primrec.ofNat_iff

#print Primrec.ofNat /-
protected theorem ofNat (α) [Denumerable α] : Primrec (ofNat α) :=
  ofNat_iff.1 Primrec.id
#align primrec.of_nat Primrec.ofNat
-/

/- warning: primrec.option_some_iff -> Primrec.option_some_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_3 : Primcodable.{u2} σ] {f : α -> σ}, Iff (Primrec.{u1, u2} α (Option.{u2} σ) _inst_1 (Primcodable.option.{u2} σ _inst_3) (fun (a : α) => Option.some.{u2} σ (f a))) (Primrec.{u1, u2} α σ _inst_1 _inst_3 f)
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_3 : Primcodable.{u1} σ] {f : α -> σ}, Iff (Primrec.{u2, u1} α (Option.{u1} σ) _inst_1 (Primcodable.option.{u1} σ _inst_3) (fun (a : α) => Option.some.{u1} σ (f a))) (Primrec.{u2, u1} α σ _inst_1 _inst_3 f)
Case conversion may be inaccurate. Consider using '#align primrec.option_some_iff Primrec.option_some_iffₓ'. -/
theorem option_some_iff {f : α → σ} : (Primrec fun a => some (f a)) ↔ Primrec f :=
  ⟨fun h => encode_iff.1 <| pred.comp <| encode_iff.2 h, option_some.comp⟩
#align primrec.option_some_iff Primrec.option_some_iff

#print Primrec.ofEquiv /-
theorem ofEquiv {β} {e : β ≃ α} :
    haveI := Primcodable.ofEquiv α e
    Primrec e :=
  letI : Primcodable β := Primcodable.ofEquiv α e
  encode_iff.1 Primrec.encode
#align primrec.of_equiv Primrec.ofEquiv
-/

#print Primrec.ofEquiv_symm /-
theorem ofEquiv_symm {β} {e : β ≃ α} :
    haveI := Primcodable.ofEquiv α e
    Primrec e.symm :=
  letI := Primcodable.ofEquiv α e
  encode_iff.1 (show Primrec fun a => encode (e (e.symm a)) by simp [Primrec.encode])
#align primrec.of_equiv_symm Primrec.ofEquiv_symm
-/

/- warning: primrec.of_equiv_iff -> Primrec.ofEquiv_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_3 : Primcodable.{u2} σ] {β : Type.{u3}} (e : Equiv.{succ u3, succ u1} β α) {f : σ -> β}, Iff (Primrec.{u2, u1} σ α _inst_3 _inst_1 (fun (a : σ) => coeFn.{max 1 (max (succ u3) (succ u1)) (succ u1) (succ u3), max (succ u3) (succ u1)} (Equiv.{succ u3, succ u1} β α) (fun (_x : Equiv.{succ u3, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u3, succ u1} β α) e (f a))) (Primrec.{u2, u3} σ β _inst_3 (Primcodable.ofEquiv.{u1, u3} α β _inst_1 e) f)
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_3 : Primcodable.{u1} σ] {β : Type.{u3}} (e : Equiv.{succ u3, succ u2} β α) {f : σ -> β}, Iff (Primrec.{u1, u2} σ α _inst_3 _inst_1 (fun (a : σ) => FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (Equiv.{succ u3, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : β) => α) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u2} β α) e (f a))) (Primrec.{u1, u3} σ β _inst_3 (Primcodable.ofEquiv.{u2, u3} α β _inst_1 e) f)
Case conversion may be inaccurate. Consider using '#align primrec.of_equiv_iff Primrec.ofEquiv_iffₓ'. -/
theorem ofEquiv_iff {β} (e : β ≃ α) {f : σ → β} :
    haveI := Primcodable.ofEquiv α e
    (Primrec fun a => e (f a)) ↔ Primrec f :=
  letI := Primcodable.ofEquiv α e
  ⟨fun h => (of_equiv_symm.comp h).of_eq fun a => by simp, of_equiv.comp⟩
#align primrec.of_equiv_iff Primrec.ofEquiv_iff

/- warning: primrec.of_equiv_symm_iff -> Primrec.ofEquiv_symm_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_3 : Primcodable.{u2} σ] {β : Type.{u3}} (e : Equiv.{succ u3, succ u1} β α) {f : σ -> α}, Iff (Primrec.{u2, u3} σ β _inst_3 (Primcodable.ofEquiv.{u1, u3} α β _inst_1 e) (fun (a : σ) => coeFn.{max 1 (max (succ u1) (succ u3)) (succ u3) (succ u1), max (succ u1) (succ u3)} (Equiv.{succ u1, succ u3} α β) (fun (_x : Equiv.{succ u1, succ u3} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u3} α β) (Equiv.symm.{succ u3, succ u1} β α e) (f a))) (Primrec.{u2, u1} σ α _inst_3 _inst_1 f)
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_3 : Primcodable.{u1} σ] {β : Type.{u3}} (e : Equiv.{succ u3, succ u2} β α) {f : σ -> α}, Iff (Primrec.{u1, u3} σ β _inst_3 (Primcodable.ofEquiv.{u2, u3} α β _inst_1 e) (fun (a : σ) => FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (Equiv.{succ u2, succ u3} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u3} α β) (Equiv.symm.{succ u3, succ u2} β α e) (f a))) (Primrec.{u1, u2} σ α _inst_3 _inst_1 f)
Case conversion may be inaccurate. Consider using '#align primrec.of_equiv_symm_iff Primrec.ofEquiv_symm_iffₓ'. -/
theorem ofEquiv_symm_iff {β} (e : β ≃ α) {f : σ → α} :
    haveI := Primcodable.ofEquiv α e
    (Primrec fun a => e.symm (f a)) ↔ Primrec f :=
  letI := Primcodable.ofEquiv α e
  ⟨fun h => (of_equiv.comp h).of_eq fun a => by simp, of_equiv_symm.comp⟩
#align primrec.of_equiv_symm_iff Primrec.ofEquiv_symm_iff

end Primrec

namespace Primcodable

open Nat.Primrec

#print Primcodable.prod /-
instance prod {α β} [Primcodable α] [Primcodable β] : Primcodable (α × β) :=
  ⟨((cases zero ((cases zero succ).comp (pair right ((Primcodable.prim β).comp left)))).comp
          (pair right ((Primcodable.prim α).comp left))).of_eq
      fun n => by
      simp [Nat.unpaired]
      cases decode α n.unpair.1; · simp
      cases decode β n.unpair.2 <;> simp⟩
#align primcodable.prod Primcodable.prod
-/

end Primcodable

namespace Primrec

variable {α : Type _} {σ : Type _} [Primcodable α] [Primcodable σ]

open Nat.Primrec

/- warning: primrec.fst -> Primrec.fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_3 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} β], Primrec.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Primcodable.prod.{u1, u2} α β _inst_3 _inst_4) _inst_3 (Prod.fst.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_3 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} β], Primrec.{max u2 u1, u2} (Prod.{u2, u1} α β) α (Primcodable.prod.{u2, u1} α β _inst_3 _inst_4) _inst_3 (Prod.fst.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align primrec.fst Primrec.fstₓ'. -/
theorem fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.fst α β) :=
  ((cases zero
            ((cases zero (Nat.Primrec.succ.comp left)).comp
              (pair right ((Primcodable.prim β).comp left)))).comp
        (pair right ((Primcodable.prim α).comp left))).of_eq
    fun n => by
    simp
    cases decode α n.unpair.1 <;> simp
    cases decode β n.unpair.2 <;> simp
#align primrec.fst Primrec.fst

/- warning: primrec.snd -> Primrec.snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_3 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} β], Primrec.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Primcodable.prod.{u1, u2} α β _inst_3 _inst_4) _inst_4 (Prod.snd.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_3 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} β], Primrec.{max u2 u1, u1} (Prod.{u2, u1} α β) β (Primcodable.prod.{u2, u1} α β _inst_3 _inst_4) _inst_4 (Prod.snd.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align primrec.snd Primrec.sndₓ'. -/
theorem snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.snd α β) :=
  ((cases zero
            ((cases zero (Nat.Primrec.succ.comp right)).comp
              (pair right ((Primcodable.prim β).comp left)))).comp
        (pair right ((Primcodable.prim α).comp left))).of_eq
    fun n => by
    simp
    cases decode α n.unpair.1 <;> simp
    cases decode β n.unpair.2 <;> simp
#align primrec.snd Primrec.snd

/- warning: primrec.pair -> Primrec.pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} β] [_inst_5 : Primcodable.{u3} γ] {f : α -> β} {g : α -> γ}, (Primrec.{u1, u2} α β _inst_3 _inst_4 f) -> (Primrec.{u1, u3} α γ _inst_3 _inst_5 g) -> (Primrec.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_3 (Primcodable.prod.{u2, u3} β γ _inst_4 _inst_5) (fun (a : α) => Prod.mk.{u2, u3} β γ (f a) (g a)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_3 : Primcodable.{u3} α] [_inst_4 : Primcodable.{u2} β] [_inst_5 : Primcodable.{u1} γ] {f : α -> β} {g : α -> γ}, (Primrec.{u3, u2} α β _inst_3 _inst_4 f) -> (Primrec.{u3, u1} α γ _inst_3 _inst_5 g) -> (Primrec.{u3, max u1 u2} α (Prod.{u2, u1} β γ) _inst_3 (Primcodable.prod.{u2, u1} β γ _inst_4 _inst_5) (fun (a : α) => Prod.mk.{u2, u1} β γ (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align primrec.pair Primrec.pairₓ'. -/
theorem pair {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {f : α → β} {g : α → γ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => (f a, g a) :=
  ((cases1 0
            (Nat.Primrec.succ.comp <|
              pair (Nat.Primrec.pred.comp hf) (Nat.Primrec.pred.comp hg))).comp
        (Primcodable.prim α)).of_eq
    fun n => by cases decode α n <;> simp [encodek] <;> rfl
#align primrec.pair Primrec.pair

#print Primrec.unpair /-
theorem unpair : Primrec Nat.unpair :=
  (pair (nat_iff.2 Nat.Primrec.left) (nat_iff.2 Nat.Primrec.right)).of_eq fun n => by simp
#align primrec.unpair Primrec.unpair
-/

#print Primrec.list_get?₁ /-
theorem list_get?₁ : ∀ l : List α, Primrec l.get?
  | [] => dom_denumerable.2 zero
  | a :: l =>
    dom_denumerable.2 <|
      (cases1 (encode a).succ <| dom_denumerable.1 <| list_nth₁ l).of_eq fun n => by
        cases n <;> simp
#align primrec.list_nth₁ Primrec.list_get?₁
-/

end Primrec

#print Primrec₂ /-
/-- `primrec₂ f` means `f` is a binary primitive recursive function.
  This is technically unnecessary since we can always curry all
  the arguments together, but there are enough natural two-arg
  functions that it is convenient to express this directly. -/
def Primrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α → β → σ) :=
  Primrec fun p : α × β => f p.1 p.2
#align primrec₂ Primrec₂
-/

#print PrimrecPred /-
/-- `primrec_pred p` means `p : α → Prop` is a (decidable)
  primitive recursive predicate, which is to say that
  `to_bool ∘ p : α → bool` is primitive recursive. -/
def PrimrecPred {α} [Primcodable α] (p : α → Prop) [DecidablePred p] :=
  Primrec fun a => decide (p a)
#align primrec_pred PrimrecPred
-/

#print PrimrecRel /-
/-- `primrec_rel p` means `p : α → β → Prop` is a (decidable)
  primitive recursive relation, which is to say that
  `to_bool ∘ p : α → β → bool` is primitive recursive. -/
def PrimrecRel {α β} [Primcodable α] [Primcodable β] (s : α → β → Prop)
    [∀ a b, Decidable (s a b)] :=
  Primrec₂ fun a b => decide (s a b)
#align primrec_rel PrimrecRel
-/

namespace Primrec₂

variable {α : Type _} {β : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable σ]

/- warning: primrec₂.of_eq -> Primrec₂.of_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} σ] {f : α -> β -> σ} {g : α -> β -> σ}, (Primrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_3 f) -> (forall (a : α) (b : β), Eq.{succ u3} σ (f a b) (g a b)) -> (Primrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_3 g)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} σ] {f : α -> β -> σ} {g : α -> β -> σ}, (Primrec₂.{u3, u2, u1} α β σ _inst_1 _inst_2 _inst_3 f) -> (forall (a : α) (b : β), Eq.{succ u1} σ (f a b) (g a b)) -> (Primrec₂.{u3, u2, u1} α β σ _inst_1 _inst_2 _inst_3 g)
Case conversion may be inaccurate. Consider using '#align primrec₂.of_eq Primrec₂.of_eqₓ'. -/
theorem of_eq {f g : α → β → σ} (hg : Primrec₂ f) (H : ∀ a b, f a b = g a b) : Primrec₂ g :=
  (by funext a b <;> apply H : f = g) ▸ hg
#align primrec₂.of_eq Primrec₂.of_eq

/- warning: primrec₂.const -> Primrec₂.const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} σ] (x : σ), Primrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_3 (fun (a : α) (b : β) => x)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} σ] (x : σ), Primrec₂.{u3, u2, u1} α β σ _inst_1 _inst_2 _inst_3 (fun (a : α) (b : β) => x)
Case conversion may be inaccurate. Consider using '#align primrec₂.const Primrec₂.constₓ'. -/
theorem const (x : σ) : Primrec₂ fun (a : α) (b : β) => x :=
  Primrec.const _
#align primrec₂.const Primrec₂.const

/- warning: primrec₂.pair -> Primrec₂.pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β], Primrec₂.{u1, u2, max u1 u2} α β (Prod.{u1, u2} α β) _inst_1 _inst_2 (Primcodable.prod.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β], Primrec₂.{u2, u1, max u2 u1} α β (Prod.{u2, u1} α β) _inst_1 _inst_2 (Primcodable.prod.{u2, u1} α β _inst_1 _inst_2) (Prod.mk.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align primrec₂.pair Primrec₂.pairₓ'. -/
protected theorem pair : Primrec₂ (@Prod.mk α β) :=
  Primrec.pair Primrec.fst Primrec.snd
#align primrec₂.pair Primrec₂.pair

/- warning: primrec₂.left -> Primrec₂.left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β], Primrec₂.{u1, u2, u1} α β α _inst_1 _inst_2 _inst_1 (fun (a : α) (b : β) => a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β], Primrec₂.{u2, u1, u2} α β α _inst_1 _inst_2 _inst_1 (fun (a : α) (b : β) => a)
Case conversion may be inaccurate. Consider using '#align primrec₂.left Primrec₂.leftₓ'. -/
theorem left : Primrec₂ fun (a : α) (b : β) => a :=
  Primrec.fst
#align primrec₂.left Primrec₂.left

/- warning: primrec₂.right -> Primrec₂.right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β], Primrec₂.{u1, u2, u2} α β β _inst_1 _inst_2 _inst_2 (fun (a : α) (b : β) => b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β], Primrec₂.{u2, u1, u1} α β β _inst_1 _inst_2 _inst_2 (fun (a : α) (b : β) => b)
Case conversion may be inaccurate. Consider using '#align primrec₂.right Primrec₂.rightₓ'. -/
theorem right : Primrec₂ fun (a : α) (b : β) => b :=
  Primrec.snd
#align primrec₂.right Primrec₂.right

#print Primrec₂.natPair /-
theorem natPair : Primrec₂ Nat.pair := by simp [Primrec₂, Primrec] <;> constructor
#align primrec₂.mkpair Primrec₂.natPair
-/

#print Primrec₂.unpaired /-
theorem unpaired {f : ℕ → ℕ → α} : Primrec (Nat.unpaired f) ↔ Primrec₂ f :=
  ⟨fun h => by simpa using h.comp mkpair, fun h => h.comp Primrec.unpair⟩
#align primrec₂.unpaired Primrec₂.unpaired
-/

#print Primrec₂.unpaired' /-
theorem unpaired' {f : ℕ → ℕ → ℕ} : Nat.Primrec (Nat.unpaired f) ↔ Primrec₂ f :=
  Primrec.nat_iff.symm.trans unpaired
#align primrec₂.unpaired' Primrec₂.unpaired'
-/

/- warning: primrec₂.encode_iff -> Primrec₂.encode_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} σ] {f : α -> β -> σ}, Iff (Primrec₂.{u1, u2, 0} α β Nat _inst_1 _inst_2 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (fun (a : α) (b : β) => Encodable.encode.{u3} σ (Primcodable.toEncodable.{u3} σ _inst_3) (f a b))) (Primrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_3 f)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} σ] {f : α -> β -> σ}, Iff (Primrec₂.{u3, u2, 0} α β Nat _inst_1 _inst_2 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (fun (a : α) (b : β) => Encodable.encode.{u1} σ (Primcodable.toEncodable.{u1} σ _inst_3) (f a b))) (Primrec₂.{u3, u2, u1} α β σ _inst_1 _inst_2 _inst_3 f)
Case conversion may be inaccurate. Consider using '#align primrec₂.encode_iff Primrec₂.encode_iffₓ'. -/
theorem encode_iff {f : α → β → σ} : (Primrec₂ fun a b => encode (f a b)) ↔ Primrec₂ f :=
  Primrec.encode_iff
#align primrec₂.encode_iff Primrec₂.encode_iff

/- warning: primrec₂.option_some_iff -> Primrec₂.option_some_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} σ] {f : α -> β -> σ}, Iff (Primrec₂.{u1, u2, u3} α β (Option.{u3} σ) _inst_1 _inst_2 (Primcodable.option.{u3} σ _inst_3) (fun (a : α) (b : β) => Option.some.{u3} σ (f a b))) (Primrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_3 f)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} σ] {f : α -> β -> σ}, Iff (Primrec₂.{u3, u2, u1} α β (Option.{u1} σ) _inst_1 _inst_2 (Primcodable.option.{u1} σ _inst_3) (fun (a : α) (b : β) => Option.some.{u1} σ (f a b))) (Primrec₂.{u3, u2, u1} α β σ _inst_1 _inst_2 _inst_3 f)
Case conversion may be inaccurate. Consider using '#align primrec₂.option_some_iff Primrec₂.option_some_iffₓ'. -/
theorem option_some_iff {f : α → β → σ} : (Primrec₂ fun a b => some (f a b)) ↔ Primrec₂ f :=
  Primrec.option_some_iff
#align primrec₂.option_some_iff Primrec₂.option_some_iff

/- warning: primrec₂.of_nat_iff -> Primrec₂.ofNat_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_4 : Denumerable.{u1} α] [_inst_5 : Denumerable.{u2} β] [_inst_6 : Primcodable.{u3} σ] {f : α -> β -> σ}, Iff (Primrec₂.{u1, u2, u3} α β σ (Primcodable.ofDenumerable.{u1} α _inst_4) (Primcodable.ofDenumerable.{u2} β _inst_5) _inst_6 f) (Primrec₂.{0, 0, u3} Nat Nat σ (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) _inst_6 (fun (m : Nat) (n : Nat) => f (Denumerable.ofNat.{u1} α _inst_4 m) (Denumerable.ofNat.{u2} β _inst_5 n)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {σ : Type.{u1}} [_inst_4 : Denumerable.{u3} α] [_inst_5 : Denumerable.{u2} β] [_inst_6 : Primcodable.{u1} σ] {f : α -> β -> σ}, Iff (Primrec₂.{u3, u2, u1} α β σ (Primcodable.ofDenumerable.{u3} α _inst_4) (Primcodable.ofDenumerable.{u2} β _inst_5) _inst_6 f) (Primrec₂.{0, 0, u1} Nat Nat σ (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) _inst_6 (fun (m : Nat) (n : Nat) => f (Denumerable.ofNat.{u3} α _inst_4 m) (Denumerable.ofNat.{u2} β _inst_5 n)))
Case conversion may be inaccurate. Consider using '#align primrec₂.of_nat_iff Primrec₂.ofNat_iffₓ'. -/
theorem ofNat_iff {α β σ} [Denumerable α] [Denumerable β] [Primcodable σ] {f : α → β → σ} :
    Primrec₂ f ↔ Primrec₂ fun m n : ℕ => f (ofNat α m) (ofNat β n) :=
  (Primrec.ofNat_iff.trans <| by simp).trans unpaired
#align primrec₂.of_nat_iff Primrec₂.ofNat_iff

/- warning: primrec₂.uncurry -> Primrec₂.uncurry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} σ] {f : α -> β -> σ}, Iff (Primrec.{max u1 u2, u3} (Prod.{u1, u2} α β) σ (Primcodable.prod.{u1, u2} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u1, u2, u3} α β σ f)) (Primrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_3 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u3} β] [_inst_3 : Primcodable.{u1} σ] {f : α -> β -> σ}, Iff (Primrec.{max u3 u2, u1} (Prod.{u2, u3} α β) σ (Primcodable.prod.{u2, u3} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u2, u3, u1} α β σ f)) (Primrec₂.{u2, u3, u1} α β σ _inst_1 _inst_2 _inst_3 f)
Case conversion may be inaccurate. Consider using '#align primrec₂.uncurry Primrec₂.uncurryₓ'. -/
theorem uncurry {f : α → β → σ} : Primrec (Function.uncurry f) ↔ Primrec₂ f := by
  rw [show Function.uncurry f = fun p : α × β => f p.1 p.2 from funext fun ⟨a, b⟩ => rfl] <;> rfl
#align primrec₂.uncurry Primrec₂.uncurry

/- warning: primrec₂.curry -> Primrec₂.curry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} σ] {f : (Prod.{u1, u2} α β) -> σ}, Iff (Primrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_3 (Function.curry.{u1, u2, u3} α β σ f)) (Primrec.{max u1 u2, u3} (Prod.{u1, u2} α β) σ (Primcodable.prod.{u1, u2} α β _inst_1 _inst_2) _inst_3 f)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} σ] {f : (Prod.{u3, u2} α β) -> σ}, Iff (Primrec₂.{u3, u2, u1} α β σ _inst_1 _inst_2 _inst_3 (Function.curry.{u3, u2, u1} α β σ f)) (Primrec.{max u3 u2, u1} (Prod.{u3, u2} α β) σ (Primcodable.prod.{u3, u2} α β _inst_1 _inst_2) _inst_3 f)
Case conversion may be inaccurate. Consider using '#align primrec₂.curry Primrec₂.curryₓ'. -/
theorem curry {f : α × β → σ} : Primrec₂ (Function.curry f) ↔ Primrec f := by
  rw [← uncurry, Function.uncurry_curry]
#align primrec₂.curry Primrec₂.curry

end Primrec₂

section Comp

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

/- warning: primrec.comp₂ -> Primrec.comp₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {σ : Type.{u4}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] [_inst_5 : Primcodable.{u4} σ] {f : γ -> σ} {g : α -> β -> γ}, (Primrec.{u3, u4} γ σ _inst_3 _inst_5 f) -> (Primrec₂.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g) -> (Primrec₂.{u1, u2, u4} α β σ _inst_1 _inst_2 _inst_5 (fun (a : α) (b : β) => f (g a b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u4}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] [_inst_3 : Primcodable.{u4} γ] [_inst_5 : Primcodable.{u3} σ] {f : γ -> σ} {g : α -> β -> γ}, (Primrec.{u4, u3} γ σ _inst_3 _inst_5 f) -> (Primrec₂.{u2, u1, u4} α β γ _inst_1 _inst_2 _inst_3 g) -> (Primrec₂.{u2, u1, u3} α β σ _inst_1 _inst_2 _inst_5 (fun (a : α) (b : β) => f (g a b)))
Case conversion may be inaccurate. Consider using '#align primrec.comp₂ Primrec.comp₂ₓ'. -/
theorem Primrec.comp₂ {f : γ → σ} {g : α → β → γ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a b => f (g a b) :=
  hf.comp hg
#align primrec.comp₂ Primrec.comp₂

/- warning: primrec₂.comp -> Primrec₂.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {σ : Type.{u4}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] [_inst_5 : Primcodable.{u4} σ] {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}, (Primrec₂.{u2, u3, u4} β γ σ _inst_2 _inst_3 _inst_5 f) -> (Primrec.{u1, u2} α β _inst_1 _inst_2 g) -> (Primrec.{u1, u3} α γ _inst_1 _inst_3 h) -> (Primrec.{u1, u4} α σ _inst_1 _inst_5 (fun (a : α) => f (g a) (h a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u4}} {γ : Type.{u3}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u4} β] [_inst_3 : Primcodable.{u3} γ] [_inst_5 : Primcodable.{u2} σ] {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}, (Primrec₂.{u4, u3, u2} β γ σ _inst_2 _inst_3 _inst_5 f) -> (Primrec.{u1, u4} α β _inst_1 _inst_2 g) -> (Primrec.{u1, u3} α γ _inst_1 _inst_3 h) -> (Primrec.{u1, u2} α σ _inst_1 _inst_5 (fun (a : α) => f (g a) (h a)))
Case conversion may be inaccurate. Consider using '#align primrec₂.comp Primrec₂.compₓ'. -/
theorem Primrec₂.comp {f : β → γ → σ} {g : α → β} {h : α → γ} (hf : Primrec₂ f) (hg : Primrec g)
    (hh : Primrec h) : Primrec fun a => f (g a) (h a) :=
  hf.comp (hg.pair hh)
#align primrec₂.comp Primrec₂.comp

/- warning: primrec₂.comp₂ -> Primrec₂.comp₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {σ : Type.{u5}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] [_inst_4 : Primcodable.{u4} δ] [_inst_5 : Primcodable.{u5} σ] {f : γ -> δ -> σ} {g : α -> β -> γ} {h : α -> β -> δ}, (Primrec₂.{u3, u4, u5} γ δ σ _inst_3 _inst_4 _inst_5 f) -> (Primrec₂.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g) -> (Primrec₂.{u1, u2, u4} α β δ _inst_1 _inst_2 _inst_4 h) -> (Primrec₂.{u1, u2, u5} α β σ _inst_1 _inst_2 _inst_5 (fun (a : α) (b : β) => f (g a b) (h a b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u5}} {δ : Type.{u4}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] [_inst_3 : Primcodable.{u5} γ] [_inst_4 : Primcodable.{u4} δ] [_inst_5 : Primcodable.{u3} σ] {f : γ -> δ -> σ} {g : α -> β -> γ} {h : α -> β -> δ}, (Primrec₂.{u5, u4, u3} γ δ σ _inst_3 _inst_4 _inst_5 f) -> (Primrec₂.{u2, u1, u5} α β γ _inst_1 _inst_2 _inst_3 g) -> (Primrec₂.{u2, u1, u4} α β δ _inst_1 _inst_2 _inst_4 h) -> (Primrec₂.{u2, u1, u3} α β σ _inst_1 _inst_2 _inst_5 (fun (a : α) (b : β) => f (g a b) (h a b)))
Case conversion may be inaccurate. Consider using '#align primrec₂.comp₂ Primrec₂.comp₂ₓ'. -/
theorem Primrec₂.comp₂ {f : γ → δ → σ} {g : α → β → γ} {h : α → β → δ} (hf : Primrec₂ f)
    (hg : Primrec₂ g) (hh : Primrec₂ h) : Primrec₂ fun a b => f (g a b) (h a b) :=
  hf.comp hg hh
#align primrec₂.comp₂ Primrec₂.comp₂

#print PrimrecPred.comp /-
theorem PrimrecPred.comp {p : β → Prop} [DecidablePred p] {f : α → β} :
    PrimrecPred p → Primrec f → PrimrecPred fun a => p (f a) :=
  Primrec.comp
#align primrec_pred.comp PrimrecPred.comp
-/

/- warning: primrec_rel.comp -> PrimrecRel.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] {R : β -> γ -> Prop} [_inst_6 : forall (a : β) (b : γ), Decidable (R a b)] {f : α -> β} {g : α -> γ}, (PrimrecRel.{u2, u3} β γ _inst_2 _inst_3 R (fun (a : β) (b : γ) => _inst_6 a b)) -> (Primrec.{u1, u2} α β _inst_1 _inst_2 f) -> (Primrec.{u1, u3} α γ _inst_1 _inst_3 g) -> (PrimrecPred.{u1} α _inst_1 (fun (a : α) => R (f a) (g a)) (fun (a : α) => _inst_6 (f a) (g a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u3} β] [_inst_3 : Primcodable.{u2} γ] {R : β -> γ -> Prop} [_inst_6 : forall (a : β) (b : γ), Decidable (R a b)] {f : α -> β} {g : α -> γ}, (PrimrecRel.{u3, u2} β γ _inst_2 _inst_3 R (fun (a : β) (b : γ) => _inst_6 a b)) -> (Primrec.{u1, u3} α β _inst_1 _inst_2 f) -> (Primrec.{u1, u2} α γ _inst_1 _inst_3 g) -> (PrimrecPred.{u1} α _inst_1 (fun (a : α) => R (f a) (g a)) (fun (a : α) => _inst_6 (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align primrec_rel.comp PrimrecRel.compₓ'. -/
theorem PrimrecRel.comp {R : β → γ → Prop} [∀ a b, Decidable (R a b)] {f : α → β} {g : α → γ} :
    PrimrecRel R → Primrec f → Primrec g → PrimrecPred fun a => R (f a) (g a) :=
  Primrec₂.comp
#align primrec_rel.comp PrimrecRel.comp

/- warning: primrec_rel.comp₂ -> PrimrecRel.comp₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] [_inst_4 : Primcodable.{u4} δ] {R : γ -> δ -> Prop} [_inst_6 : forall (a : γ) (b : δ), Decidable (R a b)] {f : α -> β -> γ} {g : α -> β -> δ}, (PrimrecRel.{u3, u4} γ δ _inst_3 _inst_4 R (fun (a : γ) (b : δ) => _inst_6 a b)) -> (Primrec₂.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f) -> (Primrec₂.{u1, u2, u4} α β δ _inst_1 _inst_2 _inst_4 g) -> (PrimrecRel.{u1, u2} α β _inst_1 _inst_2 (fun (a : α) (b : β) => R (f a b) (g a b)) (fun (a : α) (b : β) => _inst_6 (f a b) (g a b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u4}} {δ : Type.{u3}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] [_inst_3 : Primcodable.{u4} γ] [_inst_4 : Primcodable.{u3} δ] {R : γ -> δ -> Prop} [_inst_6 : forall (a : γ) (b : δ), Decidable (R a b)] {f : α -> β -> γ} {g : α -> β -> δ}, (PrimrecRel.{u4, u3} γ δ _inst_3 _inst_4 R (fun (a : γ) (b : δ) => _inst_6 a b)) -> (Primrec₂.{u2, u1, u4} α β γ _inst_1 _inst_2 _inst_3 f) -> (Primrec₂.{u2, u1, u3} α β δ _inst_1 _inst_2 _inst_4 g) -> (PrimrecRel.{u2, u1} α β _inst_1 _inst_2 (fun (a : α) (b : β) => R (f a b) (g a b)) (fun (a : α) (b : β) => _inst_6 (f a b) (g a b)))
Case conversion may be inaccurate. Consider using '#align primrec_rel.comp₂ PrimrecRel.comp₂ₓ'. -/
theorem PrimrecRel.comp₂ {R : γ → δ → Prop} [∀ a b, Decidable (R a b)] {f : α → β → γ}
    {g : α → β → δ} :
    PrimrecRel R → Primrec₂ f → Primrec₂ g → PrimrecRel fun a b => R (f a b) (g a b) :=
  PrimrecRel.comp
#align primrec_rel.comp₂ PrimrecRel.comp₂

end Comp

#print PrimrecPred.of_eq /-
theorem PrimrecPred.of_eq {α} [Primcodable α] {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : PrimrecPred p) (H : ∀ a, p a ↔ q a) : PrimrecPred q :=
  Primrec.of_eq hp fun a => Bool.decide_congr (H a)
#align primrec_pred.of_eq PrimrecPred.of_eq
-/

/- warning: primrec_rel.of_eq -> PrimrecRel.of_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {r : α -> β -> Prop} {s : α -> β -> Prop} [_inst_3 : forall (a : α) (b : β), Decidable (r a b)] [_inst_4 : forall (a : α) (b : β), Decidable (s a b)], (PrimrecRel.{u1, u2} α β _inst_1 _inst_2 r (fun (a : α) (b : β) => _inst_3 a b)) -> (forall (a : α) (b : β), Iff (r a b) (s a b)) -> (PrimrecRel.{u1, u2} α β _inst_1 _inst_2 s (fun (a : α) (b : β) => _inst_4 a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {r : α -> β -> Prop} {s : α -> β -> Prop} [_inst_3 : forall (a : α) (b : β), Decidable (r a b)] [_inst_4 : forall (a : α) (b : β), Decidable (s a b)], (PrimrecRel.{u2, u1} α β _inst_1 _inst_2 r (fun (a : α) (b : β) => _inst_3 a b)) -> (forall (a : α) (b : β), Iff (r a b) (s a b)) -> (PrimrecRel.{u2, u1} α β _inst_1 _inst_2 s (fun (a : α) (b : β) => _inst_4 a b))
Case conversion may be inaccurate. Consider using '#align primrec_rel.of_eq PrimrecRel.of_eqₓ'. -/
theorem PrimrecRel.of_eq {α β} [Primcodable α] [Primcodable β] {r s : α → β → Prop}
    [∀ a b, Decidable (r a b)] [∀ a b, Decidable (s a b)] (hr : PrimrecRel r)
    (H : ∀ a b, r a b ↔ s a b) : PrimrecRel s :=
  Primrec₂.of_eq hr fun a b => Bool.decide_congr (H a b)
#align primrec_rel.of_eq PrimrecRel.of_eq

namespace Primrec₂

variable {α : Type _} {β : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Nat.Primrec

/- warning: primrec₂.swap -> Primrec₂.swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} σ] {f : α -> β -> σ}, (Primrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_3 f) -> (Primrec₂.{u2, u1, u3} β α σ _inst_2 _inst_1 _inst_3 (Function.swap.{succ u1, succ u2, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => σ) f))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} σ] {f : α -> β -> σ}, (Primrec₂.{u3, u2, u1} α β σ _inst_1 _inst_2 _inst_3 f) -> (Primrec₂.{u2, u3, u1} β α σ _inst_2 _inst_1 _inst_3 (Function.swap.{succ u3, succ u2, succ u1} α β (fun (ᾰ : α) (ᾰ : β) => σ) f))
Case conversion may be inaccurate. Consider using '#align primrec₂.swap Primrec₂.swapₓ'. -/
theorem swap {f : α → β → σ} (h : Primrec₂ f) : Primrec₂ (swap f) :=
  h.comp₂ Primrec₂.right Primrec₂.left
#align primrec₂.swap Primrec₂.swap

/- warning: primrec₂.nat_iff -> Primrec₂.nat_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} σ] {f : α -> β -> σ}, Iff (Primrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_3 f) (Nat.Primrec (Nat.unpaired.{1} Nat (fun (m : Nat) (n : Nat) => Encodable.encode.{u3} (Option.{u3} σ) (Option.encodable.{u3} σ (Primcodable.toEncodable.{u3} σ _inst_3)) (Option.bind.{u1, u3} α σ (Encodable.decode.{u1} α (Primcodable.toEncodable.{u1} α _inst_1) m) (fun (a : α) => Option.map.{u2, u3} β σ (f a) (Encodable.decode.{u2} β (Primcodable.toEncodable.{u2} β _inst_2) n))))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} σ] {f : α -> β -> σ}, Iff (Primrec₂.{u3, u2, u1} α β σ _inst_1 _inst_2 _inst_3 f) (Nat.Primrec (Nat.unpaired.{1} Nat (fun (m : Nat) (n : Nat) => Encodable.encode.{u1} (Option.{u1} σ) (Option.encodable.{u1} σ (Primcodable.toEncodable.{u1} σ _inst_3)) (Option.bind.{u3, u1} α σ (Encodable.decode.{u3} α (Primcodable.toEncodable.{u3} α _inst_1) m) (fun (a : α) => Option.map.{u2, u1} β σ (f a) (Encodable.decode.{u2} β (Primcodable.toEncodable.{u2} β _inst_2) n))))))
Case conversion may be inaccurate. Consider using '#align primrec₂.nat_iff Primrec₂.nat_iffₓ'. -/
theorem nat_iff {f : α → β → σ} :
    Primrec₂ f ↔
      Nat.Primrec
        (Nat.unpaired fun m n : ℕ => encode <| (decode α m).bind fun a => (decode β n).map (f a)) :=
  by
  have :
    ∀ (a : Option α) (b : Option β),
      Option.map (fun p : α × β => f p.1 p.2)
          (Option.bind a fun a : α => Option.map (Prod.mk a) b) =
        Option.bind a fun a => Option.map (f a) b :=
    by intros <;> cases a <;> [rfl, · cases b <;> rfl]
  simp [Primrec₂, Primrec, this]
#align primrec₂.nat_iff Primrec₂.nat_iff

/- warning: primrec₂.nat_iff' -> Primrec₂.nat_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} σ] {f : α -> β -> σ}, Iff (Primrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_3 f) (Primrec₂.{0, 0, u3} Nat Nat (Option.{u3} σ) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.option.{u3} σ _inst_3) (fun (m : Nat) (n : Nat) => Option.bind.{u1, u3} α σ (Encodable.decode.{u1} α (Primcodable.toEncodable.{u1} α _inst_1) m) (fun (a : α) => Option.map.{u2, u3} β σ (f a) (Encodable.decode.{u2} β (Primcodable.toEncodable.{u2} β _inst_2) n))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} σ] {f : α -> β -> σ}, Iff (Primrec₂.{u3, u2, u1} α β σ _inst_1 _inst_2 _inst_3 f) (Primrec₂.{0, 0, u1} Nat Nat (Option.{u1} σ) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.option.{u1} σ _inst_3) (fun (m : Nat) (n : Nat) => Option.bind.{u3, u1} α σ (Encodable.decode.{u3} α (Primcodable.toEncodable.{u3} α _inst_1) m) (fun (a : α) => Option.map.{u2, u1} β σ (f a) (Encodable.decode.{u2} β (Primcodable.toEncodable.{u2} β _inst_2) n))))
Case conversion may be inaccurate. Consider using '#align primrec₂.nat_iff' Primrec₂.nat_iff'ₓ'. -/
theorem nat_iff' {f : α → β → σ} :
    Primrec₂ f ↔
      Primrec₂ fun m n : ℕ => Option.bind (decode α m) fun a => Option.map (f a) (decode β n) :=
  nat_iff.trans <| unpaired'.trans encode_iff
#align primrec₂.nat_iff' Primrec₂.nat_iff'

end Primrec₂

namespace Primrec

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

/- warning: primrec.to₂ -> Primrec.to₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_5 : Primcodable.{u3} σ] {f : (Prod.{u1, u2} α β) -> σ}, (Primrec.{max u1 u2, u3} (Prod.{u1, u2} α β) σ (Primcodable.prod.{u1, u2} α β _inst_1 _inst_2) _inst_5 f) -> (Primrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_5 (fun (a : α) (b : β) => f (Prod.mk.{u1, u2} α β a b)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_5 : Primcodable.{u1} σ] {f : (Prod.{u3, u2} α β) -> σ}, (Primrec.{max u3 u2, u1} (Prod.{u3, u2} α β) σ (Primcodable.prod.{u3, u2} α β _inst_1 _inst_2) _inst_5 f) -> (Primrec₂.{u3, u2, u1} α β σ _inst_1 _inst_2 _inst_5 (fun (a : α) (b : β) => f (Prod.mk.{u3, u2} α β a b)))
Case conversion may be inaccurate. Consider using '#align primrec.to₂ Primrec.to₂ₓ'. -/
theorem to₂ {f : α × β → σ} (hf : Primrec f) : Primrec₂ fun a b => f (a, b) :=
  hf.of_eq fun ⟨a, b⟩ => rfl
#align primrec.to₂ Primrec.to₂

#print Primrec.nat_elim /-
theorem nat_elim {f : α → β} {g : α → ℕ × β → β} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a (n : ℕ) => n.elim (f a) fun n IH => g a (n, IH) :=
  Primrec₂.nat_iff.2 <|
    ((Nat.Primrec.cases Nat.Primrec.zero <|
              (Nat.Primrec.prec hf <|
                    Nat.Primrec.comp hg <|
                      Nat.Primrec.left.pair <|
                        (Nat.Primrec.left.comp Nat.Primrec.right).pair <|
                          Nat.Primrec.pred.comp <| Nat.Primrec.right.comp Nat.Primrec.right).comp <|
                Nat.Primrec.right.pair <| Nat.Primrec.right.comp Nat.Primrec.left).comp <|
          Nat.Primrec.id.pair <| (Primcodable.prim α).comp Nat.Primrec.left).of_eq
      fun n => by
      simp
      cases' decode α n.unpair.1 with a; · rfl
      simp [encodek]
      induction' n.unpair.2 with m <;> simp [encodek]
      simp [ih, encodek]
#align primrec.nat_elim Primrec.nat_elim
-/

#print Primrec.nat_elim' /-
theorem nat_elim' {f : α → ℕ} {g : α → β} {h : α → ℕ × β → β} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec₂ h) : Primrec fun a => (f a).elim (g a) fun n IH => h a (n, IH) :=
  (nat_elim hg hh).comp Primrec.id hf
#align primrec.nat_elim' Primrec.nat_elim'
-/

#print Primrec.nat_elim₁ /-
theorem nat_elim₁ {f : ℕ → α → α} (a : α) (hf : Primrec₂ f) : Primrec (Nat.rec a f) :=
  nat_elim' Primrec.id (const a) <| comp₂ hf Primrec₂.right
#align primrec.nat_elim₁ Primrec.nat_elim₁
-/

/- warning: primrec.nat_cases' -> Primrec.nat_cases' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {f : α -> β} {g : α -> Nat -> β}, (Primrec.{u1, u2} α β _inst_1 _inst_2 f) -> (Primrec₂.{u1, 0, u2} α Nat β _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) _inst_2 g) -> (Primrec₂.{u1, 0, u2} α Nat β _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) _inst_2 (fun (a : α) => Nat.casesOn.{succ u2} β (f a) (g a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {f : α -> β} {g : α -> Nat -> β}, (Primrec.{u2, u1} α β _inst_1 _inst_2 f) -> (Primrec₂.{u2, 0, u1} α Nat β _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) _inst_2 g) -> (Primrec₂.{u2, 0, u1} α Nat β _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) _inst_2 (fun (a : α) (n : Nat) => Nat.casesOn.{succ u1} (fun (x._@.Mathlib.Computability.Primrec._hyg.4800 : Nat) => β) n (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align primrec.nat_cases' Primrec.nat_cases'ₓ'. -/
theorem nat_cases' {f : α → β} {g : α → ℕ → β} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a => Nat.casesOn (f a) (g a) :=
  nat_elim hf <| hg.comp₂ Primrec₂.left <| comp₂ fst Primrec₂.right
#align primrec.nat_cases' Primrec.nat_cases'

/- warning: primrec.nat_cases -> Primrec.nat_cases is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {f : α -> Nat} {g : α -> β} {h : α -> Nat -> β}, (Primrec.{u1, 0} α Nat _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) f) -> (Primrec.{u1, u2} α β _inst_1 _inst_2 g) -> (Primrec₂.{u1, 0, u2} α Nat β _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) _inst_2 h) -> (Primrec.{u1, u2} α β _inst_1 _inst_2 (fun (a : α) => Nat.casesOn.{succ u2} β (g a) (h a) (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {f : α -> Nat} {g : α -> β} {h : α -> Nat -> β}, (Primrec.{u2, 0} α Nat _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) f) -> (Primrec.{u2, u1} α β _inst_1 _inst_2 g) -> (Primrec₂.{u2, 0, u1} α Nat β _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) _inst_2 h) -> (Primrec.{u2, u1} α β _inst_1 _inst_2 (fun (a : α) => Nat.casesOn.{succ u1} (fun (x._@.Mathlib.Computability.Primrec._hyg.4875 : Nat) => β) (f a) (g a) (h a)))
Case conversion may be inaccurate. Consider using '#align primrec.nat_cases Primrec.nat_casesₓ'. -/
theorem nat_cases {f : α → ℕ} {g : α → β} {h : α → ℕ → β} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec₂ h) : Primrec fun a => (f a).cases (g a) (h a) :=
  (nat_cases' hg hh).comp Primrec.id hf
#align primrec.nat_cases Primrec.nat_cases

#print Primrec.nat_cases₁ /-
theorem nat_cases₁ {f : ℕ → α} (a : α) (hf : Primrec f) : Primrec (Nat.casesOn a f) :=
  nat_cases Primrec.id (const a) (comp₂ hf Primrec₂.right)
#align primrec.nat_cases₁ Primrec.nat_cases₁
-/

/- warning: primrec.nat_iterate -> Primrec.nat_iterate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {f : α -> Nat} {g : α -> β} {h : α -> β -> β}, (Primrec.{u1, 0} α Nat _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) f) -> (Primrec.{u1, u2} α β _inst_1 _inst_2 g) -> (Primrec₂.{u1, u2, u2} α β β _inst_1 _inst_2 _inst_2 h) -> (Primrec.{u1, u2} α β _inst_1 _inst_2 (fun (a : α) => Nat.iterate.{succ u2} β (h a) (f a) (g a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {f : α -> Nat} {g : α -> β} {h : α -> β -> β}, (Primrec.{u2, 0} α Nat _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) f) -> (Primrec.{u2, u1} α β _inst_1 _inst_2 g) -> (Primrec₂.{u2, u1, u1} α β β _inst_1 _inst_2 _inst_2 h) -> (Primrec.{u2, u1} α β _inst_1 _inst_2 (fun (a : α) => Nat.iterate.{succ u1} β (h a) (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align primrec.nat_iterate Primrec.nat_iterateₓ'. -/
theorem nat_iterate {f : α → ℕ} {g : α → β} {h : α → β → β} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec₂ h) : Primrec fun a => (h a^[f a]) (g a) :=
  (nat_elim' hf hg (hh.comp₂ Primrec₂.left <| snd.comp₂ Primrec₂.right)).of_eq fun a => by
    induction f a <;> simp [*, Function.iterate_succ']
#align primrec.nat_iterate Primrec.nat_iterate

/- warning: primrec.option_cases -> Primrec.option_cases is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_5 : Primcodable.{u3} σ] {o : α -> (Option.{u2} β)} {f : α -> σ} {g : α -> β -> σ}, (Primrec.{u1, u2} α (Option.{u2} β) _inst_1 (Primcodable.option.{u2} β _inst_2) o) -> (Primrec.{u1, u3} α σ _inst_1 _inst_5 f) -> (Primrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_5 g) -> (Primrec.{u1, u3} α σ _inst_1 _inst_5 (fun (a : α) => Option.casesOn.{succ u3, u2} β (fun (_x : Option.{u2} β) => σ) (o a) (f a) (g a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u3} β] [_inst_5 : Primcodable.{u1} σ] {o : α -> (Option.{u3} β)} {f : α -> σ} {g : α -> β -> σ}, (Primrec.{u2, u3} α (Option.{u3} β) _inst_1 (Primcodable.option.{u3} β _inst_2) o) -> (Primrec.{u2, u1} α σ _inst_1 _inst_5 f) -> (Primrec₂.{u2, u3, u1} α β σ _inst_1 _inst_2 _inst_5 g) -> (Primrec.{u2, u1} α σ _inst_1 _inst_5 (fun (a : α) => Option.casesOn.{succ u1, u3} β (fun (_x : Option.{u3} β) => σ) (o a) (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align primrec.option_cases Primrec.option_casesₓ'. -/
theorem option_cases {o : α → Option β} {f : α → σ} {g : α → β → σ} (ho : Primrec o)
    (hf : Primrec f) (hg : Primrec₂ g) :
    @Primrec _ σ _ _ fun a => Option.casesOn (o a) (f a) (g a) :=
  encode_iff.1 <|
    (nat_cases (encode_iff.2 ho) (encode_iff.2 hf) <|
          pred.comp₂ <|
            Primrec₂.encode_iff.2 <|
              (Primrec₂.nat_iff'.1 hg).comp₂ ((@Primrec.encode α _).comp fst).to₂
                Primrec₂.right).of_eq
      fun a => by cases' o a with b <;> simp [encodek] <;> rfl
#align primrec.option_cases Primrec.option_cases

/- warning: primrec.option_bind -> Primrec.option_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_5 : Primcodable.{u3} σ] {f : α -> (Option.{u2} β)} {g : α -> β -> (Option.{u3} σ)}, (Primrec.{u1, u2} α (Option.{u2} β) _inst_1 (Primcodable.option.{u2} β _inst_2) f) -> (Primrec₂.{u1, u2, u3} α β (Option.{u3} σ) _inst_1 _inst_2 (Primcodable.option.{u3} σ _inst_5) g) -> (Primrec.{u1, u3} α (Option.{u3} σ) _inst_1 (Primcodable.option.{u3} σ _inst_5) (fun (a : α) => Option.bind.{u2, u3} β σ (f a) (g a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u3} β] [_inst_5 : Primcodable.{u2} σ] {f : α -> (Option.{u3} β)} {g : α -> β -> (Option.{u2} σ)}, (Primrec.{u1, u3} α (Option.{u3} β) _inst_1 (Primcodable.option.{u3} β _inst_2) f) -> (Primrec₂.{u1, u3, u2} α β (Option.{u2} σ) _inst_1 _inst_2 (Primcodable.option.{u2} σ _inst_5) g) -> (Primrec.{u1, u2} α (Option.{u2} σ) _inst_1 (Primcodable.option.{u2} σ _inst_5) (fun (a : α) => Option.bind.{u3, u2} β σ (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align primrec.option_bind Primrec.option_bindₓ'. -/
theorem option_bind {f : α → Option β} {g : α → β → Option σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).bind (g a) :=
  (option_cases hf (const none) hg).of_eq fun a => by cases f a <;> rfl
#align primrec.option_bind Primrec.option_bind

#print Primrec.option_bind₁ /-
theorem option_bind₁ {f : α → Option σ} (hf : Primrec f) : Primrec fun o => Option.bind o f :=
  option_bind Primrec.id (hf.comp snd).to₂
#align primrec.option_bind₁ Primrec.option_bind₁
-/

/- warning: primrec.option_map -> Primrec.option_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_5 : Primcodable.{u3} σ] {f : α -> (Option.{u2} β)} {g : α -> β -> σ}, (Primrec.{u1, u2} α (Option.{u2} β) _inst_1 (Primcodable.option.{u2} β _inst_2) f) -> (Primrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_5 g) -> (Primrec.{u1, u3} α (Option.{u3} σ) _inst_1 (Primcodable.option.{u3} σ _inst_5) (fun (a : α) => Option.map.{u2, u3} β σ (g a) (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u3} β] [_inst_5 : Primcodable.{u1} σ] {f : α -> (Option.{u3} β)} {g : α -> β -> σ}, (Primrec.{u2, u3} α (Option.{u3} β) _inst_1 (Primcodable.option.{u3} β _inst_2) f) -> (Primrec₂.{u2, u3, u1} α β σ _inst_1 _inst_2 _inst_5 g) -> (Primrec.{u2, u1} α (Option.{u1} σ) _inst_1 (Primcodable.option.{u1} σ _inst_5) (fun (a : α) => Option.map.{u3, u1} β σ (g a) (f a)))
Case conversion may be inaccurate. Consider using '#align primrec.option_map Primrec.option_mapₓ'. -/
theorem option_map {f : α → Option β} {g : α → β → σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).map (g a) :=
  option_bind hf (option_some.comp₂ hg)
#align primrec.option_map Primrec.option_map

/- warning: primrec.option_map₁ -> Primrec.option_map₁ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_5 : Primcodable.{u2} σ] {f : α -> σ}, (Primrec.{u1, u2} α σ _inst_1 _inst_5 f) -> (Primrec.{u1, u2} (Option.{u1} α) (Option.{u2} σ) (Primcodable.option.{u1} α _inst_1) (Primcodable.option.{u2} σ _inst_5) (Option.map.{u1, u2} α σ f))
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_5 : Primcodable.{u1} σ] {f : α -> σ}, (Primrec.{u2, u1} α σ _inst_1 _inst_5 f) -> (Primrec.{u2, u1} (Option.{u2} α) (Option.{u1} σ) (Primcodable.option.{u2} α _inst_1) (Primcodable.option.{u1} σ _inst_5) (Option.map.{u2, u1} α σ f))
Case conversion may be inaccurate. Consider using '#align primrec.option_map₁ Primrec.option_map₁ₓ'. -/
theorem option_map₁ {f : α → σ} (hf : Primrec f) : Primrec (Option.map f) :=
  option_map Primrec.id (hf.comp snd).to₂
#align primrec.option_map₁ Primrec.option_map₁

#print Primrec.option_iget /-
theorem option_iget [Inhabited α] : Primrec (@Option.iget α _) :=
  (option_cases Primrec.id (const <| @default α _) Primrec₂.right).of_eq fun o => by cases o <;> rfl
#align primrec.option_iget Primrec.option_iget
-/

#print Primrec.option_isSome /-
theorem option_isSome : Primrec (@Option.isSome α) :=
  (option_cases Primrec.id (const false) (const true).to₂).of_eq fun o => by cases o <;> rfl
#align primrec.option_is_some Primrec.option_isSome
-/

#print Primrec.option_getD /-
theorem option_getD : Primrec₂ (@Option.getD α) :=
  Primrec.of_eq (option_cases Primrec₂.left Primrec₂.right Primrec₂.right) fun ⟨o, a⟩ => by
    cases o <;> rfl
#align primrec.option_get_or_else Primrec.option_getD
-/

/- warning: primrec.bind_decode_iff -> Primrec.bind_decode_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_5 : Primcodable.{u3} σ] {f : α -> β -> (Option.{u3} σ)}, Iff (Primrec₂.{u1, 0, u3} α Nat (Option.{u3} σ) _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.option.{u3} σ _inst_5) (fun (a : α) (n : Nat) => Option.bind.{u2, u3} β σ (Encodable.decode.{u2} β (Primcodable.toEncodable.{u2} β _inst_2) n) (f a))) (Primrec₂.{u1, u2, u3} α β (Option.{u3} σ) _inst_1 _inst_2 (Primcodable.option.{u3} σ _inst_5) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] [_inst_5 : Primcodable.{u3} σ] {f : α -> β -> (Option.{u3} σ)}, Iff (Primrec₂.{u2, 0, u3} α Nat (Option.{u3} σ) _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.option.{u3} σ _inst_5) (fun (a : α) (n : Nat) => Option.bind.{u1, u3} β σ (Encodable.decode.{u1} β (Primcodable.toEncodable.{u1} β _inst_2) n) (f a))) (Primrec₂.{u2, u1, u3} α β (Option.{u3} σ) _inst_1 _inst_2 (Primcodable.option.{u3} σ _inst_5) f)
Case conversion may be inaccurate. Consider using '#align primrec.bind_decode_iff Primrec.bind_decode_iffₓ'. -/
theorem bind_decode_iff {f : α → β → Option σ} :
    (Primrec₂ fun a n => (decode β n).bind (f a)) ↔ Primrec₂ f :=
  ⟨fun h => by simpa [encodek] using h.comp fst ((@Primrec.encode β _).comp snd), fun h =>
    option_bind (Primrec.decode.comp snd) <| h.comp (fst.comp fst) snd⟩
#align primrec.bind_decode_iff Primrec.bind_decode_iff

/- warning: primrec.map_decode_iff -> Primrec.map_decode_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_5 : Primcodable.{u3} σ] {f : α -> β -> σ}, Iff (Primrec₂.{u1, 0, u3} α Nat (Option.{u3} σ) _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.option.{u3} σ _inst_5) (fun (a : α) (n : Nat) => Option.map.{u2, u3} β σ (f a) (Encodable.decode.{u2} β (Primcodable.toEncodable.{u2} β _inst_2) n))) (Primrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_5 f)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u1} β] [_inst_5 : Primcodable.{u2} σ] {f : α -> β -> σ}, Iff (Primrec₂.{u3, 0, u2} α Nat (Option.{u2} σ) _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.option.{u2} σ _inst_5) (fun (a : α) (n : Nat) => Option.map.{u1, u2} β σ (f a) (Encodable.decode.{u1} β (Primcodable.toEncodable.{u1} β _inst_2) n))) (Primrec₂.{u3, u1, u2} α β σ _inst_1 _inst_2 _inst_5 f)
Case conversion may be inaccurate. Consider using '#align primrec.map_decode_iff Primrec.map_decode_iffₓ'. -/
theorem map_decode_iff {f : α → β → σ} :
    (Primrec₂ fun a n => (decode β n).map (f a)) ↔ Primrec₂ f :=
  bind_decode_iff.trans Primrec₂.option_some_iff
#align primrec.map_decode_iff Primrec.map_decode_iff

#print Primrec.nat_add /-
theorem nat_add : Primrec₂ ((· + ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.add
#align primrec.nat_add Primrec.nat_add
-/

#print Primrec.nat_sub /-
theorem nat_sub : Primrec₂ (Sub.sub : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.sub
#align primrec.nat_sub Primrec.nat_sub
-/

#print Primrec.nat_mul /-
theorem nat_mul : Primrec₂ ((· * ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.mul
#align primrec.nat_mul Primrec.nat_mul
-/

/- warning: primrec.cond -> Primrec.cond is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_5 : Primcodable.{u2} σ] {c : α -> Bool} {f : α -> σ} {g : α -> σ}, (Primrec.{u1, 0} α Bool _inst_1 Primcodable.bool c) -> (Primrec.{u1, u2} α σ _inst_1 _inst_5 f) -> (Primrec.{u1, u2} α σ _inst_1 _inst_5 g) -> (Primrec.{u1, u2} α σ _inst_1 _inst_5 (fun (a : α) => cond.{u2} σ (c a) (f a) (g a)))
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_5 : Primcodable.{u1} σ] {c : α -> Bool} {f : α -> σ} {g : α -> σ}, (Primrec.{u2, 0} α Bool _inst_1 Primcodable.bool c) -> (Primrec.{u2, u1} α σ _inst_1 _inst_5 f) -> (Primrec.{u2, u1} α σ _inst_1 _inst_5 g) -> (Primrec.{u2, u1} α σ _inst_1 _inst_5 (fun (a : α) => cond.{u1} σ (c a) (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align primrec.cond Primrec.condₓ'. -/
theorem cond {c : α → Bool} {f : α → σ} {g : α → σ} (hc : Primrec c) (hf : Primrec f)
    (hg : Primrec g) : Primrec fun a => cond (c a) (f a) (g a) :=
  (nat_cases (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq fun a => by cases c a <;> rfl
#align primrec.cond Primrec.cond

/- warning: primrec.ite -> Primrec.ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_5 : Primcodable.{u2} σ] {c : α -> Prop} [_inst_6 : DecidablePred.{succ u1} α c] {f : α -> σ} {g : α -> σ}, (PrimrecPred.{u1} α _inst_1 c (fun (a : α) => _inst_6 a)) -> (Primrec.{u1, u2} α σ _inst_1 _inst_5 f) -> (Primrec.{u1, u2} α σ _inst_1 _inst_5 g) -> (Primrec.{u1, u2} α σ _inst_1 _inst_5 (fun (a : α) => ite.{succ u2} σ (c a) (_inst_6 a) (f a) (g a)))
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_5 : Primcodable.{u1} σ] {c : α -> Prop} [_inst_6 : DecidablePred.{succ u2} α c] {f : α -> σ} {g : α -> σ}, (PrimrecPred.{u2} α _inst_1 c (fun (a : α) => _inst_6 a)) -> (Primrec.{u2, u1} α σ _inst_1 _inst_5 f) -> (Primrec.{u2, u1} α σ _inst_1 _inst_5 g) -> (Primrec.{u2, u1} α σ _inst_1 _inst_5 (fun (a : α) => ite.{succ u1} σ (c a) (_inst_6 a) (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align primrec.ite Primrec.iteₓ'. -/
theorem ite {c : α → Prop} [DecidablePred c] {f : α → σ} {g : α → σ} (hc : PrimrecPred c)
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => if c a then f a else g a := by
  simpa using cond hc hf hg
#align primrec.ite Primrec.ite

/- warning: primrec.nat_le -> Primrec.nat_le is a dubious translation:
lean 3 declaration is
  PrimrecRel.{0, 0} Nat Nat (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (LE.le.{0} Nat Nat.hasLe) (fun (a : Nat) (b : Nat) => Nat.decidableLe a b)
but is expected to have type
  PrimrecRel.{0, 0} Nat Nat (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (fun (x._@.Mathlib.Computability.Primrec._hyg.6194 : Nat) (x._@.Mathlib.Computability.Primrec._hyg.6196 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Computability.Primrec._hyg.6194 x._@.Mathlib.Computability.Primrec._hyg.6196) (fun (a : Nat) (b : Nat) => Nat.decLe a b)
Case conversion may be inaccurate. Consider using '#align primrec.nat_le Primrec.nat_leₓ'. -/
theorem nat_le : PrimrecRel ((· ≤ ·) : ℕ → ℕ → Prop) :=
  (nat_cases nat_sub (const true) (const false).to₂).of_eq fun p =>
    by
    dsimp [swap]
    cases' e : p.1 - p.2 with n
    · simp [tsub_eq_zero_iff_le.1 e]
    · simp [not_le.2 (Nat.lt_of_sub_eq_succ e)]
#align primrec.nat_le Primrec.nat_le

/- warning: primrec.nat_min -> Primrec.nat_min is a dubious translation:
lean 3 declaration is
  Primrec₂.{0, 0, 0} Nat Nat Nat (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (LinearOrder.min.{0} Nat Nat.linearOrder)
but is expected to have type
  Primrec₂.{0, 0, 0} Nat Nat Nat (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Min.min.{0} Nat instMinNat)
Case conversion may be inaccurate. Consider using '#align primrec.nat_min Primrec.nat_minₓ'. -/
theorem nat_min : Primrec₂ (@min ℕ _) :=
  ite nat_le fst snd
#align primrec.nat_min Primrec.nat_min

/- warning: primrec.nat_max -> Primrec.nat_max is a dubious translation:
lean 3 declaration is
  Primrec₂.{0, 0, 0} Nat Nat Nat (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (LinearOrder.max.{0} Nat Nat.linearOrder)
but is expected to have type
  Primrec₂.{0, 0, 0} Nat Nat Nat (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Max.max.{0} Nat Nat.instMaxNat)
Case conversion may be inaccurate. Consider using '#align primrec.nat_max Primrec.nat_maxₓ'. -/
theorem nat_max : Primrec₂ (@max ℕ _) :=
  ite (nat_le.comp Primrec.fst Primrec.snd) snd fst
#align primrec.nat_max Primrec.nat_max

#print Primrec.dom_bool /-
theorem dom_bool (f : Bool → α) : Primrec f :=
  (cond Primrec.id (const (f true)) (const (f false))).of_eq fun b => by cases b <;> rfl
#align primrec.dom_bool Primrec.dom_bool
-/

#print Primrec.dom_bool₂ /-
theorem dom_bool₂ (f : Bool → Bool → α) : Primrec₂ f :=
  (cond fst ((dom_bool (f true)).comp snd) ((dom_bool (f false)).comp snd)).of_eq fun ⟨a, b⟩ => by
    cases a <;> rfl
#align primrec.dom_bool₂ Primrec.dom_bool₂
-/

#print Primrec.not /-
protected theorem not : Primrec not :=
  dom_bool _
#align primrec.bnot Primrec.not
-/

#print Primrec.and /-
protected theorem and : Primrec₂ and :=
  dom_bool₂ _
#align primrec.band Primrec.and
-/

#print Primrec.or /-
protected theorem or : Primrec₂ or :=
  dom_bool₂ _
#align primrec.bor Primrec.or
-/

#print PrimrecPred.not /-
protected theorem not {p : α → Prop} [DecidablePred p] (hp : PrimrecPred p) :
    PrimrecPred fun a => ¬p a :=
  (Primrec.not.comp hp).of_eq fun n => by simp
#align primrec.not PrimrecPred.not
-/

#print PrimrecPred.and /-
protected theorem and {p q : α → Prop} [DecidablePred p] [DecidablePred q] (hp : PrimrecPred p)
    (hq : PrimrecPred q) : PrimrecPred fun a => p a ∧ q a :=
  (Primrec.and.comp hp hq).of_eq fun n => by simp
#align primrec.and PrimrecPred.and
-/

#print PrimrecPred.or /-
protected theorem or {p q : α → Prop} [DecidablePred p] [DecidablePred q] (hp : PrimrecPred p)
    (hq : PrimrecPred q) : PrimrecPred fun a => p a ∨ q a :=
  (Primrec.or.comp hp hq).of_eq fun n => by simp
#align primrec.or PrimrecPred.or
-/

#print Primrec.eq /-
protected theorem eq [DecidableEq α] : PrimrecRel (@Eq α) :=
  have : PrimrecRel fun a b : ℕ => a = b :=
    (PrimrecPred.and nat_le nat_le.symm).of_eq fun a => by simp [le_antisymm_iff]
  (this.comp₂ (Primrec.encode.comp₂ Primrec₂.left) (Primrec.encode.comp₂ Primrec₂.right)).of_eq
    fun a b => encode_injective.eq_iff
#align primrec.eq Primrec.eq
-/

/- warning: primrec.nat_lt -> Primrec.nat_lt is a dubious translation:
lean 3 declaration is
  PrimrecRel.{0, 0} Nat Nat (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (LT.lt.{0} Nat Nat.hasLt) (fun (a : Nat) (b : Nat) => Nat.decidableLt a b)
but is expected to have type
  PrimrecRel.{0, 0} Nat Nat (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (fun (x._@.Mathlib.Computability.Primrec._hyg.6908 : Nat) (x._@.Mathlib.Computability.Primrec._hyg.6910 : Nat) => LT.lt.{0} Nat instLTNat x._@.Mathlib.Computability.Primrec._hyg.6908 x._@.Mathlib.Computability.Primrec._hyg.6910) (fun (a : Nat) (b : Nat) => Nat.decLt a b)
Case conversion may be inaccurate. Consider using '#align primrec.nat_lt Primrec.nat_ltₓ'. -/
theorem nat_lt : PrimrecRel ((· < ·) : ℕ → ℕ → Prop) :=
  (nat_le.comp snd fst).Not.of_eq fun p => by simp
#align primrec.nat_lt Primrec.nat_lt

/- warning: primrec.option_guard -> Primrec.option_guard is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {p : α -> β -> Prop} [_inst_6 : forall (a : α) (b : β), Decidable (p a b)], (PrimrecRel.{u1, u2} α β _inst_1 _inst_2 p (fun (a : α) (b : β) => _inst_6 a b)) -> (forall {f : α -> β}, (Primrec.{u1, u2} α β _inst_1 _inst_2 f) -> (Primrec.{u1, u2} α (Option.{u2} β) _inst_1 (Primcodable.option.{u2} β _inst_2) (fun (a : α) => Option.guard.{u2} β (p a) (fun (a_1 : β) => _inst_6 a a_1) (f a))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {p : α -> β -> Prop} [_inst_6 : forall (a : α) (b : β), Decidable (p a b)], (PrimrecRel.{u2, u1} α β _inst_1 _inst_2 p (fun (a : α) (b : β) => _inst_6 a b)) -> (forall {f : α -> β}, (Primrec.{u2, u1} α β _inst_1 _inst_2 f) -> (Primrec.{u2, u1} α (Option.{u1} β) _inst_1 (Primcodable.option.{u1} β _inst_2) (fun (a : α) => Option.guard.{u1} β (p a) (fun (a_1 : β) => _inst_6 a a_1) (f a))))
Case conversion may be inaccurate. Consider using '#align primrec.option_guard Primrec.option_guardₓ'. -/
theorem option_guard {p : α → β → Prop} [∀ a b, Decidable (p a b)] (hp : PrimrecRel p) {f : α → β}
    (hf : Primrec f) : Primrec fun a => Option.guard (p a) (f a) :=
  ite (hp.comp Primrec.id hf) (option_some_iff.2 hf) (const none)
#align primrec.option_guard Primrec.option_guard

/- warning: primrec.option_orelse -> Primrec.option_orElse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Primcodable.{u1} α], Primrec₂.{u1, u1, u1} (Option.{u1} α) (Option.{u1} α) (Option.{u1} α) (Primcodable.option.{u1} α _inst_1) (Primcodable.option.{u1} α _inst_1) (Primcodable.option.{u1} α _inst_1) (HasOrelse.orelse.{u1, u1} Option.{u1} (Alternative.toHasOrelse.{u1, u1} Option.{u1} Option.alternative.{u1}) α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Primcodable.{u1} α], Primrec₂.{u1, u1, u1} (Option.{u1} α) (Option.{u1} α) (Option.{u1} α) (Primcodable.option.{u1} α _inst_1) (Primcodable.option.{u1} α _inst_1) (Primcodable.option.{u1} α _inst_1) (fun (x._@.Mathlib.Computability.Primrec._hyg.7041 : Option.{u1} α) (x._@.Mathlib.Computability.Primrec._hyg.7043 : Option.{u1} α) => HOrElse.hOrElse.{u1, u1, u1} (Option.{u1} α) (Option.{u1} α) (Option.{u1} α) (instHOrElse.{u1} (Option.{u1} α) (Option.instOrElseOption.{u1} α)) x._@.Mathlib.Computability.Primrec._hyg.7041 (fun (x._@.Mathlib.Computability.Primrec._hyg.7053 : Unit) => x._@.Mathlib.Computability.Primrec._hyg.7043))
Case conversion may be inaccurate. Consider using '#align primrec.option_orelse Primrec.option_orElseₓ'. -/
theorem option_orElse : Primrec₂ ((· <|> ·) : Option α → Option α → Option α) :=
  (option_cases fst snd (fst.comp fst).to₂).of_eq fun ⟨o₁, o₂⟩ => by cases o₁ <;> cases o₂ <;> rfl
#align primrec.option_orelse Primrec.option_orElse

#print Primrec.decode₂ /-
protected theorem decode₂ : Primrec (decode₂ α) :=
  option_bind Primrec.decode <|
    option_guard ((@Primrec.eq _ _ Nat.decidableEq).comp (encode_iff.2 snd) (fst.comp fst)) snd
#align primrec.decode₂ Primrec.decode₂
-/

/- warning: primrec.list_find_index₁ -> Primrec.list_findIdx₁ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {p : α -> β -> Prop} [_inst_6 : forall (a : α) (b : β), Decidable (p a b)], (PrimrecRel.{u1, u2} α β _inst_1 _inst_2 p (fun (a : α) (b : β) => _inst_6 a b)) -> (forall (l : List.{u2} β), Primrec.{u1, 0} α Nat _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (fun (a : α) => List.findIndex.{u2} β (p a) (fun (a_1 : β) => _inst_6 a a_1) l))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] {p : α -> β -> Bool}, (Primrec₂.{u2, u1, 0} α β Bool _inst_1 _inst_2 Primcodable.bool p) -> (forall (hp : List.{u1} β), Primrec.{u2, 0} α Nat _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (fun (a : α) => List.findIdx.{u1} β (p a) hp))
Case conversion may be inaccurate. Consider using '#align primrec.list_find_index₁ Primrec.list_findIdx₁ₓ'. -/
theorem list_findIdx₁ {p : α → β → Prop} [∀ a b, Decidable (p a b)] (hp : PrimrecRel p) :
    ∀ l : List β, Primrec fun a => l.findIndex (p a)
  | [] => const 0
  | a :: l => ite (hp.comp Primrec.id (const a)) (const 0) (succ.comp (list_find_index₁ l))
#align primrec.list_find_index₁ Primrec.list_findIdx₁

#print Primrec.list_indexOf₁ /-
theorem list_indexOf₁ [DecidableEq α] (l : List α) : Primrec fun a => l.indexOfₓ a :=
  list_findIdx₁ Primrec.eq l
#align primrec.list_index_of₁ Primrec.list_indexOf₁
-/

/- warning: primrec.dom_fintype -> Primrec.dom_fintype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_5 : Primcodable.{u2} σ] [_inst_6 : Fintype.{u1} α] (f : α -> σ), Primrec.{u1, u2} α σ _inst_1 _inst_5 f
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_5 : Primcodable.{u1} σ] [_inst_6 : Fintype.{u2} α] (f : α -> σ), Primrec.{u2, u1} α σ _inst_1 _inst_5 f
Case conversion may be inaccurate. Consider using '#align primrec.dom_fintype Primrec.dom_fintypeₓ'. -/
theorem dom_fintype [Fintype α] (f : α → σ) : Primrec f :=
  let ⟨l, nd, m⟩ := Finite.exists_univ_list α
  option_some_iff.1 <| by
    haveI := decidable_eq_of_encodable α
    refine' ((list_nth₁ (l.map f)).comp (list_index_of₁ l)).of_eq fun a => _
    rw [List.get?_map, List.nthLe_get? (List.indexOf_lt_length.2 (m _)), List.indexOf_nthLe] <;> rfl
#align primrec.dom_fintype Primrec.dom_fintype

/- warning: primrec.nat_bodd_div2 clashes with [anonymous] -> [anonymous]
warning: primrec.nat_bodd_div2 -> [anonymous] is a dubious translation:
lean 3 declaration is
  Primrec.{0, 0} Nat (Prod.{0, 0} Bool Nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.prod.{0, 0} Bool Nat Primcodable.bool (Primcodable.ofDenumerable.{0} Nat Denumerable.nat)) Nat.boddDiv2
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}}, (Nat -> α -> β) -> Nat -> (List.{u} α) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align primrec.nat_bodd_div2 [anonymous]ₓ'. -/
theorem [anonymous] : Primrec Nat.boddDiv2 :=
  (nat_elim' Primrec.id (const (false, 0))
        (((cond fst (pair (const false) (succ.comp snd)) (pair (const true) snd)).comp snd).comp
            snd).to₂).of_eq
    fun n => by
    simp [-Nat.boddDiv2_eq]
    induction' n with n IH; · rfl
    simp [-Nat.boddDiv2_eq, Nat.boddDiv2, *]
    rcases Nat.boddDiv2 n with ⟨_ | _, m⟩ <;> simp [Nat.boddDiv2]
#align primrec.nat_bodd_div2 [anonymous]

#print Primrec.nat_bodd /-
theorem nat_bodd : Primrec Nat.bodd :=
  fst.comp [anonymous]
#align primrec.nat_bodd Primrec.nat_bodd
-/

#print Primrec.nat_div2 /-
theorem nat_div2 : Primrec Nat.div2 :=
  snd.comp [anonymous]
#align primrec.nat_div2 Primrec.nat_div2
-/

/- warning: primrec.nat_bit0 -> Primrec.nat_double is a dubious translation:
lean 3 declaration is
  Primrec.{0, 0} Nat Nat (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (bit0.{0} Nat Nat.hasAdd)
but is expected to have type
  Primrec.{0, 0} Nat Nat (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (fun (n : Nat) => HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) n)
Case conversion may be inaccurate. Consider using '#align primrec.nat_bit0 Primrec.nat_doubleₓ'. -/
theorem nat_double : Primrec (@bit0 ℕ _) :=
  nat_add.comp Primrec.id Primrec.id
#align primrec.nat_bit0 Primrec.nat_double

/- warning: primrec.nat_bit1 -> Primrec.nat_double_succ is a dubious translation:
lean 3 declaration is
  Primrec.{0, 0} Nat Nat (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (bit1.{0} Nat Nat.hasOne Nat.hasAdd)
but is expected to have type
  Primrec.{0, 0} Nat Nat (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (fun (n : Nat) => HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) n) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align primrec.nat_bit1 Primrec.nat_double_succₓ'. -/
theorem nat_double_succ : Primrec (@bit1 ℕ _ _) :=
  nat_add.comp nat_double (const 1)
#align primrec.nat_bit1 Primrec.nat_double_succ

theorem nat_bit : Primrec₂ Nat.bit :=
  (cond Primrec.fst (nat_double_succ.comp Primrec.snd) (nat_double.comp Primrec.snd)).of_eq fun n =>
    by cases n.1 <;> rfl
#align primrec.nat_bit Primrec.nat_bit

/- warning: primrec.nat_div_mod clashes with [anonymous] -> [anonymous]
warning: primrec.nat_div_mod -> [anonymous] is a dubious translation:
lean 3 declaration is
  Primrec₂.{0, 0, 0} Nat Nat (Prod.{0, 0} Nat Nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.prod.{0, 0} Nat Nat (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.ofDenumerable.{0} Nat Denumerable.nat)) (fun (n : Nat) (k : Nat) => Prod.mk.{0, 0} Nat Nat (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.hasDiv) n k) (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.hasMod) n k))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}}, (Nat -> α -> β) -> Nat -> (List.{u} α) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align primrec.nat_div_mod [anonymous]ₓ'. -/
theorem [anonymous] : Primrec₂ fun n k : ℕ => (n / k, n % k) :=
  let f (a : ℕ × ℕ) : ℕ × ℕ :=
    a.1.elim (0, 0) fun _ IH =>
      if Nat.succ IH.2 = a.2 then (Nat.succ IH.1, 0) else (IH.1, Nat.succ IH.2)
  have hf : Primrec f :=
    nat_elim' fst (const (0, 0)) <|
      ((ite ((@Primrec.eq ℕ _ _).comp (succ.comp <| snd.comp snd) fst)
              (pair (succ.comp <| fst.comp snd) (const 0))
              (pair (fst.comp snd) (succ.comp <| snd.comp snd))).comp
          (pair (snd.comp fst) (snd.comp snd))).to₂
  suffices ∀ k n, (n / k, n % k) = f (n, k) from hf.of_eq fun ⟨m, n⟩ => by simp [this]
  fun k n =>
  by
  have :
    (f (n, k)).2 + k * (f (n, k)).1 = n ∧ (0 < k → (f (n, k)).2 < k) ∧ (k = 0 → (f (n, k)).1 = 0) :=
    by
    induction' n with n IH
    · exact ⟨rfl, id, fun _ => rfl⟩
    rw [fun n : ℕ =>
      show
        f (n.succ, k) =
          _root_.ite ((f (n, k)).2.succ = k) (Nat.succ (f (n, k)).1, 0)
            ((f (n, k)).1, (f (n, k)).2.succ)
        from rfl]
    by_cases h : (f (n, k)).2.succ = k <;> simp [h]
    · have := congr_arg Nat.succ IH.1
      refine' ⟨_, fun k0 => Nat.noConfusion (h.trans k0)⟩
      rwa [← Nat.succ_add, h, add_comm, ← Nat.mul_succ] at this
    · exact ⟨by rw [Nat.succ_add, IH.1], fun k0 => lt_of_le_of_ne (IH.2.1 k0) h, IH.2.2⟩
  revert this
  cases' f (n, k) with D M
  simp
  intro h₁ h₂ h₃
  cases Nat.eq_zero_or_pos k
  · simp [h, h₃ h] at h₁⊢
    simp [h₁]
  · exact (Nat.div_mod_unique h).2 ⟨h₁, h₂ h⟩
#align primrec.nat_div_mod [anonymous]

#print Primrec.nat_div /-
theorem nat_div : Primrec₂ ((· / ·) : ℕ → ℕ → ℕ) :=
  fst.comp₂ [anonymous]
#align primrec.nat_div Primrec.nat_div
-/

#print Primrec.nat_mod /-
theorem nat_mod : Primrec₂ ((· % ·) : ℕ → ℕ → ℕ) :=
  snd.comp₂ [anonymous]
#align primrec.nat_mod Primrec.nat_mod
-/

end Primrec

section

variable {α : Type _} {β : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable σ]

variable (H : Nat.Primrec fun n => Encodable.encode (decode (List β) n))

include H

open Primrec

private def prim : Primcodable (List β) :=
  ⟨H⟩
#align prim prim

private theorem list_cases' {f : α → List β} {g : α → σ} {h : α → β × List β → σ}
    (hf :
      haveI := prim H
      Primrec f)
    (hg : Primrec g)
    (hh :
      haveI := prim H
      Primrec₂ h) :
    @Primrec _ σ _ _ fun a => List.casesOn (f a) (g a) fun b l => h a (b, l) :=
  letI := prim H
  have :
    @Primrec _ (Option σ) _ _ fun a =>
      (decode (Option (β × List β)) (encode (f a))).map fun o => Option.casesOn o (g a) (h a) :=
    ((@map_decode_iff _ (Option (β × List β)) _ _ _ _ _).2 <|
          to₂ <|
            option_cases snd (hg.comp fst) (hh.comp₂ (fst.comp₂ Primrec₂.left) Primrec₂.right)).comp
      Primrec.id (encode_iff.2 hf)
  option_some_iff.1 <| this.of_eq fun a => by cases' f a with b l <;> simp [encodek] <;> rfl
#align list_cases' list_cases'

private theorem list_foldl' {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf :
      haveI := prim H
      Primrec f)
    (hg : Primrec g)
    (hh :
      haveI := prim H
      Primrec₂ h) :
    Primrec fun a => (f a).foldl (fun s b => h a (s, b)) (g a) :=
  letI := prim H
  let G (a : α) (IH : σ × List β) : σ × List β := List.casesOn IH.2 IH fun b l => (h a (IH.1, b), l)
  let F (a : α) (n : ℕ) := (G a^[n]) (g a, f a)
  have : Primrec fun a => (F a (encode (f a))).1 :=
    fst.comp <|
      nat_iterate (encode_iff.2 hf) (pair hg hf) <|
        list_cases' H (snd.comp snd) snd <|
          to₂ <|
            pair (hh.comp (fst.comp fst) <| pair ((fst.comp snd).comp fst) (fst.comp snd))
              (snd.comp snd)
  this.of_eq fun a =>
    by
    have :
      ∀ n, F a n = ((List.take n (f a)).foldl (fun s b => h a (s, b)) (g a), List.drop n (f a)) :=
      by
      intro
      simp [F]
      generalize f a = l
      generalize g a = x
      induction' n with n IH generalizing l x
      · rfl
      simp
      cases' l with b l <;> simp [IH]
    rw [this, List.take_all_of_le (length_le_encode _)]
#align list_foldl' list_foldl'

private theorem list_cons' :
    haveI := prim H
    Primrec₂ (@List.cons β) :=
  letI := prim H
  encode_iff.1 (succ.comp <| primrec₂.mkpair.comp (encode_iff.2 fst) (encode_iff.2 snd))
#align list_cons' list_cons'

private theorem list_reverse' :
    haveI := prim H
    Primrec (@List.reverse β) :=
  letI := prim H
  (list_foldl' H Primrec.id (const []) <| to₂ <| ((list_cons' H).comp snd fst).comp snd).of_eq
    (suffices ∀ l r, List.foldl (fun (s : List β) (b : β) => b :: s) r l = List.reverseAux l r from
      fun l => this l []
    fun l => by induction l <;> simp [*, List.reverseAux])
#align list_reverse' list_reverse'

end

namespace Primcodable

variable {α : Type _} {β : Type _}

variable [Primcodable α] [Primcodable β]

open Primrec

#print Primcodable.sum /-
instance sum : Primcodable (Sum α β) :=
  ⟨Primrec.nat_iff.1 <|
      (encode_iff.2
            (cond nat_bodd
              (((@Primrec.decode β _).comp nat_div2).option_map <|
                to₂ <| nat_bit.comp (const true) (Primrec.encode.comp snd))
              (((@Primrec.decode α _).comp nat_div2).option_map <|
                to₂ <| nat_bit.comp (const false) (Primrec.encode.comp snd)))).of_eq
        fun n =>
        show _ = encode (decodeSum n) by
          simp [decode_sum]
          cases Nat.bodd n <;> simp [decode_sum]
          · cases decode α n.div2 <;> rfl
          · cases decode β n.div2 <;> rfl⟩
#align primcodable.sum Primcodable.sum
-/

#print Primcodable.list /-
instance list : Primcodable (List α) :=
  ⟨letI H := Primcodable.prim (List ℕ)
    have : Primrec₂ fun (a : α) (o : Option (List ℕ)) => o.map (List.cons (encode a)) :=
      option_map snd <| (list_cons' H).comp ((@Primrec.encode α _).comp (fst.comp fst)) snd
    have :
      Primrec fun n =>
        (of_nat (List ℕ) n).reverse.foldl
          (fun o m => (decode α m).bind fun a => o.map (List.cons (encode a))) (some []) :=
      list_foldl' H ((list_reverse' H).comp (Primrec.ofNat (List ℕ))) (const (some []))
        (Primrec.comp₂ (bind_decode_iff.2 <| Primrec₂.swap this) Primrec₂.right)
    nat_iff.1 <|
      (encode_iff.2 this).of_eq fun n => by
        rw [List.foldl_reverse]
        apply Nat.case_strong_induction_on n; · simp
        intro n IH; simp
        cases' decode α n.unpair.1 with a; · rfl
        simp
        suffices :
          ∀ (o : Option (List ℕ)) (p) (_ : encode o = encode p),
            encode (Option.map (List.cons (encode a)) o) = encode (Option.map (List.cons a) p)
        exact this _ _ (IH _ (Nat.unpair_right_le n))
        intro o p IH
        cases o <;> cases p <;> injection IH with h
        exact congr_arg (fun k => (Nat.pair (encode a) k).succ.succ) h⟩
#align primcodable.list Primcodable.list
-/

end Primcodable

namespace Primrec

variable {α : Type _} {β : Type _} {γ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

/- warning: primrec.sum_inl -> Primrec.sum_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β], Primrec.{u1, max u1 u2} α (Sum.{u1, u2} α β) _inst_1 (Primcodable.sum.{u1, u2} α β _inst_1 _inst_2) (Sum.inl.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β], Primrec.{u2, max u2 u1} α (Sum.{u2, u1} α β) _inst_1 (Primcodable.sum.{u2, u1} α β _inst_1 _inst_2) (Sum.inl.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align primrec.sum_inl Primrec.sum_inlₓ'. -/
theorem sum_inl : Primrec (@Sum.inl α β) :=
  encode_iff.1 <| nat_double.comp Primrec.encode
#align primrec.sum_inl Primrec.sum_inl

#print Primrec.sum_inr /-
theorem sum_inr : Primrec (@Sum.inr α β) :=
  encode_iff.1 <| nat_double_succ.comp Primrec.encode
#align primrec.sum_inr Primrec.sum_inr
-/

/- warning: primrec.sum_cases -> Primrec.sum_cases is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {σ : Type.{u4}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] [_inst_4 : Primcodable.{u4} σ] {f : α -> (Sum.{u2, u3} β γ)} {g : α -> β -> σ} {h : α -> γ -> σ}, (Primrec.{u1, max u2 u3} α (Sum.{u2, u3} β γ) _inst_1 (Primcodable.sum.{u2, u3} β γ _inst_2 _inst_3) f) -> (Primrec₂.{u1, u2, u4} α β σ _inst_1 _inst_2 _inst_4 g) -> (Primrec₂.{u1, u3, u4} α γ σ _inst_1 _inst_3 _inst_4 h) -> (Primrec.{u1, u4} α σ _inst_1 _inst_4 (fun (a : α) => Sum.casesOn.{succ u4, u2, u3} β γ (fun (_x : Sum.{u2, u3} β γ) => σ) (f a) (g a) (h a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u4}} {γ : Type.{u3}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u4} β] [_inst_3 : Primcodable.{u3} γ] [_inst_4 : Primcodable.{u1} σ] {f : α -> (Sum.{u4, u3} β γ)} {g : α -> β -> σ} {h : α -> γ -> σ}, (Primrec.{u2, max u4 u3} α (Sum.{u4, u3} β γ) _inst_1 (Primcodable.sum.{u4, u3} β γ _inst_2 _inst_3) f) -> (Primrec₂.{u2, u4, u1} α β σ _inst_1 _inst_2 _inst_4 g) -> (Primrec₂.{u2, u3, u1} α γ σ _inst_1 _inst_3 _inst_4 h) -> (Primrec.{u2, u1} α σ _inst_1 _inst_4 (fun (a : α) => Sum.casesOn.{succ u1, u4, u3} β γ (fun (_x : Sum.{u4, u3} β γ) => σ) (f a) (g a) (h a)))
Case conversion may be inaccurate. Consider using '#align primrec.sum_cases Primrec.sum_casesₓ'. -/
theorem sum_cases {f : α → Sum β γ} {g : α → β → σ} {h : α → γ → σ} (hf : Primrec f)
    (hg : Primrec₂ g) (hh : Primrec₂ h) : @Primrec _ σ _ _ fun a => Sum.casesOn (f a) (g a) (h a) :=
  option_some_iff.1 <|
    (cond (nat_bodd.comp <| encode_iff.2 hf)
          (option_map (Primrec.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hh)
          (option_map (Primrec.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hg)).of_eq
      fun a => by cases' f a with b c <;> simp [Nat.div2_bit, Nat.bodd_bit, encodek] <;> rfl
#align primrec.sum_cases Primrec.sum_cases

#print Primrec.list_cons /-
theorem list_cons : Primrec₂ (@List.cons α) :=
  list_cons' (Primcodable.prim _)
#align primrec.list_cons Primrec.list_cons
-/

/- warning: primrec.list_cases -> Primrec.list_cases is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u3} σ] {f : α -> (List.{u2} β)} {g : α -> σ} {h : α -> (Prod.{u2, u2} β (List.{u2} β)) -> σ}, (Primrec.{u1, u2} α (List.{u2} β) _inst_1 (Primcodable.list.{u2} β _inst_2) f) -> (Primrec.{u1, u3} α σ _inst_1 _inst_4 g) -> (Primrec₂.{u1, u2, u3} α (Prod.{u2, u2} β (List.{u2} β)) σ _inst_1 (Primcodable.prod.{u2, u2} β (List.{u2} β) _inst_2 (Primcodable.list.{u2} β _inst_2)) _inst_4 h) -> (Primrec.{u1, u3} α σ _inst_1 _inst_4 (fun (a : α) => List.casesOn.{succ u3, u2} β (fun (_x : List.{u2} β) => σ) (f a) (g a) (fun (b : β) (l : List.{u2} β) => h a (Prod.mk.{u2, u2} β (List.{u2} β) b l))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u3} β] [_inst_4 : Primcodable.{u1} σ] {f : α -> (List.{u3} β)} {g : α -> σ} {h : α -> (Prod.{u3, u3} β (List.{u3} β)) -> σ}, (Primrec.{u2, u3} α (List.{u3} β) _inst_1 (Primcodable.list.{u3} β _inst_2) f) -> (Primrec.{u2, u1} α σ _inst_1 _inst_4 g) -> (Primrec₂.{u2, u3, u1} α (Prod.{u3, u3} β (List.{u3} β)) σ _inst_1 (Primcodable.prod.{u3, u3} β (List.{u3} β) _inst_2 (Primcodable.list.{u3} β _inst_2)) _inst_4 h) -> (Primrec.{u2, u1} α σ _inst_1 _inst_4 (fun (a : α) => List.casesOn.{succ u1, u3} β (fun (_x : List.{u3} β) => σ) (f a) (g a) (fun (b : β) (l : List.{u3} β) => h a (Prod.mk.{u3, u3} β (List.{u3} β) b l))))
Case conversion may be inaccurate. Consider using '#align primrec.list_cases Primrec.list_casesₓ'. -/
theorem list_cases {f : α → List β} {g : α → σ} {h : α → β × List β → σ} :
    Primrec f →
      Primrec g →
        Primrec₂ h → @Primrec _ σ _ _ fun a => List.casesOn (f a) (g a) fun b l => h a (b, l) :=
  list_cases' (Primcodable.prim _)
#align primrec.list_cases Primrec.list_cases

/- warning: primrec.list_foldl -> Primrec.list_foldl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u3} σ] {f : α -> (List.{u2} β)} {g : α -> σ} {h : α -> (Prod.{u3, u2} σ β) -> σ}, (Primrec.{u1, u2} α (List.{u2} β) _inst_1 (Primcodable.list.{u2} β _inst_2) f) -> (Primrec.{u1, u3} α σ _inst_1 _inst_4 g) -> (Primrec₂.{u1, max u3 u2, u3} α (Prod.{u3, u2} σ β) σ _inst_1 (Primcodable.prod.{u3, u2} σ β _inst_4 _inst_2) _inst_4 h) -> (Primrec.{u1, u3} α σ _inst_1 _inst_4 (fun (a : α) => List.foldl.{u3, u2} σ β (fun (s : σ) (b : β) => h a (Prod.mk.{u3, u2} σ β s b)) (g a) (f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u3} β] [_inst_4 : Primcodable.{u2} σ] {f : α -> (List.{u3} β)} {g : α -> σ} {h : α -> (Prod.{u2, u3} σ β) -> σ}, (Primrec.{u1, u3} α (List.{u3} β) _inst_1 (Primcodable.list.{u3} β _inst_2) f) -> (Primrec.{u1, u2} α σ _inst_1 _inst_4 g) -> (Primrec₂.{u1, max u3 u2, u2} α (Prod.{u2, u3} σ β) σ _inst_1 (Primcodable.prod.{u2, u3} σ β _inst_4 _inst_2) _inst_4 h) -> (Primrec.{u1, u2} α σ _inst_1 _inst_4 (fun (a : α) => List.foldl.{u2, u3} σ β (fun (s : σ) (b : β) => h a (Prod.mk.{u2, u3} σ β s b)) (g a) (f a)))
Case conversion may be inaccurate. Consider using '#align primrec.list_foldl Primrec.list_foldlₓ'. -/
theorem list_foldl {f : α → List β} {g : α → σ} {h : α → σ × β → σ} :
    Primrec f →
      Primrec g → Primrec₂ h → Primrec fun a => (f a).foldl (fun s b => h a (s, b)) (g a) :=
  list_foldl' (Primcodable.prim _)
#align primrec.list_foldl Primrec.list_foldl

#print Primrec.list_reverse /-
theorem list_reverse : Primrec (@List.reverse α) :=
  list_reverse' (Primcodable.prim _)
#align primrec.list_reverse Primrec.list_reverse
-/

/- warning: primrec.list_foldr -> Primrec.list_foldr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u3} σ] {f : α -> (List.{u2} β)} {g : α -> σ} {h : α -> (Prod.{u2, u3} β σ) -> σ}, (Primrec.{u1, u2} α (List.{u2} β) _inst_1 (Primcodable.list.{u2} β _inst_2) f) -> (Primrec.{u1, u3} α σ _inst_1 _inst_4 g) -> (Primrec₂.{u1, max u2 u3, u3} α (Prod.{u2, u3} β σ) σ _inst_1 (Primcodable.prod.{u2, u3} β σ _inst_2 _inst_4) _inst_4 h) -> (Primrec.{u1, u3} α σ _inst_1 _inst_4 (fun (a : α) => List.foldr.{u2, u3} β σ (fun (b : β) (s : σ) => h a (Prod.mk.{u2, u3} β σ b s)) (g a) (f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u3} β] [_inst_4 : Primcodable.{u2} σ] {f : α -> (List.{u3} β)} {g : α -> σ} {h : α -> (Prod.{u3, u2} β σ) -> σ}, (Primrec.{u1, u3} α (List.{u3} β) _inst_1 (Primcodable.list.{u3} β _inst_2) f) -> (Primrec.{u1, u2} α σ _inst_1 _inst_4 g) -> (Primrec₂.{u1, max u3 u2, u2} α (Prod.{u3, u2} β σ) σ _inst_1 (Primcodable.prod.{u3, u2} β σ _inst_2 _inst_4) _inst_4 h) -> (Primrec.{u1, u2} α σ _inst_1 _inst_4 (fun (a : α) => List.foldr.{u3, u2} β σ (fun (b : β) (s : σ) => h a (Prod.mk.{u3, u2} β σ b s)) (g a) (f a)))
Case conversion may be inaccurate. Consider using '#align primrec.list_foldr Primrec.list_foldrₓ'. -/
theorem list_foldr {f : α → List β} {g : α → σ} {h : α → β × σ → σ} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec₂ h) :
    Primrec fun a => (f a).foldr (fun b s => h a (b, s)) (g a) :=
  (list_foldl (list_reverse.comp hf) hg <| to₂ <| hh.comp fst <| (pair snd fst).comp snd).of_eq
    fun a => by simp [List.foldl_reverse]
#align primrec.list_foldr Primrec.list_foldr

#print Primrec.list_head? /-
theorem list_head? : Primrec (@List.head? α) :=
  (list_cases Primrec.id (const none) (option_some_iff.2 <| fst.comp snd).to₂).of_eq fun l => by
    cases l <;> rfl
#align primrec.list_head' Primrec.list_head?
-/

#print Primrec.list_headI /-
theorem list_headI [Inhabited α] : Primrec (@List.headI α _) :=
  (option_iget.comp list_head?).of_eq fun l => l.head!_eq_head?.symm
#align primrec.list_head Primrec.list_headI
-/

#print Primrec.list_tail /-
theorem list_tail : Primrec (@List.tail α) :=
  (list_cases Primrec.id (const []) (snd.comp snd).to₂).of_eq fun l => by cases l <;> rfl
#align primrec.list_tail Primrec.list_tail
-/

/- warning: primrec.list_rec -> Primrec.list_rec is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u3} σ] {f : α -> (List.{u2} β)} {g : α -> σ} {h : α -> (Prod.{u2, max u2 u3} β (Prod.{u2, u3} (List.{u2} β) σ)) -> σ}, (Primrec.{u1, u2} α (List.{u2} β) _inst_1 (Primcodable.list.{u2} β _inst_2) f) -> (Primrec.{u1, u3} α σ _inst_1 _inst_4 g) -> (Primrec₂.{u1, max u2 u3, u3} α (Prod.{u2, max u2 u3} β (Prod.{u2, u3} (List.{u2} β) σ)) σ _inst_1 (Primcodable.prod.{u2, max u2 u3} β (Prod.{u2, u3} (List.{u2} β) σ) _inst_2 (Primcodable.prod.{u2, u3} (List.{u2} β) σ (Primcodable.list.{u2} β _inst_2) _inst_4)) _inst_4 h) -> (Primrec.{u1, u3} α σ _inst_1 _inst_4 (fun (a : α) => List.recOn.{succ u3, u2} β (fun (_x : List.{u2} β) => σ) (f a) (g a) (fun (b : β) (l : List.{u2} β) (IH : σ) => h a (Prod.mk.{u2, max u2 u3} β (Prod.{u2, u3} (List.{u2} β) σ) b (Prod.mk.{u2, u3} (List.{u2} β) σ l IH)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u3} β] [_inst_4 : Primcodable.{u2} σ] {f : α -> (List.{u3} β)} {g : α -> σ} {h : α -> (Prod.{u3, max u2 u3} β (Prod.{u3, u2} (List.{u3} β) σ)) -> σ}, (Primrec.{u1, u3} α (List.{u3} β) _inst_1 (Primcodable.list.{u3} β _inst_2) f) -> (Primrec.{u1, u2} α σ _inst_1 _inst_4 g) -> (Primrec₂.{u1, max u3 u2, u2} α (Prod.{u3, max u2 u3} β (Prod.{u3, u2} (List.{u3} β) σ)) σ _inst_1 (Primcodable.prod.{u3, max u3 u2} β (Prod.{u3, u2} (List.{u3} β) σ) _inst_2 (Primcodable.prod.{u3, u2} (List.{u3} β) σ (Primcodable.list.{u3} β _inst_2) _inst_4)) _inst_4 h) -> (Primrec.{u1, u2} α σ _inst_1 _inst_4 (fun (a : α) => List.recOn.{succ u2, u3} β (fun (_x : List.{u3} β) => σ) (f a) (g a) (fun (b : β) (l : List.{u3} β) (IH : σ) => h a (Prod.mk.{u3, max u3 u2} β (Prod.{u3, u2} (List.{u3} β) σ) b (Prod.mk.{u3, u2} (List.{u3} β) σ l IH)))))
Case conversion may be inaccurate. Consider using '#align primrec.list_rec Primrec.list_recₓ'. -/
theorem list_rec {f : α → List β} {g : α → σ} {h : α → β × List β × σ → σ} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec₂ h) :
    @Primrec _ σ _ _ fun a => List.recOn (f a) (g a) fun b l IH => h a (b, l, IH) :=
  let F (a : α) := (f a).foldr (fun (b : β) (s : List β × σ) => (b :: s.1, h a (b, s))) ([], g a)
  have : Primrec F :=
    list_foldr hf (pair (const []) hg) <|
      to₂ <| pair ((list_cons.comp fst (fst.comp snd)).comp snd) hh
  (snd.comp this).of_eq fun a =>
    by
    suffices F a = (f a, List.recOn (f a) (g a) fun b l IH => h a (b, l, IH)) by rw [this]
    simp [F]
    induction' f a with b l IH <;> simp [*]
#align primrec.list_rec Primrec.list_rec

#print Primrec.list_get? /-
theorem list_get? : Primrec₂ (@List.get? α) :=
  let F (l : List α) (n : ℕ) :=
    l.foldl
      (fun (s : Sum ℕ α) (a : α) =>
        Sum.casesOn s (@Nat.casesOn (Sum ℕ α) (Sum.inr a) Sum.inl) Sum.inr)
      (Sum.inl n)
  have hF : Primrec₂ F :=
    list_foldl fst (sum_inl.comp snd)
      ((sum_cases fst (nat_cases snd (sum_inr.comp <| snd.comp fst) (sum_inl.comp snd).to₂).to₂
              (sum_inr.comp snd).to₂).comp
          snd).to₂
  have :
    @Primrec _ (Option α) _ _ fun p : List α × ℕ => Sum.casesOn (F p.1 p.2) (fun _ => none) some :=
    sum_cases hF (const none).to₂ (option_some.comp snd).to₂
  this.to₂.of_eq fun l n => by
    dsimp; symm
    induction' l with a l IH generalizing n; · rfl
    cases' n with n
    · rw [(_ : F (a :: l) 0 = Sum.inr a)]
      · rfl
      clear IH
      dsimp [F]
      induction' l with b l IH <;> simp [*]
    · apply IH
#align primrec.list_nth Primrec.list_get?
-/

#print Primrec.list_getD /-
theorem list_getD (d : α) : Primrec₂ fun l n => List.getD l n d :=
  by
  simp only [List.getD_eq_getD_get?]
  exact option_get_or_else.comp₂ list_nth (const _)
#align primrec.list_nthd Primrec.list_getD
-/

#print Primrec.list_getI /-
theorem list_getI [Inhabited α] : Primrec₂ (@List.getI α _) :=
  list_getD _
#align primrec.list_inth Primrec.list_getI
-/

#print Primrec.list_append /-
theorem list_append : Primrec₂ ((· ++ ·) : List α → List α → List α) :=
  (list_foldr fst snd <| to₂ <| comp (@list_cons α _) snd).to₂.of_eq fun l₁ l₂ => by
    induction l₁ <;> simp [*]
#align primrec.list_append Primrec.list_append
-/

#print Primrec.list_concat /-
theorem list_concat : Primrec₂ fun l (a : α) => l ++ [a] :=
  list_append.comp fst (list_cons.comp snd (const []))
#align primrec.list_concat Primrec.list_concat
-/

/- warning: primrec.list_map -> Primrec.list_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u3} σ] {f : α -> (List.{u2} β)} {g : α -> β -> σ}, (Primrec.{u1, u2} α (List.{u2} β) _inst_1 (Primcodable.list.{u2} β _inst_2) f) -> (Primrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_4 g) -> (Primrec.{u1, u3} α (List.{u3} σ) _inst_1 (Primcodable.list.{u3} σ _inst_4) (fun (a : α) => List.map.{u2, u3} β σ (g a) (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u3} β] [_inst_4 : Primcodable.{u1} σ] {f : α -> (List.{u3} β)} {g : α -> β -> σ}, (Primrec.{u2, u3} α (List.{u3} β) _inst_1 (Primcodable.list.{u3} β _inst_2) f) -> (Primrec₂.{u2, u3, u1} α β σ _inst_1 _inst_2 _inst_4 g) -> (Primrec.{u2, u1} α (List.{u1} σ) _inst_1 (Primcodable.list.{u1} σ _inst_4) (fun (a : α) => List.map.{u3, u1} β σ (g a) (f a)))
Case conversion may be inaccurate. Consider using '#align primrec.list_map Primrec.list_mapₓ'. -/
theorem list_map {f : α → List β} {g : α → β → σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).map (g a) :=
  (list_foldr hf (const []) <|
        to₂ <| list_cons.comp (hg.comp fst (fst.comp snd)) (snd.comp snd)).of_eq
    fun a => by induction f a <;> simp [*]
#align primrec.list_map Primrec.list_map

#print Primrec.list_range /-
theorem list_range : Primrec List.range :=
  (nat_elim' Primrec.id (const []) ((list_concat.comp snd fst).comp snd).to₂).of_eq fun n => by
    simp <;> induction n <;> simp [*, List.range_succ] <;> rfl
#align primrec.list_range Primrec.list_range
-/

#print Primrec.list_join /-
theorem list_join : Primrec (@List.join α) :=
  (list_foldr Primrec.id (const []) <| to₂ <| comp (@list_append α _) snd).of_eq fun l => by
    dsimp <;> induction l <;> simp [*]
#align primrec.list_join Primrec.list_join
-/

#print Primrec.list_length /-
theorem list_length : Primrec (@List.length α) :=
  (list_foldr (@Primrec.id (List α) _) (const 0) <| to₂ <| (succ.comp <| snd.comp snd).to₂).of_eq
    fun l => by dsimp <;> induction l <;> simp [*, -add_comm]
#align primrec.list_length Primrec.list_length
-/

/- warning: primrec.list_find_index -> Primrec.list_findIdx is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {f : α -> (List.{u2} β)} {p : α -> β -> Prop} [_inst_5 : forall (a : α) (b : β), Decidable (p a b)], (Primrec.{u1, u2} α (List.{u2} β) _inst_1 (Primcodable.list.{u2} β _inst_2) f) -> (PrimrecRel.{u1, u2} α β _inst_1 _inst_2 p (fun (a : α) (b : β) => _inst_5 a b)) -> (Primrec.{u1, 0} α Nat _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (fun (a : α) => List.findIndex.{u2} β (p a) (fun (a_1 : β) => _inst_5 a a_1) (f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] {f : α -> (List.{u2} β)} {p : α -> β -> Bool}, (Primrec.{u1, u2} α (List.{u2} β) _inst_1 (Primcodable.list.{u2} β _inst_2) f) -> (Primrec₂.{u1, u2, 0} α β Bool _inst_1 _inst_2 Primcodable.bool p) -> (Primrec.{u1, 0} α Nat _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (fun (a : α) => List.findIdx.{u2} β (p a) (f a)))
Case conversion may be inaccurate. Consider using '#align primrec.list_find_index Primrec.list_findIdxₓ'. -/
theorem list_findIdx {f : α → List β} {p : α → β → Prop} [∀ a b, Decidable (p a b)] (hf : Primrec f)
    (hp : PrimrecRel p) : Primrec fun a => (f a).findIndex (p a) :=
  (list_foldr hf (const 0) <|
        to₂ <| ite (hp.comp fst <| fst.comp snd) (const 0) (succ.comp <| snd.comp snd)).of_eq
    fun a => Eq.symm <| by dsimp <;> induction' f a with b l <;> [rfl, simp [*, List.findIndex]]
#align primrec.list_find_index Primrec.list_findIdx

theorem list_indexOf [DecidableEq α] : Primrec₂ (@List.indexOf α _) :=
  to₂ <| list_findIdx snd <| Primrec.eq.comp₂ (fst.comp fst).to₂ snd.to₂
#align primrec.list_index_of Primrec.list_indexOfₓ

#print Primrec.nat_strong_rec /-
theorem nat_strong_rec (f : α → ℕ → σ) {g : α → List σ → Option σ} (hg : Primrec₂ g)
    (H : ∀ a n, g a ((List.range n).map (f a)) = some (f a n)) : Primrec₂ f :=
  suffices Primrec₂ fun a n => (List.range n).map (f a) from
    Primrec₂.option_some_iff.1 <|
      (list_get?.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq fun a n => by
        simp [List.get?_range (Nat.lt_succ_self n)] <;> rfl
  Primrec₂.option_some_iff.1 <|
    (nat_elim (const (some []))
          (to₂ <|
            option_bind (snd.comp snd) <|
              to₂ <|
                option_map (hg.comp (fst.comp fst) snd)
                  (to₂ <| list_concat.comp (snd.comp fst) snd))).of_eq
      fun a n => by
      simp; induction' n with n IH; · rfl
      simp [IH, H, List.range_succ]
#align primrec.nat_strong_rec Primrec.nat_strong_rec
-/

end Primrec

namespace Primcodable

variable {α : Type _} {β : Type _}

variable [Primcodable α] [Primcodable β]

open Primrec

#print Primcodable.subtype /-
/-- A subtype of a primitive recursive predicate is `primcodable`. -/
def subtype {p : α → Prop} [DecidablePred p] (hp : PrimrecPred p) : Primcodable (Subtype p) :=
  ⟨have : Primrec fun n => (decode α n).bind fun a => Option.guard p a :=
      option_bind Primrec.decode (option_guard (hp.comp snd) snd)
    nat_iff.1 <|
      (encode_iff.2 this).of_eq fun n =>
        show _ = encode ((decode α n).bind fun a => _)
          by
          cases' decode α n with a; · rfl
          dsimp [Option.guard]
          by_cases h : p a <;> simp [h] <;> rfl⟩
#align primcodable.subtype Primcodable.subtype
-/

#print Primcodable.fin /-
instance fin {n} : Primcodable (Fin n) :=
  @ofEquiv _ _ (subtype <| nat_lt.comp Primrec.id (const n)) Fin.equivSubtype
#align primcodable.fin Primcodable.fin
-/

#print Primcodable.vector /-
instance vector {n} : Primcodable (Vector α n) :=
  subtype ((@Primrec.eq _ _ Nat.decidableEq).comp list_length (const _))
#align primcodable.vector Primcodable.vector
-/

#print Primcodable.finArrow /-
instance finArrow {n} : Primcodable (Fin n → α) :=
  ofEquiv _ (Equiv.vectorEquivFin _ _).symm
#align primcodable.fin_arrow Primcodable.finArrow
-/

instance array {n} : Primcodable (Array' n α) :=
  ofEquiv _ (Equiv.arrayEquivFin _ _)
#align primcodable.array Primcodable.array

section Ulower

attribute [local instance] Encodable.decidableRangeEncode Encodable.decidableEqOfEncodable

#print Primcodable.ulower /-
instance ulower : Primcodable (Ulower α) :=
  have : PrimrecPred fun n => Encodable.decode₂ α n ≠ none :=
    PrimrecPred.not
      (Primrec.eq.comp
        (Primrec.option_bind Primrec.decode
          (Primrec.ite (Primrec.eq.comp (Primrec.encode.comp Primrec.snd) Primrec.fst)
            (Primrec.option_some.comp Primrec.snd) (Primrec.const _)))
        (Primrec.const _))
  Primcodable.subtype <| PrimrecPred.of_eq this fun n => decode₂_ne_none_iff
#align primcodable.ulower Primcodable.ulower
-/

end Ulower

end Primcodable

namespace Primrec

variable {α : Type _} {β : Type _} {γ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

#print Primrec.subtype_val /-
theorem subtype_val {p : α → Prop} [DecidablePred p] {hp : PrimrecPred p} :
    haveI := Primcodable.subtype hp
    Primrec (@Subtype.val α p) :=
  by
  letI := Primcodable.subtype hp
  refine' (Primcodable.prim (Subtype p)).of_eq fun n => _
  rcases decode (Subtype p) n with (_ | ⟨a, h⟩) <;> rfl
#align primrec.subtype_val Primrec.subtype_val
-/

#print Primrec.subtype_val_iff /-
theorem subtype_val_iff {p : β → Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α → Subtype p} :
    haveI := Primcodable.subtype hp
    (Primrec fun a => (f a).1) ↔ Primrec f :=
  by
  letI := Primcodable.subtype hp
  refine' ⟨fun h => _, fun hf => subtype_val.comp hf⟩
  refine' Nat.Primrec.of_eq h fun n => _
  cases' decode α n with a; · rfl
  simp; cases f a <;> rfl
#align primrec.subtype_val_iff Primrec.subtype_val_iff
-/

#print Primrec.subtype_mk /-
theorem subtype_mk {p : β → Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α → β}
    {h : ∀ a, p (f a)} (hf : Primrec f) :
    haveI := Primcodable.subtype hp
    Primrec fun a => @Subtype.mk β p (f a) (h a) :=
  subtype_val_iff.1 hf
#align primrec.subtype_mk Primrec.subtype_mk
-/

#print Primrec.option_get /-
theorem option_get {f : α → Option β} {h : ∀ a, (f a).isSome} :
    Primrec f → Primrec fun a => Option.get (h a) :=
  by
  intro hf
  refine' (nat.primrec.pred.comp hf).of_eq fun n => _
  generalize hx : decode α n = x
  cases x <;> simp
#align primrec.option_get Primrec.option_get
-/

#print Primrec.ulower_down /-
theorem ulower_down : Primrec (Ulower.down : α → Ulower α) :=
  letI : ∀ a, Decidable (a ∈ Set.range (encode : α → ℕ)) := decidable_range_encode _
  subtype_mk Primrec.encode
#align primrec.ulower_down Primrec.ulower_down
-/

#print Primrec.ulower_up /-
theorem ulower_up : Primrec (Ulower.up : Ulower α → α) :=
  letI : ∀ a, Decidable (a ∈ Set.range (encode : α → ℕ)) := decidable_range_encode _
  option_get (primrec.decode₂.comp subtype_val)
#align primrec.ulower_up Primrec.ulower_up
-/

#print Primrec.fin_val_iff /-
theorem fin_val_iff {n} {f : α → Fin n} : (Primrec fun a => (f a).1) ↔ Primrec f :=
  by
  let : Primcodable { a // id a < n }; swap
  exact (Iff.trans (by rfl) subtype_val_iff).trans (of_equiv_iff _)
#align primrec.fin_val_iff Primrec.fin_val_iff
-/

#print Primrec.fin_val /-
theorem fin_val {n} : Primrec (coe : Fin n → ℕ) :=
  fin_val_iff.2 Primrec.id
#align primrec.fin_val Primrec.fin_val
-/

#print Primrec.fin_succ /-
theorem fin_succ {n} : Primrec (@Fin.succ n) :=
  fin_val_iff.1 <| by simp [succ.comp fin_val]
#align primrec.fin_succ Primrec.fin_succ
-/

#print Primrec.vector_toList /-
theorem vector_toList {n} : Primrec (@Vector.toList α n) :=
  subtype_val
#align primrec.vector_to_list Primrec.vector_toList
-/

#print Primrec.vector_toList_iff /-
theorem vector_toList_iff {n} {f : α → Vector β n} : (Primrec fun a => (f a).toList) ↔ Primrec f :=
  subtype_val_iff
#align primrec.vector_to_list_iff Primrec.vector_toList_iff
-/

#print Primrec.vector_cons /-
theorem vector_cons {n} : Primrec₂ (@Vector.cons α n) :=
  vector_toList_iff.1 <| by simp <;> exact list_cons.comp fst (vector_to_list_iff.2 snd)
#align primrec.vector_cons Primrec.vector_cons
-/

#print Primrec.vector_length /-
theorem vector_length {n} : Primrec (@Vector.length α n) :=
  const _
#align primrec.vector_length Primrec.vector_length
-/

#print Primrec.vector_head /-
theorem vector_head {n} : Primrec (@Vector.head α n) :=
  option_some_iff.1 <| (list_head?.comp vector_toList).of_eq fun ⟨a :: l, h⟩ => rfl
#align primrec.vector_head Primrec.vector_head
-/

#print Primrec.vector_tail /-
theorem vector_tail {n} : Primrec (@Vector.tail α n) :=
  vector_toList_iff.1 <| (list_tail.comp vector_toList).of_eq fun ⟨l, h⟩ => by cases l <;> rfl
#align primrec.vector_tail Primrec.vector_tail
-/

#print Primrec.vector_get /-
theorem vector_get {n} : Primrec₂ (@Vector.get α n) :=
  option_some_iff.1 <|
    (list_get?.comp (vector_toList.comp fst) (fin_val.comp snd)).of_eq fun a => by
      simp [Vector.get_eq_get] <;> rw [← List.nthLe_get?]
#align primrec.vector_nth Primrec.vector_get
-/

/- warning: primrec.list_of_fn -> Primrec.list_ofFn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] {n : Nat} {f : (Fin n) -> α -> σ}, (forall (i : Fin n), Primrec.{u1, u2} α σ _inst_1 _inst_4 (f i)) -> (Primrec.{u1, u2} α (List.{u2} σ) _inst_1 (Primcodable.list.{u2} σ _inst_4) (fun (a : α) => List.ofFn.{u2} σ n (fun (i : Fin n) => f i a)))
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] {n : Nat} {f : (Fin n) -> α -> σ}, (forall (i : Fin n), Primrec.{u2, u1} α σ _inst_1 _inst_4 (f i)) -> (Primrec.{u2, u1} α (List.{u1} σ) _inst_1 (Primcodable.list.{u1} σ _inst_4) (fun (a : α) => List.ofFn.{u1} σ n (fun (i : Fin n) => f i a)))
Case conversion may be inaccurate. Consider using '#align primrec.list_of_fn Primrec.list_ofFnₓ'. -/
theorem list_ofFn :
    ∀ {n} {f : Fin n → α → σ}, (∀ i, Primrec (f i)) → Primrec fun a => List.ofFn fun i => f i a
  | 0, f, hf => const []
  | n + 1, f, hf => by
    simp [List.ofFn_succ] <;> exact list_cons.comp (hf 0) (list_of_fn fun i => hf i.succ)
#align primrec.list_of_fn Primrec.list_ofFn

/- warning: primrec.vector_of_fn -> Primrec.vector_ofFn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] {n : Nat} {f : (Fin n) -> α -> σ}, (forall (i : Fin n), Primrec.{u1, u2} α σ _inst_1 _inst_4 (f i)) -> (Primrec.{u1, u2} α (Vector.{u2} σ n) _inst_1 (Primcodable.vector.{u2} σ _inst_4 n) (fun (a : α) => Vector.ofFn.{u2} σ n (fun (i : Fin n) => f i a)))
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] {n : Nat} {f : (Fin n) -> α -> σ}, (forall (i : Fin n), Primrec.{u2, u1} α σ _inst_1 _inst_4 (f i)) -> (Primrec.{u2, u1} α (Vector.{u1} σ n) _inst_1 (Primcodable.vector.{u1} σ _inst_4 n) (fun (a : α) => Vector.ofFn.{u1} σ n (fun (i : Fin n) => f i a)))
Case conversion may be inaccurate. Consider using '#align primrec.vector_of_fn Primrec.vector_ofFnₓ'. -/
theorem vector_ofFn {n} {f : Fin n → α → σ} (hf : ∀ i, Primrec (f i)) :
    Primrec fun a => Vector.ofFn fun i => f i a :=
  vector_toList_iff.1 <| by simp [list_of_fn hf]
#align primrec.vector_of_fn Primrec.vector_ofFn

#print Primrec.vector_nth' /-
theorem vector_nth' {n} : Primrec (@Vector.get α n) :=
  ofEquiv_symm
#align primrec.vector_nth' Primrec.vector_nth'
-/

#print Primrec.vector_of_fn' /-
theorem vector_of_fn' {n} : Primrec (@Vector.ofFn α n) :=
  ofEquiv
#align primrec.vector_of_fn' Primrec.vector_of_fn'
-/

#print Primrec.fin_app /-
theorem fin_app {n} : Primrec₂ (@id (Fin n → σ)) :=
  (vector_get.comp (vector_of_fn'.comp fst) snd).of_eq fun ⟨v, i⟩ => by simp
#align primrec.fin_app Primrec.fin_app
-/

/- warning: primrec.fin_curry₁ -> Primrec.fin_curry₁ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] {n : Nat} {f : (Fin n) -> α -> σ}, Iff (Primrec₂.{0, u1, u2} (Fin n) α σ (Primcodable.fin n) _inst_1 _inst_4 f) (forall (i : Fin n), Primrec.{u1, u2} α σ _inst_1 _inst_4 (f i))
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] {n : Nat} {f : (Fin n) -> α -> σ}, Iff (Primrec₂.{0, u2, u1} (Fin n) α σ (Primcodable.fin n) _inst_1 _inst_4 f) (forall (i : Fin n), Primrec.{u2, u1} α σ _inst_1 _inst_4 (f i))
Case conversion may be inaccurate. Consider using '#align primrec.fin_curry₁ Primrec.fin_curry₁ₓ'. -/
theorem fin_curry₁ {n} {f : Fin n → α → σ} : Primrec₂ f ↔ ∀ i, Primrec (f i) :=
  ⟨fun h i => h.comp (const i) Primrec.id, fun h =>
    (vector_get.comp ((vector_ofFn h).comp snd) fst).of_eq fun a => by simp⟩
#align primrec.fin_curry₁ Primrec.fin_curry₁

/- warning: primrec.fin_curry -> Primrec.fin_curry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] {n : Nat} {f : α -> (Fin n) -> σ}, Iff (Primrec.{u1, u2} α ((Fin n) -> σ) _inst_1 (Primcodable.finArrow.{u2} σ _inst_4 n) f) (Primrec₂.{u1, 0, u2} α (Fin n) σ _inst_1 (Primcodable.fin n) _inst_4 f)
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] {n : Nat} {f : α -> (Fin n) -> σ}, Iff (Primrec.{u2, u1} α ((Fin n) -> σ) _inst_1 (Primcodable.finArrow.{u1} σ _inst_4 n) f) (Primrec₂.{u2, 0, u1} α (Fin n) σ _inst_1 (Primcodable.fin n) _inst_4 f)
Case conversion may be inaccurate. Consider using '#align primrec.fin_curry Primrec.fin_curryₓ'. -/
theorem fin_curry {n} {f : α → Fin n → σ} : Primrec f ↔ Primrec₂ f :=
  ⟨fun h => fin_app.comp (h.comp fst) snd, fun h =>
    (vector_nth'.comp
          (vector_ofFn fun i => show Primrec fun a => f a i from h.comp Primrec.id (const i))).of_eq
      fun a => by funext i <;> simp⟩
#align primrec.fin_curry Primrec.fin_curry

end Primrec

namespace Nat

open Vector

#print Nat.Primrec' /-
/-- An alternative inductive definition of `primrec` which
  does not use the pairing function on ℕ, and so has to
  work with n-ary functions on ℕ instead of unary functions.
  We prove that this is equivalent to the regular notion
  in `to_prim` and `of_prim`. -/
inductive Primrec' : ∀ {n}, (Vector ℕ n → ℕ) → Prop
  | zero : @primrec' 0 fun _ => 0
  | succ : @primrec' 1 fun v => succ v.headI
  | nth {n} (i : Fin n) : primrec' fun v => v.get? i
  |
  comp {m n f} (g : Fin n → Vector ℕ m → ℕ) :
    primrec' f → (∀ i, primrec' (g i)) → primrec' fun a => f (ofFn fun i => g i a)
  |
  prec {n f g} :
    @primrec' n f →
      @primrec' (n + 2) g →
        primrec' fun v : Vector ℕ (n + 1) =>
          v.headI.elim (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)
#align nat.primrec' Nat.Primrec'
-/

end Nat

namespace Nat.Primrec'

open Vector Primrec

open Nat (Primrec')

open Nat.Primrec'

/- ./././Mathport/Syntax/Translate/Command.lean:691:6: unsupported: hide command -/
#print Nat.Primrec'.to_prim /-
theorem to_prim {n f} (pf : @Primrec' n f) : Primrec f :=
  by
  induction pf
  case zero => exact const 0
  case succ => exact primrec.succ.comp vector_head
  case nth n i => exact vector_nth.comp Primrec.id (const i)
  case comp m n f g _ _ hf hg => exact hf.comp (vector_of_fn fun i => hg i)
  case prec n f g _ _ hf hg =>
    exact
      nat_elim' vector_head (hf.comp vector_tail)
        (hg.comp <|
            vector_cons.comp (fst.comp snd) <|
              vector_cons.comp (snd.comp snd) <| (@vector_tail _ _ (n + 1)).comp fst).to₂
#align nat.primrec'.to_prim Nat.Primrec'.to_prim
-/

#print Nat.Primrec'.of_eq /-
theorem of_eq {n} {f g : Vector ℕ n → ℕ} (hf : Primrec' f) (H : ∀ i, f i = g i) : Primrec' g :=
  (funext H : f = g) ▸ hf
#align nat.primrec'.of_eq Nat.Primrec'.of_eq
-/

#print Nat.Primrec'.const /-
theorem const {n} : ∀ m, @Primrec' n fun v => m
  | 0 => zero.comp Fin.elim0 fun i => i.elim0ₓ
  | m + 1 => succ.comp _ fun i => const m
#align nat.primrec'.const Nat.Primrec'.const
-/

#print Nat.Primrec'.head /-
theorem head {n : ℕ} : @Primrec' n.succ head :=
  (get 0).of_eq fun v => by simp [nth_zero]
#align nat.primrec'.head Nat.Primrec'.head
-/

#print Nat.Primrec'.tail /-
theorem tail {n f} (hf : @Primrec' n f) : @Primrec' n.succ fun v => f v.tail :=
  (hf.comp _ fun i => @get _ i.succ).of_eq fun v => by
    rw [← of_fn_nth v.tail] <;> congr <;> funext i <;> simp
#align nat.primrec'.tail Nat.Primrec'.tail
-/

#print Nat.Primrec'.Vec /-
/-- A function from vectors to vectors is primitive recursive when all of its projections are. -/
def Vec {n m} (f : Vector ℕ n → Vector ℕ m) : Prop :=
  ∀ i, Primrec' fun v => (f v).get? i
#align nat.primrec'.vec Nat.Primrec'.Vec
-/

#print Nat.Primrec'.nil /-
protected theorem nil {n} : @Vec n 0 fun _ => nil := fun i => i.elim0ₓ
#align nat.primrec'.nil Nat.Primrec'.nil
-/

#print Nat.Primrec'.cons /-
protected theorem cons {n m f g} (hf : @Primrec' n f) (hg : @Vec n m g) :
    Vec fun v => f v ::ᵥ g v := fun i => Fin.cases (by simp [*]) (fun i => by simp [hg i]) i
#align nat.primrec'.cons Nat.Primrec'.cons
-/

#print Nat.Primrec'.idv /-
theorem idv {n} : @Vec n n id :=
  get
#align nat.primrec'.idv Nat.Primrec'.idv
-/

#print Nat.Primrec'.comp' /-
theorem comp' {n m f g} (hf : @Primrec' m f) (hg : @Vec n m g) : Primrec' fun v => f (g v) :=
  (hf.comp _ hg).of_eq fun v => by simp
#align nat.primrec'.comp' Nat.Primrec'.comp'
-/

#print Nat.Primrec'.comp₁ /-
theorem comp₁ (f : ℕ → ℕ) (hf : @Primrec' 1 fun v => f v.headI) {n g} (hg : @Primrec' n g) :
    Primrec' fun v => f (g v) :=
  hf.comp _ fun i => hg
#align nat.primrec'.comp₁ Nat.Primrec'.comp₁
-/

#print Nat.Primrec'.comp₂ /-
theorem comp₂ (f : ℕ → ℕ → ℕ) (hf : @Primrec' 2 fun v => f v.headI v.tail.headI) {n g h}
    (hg : @Primrec' n g) (hh : @Primrec' n h) : Primrec' fun v => f (g v) (h v) := by
  simpa using hf.comp' (hg.cons <| hh.cons primrec'.nil)
#align nat.primrec'.comp₂ Nat.Primrec'.comp₂
-/

#print Nat.Primrec'.prec' /-
theorem prec' {n f g h} (hf : @Primrec' n f) (hg : @Primrec' n g) (hh : @Primrec' (n + 2) h) :
    @Primrec' n fun v => (f v).elim (g v) fun y IH : ℕ => h (y ::ᵥ IH ::ᵥ v) := by
  simpa using comp' (prec hg hh) (hf.cons idv)
#align nat.primrec'.prec' Nat.Primrec'.prec'
-/

#print Nat.Primrec'.pred /-
theorem pred : @Primrec' 1 fun v => v.headI.pred :=
  (prec' head (const 0) head).of_eq fun v => by simp <;> cases v.head <;> rfl
#align nat.primrec'.pred Nat.Primrec'.pred
-/

#print Nat.Primrec'.add /-
theorem add : @Primrec' 2 fun v => v.headI + v.tail.headI :=
  (prec head (succ.comp₁ _ (tail head))).of_eq fun v => by
    simp <;> induction v.head <;> simp [*, Nat.succ_add]
#align nat.primrec'.add Nat.Primrec'.add
-/

#print Nat.Primrec'.sub /-
theorem sub : @Primrec' 2 fun v => v.headI - v.tail.headI :=
  by
  suffices; simpa using comp₂ (fun a b => b - a) this (tail head) head
  refine' (prec head (pred.comp₁ _ (tail head))).of_eq fun v => _
  simp; induction v.head <;> simp [*, Nat.sub_succ]
#align nat.primrec'.sub Nat.Primrec'.sub
-/

#print Nat.Primrec'.mul /-
theorem mul : @Primrec' 2 fun v => v.headI * v.tail.headI :=
  (prec (const 0) (tail (add.comp₂ _ (tail head) head))).of_eq fun v => by
    simp <;> induction v.head <;> simp [*, Nat.succ_mul] <;> rw [add_comm]
#align nat.primrec'.mul Nat.Primrec'.mul
-/

/- warning: nat.primrec'.if_lt -> Nat.Primrec'.if_lt is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {a : (Vector.{0} Nat n) -> Nat} {b : (Vector.{0} Nat n) -> Nat} {f : (Vector.{0} Nat n) -> Nat} {g : (Vector.{0} Nat n) -> Nat}, (Nat.Primrec' n a) -> (Nat.Primrec' n b) -> (Nat.Primrec' n f) -> (Nat.Primrec' n g) -> (Nat.Primrec' n (fun (v : Vector.{0} Nat n) => ite.{1} Nat (LT.lt.{0} Nat Nat.hasLt (a v) (b v)) (Nat.decidableLt (a v) (b v)) (f v) (g v)))
but is expected to have type
  forall {n : Nat} {a : (Vector.{0} Nat n) -> Nat} {b : (Vector.{0} Nat n) -> Nat} {f : (Vector.{0} Nat n) -> Nat} {g : (Vector.{0} Nat n) -> Nat}, (Nat.Primrec' n a) -> (Nat.Primrec' n b) -> (Nat.Primrec' n f) -> (Nat.Primrec' n g) -> (Nat.Primrec' n (fun (v : Vector.{0} Nat n) => ite.{1} Nat (LT.lt.{0} Nat instLTNat (a v) (b v)) (Nat.decLt (a v) (b v)) (f v) (g v)))
Case conversion may be inaccurate. Consider using '#align nat.primrec'.if_lt Nat.Primrec'.if_ltₓ'. -/
theorem if_lt {n a b f g} (ha : @Primrec' n a) (hb : @Primrec' n b) (hf : @Primrec' n f)
    (hg : @Primrec' n g) : @Primrec' n fun v => if a v < b v then f v else g v :=
  (prec' (sub.comp₂ _ hb ha) hg (tail <| tail hf)).of_eq fun v =>
    by
    cases e : b v - a v
    · simp [not_lt.2 (tsub_eq_zero_iff_le.mp e)]
    · simp [Nat.lt_of_sub_eq_succ e]
#align nat.primrec'.if_lt Nat.Primrec'.if_lt

#print Nat.Primrec'.natPair /-
theorem natPair : @Primrec' 2 fun v => v.headI.pair v.tail.headI :=
  if_lt head (tail head) (add.comp₂ _ (tail <| mul.comp₂ _ head head) head)
    (add.comp₂ _ (add.comp₂ _ (mul.comp₂ _ head head) head) (tail head))
#align nat.primrec'.mkpair Nat.Primrec'.natPair
-/

#print Nat.Primrec'.encode /-
protected theorem encode : ∀ {n}, @Primrec' n encode
  | 0 => (const 0).of_eq fun v => by rw [v.eq_nil] <;> rfl
  | n + 1 => (succ.comp₁ _ (natPair.comp₂ _ head (tail encode))).of_eq fun ⟨a :: l, e⟩ => rfl
#align nat.primrec'.encode Nat.Primrec'.encode
-/

#print Nat.Primrec'.sqrt /-
theorem sqrt : @Primrec' 1 fun v => v.headI.sqrt :=
  by
  suffices H : ∀ n : ℕ, n.sqrt = n.elim 0 fun x y => if x.succ < y.succ * y.succ then y else y.succ
  · simp [H]
    have :=
      @prec' 1 _ _
        (fun v => by
          have x := v.head <;> have y := v.tail.head <;>
            exact if x.succ < y.succ * y.succ then y else y.succ)
        head (const 0) _
    · convert this
      funext
      congr
      funext x y
      congr <;> simp
    have x1 := succ.comp₁ _ head
    have y1 := succ.comp₁ _ (tail head)
    exact if_lt x1 (mul.comp₂ _ y1 y1) (tail head) y1
  intro ; symm
  induction' n with n IH; · simp
  dsimp; rw [IH]; split_ifs
  · exact le_antisymm (Nat.sqrt_le_sqrt (Nat.le_succ _)) (Nat.lt_succ_iff.1 <| Nat.sqrt_lt.2 h)
  ·
    exact
      Nat.eq_sqrt.2 ⟨not_lt.1 h, Nat.sqrt_lt.1 <| Nat.lt_succ_iff.2 <| Nat.sqrt_succ_le_succ_sqrt _⟩
#align nat.primrec'.sqrt Nat.Primrec'.sqrt
-/

#print Nat.Primrec'.unpair₁ /-
theorem unpair₁ {n f} (hf : @Primrec' n f) : @Primrec' n fun v => (f v).unpair.1 :=
  by
  have s := sqrt.comp₁ _ hf
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
  refine' (if_lt fss s fss s).of_eq fun v => _
  simp [Nat.unpair]; split_ifs <;> rfl
#align nat.primrec'.unpair₁ Nat.Primrec'.unpair₁
-/

#print Nat.Primrec'.unpair₂ /-
theorem unpair₂ {n f} (hf : @Primrec' n f) : @Primrec' n fun v => (f v).unpair.2 :=
  by
  have s := sqrt.comp₁ _ hf
  have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
  refine' (if_lt fss s s (sub.comp₂ _ fss s)).of_eq fun v => _
  simp [Nat.unpair]; split_ifs <;> rfl
#align nat.primrec'.unpair₂ Nat.Primrec'.unpair₂
-/

#print Nat.Primrec'.of_prim /-
theorem of_prim : ∀ {n f}, Primrec f → @Primrec' n f :=
  suffices ∀ f, Nat.Primrec f → @Primrec' 1 fun v => f v.headI from fun n f hf =>
    (pred.comp₁ _ <|
          (this _ hf).comp₁ (fun m => Encodable.encode <| (decode (Vector ℕ n) m).map f)
            Primrec'.encode).of_eq
      fun i => by simp [encodek]
  fun f hf => by
  induction hf
  case zero => exact const 0
  case succ => exact succ
  case left => exact unpair₁ head
  case right => exact unpair₂ head
  case pair f g _ _ hf hg => exact mkpair.comp₂ _ hf hg
  case comp f g _ _ hf hg => exact hf.comp₁ _ hg
  case prec f g _ _ hf hg =>
    simpa using
      prec' (unpair₂ head) (hf.comp₁ _ (unpair₁ head))
        (hg.comp₁ _ <|
          mkpair.comp₂ _ (unpair₁ <| tail <| tail head) (mkpair.comp₂ _ head (tail head)))
#align nat.primrec'.of_prim Nat.Primrec'.of_prim
-/

#print Nat.Primrec'.prim_iff /-
theorem prim_iff {n f} : @Primrec' n f ↔ Primrec f :=
  ⟨to_prim, of_prim⟩
#align nat.primrec'.prim_iff Nat.Primrec'.prim_iff
-/

#print Nat.Primrec'.prim_iff₁ /-
theorem prim_iff₁ {f : ℕ → ℕ} : (@Primrec' 1 fun v => f v.headI) ↔ Primrec f :=
  prim_iff.trans
    ⟨fun h => (h.comp <| vector_ofFn fun i => Primrec.id).of_eq fun v => by simp, fun h =>
      h.comp vector_head⟩
#align nat.primrec'.prim_iff₁ Nat.Primrec'.prim_iff₁
-/

#print Nat.Primrec'.prim_iff₂ /-
theorem prim_iff₂ {f : ℕ → ℕ → ℕ} : (@Primrec' 2 fun v => f v.headI v.tail.headI) ↔ Primrec₂ f :=
  prim_iff.trans
    ⟨fun h =>
      (h.comp <| vector_cons.comp fst <| vector_cons.comp snd (Primrec.const nil)).of_eq fun v => by
        simp,
      fun h => h.comp vector_head (vector_head.comp vector_tail)⟩
#align nat.primrec'.prim_iff₂ Nat.Primrec'.prim_iff₂
-/

#print Nat.Primrec'.vec_iff /-
theorem vec_iff {m n f} : @Vec m n f ↔ Primrec f :=
  ⟨fun h => by simpa using vector_of_fn fun i => to_prim (h i), fun h i =>
    of_prim <| vector_get.comp h (Primrec.const i)⟩
#align nat.primrec'.vec_iff Nat.Primrec'.vec_iff
-/

end Nat.Primrec'

#print Primrec.nat_sqrt /-
theorem Primrec.nat_sqrt : Primrec Nat.sqrt :=
  Nat.Primrec'.prim_iff₁.1 Nat.Primrec'.sqrt
#align primrec.nat_sqrt Primrec.nat_sqrt
-/

