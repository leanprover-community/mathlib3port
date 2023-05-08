/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module computability.partrec
! leanprover-community/mathlib commit 9ee02c6c2208fd7795005aa394107c0374906cca
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Computability.Primrec
import Mathbin.Data.Nat.Psub
import Mathbin.Data.Pfun

/-!
# The partial recursive functions

The partial recursive functions are defined similarly to the primitive
recursive functions, but now all functions are partial, implemented
using the `part` monad, and there is an additional operation, called
μ-recursion, which performs unbounded minimization.

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/


open Encodable Denumerable Part

attribute [-simp] not_forall

namespace Nat

section Rfind

parameter (p : ℕ →. Bool)

private def lbp (m n : ℕ) : Prop :=
  m = n + 1 ∧ ∀ k ≤ n, false ∈ p k
#align nat.lbp nat.lbp

parameter (H : ∃ n, true ∈ p n ∧ ∀ k < n, (p k).Dom)

private def wf_lbp : WellFounded lbp :=
  ⟨by
    let ⟨n, pn⟩ := H
    suffices ∀ m k, n ≤ k + m → Acc (lbp p) k by exact fun a => this _ _ (Nat.le_add_left _ _)
    intro m k kn
    induction' m with m IH generalizing k <;> refine' ⟨_, fun y r => _⟩ <;> rcases r with ⟨rfl, a⟩
    · injection mem_unique pn.1 (a _ kn)
    · exact IH _ (by rw [Nat.add_right_comm] <;> exact kn)⟩
#align nat.wf_lbp nat.wf_lbp

#print Nat.rfindX /-
def rfindX : { n // true ∈ p n ∧ ∀ m < n, false ∈ p m } :=
  suffices ∀ k, (∀ n < k, false ∈ p n) → { n // true ∈ p n ∧ ∀ m < n, false ∈ p m } from
    this 0 fun n => (Nat.not_lt_zero _).elim
  @WellFounded.fix _ _ lbp wf_lbp
    (by
      intro m IH al
      have pm : (p m).Dom := by
        rcases H with ⟨n, h₁, h₂⟩
        rcases lt_trichotomy m n with (h₃ | h₃ | h₃)
        · exact h₂ _ h₃
        · rw [h₃]
          exact h₁.fst
        · injection mem_unique h₁ (al _ h₃)
      cases e : (p m).get pm
      · suffices
        exact IH _ ⟨rfl, this⟩ fun n h => this _ (le_of_lt_succ h)
        intro n h
        cases' h.lt_or_eq_dec with h h
        · exact al _ h
        · rw [h]
          exact ⟨_, e⟩
      · exact ⟨m, ⟨_, e⟩, al⟩)
#align nat.rfind_x Nat.rfindX
-/

end Rfind

#print Nat.rfind /-
def rfind (p : ℕ →. Bool) : Part ℕ :=
  ⟨_, fun h => (rfindX p h).1⟩
#align nat.rfind Nat.rfind
-/

#print Nat.rfind_spec /-
theorem rfind_spec {p : ℕ →. Bool} {n : ℕ} (h : n ∈ rfind p) : true ∈ p n :=
  h.snd ▸ (rfindX p h.fst).2.1
#align nat.rfind_spec Nat.rfind_spec
-/

#print Nat.rfind_min /-
theorem rfind_min {p : ℕ →. Bool} {n : ℕ} (h : n ∈ rfind p) : ∀ {m : ℕ}, m < n → false ∈ p m :=
  h.snd ▸ (rfindX p h.fst).2.2
#align nat.rfind_min Nat.rfind_min
-/

#print Nat.rfind_dom /-
@[simp]
theorem rfind_dom {p : ℕ →. Bool} :
    (rfind p).Dom ↔ ∃ n, true ∈ p n ∧ ∀ {m : ℕ}, m < n → (p m).Dom :=
  Iff.rfl
#align nat.rfind_dom Nat.rfind_dom
-/

#print Nat.rfind_dom' /-
theorem rfind_dom' {p : ℕ →. Bool} :
    (rfind p).Dom ↔ ∃ n, true ∈ p n ∧ ∀ {m : ℕ}, m ≤ n → (p m).Dom :=
  exists_congr fun n =>
    and_congr_right fun pn =>
      ⟨fun H m h => (Decidable.eq_or_lt_of_le h).elim (fun e => e.symm ▸ pn.fst) (H _), fun H m h =>
        H (le_of_lt h)⟩
#align nat.rfind_dom' Nat.rfind_dom'
-/

#print Nat.mem_rfind /-
@[simp]
theorem mem_rfind {p : ℕ →. Bool} {n : ℕ} :
    n ∈ rfind p ↔ true ∈ p n ∧ ∀ {m : ℕ}, m < n → false ∈ p m :=
  ⟨fun h => ⟨rfind_spec h, @rfind_min _ _ h⟩, fun ⟨h₁, h₂⟩ =>
    by
    let ⟨m, hm⟩ := dom_iff_mem.1 <| (@rfind_dom p).2 ⟨_, h₁, fun m mn => (h₂ mn).fst⟩
    rcases lt_trichotomy m n with (h | h | h)
    · injection mem_unique (h₂ h) (rfind_spec hm)
    · rwa [← h]
    · injection mem_unique h₁ (rfind_min hm h)⟩
#align nat.mem_rfind Nat.mem_rfind
-/

/- warning: nat.rfind_min' -> Nat.rfind_min' is a dubious translation:
lean 3 declaration is
  forall {p : Nat -> Bool} {m : Nat}, (coeSort.{1, 1} Bool Prop coeSortBool (p m)) -> (Exists.{1} Nat (fun (n : Nat) => Exists.{0} (Membership.Mem.{0, 0} Nat (Part.{0} Nat) (Part.hasMem.{0} Nat) n (Nat.rfind ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Nat -> Bool) (PFun.{0, 0} Nat Bool) (HasLiftT.mk.{1, 1} (Nat -> Bool) (PFun.{0, 0} Nat Bool) (CoeTCₓ.coe.{1, 1} (Nat -> Bool) (PFun.{0, 0} Nat Bool) (coeBase.{1, 1} (Nat -> Bool) (PFun.{0, 0} Nat Bool) (PFun.coe.{0, 0} Nat Bool)))) p))) (fun (H : Membership.Mem.{0, 0} Nat (Part.{0} Nat) (Part.hasMem.{0} Nat) n (Nat.rfind ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Nat -> Bool) (PFun.{0, 0} Nat Bool) (HasLiftT.mk.{1, 1} (Nat -> Bool) (PFun.{0, 0} Nat Bool) (CoeTCₓ.coe.{1, 1} (Nat -> Bool) (PFun.{0, 0} Nat Bool) (coeBase.{1, 1} (Nat -> Bool) (PFun.{0, 0} Nat Bool) (PFun.coe.{0, 0} Nat Bool)))) p))) => LE.le.{0} Nat Nat.hasLe n m)))
but is expected to have type
  forall {p : Nat -> Bool} {m : Nat}, (Eq.{1} Bool (p m) Bool.true) -> (Exists.{1} Nat (fun (n : Nat) => And (Membership.mem.{0, 0} Nat (Part.{0} Nat) (Part.instMembershipPart.{0} Nat) n (Nat.rfind (PFun.lift.{0, 0} Nat Bool p))) (LE.le.{0} Nat instLENat n m)))
Case conversion may be inaccurate. Consider using '#align nat.rfind_min' Nat.rfind_min'ₓ'. -/
theorem rfind_min' {p : ℕ → Bool} {m : ℕ} (pm : p m) : ∃ n ∈ rfind p, n ≤ m :=
  have : true ∈ (p : ℕ →. Bool) m := ⟨trivial, pm⟩
  let ⟨n, hn⟩ := dom_iff_mem.1 <| (@rfind_dom p).2 ⟨m, this, fun k h => ⟨⟩⟩
  ⟨n, hn, not_lt.1 fun h => by injection mem_unique this (rfind_min hn h)⟩
#align nat.rfind_min' Nat.rfind_min'

#print Nat.rfind_zero_none /-
theorem rfind_zero_none (p : ℕ →. Bool) (p0 : p 0 = none) : rfind p = none :=
  eq_none_iff.2 fun a h =>
    let ⟨n, h₁, h₂⟩ := rfind_dom'.1 h.fst
    (p0 ▸ h₂ (zero_le _) : (@Part.none Bool).Dom)
#align nat.rfind_zero_none Nat.rfind_zero_none
-/

#print Nat.rfindOpt /-
def rfindOpt {α} (f : ℕ → Option α) : Part α :=
  (rfind fun n => (f n).isSome).bind fun n => f n
#align nat.rfind_opt Nat.rfindOpt
-/

#print Nat.rfindOpt_spec /-
theorem rfindOpt_spec {α} {f : ℕ → Option α} {a} (h : a ∈ rfindOpt f) : ∃ n, a ∈ f n :=
  let ⟨n, h₁, h₂⟩ := mem_bind_iff.1 h
  ⟨n, mem_coe.1 h₂⟩
#align nat.rfind_opt_spec Nat.rfindOpt_spec
-/

#print Nat.rfindOpt_dom /-
theorem rfindOpt_dom {α} {f : ℕ → Option α} : (rfindOpt f).Dom ↔ ∃ n a, a ∈ f n :=
  ⟨fun h => (rfindOpt_spec ⟨h, rfl⟩).imp fun n h => ⟨_, h⟩, fun h =>
    by
    have h' : ∃ n, (f n).isSome := h.imp fun n => Option.isSome_iff_exists.2
    have s := Nat.find_spec h'
    have fd : (rfind fun n => (f n).isSome).Dom :=
      ⟨Nat.find h', by simpa using s.symm, fun _ _ => trivial⟩
    refine' ⟨fd, _⟩
    have := rfind_spec (get_mem fd)
    simp at this⊢
    cases' Option.isSome_iff_exists.1 this.symm with a e
    rw [e]; trivial⟩
#align nat.rfind_opt_dom Nat.rfindOpt_dom
-/

#print Nat.rfindOpt_mono /-
theorem rfindOpt_mono {α} {f : ℕ → Option α} (H : ∀ {a m n}, m ≤ n → a ∈ f m → a ∈ f n) {a} :
    a ∈ rfindOpt f ↔ ∃ n, a ∈ f n :=
  ⟨rfindOpt_spec, fun ⟨n, h⟩ => by
    have h' := rfind_opt_dom.2 ⟨_, _, h⟩
    cases' rfind_opt_spec ⟨h', rfl⟩ with k hk
    have := (H (le_max_left _ _) h).symm.trans (H (le_max_right _ _) hk)
    simp at this; simp [this, get_mem]⟩
#align nat.rfind_opt_mono Nat.rfindOpt_mono
-/

#print Nat.Partrec /-
inductive Partrec : (ℕ →. ℕ) → Prop
  | zero : Partrec (pure 0)
  | succ : Partrec succ
  | left : Partrec ↑fun n : ℕ => n.unpair.1
  | right : Partrec ↑fun n : ℕ => n.unpair.2
  | pair {f g} : Partrec f → Partrec g → Partrec fun n => pair <$> f n <*> g n
  | comp {f g} : Partrec f → Partrec g → Partrec fun n => g n >>= f
  |
  prec {f g} :
    Partrec f →
      Partrec g →
        Partrec
          (unpaired fun a n =>
            n.elim (f a) fun y IH => do
              let i ← IH
              g (mkpair a (mkpair y i)))
  | rfind {f} : Partrec f → Partrec fun a => rfind fun n => (fun m => m = 0) <$> f (pair a n)
#align nat.partrec Nat.Partrec
-/

namespace Partrec

#print Nat.Partrec.of_eq /-
theorem of_eq {f g : ℕ →. ℕ} (hf : Partrec f) (H : ∀ n, f n = g n) : Partrec g :=
  (funext H : f = g) ▸ hf
#align nat.partrec.of_eq Nat.Partrec.of_eq
-/

#print Nat.Partrec.of_eq_tot /-
theorem of_eq_tot {f : ℕ →. ℕ} {g : ℕ → ℕ} (hf : Partrec f) (H : ∀ n, g n ∈ f n) : Partrec g :=
  hf.of_eq fun n => eq_some_iff.2 (H n)
#align nat.partrec.of_eq_tot Nat.Partrec.of_eq_tot
-/

#print Nat.Partrec.of_primrec /-
theorem of_primrec {f : ℕ → ℕ} (hf : Primrec f) : Partrec f :=
  by
  induction hf
  case zero => exact zero
  case succ => exact succ
  case left => exact left
  case right => exact right
  case pair f g hf hg pf pg =>
    refine' (pf.pair pg).of_eq_tot fun n => _
    simp [Seq.seq]
  case comp f g hf hg pf pg =>
    refine' (pf.comp pg).of_eq_tot fun n => _
    simp
  case prec f g hf hg pf pg =>
    refine' (pf.prec pg).of_eq_tot fun n => _
    simp
    induction' n.unpair.2 with m IH; · simp
    simp; exact ⟨_, IH, rfl⟩
#align nat.partrec.of_primrec Nat.Partrec.of_primrec
-/

#print Nat.Partrec.some /-
protected theorem some : Partrec some :=
  of_primrec Primrec.id
#align nat.partrec.some Nat.Partrec.some
-/

#print Nat.Partrec.none /-
theorem none : Partrec fun n => none :=
  (of_primrec (Nat.Primrec.const 1)).rfind.of_eq fun n =>
    eq_none_iff.2 fun a ⟨h, e⟩ => by simpa using h
#align nat.partrec.none Nat.Partrec.none
-/

#print Nat.Partrec.prec' /-
theorem prec' {f g h} (hf : Partrec f) (hg : Partrec g) (hh : Partrec h) :
    Partrec fun a =>
      (f a).bind fun n =>
        n.elim (g a) fun y IH => do
          let i ← IH
          h (mkpair a (mkpair y i)) :=
  ((prec hg hh).comp (pair Partrec.some hf)).of_eq fun a =>
    ext fun s => by
      simp [(· <*> ·)] <;>
        exact
          ⟨fun ⟨n, h₁, h₂⟩ => ⟨_, ⟨_, h₁, rfl⟩, by simpa using h₂⟩, fun ⟨_, ⟨n, h₁, rfl⟩, h₂⟩ =>
            ⟨_, h₁, by simpa using h₂⟩⟩
#align nat.partrec.prec' Nat.Partrec.prec'
-/

#print Nat.Partrec.ppred /-
theorem ppred : Partrec fun n => ppred n :=
  have : Primrec₂ fun n m => if n = Nat.succ m then 0 else 1 :=
    (Primrec.ite
        (@PrimrecRel.comp _ _ _ _ _ _ _ Primrec.eq Primrec.fst (Primrec.succ.comp Primrec.snd))
        (Primrec.const 0) (Primrec.const 1)).to₂
  (of_primrec (Primrec₂.unpaired'.2 this)).rfind.of_eq fun n =>
    by
    cases n <;> simp
    ·
      exact
        eq_none_iff.2 fun a ⟨⟨m, h, _⟩, _⟩ => by
          simpa [show 0 ≠ m.succ by intro h <;> injection h] using h
    · refine' eq_some_iff.2 _
      simp
      intro m h
      simp [ne_of_gt h]
#align nat.partrec.ppred Nat.Partrec.ppred
-/

end Partrec

end Nat

#print Partrec /-
def Partrec {α σ} [Primcodable α] [Primcodable σ] (f : α →. σ) :=
  Nat.Partrec fun n => Part.bind (decode α n) fun a => (f a).map encode
#align partrec Partrec
-/

#print Partrec₂ /-
def Partrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α → β →. σ) :=
  Partrec fun p : α × β => f p.1 p.2
#align partrec₂ Partrec₂
-/

#print Computable /-
def Computable {α σ} [Primcodable α] [Primcodable σ] (f : α → σ) :=
  Partrec (f : α →. σ)
#align computable Computable
-/

#print Computable₂ /-
def Computable₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α → β → σ) :=
  Computable fun p : α × β => f p.1 p.2
#align computable₂ Computable₂
-/

/- warning: primrec.to_comp -> Primrec.to_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} σ] {f : α -> σ}, (Primrec.{u1, u2} α σ _inst_1 _inst_2 f) -> (Computable.{u1, u2} α σ _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} σ] {f : α -> σ}, (Primrec.{u2, u1} α σ _inst_1 _inst_2 f) -> (Computable.{u2, u1} α σ _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align primrec.to_comp Primrec.to_compₓ'. -/
theorem Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {f : α → σ} (hf : Primrec f) :
    Computable f :=
  (Nat.Partrec.ppred.comp (Nat.Partrec.of_primrec hf)).of_eq fun n => by
    simp <;> cases decode α n <;> simp
#align primrec.to_comp Primrec.to_comp

/- warning: primrec₂.to_comp -> Primrec₂.to_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} σ] {f : α -> β -> σ}, (Primrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_3 f) -> (Computable₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_3 f)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} σ] {f : α -> β -> σ}, (Primrec₂.{u3, u2, u1} α β σ _inst_1 _inst_2 _inst_3 f) -> (Computable₂.{u3, u2, u1} α β σ _inst_1 _inst_2 _inst_3 f)
Case conversion may be inaccurate. Consider using '#align primrec₂.to_comp Primrec₂.to_compₓ'. -/
theorem Primrec₂.to_comp {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] {f : α → β → σ}
    (hf : Primrec₂ f) : Computable₂ f :=
  hf.to_comp
#align primrec₂.to_comp Primrec₂.to_comp

/- warning: computable.partrec -> Computable.partrec is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} σ] {f : α -> σ}, (Computable.{u1, u2} α σ _inst_1 _inst_2 f) -> (Partrec.{u1, u2} α σ _inst_1 _inst_2 ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (α -> σ) (PFun.{u1, u2} α σ) (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> σ) (PFun.{u1, u2} α σ) (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> σ) (PFun.{u1, u2} α σ) (coeBase.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> σ) (PFun.{u1, u2} α σ) (PFun.coe.{u1, u2} α σ)))) f))
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} σ] {f : α -> σ}, (Computable.{u2, u1} α σ _inst_1 _inst_2 f) -> (Partrec.{u2, u1} α σ _inst_1 _inst_2 (PFun.lift.{u2, u1} α σ f))
Case conversion may be inaccurate. Consider using '#align computable.partrec Computable.partrecₓ'. -/
protected theorem Computable.partrec {α σ} [Primcodable α] [Primcodable σ] {f : α → σ}
    (hf : Computable f) : Partrec (f : α →. σ) :=
  hf
#align computable.partrec Computable.partrec

/- warning: computable₂.partrec₂ -> Computable₂.partrec₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} σ] {f : α -> β -> σ}, (Computable₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_3 f) -> (Partrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_3 (fun (a : α) => (fun (a : Sort.{max (succ u2) (succ u3)}) (b : Sort.{max (succ u2) (succ u3)}) [self : HasLiftT.{max (succ u2) (succ u3), max (succ u2) (succ u3)} a b] => self.0) (β -> σ) (PFun.{u2, u3} β σ) (HasLiftT.mk.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (β -> σ) (PFun.{u2, u3} β σ) (CoeTCₓ.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (β -> σ) (PFun.{u2, u3} β σ) (coeBase.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (β -> σ) (PFun.{u2, u3} β σ) (PFun.coe.{u2, u3} β σ)))) (f a)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} σ] {f : α -> β -> σ}, (Computable₂.{u3, u2, u1} α β σ _inst_1 _inst_2 _inst_3 f) -> (Partrec₂.{u3, u2, u1} α β σ _inst_1 _inst_2 _inst_3 (fun (a : α) => PFun.lift.{u2, u1} β σ (f a)))
Case conversion may be inaccurate. Consider using '#align computable₂.partrec₂ Computable₂.partrec₂ₓ'. -/
protected theorem Computable₂.partrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} (hf : Computable₂ f) : Partrec₂ fun a => (f a : β →. σ) :=
  hf
#align computable₂.partrec₂ Computable₂.partrec₂

namespace Computable

variable {α : Type _} {β : Type _} {γ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

/- warning: computable.of_eq -> Computable.of_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] {f : α -> σ} {g : α -> σ}, (Computable.{u1, u2} α σ _inst_1 _inst_4 f) -> (forall (n : α), Eq.{succ u2} σ (f n) (g n)) -> (Computable.{u1, u2} α σ _inst_1 _inst_4 g)
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] {f : α -> σ} {g : α -> σ}, (Computable.{u2, u1} α σ _inst_1 _inst_4 f) -> (forall (n : α), Eq.{succ u1} σ (f n) (g n)) -> (Computable.{u2, u1} α σ _inst_1 _inst_4 g)
Case conversion may be inaccurate. Consider using '#align computable.of_eq Computable.of_eqₓ'. -/
theorem of_eq {f g : α → σ} (hf : Computable f) (H : ∀ n, f n = g n) : Computable g :=
  (funext H : f = g) ▸ hf
#align computable.of_eq Computable.of_eq

/- warning: computable.const -> Computable.const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] (s : σ), Computable.{u1, u2} α σ _inst_1 _inst_4 (fun (a : α) => s)
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] (s : σ), Computable.{u2, u1} α σ _inst_1 _inst_4 (fun (a : α) => s)
Case conversion may be inaccurate. Consider using '#align computable.const Computable.constₓ'. -/
theorem const (s : σ) : Computable fun a : α => s :=
  (Primrec.const _).to_comp
#align computable.const Computable.const

#print Computable.of_option /-
theorem of_option {f : α → Option β} (hf : Computable f) : Partrec fun a => (f a : Part β) :=
  (Nat.Partrec.ppred.comp hf).of_eq fun n =>
    by
    cases' decode α n with a <;> simp
    cases' f a with b <;> simp
#align computable.of_option Computable.of_option
-/

/- warning: computable.to₂ -> Computable.to₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u3} σ] {f : (Prod.{u1, u2} α β) -> σ}, (Computable.{max u1 u2, u3} (Prod.{u1, u2} α β) σ (Primcodable.prod.{u1, u2} α β _inst_1 _inst_2) _inst_4 f) -> (Computable₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_4 (fun (a : α) (b : β) => f (Prod.mk.{u1, u2} α β a b)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u1} σ] {f : (Prod.{u3, u2} α β) -> σ}, (Computable.{max u3 u2, u1} (Prod.{u3, u2} α β) σ (Primcodable.prod.{u3, u2} α β _inst_1 _inst_2) _inst_4 f) -> (Computable₂.{u3, u2, u1} α β σ _inst_1 _inst_2 _inst_4 (fun (a : α) (b : β) => f (Prod.mk.{u3, u2} α β a b)))
Case conversion may be inaccurate. Consider using '#align computable.to₂ Computable.to₂ₓ'. -/
theorem to₂ {f : α × β → σ} (hf : Computable f) : Computable₂ fun a b => f (a, b) :=
  hf.of_eq fun ⟨a, b⟩ => rfl
#align computable.to₂ Computable.to₂

#print Computable.id /-
protected theorem id : Computable (@id α) :=
  Primrec.id.to_comp
#align computable.id Computable.id
-/

/- warning: computable.fst -> Computable.fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β], Computable.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Primcodable.prod.{u1, u2} α β _inst_1 _inst_2) _inst_1 (Prod.fst.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β], Computable.{max u2 u1, u2} (Prod.{u2, u1} α β) α (Primcodable.prod.{u2, u1} α β _inst_1 _inst_2) _inst_1 (Prod.fst.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align computable.fst Computable.fstₓ'. -/
theorem fst : Computable (@Prod.fst α β) :=
  Primrec.fst.to_comp
#align computable.fst Computable.fst

/- warning: computable.snd -> Computable.snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β], Computable.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Primcodable.prod.{u1, u2} α β _inst_1 _inst_2) _inst_2 (Prod.snd.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β], Computable.{max u2 u1, u1} (Prod.{u2, u1} α β) β (Primcodable.prod.{u2, u1} α β _inst_1 _inst_2) _inst_2 (Prod.snd.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align computable.snd Computable.sndₓ'. -/
theorem snd : Computable (@Prod.snd α β) :=
  Primrec.snd.to_comp
#align computable.snd Computable.snd

/- warning: computable.pair -> Computable.pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] {f : α -> β} {g : α -> γ}, (Computable.{u1, u2} α β _inst_1 _inst_2 f) -> (Computable.{u1, u3} α γ _inst_1 _inst_3 g) -> (Computable.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Primcodable.prod.{u2, u3} β γ _inst_2 _inst_3) (fun (a : α) => Prod.mk.{u2, u3} β γ (f a) (g a)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u1} γ] {f : α -> β} {g : α -> γ}, (Computable.{u3, u2} α β _inst_1 _inst_2 f) -> (Computable.{u3, u1} α γ _inst_1 _inst_3 g) -> (Computable.{u3, max u1 u2} α (Prod.{u2, u1} β γ) _inst_1 (Primcodable.prod.{u2, u1} β γ _inst_2 _inst_3) (fun (a : α) => Prod.mk.{u2, u1} β γ (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align computable.pair Computable.pairₓ'. -/
theorem pair {f : α → β} {g : α → γ} (hf : Computable f) (hg : Computable g) :
    Computable fun a => (f a, g a) :=
  (hf.pair hg).of_eq fun n => by cases decode α n <;> simp [(· <*> ·)]
#align computable.pair Computable.pair

#print Computable.unpair /-
theorem unpair : Computable Nat.unpair :=
  Primrec.unpair.to_comp
#align computable.unpair Computable.unpair
-/

#print Computable.succ /-
theorem succ : Computable Nat.succ :=
  Primrec.succ.to_comp
#align computable.succ Computable.succ
-/

#print Computable.pred /-
theorem pred : Computable Nat.pred :=
  Primrec.pred.to_comp
#align computable.pred Computable.pred
-/

#print Computable.nat_bodd /-
theorem nat_bodd : Computable Nat.bodd :=
  Primrec.nat_bodd.to_comp
#align computable.nat_bodd Computable.nat_bodd
-/

#print Computable.nat_div2 /-
theorem nat_div2 : Computable Nat.div2 :=
  Primrec.nat_div2.to_comp
#align computable.nat_div2 Computable.nat_div2
-/

/- warning: computable.sum_inl -> Computable.sum_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β], Computable.{u1, max u1 u2} α (Sum.{u1, u2} α β) _inst_1 (Primcodable.sum.{u1, u2} α β _inst_1 _inst_2) (Sum.inl.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β], Computable.{u2, max u2 u1} α (Sum.{u2, u1} α β) _inst_1 (Primcodable.sum.{u2, u1} α β _inst_1 _inst_2) (Sum.inl.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align computable.sum_inl Computable.sum_inlₓ'. -/
theorem sum_inl : Computable (@Sum.inl α β) :=
  Primrec.sum_inl.to_comp
#align computable.sum_inl Computable.sum_inl

#print Computable.sum_inr /-
theorem sum_inr : Computable (@Sum.inr α β) :=
  Primrec.sum_inr.to_comp
#align computable.sum_inr Computable.sum_inr
-/

#print Computable.list_cons /-
theorem list_cons : Computable₂ (@List.cons α) :=
  Primrec.list_cons.to_comp
#align computable.list_cons Computable.list_cons
-/

#print Computable.list_reverse /-
theorem list_reverse : Computable (@List.reverse α) :=
  Primrec.list_reverse.to_comp
#align computable.list_reverse Computable.list_reverse
-/

#print Computable.list_get? /-
theorem list_get? : Computable₂ (@List.get? α) :=
  Primrec.list_get?.to_comp
#align computable.list_nth Computable.list_get?
-/

#print Computable.list_append /-
theorem list_append : Computable₂ ((· ++ ·) : List α → List α → List α) :=
  Primrec.list_append.to_comp
#align computable.list_append Computable.list_append
-/

#print Computable.list_concat /-
theorem list_concat : Computable₂ fun l (a : α) => l ++ [a] :=
  Primrec.list_concat.to_comp
#align computable.list_concat Computable.list_concat
-/

#print Computable.list_length /-
theorem list_length : Computable (@List.length α) :=
  Primrec.list_length.to_comp
#align computable.list_length Computable.list_length
-/

#print Computable.vector_cons /-
theorem vector_cons {n} : Computable₂ (@Vector.cons α n) :=
  Primrec.vector_cons.to_comp
#align computable.vector_cons Computable.vector_cons
-/

#print Computable.vector_toList /-
theorem vector_toList {n} : Computable (@Vector.toList α n) :=
  Primrec.vector_toList.to_comp
#align computable.vector_to_list Computable.vector_toList
-/

#print Computable.vector_length /-
theorem vector_length {n} : Computable (@Vector.length α n) :=
  Primrec.vector_length.to_comp
#align computable.vector_length Computable.vector_length
-/

#print Computable.vector_head /-
theorem vector_head {n} : Computable (@Vector.head α n) :=
  Primrec.vector_head.to_comp
#align computable.vector_head Computable.vector_head
-/

#print Computable.vector_tail /-
theorem vector_tail {n} : Computable (@Vector.tail α n) :=
  Primrec.vector_tail.to_comp
#align computable.vector_tail Computable.vector_tail
-/

#print Computable.vector_get /-
theorem vector_get {n} : Computable₂ (@Vector.get α n) :=
  Primrec.vector_get.to_comp
#align computable.vector_nth Computable.vector_get
-/

/- warning: computable.vector_nth' clashes with computable.vector_nth -> Computable.vector_get
warning: computable.vector_nth' -> Computable.vector_get is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Primcodable.{u1} α] {n : Nat}, Computable.{u1, u1} (Vector.{u1} α n) ((Fin n) -> α) (Primcodable.vector.{u1} α _inst_1 n) (Primcodable.finArrow.{u1} α _inst_1 n) (Vector.get.{u1} α n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Primcodable.{u1} α] {n : Nat}, Computable₂.{u1, 0, u1} (Vector.{u1} α n) (Fin n) α (Primcodable.vector.{u1} α _inst_1 n) (Primcodable.fin n) _inst_1 (Vector.get.{u1} α n)
Case conversion may be inaccurate. Consider using '#align computable.vector_nth' Computable.vector_getₓ'. -/
theorem vector_get {n} : Computable (@Vector.get α n) :=
  Primrec.vector_nth'.to_comp
#align computable.vector_nth' Computable.vector_get

#print Computable.vector_ofFn' /-
theorem vector_ofFn' {n} : Computable (@Vector.ofFn α n) :=
  Primrec.vector_of_fn'.to_comp
#align computable.vector_of_fn' Computable.vector_ofFn'
-/

#print Computable.fin_app /-
theorem fin_app {n} : Computable₂ (@id (Fin n → σ)) :=
  Primrec.fin_app.to_comp
#align computable.fin_app Computable.fin_app
-/

#print Computable.encode /-
protected theorem encode : Computable (@encode α _) :=
  Primrec.encode.to_comp
#align computable.encode Computable.encode
-/

#print Computable.decode /-
protected theorem decode : Computable (decode α) :=
  Primrec.decode.to_comp
#align computable.decode Computable.decode
-/

#print Computable.ofNat /-
protected theorem ofNat (α) [Denumerable α] : Computable (ofNat α) :=
  (Primrec.ofNat _).to_comp
#align computable.of_nat Computable.ofNat
-/

/- warning: computable.encode_iff -> Computable.encode_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] {f : α -> σ}, Iff (Computable.{u1, 0} α Nat _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (fun (a : α) => Encodable.encode.{u2} σ (Primcodable.toEncodable.{u2} σ _inst_4) (f a))) (Computable.{u1, u2} α σ _inst_1 _inst_4 f)
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] {f : α -> σ}, Iff (Computable.{u2, 0} α Nat _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (fun (a : α) => Encodable.encode.{u1} σ (Primcodable.toEncodable.{u1} σ _inst_4) (f a))) (Computable.{u2, u1} α σ _inst_1 _inst_4 f)
Case conversion may be inaccurate. Consider using '#align computable.encode_iff Computable.encode_iffₓ'. -/
theorem encode_iff {f : α → σ} : (Computable fun a => encode (f a)) ↔ Computable f :=
  Iff.rfl
#align computable.encode_iff Computable.encode_iff

#print Computable.option_some /-
theorem option_some : Computable (@Option.some α) :=
  Primrec.option_some.to_comp
#align computable.option_some Computable.option_some
-/

end Computable

namespace Partrec

variable {α : Type _} {β : Type _} {γ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

open Computable

/- warning: partrec.of_eq -> Partrec.of_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] {f : PFun.{u1, u2} α σ} {g : PFun.{u1, u2} α σ}, (Partrec.{u1, u2} α σ _inst_1 _inst_4 f) -> (forall (n : α), Eq.{succ u2} (Part.{u2} σ) (f n) (g n)) -> (Partrec.{u1, u2} α σ _inst_1 _inst_4 g)
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] {f : PFun.{u2, u1} α σ} {g : PFun.{u2, u1} α σ}, (Partrec.{u2, u1} α σ _inst_1 _inst_4 f) -> (forall (n : α), Eq.{succ u1} (Part.{u1} σ) (f n) (g n)) -> (Partrec.{u2, u1} α σ _inst_1 _inst_4 g)
Case conversion may be inaccurate. Consider using '#align partrec.of_eq Partrec.of_eqₓ'. -/
theorem of_eq {f g : α →. σ} (hf : Partrec f) (H : ∀ n, f n = g n) : Partrec g :=
  (funext H : f = g) ▸ hf
#align partrec.of_eq Partrec.of_eq

/- warning: partrec.of_eq_tot -> Partrec.of_eq_tot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] {f : PFun.{u1, u2} α σ} {g : α -> σ}, (Partrec.{u1, u2} α σ _inst_1 _inst_4 f) -> (forall (n : α), Membership.Mem.{u2, u2} σ (Part.{u2} σ) (Part.hasMem.{u2} σ) (g n) (f n)) -> (Computable.{u1, u2} α σ _inst_1 _inst_4 g)
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] {f : PFun.{u2, u1} α σ} {g : α -> σ}, (Partrec.{u2, u1} α σ _inst_1 _inst_4 f) -> (forall (n : α), Membership.mem.{u1, u1} σ (Part.{u1} σ) (Part.instMembershipPart.{u1} σ) (g n) (f n)) -> (Computable.{u2, u1} α σ _inst_1 _inst_4 g)
Case conversion may be inaccurate. Consider using '#align partrec.of_eq_tot Partrec.of_eq_totₓ'. -/
theorem of_eq_tot {f : α →. σ} {g : α → σ} (hf : Partrec f) (H : ∀ n, g n ∈ f n) : Computable g :=
  hf.of_eq fun a => eq_some_iff.2 (H a)
#align partrec.of_eq_tot Partrec.of_eq_tot

/- warning: partrec.none -> Partrec.none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ], Partrec.{u1, u2} α σ _inst_1 _inst_4 (fun (a : α) => Part.none.{u2} σ)
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ], Partrec.{u2, u1} α σ _inst_1 _inst_4 (fun (a : α) => Part.none.{u1} σ)
Case conversion may be inaccurate. Consider using '#align partrec.none Partrec.noneₓ'. -/
theorem none : Partrec fun a : α => @Part.none σ :=
  Nat.Partrec.none.of_eq fun n => by cases decode α n <;> simp
#align partrec.none Partrec.none

#print Partrec.some /-
protected theorem some : Partrec (@Part.some α) :=
  Computable.id
#align partrec.some Partrec.some
-/

#print Decidable.Partrec.const' /-
theorem Decidable.Partrec.const' (s : Part σ) [Decidable s.Dom] : Partrec fun a : α => s :=
  (of_option (const (toOption s))).of_eq fun a => of_toOption s
#align decidable.partrec.const' Decidable.Partrec.const'
-/

#print Partrec.const' /-
theorem const' (s : Part σ) : Partrec fun a : α => s :=
  haveI := Classical.dec s.dom
  Decidable.Partrec.const' s
#align partrec.const' Partrec.const'
-/

/- warning: partrec.bind -> Partrec.bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u3} σ] {f : PFun.{u1, u2} α β} {g : α -> (PFun.{u2, u3} β σ)}, (Partrec.{u1, u2} α β _inst_1 _inst_2 f) -> (Partrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_4 g) -> (Partrec.{u1, u3} α σ _inst_1 _inst_4 (fun (a : α) => Part.bind.{u2, u3} β σ (f a) (g a)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u1} σ] {f : PFun.{u3, u2} α β} {g : α -> (PFun.{u2, u1} β σ)}, (Partrec.{u3, u2} α β _inst_1 _inst_2 f) -> (Partrec₂.{u3, u2, u1} α β σ _inst_1 _inst_2 _inst_4 g) -> (Partrec.{u3, u1} α σ _inst_1 _inst_4 (fun (a : α) => Part.bind.{u2, u1} β σ (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align partrec.bind Partrec.bindₓ'. -/
protected theorem bind {f : α →. β} {g : α → β →. σ} (hf : Partrec f) (hg : Partrec₂ g) :
    Partrec fun a => (f a).bind (g a) :=
  (hg.comp (Nat.Partrec.some.pair hf)).of_eq fun n => by
    simp [(· <*> ·)] <;> cases' e : decode α n with a <;> simp [e, encodek]
#align partrec.bind Partrec.bind

/- warning: partrec.map -> Partrec.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u3} σ] {f : PFun.{u1, u2} α β} {g : α -> β -> σ}, (Partrec.{u1, u2} α β _inst_1 _inst_2 f) -> (Computable₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_4 g) -> (Partrec.{u1, u3} α σ _inst_1 _inst_4 (fun (a : α) => Part.map.{u2, u3} β σ (g a) (f a)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u1} σ] {f : PFun.{u3, u2} α β} {g : α -> β -> σ}, (Partrec.{u3, u2} α β _inst_1 _inst_2 f) -> (Computable₂.{u3, u2, u1} α β σ _inst_1 _inst_2 _inst_4 g) -> (Partrec.{u3, u1} α σ _inst_1 _inst_4 (fun (a : α) => Part.map.{u2, u1} β σ (g a) (f a)))
Case conversion may be inaccurate. Consider using '#align partrec.map Partrec.mapₓ'. -/
theorem map {f : α →. β} {g : α → β → σ} (hf : Partrec f) (hg : Computable₂ g) :
    Partrec fun a => (f a).map (g a) := by
  simpa [bind_some_eq_map] using @Partrec.bind _ _ _ (fun a b => Part.some (g a b)) hf hg
#align partrec.map Partrec.map

/- warning: partrec.to₂ -> Partrec.to₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u3} σ] {f : PFun.{max u1 u2, u3} (Prod.{u1, u2} α β) σ}, (Partrec.{max u1 u2, u3} (Prod.{u1, u2} α β) σ (Primcodable.prod.{u1, u2} α β _inst_1 _inst_2) _inst_4 f) -> (Partrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_4 (fun (a : α) (b : β) => f (Prod.mk.{u1, u2} α β a b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u3} β] [_inst_4 : Primcodable.{u1} σ] {f : PFun.{max u3 u2, u1} (Prod.{u2, u3} α β) σ}, (Partrec.{max u2 u3, u1} (Prod.{u2, u3} α β) σ (Primcodable.prod.{u2, u3} α β _inst_1 _inst_2) _inst_4 f) -> (Partrec₂.{u2, u3, u1} α β σ _inst_1 _inst_2 _inst_4 (fun (a : α) (b : β) => f (Prod.mk.{u2, u3} α β a b)))
Case conversion may be inaccurate. Consider using '#align partrec.to₂ Partrec.to₂ₓ'. -/
theorem to₂ {f : α × β →. σ} (hf : Partrec f) : Partrec₂ fun a b => f (a, b) :=
  hf.of_eq fun ⟨a, b⟩ => rfl
#align partrec.to₂ Partrec.to₂

/- warning: partrec.nat_elim -> Partrec.nat_rec is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] {f : α -> Nat} {g : PFun.{u1, u2} α σ} {h : α -> (PFun.{u2, u2} (Prod.{0, u2} Nat σ) σ)}, (Computable.{u1, 0} α Nat _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) f) -> (Partrec.{u1, u2} α σ _inst_1 _inst_4 g) -> (Partrec₂.{u1, u2, u2} α (Prod.{0, u2} Nat σ) σ _inst_1 (Primcodable.prod.{0, u2} Nat σ (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) _inst_4) _inst_4 h) -> (Partrec.{u1, u2} α σ _inst_1 _inst_4 (fun (a : α) => Nat.rec.{succ u2} (Part.{u2} σ) (g a) (fun (y : Nat) (IH : Part.{u2} σ) => Part.bind.{u2, u2} σ σ IH (fun (i : σ) => h a (Prod.mk.{0, u2} Nat σ y i))) (f a)))
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] {f : α -> Nat} {g : PFun.{u2, u1} α σ} {h : α -> (PFun.{u1, u1} (Prod.{0, u1} Nat σ) σ)}, (Computable.{u2, 0} α Nat _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) f) -> (Partrec.{u2, u1} α σ _inst_1 _inst_4 g) -> (Partrec₂.{u2, u1, u1} α (Prod.{0, u1} Nat σ) σ _inst_1 (Primcodable.prod.{0, u1} Nat σ (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) _inst_4) _inst_4 h) -> (Partrec.{u2, u1} α σ _inst_1 _inst_4 (fun (a : α) => Nat.rec.{succ u1} (fun (x._@.Mathlib.Computability.Partrec._hyg.4628 : Nat) => Part.{u1} σ) (g a) (fun (y : Nat) (IH : Part.{u1} σ) => Part.bind.{u1, u1} σ σ IH (fun (i : σ) => h a (Prod.mk.{0, u1} Nat σ y i))) (f a)))
Case conversion may be inaccurate. Consider using '#align partrec.nat_elim Partrec.nat_recₓ'. -/
theorem nat_rec {f : α → ℕ} {g : α →. σ} {h : α → ℕ × σ →. σ} (hf : Computable f) (hg : Partrec g)
    (hh : Partrec₂ h) : Partrec fun a => (f a).elim (g a) fun y IH => IH.bind fun i => h a (y, i) :=
  (Nat.Partrec.prec' hf hg hh).of_eq fun n =>
    by
    cases' e : decode α n with a <;> simp [e]
    induction' f a with m IH <;> simp
    rw [IH, bind_map]
    congr ; funext s
    simp [encodek]
#align partrec.nat_elim Partrec.nat_rec

/- warning: partrec.comp -> Partrec.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u3} σ] {f : PFun.{u2, u3} β σ} {g : α -> β}, (Partrec.{u2, u3} β σ _inst_2 _inst_4 f) -> (Computable.{u1, u2} α β _inst_1 _inst_2 g) -> (Partrec.{u1, u3} α σ _inst_1 _inst_4 (fun (a : α) => f (g a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u3} β] [_inst_4 : Primcodable.{u2} σ] {f : PFun.{u3, u2} β σ} {g : α -> β}, (Partrec.{u3, u2} β σ _inst_2 _inst_4 f) -> (Computable.{u1, u3} α β _inst_1 _inst_2 g) -> (Partrec.{u1, u2} α σ _inst_1 _inst_4 (fun (a : α) => f (g a)))
Case conversion may be inaccurate. Consider using '#align partrec.comp Partrec.compₓ'. -/
theorem comp {f : β →. σ} {g : α → β} (hf : Partrec f) (hg : Computable g) :
    Partrec fun a => f (g a) :=
  (hf.comp hg).of_eq fun n => by simp <;> cases' e : decode α n with a <;> simp [e, encodek]
#align partrec.comp Partrec.comp

#print Partrec.nat_iff /-
theorem nat_iff {f : ℕ →. ℕ} : Partrec f ↔ Nat.Partrec f := by simp [Partrec, map_id']
#align partrec.nat_iff Partrec.nat_iff
-/

/- warning: partrec.map_encode_iff -> Partrec.map_encode_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] {f : PFun.{u1, u2} α σ}, Iff (Partrec.{u1, 0} α Nat _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (fun (a : α) => Part.map.{u2, 0} σ Nat (Encodable.encode.{u2} σ (Primcodable.toEncodable.{u2} σ _inst_4)) (f a))) (Partrec.{u1, u2} α σ _inst_1 _inst_4 f)
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] {f : PFun.{u2, u1} α σ}, Iff (Partrec.{u2, 0} α Nat _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (fun (a : α) => Part.map.{u1, 0} σ Nat (Encodable.encode.{u1} σ (Primcodable.toEncodable.{u1} σ _inst_4)) (f a))) (Partrec.{u2, u1} α σ _inst_1 _inst_4 f)
Case conversion may be inaccurate. Consider using '#align partrec.map_encode_iff Partrec.map_encode_iffₓ'. -/
theorem map_encode_iff {f : α →. σ} : (Partrec fun a => (f a).map encode) ↔ Partrec f :=
  Iff.rfl
#align partrec.map_encode_iff Partrec.map_encode_iff

end Partrec

namespace Partrec₂

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

#print Partrec₂.unpaired /-
theorem unpaired {f : ℕ → ℕ →. α} : Partrec (Nat.unpaired f) ↔ Partrec₂ f :=
  ⟨fun h => by simpa using h.comp primrec₂.mkpair.to_comp, fun h => h.comp Primrec.unpair.to_comp⟩
#align partrec₂.unpaired Partrec₂.unpaired
-/

#print Partrec₂.unpaired' /-
theorem unpaired' {f : ℕ → ℕ →. ℕ} : Nat.Partrec (Nat.unpaired f) ↔ Partrec₂ f :=
  Partrec.nat_iff.symm.trans unpaired
#align partrec₂.unpaired' Partrec₂.unpaired'
-/

/- warning: partrec₂.comp -> Partrec₂.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {σ : Type.{u4}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] [_inst_5 : Primcodable.{u4} σ] {f : β -> (PFun.{u3, u4} γ σ)} {g : α -> β} {h : α -> γ}, (Partrec₂.{u2, u3, u4} β γ σ _inst_2 _inst_3 _inst_5 f) -> (Computable.{u1, u2} α β _inst_1 _inst_2 g) -> (Computable.{u1, u3} α γ _inst_1 _inst_3 h) -> (Partrec.{u1, u4} α σ _inst_1 _inst_5 (fun (a : α) => f (g a) (h a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u4} γ] [_inst_5 : Primcodable.{u3} σ] {f : β -> (PFun.{u4, u3} γ σ)} {g : α -> β} {h : α -> γ}, (Partrec₂.{u2, u4, u3} β γ σ _inst_2 _inst_3 _inst_5 f) -> (Computable.{u1, u2} α β _inst_1 _inst_2 g) -> (Computable.{u1, u4} α γ _inst_1 _inst_3 h) -> (Partrec.{u1, u3} α σ _inst_1 _inst_5 (fun (a : α) => f (g a) (h a)))
Case conversion may be inaccurate. Consider using '#align partrec₂.comp Partrec₂.compₓ'. -/
theorem comp {f : β → γ →. σ} {g : α → β} {h : α → γ} (hf : Partrec₂ f) (hg : Computable g)
    (hh : Computable h) : Partrec fun a => f (g a) (h a) :=
  hf.comp (hg.pair hh)
#align partrec₂.comp Partrec₂.comp

/- warning: partrec₂.comp₂ -> Partrec₂.comp₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {σ : Type.{u5}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] [_inst_4 : Primcodable.{u4} δ] [_inst_5 : Primcodable.{u5} σ] {f : γ -> (PFun.{u4, u5} δ σ)} {g : α -> β -> γ} {h : α -> β -> δ}, (Partrec₂.{u3, u4, u5} γ δ σ _inst_3 _inst_4 _inst_5 f) -> (Computable₂.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g) -> (Computable₂.{u1, u2, u4} α β δ _inst_1 _inst_2 _inst_4 h) -> (Partrec₂.{u1, u2, u5} α β σ _inst_1 _inst_2 _inst_5 (fun (a : α) (b : β) => f (g a b) (h a b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {δ : Type.{u5}} {σ : Type.{u4}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] [_inst_3 : Primcodable.{u3} γ] [_inst_4 : Primcodable.{u5} δ] [_inst_5 : Primcodable.{u4} σ] {f : γ -> (PFun.{u5, u4} δ σ)} {g : α -> β -> γ} {h : α -> β -> δ}, (Partrec₂.{u3, u5, u4} γ δ σ _inst_3 _inst_4 _inst_5 f) -> (Computable₂.{u2, u1, u3} α β γ _inst_1 _inst_2 _inst_3 g) -> (Computable₂.{u2, u1, u5} α β δ _inst_1 _inst_2 _inst_4 h) -> (Partrec₂.{u2, u1, u4} α β σ _inst_1 _inst_2 _inst_5 (fun (a : α) (b : β) => f (g a b) (h a b)))
Case conversion may be inaccurate. Consider using '#align partrec₂.comp₂ Partrec₂.comp₂ₓ'. -/
theorem comp₂ {f : γ → δ →. σ} {g : α → β → γ} {h : α → β → δ} (hf : Partrec₂ f)
    (hg : Computable₂ g) (hh : Computable₂ h) : Partrec₂ fun a b => f (g a b) (h a b) :=
  hf.comp hg hh
#align partrec₂.comp₂ Partrec₂.comp₂

end Partrec₂

namespace Computable

variable {α : Type _} {β : Type _} {γ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

/- warning: computable.comp -> Computable.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u3} σ] {f : β -> σ} {g : α -> β}, (Computable.{u2, u3} β σ _inst_2 _inst_4 f) -> (Computable.{u1, u2} α β _inst_1 _inst_2 g) -> (Computable.{u1, u3} α σ _inst_1 _inst_4 (fun (a : α) => f (g a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u3} β] [_inst_4 : Primcodable.{u2} σ] {f : β -> σ} {g : α -> β}, (Computable.{u3, u2} β σ _inst_2 _inst_4 f) -> (Computable.{u1, u3} α β _inst_1 _inst_2 g) -> (Computable.{u1, u2} α σ _inst_1 _inst_4 (fun (a : α) => f (g a)))
Case conversion may be inaccurate. Consider using '#align computable.comp Computable.compₓ'. -/
theorem comp {f : β → σ} {g : α → β} (hf : Computable f) (hg : Computable g) :
    Computable fun a => f (g a) :=
  hf.comp hg
#align computable.comp Computable.comp

/- warning: computable.comp₂ -> Computable.comp₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {σ : Type.{u4}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] [_inst_4 : Primcodable.{u4} σ] {f : γ -> σ} {g : α -> β -> γ}, (Computable.{u3, u4} γ σ _inst_3 _inst_4 f) -> (Computable₂.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g) -> (Computable₂.{u1, u2, u4} α β σ _inst_1 _inst_2 _inst_4 (fun (a : α) (b : β) => f (g a b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u4}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] [_inst_3 : Primcodable.{u4} γ] [_inst_4 : Primcodable.{u3} σ] {f : γ -> σ} {g : α -> β -> γ}, (Computable.{u4, u3} γ σ _inst_3 _inst_4 f) -> (Computable₂.{u2, u1, u4} α β γ _inst_1 _inst_2 _inst_3 g) -> (Computable₂.{u2, u1, u3} α β σ _inst_1 _inst_2 _inst_4 (fun (a : α) (b : β) => f (g a b)))
Case conversion may be inaccurate. Consider using '#align computable.comp₂ Computable.comp₂ₓ'. -/
theorem comp₂ {f : γ → σ} {g : α → β → γ} (hf : Computable f) (hg : Computable₂ g) :
    Computable₂ fun a b => f (g a b) :=
  hf.comp hg
#align computable.comp₂ Computable.comp₂

end Computable

namespace Computable₂

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

/- warning: computable₂.comp -> Computable₂.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {σ : Type.{u4}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] [_inst_5 : Primcodable.{u4} σ] {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}, (Computable₂.{u2, u3, u4} β γ σ _inst_2 _inst_3 _inst_5 f) -> (Computable.{u1, u2} α β _inst_1 _inst_2 g) -> (Computable.{u1, u3} α γ _inst_1 _inst_3 h) -> (Computable.{u1, u4} α σ _inst_1 _inst_5 (fun (a : α) => f (g a) (h a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u4}} {γ : Type.{u3}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u4} β] [_inst_3 : Primcodable.{u3} γ] [_inst_5 : Primcodable.{u2} σ] {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}, (Computable₂.{u4, u3, u2} β γ σ _inst_2 _inst_3 _inst_5 f) -> (Computable.{u1, u4} α β _inst_1 _inst_2 g) -> (Computable.{u1, u3} α γ _inst_1 _inst_3 h) -> (Computable.{u1, u2} α σ _inst_1 _inst_5 (fun (a : α) => f (g a) (h a)))
Case conversion may be inaccurate. Consider using '#align computable₂.comp Computable₂.compₓ'. -/
theorem comp {f : β → γ → σ} {g : α → β} {h : α → γ} (hf : Computable₂ f) (hg : Computable g)
    (hh : Computable h) : Computable fun a => f (g a) (h a) :=
  hf.comp (hg.pair hh)
#align computable₂.comp Computable₂.comp

/- warning: computable₂.comp₂ -> Computable₂.comp₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {σ : Type.{u5}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] [_inst_4 : Primcodable.{u4} δ] [_inst_5 : Primcodable.{u5} σ] {f : γ -> δ -> σ} {g : α -> β -> γ} {h : α -> β -> δ}, (Computable₂.{u3, u4, u5} γ δ σ _inst_3 _inst_4 _inst_5 f) -> (Computable₂.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g) -> (Computable₂.{u1, u2, u4} α β δ _inst_1 _inst_2 _inst_4 h) -> (Computable₂.{u1, u2, u5} α β σ _inst_1 _inst_2 _inst_5 (fun (a : α) (b : β) => f (g a b) (h a b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u5}} {δ : Type.{u4}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] [_inst_3 : Primcodable.{u5} γ] [_inst_4 : Primcodable.{u4} δ] [_inst_5 : Primcodable.{u3} σ] {f : γ -> δ -> σ} {g : α -> β -> γ} {h : α -> β -> δ}, (Computable₂.{u5, u4, u3} γ δ σ _inst_3 _inst_4 _inst_5 f) -> (Computable₂.{u2, u1, u5} α β γ _inst_1 _inst_2 _inst_3 g) -> (Computable₂.{u2, u1, u4} α β δ _inst_1 _inst_2 _inst_4 h) -> (Computable₂.{u2, u1, u3} α β σ _inst_1 _inst_2 _inst_5 (fun (a : α) (b : β) => f (g a b) (h a b)))
Case conversion may be inaccurate. Consider using '#align computable₂.comp₂ Computable₂.comp₂ₓ'. -/
theorem comp₂ {f : γ → δ → σ} {g : α → β → γ} {h : α → β → δ} (hf : Computable₂ f)
    (hg : Computable₂ g) (hh : Computable₂ h) : Computable₂ fun a b => f (g a b) (h a b) :=
  hf.comp hg hh
#align computable₂.comp₂ Computable₂.comp₂

end Computable₂

namespace Partrec

variable {α : Type _} {β : Type _} {γ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

open Computable

#print Partrec.rfind /-
theorem rfind {p : α → ℕ →. Bool} (hp : Partrec₂ p) : Partrec fun a => Nat.rfind (p a) :=
  (Nat.Partrec.rfind <|
        hp.map ((Primrec.dom_bool fun b => cond b 0 1).comp Primrec.snd).to₂.to_comp).of_eq
    fun n => by
    cases' e : decode α n with a <;> simp [e, Nat.rfind_zero_none, map_id']
    congr ; funext n
    simp [Part.map_map, (· ∘ ·)]
    apply map_id' fun b => _
    cases b <;> rfl
#align partrec.rfind Partrec.rfind
-/

#print Partrec.rfindOpt /-
theorem rfindOpt {f : α → ℕ → Option σ} (hf : Computable₂ f) :
    Partrec fun a => Nat.rfindOpt (f a) :=
  (rfind (Primrec.option_isSome.to_comp.comp hf).Partrec.to₂).bind (of_option hf)
#align partrec.rfind_opt Partrec.rfindOpt
-/

#print Partrec.nat_casesOn_right /-
theorem nat_casesOn_right {f : α → ℕ} {g : α → σ} {h : α → ℕ →. σ} (hf : Computable f)
    (hg : Computable g) (hh : Partrec₂ h) : Partrec fun a => (f a).cases (some (g a)) (h a) :=
  (nat_rec hf hg (hh.comp fst (pred.comp <| hf.comp fst)).to₂).of_eq fun a =>
    by
    simp; cases f a <;> simp
    refine' ext fun b => ⟨fun H => _, fun H => _⟩
    · rcases mem_bind_iff.1 H with ⟨c, h₁, h₂⟩
      exact h₂
    · have : ∀ m, (Nat.rec (Part.some (g a)) (fun y IH => IH.bind fun _ => h a n) m).Dom :=
        by
        intro
        induction m <;> simp [*, H.fst]
      exact ⟨⟨this n, H.fst⟩, H.snd⟩
#align partrec.nat_cases_right Partrec.nat_casesOn_right
-/

/- warning: partrec.bind_decode₂_iff -> Partrec.bind_decode₂_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] {f : PFun.{u1, u2} α σ}, Iff (Partrec.{u1, u2} α σ _inst_1 _inst_4 f) (Nat.Partrec (fun (n : Nat) => Part.bind.{u1, 0} α Nat ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Option.{u1} α) (Part.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Option.{u1} α) (Part.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Option.{u1} α) (Part.{u1} α) (coeBase.{succ u1, succ u1} (Option.{u1} α) (Part.{u1} α) (Part.hasCoe.{u1} α)))) (Encodable.decode₂.{u1} α (Primcodable.toEncodable.{u1} α _inst_1) n)) (fun (a : α) => Part.map.{u2, 0} σ Nat (Encodable.encode.{u2} σ (Primcodable.toEncodable.{u2} σ _inst_4)) (f a))))
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] {f : PFun.{u2, u1} α σ}, Iff (Partrec.{u2, u1} α σ _inst_1 _inst_4 f) (Nat.Partrec (fun (n : Nat) => Part.bind.{u2, 0} α Nat (Part.ofOption.{u2} α (Encodable.decode₂.{u2} α (Primcodable.toEncodable.{u2} α _inst_1) n)) (fun (a : α) => Part.map.{u1, 0} σ Nat (Encodable.encode.{u1} σ (Primcodable.toEncodable.{u1} σ _inst_4)) (f a))))
Case conversion may be inaccurate. Consider using '#align partrec.bind_decode₂_iff Partrec.bind_decode₂_iffₓ'. -/
theorem bind_decode₂_iff {f : α →. σ} :
    Partrec f ↔ Nat.Partrec fun n => Part.bind (decode₂ α n) fun a => (f a).map encode :=
  ⟨fun hf =>
    nat_iff.1 <|
      (of_option Primrec.decode₂.to_comp).bind <|
        (map hf (Computable.encode.comp snd).to₂).comp snd,
    fun h =>
    map_encode_iff.1 <| by simpa [encodek₂] using (nat_iff.2 h).comp (@Computable.encode α _)⟩
#align partrec.bind_decode₂_iff Partrec.bind_decode₂_iff

/- warning: partrec.vector_m_of_fn -> Partrec.vector_mOfFn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] {n : Nat} {f : (Fin n) -> (PFun.{u1, u2} α σ)}, (forall (i : Fin n), Partrec.{u1, u2} α σ _inst_1 _inst_4 (f i)) -> (Partrec.{u1, u2} α (Vector.{u2} σ n) _inst_1 (Primcodable.vector.{u2} σ _inst_4 n) (fun (a : α) => Vector.mOfFn.{u2, u2} Part.{u2} Part.monad.{u2} σ n (fun (i : Fin n) => f i a)))
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] {n : Nat} {f : (Fin n) -> (PFun.{u2, u1} α σ)}, (forall (i : Fin n), Partrec.{u2, u1} α σ _inst_1 _inst_4 (f i)) -> (Partrec.{u2, u1} α (Vector.{u1} σ n) _inst_1 (Primcodable.vector.{u1} σ _inst_4 n) (fun (a : α) => Vector.mOfFn.{u1, u1} Part.{u1} Part.instMonadPart.{u1} σ n (fun (i : Fin n) => f i a)))
Case conversion may be inaccurate. Consider using '#align partrec.vector_m_of_fn Partrec.vector_mOfFnₓ'. -/
theorem vector_mOfFn :
    ∀ {n} {f : Fin n → α →. σ},
      (∀ i, Partrec (f i)) → Partrec fun a : α => Vector.mOfFn fun i => f i a
  | 0, f, hf => const _
  | n + 1, f, hf => by
    simp [Vector.mOfFn] <;>
      exact
        (hf 0).bind
          (Partrec.bind ((vector_m_of_fn fun i => hf i.succ).comp fst)
            (primrec.vector_cons.to_comp.comp (snd.comp fst) snd))
#align partrec.vector_m_of_fn Partrec.vector_mOfFn

end Partrec

/- warning: vector.m_of_fn_part_some -> Vector.mOfFn_part_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat} (f : (Fin n) -> α), Eq.{succ u1} (Part.{u1} (Vector.{u1} α n)) (Vector.mOfFn.{u1, u1} Part.{u1} Part.monad.{u1} α n (fun (i : Fin n) => Part.some.{u1} α (f i))) (Part.some.{u1} (Vector.{u1} α n) (Vector.ofFn.{u1} α n f))
but is expected to have type
  forall {α : Type.{u1}} {n : Nat} (f : (Fin n) -> α), Eq.{succ u1} (Part.{u1} (Vector.{u1} α n)) (Vector.mOfFn.{u1, u1} Part.{u1} Part.instMonadPart.{u1} α n (fun (i : Fin n) => Part.some.{u1} α (f i))) (Part.some.{u1} (Vector.{u1} α n) (Vector.ofFn.{u1} α n f))
Case conversion may be inaccurate. Consider using '#align vector.m_of_fn_part_some Vector.mOfFn_part_someₓ'. -/
@[simp]
theorem Vector.mOfFn_part_some {α n} :
    ∀ f : Fin n → α, (Vector.mOfFn fun i => Part.some (f i)) = Part.some (Vector.ofFn f) :=
  Vector.mOfFn_pure
#align vector.m_of_fn_part_some Vector.mOfFn_part_some

namespace Computable

variable {α : Type _} {β : Type _} {γ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

/- warning: computable.option_some_iff -> Computable.option_some_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] {f : α -> σ}, Iff (Computable.{u1, u2} α (Option.{u2} σ) _inst_1 (Primcodable.option.{u2} σ _inst_4) (fun (a : α) => Option.some.{u2} σ (f a))) (Computable.{u1, u2} α σ _inst_1 _inst_4 f)
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] {f : α -> σ}, Iff (Computable.{u2, u1} α (Option.{u1} σ) _inst_1 (Primcodable.option.{u1} σ _inst_4) (fun (a : α) => Option.some.{u1} σ (f a))) (Computable.{u2, u1} α σ _inst_1 _inst_4 f)
Case conversion may be inaccurate. Consider using '#align computable.option_some_iff Computable.option_some_iffₓ'. -/
theorem option_some_iff {f : α → σ} : (Computable fun a => some (f a)) ↔ Computable f :=
  ⟨fun h => encode_iff.1 <| Primrec.pred.to_comp.comp <| encode_iff.2 h, option_some.comp⟩
#align computable.option_some_iff Computable.option_some_iff

/- warning: computable.bind_decode_iff -> Computable.bind_decode_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u3} σ] {f : α -> β -> (Option.{u3} σ)}, Iff (Computable₂.{u1, 0, u3} α Nat (Option.{u3} σ) _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.option.{u3} σ _inst_4) (fun (a : α) (n : Nat) => Option.bind.{u2, u3} β σ (Encodable.decode.{u2} β (Primcodable.toEncodable.{u2} β _inst_2) n) (f a))) (Computable₂.{u1, u2, u3} α β (Option.{u3} σ) _inst_1 _inst_2 (Primcodable.option.{u3} σ _inst_4) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u1} β] [_inst_4 : Primcodable.{u3} σ] {f : α -> β -> (Option.{u3} σ)}, Iff (Computable₂.{u2, 0, u3} α Nat (Option.{u3} σ) _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.option.{u3} σ _inst_4) (fun (a : α) (n : Nat) => Option.bind.{u1, u3} β σ (Encodable.decode.{u1} β (Primcodable.toEncodable.{u1} β _inst_2) n) (f a))) (Computable₂.{u2, u1, u3} α β (Option.{u3} σ) _inst_1 _inst_2 (Primcodable.option.{u3} σ _inst_4) f)
Case conversion may be inaccurate. Consider using '#align computable.bind_decode_iff Computable.bind_decode_iffₓ'. -/
theorem bind_decode_iff {f : α → β → Option σ} :
    (Computable₂ fun a n => (decode β n).bind (f a)) ↔ Computable₂ f :=
  ⟨fun hf =>
    Nat.Partrec.of_eq
      (((Partrec.nat_iff.2
                (Nat.Partrec.ppred.comp <| Nat.Partrec.of_primrec <| Primcodable.prim β)).comp
            snd).bind
        (Computable.comp hf fst).to₂.Partrec₂)
      fun n => by
      simp <;> cases decode α n.unpair.1 <;> simp <;> cases decode β n.unpair.2 <;> simp,
    fun hf =>
    by
    have :
      Partrec fun a : α × ℕ =>
        (encode (decode β a.2)).cases (some Option.none) fun n => Part.map (f a.1) (decode β n) :=
      Partrec.nat_casesOn_right (primrec.encdec.to_comp.comp snd) (const none)
        ((of_option (computable.decode.comp snd)).map (hf.comp (fst.comp <| fst.comp fst) snd).to₂)
    refine' this.of_eq fun a => _
    simp; cases decode β a.2 <;> simp [encodek]⟩
#align computable.bind_decode_iff Computable.bind_decode_iff

/- warning: computable.map_decode_iff -> Computable.map_decode_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u3} σ] {f : α -> β -> σ}, Iff (Computable₂.{u1, 0, u3} α Nat (Option.{u3} σ) _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.option.{u3} σ _inst_4) (fun (a : α) (n : Nat) => Option.map.{u2, u3} β σ (f a) (Encodable.decode.{u2} β (Primcodable.toEncodable.{u2} β _inst_2) n))) (Computable₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_4 f)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u3} α] [_inst_2 : Primcodable.{u1} β] [_inst_4 : Primcodable.{u2} σ] {f : α -> β -> σ}, Iff (Computable₂.{u3, 0, u2} α Nat (Option.{u2} σ) _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) (Primcodable.option.{u2} σ _inst_4) (fun (a : α) (n : Nat) => Option.map.{u1, u2} β σ (f a) (Encodable.decode.{u1} β (Primcodable.toEncodable.{u1} β _inst_2) n))) (Computable₂.{u3, u1, u2} α β σ _inst_1 _inst_2 _inst_4 f)
Case conversion may be inaccurate. Consider using '#align computable.map_decode_iff Computable.map_decode_iffₓ'. -/
theorem map_decode_iff {f : α → β → σ} :
    (Computable₂ fun a n => (decode β n).map (f a)) ↔ Computable₂ f :=
  bind_decode_iff.trans option_some_iff
#align computable.map_decode_iff Computable.map_decode_iff

#print Computable.nat_rec /-
theorem nat_rec {f : α → ℕ} {g : α → σ} {h : α → ℕ × σ → σ} (hf : Computable f) (hg : Computable g)
    (hh : Computable₂ h) : Computable fun a => (f a).elim (g a) fun y IH => h a (y, IH) :=
  (Partrec.nat_rec hf hg hh.Partrec₂).of_eq fun a => by simp <;> induction f a <;> simp [*]
#align computable.nat_elim Computable.nat_rec
-/

/- warning: computable.nat_cases -> Computable.nat_casesOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] {f : α -> Nat} {g : α -> σ} {h : α -> Nat -> σ}, (Computable.{u1, 0} α Nat _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) f) -> (Computable.{u1, u2} α σ _inst_1 _inst_4 g) -> (Computable₂.{u1, 0, u2} α Nat σ _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) _inst_4 h) -> (Computable.{u1, u2} α σ _inst_1 _inst_4 (fun (a : α) => Nat.casesOn.{succ u2} σ (g a) (h a) (f a)))
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] {f : α -> Nat} {g : α -> σ} {h : α -> Nat -> σ}, (Computable.{u2, 0} α Nat _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) f) -> (Computable.{u2, u1} α σ _inst_1 _inst_4 g) -> (Computable₂.{u2, 0, u1} α Nat σ _inst_1 (Primcodable.ofDenumerable.{0} Nat Denumerable.nat) _inst_4 h) -> (Computable.{u2, u1} α σ _inst_1 _inst_4 (fun (a : α) => Nat.casesOn.{succ u1} (fun (x._@.Mathlib.Computability.Partrec._hyg.6892 : Nat) => σ) (f a) (g a) (h a)))
Case conversion may be inaccurate. Consider using '#align computable.nat_cases Computable.nat_casesOnₓ'. -/
theorem nat_casesOn {f : α → ℕ} {g : α → σ} {h : α → ℕ → σ} (hf : Computable f) (hg : Computable g)
    (hh : Computable₂ h) : Computable fun a => (f a).cases (g a) (h a) :=
  nat_rec hf hg (hh.comp fst <| fst.comp snd).to₂
#align computable.nat_cases Computable.nat_casesOn

/- warning: computable.cond -> Computable.cond is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] {c : α -> Bool} {f : α -> σ} {g : α -> σ}, (Computable.{u1, 0} α Bool _inst_1 Primcodable.bool c) -> (Computable.{u1, u2} α σ _inst_1 _inst_4 f) -> (Computable.{u1, u2} α σ _inst_1 _inst_4 g) -> (Computable.{u1, u2} α σ _inst_1 _inst_4 (fun (a : α) => cond.{u2} σ (c a) (f a) (g a)))
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] {c : α -> Bool} {f : α -> σ} {g : α -> σ}, (Computable.{u2, 0} α Bool _inst_1 Primcodable.bool c) -> (Computable.{u2, u1} α σ _inst_1 _inst_4 f) -> (Computable.{u2, u1} α σ _inst_1 _inst_4 g) -> (Computable.{u2, u1} α σ _inst_1 _inst_4 (fun (a : α) => cond.{u1} σ (c a) (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align computable.cond Computable.condₓ'. -/
theorem cond {c : α → Bool} {f : α → σ} {g : α → σ} (hc : Computable c) (hf : Computable f)
    (hg : Computable g) : Computable fun a => cond (c a) (f a) (g a) :=
  (nat_casesOn (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq fun a => by cases c a <;> rfl
#align computable.cond Computable.cond

/- warning: computable.option_cases -> Computable.option_cases is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u3} σ] {o : α -> (Option.{u2} β)} {f : α -> σ} {g : α -> β -> σ}, (Computable.{u1, u2} α (Option.{u2} β) _inst_1 (Primcodable.option.{u2} β _inst_2) o) -> (Computable.{u1, u3} α σ _inst_1 _inst_4 f) -> (Computable₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_4 g) -> (Computable.{u1, u3} α σ _inst_1 _inst_4 (fun (a : α) => Option.casesOn.{succ u3, u2} β (fun (_x : Option.{u2} β) => σ) (o a) (f a) (g a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u3} β] [_inst_4 : Primcodable.{u1} σ] {o : α -> (Option.{u3} β)} {f : α -> σ} {g : α -> β -> σ}, (Computable.{u2, u3} α (Option.{u3} β) _inst_1 (Primcodable.option.{u3} β _inst_2) o) -> (Computable.{u2, u1} α σ _inst_1 _inst_4 f) -> (Computable₂.{u2, u3, u1} α β σ _inst_1 _inst_2 _inst_4 g) -> (Computable.{u2, u1} α σ _inst_1 _inst_4 (fun (a : α) => Option.casesOn.{succ u1, u3} β (fun (_x : Option.{u3} β) => σ) (o a) (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align computable.option_cases Computable.option_casesₓ'. -/
theorem option_cases {o : α → Option β} {f : α → σ} {g : α → β → σ} (ho : Computable o)
    (hf : Computable f) (hg : Computable₂ g) :
    @Computable _ σ _ _ fun a => Option.casesOn (o a) (f a) (g a) :=
  option_some_iff.1 <|
    (nat_casesOn (encode_iff.2 ho) (option_some_iff.2 hf) (map_decode_iff.2 hg)).of_eq fun a => by
      cases o a <;> simp [encodek] <;> rfl
#align computable.option_cases Computable.option_cases

/- warning: computable.option_bind -> Computable.option_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u3} σ] {f : α -> (Option.{u2} β)} {g : α -> β -> (Option.{u3} σ)}, (Computable.{u1, u2} α (Option.{u2} β) _inst_1 (Primcodable.option.{u2} β _inst_2) f) -> (Computable₂.{u1, u2, u3} α β (Option.{u3} σ) _inst_1 _inst_2 (Primcodable.option.{u3} σ _inst_4) g) -> (Computable.{u1, u3} α (Option.{u3} σ) _inst_1 (Primcodable.option.{u3} σ _inst_4) (fun (a : α) => Option.bind.{u2, u3} β σ (f a) (g a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u3} β] [_inst_4 : Primcodable.{u2} σ] {f : α -> (Option.{u3} β)} {g : α -> β -> (Option.{u2} σ)}, (Computable.{u1, u3} α (Option.{u3} β) _inst_1 (Primcodable.option.{u3} β _inst_2) f) -> (Computable₂.{u1, u3, u2} α β (Option.{u2} σ) _inst_1 _inst_2 (Primcodable.option.{u2} σ _inst_4) g) -> (Computable.{u1, u2} α (Option.{u2} σ) _inst_1 (Primcodable.option.{u2} σ _inst_4) (fun (a : α) => Option.bind.{u3, u2} β σ (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align computable.option_bind Computable.option_bindₓ'. -/
theorem option_bind {f : α → Option β} {g : α → β → Option σ} (hf : Computable f)
    (hg : Computable₂ g) : Computable fun a => (f a).bind (g a) :=
  (option_cases hf (const Option.none) hg).of_eq fun a => by cases f a <;> rfl
#align computable.option_bind Computable.option_bind

/- warning: computable.option_map -> Computable.option_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u3} σ] {f : α -> (Option.{u2} β)} {g : α -> β -> σ}, (Computable.{u1, u2} α (Option.{u2} β) _inst_1 (Primcodable.option.{u2} β _inst_2) f) -> (Computable₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_4 g) -> (Computable.{u1, u3} α (Option.{u3} σ) _inst_1 (Primcodable.option.{u3} σ _inst_4) (fun (a : α) => Option.map.{u2, u3} β σ (g a) (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u3} β] [_inst_4 : Primcodable.{u1} σ] {f : α -> (Option.{u3} β)} {g : α -> β -> σ}, (Computable.{u2, u3} α (Option.{u3} β) _inst_1 (Primcodable.option.{u3} β _inst_2) f) -> (Computable₂.{u2, u3, u1} α β σ _inst_1 _inst_2 _inst_4 g) -> (Computable.{u2, u1} α (Option.{u1} σ) _inst_1 (Primcodable.option.{u1} σ _inst_4) (fun (a : α) => Option.map.{u3, u1} β σ (g a) (f a)))
Case conversion may be inaccurate. Consider using '#align computable.option_map Computable.option_mapₓ'. -/
theorem option_map {f : α → Option β} {g : α → β → σ} (hf : Computable f) (hg : Computable₂ g) :
    Computable fun a => (f a).map (g a) :=
  option_bind hf (option_some.comp₂ hg)
#align computable.option_map Computable.option_map

#print Computable.option_getD /-
theorem option_getD {f : α → Option β} {g : α → β} (hf : Computable f) (hg : Computable g) :
    Computable fun a => (f a).getD (g a) :=
  (Computable.option_cases hf hg (show Computable₂ fun a b => b from Computable.snd)).of_eq fun a =>
    by cases f a <;> rfl
#align computable.option_get_or_else Computable.option_getD
-/

#print Computable.subtype_mk /-
theorem subtype_mk {f : α → β} {p : β → Prop} [DecidablePred p] {h : ∀ a, p (f a)}
    (hp : PrimrecPred p) (hf : Computable f) :
    @Computable _ _ _ (Primcodable.subtype hp) fun a => (⟨f a, h a⟩ : Subtype p) :=
  hf
#align computable.subtype_mk Computable.subtype_mk
-/

/- warning: computable.sum_cases -> Computable.sum_cases is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {σ : Type.{u4}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] [_inst_4 : Primcodable.{u4} σ] {f : α -> (Sum.{u2, u3} β γ)} {g : α -> β -> σ} {h : α -> γ -> σ}, (Computable.{u1, max u2 u3} α (Sum.{u2, u3} β γ) _inst_1 (Primcodable.sum.{u2, u3} β γ _inst_2 _inst_3) f) -> (Computable₂.{u1, u2, u4} α β σ _inst_1 _inst_2 _inst_4 g) -> (Computable₂.{u1, u3, u4} α γ σ _inst_1 _inst_3 _inst_4 h) -> (Computable.{u1, u4} α σ _inst_1 _inst_4 (fun (a : α) => Sum.casesOn.{succ u4, u2, u3} β γ (fun (_x : Sum.{u2, u3} β γ) => σ) (f a) (g a) (h a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u4}} {γ : Type.{u3}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_2 : Primcodable.{u4} β] [_inst_3 : Primcodable.{u3} γ] [_inst_4 : Primcodable.{u1} σ] {f : α -> (Sum.{u4, u3} β γ)} {g : α -> β -> σ} {h : α -> γ -> σ}, (Computable.{u2, max u4 u3} α (Sum.{u4, u3} β γ) _inst_1 (Primcodable.sum.{u4, u3} β γ _inst_2 _inst_3) f) -> (Computable₂.{u2, u4, u1} α β σ _inst_1 _inst_2 _inst_4 g) -> (Computable₂.{u2, u3, u1} α γ σ _inst_1 _inst_3 _inst_4 h) -> (Computable.{u2, u1} α σ _inst_1 _inst_4 (fun (a : α) => Sum.casesOn.{succ u1, u4, u3} β γ (fun (_x : Sum.{u4, u3} β γ) => σ) (f a) (g a) (h a)))
Case conversion may be inaccurate. Consider using '#align computable.sum_cases Computable.sum_casesₓ'. -/
theorem sum_cases {f : α → Sum β γ} {g : α → β → σ} {h : α → γ → σ} (hf : Computable f)
    (hg : Computable₂ g) (hh : Computable₂ h) :
    @Computable _ σ _ _ fun a => Sum.casesOn (f a) (g a) (h a) :=
  option_some_iff.1 <|
    (cond (nat_bodd.comp <| encode_iff.2 hf)
          (option_map (Computable.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hh)
          (option_map (Computable.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hg)).of_eq
      fun a => by cases' f a with b c <;> simp [Nat.div2_bit, Nat.bodd_bit, encodek] <;> rfl
#align computable.sum_cases Computable.sum_cases

#print Computable.nat_strong_rec /-
theorem nat_strong_rec (f : α → ℕ → σ) {g : α → List σ → Option σ} (hg : Computable₂ g)
    (H : ∀ a n, g a ((List.range n).map (f a)) = some (f a n)) : Computable₂ f :=
  suffices Computable₂ fun a n => (List.range n).map (f a) from
    option_some_iff.1 <|
      (list_get?.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq fun a => by
        simp [List.get?_range (Nat.lt_succ_self a.2)] <;> rfl
  option_some_iff.1 <|
    (nat_rec snd (const (Option.some []))
          (to₂ <|
            option_bind (snd.comp snd) <|
              to₂ <|
                option_map (hg.comp (fst.comp <| fst.comp fst) snd)
                  (to₂ <| list_concat.comp (snd.comp fst) snd))).of_eq
      fun a => by
      simp; induction' a.2 with n IH; · rfl
      simp [IH, H, List.range_succ]
#align computable.nat_strong_rec Computable.nat_strong_rec
-/

/- warning: computable.list_of_fn -> Computable.list_ofFn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] {n : Nat} {f : (Fin n) -> α -> σ}, (forall (i : Fin n), Computable.{u1, u2} α σ _inst_1 _inst_4 (f i)) -> (Computable.{u1, u2} α (List.{u2} σ) _inst_1 (Primcodable.list.{u2} σ _inst_4) (fun (a : α) => List.ofFn.{u2} σ n (fun (i : Fin n) => f i a)))
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] {n : Nat} {f : (Fin n) -> α -> σ}, (forall (i : Fin n), Computable.{u2, u1} α σ _inst_1 _inst_4 (f i)) -> (Computable.{u2, u1} α (List.{u1} σ) _inst_1 (Primcodable.list.{u1} σ _inst_4) (fun (a : α) => List.ofFn.{u1} σ n (fun (i : Fin n) => f i a)))
Case conversion may be inaccurate. Consider using '#align computable.list_of_fn Computable.list_ofFnₓ'. -/
theorem list_ofFn :
    ∀ {n} {f : Fin n → α → σ},
      (∀ i, Computable (f i)) → Computable fun a => List.ofFn fun i => f i a
  | 0, f, hf => const []
  | n + 1, f, hf => by
    simp [List.ofFn_succ] <;> exact list_cons.comp (hf 0) (list_of_fn fun i => hf i.succ)
#align computable.list_of_fn Computable.list_ofFn

/- warning: computable.vector_of_fn -> Computable.vector_ofFn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] {n : Nat} {f : (Fin n) -> α -> σ}, (forall (i : Fin n), Computable.{u1, u2} α σ _inst_1 _inst_4 (f i)) -> (Computable.{u1, u2} α (Vector.{u2} σ n) _inst_1 (Primcodable.vector.{u2} σ _inst_4 n) (fun (a : α) => Vector.ofFn.{u2} σ n (fun (i : Fin n) => f i a)))
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] {n : Nat} {f : (Fin n) -> α -> σ}, (forall (i : Fin n), Computable.{u2, u1} α σ _inst_1 _inst_4 (f i)) -> (Computable.{u2, u1} α (Vector.{u1} σ n) _inst_1 (Primcodable.vector.{u1} σ _inst_4 n) (fun (a : α) => Vector.ofFn.{u1} σ n (fun (i : Fin n) => f i a)))
Case conversion may be inaccurate. Consider using '#align computable.vector_of_fn Computable.vector_ofFnₓ'. -/
theorem vector_ofFn {n} {f : Fin n → α → σ} (hf : ∀ i, Computable (f i)) :
    Computable fun a => Vector.ofFn fun i => f i a :=
  (Partrec.vector_mOfFn hf).of_eq fun a => by simp
#align computable.vector_of_fn Computable.vector_ofFn

end Computable

namespace Partrec

variable {α : Type _} {β : Type _} {γ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

open Computable

/- warning: partrec.option_some_iff -> Partrec.option_some_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] {f : PFun.{u1, u2} α σ}, Iff (Partrec.{u1, u2} α (Option.{u2} σ) _inst_1 (Primcodable.option.{u2} σ _inst_4) (fun (a : α) => Part.map.{u2, u2} σ (Option.{u2} σ) (Option.some.{u2} σ) (f a))) (Partrec.{u1, u2} α σ _inst_1 _inst_4 f)
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] {f : PFun.{u2, u1} α σ}, Iff (Partrec.{u2, u1} α (Option.{u1} σ) _inst_1 (Primcodable.option.{u1} σ _inst_4) (fun (a : α) => Part.map.{u1, u1} σ (Option.{u1} σ) (Option.some.{u1} σ) (f a))) (Partrec.{u2, u1} α σ _inst_1 _inst_4 f)
Case conversion may be inaccurate. Consider using '#align partrec.option_some_iff Partrec.option_some_iffₓ'. -/
theorem option_some_iff {f : α →. σ} : (Partrec fun a => (f a).map Option.some) ↔ Partrec f :=
  ⟨fun h => (Nat.Partrec.ppred.comp h).of_eq fun n => by simp [Part.bind_assoc, bind_some_eq_map],
    fun hf => hf.map (option_some.comp snd).to₂⟩
#align partrec.option_some_iff Partrec.option_some_iff

/- warning: partrec.option_cases_right -> Partrec.option_cases_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {σ : Type.{u3}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_4 : Primcodable.{u3} σ] {o : α -> (Option.{u2} β)} {f : α -> σ} {g : α -> (PFun.{u2, u3} β σ)}, (Computable.{u1, u2} α (Option.{u2} β) _inst_1 (Primcodable.option.{u2} β _inst_2) o) -> (Computable.{u1, u3} α σ _inst_1 _inst_4 f) -> (Partrec₂.{u1, u2, u3} α β σ _inst_1 _inst_2 _inst_4 g) -> (Partrec.{u1, u3} α σ _inst_1 _inst_4 (fun (a : α) => Option.casesOn.{succ u3, u2} β (fun (_x : Option.{u2} β) => Part.{u3} σ) (o a) (Part.some.{u3} σ (f a)) (g a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u3} β] [_inst_4 : Primcodable.{u2} σ] {o : α -> (Option.{u3} β)} {f : α -> σ} {g : α -> (PFun.{u3, u2} β σ)}, (Computable.{u1, u3} α (Option.{u3} β) _inst_1 (Primcodable.option.{u3} β _inst_2) o) -> (Computable.{u1, u2} α σ _inst_1 _inst_4 f) -> (Partrec₂.{u1, u3, u2} α β σ _inst_1 _inst_2 _inst_4 g) -> (Partrec.{u1, u2} α σ _inst_1 _inst_4 (fun (a : α) => Option.casesOn.{succ u2, u3} β (fun (_x : Option.{u3} β) => Part.{u2} σ) (o a) (Part.some.{u2} σ (f a)) (g a)))
Case conversion may be inaccurate. Consider using '#align partrec.option_cases_right Partrec.option_cases_rightₓ'. -/
theorem option_cases_right {o : α → Option β} {f : α → σ} {g : α → β →. σ} (ho : Computable o)
    (hf : Computable f) (hg : Partrec₂ g) :
    @Partrec _ σ _ _ fun a => Option.casesOn (o a) (some (f a)) (g a) :=
  have :
    Partrec fun a : α =>
      Nat.casesOn (Part.some (f a)) (fun n => Part.bind (decode β n) (g a)) (encode (o a)) :=
    nat_casesOn_right (encode_iff.2 ho) hf.Partrec <|
      ((@Computable.decode β _).comp snd).ofOption.bind (hg.comp (fst.comp fst) snd).to₂
  this.of_eq fun a => by cases' o a with b <;> simp [encodek]
#align partrec.option_cases_right Partrec.option_cases_right

/- warning: partrec.sum_cases_right -> Partrec.sum_cases_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {σ : Type.{u4}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] [_inst_4 : Primcodable.{u4} σ] {f : α -> (Sum.{u2, u3} β γ)} {g : α -> β -> σ} {h : α -> (PFun.{u3, u4} γ σ)}, (Computable.{u1, max u2 u3} α (Sum.{u2, u3} β γ) _inst_1 (Primcodable.sum.{u2, u3} β γ _inst_2 _inst_3) f) -> (Computable₂.{u1, u2, u4} α β σ _inst_1 _inst_2 _inst_4 g) -> (Partrec₂.{u1, u3, u4} α γ σ _inst_1 _inst_3 _inst_4 h) -> (Partrec.{u1, u4} α σ _inst_1 _inst_4 (fun (a : α) => Sum.casesOn.{succ u4, u2, u3} β γ (fun (_x : Sum.{u2, u3} β γ) => Part.{u4} σ) (f a) (fun (b : β) => Part.some.{u4} σ (g a b)) (h a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u4}} {γ : Type.{u3}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u4} β] [_inst_3 : Primcodable.{u3} γ] [_inst_4 : Primcodable.{u2} σ] {f : α -> (Sum.{u4, u3} β γ)} {g : α -> β -> σ} {h : α -> (PFun.{u3, u2} γ σ)}, (Computable.{u1, max u4 u3} α (Sum.{u4, u3} β γ) _inst_1 (Primcodable.sum.{u4, u3} β γ _inst_2 _inst_3) f) -> (Computable₂.{u1, u4, u2} α β σ _inst_1 _inst_2 _inst_4 g) -> (Partrec₂.{u1, u3, u2} α γ σ _inst_1 _inst_3 _inst_4 h) -> (Partrec.{u1, u2} α σ _inst_1 _inst_4 (fun (a : α) => Sum.casesOn.{succ u2, u4, u3} β γ (fun (_x : Sum.{u4, u3} β γ) => Part.{u2} σ) (f a) (fun (b : β) => Part.some.{u2} σ (g a b)) (h a)))
Case conversion may be inaccurate. Consider using '#align partrec.sum_cases_right Partrec.sum_cases_rightₓ'. -/
theorem sum_cases_right {f : α → Sum β γ} {g : α → β → σ} {h : α → γ →. σ} (hf : Computable f)
    (hg : Computable₂ g) (hh : Partrec₂ h) :
    @Partrec _ σ _ _ fun a => Sum.casesOn (f a) (fun b => some (g a b)) (h a) :=
  have :
    Partrec fun a =>
      (Option.casesOn (Sum.casesOn (f a) (fun b => Option.none) Option.some : Option γ)
          (some (Sum.casesOn (f a) (fun b => some (g a b)) fun c => Option.none)) fun c =>
          (h a c).map Option.some :
        Part (Option σ)) :=
    option_cases_right (sum_cases hf (const Option.none).to₂ (option_some.comp snd).to₂)
      (sum_cases hf (option_some.comp hg) (const Option.none).to₂) (option_some_iff.2 hh)
  option_some_iff.1 <| this.of_eq fun a => by cases f a <;> simp
#align partrec.sum_cases_right Partrec.sum_cases_right

/- warning: partrec.sum_cases_left -> Partrec.sum_cases_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {σ : Type.{u4}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u2} β] [_inst_3 : Primcodable.{u3} γ] [_inst_4 : Primcodable.{u4} σ] {f : α -> (Sum.{u2, u3} β γ)} {g : α -> (PFun.{u2, u4} β σ)} {h : α -> γ -> σ}, (Computable.{u1, max u2 u3} α (Sum.{u2, u3} β γ) _inst_1 (Primcodable.sum.{u2, u3} β γ _inst_2 _inst_3) f) -> (Partrec₂.{u1, u2, u4} α β σ _inst_1 _inst_2 _inst_4 g) -> (Computable₂.{u1, u3, u4} α γ σ _inst_1 _inst_3 _inst_4 h) -> (Partrec.{u1, u4} α σ _inst_1 _inst_4 (fun (a : α) => Sum.casesOn.{succ u4, u2, u3} β γ (fun (_x : Sum.{u2, u3} β γ) => Part.{u4} σ) (f a) (g a) (fun (c : γ) => Part.some.{u4} σ (h a c))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u4}} {γ : Type.{u3}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_2 : Primcodable.{u4} β] [_inst_3 : Primcodable.{u3} γ] [_inst_4 : Primcodable.{u2} σ] {f : α -> (Sum.{u4, u3} β γ)} {g : α -> (PFun.{u4, u2} β σ)} {h : α -> γ -> σ}, (Computable.{u1, max u4 u3} α (Sum.{u4, u3} β γ) _inst_1 (Primcodable.sum.{u4, u3} β γ _inst_2 _inst_3) f) -> (Partrec₂.{u1, u4, u2} α β σ _inst_1 _inst_2 _inst_4 g) -> (Computable₂.{u1, u3, u2} α γ σ _inst_1 _inst_3 _inst_4 h) -> (Partrec.{u1, u2} α σ _inst_1 _inst_4 (fun (a : α) => Sum.casesOn.{succ u2, u4, u3} β γ (fun (_x : Sum.{u4, u3} β γ) => Part.{u2} σ) (f a) (g a) (fun (c : γ) => Part.some.{u2} σ (h a c))))
Case conversion may be inaccurate. Consider using '#align partrec.sum_cases_left Partrec.sum_cases_leftₓ'. -/
theorem sum_cases_left {f : α → Sum β γ} {g : α → β →. σ} {h : α → γ → σ} (hf : Computable f)
    (hg : Partrec₂ g) (hh : Computable₂ h) :
    @Partrec _ σ _ _ fun a => Sum.casesOn (f a) (g a) fun c => some (h a c) :=
  (sum_cases_right (sum_cases hf (sum_inr.comp snd).to₂ (sum_inl.comp snd).to₂) hh hg).of_eq
    fun a => by cases f a <;> simp
#align partrec.sum_cases_left Partrec.sum_cases_left

/- warning: partrec.fix_aux -> Partrec.fix_aux is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} (f : PFun.{u1, max u2 u1} α (Sum.{u2, u1} σ α)) (a : α) (b : σ), let F : α -> (PFun.{0, max u2 u1} Nat (Sum.{u2, u1} σ α)) := fun (a : α) (n : Nat) => Nat.rec.{succ (max u2 u1)} (Part.{max u2 u1} (Sum.{u2, u1} σ α)) (Part.some.{max u2 u1} (Sum.{u2, u1} σ α) (Sum.inr.{u2, u1} σ α a)) (fun (y : Nat) (IH : Part.{max u2 u1} (Sum.{u2, u1} σ α)) => Part.bind.{max u2 u1, max u2 u1} (Sum.{u2, u1} σ α) (Sum.{u2, u1} σ α) IH (fun (s : Sum.{u2, u1} σ α) => Sum.casesOn.{succ (max u2 u1), u2, u1} σ α (fun (_x : Sum.{u2, u1} σ α) => Part.{max u2 u1} (Sum.{u2, u1} σ α)) s (fun (_x : σ) => Part.some.{max u2 u1} (Sum.{u2, u1} σ α) s) f)) n; Iff (Exists.{1} Nat (fun (n : Nat) => And (And (Exists.{succ u2} σ (fun (b' : σ) => Membership.Mem.{max u2 u1, max u2 u1} (Sum.{u2, u1} σ α) (Part.{max u2 u1} (Sum.{u2, u1} σ α)) (Part.hasMem.{max u2 u1} (Sum.{u2, u1} σ α)) (Sum.inl.{u2, u1} σ α b') (F a n))) (forall {m : Nat}, (LT.lt.{0} Nat Nat.hasLt m n) -> (Exists.{succ u1} α (fun (b : α) => Membership.Mem.{max u2 u1, max u2 u1} (Sum.{u2, u1} σ α) (Part.{max u2 u1} (Sum.{u2, u1} σ α)) (Part.hasMem.{max u2 u1} (Sum.{u2, u1} σ α)) (Sum.inr.{u2, u1} σ α b) (F a m))))) (Membership.Mem.{max u2 u1, max u2 u1} (Sum.{u2, u1} σ α) (Part.{max u2 u1} (Sum.{u2, u1} σ α)) (Part.hasMem.{max u2 u1} (Sum.{u2, u1} σ α)) (Sum.inl.{u2, u1} σ α b) (F a n)))) (Membership.Mem.{u2, u2} σ (Part.{u2} σ) (Part.hasMem.{u2} σ) b (PFun.fix.{u1, u2} α σ f a))
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} (f : PFun.{u2, max u2 u1} α (Sum.{u1, u2} σ α)) (a : α) (b : σ), let F : α -> (PFun.{0, max u2 u1} Nat (Sum.{u1, u2} σ α)) := fun (a : α) (n : Nat) => Nat.rec.{max (succ u2) (succ u1)} (fun (x._@.Mathlib.Computability.Partrec._hyg.8728 : Nat) => Part.{max u2 u1} (Sum.{u1, u2} σ α)) (Part.some.{max u2 u1} (Sum.{u1, u2} σ α) (Sum.inr.{u1, u2} σ α a)) (fun (y : Nat) (IH : Part.{max u2 u1} (Sum.{u1, u2} σ α)) => Part.bind.{max u2 u1, max u2 u1} (Sum.{u1, u2} σ α) (Sum.{u1, u2} σ α) IH (fun (s : Sum.{u1, u2} σ α) => Sum.casesOn.{max (succ u2) (succ u1), u1, u2} σ α (fun (_x : Sum.{u1, u2} σ α) => Part.{max u2 u1} (Sum.{u1, u2} σ α)) s (fun (_x : σ) => Part.some.{max u2 u1} (Sum.{u1, u2} σ α) s) f)) n; Iff (Exists.{1} Nat (fun (n : Nat) => And (And (Exists.{succ u1} σ (fun (b' : σ) => Membership.mem.{max u2 u1, max u2 u1} (Sum.{u1, u2} σ α) (Part.{max u2 u1} (Sum.{u1, u2} σ α)) (Part.instMembershipPart.{max u1 u2} (Sum.{u1, u2} σ α)) (Sum.inl.{u1, u2} σ α b') (F a n))) (forall {m : Nat}, (LT.lt.{0} Nat instLTNat m n) -> (Exists.{succ u2} α (fun (b : α) => Membership.mem.{max u2 u1, max u2 u1} (Sum.{u1, u2} σ α) (Part.{max u2 u1} (Sum.{u1, u2} σ α)) (Part.instMembershipPart.{max u2 u1} (Sum.{u1, u2} σ α)) (Sum.inr.{u1, u2} σ α b) (F a m))))) (Membership.mem.{max u2 u1, max u2 u1} (Sum.{u1, u2} σ α) (Part.{max u2 u1} (Sum.{u1, u2} σ α)) (Part.instMembershipPart.{max u1 u2} (Sum.{u1, u2} σ α)) (Sum.inl.{u1, u2} σ α b) (F a n)))) (Membership.mem.{u1, u1} σ (Part.{u1} σ) (Part.instMembershipPart.{u1} σ) b (PFun.fix.{u2, u1} α σ f a))
Case conversion may be inaccurate. Consider using '#align partrec.fix_aux Partrec.fix_auxₓ'. -/
theorem fix_aux {α σ} (f : α →. Sum σ α) (a : α) (b : σ) :
    let F : α → ℕ →. Sum σ α := fun a n =>
      n.elim (some (Sum.inr a)) fun y IH => IH.bind fun s => Sum.casesOn s (fun _ => Part.some s) f
    (∃ n : ℕ,
        ((∃ b' : σ, Sum.inl b' ∈ F a n) ∧ ∀ {m : ℕ}, m < n → ∃ b : α, Sum.inr b ∈ F a m) ∧
          Sum.inl b ∈ F a n) ↔
      b ∈ PFun.fix f a :=
  by
  intro ; refine' ⟨fun h => _, fun h => _⟩
  · rcases h with ⟨n, ⟨_x, h₁⟩, h₂⟩
    have : ∀ (m a') (_ : Sum.inr a' ∈ F a m) (_ : b ∈ PFun.fix f a'), b ∈ PFun.fix f a :=
      by
      intro m a' am ba
      induction' m with m IH generalizing a' <;> simp [F] at am
      · rwa [← am]
      rcases am with ⟨a₂, am₂, fa₂⟩
      exact IH _ am₂ (PFun.mem_fix_iff.2 (Or.inr ⟨_, fa₂, ba⟩))
    cases n <;> simp [F] at h₂
    · cases h₂
    rcases h₂ with (h₂ | ⟨a', am', fa'⟩)
    · cases' h₁ (Nat.lt_succ_self _) with a' h
      injection mem_unique h h₂
    · exact this _ _ am' (PFun.mem_fix_iff.2 (Or.inl fa'))
  · suffices
      ∀ (a') (_ : b ∈ PFun.fix f a') (k) (_ : Sum.inr a' ∈ F a k),
        ∃ n, Sum.inl b ∈ F a n ∧ ∀ m < n, ∀ (_ : k ≤ m), ∃ a₂, Sum.inr a₂ ∈ F a m
      by
      rcases this _ h 0 (by simp [F]) with ⟨n, hn₁, hn₂⟩
      exact ⟨_, ⟨⟨_, hn₁⟩, fun m mn => hn₂ m mn (Nat.zero_le _)⟩, hn₁⟩
    intro a₁ h₁
    apply PFun.fixInduction h₁
    intro a₂ h₂ IH k hk
    rcases PFun.mem_fix_iff.1 h₂ with (h₂ | ⟨a₃, am₃, fa₃⟩)
    · refine' ⟨k.succ, _, fun m mk km => ⟨a₂, _⟩⟩
      · simp [F]
        exact Or.inr ⟨_, hk, h₂⟩
      · rwa [le_antisymm (Nat.le_of_lt_succ mk) km]
    · rcases IH _ am₃ k.succ _ with ⟨n, hn₁, hn₂⟩
      · refine' ⟨n, hn₁, fun m mn km => _⟩
        cases' km.lt_or_eq_dec with km km
        · exact hn₂ _ mn km
        · exact km ▸ ⟨_, hk⟩
      · simp [F]
        exact ⟨_, hk, am₃⟩
#align partrec.fix_aux Partrec.fix_aux

/- warning: partrec.fix -> Partrec.fix is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} [_inst_1 : Primcodable.{u1} α] [_inst_4 : Primcodable.{u2} σ] {f : PFun.{u1, max u2 u1} α (Sum.{u2, u1} σ α)}, (Partrec.{u1, max u2 u1} α (Sum.{u2, u1} σ α) _inst_1 (Primcodable.sum.{u2, u1} σ α _inst_4 _inst_1) f) -> (Partrec.{u1, u2} α σ _inst_1 _inst_4 (PFun.fix.{u1, u2} α σ f))
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} [_inst_1 : Primcodable.{u2} α] [_inst_4 : Primcodable.{u1} σ] {f : PFun.{u2, max u2 u1} α (Sum.{u1, u2} σ α)}, (Partrec.{u2, max u2 u1} α (Sum.{u1, u2} σ α) _inst_1 (Primcodable.sum.{u1, u2} σ α _inst_4 _inst_1) f) -> (Partrec.{u2, u1} α σ _inst_1 _inst_4 (PFun.fix.{u2, u1} α σ f))
Case conversion may be inaccurate. Consider using '#align partrec.fix Partrec.fixₓ'. -/
theorem fix {f : α →. Sum σ α} (hf : Partrec f) : Partrec (PFun.fix f) :=
  let F : α → ℕ →. Sum σ α := fun a n =>
    n.elim (some (Sum.inr a)) fun y IH => IH.bind fun s => Sum.casesOn s (fun _ => Part.some s) f
  have hF : Partrec₂ F :=
    Partrec.nat_rec snd (sum_inr.comp fst).Partrec
      (sum_cases_right (snd.comp snd) (snd.comp <| snd.comp fst).to₂ (hf.comp snd).to₂).to₂
  let p a n := @Part.map _ Bool (fun s => Sum.casesOn s (fun _ => true) fun _ => false) (F a n)
  have hp : Partrec₂ p :=
    hF.map ((sum_cases Computable.id (const true).to₂ (const false).to₂).comp snd).to₂
  (hp.rfind.bind (hF.bind (sum_cases_right snd snd.to₂ none.to₂).to₂).to₂).of_eq fun a =>
    ext fun b => by simp <;> apply fix_aux f
#align partrec.fix Partrec.fix

end Partrec

