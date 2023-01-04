/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module computability.partrec
! leanprover-community/mathlib commit d3e8e0a0237c10c2627bf52c246b15ff8e7df4c0
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
  m = n + 1 ∧ ∀ k ≤ n, ff ∈ p k
#align nat.lbp nat.lbp

parameter (H : ∃ n, tt ∈ p n ∧ ∀ k < n, (p k).Dom)

private def wf_lbp : WellFounded lbp :=
  ⟨by
    let ⟨n, pn⟩ := H
    suffices ∀ m k, n ≤ k + m → Acc (lbp p) k by exact fun a => this _ _ (Nat.le_add_left _ _)
    intro m k kn
    induction' m with m IH generalizing k <;> refine' ⟨_, fun y r => _⟩ <;> rcases r with ⟨rfl, a⟩
    · injection mem_unique pn.1 (a _ kn)
    · exact IH _ (by rw [Nat.add_right_comm] <;> exact kn)⟩
#align nat.wf_lbp nat.wf_lbp

def rfindX : { n // tt ∈ p n ∧ ∀ m < n, ff ∈ p m } :=
  suffices ∀ k, (∀ n < k, ff ∈ p n) → { n // tt ∈ p n ∧ ∀ m < n, ff ∈ p m } from
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

end Rfind

def rfind (p : ℕ →. Bool) : Part ℕ :=
  ⟨_, fun h => (rfindX p h).1⟩
#align nat.rfind Nat.rfind

theorem rfind_spec {p : ℕ →. Bool} {n : ℕ} (h : n ∈ rfind p) : tt ∈ p n :=
  h.snd ▸ (rfindX p h.fst).2.1
#align nat.rfind_spec Nat.rfind_spec

theorem rfind_min {p : ℕ →. Bool} {n : ℕ} (h : n ∈ rfind p) : ∀ {m : ℕ}, m < n → ff ∈ p m :=
  h.snd ▸ (rfindX p h.fst).2.2
#align nat.rfind_min Nat.rfind_min

@[simp]
theorem rfind_dom {p : ℕ →. Bool} : (rfind p).Dom ↔ ∃ n, tt ∈ p n ∧ ∀ {m : ℕ}, m < n → (p m).Dom :=
  Iff.rfl
#align nat.rfind_dom Nat.rfind_dom

theorem rfind_dom' {p : ℕ →. Bool} : (rfind p).Dom ↔ ∃ n, tt ∈ p n ∧ ∀ {m : ℕ}, m ≤ n → (p m).Dom :=
  exists_congr fun n =>
    and_congr_right fun pn =>
      ⟨fun H m h => (Decidable.eq_or_lt_of_le h).elim (fun e => e.symm ▸ pn.fst) (H _), fun H m h =>
        H (le_of_lt h)⟩
#align nat.rfind_dom' Nat.rfind_dom'

@[simp]
theorem mem_rfind {p : ℕ →. Bool} {n : ℕ} : n ∈ rfind p ↔ tt ∈ p n ∧ ∀ {m : ℕ}, m < n → ff ∈ p m :=
  ⟨fun h => ⟨rfind_spec h, @rfind_min _ _ h⟩, fun ⟨h₁, h₂⟩ =>
    by
    let ⟨m, hm⟩ := dom_iff_mem.1 <| (@rfind_dom p).2 ⟨_, h₁, fun m mn => (h₂ mn).fst⟩
    rcases lt_trichotomy m n with (h | h | h)
    · injection mem_unique (h₂ h) (rfind_spec hm)
    · rwa [← h]
    · injection mem_unique h₁ (rfind_min hm h)⟩
#align nat.mem_rfind Nat.mem_rfind

theorem rfind_min' {p : ℕ → Bool} {m : ℕ} (pm : p m) : ∃ n ∈ rfind p, n ≤ m :=
  have : tt ∈ (p : ℕ →. Bool) m := ⟨trivial, pm⟩
  let ⟨n, hn⟩ := dom_iff_mem.1 <| (@rfind_dom p).2 ⟨m, this, fun k h => ⟨⟩⟩
  ⟨n, hn, not_lt.1 fun h => by injection mem_unique this (rfind_min hn h)⟩
#align nat.rfind_min' Nat.rfind_min'

theorem rfind_zero_none (p : ℕ →. Bool) (p0 : p 0 = none) : rfind p = none :=
  eq_none_iff.2 fun a h =>
    let ⟨n, h₁, h₂⟩ := rfind_dom'.1 h.fst
    (p0 ▸ h₂ (zero_le _) : (@Part.none Bool).Dom)
#align nat.rfind_zero_none Nat.rfind_zero_none

def rfindOpt {α} (f : ℕ → Option α) : Part α :=
  (rfind fun n => (f n).isSome).bind fun n => f n
#align nat.rfind_opt Nat.rfindOpt

theorem rfind_opt_spec {α} {f : ℕ → Option α} {a} (h : a ∈ rfindOpt f) : ∃ n, a ∈ f n :=
  let ⟨n, h₁, h₂⟩ := mem_bind_iff.1 h
  ⟨n, mem_coe.1 h₂⟩
#align nat.rfind_opt_spec Nat.rfind_opt_spec

theorem rfind_opt_dom {α} {f : ℕ → Option α} : (rfindOpt f).Dom ↔ ∃ n a, a ∈ f n :=
  ⟨fun h => (rfind_opt_spec ⟨h, rfl⟩).imp fun n h => ⟨_, h⟩, fun h =>
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
#align nat.rfind_opt_dom Nat.rfind_opt_dom

theorem rfind_opt_mono {α} {f : ℕ → Option α} (H : ∀ {a m n}, m ≤ n → a ∈ f m → a ∈ f n) {a} :
    a ∈ rfindOpt f ↔ ∃ n, a ∈ f n :=
  ⟨rfind_opt_spec, fun ⟨n, h⟩ =>
    by
    have h' := rfind_opt_dom.2 ⟨_, _, h⟩
    cases' rfind_opt_spec ⟨h', rfl⟩ with k hk
    have := (H (le_max_left _ _) h).symm.trans (H (le_max_right _ _) hk)
    simp at this; simp [this, get_mem]⟩
#align nat.rfind_opt_mono Nat.rfind_opt_mono

inductive Partrec : (ℕ →. ℕ) → Prop
  | zero : Partrec (pure 0)
  | succ : Partrec succ
  | left : Partrec ↑fun n : ℕ => n.unpair.1
  | right : Partrec ↑fun n : ℕ => n.unpair.2
  | pair {f g} : Partrec f → Partrec g → Partrec fun n => mkpair <$> f n <*> g n
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
  | rfind {f} : Partrec f → Partrec fun a => rfind fun n => (fun m => m = 0) <$> f (mkpair a n)
#align nat.partrec Nat.Partrec

namespace Partrec

theorem ofEq {f g : ℕ →. ℕ} (hf : Partrec f) (H : ∀ n, f n = g n) : Partrec g :=
  (funext H : f = g) ▸ hf
#align nat.partrec.of_eq Nat.Partrec.ofEq

theorem ofEqTot {f : ℕ →. ℕ} {g : ℕ → ℕ} (hf : Partrec f) (H : ∀ n, g n ∈ f n) : Partrec g :=
  hf.of_eq fun n => eq_some_iff.2 (H n)
#align nat.partrec.of_eq_tot Nat.Partrec.ofEqTot

theorem ofPrimrec {f : ℕ → ℕ} (hf : Primrec f) : Partrec f :=
  by
  induction hf
  case zero => exact zero
  case succ => exact succ
  case left => exact left
  case right => exact right
  case pair f g hf hg pf pg =>
    refine' (pf.pair pg).ofEqTot fun n => _
    simp [Seq.seq]
  case comp f g hf hg pf pg =>
    refine' (pf.comp pg).ofEqTot fun n => _
    simp
  case prec f g hf hg pf pg =>
    refine' (pf.prec pg).ofEqTot fun n => _
    simp
    induction' n.unpair.2 with m IH; · simp
    simp; exact ⟨_, IH, rfl⟩
#align nat.partrec.of_primrec Nat.Partrec.ofPrimrec

protected theorem some : Partrec some :=
  ofPrimrec Primrec.id
#align nat.partrec.some Nat.Partrec.some

theorem none : Partrec fun n => none :=
  (ofPrimrec (Nat.Primrec.const 1)).rfind.of_eq fun n =>
    eq_none_iff.2 fun a ⟨h, e⟩ => by simpa using h
#align nat.partrec.none Nat.Partrec.none

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

theorem ppred : Partrec fun n => ppred n :=
  have : Primrec₂ fun n m => if n = Nat.succ m then 0 else 1 :=
    (Primrec.ite
        (@PrimrecRel.comp _ _ _ _ _ _ _ Primrec.eq Primrec.fst (Primrec.succ.comp Primrec.snd))
        (Primrec.const 0) (Primrec.const 1)).to₂
  (ofPrimrec (Primrec₂.unpaired'.2 this)).rfind.of_eq fun n =>
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

end Partrec

end Nat

def Partrec {α σ} [Primcodable α] [Primcodable σ] (f : α →. σ) :=
  Nat.Partrec fun n => Part.bind (decode α n) fun a => (f a).map encode
#align partrec Partrec

def Partrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α → β →. σ) :=
  Partrec fun p : α × β => f p.1 p.2
#align partrec₂ Partrec₂

def Computable {α σ} [Primcodable α] [Primcodable σ] (f : α → σ) :=
  Partrec (f : α →. σ)
#align computable Computable

def Computable₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α → β → σ) :=
  Computable fun p : α × β => f p.1 p.2
#align computable₂ Computable₂

theorem Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {f : α → σ} (hf : Primrec f) :
    Computable f :=
  (Nat.Partrec.ppred.comp (Nat.Partrec.ofPrimrec hf)).of_eq fun n => by
    simp <;> cases decode α n <;> simp
#align primrec.to_comp Primrec.to_comp

theorem Primrec₂.to_comp {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] {f : α → β → σ}
    (hf : Primrec₂ f) : Computable₂ f :=
  hf.to_comp
#align primrec₂.to_comp Primrec₂.to_comp

protected theorem Computable.partrec {α σ} [Primcodable α] [Primcodable σ] {f : α → σ}
    (hf : Computable f) : Partrec (f : α →. σ) :=
  hf
#align computable.partrec Computable.partrec

protected theorem Computable₂.partrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} (hf : Computable₂ f) : Partrec₂ fun a => (f a : β →. σ) :=
  hf
#align computable₂.partrec₂ Computable₂.partrec₂

namespace Computable

variable {α : Type _} {β : Type _} {γ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

theorem of_eq {f g : α → σ} (hf : Computable f) (H : ∀ n, f n = g n) : Computable g :=
  (funext H : f = g) ▸ hf
#align computable.of_eq Computable.of_eq

theorem const (s : σ) : Computable fun a : α => s :=
  (Primrec.const _).to_comp
#align computable.const Computable.const

theorem of_option {f : α → Option β} (hf : Computable f) : Partrec fun a => (f a : Part β) :=
  (Nat.Partrec.ppred.comp hf).of_eq fun n =>
    by
    cases' decode α n with a <;> simp
    cases' f a with b <;> simp
#align computable.of_option Computable.of_option

theorem to₂ {f : α × β → σ} (hf : Computable f) : Computable₂ fun a b => f (a, b) :=
  hf.of_eq fun ⟨a, b⟩ => rfl
#align computable.to₂ Computable.to₂

protected theorem id : Computable (@id α) :=
  Primrec.id.to_comp
#align computable.id Computable.id

theorem fst : Computable (@Prod.fst α β) :=
  Primrec.fst.to_comp
#align computable.fst Computable.fst

theorem snd : Computable (@Prod.snd α β) :=
  Primrec.snd.to_comp
#align computable.snd Computable.snd

theorem pair {f : α → β} {g : α → γ} (hf : Computable f) (hg : Computable g) :
    Computable fun a => (f a, g a) :=
  (hf.pair hg).of_eq fun n => by cases decode α n <;> simp [(· <*> ·)]
#align computable.pair Computable.pair

theorem unpair : Computable Nat.unpair :=
  Primrec.unpair.to_comp
#align computable.unpair Computable.unpair

theorem succ : Computable Nat.succ :=
  Primrec.succ.to_comp
#align computable.succ Computable.succ

theorem pred : Computable Nat.pred :=
  Primrec.pred.to_comp
#align computable.pred Computable.pred

theorem nat_bodd : Computable Nat.bodd :=
  Primrec.nat_bodd.to_comp
#align computable.nat_bodd Computable.nat_bodd

theorem nat_div2 : Computable Nat.div2 :=
  Primrec.nat_div2.to_comp
#align computable.nat_div2 Computable.nat_div2

theorem sum_inl : Computable (@Sum.inl α β) :=
  Primrec.sum_inl.to_comp
#align computable.sum_inl Computable.sum_inl

theorem sum_inr : Computable (@Sum.inr α β) :=
  Primrec.sum_inr.to_comp
#align computable.sum_inr Computable.sum_inr

theorem list_cons : Computable₂ (@List.cons α) :=
  Primrec.list_cons.to_comp
#align computable.list_cons Computable.list_cons

theorem list_reverse : Computable (@List.reverse α) :=
  Primrec.list_reverse.to_comp
#align computable.list_reverse Computable.list_reverse

theorem list_nth : Computable₂ (@List.nth α) :=
  Primrec.list_nth.to_comp
#align computable.list_nth Computable.list_nth

theorem list_append : Computable₂ ((· ++ ·) : List α → List α → List α) :=
  Primrec.list_append.to_comp
#align computable.list_append Computable.list_append

theorem list_concat : Computable₂ fun l (a : α) => l ++ [a] :=
  Primrec.list_concat.to_comp
#align computable.list_concat Computable.list_concat

theorem list_length : Computable (@List.length α) :=
  Primrec.list_length.to_comp
#align computable.list_length Computable.list_length

theorem vector_cons {n} : Computable₂ (@Vector.cons α n) :=
  Primrec.vector_cons.to_comp
#align computable.vector_cons Computable.vector_cons

theorem vector_to_list {n} : Computable (@Vector.toList α n) :=
  Primrec.vector_to_list.to_comp
#align computable.vector_to_list Computable.vector_to_list

theorem vector_length {n} : Computable (@Vector.length α n) :=
  Primrec.vector_length.to_comp
#align computable.vector_length Computable.vector_length

theorem vector_head {n} : Computable (@Vector.head α n) :=
  Primrec.vector_head.to_comp
#align computable.vector_head Computable.vector_head

theorem vector_tail {n} : Computable (@Vector.tail α n) :=
  Primrec.vector_tail.to_comp
#align computable.vector_tail Computable.vector_tail

theorem vector_nth {n} : Computable₂ (@Vector.nth α n) :=
  Primrec.vector_nth.to_comp
#align computable.vector_nth Computable.vector_nth

theorem vector_nth' {n} : Computable (@Vector.nth α n) :=
  Primrec.vector_nth'.to_comp
#align computable.vector_nth' Computable.vector_nth'

theorem vector_of_fn' {n} : Computable (@Vector.ofFn α n) :=
  Primrec.vector_of_fn'.to_comp
#align computable.vector_of_fn' Computable.vector_of_fn'

theorem fin_app {n} : Computable₂ (@id (Fin n → σ)) :=
  Primrec.fin_app.to_comp
#align computable.fin_app Computable.fin_app

protected theorem encode : Computable (@encode α _) :=
  Primrec.encode.to_comp
#align computable.encode Computable.encode

protected theorem decode : Computable (decode α) :=
  Primrec.decode.to_comp
#align computable.decode Computable.decode

protected theorem of_nat (α) [Denumerable α] : Computable (ofNat α) :=
  (Primrec.of_nat _).to_comp
#align computable.of_nat Computable.of_nat

theorem encode_iff {f : α → σ} : (Computable fun a => encode (f a)) ↔ Computable f :=
  Iff.rfl
#align computable.encode_iff Computable.encode_iff

theorem option_some : Computable (@Option.some α) :=
  Primrec.option_some.to_comp
#align computable.option_some Computable.option_some

end Computable

namespace Partrec

variable {α : Type _} {β : Type _} {γ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

open Computable

theorem of_eq {f g : α →. σ} (hf : Partrec f) (H : ∀ n, f n = g n) : Partrec g :=
  (funext H : f = g) ▸ hf
#align partrec.of_eq Partrec.of_eq

theorem of_eq_tot {f : α →. σ} {g : α → σ} (hf : Partrec f) (H : ∀ n, g n ∈ f n) : Computable g :=
  hf.of_eq fun a => eq_some_iff.2 (H a)
#align partrec.of_eq_tot Partrec.of_eq_tot

theorem none : Partrec fun a : α => @Part.none σ :=
  Nat.Partrec.none.of_eq fun n => by cases decode α n <;> simp
#align partrec.none Partrec.none

protected theorem some : Partrec (@Part.some α) :=
  Computable.id
#align partrec.some Partrec.some

theorem Decidable.Partrec.const' (s : Part σ) [Decidable s.Dom] : Partrec fun a : α => s :=
  (of_option (const (toOption s))).of_eq fun a => of_toOption s
#align decidable.partrec.const' Decidable.Partrec.const'

theorem const' (s : Part σ) : Partrec fun a : α => s :=
  haveI := Classical.dec s.dom
  Decidable.Partrec.const' s
#align partrec.const' Partrec.const'

protected theorem bind {f : α →. β} {g : α → β →. σ} (hf : Partrec f) (hg : Partrec₂ g) :
    Partrec fun a => (f a).bind (g a) :=
  (hg.comp (Nat.Partrec.some.pair hf)).of_eq fun n => by
    simp [(· <*> ·)] <;> cases' e : decode α n with a <;> simp [e, encodek]
#align partrec.bind Partrec.bind

theorem map {f : α →. β} {g : α → β → σ} (hf : Partrec f) (hg : Computable₂ g) :
    Partrec fun a => (f a).map (g a) := by
  simpa [bind_some_eq_map] using @Partrec.bind _ _ _ (fun a b => Part.some (g a b)) hf hg
#align partrec.map Partrec.map

theorem to₂ {f : α × β →. σ} (hf : Partrec f) : Partrec₂ fun a b => f (a, b) :=
  hf.of_eq fun ⟨a, b⟩ => rfl
#align partrec.to₂ Partrec.to₂

theorem nat_elim {f : α → ℕ} {g : α →. σ} {h : α → ℕ × σ →. σ} (hf : Computable f) (hg : Partrec g)
    (hh : Partrec₂ h) : Partrec fun a => (f a).elim (g a) fun y IH => IH.bind fun i => h a (y, i) :=
  (Nat.Partrec.prec' hf hg hh).of_eq fun n =>
    by
    cases' e : decode α n with a <;> simp [e]
    induction' f a with m IH <;> simp
    rw [IH, bind_map]
    congr ; funext s
    simp [encodek]
#align partrec.nat_elim Partrec.nat_elim

theorem comp {f : β →. σ} {g : α → β} (hf : Partrec f) (hg : Computable g) :
    Partrec fun a => f (g a) :=
  (hf.comp hg).of_eq fun n => by simp <;> cases' e : decode α n with a <;> simp [e, encodek]
#align partrec.comp Partrec.comp

theorem nat_iff {f : ℕ →. ℕ} : Partrec f ↔ Nat.Partrec f := by simp [Partrec, map_id']
#align partrec.nat_iff Partrec.nat_iff

theorem map_encode_iff {f : α →. σ} : (Partrec fun a => (f a).map encode) ↔ Partrec f :=
  Iff.rfl
#align partrec.map_encode_iff Partrec.map_encode_iff

end Partrec

namespace Partrec₂

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

theorem unpaired {f : ℕ → ℕ →. α} : Partrec (Nat.unpaired f) ↔ Partrec₂ f :=
  ⟨fun h => by simpa using h.comp primrec₂.mkpair.to_comp, fun h => h.comp Primrec.unpair.to_comp⟩
#align partrec₂.unpaired Partrec₂.unpaired

theorem unpaired' {f : ℕ → ℕ →. ℕ} : Nat.Partrec (Nat.unpaired f) ↔ Partrec₂ f :=
  Partrec.nat_iff.symm.trans unpaired
#align partrec₂.unpaired' Partrec₂.unpaired'

theorem comp {f : β → γ →. σ} {g : α → β} {h : α → γ} (hf : Partrec₂ f) (hg : Computable g)
    (hh : Computable h) : Partrec fun a => f (g a) (h a) :=
  hf.comp (hg.pair hh)
#align partrec₂.comp Partrec₂.comp

theorem comp₂ {f : γ → δ →. σ} {g : α → β → γ} {h : α → β → δ} (hf : Partrec₂ f)
    (hg : Computable₂ g) (hh : Computable₂ h) : Partrec₂ fun a b => f (g a b) (h a b) :=
  hf.comp hg hh
#align partrec₂.comp₂ Partrec₂.comp₂

end Partrec₂

namespace Computable

variable {α : Type _} {β : Type _} {γ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

theorem comp {f : β → σ} {g : α → β} (hf : Computable f) (hg : Computable g) :
    Computable fun a => f (g a) :=
  hf.comp hg
#align computable.comp Computable.comp

theorem comp₂ {f : γ → σ} {g : α → β → γ} (hf : Computable f) (hg : Computable₂ g) :
    Computable₂ fun a b => f (g a b) :=
  hf.comp hg
#align computable.comp₂ Computable.comp₂

end Computable

namespace Computable₂

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

theorem comp {f : β → γ → σ} {g : α → β} {h : α → γ} (hf : Computable₂ f) (hg : Computable g)
    (hh : Computable h) : Computable fun a => f (g a) (h a) :=
  hf.comp (hg.pair hh)
#align computable₂.comp Computable₂.comp

theorem comp₂ {f : γ → δ → σ} {g : α → β → γ} {h : α → β → δ} (hf : Computable₂ f)
    (hg : Computable₂ g) (hh : Computable₂ h) : Computable₂ fun a b => f (g a b) (h a b) :=
  hf.comp hg hh
#align computable₂.comp₂ Computable₂.comp₂

end Computable₂

namespace Partrec

variable {α : Type _} {β : Type _} {γ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

open Computable

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

theorem rfind_opt {f : α → ℕ → Option σ} (hf : Computable₂ f) :
    Partrec fun a => Nat.rfindOpt (f a) :=
  (rfind (Primrec.option_is_some.to_comp.comp hf).Partrec.to₂).bind (of_option hf)
#align partrec.rfind_opt Partrec.rfind_opt

theorem nat_cases_right {f : α → ℕ} {g : α → σ} {h : α → ℕ →. σ} (hf : Computable f)
    (hg : Computable g) (hh : Partrec₂ h) : Partrec fun a => (f a).cases (some (g a)) (h a) :=
  (nat_elim hf hg (hh.comp fst (pred.comp <| hf.comp fst)).to₂).of_eq fun a =>
    by
    simp; cases f a <;> simp
    refine' ext fun b => ⟨fun H => _, fun H => _⟩
    · rcases mem_bind_iff.1 H with ⟨c, h₁, h₂⟩
      exact h₂
    · have : ∀ m, (Nat.elim (Part.some (g a)) (fun y IH => IH.bind fun _ => h a n) m).Dom :=
        by
        intro
        induction m <;> simp [*, H.fst]
      exact ⟨⟨this n, H.fst⟩, H.snd⟩
#align partrec.nat_cases_right Partrec.nat_cases_right

theorem bind_decode₂_iff {f : α →. σ} :
    Partrec f ↔ Nat.Partrec fun n => Part.bind (decode₂ α n) fun a => (f a).map encode :=
  ⟨fun hf =>
    nat_iff.1 <|
      (of_option Primrec.decode₂.to_comp).bind <|
        (map hf (Computable.encode.comp snd).to₂).comp snd,
    fun h =>
    map_encode_iff.1 <| by simpa [encodek₂] using (nat_iff.2 h).comp (@Computable.encode α _)⟩
#align partrec.bind_decode₂_iff Partrec.bind_decode₂_iff

theorem vector_m_of_fn :
    ∀ {n} {f : Fin n → α →. σ},
      (∀ i, Partrec (f i)) → Partrec fun a : α => Vector.mOfFn fun i => f i a
  | 0, f, hf => const _
  | n + 1, f, hf => by
    simp [Vector.mOfFn] <;>
      exact
        (hf 0).bind
          (Partrec.bind ((vector_m_of_fn fun i => hf i.succ).comp fst)
            (primrec.vector_cons.to_comp.comp (snd.comp fst) snd))
#align partrec.vector_m_of_fn Partrec.vector_m_of_fn

end Partrec

@[simp]
theorem Vector.m_of_fn_part_some {α n} :
    ∀ f : Fin n → α, (Vector.mOfFn fun i => Part.some (f i)) = Part.some (Vector.ofFn f) :=
  Vector.m_of_fn_pure
#align vector.m_of_fn_part_some Vector.m_of_fn_part_some

namespace Computable

variable {α : Type _} {β : Type _} {γ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

theorem option_some_iff {f : α → σ} : (Computable fun a => some (f a)) ↔ Computable f :=
  ⟨fun h => encode_iff.1 <| Primrec.pred.to_comp.comp <| encode_iff.2 h, option_some.comp⟩
#align computable.option_some_iff Computable.option_some_iff

theorem bind_decode_iff {f : α → β → Option σ} :
    (Computable₂ fun a n => (decode β n).bind (f a)) ↔ Computable₂ f :=
  ⟨fun hf =>
    (Nat.Partrec.ofEq
        (((Partrec.nat_iff.2
                  (Nat.Partrec.ppred.comp <| Nat.Partrec.ofPrimrec <| Primcodable.prim β)).comp
              snd).bind
          (Computable.comp hf fst).to₂.Partrec₂))
      fun n => by
      simp <;> cases decode α n.unpair.1 <;> simp <;> cases decode β n.unpair.2 <;> simp,
    fun hf =>
    by
    have :
      Partrec fun a : α × ℕ =>
        (encode (decode β a.2)).cases (some Option.none) fun n => Part.map (f a.1) (decode β n) :=
      Partrec.nat_cases_right (primrec.encdec.to_comp.comp snd) (const none)
        ((of_option (computable.decode.comp snd)).map (hf.comp (fst.comp <| fst.comp fst) snd).to₂)
    refine' this.of_eq fun a => _
    simp; cases decode β a.2 <;> simp [encodek]⟩
#align computable.bind_decode_iff Computable.bind_decode_iff

theorem map_decode_iff {f : α → β → σ} :
    (Computable₂ fun a n => (decode β n).map (f a)) ↔ Computable₂ f :=
  bind_decode_iff.trans option_some_iff
#align computable.map_decode_iff Computable.map_decode_iff

theorem nat_elim {f : α → ℕ} {g : α → σ} {h : α → ℕ × σ → σ} (hf : Computable f) (hg : Computable g)
    (hh : Computable₂ h) : Computable fun a => (f a).elim (g a) fun y IH => h a (y, IH) :=
  (Partrec.nat_elim hf hg hh.Partrec₂).of_eq fun a => by simp <;> induction f a <;> simp [*]
#align computable.nat_elim Computable.nat_elim

theorem nat_cases {f : α → ℕ} {g : α → σ} {h : α → ℕ → σ} (hf : Computable f) (hg : Computable g)
    (hh : Computable₂ h) : Computable fun a => (f a).cases (g a) (h a) :=
  nat_elim hf hg (hh.comp fst <| fst.comp snd).to₂
#align computable.nat_cases Computable.nat_cases

theorem cond {c : α → Bool} {f : α → σ} {g : α → σ} (hc : Computable c) (hf : Computable f)
    (hg : Computable g) : Computable fun a => cond (c a) (f a) (g a) :=
  (nat_cases (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq fun a => by cases c a <;> rfl
#align computable.cond Computable.cond

theorem option_cases {o : α → Option β} {f : α → σ} {g : α → β → σ} (ho : Computable o)
    (hf : Computable f) (hg : Computable₂ g) :
    @Computable _ σ _ _ fun a => Option.casesOn (o a) (f a) (g a) :=
  option_some_iff.1 <|
    (nat_cases (encode_iff.2 ho) (option_some_iff.2 hf) (map_decode_iff.2 hg)).of_eq fun a => by
      cases o a <;> simp [encodek] <;> rfl
#align computable.option_cases Computable.option_cases

theorem option_bind {f : α → Option β} {g : α → β → Option σ} (hf : Computable f)
    (hg : Computable₂ g) : Computable fun a => (f a).bind (g a) :=
  (option_cases hf (const Option.none) hg).of_eq fun a => by cases f a <;> rfl
#align computable.option_bind Computable.option_bind

theorem option_map {f : α → Option β} {g : α → β → σ} (hf : Computable f) (hg : Computable₂ g) :
    Computable fun a => (f a).map (g a) :=
  option_bind hf (option_some.comp₂ hg)
#align computable.option_map Computable.option_map

theorem option_get_or_else {f : α → Option β} {g : α → β} (hf : Computable f) (hg : Computable g) :
    Computable fun a => (f a).getOrElse (g a) :=
  (Computable.option_cases hf hg (show Computable₂ fun a b => b from Computable.snd)).of_eq fun a =>
    by cases f a <;> rfl
#align computable.option_get_or_else Computable.option_get_or_else

theorem subtype_mk {f : α → β} {p : β → Prop} [DecidablePred p] {h : ∀ a, p (f a)}
    (hp : PrimrecPred p) (hf : Computable f) :
    @Computable _ _ _ (Primcodable.subtype hp) fun a => (⟨f a, h a⟩ : Subtype p) :=
  hf
#align computable.subtype_mk Computable.subtype_mk

theorem sum_cases {f : α → Sum β γ} {g : α → β → σ} {h : α → γ → σ} (hf : Computable f)
    (hg : Computable₂ g) (hh : Computable₂ h) :
    @Computable _ σ _ _ fun a => Sum.casesOn (f a) (g a) (h a) :=
  option_some_iff.1 <|
    (cond (nat_bodd.comp <| encode_iff.2 hf)
          (option_map (Computable.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hh)
          (option_map (Computable.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hg)).of_eq
      fun a => by cases' f a with b c <;> simp [Nat.div2_bit, Nat.bodd_bit, encodek] <;> rfl
#align computable.sum_cases Computable.sum_cases

theorem nat_strong_rec (f : α → ℕ → σ) {g : α → List σ → Option σ} (hg : Computable₂ g)
    (H : ∀ a n, g a ((List.range n).map (f a)) = some (f a n)) : Computable₂ f :=
  suffices Computable₂ fun a n => (List.range n).map (f a) from
    option_some_iff.1 <|
      (list_nth.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq fun a => by
        simp [List.nth_range (Nat.lt_succ_self a.2)] <;> rfl
  option_some_iff.1 <|
    (nat_elim snd (const (Option.some []))
          (to₂ <|
            option_bind (snd.comp snd) <|
              to₂ <|
                option_map (hg.comp (fst.comp <| fst.comp fst) snd)
                  (to₂ <| list_concat.comp (snd.comp fst) snd))).of_eq
      fun a => by
      simp; induction' a.2 with n IH; · rfl
      simp [IH, H, List.range_succ]
#align computable.nat_strong_rec Computable.nat_strong_rec

theorem list_of_fn :
    ∀ {n} {f : Fin n → α → σ},
      (∀ i, Computable (f i)) → Computable fun a => List.ofFn fun i => f i a
  | 0, f, hf => const []
  | n + 1, f, hf => by
    simp [List.of_fn_succ] <;> exact list_cons.comp (hf 0) (list_of_fn fun i => hf i.succ)
#align computable.list_of_fn Computable.list_of_fn

theorem vector_of_fn {n} {f : Fin n → α → σ} (hf : ∀ i, Computable (f i)) :
    Computable fun a => Vector.ofFn fun i => f i a :=
  (Partrec.vector_m_of_fn hf).of_eq fun a => by simp
#align computable.vector_of_fn Computable.vector_of_fn

end Computable

namespace Partrec

variable {α : Type _} {β : Type _} {γ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

open Computable

theorem option_some_iff {f : α →. σ} : (Partrec fun a => (f a).map Option.some) ↔ Partrec f :=
  ⟨fun h => (Nat.Partrec.ppred.comp h).of_eq fun n => by simp [Part.bind_assoc, bind_some_eq_map],
    fun hf => hf.map (option_some.comp snd).to₂⟩
#align partrec.option_some_iff Partrec.option_some_iff

theorem option_cases_right {o : α → Option β} {f : α → σ} {g : α → β →. σ} (ho : Computable o)
    (hf : Computable f) (hg : Partrec₂ g) :
    @Partrec _ σ _ _ fun a => Option.casesOn (o a) (some (f a)) (g a) :=
  have :
    Partrec fun a : α =>
      Nat.cases (Part.some (f a)) (fun n => Part.bind (decode β n) (g a)) (encode (o a)) :=
    nat_cases_right (encode_iff.2 ho) hf.Partrec <|
      ((@Computable.decode β _).comp snd).ofOption.bind (hg.comp (fst.comp fst) snd).to₂
  this.of_eq fun a => by cases' o a with b <;> simp [encodek]
#align partrec.option_cases_right Partrec.option_cases_right

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

theorem sum_cases_left {f : α → Sum β γ} {g : α → β →. σ} {h : α → γ → σ} (hf : Computable f)
    (hg : Partrec₂ g) (hh : Computable₂ h) :
    @Partrec _ σ _ _ fun a => Sum.casesOn (f a) (g a) fun c => some (h a c) :=
  (sum_cases_right (sum_cases hf (sum_inr.comp snd).to₂ (sum_inl.comp snd).to₂) hh hg).of_eq
    fun a => by cases f a <;> simp
#align partrec.sum_cases_left Partrec.sum_cases_left

theorem fix_aux {α σ} (f : α →. Sum σ α) (a : α) (b : σ) :
    let F : α → ℕ →. Sum σ α := fun a n =>
      (n.elim (some (Sum.inr a))) fun y IH =>
        IH.bind fun s => Sum.casesOn s (fun _ => Part.some s) f
    (∃ n : ℕ,
        ((∃ b' : σ, Sum.inl b' ∈ F a n) ∧ ∀ {m : ℕ}, m < n → ∃ b : α, Sum.inr b ∈ F a m) ∧
          Sum.inl b ∈ F a n) ↔
      b ∈ Pfun.fix f a :=
  by
  intro ; refine' ⟨fun h => _, fun h => _⟩
  · rcases h with ⟨n, ⟨_x, h₁⟩, h₂⟩
    have : ∀ (m a') (_ : Sum.inr a' ∈ F a m) (_ : b ∈ Pfun.fix f a'), b ∈ Pfun.fix f a :=
      by
      intro m a' am ba
      induction' m with m IH generalizing a' <;> simp [F] at am
      · rwa [← am]
      rcases am with ⟨a₂, am₂, fa₂⟩
      exact IH _ am₂ (Pfun.mem_fix_iff.2 (Or.inr ⟨_, fa₂, ba⟩))
    cases n <;> simp [F] at h₂
    · cases h₂
    rcases h₂ with (h₂ | ⟨a', am', fa'⟩)
    · cases' h₁ (Nat.lt_succ_self _) with a' h
      injection mem_unique h h₂
    · exact this _ _ am' (Pfun.mem_fix_iff.2 (Or.inl fa'))
  · suffices
      ∀ (a') (_ : b ∈ Pfun.fix f a') (k) (_ : Sum.inr a' ∈ F a k),
        ∃ n, Sum.inl b ∈ F a n ∧ ∀ m < n, ∀ (_ : k ≤ m), ∃ a₂, Sum.inr a₂ ∈ F a m
      by
      rcases this _ h 0 (by simp [F]) with ⟨n, hn₁, hn₂⟩
      exact ⟨_, ⟨⟨_, hn₁⟩, fun m mn => hn₂ m mn (Nat.zero_le _)⟩, hn₁⟩
    intro a₁ h₁
    apply Pfun.fixInduction h₁
    intro a₂ h₂ IH k hk
    rcases Pfun.mem_fix_iff.1 h₂ with (h₂ | ⟨a₃, am₃, fa₃⟩)
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

theorem fix {f : α →. Sum σ α} (hf : Partrec f) : Partrec (Pfun.fix f) :=
  let F : α → ℕ →. Sum σ α := fun a n =>
    (n.elim (some (Sum.inr a))) fun y IH => IH.bind fun s => Sum.casesOn s (fun _ => Part.some s) f
  have hF : Partrec₂ F :=
    Partrec.nat_elim snd (sum_inr.comp fst).Partrec
      (sum_cases_right (snd.comp snd) (snd.comp <| snd.comp fst).to₂ (hf.comp snd).to₂).to₂
  let p a n := @Part.map _ Bool (fun s => Sum.casesOn s (fun _ => true) fun _ => false) (F a n)
  have hp : Partrec₂ p :=
    hF.map ((sum_cases Computable.id (const true).to₂ (const false).to₂).comp snd).to₂
  (hp.rfind.bind (hF.bind (sum_cases_right snd snd.to₂ none.to₂).to₂).to₂).of_eq fun a =>
    ext fun b => by simp <;> apply fix_aux f
#align partrec.fix Partrec.fix

end Partrec

