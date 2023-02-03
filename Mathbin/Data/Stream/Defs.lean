/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module data.stream.defs
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

/-!
# Definition of `stream` and functions on streams

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A stream `stream α` is an infinite sequence of elements of `α`. One can also think about it as an
infinite list. In this file we define `stream` and some functions that take and/or return streams.
-/


universe u v w

#print Stream' /-
/-- A stream `stream α` is an infinite sequence of elements of `α`. -/
def Stream' (α : Type u) :=
  Nat → α
#align stream Stream'
-/

open Nat

namespace Stream'

variable {α : Type u} {β : Type v} {δ : Type w}

#print Stream'.cons /-
/-- Prepend an element to a stream. -/
def cons (a : α) (s : Stream' α) : Stream' α
  | 0 => a
  | n + 1 => s n
#align stream.cons Stream'.cons
-/

-- mathport name: stream.cons
notation h "::" t => cons h t

#print Stream'.head /-
/-- Head of a stream: `stream.head s = stream.nth 0 s`. -/
def head (s : Stream' α) : α :=
  s 0
#align stream.head Stream'.head
-/

#print Stream'.tail /-
/-- Tail of a stream: `stream.tail (h :: t) = t`. -/
def tail (s : Stream' α) : Stream' α := fun i => s (i + 1)
#align stream.tail Stream'.tail
-/

#print Stream'.drop /-
/-- Drop first `n` elements of a stream. -/
def drop (n : Nat) (s : Stream' α) : Stream' α := fun i => s (i + n)
#align stream.drop Stream'.drop
-/

#print Stream'.nth /-
/-- `n`-th element of a stream. -/
def nth (s : Stream' α) (n : ℕ) : α :=
  s n
#align stream.nth Stream'.nth
-/

#print Stream'.All /-
/-- Proposition saying that all elements of a stream satisfy a predicate. -/
def All (p : α → Prop) (s : Stream' α) :=
  ∀ n, p (nth s n)
#align stream.all Stream'.All
-/

#print Stream'.Any /-
/-- Proposition saying that at least one element of a stream satisfies a predicate. -/
def Any (p : α → Prop) (s : Stream' α) :=
  ∃ n, p (nth s n)
#align stream.any Stream'.Any
-/

/-- `a ∈ s` means that `a = stream.nth n s` for some `n`. -/
instance : Membership α (Stream' α) :=
  ⟨fun a s => Any (fun b => a = b) s⟩

#print Stream'.map /-
/-- Apply a function `f` to all elements of a stream `s`. -/
def map (f : α → β) (s : Stream' α) : Stream' β := fun n => f (nth s n)
#align stream.map Stream'.map
-/

#print Stream'.zip /-
/-- Zip two streams using a binary operation:
`stream.nth n (stream.zip f s₁ s₂) = f (stream.nth s₁) (stream.nth s₂)`. -/
def zip (f : α → β → δ) (s₁ : Stream' α) (s₂ : Stream' β) : Stream' δ := fun n =>
  f (nth s₁ n) (nth s₂ n)
#align stream.zip Stream'.zip
-/

#print Stream'.enum /-
/-- Enumerate a stream by tagging each element with its index. -/
def enum (s : Stream' α) : Stream' (ℕ × α) := fun n => (n, s.get? n)
#align stream.enum Stream'.enum
-/

#print Stream'.const /-
/-- The constant stream: `stream.nth n (stream.const a) = a`. -/
def const (a : α) : Stream' α := fun n => a
#align stream.const Stream'.const
-/

#print Stream'.iterate /-
/-- Iterates of a function as a stream. -/
def iterate (f : α → α) (a : α) : Stream' α := fun n => Nat.recOn n a fun n r => f r
#align stream.iterate Stream'.iterate
-/

#print Stream'.corec /-
def corec (f : α → β) (g : α → α) : α → Stream' β := fun a => map f (iterate g a)
#align stream.corec Stream'.corec
-/

#print Stream'.corecOn /-
def corecOn (a : α) (f : α → β) (g : α → α) : Stream' β :=
  corec f g a
#align stream.corec_on Stream'.corecOn
-/

#print Stream'.corec' /-
def corec' (f : α → β × α) : α → Stream' β :=
  corec (Prod.fst ∘ f) (Prod.snd ∘ f)
#align stream.corec' Stream'.corec'
-/

#print Stream'.corecState /-
/-- Use a state monad to generate a stream through corecursion -/
def corecState {σ α} (cmd : StateM σ α) (s : σ) : Stream' α :=
  corec Prod.fst (cmd.run ∘ Prod.snd) (cmd.run s)
#align stream.corec_state Stream'.corecState
-/

#print Stream'.unfolds /-
-- corec is also known as unfold
def unfolds (g : α → β) (f : α → α) (a : α) : Stream' β :=
  corec g f a
#align stream.unfolds Stream'.unfolds
-/

#print Stream'.interleave /-
/-- Interleave two streams. -/
def interleave (s₁ s₂ : Stream' α) : Stream' α :=
  corecOn (s₁, s₂) (fun ⟨s₁, s₂⟩ => head s₁) fun ⟨s₁, s₂⟩ => (s₂, tail s₁)
#align stream.interleave Stream'.interleave
-/

-- mathport name: «expr ⋈ »
infixl:65 " ⋈ " => interleave

#print Stream'.even /-
/-- Elements of a stream with even indices. -/
def even (s : Stream' α) : Stream' α :=
  corec (fun s => head s) (fun s => tail (tail s)) s
#align stream.even Stream'.even
-/

#print Stream'.odd /-
/-- Elements of a stream with odd indices. -/
def odd (s : Stream' α) : Stream' α :=
  even (tail s)
#align stream.odd Stream'.odd
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Stream'.appendStream' /-
/-- Append a stream to a list. -/
def appendStream' : List α → Stream' α → Stream' α
  | [], s => s
  | List.cons a l, s => a::append_stream l s
#align stream.append_stream Stream'.appendStream'
-/

-- mathport name: «expr ++ₛ »
infixl:65 " ++ₛ " => appendStream'

#print Stream'.take /-
/-- `take n s` returns a list of the `n` first elements of stream `s` -/
def take : ℕ → Stream' α → List α
  | 0, s => []
  | n + 1, s => List.cons (head s) (take n (tail s))
#align stream.take Stream'.take
-/

#print Stream'.cycleF /-
/-- An auxiliary definition for `stream.cycle` corecursive def -/
protected def cycleF : α × List α × α × List α → α
  | (v, _, _, _) => v
#align stream.cycle_f Stream'.cycleF
-/

#print Stream'.cycleG /-
/-- An auxiliary definition for `stream.cycle` corecursive def -/
protected def cycleG : α × List α × α × List α → α × List α × α × List α
  | (v₁, [], v₀, l₀) => (v₀, l₀, v₀, l₀)
  | (v₁, List.cons v₂ l₂, v₀, l₀) => (v₂, l₂, v₀, l₀)
#align stream.cycle_g Stream'.cycleG
-/

#print Stream'.cycle /-
/-- Interpret a nonempty list as a cyclic stream. -/
def cycle : ∀ l : List α, l ≠ [] → Stream' α
  | [], h => absurd rfl h
  | List.cons a l, h => corec Stream'.cycleF Stream'.cycleG (a, l, a, l)
#align stream.cycle Stream'.cycle
-/

#print Stream'.tails /-
/-- Tails of a stream, starting with `stream.tail s`. -/
def tails (s : Stream' α) : Stream' (Stream' α) :=
  corec id tail (tail s)
#align stream.tails Stream'.tails
-/

#print Stream'.initsCore /-
/-- An auxiliary definition for `stream.inits`. -/
def initsCore (l : List α) (s : Stream' α) : Stream' (List α) :=
  corecOn (l, s) (fun ⟨a, b⟩ => a) fun p =>
    match p with
    | (l', s') => (l' ++ [head s'], tail s')
#align stream.inits_core Stream'.initsCore
-/

#print Stream'.inits /-
/-- Nonempty initial segments of a stream. -/
def inits (s : Stream' α) : Stream' (List α) :=
  initsCore [head s] (tail s)
#align stream.inits Stream'.inits
-/

#print Stream'.pure /-
/-- A constant stream, same as `stream.const`. -/
def pure (a : α) : Stream' α :=
  const a
#align stream.pure Stream'.pure
-/

#print Stream'.apply /-
/-- Given a stream of functions and a stream of values, apply `n`-th function to `n`-th value. -/
def apply (f : Stream' (α → β)) (s : Stream' α) : Stream' β := fun n => (nth f n) (nth s n)
#align stream.apply Stream'.apply
-/

-- mathport name: «expr ⊛ »
infixl:75 " ⊛ " => apply

#print Stream'.nats /-
-- input as \o*
/-- The stream of natural numbers: `stream.nth n stream.nats = n`. -/
def nats : Stream' Nat := fun n => n
#align stream.nats Stream'.nats
-/

end Stream'

