/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

/-!
# Definition of `stream` and functions on streams

A stream `stream α` is an infinite sequence of elements of `α`. One can also think about it as an
infinite list. In this file we define `stream` and some functions that take and/or return streams.
-/


universe u v w

/- warning: stream -> Stream is a dubious translation:
lean 3 declaration is
  Type.{u} -> Sort.{max 1 (succ u)}
but is expected to have type
  Type.{u} -> (outParam.{succ (succ v)} Type.{v}) -> Type.{max u v}
Case conversion may be inaccurate. Consider using '#align stream Streamₓ'. -/
/-- A stream `stream α` is an infinite sequence of elements of `α`. -/
def Stream (α : Type u) :=
  Nat → α

open Nat

namespace Stream

variable {α : Type u} {β : Type v} {δ : Type w}

/-- Prepend an element to a stream. -/
def cons (a : α) (s : Stream α) : Stream α
  | 0 => a
  | n + 1 => s n

-- mathport name: stream.cons
notation h "::" t => cons h t

/-- Head of a stream: `stream.head s = stream.nth 0 s`. -/
def head (s : Stream α) : α :=
  s 0

/-- Tail of a stream: `stream.tail (h :: t) = t`. -/
def tail (s : Stream α) : Stream α := fun i => s (i + 1)

/-- Drop first `n` elements of a stream. -/
def drop (n : Nat) (s : Stream α) : Stream α := fun i => s (i + n)

/-- `n`-th element of a stream. -/
def nth (s : Stream α) (n : ℕ) : α :=
  s n

/-- Proposition saying that all elements of a stream satisfy a predicate. -/
def All (p : α → Prop) (s : Stream α) :=
  ∀ n, p (nth s n)

/-- Proposition saying that at least one element of a stream satisfies a predicate. -/
def Any (p : α → Prop) (s : Stream α) :=
  ∃ n, p (nth s n)

/-- `a ∈ s` means that `a = stream.nth n s` for some `n`. -/
instance : Membership α (Stream α) :=
  ⟨fun a s => Any (fun b => a = b) s⟩

/-- Apply a function `f` to all elements of a stream `s`. -/
def map (f : α → β) (s : Stream α) : Stream β := fun n => f (nth s n)

/-- Zip two streams using a binary operation:
`stream.nth n (stream.zip f s₁ s₂) = f (stream.nth s₁) (stream.nth s₂)`. -/
def zip (f : α → β → δ) (s₁ : Stream α) (s₂ : Stream β) : Stream δ := fun n => f (nth s₁ n) (nth s₂ n)

/-- The constant stream: `stream.nth n (stream.const a) = a`. -/
def const (a : α) : Stream α := fun n => a

/-- Iterates of a function as a stream. -/
def iterate (f : α → α) (a : α) : Stream α := fun n => Nat.recOn n a fun n r => f r

def corec (f : α → β) (g : α → α) : α → Stream β := fun a => map f (iterate g a)

def corecOn (a : α) (f : α → β) (g : α → α) : Stream β :=
  corec f g a

def corec' (f : α → β × α) : α → Stream β :=
  corec (Prod.fst ∘ f) (Prod.snd ∘ f)

/-- Use a state monad to generate a stream through corecursion -/
def corecState {σ α} (cmd : State σ α) (s : σ) : Stream α :=
  corec Prod.fst (cmd.run ∘ Prod.snd) (cmd.run s)

-- corec is also known as unfold
def unfolds (g : α → β) (f : α → α) (a : α) : Stream β :=
  corec g f a

/-- Interleave two streams. -/
def interleave (s₁ s₂ : Stream α) : Stream α :=
  corecOn (s₁, s₂) (fun ⟨s₁, s₂⟩ => head s₁) fun ⟨s₁, s₂⟩ => (s₂, tail s₁)

-- mathport name: «expr ⋈ »
infixl:65 " ⋈ " => interleave

/-- Elements of a stream with even indices. -/
def even (s : Stream α) : Stream α :=
  corec (fun s => head s) (fun s => tail (tail s)) s

/-- Elements of a stream with odd indices. -/
def odd (s : Stream α) : Stream α :=
  even (tail s)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Append a stream to a list. -/
def appendStream : List α → Stream α → Stream α
  | [], s => s
  | List.cons a l, s => a::append_stream l s

-- mathport name: «expr ++ₛ »
infixl:65 " ++ₛ " => appendStream

/-- `take n s` returns a list of the `n` first elements of stream `s` -/
def take : ℕ → Stream α → List α
  | 0, s => []
  | n + 1, s => List.cons (head s) (take n (tail s))

/-- An auxiliary definition for `stream.cycle` corecursive def -/
protected def cycleF : α × List α × α × List α → α
  | (v, _, _, _) => v

/-- An auxiliary definition for `stream.cycle` corecursive def -/
protected def cycleG : α × List α × α × List α → α × List α × α × List α
  | (v₁, [], v₀, l₀) => (v₀, l₀, v₀, l₀)
  | (v₁, List.cons v₂ l₂, v₀, l₀) => (v₂, l₂, v₀, l₀)

/-- Interpret a nonempty list as a cyclic stream. -/
def cycle : ∀ l : List α, l ≠ [] → Stream α
  | [], h => absurd rfl h
  | List.cons a l, h => corec Stream.cycleF Stream.cycleG (a, l, a, l)

/-- Tails of a stream, starting with `stream.tail s`. -/
def tails (s : Stream α) : Stream (Stream α) :=
  corec id tail (tail s)

/-- An auxiliary definition for `stream.inits`. -/
def initsCore (l : List α) (s : Stream α) : Stream (List α) :=
  corecOn (l, s) (fun ⟨a, b⟩ => a) fun p =>
    match p with
    | (l', s') => (l' ++ [head s'], tail s')

/-- Nonempty initial segments of a stream. -/
def inits (s : Stream α) : Stream (List α) :=
  initsCore [head s] (tail s)

/-- A constant stream, same as `stream.const`. -/
def pure (a : α) : Stream α :=
  const a

/-- Given a stream of functions and a stream of values, apply `n`-th function to `n`-th value. -/
def apply (f : Stream (α → β)) (s : Stream α) : Stream β := fun n => (nth f n) (nth s n)

-- mathport name: «expr ⊛ »
infixl:75 " ⊛ " => apply

-- input as \o*
/-- The stream of natural numbers: `stream.nth n stream.nats = n`. -/
def nats : Stream Nat := fun n => n

end Stream

