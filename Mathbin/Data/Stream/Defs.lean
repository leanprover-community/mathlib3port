
/-!
# Definition of `stream` and functions on streams

A stream `stream α` is an infinite sequence of elements of `α`. One can also think about it as an
infinite list. In this file we define `stream` and some functions that take and/or return streams.
-/


universe u v w

def Streamₓ (α : Type u) :=
  Nat → α

open Nat

namespace Streamₓ

variable {α : Type u} {β : Type v} {δ : Type w}

def cons (a : α) (s : Streamₓ α) : Streamₓ α :=
  fun i =>
    match i with 
    | 0 => a
    | succ n => s n

@[reducible]
def head (s : Streamₓ α) : α :=
  s 0

def tail (s : Streamₓ α) : Streamₓ α :=
  fun i => s (i+1)

def drop (n : Nat) (s : Streamₓ α) : Streamₓ α :=
  fun i => s (i+n)

@[reducible]
def nth (n : Nat) (s : Streamₓ α) : α :=
  s n

def all (p : α → Prop) (s : Streamₓ α) :=
  ∀ n, p (nth n s)

def any (p : α → Prop) (s : Streamₓ α) :=
  ∃ n, p (nth n s)

protected def mem (a : α) (s : Streamₓ α) :=
  any (fun b => a = b) s

instance : HasMem α (Streamₓ α) :=
  ⟨Streamₓ.Mem⟩

def map (f : α → β) (s : Streamₓ α) : Streamₓ β :=
  fun n => f (nth n s)

def zip (f : α → β → δ) (s₁ : Streamₓ α) (s₂ : Streamₓ β) : Streamₓ δ :=
  fun n => f (nth n s₁) (nth n s₂)

def const (a : α) : Streamₓ α :=
  fun n => a

def iterate (f : α → α) (a : α) : Streamₓ α :=
  fun n => Nat.recOn n a fun n r => f r

def corec (f : α → β) (g : α → α) : α → Streamₓ β :=
  fun a => map f (iterate g a)

def corec_on (a : α) (f : α → β) (g : α → α) : Streamₓ β :=
  corec f g a

def corec' (f : α → β × α) : α → Streamₓ β :=
  corec (Prod.fst ∘ f) (Prod.snd ∘ f)

def unfolds (g : α → β) (f : α → α) (a : α) : Streamₓ β :=
  corec g f a

def interleave (s₁ s₂ : Streamₓ α) : Streamₓ α :=
  corec_on (s₁, s₂) (fun ⟨s₁, s₂⟩ => head s₁) fun ⟨s₁, s₂⟩ => (s₂, tail s₁)

infixl:65 "⋈" => interleave

def even (s : Streamₓ α) : Streamₓ α :=
  corec (fun s => head s) (fun s => tail (tail s)) s

def odd (s : Streamₓ α) : Streamₓ α :=
  even (tail s)

def append_stream : List α → Streamₓ α → Streamₓ α
| [], s => s
| List.cons a l, s => a :: append_stream l s

infixl:65 "++ₛ" => append_stream

def approx : Nat → Streamₓ α → List α
| 0, s => []
| n+1, s => List.cons (head s) (approx n (tail s))

/-- `take s n` returns a list of the `n` first elements of stream `s` -/
def take {α} (s : Streamₓ α) (n : ℕ) : List α :=
  (List.range n).map s

/-- An auxiliary definition for `stream.cycle` corecursive def -/
protected def cycle_f : α × List α × α × List α → α
| (v, _, _, _) => v

/-- An auxiliary definition for `stream.cycle` corecursive def -/
protected def cycle_g : α × List α × α × List α → α × List α × α × List α
| (v₁, [], v₀, l₀) => (v₀, l₀, v₀, l₀)
| (v₁, List.cons v₂ l₂, v₀, l₀) => (v₂, l₂, v₀, l₀)

def cycle : ∀ l : List α, l ≠ [] → Streamₓ α
| [], h => absurd rfl h
| List.cons a l, h => corec Streamₓ.cycleF Streamₓ.cycleG (a, l, a, l)

def tails (s : Streamₓ α) : Streamₓ (Streamₓ α) :=
  corec id tail (tail s)

def inits_core (l : List α) (s : Streamₓ α) : Streamₓ (List α) :=
  corec_on (l, s) (fun ⟨a, b⟩ => a)
    fun p =>
      match p with 
      | (l', s') => (l' ++ [head s'], tail s')

def inits (s : Streamₓ α) : Streamₓ (List α) :=
  inits_core [head s] (tail s)

def pure (a : α) : Streamₓ α :=
  const a

def apply (f : Streamₓ (α → β)) (s : Streamₓ α) : Streamₓ β :=
  fun n => (nth n f) (nth n s)

infixl:75 "⊛" => apply

def nats : Streamₓ Nat :=
  fun n => n

end Streamₓ

