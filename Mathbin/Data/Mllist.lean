/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Keeley Hoek, Simon Hudon, Scott Morrison
-/
import Mathbin.Data.Option.Defs

#align_import data.mllist from "leanprover-community/mathlib"@"31ca6f9cf5f90a6206092cd7f84b359dcb6d52e0"

/-! # Monadic lazy lists.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An alternative construction of lazy lists (see also `data.lazy_list`),
with "lazyness" controlled by an arbitrary monad.

The inductive construction is not allowed outside of meta (indeed, we can build infinite objects).
This isn't so bad, as the typical use is with the tactic monad, in any case.

As we're in meta anyway, we don't bother with proofs about these constructions.
-/


universe u v

namespace Tactic

#print ListM /-
-- We hide this away in the tactic namespace, just because it's all meta.
/-- A monadic lazy list, controlled by an arbitrary monad. -/
unsafe inductive ListM (m : Type u → Type u) (α : Type u) : Type u
  | nil : mllist
  | cons : m (Option α × mllist) → mllist
#align tactic.mllist ListM
-/

namespace Mllist

variable {α β : Type u} {m : Type u → Type u}

#print ListM.fix /-
/-- Construct an `mllist` recursively. -/
unsafe def ListM.fix [Alternative m] (f : α → m α) : α → ListM m α
  | x => cons <| (fun a => (some x, fix a)) <$> f x <|> pure (some x, nil)
#align tactic.mllist.fix ListM.fix
-/

variable [Monad m]

#print ListM.fixl_with /-
/-- Repeatedly apply a function `f : α → m (α × list β)` to an initial `a : α`,
accumulating the elements of the resulting `list β` as a single monadic lazy list.

(This variant allows starting with a specified `list β` of elements, as well. )-/
unsafe def ListM.fixl_with [Alternative m] (f : α → m (α × List β)) : α → List β → ListM m β
  | s, b :: rest => cons <| pure (some b, fixl_with s rest)
  | s, [] =>
    cons <|
      (do
          let (s', l) ← f s
          match l with
            | b :: rest => pure (some b, fixl_with s' rest)
            | [] => pure (none, fixl_with s' [])) <|>
        pure (none, nil)
#align tactic.mllist.fixl_with ListM.fixl_with
-/

#print ListM.fixl /-
/-- Repeatedly apply a function `f : α → m (α × list β)` to an initial `a : α`,
accumulating the elements of the resulting `list β` as a single monadic lazy list. -/
unsafe def ListM.fixl [Alternative m] (f : α → m (α × List β)) (s : α) : ListM m β :=
  ListM.fixl_with f s []
#align tactic.mllist.fixl ListM.fixl
-/

#print ListM.uncons /-
/-- Deconstruct an `mllist`, returning inside the monad an optional pair `α × mllist m α`
representing the head and tail of the list. -/
unsafe def ListM.uncons {α : Type u} : ListM m α → m (Option (α × ListM m α))
  | nil => pure none
  | cons l => do
    let (x, xs) ← l
    let some x ← return x |
      uncons xs
    return (x, xs)
#align tactic.mllist.uncons ListM.uncons
-/

#print ListM.isEmpty /-
/-- Compute, inside the monad, whether an `mllist` is empty. -/
unsafe def ListM.isEmpty {α : Type u} (xs : ListM m α) : m (ULift Bool) :=
  (ULift.up ∘ Option.isSome) <$> ListM.uncons xs
#align tactic.mllist.empty ListM.isEmpty
-/

#print ListM.ofList /-
/-- Convert a `list` to an `mllist`. -/
unsafe def ListM.ofList {α : Type u} : List α → ListM m α
  | [] => nil
  | h :: t => cons (pure (h, of_list t))
#align tactic.mllist.of_list ListM.ofList
-/

#print ListM.ofListM /-
/-- Convert a `list` of values inside the monad into an `mllist`. -/
unsafe def ListM.ofListM {α : Type u} : List (m α) → ListM m α
  | [] => nil
  | h :: t => cons ((fun x => (x, m_of_list t)) <$> some <$> h)
#align tactic.mllist.m_of_list ListM.ofListM
-/

#print ListM.force /-
/-- Extract a list inside the monad from an `mllist`. -/
unsafe def ListM.force {α} : ListM m α → m (List α)
  | nil => pure []
  | cons l => do
    let (x, xs) ← l
    let some x ← pure x |
      force xs
    (· :: ·) x <$> force xs
#align tactic.mllist.force ListM.force
-/

#print ListM.takeAsList /-
/-- Take the first `n` elements, as a list inside the monad. -/
unsafe def ListM.takeAsList {α} : ListM m α → ℕ → m (List α)
  | nil, _ => pure []
  | _, 0 => pure []
  | cons l, n + 1 => do
    let (x, xs) ← l
    let some x ← pure x |
      take xs (n + 1)
    (· :: ·) x <$> take xs n
#align tactic.mllist.take ListM.takeAsList
-/

#print ListM.map /-
/-- Apply a function to every element of an `mllist`. -/
unsafe def ListM.map {α β : Type u} (f : α → β) : ListM m α → ListM m β
  | nil => nil
  | cons l =>
    cons do
      let (x, xs) ← l
      pure (f <$> x, map xs)
#align tactic.mllist.map ListM.map
-/

#print ListM.mapM /-
/-- Apply a function which returns values in the monad to every element of an `mllist`. -/
unsafe def ListM.mapM {α β : Type u} (f : α → m β) : ListM m α → ListM m β
  | nil => nil
  | cons l =>
    cons do
      let (x, xs) ← l
      let b ← x.traverse f
      return (b, mmap xs)
#align tactic.mllist.mmap ListM.mapM
-/

#print ListM.filter /-
/-- Filter a `mllist`. -/
unsafe def ListM.filter {α : Type u} (p : α → Prop) [DecidablePred p] : ListM m α → ListM m α
  | nil => nil
  | cons l =>
    cons do
      let (a, r) ← l
      let some a ← return a |
        return (none, Filter r)
      return (if p a then some a else none, Filter r)
#align tactic.mllist.filter ListM.filter
-/

#print ListM.filterM /-
/-- Filter a `mllist` using a function which returns values in the (alternative) monad.
Whenever the function "succeeds", we accept the element, and reject otherwise. -/
unsafe def ListM.filterM [Alternative m] {α β : Type u} (p : α → m β) : ListM m α → ListM m α
  | nil => nil
  | cons l =>
    cons do
      let (a, r) ← l
      let some a ← return a |
        return (none, mfilter r)
      p a >> return (a, mfilter r) <|> return (none, mfilter r)
#align tactic.mllist.mfilter ListM.filterM
-/

#print ListM.filterMap /-
/-- Filter and transform a `mllist` using an `option` valued function. -/
unsafe def ListM.filterMap {α β : Type u} (f : α → Option β) : ListM m α → ListM m β
  | nil => nil
  | cons l =>
    cons do
      let (a, r) ← l
      let some a ← return a |
        return (none, filter_map r)
      match f a with
        | some b => return (some b, filter_map r)
        | none => return (none, filter_map r)
#align tactic.mllist.filter_map ListM.filterMap
-/

#print ListM.filterMapM /-
/-- Filter and transform a `mllist` using a function that returns values inside the monad.
We discard elements where the function fails. -/
unsafe def ListM.filterMapM [Alternative m] {α β : Type u} (f : α → m β) : ListM m α → ListM m β
  | nil => nil
  | cons l =>
    cons do
      let (a, r) ← l
      let some a ← return a |
        return (none, mfilter_map r)
      (f a >>= fun b => return (some b, mfilter_map r)) <|> return (none, mfilter_map r)
#align tactic.mllist.mfilter_map ListM.filterMapM
-/

#print ListM.append /-
/-- Concatenate two monadic lazty lists. -/
unsafe def ListM.append {α : Type u} : ListM m α → ListM m α → ListM m α
  | nil, ys => ys
  | cons xs, ys =>
    cons do
      let (x, xs) ← xs
      return (x, append xs ys)
#align tactic.mllist.append ListM.append
-/

#print ListM.join /-
/-- Join a monadic lazy list of monadic lazy lists into a single monadic lazy list. -/
unsafe def ListM.join {α : Type u} : ListM m (ListM m α) → ListM m α
  | nil => nil
  | cons l =>
    cons do
      let (xs, r) ← l
      let some xs ← return xs |
        return (none, join r)
      match xs with
        | nil => return (none, join r)
        | cons m => do
          let (a, n) ← m
          return (a, join (cons <| return (n, r)))
#align tactic.mllist.join ListM.join
-/

#print ListM.squash /-
/-- Lift a monadic lazy list inside the monad to a monadic lazy list. -/
unsafe def ListM.squash {α} (t : m (ListM m α)) : ListM m α :=
  (ListM.ofListM [t]).join
#align tactic.mllist.squash ListM.squash
-/

#print ListM.enum_from /-
/-- Enumerate the elements of a monadic lazy list, starting at a specified offset. -/
unsafe def ListM.enum_from {α : Type u} : ℕ → ListM m α → ListM m (ℕ × α)
  | _, nil => nil
  | n, cons l =>
    cons do
      let (a, r) ← l
      let some a ← return a |
        return (none, enum_from n r)
      return ((n, a), enum_from (n + 1) r)
#align tactic.mllist.enum_from ListM.enum_from
-/

#print ListM.enum /-
/-- Enumerate the elements of a monadic lazy list. -/
unsafe def ListM.enum {α : Type u} : ListM m α → ListM m (ℕ × α) :=
  ListM.enum_from 0
#align tactic.mllist.enum ListM.enum
-/

#print ListM.range /-
/-- The infinite monadic lazy list of natural numbers.-/
unsafe def ListM.range {m : Type → Type} [Alternative m] : ListM m ℕ :=
  ListM.fix (fun n => pure (n + 1)) 0
#align tactic.mllist.range ListM.range
-/

#print ListM.concat /-
/-- Add one element to the end of a monadic lazy list. -/
unsafe def ListM.concat {α : Type u} : ListM m α → α → ListM m α
  | L, a => (ListM.ofList [L, ListM.ofList [a]]).join
#align tactic.mllist.concat ListM.concat
-/

#print ListM.bind /-
/-- Apply a function returning a monadic lazy list to each element of a monadic lazy list,
joining the results. -/
unsafe def ListM.bind {α β : Type u} : ListM m α → (α → ListM m β) → ListM m β
  | nil, f => nil
  | cons ll, f =>
    cons do
      let (x, xs) ← ll
      let some x ← return x |
        return (none, bind_ xs f)
      return (none, append (f x) (bind_ xs f))
#align tactic.mllist.bind_ ListM.bind
-/

#print ListM.monadLift /-
/-- Convert any value in the monad to the singleton monadic lazy list. -/
unsafe def ListM.monadLift {α} (x : m α) : ListM m α :=
  cons <| (flip Prod.mk nil ∘ some) <$> x
#align tactic.mllist.monad_lift ListM.monadLift
-/

#print ListM.head /-
/-- Return the head of a monadic lazy list, as a value in the monad. -/
unsafe def ListM.head [Alternative m] {α} (L : ListM m α) : m α := do
  let some (r, _) ← L.uncons |
    failure
  return r
#align tactic.mllist.head ListM.head
-/

#print ListM.firstM /-
/-- Apply a function returning values inside the monad to a monadic lazy list,
returning only the first successful result. -/
unsafe def ListM.firstM [Alternative m] {α β} (L : ListM m α) (f : α → m β) : m β :=
  (L.mfilter_map f).headI
#align tactic.mllist.mfirst ListM.firstM
-/

end Mllist

end Tactic

