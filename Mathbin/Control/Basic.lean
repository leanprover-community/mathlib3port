/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Extends the theory on functors, applicatives and monads.

! This file was ported from Lean 3 source module control.basic
! leanprover-community/mathlib commit abb3121f210743a930dea73cd766d988079bdf8b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

universe u v w

variable {α β γ : Type u}

-- mathport name: «expr $< »
notation:1 a " $< " f:1 => f a

section Functor

variable {f : Type u → Type v} [Functor f] [LawfulFunctor f]

run_cmd
  mk_simp_attr `functor_norm

run_cmd
  tactic.add_doc_string `simp_attr.functor_norm "Simp set for functor_norm"

@[functor_norm]
theorem Functor.map_map (m : α → β) (g : β → γ) (x : f α) : g <$> m <$> x = (g ∘ m) <$> x :=
  (comp_map _ _ _).symm
#align functor.map_map Functor.map_mapₓ

@[simp]
theorem id_map' (x : f α) : (fun a => a) <$> x = x :=
  id_map _
#align id_map' id_map'ₓ

end Functor

section Applicative

variable {F : Type u → Type v} [Applicative F]

#print zipWithM /-
def zipWithM {α₁ α₂ φ : Type u} (f : α₁ → α₂ → F φ) : ∀ (ma₁ : List α₁) (ma₂ : List α₂), F (List φ)
  | x :: xs, y :: ys => (· :: ·) <$> f x y <*> zipWithM xs ys
  | _, _ => pure []
#align mzip_with zipWithM
-/

#print zipWithM' /-
def zipWithM' (f : α → β → F γ) : List α → List β → F PUnit
  | x :: xs, y :: ys => f x y *> zipWithM' xs ys
  | [], _ => pure PUnit.unit
  | _, [] => pure PUnit.unit
#align mzip_with' zipWithM'
-/

variable [LawfulApplicative F]

attribute [functor_norm] seq_assoc pure_seq_eq_map

@[simp]
theorem pure_id'_seq (x : F α) : (pure fun x => x) <*> x = x :=
  pure_id_seq x
#align pure_id'_seq pure_id'_seq

attribute [functor_norm] seq_assoc pure_seq_eq_map

@[functor_norm]
theorem seq_map_assoc (x : F (α → β)) (f : γ → α) (y : F γ) :
    x <*> f <$> y = (fun m : α → β => m ∘ f) <$> x <*> y :=
  by
  simp [(pure_seq_eq_map _ _).symm]
  simp [seq_assoc, (comp_map _ _ _).symm, (· ∘ ·)]
  simp [pure_seq_eq_map]
#align seq_map_assoc seq_map_assoc

@[functor_norm]
theorem map_seq (f : β → γ) (x : F (α → β)) (y : F α) : f <$> (x <*> y) = (· ∘ ·) f <$> x <*> y :=
  by simp [(pure_seq_eq_map _ _).symm] <;> simp [seq_assoc]
#align map_seq map_seq

end Applicative

-- TODO: setup `functor_norm` for `monad` laws
attribute [functor_norm] pure_bind bind_assoc bind_pure

section Monad

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

open List

#print List.partitionM /-
def List.partitionM {f : Type → Type} [Monad f] {α : Type} (p : α → f Bool) :
    List α → f (List α × List α)
  | [] => pure ([], [])
  | x :: xs =>
    condM (p x) (Prod.map (cons x) id <$> List.partitionM xs)
      (Prod.map id (cons x) <$> List.partitionM xs)
#align list.mpartition List.partitionM
-/

#print map_bind /-
theorem map_bind (x : m α) {g : α → m β} {f : β → γ} : f <$> (x >>= g) = x >>= fun a => f <$> g a :=
  by rw [← bind_pure_comp_eq_map, bind_assoc] <;> simp [bind_pure_comp_eq_map]
#align map_bind map_bind
-/

#print seq_bind_eq /-
theorem seq_bind_eq (x : m α) {g : β → m γ} {f : α → β} : f <$> x >>= g = x >>= g ∘ f :=
  show bind (f <$> x) g = bind x (g ∘ f) by
    rw [← bind_pure_comp_eq_map, bind_assoc] <;> simp [pure_bind]
#align seq_bind_eq seq_bind_eq
-/

theorem seq_eq_bind_map {x : m α} {f : m (α → β)} : f <*> x = f >>= (· <$> x) :=
  (bind_map_eq_seq f x).symm
#align seq_eq_bind_map seq_eq_bind_mapₓ

/-- This is the Kleisli composition -/
@[reducible]
def fish {m} [Monad m] {α β γ} (f : α → m β) (g : β → m γ) := fun x => f x >>= g
#align fish fish

-- mathport name: «expr >=> »
infixl:55
  " >=> " =>-- >=> is already defined in the core library but it is unusable
  -- because of its precedence (it is defined with precedence 2) and
  -- because it is defined as a lambda instead of having a named
  -- function
  fish

@[functor_norm]
theorem fish_pure {α β} (f : α → m β) : f >=> pure = f := by simp only [(· >=> ·), functor_norm]
#align fish_pure fish_pure

#print fish_pipe /-
@[functor_norm]
theorem fish_pipe {α β} (f : α → m β) : pure >=> f = f := by simp only [(· >=> ·), functor_norm]
#align fish_pipe fish_pipe
-/

@[functor_norm]
theorem fish_assoc {α β γ φ} (f : α → m β) (g : β → m γ) (h : γ → m φ) :
    f >=> g >=> h = f >=> (g >=> h) := by simp only [(· >=> ·), functor_norm]
#align fish_assoc fish_assoc

variable {β' γ' : Type v}

variable {m' : Type v → Type w} [Monad m']

#print List.mapAccumRM /-
def List.mapAccumRM (f : α → β' → m' (β' × γ')) : β' → List α → m' (β' × List γ')
  | a, [] => pure (a, [])
  | a, x :: xs => do
    let (a', ys) ← List.mapAccumRM a xs
    let (a'', y) ← f x a'
    pure (a'', y :: ys)
#align list.mmap_accumr List.mapAccumRM
-/

#print List.mapAccumLM /-
def List.mapAccumLM (f : β' → α → m' (β' × γ')) : β' → List α → m' (β' × List γ')
  | a, [] => pure (a, [])
  | a, x :: xs => do
    let (a', y) ← f a x
    let (a'', ys) ← List.mapAccumLM a' xs
    pure (a'', y :: ys)
#align list.mmap_accuml List.mapAccumLM
-/

end Monad

section

variable {m : Type u → Type u} [Monad m] [LawfulMonad m]

#print joinM_map_map /-
theorem joinM_map_map {α β : Type u} (f : α → β) (a : m (m α)) :
    joinM (Functor.map f <$> a) = f <$> joinM a := by
  simp only [joinM, (· ∘ ·), id.def, (bind_pure_comp_eq_map _ _).symm, bind_assoc, map_bind,
    pure_bind]
#align mjoin_map_map joinM_map_map
-/

#print joinM_map_joinM /-
theorem joinM_map_joinM {α : Type u} (a : m (m (m α))) : joinM (joinM <$> a) = joinM (joinM a) := by
  simp only [joinM, (· ∘ ·), id.def, map_bind, (bind_pure_comp_eq_map _ _).symm, bind_assoc,
    pure_bind]
#align mjoin_map_mjoin joinM_map_joinM
-/

#print joinM_map_pure /-
@[simp]
theorem joinM_map_pure {α : Type u} (a : m α) : joinM (pure <$> a) = a := by
  simp only [joinM, (· ∘ ·), id.def, map_bind, (bind_pure_comp_eq_map _ _).symm, bind_assoc,
    pure_bind, bind_pure]
#align mjoin_map_pure joinM_map_pure
-/

#print joinM_pure /-
@[simp]
theorem joinM_pure {α : Type u} (a : m α) : joinM (pure a) = a :=
  LawfulMonad.pure_bind a id
#align mjoin_pure joinM_pure
-/

end

section Alternative

variable {F : Type → Type v} [Alternative F]

#print succeeds /-
def succeeds {α} (x : F α) : F Bool :=
  x $> true <|> pure false
#align succeeds succeeds
-/

#print tryM /-
def tryM {α} (x : F α) : F Unit :=
  x $> () <|> pure ()
#align mtry tryM
-/

#print guard_true /-
@[simp]
theorem guard_true {h : Decidable True} : @guard F _ True h = pure () := by simp [guard]
#align guard_true guard_true
-/

#print guard_false /-
@[simp]
theorem guard_false {h : Decidable False} : @guard F _ False h = failure := by simp [guard]
#align guard_false guard_false
-/

end Alternative

namespace Sum

variable {e : Type v}

#print Sum.bind /-
protected def bind {α β} : Sum e α → (α → Sum e β) → Sum e β
  | inl x, _ => inl x
  | inr x, f => f x
#align sum.bind Sum.bind
-/

instance : Monad (Sum.{v, u} e) where
  pure := @Sum.inr e
  bind := @Sum.bind e

instance : LawfulFunctor (Sum.{v, u} e) := by refine' { .. } <;> intros <;> casesm Sum _ _ <;> rfl

instance : LawfulMonad (Sum.{v, u} e)
    where
  bind_assoc := by intros; casesm Sum _ _ <;> rfl
  pure_bind := by intros; rfl
  bind_pure_comp_eq_map := by intros; casesm Sum _ _ <;> rfl
  bind_map_eq_seq := by intros; cases f <;> rfl

end Sum

#print CommApplicative /-
class CommApplicative (m : Type _ → Type _) [Applicative m] extends LawfulApplicative m : Prop where
  commutative_prod :
    ∀ {α β} (a : m α) (b : m β), Prod.mk <$> a <*> b = (fun b a => (a, b)) <$> b <*> a
#align is_comm_applicative CommApplicative
-/

open Functor

theorem CommApplicative.commutative_map {m : Type _ → Type _} [Applicative m] [CommApplicative m]
    {α β γ} (a : m α) (b : m β) {f : α → β → γ} : f <$> a <*> b = flip f <$> b <*> a :=
  calc
    f <$> a <*> b = (fun p : α × β => f p.1 p.2) <$> (Prod.mk <$> a <*> b) := by
      simp [seq_map_assoc, map_seq, seq_assoc, seq_pure, map_map]
    _ = (fun b a => f a b) <$> b <*> a := by
      rw [CommApplicative.commutative_prod] <;>
        simp [seq_map_assoc, map_seq, seq_assoc, seq_pure, map_map]
    
#align is_comm_applicative.commutative_map CommApplicative.commutative_map

