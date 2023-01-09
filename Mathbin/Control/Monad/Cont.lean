/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Monad encapsulating continuation passing programming style, similar to
Haskell's `Cont`, `ContT` and `MonadCont`:
<http://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Cont.html>

! This file was ported from Lean 3 source module control.monad.cont
! leanprover-community/mathlib commit 247a102b14f3cebfee126293341af5f6bed00237
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Control.Monad.Basic
import Mathbin.Control.Monad.Writer

universe u v w u₀ u₁ v₀ v₁

structure MonadCont.Label (α : Type w) (m : Type u → Type v) (β : Type u) where
  apply : α → m β
#align monad_cont.label MonadCont.Label

def MonadCont.goto {α β} {m : Type u → Type v} (f : MonadCont.Label α m β) (x : α) :=
  f.apply x
#align monad_cont.goto MonadCont.goto

class MonadCont (m : Type u → Type v) where
  callCc : ∀ {α β}, (MonadCont.Label α m β → m α) → m α
#align monad_cont MonadCont

open MonadCont

class IsLawfulMonadCont (m : Type u → Type v) [Monad m] [MonadCont m] extends LawfulMonad m where
  call_cc_bind_right {α ω γ} (cmd : m α) (next : Label ω m γ → α → m ω) :
    (callCc fun f => cmd >>= next f) = cmd >>= fun x => callCc fun f => next f x
  call_cc_bind_left {α} (β) (x : α) (dead : Label α m β → β → m α) :
    (callCc fun f : Label α m β => goto f x >>= dead f) = pure x
  call_cc_dummy {α β} (dummy : m α) : (callCc fun f : Label α m β => dummy) = dummy
#align is_lawful_monad_cont IsLawfulMonadCont

export IsLawfulMonadCont ()

def ContT (r : Type u) (m : Type u → Type v) (α : Type w) :=
  (α → m r) → m r
#align cont_t ContT

@[reducible]
def Cont (r : Type u) (α : Type w) :=
  ContT r id α
#align cont Cont

namespace ContT

export MonadCont (Label goto)

variable {r : Type u} {m : Type u → Type v} {α β γ ω : Type w}

def run : ContT r m α → (α → m r) → m r :=
  id
#align cont_t.run ContT.run

def map (f : m r → m r) (x : ContT r m α) : ContT r m α :=
  f ∘ x
#align cont_t.map ContT.map

theorem run_cont_t_map_cont_t (f : m r → m r) (x : ContT r m α) : run (map f x) = f ∘ run x :=
  rfl
#align cont_t.run_cont_t_map_cont_t ContT.run_cont_t_map_cont_t

def withContT (f : (β → m r) → α → m r) (x : ContT r m α) : ContT r m β := fun g => x <| f g
#align cont_t.with_cont_t ContT.withContT

theorem run_with_cont_t (f : (β → m r) → α → m r) (x : ContT r m α) :
    run (withContT f x) = run x ∘ f :=
  rfl
#align cont_t.run_with_cont_t ContT.run_with_cont_t

@[ext]
protected theorem ext {x y : ContT r m α} (h : ∀ f, x.run f = y.run f) : x = y := by ext <;> apply h
#align cont_t.ext ContT.ext

instance : Monad (ContT r m) where
  pure α x f := f x
  bind α β x f g := x fun i => f i g

instance : LawfulMonad (ContT r m)
    where
  id_map := by
    intros
    rfl
  pure_bind := by
    intros
    ext
    rfl
  bind_assoc := by
    intros
    ext
    rfl

def monadLift [Monad m] {α} : m α → ContT r m α := fun x f => x >>= f
#align cont_t.monad_lift ContT.monadLift

instance [Monad m] : HasMonadLift m (ContT r m) where monadLift α := ContT.monadLift

theorem monad_lift_bind [Monad m] [LawfulMonad m] {α β} (x : m α) (f : α → m β) :
    (monadLift (x >>= f) : ContT r m β) = monadLift x >>= monad_lift ∘ f :=
  by
  ext
  simp only [monad_lift, HasMonadLift.monadLift, (· ∘ ·), (· >>= ·), bind_assoc, id.def, run,
    ContT.monadLift]
#align cont_t.monad_lift_bind ContT.monad_lift_bind

instance : MonadCont (ContT r m) where callCc α β f g := f ⟨fun x h => g x⟩ g

instance : IsLawfulMonadCont (ContT r m)
    where
  call_cc_bind_right := by intros <;> ext <;> rfl
  call_cc_bind_left := by intros <;> ext <;> rfl
  call_cc_dummy := by intros <;> ext <;> rfl

instance (ε) [MonadExcept ε m] : MonadExcept ε (ContT r m)
    where
  throw x e f := throw e
  catch α act h f := catch (act f) fun e => h e f

instance : MonadRun (fun α => (α → m r) → ULift.{u, v} (m r)) (ContT.{u, v, u} r m)
    where run α f x := ⟨f x⟩

end ContT

variable {m : Type u → Type v} [Monad m]

def ExceptT.mkLabel {α β ε} : Label (Except.{u, u} ε α) m β → Label α (ExceptT ε m) β
  | ⟨f⟩ => ⟨fun a => monad_lift <| f (Except.ok a)⟩
#align except_t.mk_label ExceptTₓ.mkLabel

theorem ExceptT.goto_mk_label {α β ε : Type _} (x : Label (Except.{u, u} ε α) m β) (i : α) :
    goto (ExceptT.mkLabel x) i = ⟨Except.ok <$> goto x (Except.ok i)⟩ := by cases x <;> rfl
#align except_t.goto_mk_label ExceptTₓ.goto_mk_label

def ExceptT.callCc {ε} [MonadCont m] {α β : Type _} (f : Label α (ExceptT ε m) β → ExceptT ε m α) :
    ExceptT ε m α :=
  ExceptT.mk (call_cc fun x : Label _ m β => ExceptT.run <| f (ExceptT.mkLabel x) : m (Except ε α))
#align except_t.call_cc ExceptTₓ.callCc

instance {ε} [MonadCont m] : MonadCont (ExceptT ε m) where callCc α β := ExceptT.callCc

instance {ε} [MonadCont m] [IsLawfulMonadCont m] : IsLawfulMonadCont (ExceptT ε m)
    where
  call_cc_bind_right := by
    intros
    simp [call_cc, ExceptT.callCc, call_cc_bind_right]
    ext
    dsimp
    congr with ⟨⟩ <;> simp [ExceptT.bindCont, @call_cc_dummy m _]
  call_cc_bind_left := by
    intros
    simp [call_cc, ExceptT.callCc, call_cc_bind_right, ExceptT.goto_mk_label, map_eq_bind_pure_comp,
      bind_assoc, @call_cc_bind_left m _]
    ext
    rfl
  call_cc_dummy := by
    intros
    simp [call_cc, ExceptT.callCc, @call_cc_dummy m _]
    ext
    rfl

def OptionT.mkLabel {α β} : Label (Option.{u} α) m β → Label α (OptionT m) β
  | ⟨f⟩ => ⟨fun a => monad_lift <| f (some a)⟩
#align option_t.mk_label OptionTₓ.mkLabel

theorem OptionT.goto_mk_label {α β : Type _} (x : Label (Option.{u} α) m β) (i : α) :
    goto (OptionT.mkLabel x) i = ⟨some <$> goto x (some i)⟩ := by cases x <;> rfl
#align option_t.goto_mk_label OptionTₓ.goto_mk_label

def OptionT.callCc [MonadCont m] {α β : Type _} (f : Label α (OptionT m) β → OptionT m α) :
    OptionT m α :=
  OptionT.mk (call_cc fun x : Label _ m β => OptionT.run <| f (OptionT.mkLabel x) : m (Option α))
#align option_t.call_cc OptionTₓ.callCc

instance [MonadCont m] : MonadCont (OptionT m) where callCc α β := OptionT.callCc

instance [MonadCont m] [IsLawfulMonadCont m] : IsLawfulMonadCont (OptionT m)
    where
  call_cc_bind_right := by
    intros
    simp [call_cc, OptionT.callCc, call_cc_bind_right]
    ext
    dsimp
    congr with ⟨⟩ <;> simp [OptionT.bindCont, @call_cc_dummy m _]
  call_cc_bind_left := by
    intros
    simp [call_cc, OptionT.callCc, call_cc_bind_right, OptionT.goto_mk_label, map_eq_bind_pure_comp,
      bind_assoc, @call_cc_bind_left m _]
    ext
    rfl
  call_cc_dummy := by
    intros
    simp [call_cc, OptionT.callCc, @call_cc_dummy m _]
    ext
    rfl

/- warning: writer_t.mk_label -> WriterTₓ.mkLabel is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m] {α : Type.{u3}} {β : Type.{u1}} {ω : Type.{u1}} [_inst_2 : One.{u1} ω], (MonadCont.Label.{u1, u2, max u3 u1} (Prod.{u3, u1} α ω) m β) -> (MonadCont.Label.{u1, max u1 u2, u3} α (WriterTₓ.{u1, u2} ω m) β)
but is expected to have type
  forall {m : Type.{u2} -> Type.{u3}} [_inst_1 : Monad.{u2, u3} m] {α : Type.{u1}} {β : Type.{u2}} {ω : Type.{u2}} [_inst_2 : One.{u2} ω], (MonadCont.Label.{u2, u3, max u1 u2} (Prod.{u1, u2} α ω) m β) -> (MonadCont.Label.{u2, max u2 u3, u1} α (WriterTₓ.{u2, u3} ω m) β)
Case conversion may be inaccurate. Consider using '#align writer_t.mk_label WriterTₓ.mkLabelₓ'. -/
def WriterT.mkLabel {α β ω} [One ω] : Label (α × ω) m β → Label α (WriterT ω m) β
  | ⟨f⟩ => ⟨fun a => monad_lift <| f (a, 1)⟩
#align writer_t.mk_label WriterTₓ.mkLabel

theorem WriterT.goto_mk_label {α β ω : Type _} [One ω] (x : Label (α × ω) m β) (i : α) :
    goto (WriterT.mkLabel x) i = monadLift (goto x (i, 1)) := by cases x <;> rfl
#align writer_t.goto_mk_label WriterTₓ.goto_mk_label

def WriterT.callCc [MonadCont m] {α β ω : Type _} [One ω]
    (f : Label α (WriterT ω m) β → WriterT ω m α) : WriterT ω m α :=
  ⟨callCc (WriterT.run ∘ f ∘ WriterT.mkLabel : Label (α × ω) m β → m (α × ω))⟩
#align writer_t.call_cc WriterTₓ.callCc

instance (ω) [Monad m] [One ω] [MonadCont m] : MonadCont (WriterT ω m)
    where callCc α β := WriterT.callCc

/- warning: state_t.mk_label -> StateTₓ.mkLabel is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m] {α : Type.{u1}} {β : Type.{u1}} {σ : Type.{u1}}, (MonadCont.Label.{u1, u2, u1} (Prod.{u1, u1} α σ) m (Prod.{u1, u1} β σ)) -> (MonadCont.Label.{u1, max u1 u2, u1} α (StateTₓ.{u1, u2} σ m) β)
but is expected to have type
  forall {m : Type.{u1} -> Type.{u2}} {_inst_1 : Type.{u1}} {α : Type.{u1}} {β : Type.{u1}}, (MonadCont.Label.{u1, u2, u1} (Prod.{u1, u1} _inst_1 β) m (Prod.{u1, u1} α β)) -> (MonadCont.Label.{u1, max u1 u2, u1} _inst_1 (StateTₓ.{u1, u2} β m) α)
Case conversion may be inaccurate. Consider using '#align state_t.mk_label StateTₓ.mkLabelₓ'. -/
def StateT.mkLabel {α β σ : Type u} : Label (α × σ) m (β × σ) → Label α (StateT σ m) β
  | ⟨f⟩ => ⟨fun a => ⟨fun s => f (a, s)⟩⟩
#align state_t.mk_label StateTₓ.mkLabel

theorem StateT.goto_mk_label {α β σ : Type u} (x : Label (α × σ) m (β × σ)) (i : α) :
    goto (StateT.mkLabel x) i = ⟨fun s => goto x (i, s)⟩ := by cases x <;> rfl
#align state_t.goto_mk_label StateTₓ.goto_mk_label

def StateT.callCc {σ} [MonadCont m] {α β : Type _} (f : Label α (StateT σ m) β → StateT σ m α) :
    StateT σ m α :=
  ⟨fun r => callCc fun f' => (f <| StateT.mkLabel f').run r⟩
#align state_t.call_cc StateTₓ.callCc

instance {σ} [MonadCont m] : MonadCont (StateT σ m) where callCc α β := StateT.callCc

instance {σ} [MonadCont m] [IsLawfulMonadCont m] : IsLawfulMonadCont (StateT σ m)
    where
  call_cc_bind_right := by
    intros
    simp [call_cc, StateT.callCc, call_cc_bind_right, (· >>= ·), StateT.bind]
    ext
    dsimp
    congr with ⟨x₀, x₁⟩
    rfl
  call_cc_bind_left := by
    intros
    simp [call_cc, StateT.callCc, call_cc_bind_left, (· >>= ·), StateT.bind, StateT.goto_mk_label]
    ext
    rfl
  call_cc_dummy := by
    intros
    simp [call_cc, StateT.callCc, call_cc_bind_right, (· >>= ·), StateT.bind, @call_cc_dummy m _]
    ext
    rfl

/- warning: reader_t.mk_label -> ReaderTₓ.mkLabel is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m] {α : Type.{u3}} {β : Type.{u1}} (ρ : Type.{u1}), (MonadCont.Label.{u1, u2, u3} α m β) -> (MonadCont.Label.{u1, max u1 u2, u3} α (ReaderTₓ.{u1, u2} ρ m) β)
but is expected to have type
  forall {m : Type.{u2} -> Type.{u3}} [_inst_1 : Monad.{u2, u3} m] {α : Type.{u1}} {β : Type.{u2}} (ρ : Type.{u2}), (MonadCont.Label.{u2, u3, u1} α m β) -> (MonadCont.Label.{u2, max u2 u3, u1} α (ReaderTₓ.{u2, u3} ρ m) β)
Case conversion may be inaccurate. Consider using '#align reader_t.mk_label ReaderTₓ.mkLabelₓ'. -/
def ReaderT.mkLabel {α β} (ρ) : Label α m β → Label α (ReaderT ρ m) β
  | ⟨f⟩ => ⟨monad_lift ∘ f⟩
#align reader_t.mk_label ReaderTₓ.mkLabel

theorem ReaderT.goto_mk_label {α ρ β} (x : Label α m β) (i : α) :
    goto (ReaderT.mkLabel ρ x) i = monadLift (goto x i) := by cases x <;> rfl
#align reader_t.goto_mk_label ReaderTₓ.goto_mk_label

def ReaderT.callCc {ε} [MonadCont m] {α β : Type _} (f : Label α (ReaderT ε m) β → ReaderT ε m α) :
    ReaderT ε m α :=
  ⟨fun r => callCc fun f' => (f <| ReaderT.mkLabel _ f').run r⟩
#align reader_t.call_cc ReaderTₓ.callCc

instance {ρ} [MonadCont m] : MonadCont (ReaderT ρ m) where callCc α β := ReaderT.callCc

instance {ρ} [MonadCont m] [IsLawfulMonadCont m] : IsLawfulMonadCont (ReaderT ρ m)
    where
  call_cc_bind_right := by
    intros
    simp [call_cc, ReaderT.callCc, call_cc_bind_right]
    ext
    rfl
  call_cc_bind_left := by
    intros
    simp [call_cc, ReaderT.callCc, call_cc_bind_left, ReaderT.goto_mk_label]
    ext
    rfl
  call_cc_dummy := by
    intros
    simp [call_cc, ReaderT.callCc, @call_cc_dummy m _]
    ext
    rfl

/-- reduce the equivalence between two continuation passing monads to the equivalence between
their underlying monad -/
def ContT.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁} {α₁ r₁ : Type u₀}
    {α₂ r₂ : Type u₁} (F : m₁ r₁ ≃ m₂ r₂) (G : α₁ ≃ α₂) : ContT r₁ m₁ α₁ ≃ ContT r₂ m₂ α₂
    where
  toFun f r := F <| f fun x => F.symm <| r <| G x
  invFun f r := F.symm <| f fun x => F <| r <| G.symm x
  left_inv f := by funext r <;> simp
  right_inv f := by funext r <;> simp
#align cont_t.equiv ContT.equiv

