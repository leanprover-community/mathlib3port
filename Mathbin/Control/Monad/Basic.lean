/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module control.monad.basic
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Equiv.Defs
import Mathbin.Tactic.Basic

/-!
# Monad

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Attributes

 * ext
 * functor_norm
 * monad_norm

## Implementation Details

Set of rewrite rules and automation for monads in general and
`reader_t`, `state_t`, `except_t` and `option_t` in particular.

The rewrite rules for monads are carefully chosen so that `simp with
functor_norm` will not introduce monadic vocabulary in a context where
applicatives would do just fine but will handle monadic notation
already present in an expression.

In a context where monadic reasoning is desired `simp with monad_norm`
will translate functor and applicative notation into monad notation
and use regular `functor_norm` rules as well.

## Tags

functor, applicative, monad, simp

-/


/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:61:9: unsupported: weird string -/
/- failed to parenthesize: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
[PrettyPrinter.parenthesize.input] (Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr
     [(Command.docComment
       "/--"
       "./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:61:9: unsupported: weird string -/")]
     "register_simp_attr"
     `monad_norm)-/-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/-- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:61:9: unsupported: weird string -/
  register_simp_attr
  monad_norm

/- [mathport] port note: move this to another file, it won't work here -/
attribute [monad_norm] functor_norm

attribute [ext] ReaderT.ext StateT.ext ExceptT.ext OptionT.ext

attribute [functor_norm] bind_assoc pure_bind bind_pure

attribute [monad_norm] seq_eq_bind_map

universe u v

/- warning: map_eq_bind_pure_comp -> map_eq_bind_pure_comp is a dubious translation:
lean 3 declaration is
  forall (m : Type.{u1} -> Type.{u2}) [_inst_1 : Monad.{u1, u2} m] [_inst_2 : LawfulMonad.{u1, u2} m _inst_1] {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (x : m α), Eq.{succ u2} (m β) (Functor.map.{u1, u2} (fun {α : Type.{u1}} => m α) (Applicative.toFunctor.{u1, u2} (fun {α : Type.{u1}} => m α) (Monad.toApplicative.{u1, u2} (fun {α : Type.{u1}} => m α) _inst_1)) α β f x) (Bind.bind.{u1, u2} m (Monad.toHasBind.{u1, u2} m _inst_1) α β x (Function.comp.{succ u1, succ u1, succ u2} α β (m β) (Pure.pure.{u1, u2} m (Applicative.toHasPure.{u1, u2} m (Monad.toApplicative.{u1, u2} m _inst_1)) β) f))
but is expected to have type
  forall {m : Type.{u1}} {_inst_1 : Type.{u1}} (_inst_2 : Type.{u1} -> Type.{u2}) [α : Monad.{u1, u2} _inst_2] [β : LawfulMonad.{u1, u2} _inst_2 α] (f : m -> _inst_1) (x : _inst_2 m), Eq.{succ u2} (_inst_2 _inst_1) (Functor.map.{u1, u2} _inst_2 (Applicative.toFunctor.{u1, u2} _inst_2 (Monad.toApplicative.{u1, u2} _inst_2 α)) m _inst_1 f x) (Bind.bind.{u1, u2} _inst_2 (Monad.toBind.{u1, u2} _inst_2 α) m _inst_1 x (Function.comp.{succ u1, succ u1, succ u2} m _inst_1 (_inst_2 _inst_1) (Pure.pure.{u1, u2} _inst_2 (Applicative.toPure.{u1, u2} _inst_2 (Monad.toApplicative.{u1, u2} _inst_2 α)) _inst_1) f))
Case conversion may be inaccurate. Consider using '#align map_eq_bind_pure_comp map_eq_bind_pure_compₓ'. -/
@[monad_norm]
theorem map_eq_bind_pure_comp (m : Type u → Type v) [Monad m] [LawfulMonad m] {α β : Type u}
    (f : α → β) (x : m α) : f <$> x = x >>= pure ∘ f := by rw [bind_pure_comp_eq_map]
#align map_eq_bind_pure_comp map_eq_bind_pure_comp

/- warning: state_t.eval -> StateT.eval is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Functor.{u1, u2} m] {σ : Type.{u1}} {α : Type.{u1}}, (StateTₓ.{u1, u2} σ m α) -> σ -> (m α)
but is expected to have type
  forall {m : Type.{u1}} {_inst_1 : Type.{u1}} {σ : Type.{u1} -> Type.{u2}} [α : Functor.{u1, u2} σ], (StateT.{u1, u2} m σ _inst_1) -> m -> (σ _inst_1)
Case conversion may be inaccurate. Consider using '#align state_t.eval StateT.evalₓ'. -/
/-- run a `state_t` program and discard the final state -/
def StateT.eval {m : Type u → Type v} [Functor m] {σ α} (cmd : StateT σ m α) (s : σ) : m α :=
  Prod.fst <$> cmd.run s
#align state_t.eval StateT.eval

universe u₀ u₁ v₀ v₁

/- warning: state_t.equiv -> StateT.equiv is a dubious translation:
lean 3 declaration is
  forall {m₁ : Type.{u1} -> Type.{u3}} {m₂ : Type.{u2} -> Type.{u4}} {α₁ : Type.{u1}} {σ₁ : Type.{u1}} {α₂ : Type.{u2}} {σ₂ : Type.{u2}}, (Equiv.{max (succ u1) (succ u3), max (succ u2) (succ u4)} (σ₁ -> (m₁ (Prod.{u1, u1} α₁ σ₁))) (σ₂ -> (m₂ (Prod.{u2, u2} α₂ σ₂)))) -> (Equiv.{succ (max u1 u3), succ (max u2 u4)} (StateTₓ.{u1, u3} σ₁ m₁ α₁) (StateTₓ.{u2, u4} σ₂ m₂ α₂))
but is expected to have type
  forall {m₁ : Type.{u1}} {m₂ : Type.{u1}} {α₁ : Type.{u3}} {σ₁ : Type.{u3}} {α₂ : Type.{u1} -> Type.{u2}} {σ₂ : Type.{u3} -> Type.{u4}}, (Equiv.{max (succ u2) (succ u1), max (succ u4) (succ u3)} (m₁ -> (α₂ (Prod.{u1, u1} m₂ m₁))) (α₁ -> (σ₂ (Prod.{u3, u3} σ₁ α₁)))) -> (Equiv.{max (succ u2) (succ u1), max (succ u4) (succ u3)} (StateT.{u1, u2} m₁ α₂ m₂) (StateT.{u3, u4} α₁ σ₂ σ₁))
Case conversion may be inaccurate. Consider using '#align state_t.equiv StateT.equivₓ'. -/
/-- reduce the equivalence between two state monads to the equivalence between
their respective function spaces -/
def StateT.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁} {α₁ σ₁ : Type u₀}
    {α₂ σ₂ : Type u₁} (F : (σ₁ → m₁ (α₁ × σ₁)) ≃ (σ₂ → m₂ (α₂ × σ₂))) :
    StateT σ₁ m₁ α₁ ≃ StateT σ₂ m₂ α₂
    where
  toFun := fun ⟨f⟩ => ⟨F f⟩
  invFun := fun ⟨f⟩ => ⟨F.symm f⟩
  left_inv := fun ⟨f⟩ => congr_arg StateT.mk <| F.left_inv _
  right_inv := fun ⟨f⟩ => congr_arg StateT.mk <| F.right_inv _
#align state_t.equiv StateT.equiv

/- warning: reader_t.equiv -> ReaderT.equiv is a dubious translation:
lean 3 declaration is
  forall {m₁ : Type.{u1} -> Type.{u3}} {m₂ : Type.{u2} -> Type.{u4}} {α₁ : Type.{u1}} {ρ₁ : Type.{u1}} {α₂ : Type.{u2}} {ρ₂ : Type.{u2}}, (Equiv.{max (succ u1) (succ u3), max (succ u2) (succ u4)} (ρ₁ -> (m₁ α₁)) (ρ₂ -> (m₂ α₂))) -> (Equiv.{succ (max u1 u3), succ (max u2 u4)} (ReaderTₓ.{u1, u3} ρ₁ m₁ α₁) (ReaderTₓ.{u2, u4} ρ₂ m₂ α₂))
but is expected to have type
  forall {m₁ : Type.{u1}} {m₂ : Type.{u1}} {α₁ : Type.{u3}} {ρ₁ : Type.{u3}} {α₂ : Type.{u1} -> Type.{u2}} {ρ₂ : Type.{u3} -> Type.{u4}}, (Equiv.{max (succ u2) (succ u1), max (succ u4) (succ u3)} (m₁ -> (α₂ m₂)) (α₁ -> (ρ₂ ρ₁))) -> (Equiv.{max (succ u2) (succ u1), max (succ u4) (succ u3)} (ReaderT.{u1, u2} m₁ α₂ m₂) (ReaderT.{u3, u4} α₁ ρ₂ ρ₁))
Case conversion may be inaccurate. Consider using '#align reader_t.equiv ReaderT.equivₓ'. -/
/-- reduce the equivalence between two reader monads to the equivalence between
their respective function spaces -/
def ReaderT.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁} {α₁ ρ₁ : Type u₀}
    {α₂ ρ₂ : Type u₁} (F : (ρ₁ → m₁ α₁) ≃ (ρ₂ → m₂ α₂)) : ReaderT ρ₁ m₁ α₁ ≃ ReaderT ρ₂ m₂ α₂
    where
  toFun := fun ⟨f⟩ => ⟨F f⟩
  invFun := fun ⟨f⟩ => ⟨F.symm f⟩
  left_inv := fun ⟨f⟩ => congr_arg ReaderT.mk <| F.left_inv _
  right_inv := fun ⟨f⟩ => congr_arg ReaderT.mk <| F.right_inv _
#align reader_t.equiv ReaderT.equiv

