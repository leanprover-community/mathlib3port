/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Algebra.Expr
import Data.Matrix.Reflection

#align_import data.matrix.auto from "leanprover-community/mathlib"@"08b081ea92d80e3a41f899eea36ef6d56e0f1db0"

/-! # Automatically generated lemmas for working with concrete matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains "magic" lemmas which autogenerate to the correct size of matrix. For instance,
`matrix.of_mul_of_fin` can be used as:
```lean
example {α} [add_comm_monoid α] [has_mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
  !![a₁₁, a₁₂;
     a₂₁, a₂₂] ⬝ !![b₁₁, b₁₂;
                    b₂₁, b₂₂] = !![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂;
                                   a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂] :=
begin
  rw of_mul_of_fin,
end
```

## Main results

* `matrix.fin_eta`
* `matrix.of_mul_of_fin`

-/


/-- Like `list.mmap` but for a vector. -/
def Fin.mmap {α} {n : ℕ} {m : Type _ → Type _} [Monad m] (f : Fin n → m α) : m (Fin n → α) :=
  Vector.get <$> Vector.mmap f ⟨List.finRange n, List.length_finRange _⟩
#align fin.mmap Fin.mmap

namespace Matrix

section FinEta

/- ././././Mathport/Syntax/Translate/Expr.lean:338:4: warning: unsupported (TODO): `[tacs] -/
-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Prove a statement of the form `∀ A : matrix m n α, A = !![A 0 0, ...]`.
      Returns the type of this statement and its proof. -/
    unsafe
  def
    fin_eta.prove
    ( m n : ℕ ) : tactic ( expr × expr )
    :=
      do
        let u ← tactic.mk_meta_univ
          let α ← tactic.mk_local' `α BinderInfo.implicit ( expr.sort u . succ )
          let
            A
              ←
              tactic.mk_local'
                `A
                  BinderInfo.default
                  (
                    expr.const
                      `matrix
                        [ level.zero , level.zero , u ]
                        q( Fin $ ( q( m ) ) )
                        q( Fin $ ( q( n ) ) )
                        α
                    )
          let entries ( i : Fin m ) ( j : Fin n ) := A q( i ) q( j )
          let
            entry_vals := pi_fin.to_pexpr fun i => pi_fin.to_pexpr fun j => to_pexpr <| entries i j
          let
            A_eta := ` `( @ Matrix.of ( Fin $ ( q( m ) ) ) ( Fin $ ( q( n ) ) ) _ ) . app entry_vals
          let A_eq ← tactic.to_expr ` `( $ ( A ) = $ ( A_eta ) )
          let t ← tactic.pis [ α , A ] A_eq
          let ( ( ) , pr ) ← tactic.solve_aux t sorry
          pure ( t , pr )
#align matrix.fin_eta.prove matrix.fin_eta.prove

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
/-- Helper tactic used as an `auto_param` for `matrix.fin_eta` -/ unsafe
  def
    fin_eta.derive
    : tactic Unit
    :=
      do
        let target @ q( $ ( A' ) = $ ( A_eta ) ) ← tactic.target
          let
            ( expr.const `matrix ls , [ q( Fin $ ( m ) ) , q( Fin $ ( n ) ) , α ] )
              ←
              expr.get_app_fn_args <$> tactic.infer_type A'
          let
            some ( m , n )
              ←
              pure ( Prod.mk <$> m . toNat <*> n . toNat )
              | throwError "Dimensions { ( ← m ) } { ← n } are not numerals"
          let ( t , pr ) ← matrix.fin_eta.prove m n
          tactic.unify target ( t [ α , A' ] )
          tactic.exact ( pr α A' )
#align matrix.fin_eta.derive matrix.fin_eta.derive

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic matrix.fin_eta.derive -/
/-- This lemma expands `A` into `!![A 0 0, ...]`. -/
theorem fin_eta {α} {m n : ℕ} (A : Matrix (Fin m) (Fin n) α)
    {«!![A 0 0, ...]» : Matrix (Fin m) (Fin n) α}
    (h : A = «!![A 0 0, ...]» := by
      run_tac
        matrix.fin_eta.derive) :
    A = «!![A 0 0, ...]» :=
  h
#align matrix.fin_eta Matrix.fin_eta

example : True := by
  let B : Matrix (Fin 20) (Fin 20) ℕ := 0
  have := Matrix.fin_eta B
  -- 400 coefficients, but very fast
  have : B = B := by rw [this]
  trivial

end FinEta

section OfMulOfFin

/-- Choose a name suffix for a matrix index -/
private def name_suffix {m n : ℕ} : Fin m → Fin n → String :=
  let chars := "₀₁₂₃₄₅₆₇₈₉".data
  if h : m ≤ 10 ∧ n ≤ 10 then fun i j =>
    [chars.nthLe i (i.IProp.trans_le h.1), chars.nthLe j (j.IProp.trans_le h.2)].asString
  else fun i j => "_" ++ toString i ++ "_" ++ toString j

/-- `pi_fin.to_pexpr` but for matrices -/
unsafe def fin_to_pexpr {m n : ℕ} (A : Matrix (Fin m) (Fin n) pexpr) : pexpr :=
  ``(@Matrix.of (Fin $(q(m))) (Fin $(q(n))) _).app <|
    pi_fin.to_pexpr fun i : Fin m => pi_fin.to_pexpr fun j : Fin n => A i j
#align matrix.fin_to_pexpr matrix.fin_to_pexpr

/-- This statement is defeq to `of_mul_of_fin`, but syntactically worse-/
theorem of_hMul_of_fin_aux (l m n : ℕ) ⦃α⦄ [Mul α] [AddCommMonoid α] :
    Forall fun A : Matrix (Fin l) (Fin m) α =>
      Forall fun B : Matrix (Fin m) (Fin n) α => A.mul B = A.mulᵣ B :=
  by simp_rw [forall_iff, mulᵣ_eq, eq_self_iff_true, forall_const]
#align matrix.of_mul_of_fin_aux Matrix.of_hMul_of_fin_aux

/-- Prove a statement of the form
```
∀ α [has_mul α] [add_comm_monoid α] (a₁₁ ... aₗₘ b₁₁ ... bₘₙ : α),
   !![a₁₁ ⋱ aₗₘ] ⬝ !![b₁₁ ⋱ bₘₙ] = !![⋱]
```
Returns the type of this statement and its proof. -/
unsafe def of_mul_of_fin.prove (l m n : ℕ) : tactic (expr × expr) := do
  let u
    ←-- create all the binders, one for each coefficient
      tactic.mk_meta_univ
  let α ← tactic.mk_local' `α BinderInfo.implicit (expr.sort u.succ)
  let has_mul_α ← tactic.mk_app `has_mul [α] >>= tactic.mk_local' `_inst_1 BinderInfo.inst_implicit
  let add_comm_monoid_α ←
    tactic.mk_app `add_comm_monoid [α] >>= tactic.mk_local' `_inst_2 BinderInfo.inst_implicit
  let a ←
    Fin.mmap fun i : Fin l =>
        Fin.mmap fun j : Fin m =>
          tactic.mk_local' (`a.appendSuffix (nameSuffix i j)) BinderInfo.default α
  let b ←
    Fin.mmap fun i : Fin m =>
        Fin.mmap fun j : Fin n =>
          tactic.mk_local' (`b.appendSuffix (nameSuffix i j)) BinderInfo.default α
  let a_flat := (List.finRange l).bind fun i => (List.finRange m).map fun j => a i j
  let b_flat := (List.finRange m).bind fun i => (List.finRange n).map fun j => b i j
  let args := [α, has_mul_α, add_comm_monoid_α] ++ a_flat ++ b_flat
  let-- build the matrices out of the coefficients
  A := matrix.fin_to_pexpr (Matrix.map a to_pexpr)
  let B := matrix.fin_to_pexpr (Matrix.map b to_pexpr)
  let t
    ←-- get an instance cache holding all the instances needed for matrix multiplication. There must
        -- be a better way to do this.
        tactic.mk_instance_cache
        α
  let has_add_α ←
    tactic.mk_app `has_add [α] >>= fun t =>
        Prod.snd <$>
          @tactic.solve_aux Unit t do
            let tmp2 ← tactic.pose `_inst_2' none add_comm_monoid_α
            tactic.reset_instance_cache
            tactic.apply_instance
  let has_zero_α ←
    tactic.mk_app `has_zero [α] >>= fun t =>
        Prod.snd <$>
          @tactic.solve_aux Unit t do
            let tmp2 ← tactic.pose `_inst_2' none add_comm_monoid_α
            tactic.reset_instance_cache
            tactic.apply_instance
  let t :=
    { t with
      inst :=
        [(`has_mul, has_mul_α), (`has_add, has_add_α), (`has_zero, has_zero_α),
              (`add_comm_monoid, add_comm_monoid_α)].foldl
          (fun n x => n.insert x.1 x.2) t.inst }
  let-- clever trick: create algebraic instances on `expr` so that we can use `matrix.mul` or
    -- `matrix.mulᵣ` to build the expression we want to end up with. It doesn't matter which we pick,
    -- but the typeclasses are easier to create for the latter.
    (t, has_mul_αe)
    ← Expr.instMul t
  let (t, has_add_αe) ← Expr.instAdd t
  let (t, has_zero_αe) ← Expr.instZero t
  let ab := @Matrix.mulᵣ _ _ _ _ has_mul_αe has_add_αe has_zero_αe a b
  let AB := matrix.fin_to_pexpr (Matrix.map ab to_pexpr)
  let A_eq
    ←-- State and prove the equality, noting the RHS is defeq to `mulᵣ A B`.
        tactic.to_expr
        ``(@HMul.hMul _ _ _ _ _ $(has_mul_α) $(add_comm_monoid_α) $(A) $(B) = $(AB))
  let t ← tactic.pis args A_eq
  let pr := (expr.const `matrix.of_mul_of_fin_aux [u]).mk_app [q(l), q(m), q(n)]
  let-- This seems to create a metavariable then assign it, which ensures `pr` carries the right type.
    ((), pr)
    ← tactic.solve_aux t <| tactic.exact pr
  pure (t, pr)
#align matrix.of_mul_of_fin.prove matrix.of_mul_of_fin.prove

open scoped Matrix

/-- Helper tactic used as an `auto_param` for `matrix.of_mul_of_fin` -/
unsafe def of_mul_of_fin.derive : tactic Unit := do
  let target@q(@HMul.hMul (Fin $(l)) (Fin $(m)) (Fin $(n)) $(α) $(_) $(i1) $(i2) $(A) $(B) = $(AB))
    ← tactic.target
  let some (l, m, n) ← pure (Prod.mk <$> l.toNat <*> (Prod.mk <$> m.toNat <*> n.toNat)) |
    throwError "Dimensions {(← l)}, {(← m)} {← n} are not numerals"
  let (t, pr) ← of_mul_of_fin.prove l m n
  tactic.apply (pr α i1 i2) { }
  tactic.done
#align matrix.of_mul_of_fin.derive matrix.of_mul_of_fin.derive

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic of_mul_of_fin.derive -/
-- TODO: should we be extracting the coefficients manually so we can do a full invocation as
-- something like:
--   tactic.unify target (t.instantiate_pis [α, A']),
--   tactic.exact (pr α A')
/-- This lemma assumes that `a_coeffs` and `b_coeffs` refer to expressions of the form
`![![x₀₀, x₀₁], ![x₁₀, x₁₁]]`. It then uses an `auto_param` to populate `ab_coeffs` with an
expression of the same form, containing the appropriate expressions in terms of `+`, `*`, `aᵢⱼ`,
and `bⱼₖ`. -/
theorem of_hMul_of_fin {α} [Mul α] [AddCommMonoid α] {l m n : ℕ} {a_coeffs : Fin l → Fin m → α}
    {b_coeffs : Fin m → Fin n → α} {ab_coeffs : Fin l → Fin n → α}
    (h : of a_coeffs ⬝ of b_coeffs = of ab_coeffs := by
      run_tac
        of_mul_of_fin.derive) :
    of a_coeffs ⬝ of b_coeffs = of ab_coeffs :=
  h
#align matrix.of_mul_of_fin Matrix.of_hMul_of_fin

end OfMulOfFin

end Matrix

