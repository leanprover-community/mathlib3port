import Mathbin.Data.Matrix.Basis
import Mathbin.RingTheory.TensorProduct

/-!
We show `matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R)`.
-/


universe u v w

open_locale TensorProduct

open_locale BigOperators

open TensorProduct

open Algebra.TensorProduct

open Matrix

variable {R : Type u} [CommSemiringₓ R]

variable {A : Type v} [Semiringₓ A] [Algebra R A]

variable {n : Type w}

variable (R A n)

namespace matrixEquivTensor

/-- 
(Implementation detail).
The bare function underlying `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`, on pure tensors.
-/
def to_fun (a : A) (m : Matrix n n R) : Matrix n n A := fun i j => a*algebraMap R A (m i j)

/-- 
(Implementation detail).
The function underlying `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`,
as an `R`-linear map in the second tensor factor.
-/
def to_fun_right_linear (a : A) : Matrix n n R →ₗ[R] Matrix n n A :=
  { toFun := to_fun R A n a,
    map_add' := fun x y => by
      dsimp only [to_fun]
      ext
      simp [mul_addₓ],
    map_smul' := fun r x => by
      dsimp only [to_fun]
      ext
      simp only [Pi.smul_apply, RingHom.map_mul, Algebra.id.smul_eq_mul]
      dsimp
      rw [Algebra.smul_def r, ← _root_.mul_assoc, ← _root_.mul_assoc, Algebra.commutes] }

/-- 
(Implementation detail).
The function underlying `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`,
as an `R`-bilinear map.
-/
def to_fun_bilinear : A →ₗ[R] Matrix n n R →ₗ[R] Matrix n n A :=
  { toFun := to_fun_right_linear R A n,
    map_add' := fun x y => by
      ext
      simp [to_fun_right_linear, to_fun, add_mulₓ],
    map_smul' := fun r x => by
      ext
      simp [to_fun_right_linear, to_fun] }

/-- 
(Implementation detail).
The function underlying `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`,
as an `R`-linear map.
-/
def to_fun_linear : A ⊗[R] Matrix n n R →ₗ[R] Matrix n n A :=
  TensorProduct.lift (to_fun_bilinear R A n)

variable [DecidableEq n] [Fintype n]

/-- 
The function `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`, as an algebra homomorphism.
-/
def to_fun_alg_hom : A ⊗[R] Matrix n n R →ₐ[R] Matrix n n A :=
  alg_hom_of_linear_map_tensor_product (to_fun_linear R A n)
    (by
      intros
      ext
      simp_rw [to_fun_linear, to_fun_bilinear, lift.tmul]
      dsimp
      simp_rw [to_fun_right_linear]
      dsimp
      simp_rw [to_fun, Matrix.mul_mul_left, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, ← _root_.mul_assoc _ a₂ _,
        Algebra.commutes, _root_.mul_assoc a₂ _ _, ← Finset.mul_sum, RingHom.map_sum, RingHom.map_mul,
        _root_.mul_assoc])
    (by
      intros
      ext
      simp only [to_fun_linear, to_fun_bilinear, to_fun_right_linear, to_fun, Matrix.one_apply,
        algebra_map_matrix_apply, lift.tmul, LinearMap.coe_mk]
      split_ifs <;> simp )

@[simp]
theorem to_fun_alg_hom_apply (a : A) (m : Matrix n n R) :
    to_fun_alg_hom R A n (a ⊗ₜ m) = fun i j => a*algebraMap R A (m i j) := by
  simp [to_fun_alg_hom, alg_hom_of_linear_map_tensor_product, to_fun_linear]
  rfl

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "\n(Implementation detail.)\n\nThe bare function `matrix n n A → A ⊗[R] matrix n n R`.\n(We don't need to show that it's an algebra map, thankfully --- just that it's an inverse.)\n-/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `inv_fun [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`M] [":" (Term.app `Matrix [`n `n `A])] [] ")")]
   [(Term.typeSpec ":" (LinearAlgebra.TensorProduct.«term_⊗[_]_» `A " ⊗[" `R "] " (Term.app `Matrix [`n `n `R])))])
  (Command.declValSimple
   ":="
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] [":" («term_×_» `n "×" `n)]))
    ", "
    (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
     (Term.app `M [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2"))])
     " ⊗ₜ "
     (Term.app `std_basis_matrix [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2")) (numLit "1")])))
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] [":" («term_×_» `n "×" `n)]))
   ", "
   (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
    (Term.app `M [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2"))])
    " ⊗ₜ "
    (Term.app `std_basis_matrix [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2")) (numLit "1")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
   (Term.app `M [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2"))])
   " ⊗ₜ "
   (Term.app `std_basis_matrix [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2")) (numLit "1")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `std_basis_matrix [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2")) (numLit "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `p "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `p "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `std_basis_matrix
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
  (Term.app `M [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `p "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `p "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1022, (some 1023, term) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 100, (some 101, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    (Implementation detail.)
    
    The bare function `matrix n n A → A ⊗[R] matrix n n R`.
    (We don't need to show that it's an algebra map, thankfully --- just that it's an inverse.)
    -/
  def
    inv_fun
    ( M : Matrix n n A ) : A ⊗[ R ] Matrix n n R
    := ∑ p : n × n , M p . 1 p . 2 ⊗ₜ std_basis_matrix p . 1 p . 2 1

@[simp]
theorem inv_fun_zero : inv_fun R A n 0 = 0 := by
  simp [inv_fun]

@[simp]
theorem inv_fun_add (M N : Matrix n n A) : inv_fun R A n (M+N) = inv_fun R A n M+inv_fun R A n N := by
  simp [inv_fun, add_tmul, Finset.sum_add_distrib]

@[simp]
theorem inv_fun_smul (a : A) (M : Matrix n n A) : (inv_fun R A n fun i j => a*M i j) = (a ⊗ₜ 1)*inv_fun R A n M := by
  simp [inv_fun, Finset.mul_sum]

@[simp]
theorem inv_fun_algebra_map (M : Matrix n n R) : (inv_fun R A n fun i j => algebraMap R A (M i j)) = 1 ⊗ₜ M := by
  dsimp [inv_fun]
  simp only [Algebra.algebra_map_eq_smul_one, smul_tmul, ← tmul_sum, mul_boole]
  congr
  conv_rhs => rw [matrix_eq_sum_std_basis M]
  convert Finset.sum_product
  simp

theorem right_inv (M : Matrix n n A) : (to_fun_alg_hom R A n) (inv_fun R A n M) = M := by
  simp only [inv_fun, AlgHom.map_sum, std_basis_matrix, apply_ite (⇑algebraMap R A), mul_boole, to_fun_alg_hom_apply,
    RingHom.map_zero, RingHom.map_one]
  convert Finset.sum_product
  apply matrix_eq_sum_std_basis

theorem left_inv (M : A ⊗[R] Matrix n n R) : inv_fun R A n (to_fun_alg_hom R A n M) = M := by
  apply TensorProduct.induction_on M
  ·
    simp
  ·
    intro a m
    simp
  ·
    intro x y hx hy
    simp [AlgHom.map_sum, hx, hy]

/-- 
(Implementation detail)

The equivalence, ignoring the algebra structure, `(A ⊗[R] matrix n n R) ≃ matrix n n A`.
-/
def Equivₓ : A ⊗[R] Matrix n n R ≃ Matrix n n A :=
  { toFun := to_fun_alg_hom R A n, invFun := inv_fun R A n, left_inv := left_inv R A n, right_inv := right_inv R A n }

end matrixEquivTensor

variable [Fintype n] [DecidableEq n]

/-- 
The `R`-algebra isomorphism `matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R)`.
-/
def matrixEquivTensor : Matrix n n A ≃ₐ[R] A ⊗[R] Matrix n n R :=
  AlgEquiv.symm { MatrixEquivTensor.toFunAlgHom R A n, MatrixEquivTensor.equiv R A n with }

open matrixEquivTensor

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `matrix_equiv_tensor_apply [])
  (Command.declSig
   [(Term.explicitBinder "(" [`M] [":" (Term.app `Matrix [`n `n `A])] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `matrixEquivTensor [`R `A `n `M])
     "="
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] [":" («term_×_» `n "×" `n)]))
      ", "
      (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
       (Term.app `M [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2"))])
       " ⊗ₜ "
       (Term.app
        `std_basis_matrix
        [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2")) (numLit "1")]))))))
  (Command.declValSimple ":=" `rfl [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app `matrixEquivTensor [`R `A `n `M])
   "="
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] [":" («term_×_» `n "×" `n)]))
    ", "
    (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
     (Term.app `M [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2"))])
     " ⊗ₜ "
     (Term.app `std_basis_matrix [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2")) (numLit "1")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] [":" («term_×_» `n "×" `n)]))
   ", "
   (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
    (Term.app `M [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2"))])
    " ⊗ₜ "
    (Term.app `std_basis_matrix [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2")) (numLit "1")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
   (Term.app `M [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2"))])
   " ⊗ₜ "
   (Term.app `std_basis_matrix [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2")) (numLit "1")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `std_basis_matrix [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2")) (numLit "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `p "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `p "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `std_basis_matrix
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
  (Term.app `M [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `p "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `p "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1022, (some 1023, term) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 100, (some 101, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    matrix_equiv_tensor_apply
    ( M : Matrix n n A ) : matrixEquivTensor R A n M = ∑ p : n × n , M p . 1 p . 2 ⊗ₜ std_basis_matrix p . 1 p . 2 1
    := rfl

@[simp]
theorem matrix_equiv_tensor_apply_std_basis (i j : n) (x : A) :
    matrixEquivTensor R A n (std_basis_matrix i j x) = x ⊗ₜ std_basis_matrix i j 1 := by
  have t : ∀ p : n × n, i = p.1 ∧ j = p.2 ↔ p = (i, j) := by
    tidy
  simp [ite_tmul, t, std_basis_matrix]

@[simp]
theorem matrix_equiv_tensor_apply_symm (a : A) (M : Matrix n n R) :
    (matrixEquivTensor R A n).symm (a ⊗ₜ M) = fun i j => a*algebraMap R A (M i j) := by
  simp [matrixEquivTensor, to_fun_alg_hom, alg_hom_of_linear_map_tensor_product, to_fun_linear]
  rfl

