/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Sébastien Gouëzel, Heather Macbeth

! This file was ported from Lean 3 source module analysis.inner_product_space.pi_L2
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Projection
import Mathbin.Analysis.NormedSpace.PiLp
import Mathbin.LinearAlgebra.FiniteDimensional
import Mathbin.LinearAlgebra.UnitaryGroup

/-!
# `L²` inner product space structure on finite products of inner product spaces

The `L²` norm on a finite product of inner product spaces is compatible with an inner product
$$
\langle x, y\rangle = \sum \langle x_i, y_i \rangle.
$$
This is recorded in this file as an inner product space instance on `pi_Lp 2`.

This file develops the notion of a finite dimensional Hilbert space over `𝕜 = ℂ, ℝ`, referred to as
`E`. We define an `orthonormal_basis 𝕜 ι E` as a linear isometric equivalence
between `E` and `euclidean_space 𝕜 ι`. Then `std_orthonormal_basis` shows that such an equivalence
always exists if `E` is finite dimensional. We provide language for converting between a basis
that is orthonormal and an orthonormal basis (e.g. `basis.to_orthonormal_basis`). We show that
orthonormal bases for each summand in a direct sum of spaces can be combined into an orthonormal
basis for the the whole sum in `direct_sum.submodule_is_internal.subordinate_orthonormal_basis`. In
the last section, various properties of matrices are explored.

## Main definitions

- `euclidean_space 𝕜 n`: defined to be `pi_Lp 2 (n → 𝕜)` for any `fintype n`, i.e., the space
  from functions to `n` to `𝕜` with the `L²` norm. We register several instances on it (notably
  that it is a finite-dimensional inner product space).

- `orthonormal_basis 𝕜 ι`: defined to be an isometry to Euclidean space from a given
  finite-dimensional innner product space, `E ≃ₗᵢ[𝕜] euclidean_space 𝕜 ι`.

- `basis.to_orthonormal_basis`: constructs an `orthonormal_basis` for a finite-dimensional
  Euclidean space from a `basis` which is `orthonormal`.

- `orthonormal.exists_orthonormal_basis_extension`: provides an existential result of an
  `orthonormal_basis` extending a given orthonormal set

- `exists_orthonormal_basis`: provides an orthonormal basis on a finite dimensional vector space

- `std_orthonormal_basis`: provides an arbitrarily-chosen `orthonormal_basis` of a given finite
  dimensional inner product space

For consequences in infinite dimension (Hilbert bases, etc.), see the file
`analysis.inner_product_space.l2_space`.

-/


open Real Set Filter IsROrC Submodule Function

open BigOperators uniformity TopologicalSpace Nnreal Ennreal ComplexConjugate DirectSum

noncomputable section

variable {ι : Type _} {ι' : Type _}

variable {𝕜 : Type _} [IsROrC 𝕜] {E : Type _} [InnerProductSpace 𝕜 E]

variable {E' : Type _} [InnerProductSpace 𝕜 E']

variable {F : Type _} [InnerProductSpace ℝ F]

variable {F' : Type _} [InnerProductSpace ℝ F']

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-
 If `ι` is a finite type and each space `f i`, `i : ι`, is an inner product space,
then `Π i, f i` is an inner product space as well. Since `Π i, f i` is endowed with the sup norm,
we use instead `pi_Lp 2 f` for the product space, which is endowed with the `L^2` norm.
-/
instance PiLp.innerProductSpace {ι : Type _} [Fintype ι] (f : ι → Type _)
    [∀ i, InnerProductSpace 𝕜 (f i)] : InnerProductSpace 𝕜 (PiLp 2 f)
    where
  toNormedAddCommGroup := inferInstance
  inner x y := ∑ i, inner (x i) (y i)
  norm_sq_eq_inner x := by
    simp only [PiLp.norm_sq_eq_of_L2, AddMonoidHom.map_sum, ← norm_sq_eq_inner, one_div]
  conj_sym := by
    intro x y
    unfold inner
    rw [RingHom.map_sum]
    apply Finset.sum_congr rfl
    rintro z -
    apply inner_conj_sym
  add_left x y z :=
    show (∑ i, inner (x i + y i) (z i)) = (∑ i, inner (x i) (z i)) + ∑ i, inner (y i) (z i) by
      simp only [inner_add_left, Finset.sum_add_distrib]
  smul_left x y r :=
    show (∑ i : ι, inner (r • x i) (y i)) = conj r * ∑ i, inner (x i) (y i) by
      simp only [Finset.mul_sum, inner_smul_left]
#align pi_Lp.inner_product_space PiLp.innerProductSpace

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
      (Command.declId `PiLp.inner_apply [])
      (Command.declSig
       [(Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.instBinder "[" [] (Term.app `Fintype [`ι]) "]")
        (Term.implicitBinder
         "{"
         [`f]
         [":" (Term.arrow `ι "→" (Term.type "Type" [(Level.hole "_")]))]
         "}")
        (Term.instBinder
         "["
         []
         (Term.forall "∀" [`i] [] "," (Term.app `InnerProductSpace [`𝕜 (Term.app `f [`i])]))
         "]")
        (Term.explicitBinder "(" [`x `y] [":" (Term.app `PiLp [(num "2") `f])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" `x ", " `y "⟫")
         "="
         (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          ", "
          (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
           "⟪"
           (Term.app `x [`i])
           ", "
           (Term.app `y [`i])
           "⟫")))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" `x ", " `y "⟫")
       "="
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
         "⟪"
         (Term.app `x [`i])
         ", "
         (Term.app `y [`i])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       ", "
       (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
        "⟪"
        (Term.app `x [`i])
        ", "
        (Term.app `y [`i])
        "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
       "⟪"
       (Term.app `x [`i])
       ", "
       (Term.app `y [`i])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.PiL2.term⟪_,_⟫._@.Analysis.InnerProductSpace.PiL2._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    PiLp.inner_apply
    { ι : Type _ }
        [ Fintype ι ]
        { f : ι → Type _ }
        [ ∀ i , InnerProductSpace 𝕜 f i ]
        ( x y : PiLp 2 f )
      : ⟪ x , y ⟫ = ∑ i , ⟪ x i , y i ⟫
    := rfl
#align pi_Lp.inner_apply PiLp.inner_apply

/-- The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional
space use `euclidean_space 𝕜 (fin n)`. -/
@[reducible, nolint unused_arguments]
def EuclideanSpace (𝕜 : Type _) [IsROrC 𝕜] (n : Type _) [Fintype n] : Type _ :=
  PiLp 2 fun i : n => 𝕜
#align euclidean_space EuclideanSpace

theorem EuclideanSpace.nnnorm_eq {𝕜 : Type _} [IsROrC 𝕜] {n : Type _} [Fintype n]
    (x : EuclideanSpace 𝕜 n) : ‖x‖₊ = Nnreal.sqrt (∑ i, ‖x i‖₊ ^ 2) :=
  PiLp.nnnorm_eq_of_L2 x
#align euclidean_space.nnnorm_eq EuclideanSpace.nnnorm_eq

theorem EuclideanSpace.norm_eq {𝕜 : Type _} [IsROrC 𝕜] {n : Type _} [Fintype n]
    (x : EuclideanSpace 𝕜 n) : ‖x‖ = Real.sqrt (∑ i, ‖x i‖ ^ 2) := by
  simpa only [Real.coe_sqrt, Nnreal.coe_sum] using congr_arg (coe : ℝ≥0 → ℝ) x.nnnorm_eq
#align euclidean_space.norm_eq EuclideanSpace.norm_eq

theorem EuclideanSpace.dist_eq {𝕜 : Type _} [IsROrC 𝕜] {n : Type _} [Fintype n]
    (x y : EuclideanSpace 𝕜 n) : dist x y = (∑ i, dist (x i) (y i) ^ 2).sqrt :=
  (PiLp.dist_eq_of_L2 x y : _)
#align euclidean_space.dist_eq EuclideanSpace.dist_eq

theorem EuclideanSpace.nndist_eq {𝕜 : Type _} [IsROrC 𝕜] {n : Type _} [Fintype n]
    (x y : EuclideanSpace 𝕜 n) : nndist x y = (∑ i, nndist (x i) (y i) ^ 2).sqrt :=
  (PiLp.nndist_eq_of_L2 x y : _)
#align euclidean_space.nndist_eq EuclideanSpace.nndist_eq

theorem EuclideanSpace.edist_eq {𝕜 : Type _} [IsROrC 𝕜] {n : Type _} [Fintype n]
    (x y : EuclideanSpace 𝕜 n) : edist x y = (∑ i, edist (x i) (y i) ^ 2) ^ (1 / 2 : ℝ) :=
  (PiLp.edist_eq_of_L2 x y : _)
#align euclidean_space.edist_eq EuclideanSpace.edist_eq

variable [Fintype ι]

section

attribute [local reducible] PiLp

instance : FiniteDimensional 𝕜 (EuclideanSpace 𝕜 ι) := by infer_instance

instance : InnerProductSpace 𝕜 (EuclideanSpace 𝕜 ι) := by infer_instance

@[simp]
theorem finrank_euclidean_space :
    FiniteDimensional.finrank 𝕜 (EuclideanSpace 𝕜 ι) = Fintype.card ι := by simp
#align finrank_euclidean_space finrank_euclidean_space

theorem finrank_euclidean_space_fin {n : ℕ} :
    FiniteDimensional.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n := by simp
#align finrank_euclidean_space_fin finrank_euclidean_space_fin

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `EuclideanSpace.inner_eq_star_dot_product [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x `y] [":" (Term.app `EuclideanSpace [`𝕜 `ι])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" `x ", " `y "⟫")
         "="
         (Term.app
          `Matrix.dotProduct
          [(«term_<|_» `star "<|" (Term.app `PiLp.equiv [(Term.hole "_") (Term.hole "_") `x]))
           (Term.app `PiLp.equiv [(Term.hole "_") (Term.hole "_") `y])]))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" `x ", " `y "⟫")
       "="
       (Term.app
        `Matrix.dotProduct
        [(«term_<|_» `star "<|" (Term.app `PiLp.equiv [(Term.hole "_") (Term.hole "_") `x]))
         (Term.app `PiLp.equiv [(Term.hole "_") (Term.hole "_") `y])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Matrix.dotProduct
       [(«term_<|_» `star "<|" (Term.app `PiLp.equiv [(Term.hole "_") (Term.hole "_") `x]))
        (Term.app `PiLp.equiv [(Term.hole "_") (Term.hole "_") `y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `PiLp.equiv [(Term.hole "_") (Term.hole "_") `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PiLp.equiv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `PiLp.equiv [(Term.hole "_") (Term.hole "_") `y])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_» `star "<|" (Term.app `PiLp.equiv [(Term.hole "_") (Term.hole "_") `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `PiLp.equiv [(Term.hole "_") (Term.hole "_") `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PiLp.equiv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `star
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» `star "<|" (Term.app `PiLp.equiv [(Term.hole "_") (Term.hole "_") `x]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Matrix.dotProduct
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" `x ", " `y "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.PiL2.term⟪_,_⟫._@.Analysis.InnerProductSpace.PiL2._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  EuclideanSpace.inner_eq_star_dot_product
  ( x y : EuclideanSpace 𝕜 ι )
    : ⟪ x , y ⟫ = Matrix.dotProduct star <| PiLp.equiv _ _ x PiLp.equiv _ _ y
  := rfl
#align euclidean_space.inner_eq_star_dot_product EuclideanSpace.inner_eq_star_dot_product

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A finite, mutually orthogonal family of subspaces of `E`, which span `E`, induce an isometry\nfrom `E` to `pi_Lp 2` of the subspaces equipped with the `L2` inner product. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `DirectSum.IsInternal.isometryL2OfOrthogonalFamily [])
      (Command.optDeclSig
       [(Term.instBinder "[" [] (Term.app `DecidableEq [`ι]) "]")
        (Term.implicitBinder "{" [`V] [":" (Term.arrow `ι "→" (Term.app `Submodule [`𝕜 `E]))] "}")
        (Term.explicitBinder "(" [`hV] [":" (Term.app `DirectSum.IsInternal [`V])] [] ")")
        (Term.explicitBinder
         "("
         [`hV']
         [":"
          (Term.app
           (Term.explicit "@" `OrthogonalFamily)
           [`𝕜
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.app `V [`i])))
            (Term.hole "_")
            (Term.fun
             "fun"
             (Term.basicFun [`i] [] "=>" (Term.proj (Term.app `V [`i]) "." `subtypeₗᵢ)))])]
         []
         ")")]
       [(Term.typeSpec
         ":"
         (Analysis.NormedSpace.LinearIsometry.«term_≃ₗᵢ[_]_»
          `E
          " ≃ₗᵢ["
          `𝕜
          "] "
          (Term.app
           `PiLp
           [(num "2") (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.app `V [`i])))])))])
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `e₁
              []
              []
              ":="
              (Term.app
               `DirectSum.linearEquivFunOnFintype
               [`𝕜 `ι (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.app `V [`i])))]))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `e₂
              []
              []
              ":="
              (Term.app `LinearEquiv.ofBijective [(Term.app `DirectSum.coeLinearMap [`V]) `hV]))))
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             (Term.proj (Term.app `e₂.symm.trans [`e₁]) "." `isometryOfInner)
             [(Term.hole "_")]))
           []
           (Tactic.tacticSuffices_
            "suffices"
            (Term.sufficesDecl
             []
             (Term.forall
              "∀"
              [`v `w]
              []
              ","
              («term_=_»
               (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" `v ", " `w "⟫")
               "="
               (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
                "⟪"
                (Term.app `e₂ [(Term.app `e₁.symm [`v])])
                ", "
                (Term.app `e₂ [(Term.app `e₁.symm [`w])])
                "⟫")))
             (Term.byTactic'
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`v₀ `w₀])
                 []
                 (Tactic.«tactic_<;>_»
                  (convert
                   "convert"
                   []
                   (Term.app
                    `this
                    [(Term.app `e₁ [(Term.app `e₂.symm [`v₀])])
                     (Term.app `e₁ [(Term.app `e₂.symm [`w₀])])])
                   [])
                  "<;>"
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `LinearEquiv.symm_apply_apply)
                     ","
                     (Tactic.simpLemma [] [] `LinearEquiv.apply_symm_apply)]
                    "]"]
                   []))])))))
           []
           (Tactic.intro "intro" [`v `w])
           []
           (Mathlib.Tactic.tacticTrans___
            "trans"
            [(Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
              "⟪"
              (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
               ", "
               (Term.app (Term.proj (Term.app `V [`i]) "." `subtypeₗᵢ) [(Term.app `v [`i])]))
              ", "
              (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
               ", "
               (Term.app (Term.proj (Term.app `V [`i]) "." `subtypeₗᵢ) [(Term.app `w [`i])]))
              "⟫")])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `sum_inner)
                ","
                (Tactic.simpLemma [] [] `hV'.inner_right_fintype)
                ","
                (Tactic.simpLemma [] [] `PiLp.inner_apply)]
               "]"]
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.«tactic_<;>_»
              (Tactic.congr "congr" [])
              "<;>"
              (Tactic.simp "simp" [] [] [] [] []))])])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `e₁
             []
             []
             ":="
             (Term.app
              `DirectSum.linearEquivFunOnFintype
              [`𝕜 `ι (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.app `V [`i])))]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `e₂
             []
             []
             ":="
             (Term.app `LinearEquiv.ofBijective [(Term.app `DirectSum.coeLinearMap [`V]) `hV]))))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            (Term.proj (Term.app `e₂.symm.trans [`e₁]) "." `isometryOfInner)
            [(Term.hole "_")]))
          []
          (Tactic.tacticSuffices_
           "suffices"
           (Term.sufficesDecl
            []
            (Term.forall
             "∀"
             [`v `w]
             []
             ","
             («term_=_»
              (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" `v ", " `w "⟫")
              "="
              (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
               "⟪"
               (Term.app `e₂ [(Term.app `e₁.symm [`v])])
               ", "
               (Term.app `e₂ [(Term.app `e₁.symm [`w])])
               "⟫")))
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.intro "intro" [`v₀ `w₀])
                []
                (Tactic.«tactic_<;>_»
                 (convert
                  "convert"
                  []
                  (Term.app
                   `this
                   [(Term.app `e₁ [(Term.app `e₂.symm [`v₀])])
                    (Term.app `e₁ [(Term.app `e₂.symm [`w₀])])])
                  [])
                 "<;>"
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `LinearEquiv.symm_apply_apply)
                    ","
                    (Tactic.simpLemma [] [] `LinearEquiv.apply_symm_apply)]
                   "]"]
                  []))])))))
          []
          (Tactic.intro "intro" [`v `w])
          []
          (Mathlib.Tactic.tacticTrans___
           "trans"
           [(Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
             "⟪"
             (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
              ", "
              (Term.app (Term.proj (Term.app `V [`i]) "." `subtypeₗᵢ) [(Term.app `v [`i])]))
             ", "
             (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
              ", "
              (Term.app (Term.proj (Term.app `V [`i]) "." `subtypeₗᵢ) [(Term.app `w [`i])]))
             "⟫")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `sum_inner)
               ","
               (Tactic.simpLemma [] [] `hV'.inner_right_fintype)
               ","
               (Tactic.simpLemma [] [] `PiLp.inner_apply)]
              "]"]
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.«tactic_<;>_»
             (Tactic.congr "congr" [])
             "<;>"
             (Tactic.simp "simp" [] [] [] [] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.«tactic_<;>_» (Tactic.congr "congr" []) "<;>" (Tactic.simp "simp" [] [] [] [] []))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_» (Tactic.congr "congr" []) "<;>" (Tactic.simp "simp" [] [] [] [] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `sum_inner)
           ","
           (Tactic.simpLemma [] [] `hV'.inner_right_fintype)
           ","
           (Tactic.simpLemma [] [] `PiLp.inner_apply)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `sum_inner)
         ","
         (Tactic.simpLemma [] [] `hV'.inner_right_fintype)
         ","
         (Tactic.simpLemma [] [] `PiLp.inner_apply)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PiLp.inner_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hV'.inner_right_fintype
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sum_inner
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticTrans___
       "trans"
       [(Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
         "⟪"
         (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          ", "
          (Term.app (Term.proj (Term.app `V [`i]) "." `subtypeₗᵢ) [(Term.app `v [`i])]))
         ", "
         (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          ", "
          (Term.app (Term.proj (Term.app `V [`i]) "." `subtypeₗᵢ) [(Term.app `w [`i])]))
         "⟫")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
       "⟪"
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        (Term.app (Term.proj (Term.app `V [`i]) "." `subtypeₗᵢ) [(Term.app `v [`i])]))
       ", "
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        (Term.app (Term.proj (Term.app `V [`i]) "." `subtypeₗᵢ) [(Term.app `w [`i])]))
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.PiL2.term⟪_,_⟫._@.Analysis.InnerProductSpace.PiL2._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    A finite, mutually orthogonal family of subspaces of `E`, which span `E`, induce an isometry
    from `E` to `pi_Lp 2` of the subspaces equipped with the `L2` inner product. -/
  def
    DirectSum.IsInternal.isometryL2OfOrthogonalFamily
    [ DecidableEq ι ]
        { V : ι → Submodule 𝕜 E }
        ( hV : DirectSum.IsInternal V )
        ( hV' : @ OrthogonalFamily 𝕜 _ _ _ _ fun i => V i _ fun i => V i . subtypeₗᵢ )
      : E ≃ₗᵢ[ 𝕜 ] PiLp 2 fun i => V i
    :=
      by
        let e₁ := DirectSum.linearEquivFunOnFintype 𝕜 ι fun i => V i
          let e₂ := LinearEquiv.ofBijective DirectSum.coeLinearMap V hV
          refine' e₂.symm.trans e₁ . isometryOfInner _
          suffices
            ∀ v w , ⟪ v , w ⟫ = ⟪ e₂ e₁.symm v , e₂ e₁.symm w ⟫
              by
                intro v₀ w₀
                  convert this e₁ e₂.symm v₀ e₁ e₂.symm w₀
                    <;>
                    simp only [ LinearEquiv.symm_apply_apply , LinearEquiv.apply_symm_apply ]
          intro v w
          trans ⟪ ∑ i , V i . subtypeₗᵢ v i , ∑ i , V i . subtypeₗᵢ w i ⟫
          · simp only [ sum_inner , hV'.inner_right_fintype , PiLp.inner_apply ]
          · congr <;> simp
#align
  direct_sum.is_internal.isometry_L2_of_orthogonal_family DirectSum.IsInternal.isometryL2OfOrthogonalFamily

@[simp]
theorem DirectSum.IsInternal.isometry_L2_of_orthogonal_family_symm_apply [DecidableEq ι]
    {V : ι → Submodule 𝕜 E} (hV : DirectSum.IsInternal V)
    (hV' : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => V i) _ fun i => (V i).subtypeₗᵢ)
    (w : PiLp 2 fun i => V i) : (hV.isometryL2OfOrthogonalFamily hV').symm w = ∑ i, (w i : E) := by
  classical
    let e₁ := DirectSum.linearEquivFunOnFintype 𝕜 ι fun i => V i
    let e₂ := LinearEquiv.ofBijective (DirectSum.coeLinearMap V) hV
    suffices ∀ v : ⨁ i, V i, e₂ v = ∑ i, e₁ v i by exact this (e₁.symm w)
    intro v
    simp [e₂, DirectSum.coeLinearMap, DirectSum.toModule, Dfinsupp.sum_add_hom_apply]
#align
  direct_sum.is_internal.isometry_L2_of_orthogonal_family_symm_apply DirectSum.IsInternal.isometry_L2_of_orthogonal_family_symm_apply

end

variable (ι 𝕜)

-- TODO : This should be generalized to `pi_Lp` with finite dimensional factors.
/-- `pi_Lp.linear_equiv` upgraded to a continuous linear map between `euclidean_space 𝕜 ι`
and `ι → 𝕜`. -/
@[simps]
def EuclideanSpace.equiv : EuclideanSpace 𝕜 ι ≃L[𝕜] ι → 𝕜 :=
  (PiLp.linearEquiv 2 𝕜 fun i : ι => 𝕜).toContinuousLinearEquiv
#align euclidean_space.equiv EuclideanSpace.equiv

variable {ι 𝕜}

-- TODO : This should be generalized to `pi_Lp`.
/-- The projection on the `i`-th coordinate of `euclidean_space 𝕜 ι`, as a linear map. -/
@[simps]
def EuclideanSpace.projₗ (i : ι) : EuclideanSpace 𝕜 ι →ₗ[𝕜] 𝕜 :=
  (LinearMap.proj i).comp (PiLp.linearEquiv 2 𝕜 fun i : ι => 𝕜 : EuclideanSpace 𝕜 ι →ₗ[𝕜] ι → 𝕜)
#align euclidean_space.projₗ EuclideanSpace.projₗ

-- TODO : This should be generalized to `pi_Lp`.
/-- The projection on the `i`-th coordinate of `euclidean_space 𝕜 ι`,
as a continuous linear map. -/
@[simps]
def EuclideanSpace.proj (i : ι) : EuclideanSpace 𝕜 ι →L[𝕜] 𝕜 :=
  ⟨EuclideanSpace.projₗ i, continuous_apply i⟩
#align euclidean_space.proj EuclideanSpace.proj

-- TODO : This should be generalized to `pi_Lp`.
/-- The vector given in euclidean space by being `1 : 𝕜` at coordinate `i : ι` and `0 : 𝕜` at
all other coordinates. -/
def EuclideanSpace.single [DecidableEq ι] (i : ι) (a : 𝕜) : EuclideanSpace 𝕜 ι :=
  (PiLp.equiv _ _).symm (Pi.single i a)
#align euclidean_space.single EuclideanSpace.single

@[simp]
theorem PiLp.equiv_single [DecidableEq ι] (i : ι) (a : 𝕜) :
    PiLp.equiv _ _ (EuclideanSpace.single i a) = Pi.single i a :=
  rfl
#align pi_Lp.equiv_single PiLp.equiv_single

@[simp]
theorem PiLp.equiv_symm_single [DecidableEq ι] (i : ι) (a : 𝕜) :
    (PiLp.equiv _ _).symm (Pi.single i a) = EuclideanSpace.single i a :=
  rfl
#align pi_Lp.equiv_symm_single PiLp.equiv_symm_single

@[simp]
theorem EuclideanSpace.single_apply [DecidableEq ι] (i : ι) (a : 𝕜) (j : ι) :
    (EuclideanSpace.single i a) j = ite (j = i) a 0 := by
  rw [EuclideanSpace.single, PiLp.equiv_symm_apply, ← Pi.single_apply i a j]
#align euclidean_space.single_apply EuclideanSpace.single_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `EuclideanSpace.inner_single_left [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `DecidableEq [`ι]) "]")
        (Term.explicitBinder "(" [`i] [":" `ι] [] ")")
        (Term.explicitBinder "(" [`a] [":" `𝕜] [] ")")
        (Term.explicitBinder "(" [`v] [":" (Term.app `EuclideanSpace [`𝕜 `ι])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
          "⟪"
          (Term.app `EuclideanSpace.single [`i (Term.typeAscription "(" `a ":" [`𝕜] ")")])
          ", "
          `v
          "⟫")
         "="
         («term_*_»
          (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`a])
          "*"
          (Term.app `v [`i])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma
               []
               []
               (Term.app `apply_ite [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")]))]
             "]"]
            [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma
              []
              []
              (Term.app `apply_ite [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")]))]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma
          []
          []
          (Term.app `apply_ite [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `apply_ite [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ComplexConjugate.Algebra.Star.Basic.star_ring_end', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ComplexConjugate.Algebra.Star.Basic.star_ring_end', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `apply_ite
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
        "⟪"
        (Term.app `EuclideanSpace.single [`i (Term.typeAscription "(" `a ":" [`𝕜] ")")])
        ", "
        `v
        "⟫")
       "="
       («term_*_»
        (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`a])
        "*"
        (Term.app `v [`i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`a])
       "*"
       (Term.app `v [`i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `v [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
       "⟪"
       (Term.app `EuclideanSpace.single [`i (Term.typeAscription "(" `a ":" [`𝕜] ")")])
       ", "
       `v
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.PiL2.term⟪_,_⟫._@.Analysis.InnerProductSpace.PiL2._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  EuclideanSpace.inner_single_left
  [ DecidableEq ι ] ( i : ι ) ( a : 𝕜 ) ( v : EuclideanSpace 𝕜 ι )
    : ⟪ EuclideanSpace.single i ( a : 𝕜 ) , v ⟫ = conj a * v i
  := by simp [ apply_ite conj ]
#align euclidean_space.inner_single_left EuclideanSpace.inner_single_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `EuclideanSpace.inner_single_right [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `DecidableEq [`ι]) "]")
        (Term.explicitBinder "(" [`i] [":" `ι] [] ")")
        (Term.explicitBinder "(" [`a] [":" `𝕜] [] ")")
        (Term.explicitBinder "(" [`v] [":" (Term.app `EuclideanSpace [`𝕜 `ι])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
          "⟪"
          `v
          ", "
          (Term.app `EuclideanSpace.single [`i (Term.typeAscription "(" `a ":" [`𝕜] ")")])
          "⟫")
         "="
         («term_*_»
          `a
          "*"
          (Term.app
           (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
           [(Term.app `v [`i])])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma
               []
               []
               (Term.app `apply_ite [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")]))
              ","
              (Tactic.simpLemma [] [] `mul_comm)]
             "]"]
            [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma
              []
              []
              (Term.app `apply_ite [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")]))
             ","
             (Tactic.simpLemma [] [] `mul_comm)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma
          []
          []
          (Term.app `apply_ite [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")]))
         ","
         (Tactic.simpLemma [] [] `mul_comm)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `apply_ite [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ComplexConjugate.Algebra.Star.Basic.star_ring_end', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ComplexConjugate.Algebra.Star.Basic.star_ring_end', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `apply_ite
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
        "⟪"
        `v
        ", "
        (Term.app `EuclideanSpace.single [`i (Term.typeAscription "(" `a ":" [`𝕜] ")")])
        "⟫")
       "="
       («term_*_»
        `a
        "*"
        (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [(Term.app `v [`i])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       `a
       "*"
       (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [(Term.app `v [`i])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [(Term.app `v [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `v [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `v [`i]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
       "⟪"
       `v
       ", "
       (Term.app `EuclideanSpace.single [`i (Term.typeAscription "(" `a ":" [`𝕜] ")")])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.PiL2.term⟪_,_⟫._@.Analysis.InnerProductSpace.PiL2._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  EuclideanSpace.inner_single_right
  [ DecidableEq ι ] ( i : ι ) ( a : 𝕜 ) ( v : EuclideanSpace 𝕜 ι )
    : ⟪ v , EuclideanSpace.single i ( a : 𝕜 ) ⟫ = a * conj v i
  := by simp [ apply_ite conj , mul_comm ]
#align euclidean_space.inner_single_right EuclideanSpace.inner_single_right

theorem EuclideanSpace.pi_Lp_congr_left_single [DecidableEq ι] {ι' : Type _} [Fintype ι']
    [DecidableEq ι'] (e : ι' ≃ ι) (i' : ι') :
    LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e (EuclideanSpace.single i' (1 : 𝕜)) =
      EuclideanSpace.single (e i') (1 : 𝕜) :=
  by
  ext i
  simpa using if_congr e.symm_apply_eq rfl rfl
#align euclidean_space.pi_Lp_congr_left_single EuclideanSpace.pi_Lp_congr_left_single

variable (ι 𝕜 E)

/-- An orthonormal basis on E is an identification of `E` with its dimensional-matching
`euclidean_space 𝕜 ι`. -/
structure OrthonormalBasis where of_repr ::
  repr : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι
#align orthonormal_basis OrthonormalBasis

variable {ι 𝕜 E}

namespace OrthonormalBasis

instance : Inhabited (OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)) :=
  ⟨of_repr (LinearIsometryEquiv.refl 𝕜 (EuclideanSpace 𝕜 ι))⟩

/-- `b i` is the `i`th basis vector. -/
instance : CoeFun (OrthonormalBasis ι 𝕜 E) fun _ => ι → E
    where coe b i := by classical exact b.repr.symm (EuclideanSpace.single i (1 : 𝕜))

@[simp]
theorem coe_of_repr [DecidableEq ι] (e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) :
    ⇑(OrthonormalBasis.of_repr e) = fun i => e.symm (EuclideanSpace.single i (1 : 𝕜)) :=
  by
  rw [coeFn]
  unfold CoeFun.coe
  funext
  congr
  simp only [eq_iff_true_of_subsingleton]
#align orthonormal_basis.coe_of_repr OrthonormalBasis.coe_of_repr

@[simp]
protected theorem repr_symm_single [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    b.repr.symm (EuclideanSpace.single i (1 : 𝕜)) = b i := by
  classical
    congr
    simp
#align orthonormal_basis.repr_symm_single OrthonormalBasis.repr_symm_single

@[simp]
protected theorem repr_self [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    b.repr (b i) = EuclideanSpace.single i (1 : 𝕜) := by
  rw [← b.repr_symm_single i, LinearIsometryEquiv.apply_symm_apply]
#align orthonormal_basis.repr_self OrthonormalBasis.repr_self

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `repr_apply_apply [])
      (Command.declSig
       [(Term.explicitBinder "(" [`b] [":" (Term.app `OrthonormalBasis [`ι `𝕜 `E])] [] ")")
        (Term.explicitBinder "(" [`v] [":" `E] [] ")")
        (Term.explicitBinder "(" [`i] [":" `ι] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (Term.proj `b "." `repr) [`v `i])
         "="
         (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" (Term.app `b [`i]) ", " `v "⟫"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticClassical_
            "classical"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app `b.repr.inner_map_map [(Term.app `b [`i]) `v]))
                  ","
                  (Tactic.rwRule [] (Term.app `b.repr_self [`i]))
                  ","
                  (Tactic.rwRule [] `EuclideanSpace.inner_single_left)]
                 "]")
                [])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `one_mul)
                  ","
                  (Tactic.simpLemma [] [] `eq_self_iff_true)
                  ","
                  (Tactic.simpLemma [] [] `map_one)]
                 "]"]
                [])])))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.tacticClassical_
           "classical"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app `b.repr.inner_map_map [(Term.app `b [`i]) `v]))
                 ","
                 (Tactic.rwRule [] (Term.app `b.repr_self [`i]))
                 ","
                 (Tactic.rwRule [] `EuclideanSpace.inner_single_left)]
                "]")
               [])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `one_mul)
                 ","
                 (Tactic.simpLemma [] [] `eq_self_iff_true)
                 ","
                 (Tactic.simpLemma [] [] `map_one)]
                "]"]
               [])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticClassical_
       "classical"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `b.repr.inner_map_map [(Term.app `b [`i]) `v]))
             ","
             (Tactic.rwRule [] (Term.app `b.repr_self [`i]))
             ","
             (Tactic.rwRule [] `EuclideanSpace.inner_single_left)]
            "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `one_mul)
             ","
             (Tactic.simpLemma [] [] `eq_self_iff_true)
             ","
             (Tactic.simpLemma [] [] `map_one)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `one_mul)
         ","
         (Tactic.simpLemma [] [] `eq_self_iff_true)
         ","
         (Tactic.simpLemma [] [] `map_one)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_self_iff_true
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `b.repr.inner_map_map [(Term.app `b [`i]) `v]))
         ","
         (Tactic.rwRule [] (Term.app `b.repr_self [`i]))
         ","
         (Tactic.rwRule [] `EuclideanSpace.inner_single_left)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `EuclideanSpace.inner_single_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `b.repr_self [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `b.repr_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `b.repr.inner_map_map [(Term.app `b [`i]) `v])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `b [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `b [`i]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `b.repr.inner_map_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (Term.proj `b "." `repr) [`v `i])
       "="
       (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" (Term.app `b [`i]) ", " `v "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" (Term.app `b [`i]) ", " `v "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.PiL2.term⟪_,_⟫._@.Analysis.InnerProductSpace.PiL2._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    repr_apply_apply
    ( b : OrthonormalBasis ι 𝕜 E ) ( v : E ) ( i : ι ) : b . repr v i = ⟪ b i , v ⟫
    :=
      by
        classical
          rw [ ← b.repr.inner_map_map b i v , b.repr_self i , EuclideanSpace.inner_single_left ]
            simp only [ one_mul , eq_self_iff_true , map_one ]
#align orthonormal_basis.repr_apply_apply OrthonormalBasis.repr_apply_apply

@[simp]
protected theorem orthonormal (b : OrthonormalBasis ι 𝕜 E) : Orthonormal 𝕜 b := by
  classical
    rw [orthonormal_iff_ite]
    intro i j
    rw [← b.repr.inner_map_map (b i) (b j), b.repr_self i, b.repr_self j,
      EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, map_one, one_mul]
#align orthonormal_basis.orthonormal OrthonormalBasis.orthonormal

/-- The `basis ι 𝕜 E` underlying the `orthonormal_basis` -/
protected def toBasis (b : OrthonormalBasis ι 𝕜 E) : Basis ι 𝕜 E :=
  Basis.ofEquivFun b.repr.toLinearEquiv
#align orthonormal_basis.to_basis OrthonormalBasis.toBasis

@[simp]
protected theorem coe_to_basis (b : OrthonormalBasis ι 𝕜 E) : (⇑b.toBasis : ι → E) = ⇑b :=
  by
  change ⇑(Basis.ofEquivFun b.repr.to_linear_equiv) = b
  ext j
  rw [Basis.coe_of_equiv_fun]
  congr
#align orthonormal_basis.coe_to_basis OrthonormalBasis.coe_to_basis

@[simp]
protected theorem coe_to_basis_repr (b : OrthonormalBasis ι 𝕜 E) :
    b.toBasis.equivFun = b.repr.toLinearEquiv :=
  by
  change (Basis.ofEquivFun b.repr.to_linear_equiv).equivFun = b.repr.to_linear_equiv
  ext (x j)
  simp only [Basis.of_equiv_fun_repr_apply, LinearIsometryEquiv.coe_to_linear_equiv,
    Basis.equiv_fun_apply]
#align orthonormal_basis.coe_to_basis_repr OrthonormalBasis.coe_to_basis_repr

@[simp]
protected theorem coe_to_basis_repr_apply (b : OrthonormalBasis ι 𝕜 E) (x : E) (i : ι) :
    b.toBasis.repr x i = b.repr x i := by
  rw [← Basis.equiv_fun_apply, OrthonormalBasis.coe_to_basis_repr,
    LinearIsometryEquiv.coe_to_linear_equiv]
#align orthonormal_basis.coe_to_basis_repr_apply OrthonormalBasis.coe_to_basis_repr_apply

protected theorem sum_repr (b : OrthonormalBasis ι 𝕜 E) (x : E) : (∑ i, b.repr x i • b i) = x :=
  by
  simp_rw [← b.coe_to_basis_repr_apply, ← b.coe_to_basis]
  exact b.to_basis.sum_repr x
#align orthonormal_basis.sum_repr OrthonormalBasis.sum_repr

protected theorem sum_repr_symm (b : OrthonormalBasis ι 𝕜 E) (v : EuclideanSpace 𝕜 ι) :
    (∑ i, v i • b i) = b.repr.symm v := by simpa using (b.to_basis.equiv_fun_symm_apply v).symm
#align orthonormal_basis.sum_repr_symm OrthonormalBasis.sum_repr_symm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `sum_inner_mul_inner [])
      (Command.declSig
       [(Term.explicitBinder "(" [`b] [":" (Term.app `OrthonormalBasis [`ι `𝕜 `E])] [] ")")
        (Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          ", "
          («term_*_»
           (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" `x ", " (Term.app `b [`i]) "⟫")
           "*"
           (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" (Term.app `b [`i]) ", " `y "⟫")))
         "="
         (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" `x ", " `y "⟫"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              []
              ":="
              (Term.app
               `congr_arg
               [(Term.app
                 (Term.explicit "@" `innerSL)
                 [`𝕜 (Term.hole "_") (Term.hole "_") (Term.hole "_") `x])
                (Term.app `b.sum_repr [`y])]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `map_sum)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           []
           (convert "convert" [] `this [])
           []
           (Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `SmulHomClass.map_smul)
              ","
              (Tactic.rwRule [] `b.repr_apply_apply)
              ","
              (Tactic.rwRule [] `mul_comm)]
             "]")
            [])
           []
           (Tactic.tacticRfl "rfl")])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             []
             ":="
             (Term.app
              `congr_arg
              [(Term.app
                (Term.explicit "@" `innerSL)
                [`𝕜 (Term.hole "_") (Term.hole "_") (Term.hole "_") `x])
               (Term.app `b.sum_repr [`y])]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `map_sum)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          []
          (convert "convert" [] `this [])
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `SmulHomClass.map_smul)
             ","
             (Tactic.rwRule [] `b.repr_apply_apply)
             ","
             (Tactic.rwRule [] `mul_comm)]
            "]")
           [])
          []
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `SmulHomClass.map_smul)
         ","
         (Tactic.rwRule [] `b.repr_apply_apply)
         ","
         (Tactic.rwRule [] `mul_comm)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b.repr_apply_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `SmulHomClass.map_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] `this [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `map_sum)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_sum
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         []
         ":="
         (Term.app
          `congr_arg
          [(Term.app
            (Term.explicit "@" `innerSL)
            [`𝕜 (Term.hole "_") (Term.hole "_") (Term.hole "_") `x])
           (Term.app `b.sum_repr [`y])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [(Term.app
         (Term.explicit "@" `innerSL)
         [`𝕜 (Term.hole "_") (Term.hole "_") (Term.hole "_") `x])
        (Term.app `b.sum_repr [`y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `b.sum_repr [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `b.sum_repr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `b.sum_repr [`y]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.explicit "@" `innerSL)
       [`𝕜 (Term.hole "_") (Term.hole "_") (Term.hole "_") `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `innerSL)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `innerSL
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.explicit "@" `innerSL) [`𝕜 (Term.hole "_") (Term.hole "_") (Term.hole "_") `x])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        («term_*_»
         (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" `x ", " (Term.app `b [`i]) "⟫")
         "*"
         (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" (Term.app `b [`i]) ", " `y "⟫")))
       "="
       (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" `x ", " `y "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" `x ", " `y "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.PiL2.term⟪_,_⟫._@.Analysis.InnerProductSpace.PiL2._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    sum_inner_mul_inner
    ( b : OrthonormalBasis ι 𝕜 E ) ( x y : E ) : ∑ i , ⟪ x , b i ⟫ * ⟪ b i , y ⟫ = ⟪ x , y ⟫
    :=
      by
        have := congr_arg @ innerSL 𝕜 _ _ _ x b.sum_repr y
          rw [ map_sum ] at this
          convert this
          ext i
          rw [ SmulHomClass.map_smul , b.repr_apply_apply , mul_comm ]
          rfl
#align orthonormal_basis.sum_inner_mul_inner OrthonormalBasis.sum_inner_mul_inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `orthogonal_projection_eq_sum [])
      (Command.declSig
       [(Term.implicitBinder "{" [`U] [":" (Term.app `Submodule [`𝕜 `E])] "}")
        (Term.instBinder "[" [] (Term.app `CompleteSpace [`U]) "]")
        (Term.explicitBinder "(" [`b] [":" (Term.app `OrthonormalBasis [`ι `𝕜 `U])] [] ")")
        (Term.explicitBinder "(" [`x] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `orthogonalProjection [`U `x])
         "="
         (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          ", "
          (Algebra.Group.Defs.«term_•_»
           (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
            "⟪"
            (Term.typeAscription "(" (Term.app `b [`i]) ":" [`E] ")")
            ", "
            `x
            "⟫")
           " • "
           (Term.app `b [`i]))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             ["only"]
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [] `b.repr_apply_apply)
                ","
                (Tactic.simpLemma [] [] `inner_orthogonal_projection_eq_of_mem_left)]
               "]")]
             ["using"
              (Term.proj
               (Term.app `b.sum_repr [(Term.app `orthogonalProjection [`U `x])])
               "."
               `symm)]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `b.repr_apply_apply)
               ","
               (Tactic.simpLemma [] [] `inner_orthogonal_projection_eq_of_mem_left)]
              "]")]
            ["using"
             (Term.proj
              (Term.app `b.sum_repr [(Term.app `orthogonalProjection [`U `x])])
              "."
              `symm)]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `b.repr_apply_apply)
           ","
           (Tactic.simpLemma [] [] `inner_orthogonal_projection_eq_of_mem_left)]
          "]")]
        ["using"
         (Term.proj (Term.app `b.sum_repr [(Term.app `orthogonalProjection [`U `x])]) "." `symm)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `b.sum_repr [(Term.app `orthogonalProjection [`U `x])]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `b.sum_repr [(Term.app `orthogonalProjection [`U `x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `orthogonalProjection [`U `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `orthogonalProjection
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `orthogonalProjection [`U `x])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `b.sum_repr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `b.sum_repr [(Term.paren "(" (Term.app `orthogonalProjection [`U `x]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_orthogonal_projection_eq_of_mem_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b.repr_apply_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `orthogonalProjection [`U `x])
       "="
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        (Algebra.Group.Defs.«term_•_»
         (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
          "⟪"
          (Term.typeAscription "(" (Term.app `b [`i]) ":" [`E] ")")
          ", "
          `x
          "⟫")
         " • "
         (Term.app `b [`i]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       ", "
       (Algebra.Group.Defs.«term_•_»
        (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
         "⟪"
         (Term.typeAscription "(" (Term.app `b [`i]) ":" [`E] ")")
         ", "
         `x
         "⟫")
        " • "
        (Term.app `b [`i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
        "⟪"
        (Term.typeAscription "(" (Term.app `b [`i]) ":" [`E] ")")
        ", "
        `x
        "⟫")
       " • "
       (Term.app `b [`i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `b [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
       "⟪"
       (Term.typeAscription "(" (Term.app `b [`i]) ":" [`E] ")")
       ", "
       `x
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.PiL2.term⟪_,_⟫._@.Analysis.InnerProductSpace.PiL2._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    orthogonal_projection_eq_sum
    { U : Submodule 𝕜 E } [ CompleteSpace U ] ( b : OrthonormalBasis ι 𝕜 U ) ( x : E )
      : orthogonalProjection U x = ∑ i , ⟪ ( b i : E ) , x ⟫ • b i
    :=
      by
        simpa
          only
            [ b.repr_apply_apply , inner_orthogonal_projection_eq_of_mem_left ]
            using b.sum_repr orthogonalProjection U x . symm
#align orthonormal_basis.orthogonal_projection_eq_sum OrthonormalBasis.orthogonal_projection_eq_sum

/-- Mapping an orthonormal basis along a `linear_isometry_equiv`. -/
protected def map {G : Type _} [InnerProductSpace 𝕜 G] (b : OrthonormalBasis ι 𝕜 E)
    (L : E ≃ₗᵢ[𝕜] G) : OrthonormalBasis ι 𝕜 G where repr := L.symm.trans b.repr
#align orthonormal_basis.map OrthonormalBasis.map

@[simp]
protected theorem map_apply {G : Type _} [InnerProductSpace 𝕜 G] (b : OrthonormalBasis ι 𝕜 E)
    (L : E ≃ₗᵢ[𝕜] G) (i : ι) : b.map L i = L (b i) :=
  rfl
#align orthonormal_basis.map_apply OrthonormalBasis.map_apply

@[simp]
protected theorem to_basis_map {G : Type _} [InnerProductSpace 𝕜 G] (b : OrthonormalBasis ι 𝕜 E)
    (L : E ≃ₗᵢ[𝕜] G) : (b.map L).toBasis = b.toBasis.map L.toLinearEquiv :=
  rfl
#align orthonormal_basis.to_basis_map OrthonormalBasis.to_basis_map

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "A basis that is orthonormal is an orthonormal basis. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `Basis.toOrthonormalBasis [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`v] [":" (Term.app `Basis [`ι `𝕜 `E])] [] ")")
        (Term.explicitBinder "(" [`hv] [":" (Term.app `Orthonormal [`𝕜 `v])] [] ")")]
       [(Term.typeSpec ":" (Term.app `OrthonormalBasis [`ι `𝕜 `E]))])
      (Command.declValSimple
       ":="
       («term_<|_»
        `OrthonormalBasis.of_repr
        "<|"
        (Term.app
         `LinearEquiv.isometryOfInner
         [(Term.proj `v "." `equivFun)
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.intro "intro" [`x `y])
              []
              (Tactic.tacticLet_
               "let"
               (Term.letDecl
                (Term.letIdDecl
                 `p
                 []
                 [(Term.typeSpec ":" (Term.app `EuclideanSpace [`𝕜 `ι]))]
                 ":="
                 (Term.app `v.equiv_fun [`x]))))
              []
              (Tactic.tacticLet_
               "let"
               (Term.letDecl
                (Term.letIdDecl
                 `q
                 []
                 [(Term.typeSpec ":" (Term.app `EuclideanSpace [`𝕜 `ι]))]
                 ":="
                 (Term.app `v.equiv_fun [`y]))))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`key []]
                 [(Term.typeSpec
                   ":"
                   («term_=_»
                    (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" `p ", " `q "⟫")
                    "="
                    (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
                     "⟪"
                     (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                      "∑"
                      (Std.ExtendedBinder.extBinders
                       (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                      ", "
                      (Algebra.Group.Defs.«term_•_» (Term.app `p [`i]) " • " (Term.app `v [`i])))
                     ", "
                     (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                      "∑"
                      (Std.ExtendedBinder.extBinders
                       (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                      ", "
                      (Algebra.Group.Defs.«term_•_» (Term.app `q [`i]) " • " (Term.app `v [`i])))
                     "⟫")))]
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.simp
                      "simp"
                      []
                      []
                      []
                      ["["
                       [(Tactic.simpLemma [] [] `sum_inner)
                        ","
                        (Tactic.simpLemma [] [] `inner_smul_left)
                        ","
                        (Tactic.simpLemma [] [] `hv.inner_right_fintype)]
                       "]"]
                      [])]))))))
              []
              (convert "convert" [] `key [])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    (Term.app `v.equiv_fun.symm_apply_apply [`x]))
                   ","
                   (Tactic.rwRule [] `v.equiv_fun_symm_apply)]
                  "]")
                 [])])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    (Term.app `v.equiv_fun.symm_apply_apply [`y]))
                   ","
                   (Tactic.rwRule [] `v.equiv_fun_symm_apply)]
                  "]")
                 [])])])))]))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `OrthonormalBasis.of_repr
       "<|"
       (Term.app
        `LinearEquiv.isometryOfInner
        [(Term.proj `v "." `equivFun)
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`x `y])
             []
             (Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl
                `p
                []
                [(Term.typeSpec ":" (Term.app `EuclideanSpace [`𝕜 `ι]))]
                ":="
                (Term.app `v.equiv_fun [`x]))))
             []
             (Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl
                `q
                []
                [(Term.typeSpec ":" (Term.app `EuclideanSpace [`𝕜 `ι]))]
                ":="
                (Term.app `v.equiv_fun [`y]))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`key []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" `p ", " `q "⟫")
                   "="
                   (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
                    "⟪"
                    (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                     "∑"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                     ", "
                     (Algebra.Group.Defs.«term_•_» (Term.app `p [`i]) " • " (Term.app `v [`i])))
                    ", "
                    (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                     "∑"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                     ", "
                     (Algebra.Group.Defs.«term_•_» (Term.app `q [`i]) " • " (Term.app `v [`i])))
                    "⟫")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.simp
                     "simp"
                     []
                     []
                     []
                     ["["
                      [(Tactic.simpLemma [] [] `sum_inner)
                       ","
                       (Tactic.simpLemma [] [] `inner_smul_left)
                       ","
                       (Tactic.simpLemma [] [] `hv.inner_right_fintype)]
                      "]"]
                     [])]))))))
             []
             (convert "convert" [] `key [])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app `v.equiv_fun.symm_apply_apply [`x]))
                  ","
                  (Tactic.rwRule [] `v.equiv_fun_symm_apply)]
                 "]")
                [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app `v.equiv_fun.symm_apply_apply [`y]))
                  ","
                  (Tactic.rwRule [] `v.equiv_fun_symm_apply)]
                 "]")
                [])])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `LinearEquiv.isometryOfInner
       [(Term.proj `v "." `equivFun)
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.intro "intro" [`x `y])
            []
            (Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letIdDecl
               `p
               []
               [(Term.typeSpec ":" (Term.app `EuclideanSpace [`𝕜 `ι]))]
               ":="
               (Term.app `v.equiv_fun [`x]))))
            []
            (Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letIdDecl
               `q
               []
               [(Term.typeSpec ":" (Term.app `EuclideanSpace [`𝕜 `ι]))]
               ":="
               (Term.app `v.equiv_fun [`y]))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`key []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" `p ", " `q "⟫")
                  "="
                  (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
                   "⟪"
                   (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                    "∑"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                    ", "
                    (Algebra.Group.Defs.«term_•_» (Term.app `p [`i]) " • " (Term.app `v [`i])))
                   ", "
                   (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                    "∑"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                    ", "
                    (Algebra.Group.Defs.«term_•_» (Term.app `q [`i]) " • " (Term.app `v [`i])))
                   "⟫")))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.simp
                    "simp"
                    []
                    []
                    []
                    ["["
                     [(Tactic.simpLemma [] [] `sum_inner)
                      ","
                      (Tactic.simpLemma [] [] `inner_smul_left)
                      ","
                      (Tactic.simpLemma [] [] `hv.inner_right_fintype)]
                     "]"]
                    [])]))))))
            []
            (convert "convert" [] `key [])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app `v.equiv_fun.symm_apply_apply [`x]))
                 ","
                 (Tactic.rwRule [] `v.equiv_fun_symm_apply)]
                "]")
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app `v.equiv_fun.symm_apply_apply [`y]))
                 ","
                 (Tactic.rwRule [] `v.equiv_fun_symm_apply)]
                "]")
               [])])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`x `y])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `p
             []
             [(Term.typeSpec ":" (Term.app `EuclideanSpace [`𝕜 `ι]))]
             ":="
             (Term.app `v.equiv_fun [`x]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `q
             []
             [(Term.typeSpec ":" (Term.app `EuclideanSpace [`𝕜 `ι]))]
             ":="
             (Term.app `v.equiv_fun [`y]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`key []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" `p ", " `q "⟫")
                "="
                (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
                 "⟪"
                 (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                  "∑"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                  ", "
                  (Algebra.Group.Defs.«term_•_» (Term.app `p [`i]) " • " (Term.app `v [`i])))
                 ", "
                 (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                  "∑"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                  ", "
                  (Algebra.Group.Defs.«term_•_» (Term.app `q [`i]) " • " (Term.app `v [`i])))
                 "⟫")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp
                  "simp"
                  []
                  []
                  []
                  ["["
                   [(Tactic.simpLemma [] [] `sum_inner)
                    ","
                    (Tactic.simpLemma [] [] `inner_smul_left)
                    ","
                    (Tactic.simpLemma [] [] `hv.inner_right_fintype)]
                   "]"]
                  [])]))))))
          []
          (convert "convert" [] `key [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app `v.equiv_fun.symm_apply_apply [`x]))
               ","
               (Tactic.rwRule [] `v.equiv_fun_symm_apply)]
              "]")
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app `v.equiv_fun.symm_apply_apply [`y]))
               ","
               (Tactic.rwRule [] `v.equiv_fun_symm_apply)]
              "]")
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app `v.equiv_fun.symm_apply_apply [`y]))
           ","
           (Tactic.rwRule [] `v.equiv_fun_symm_apply)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `v.equiv_fun.symm_apply_apply [`y]))
         ","
         (Tactic.rwRule [] `v.equiv_fun_symm_apply)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v.equiv_fun_symm_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `v.equiv_fun.symm_apply_apply [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `v.equiv_fun.symm_apply_apply
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app `v.equiv_fun.symm_apply_apply [`x]))
           ","
           (Tactic.rwRule [] `v.equiv_fun_symm_apply)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `v.equiv_fun.symm_apply_apply [`x]))
         ","
         (Tactic.rwRule [] `v.equiv_fun_symm_apply)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v.equiv_fun_symm_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `v.equiv_fun.symm_apply_apply [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `v.equiv_fun.symm_apply_apply
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] `key [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `key
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`key []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" `p ", " `q "⟫")
            "="
            (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
             "⟪"
             (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
              ", "
              (Algebra.Group.Defs.«term_•_» (Term.app `p [`i]) " • " (Term.app `v [`i])))
             ", "
             (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
              ", "
              (Algebra.Group.Defs.«term_•_» (Term.app `q [`i]) " • " (Term.app `v [`i])))
             "⟫")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp
              "simp"
              []
              []
              []
              ["["
               [(Tactic.simpLemma [] [] `sum_inner)
                ","
                (Tactic.simpLemma [] [] `inner_smul_left)
                ","
                (Tactic.simpLemma [] [] `hv.inner_right_fintype)]
               "]"]
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `sum_inner)
             ","
             (Tactic.simpLemma [] [] `inner_smul_left)
             ","
             (Tactic.simpLemma [] [] `hv.inner_right_fintype)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `sum_inner)
         ","
         (Tactic.simpLemma [] [] `inner_smul_left)
         ","
         (Tactic.simpLemma [] [] `hv.inner_right_fintype)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hv.inner_right_fintype
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_smul_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sum_inner
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫» "⟪" `p ", " `q "⟫")
       "="
       (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
        "⟪"
        (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
         "∑"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         ", "
         (Algebra.Group.Defs.«term_•_» (Term.app `p [`i]) " • " (Term.app `v [`i])))
        ", "
        (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
         "∑"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         ", "
         (Algebra.Group.Defs.«term_•_» (Term.app `q [`i]) " • " (Term.app `v [`i])))
        "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
       "⟪"
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        (Algebra.Group.Defs.«term_•_» (Term.app `p [`i]) " • " (Term.app `v [`i])))
       ", "
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        (Algebra.Group.Defs.«term_•_» (Term.app `q [`i]) " • " (Term.app `v [`i])))
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.PiL2.term⟪_,_⟫._@.Analysis.InnerProductSpace.PiL2._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- A basis that is orthonormal is an orthonormal basis. -/
  def
    Basis.toOrthonormalBasis
    ( v : Basis ι 𝕜 E ) ( hv : Orthonormal 𝕜 v ) : OrthonormalBasis ι 𝕜 E
    :=
      OrthonormalBasis.of_repr
        <|
        LinearEquiv.isometryOfInner
          v . equivFun
            by
              intro x y
                let p : EuclideanSpace 𝕜 ι := v.equiv_fun x
                let q : EuclideanSpace 𝕜 ι := v.equiv_fun y
                have
                  key
                    : ⟪ p , q ⟫ = ⟪ ∑ i , p i • v i , ∑ i , q i • v i ⟫
                    :=
                    by simp [ sum_inner , inner_smul_left , hv.inner_right_fintype ]
                convert key
                · rw [ ← v.equiv_fun.symm_apply_apply x , v.equiv_fun_symm_apply ]
                · rw [ ← v.equiv_fun.symm_apply_apply y , v.equiv_fun_symm_apply ]
#align basis.to_orthonormal_basis Basis.toOrthonormalBasis

@[simp]
theorem Basis.coe_to_orthonormal_basis_repr (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    ((v.toOrthonormalBasis hv).repr : E → EuclideanSpace 𝕜 ι) = v.equivFun :=
  rfl
#align basis.coe_to_orthonormal_basis_repr Basis.coe_to_orthonormal_basis_repr

@[simp]
theorem Basis.coe_to_orthonormal_basis_repr_symm (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    ((v.toOrthonormalBasis hv).repr.symm : EuclideanSpace 𝕜 ι → E) = v.equivFun.symm :=
  rfl
#align basis.coe_to_orthonormal_basis_repr_symm Basis.coe_to_orthonormal_basis_repr_symm

@[simp]
theorem Basis.to_basis_to_orthonormal_basis (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    (v.toOrthonormalBasis hv).toBasis = v := by
  simp [Basis.toOrthonormalBasis, OrthonormalBasis.toBasis]
#align basis.to_basis_to_orthonormal_basis Basis.to_basis_to_orthonormal_basis

@[simp]
theorem Basis.coe_to_orthonormal_basis (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    (v.toOrthonormalBasis hv : ι → E) = (v : ι → E) :=
  calc
    (v.toOrthonormalBasis hv : ι → E) = ((v.toOrthonormalBasis hv).toBasis : ι → E) := by
      classical rw [OrthonormalBasis.coe_to_basis]
    _ = (v : ι → E) := by simp
    
#align basis.coe_to_orthonormal_basis Basis.coe_to_orthonormal_basis

variable {v : ι → E}

/-- A finite orthonormal set that spans is an orthonormal basis -/
protected def mk (hon : Orthonormal 𝕜 v) (hsp : ⊤ ≤ Submodule.span 𝕜 (Set.range v)) :
    OrthonormalBasis ι 𝕜 E :=
  (Basis.mk (Orthonormal.linear_independent hon) hsp).toOrthonormalBasis (by rwa [Basis.coe_mk])
#align orthonormal_basis.mk OrthonormalBasis.mk

@[simp]
protected theorem coe_mk (hon : Orthonormal 𝕜 v) (hsp : ⊤ ≤ Submodule.span 𝕜 (Set.range v)) :
    ⇑(OrthonormalBasis.mk hon hsp) = v := by
  classical rw [OrthonormalBasis.mk, _root_.basis.coe_to_orthonormal_basis, Basis.coe_mk]
#align orthonormal_basis.coe_mk OrthonormalBasis.coe_mk

/-- Any finite subset of a orthonormal family is an `orthonormal_basis` for its span. -/
protected def span {v' : ι' → E} (h : Orthonormal 𝕜 v') (s : Finset ι') :
    OrthonormalBasis s 𝕜 (span 𝕜 (s.image v' : Set E)) :=
  let e₀' : Basis s 𝕜 _ :=
    Basis.span (h.LinearIndependent.comp (coe : s → ι') Subtype.coe_injective)
  let e₀ : OrthonormalBasis s 𝕜 _ :=
    OrthonormalBasis.mk
      (by
        convert orthonormalSpan (h.comp (coe : s → ι') Subtype.coe_injective)
        ext
        simp [e₀', Basis.span_apply])
      e₀'.span_eq.ge
  let φ : span 𝕜 (s.image v' : Set E) ≃ₗᵢ[𝕜] span 𝕜 (range (v' ∘ (coe : s → ι'))) :=
    LinearIsometryEquiv.ofEq _ _
      (by
        rw [Finset.coe_image, image_eq_range]
        rfl)
  e₀.map φ.symm
#align orthonormal_basis.span OrthonormalBasis.span

@[simp]
protected theorem span_apply {v' : ι' → E} (h : Orthonormal 𝕜 v') (s : Finset ι') (i : s) :
    (OrthonormalBasis.span h s i : E) = v' i := by
  simp only [OrthonormalBasis.span, Basis.span_apply, LinearIsometryEquiv.of_eq_symm,
    OrthonormalBasis.map_apply, OrthonormalBasis.coe_mk, LinearIsometryEquiv.coe_of_eq_apply]
#align orthonormal_basis.span_apply OrthonormalBasis.span_apply

open Submodule

/-- A finite orthonormal family of vectors whose span has trivial orthogonal complement is an
orthonormal basis. -/
protected def mkOfOrthogonalEqBot (hon : Orthonormal 𝕜 v) (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) :
    OrthonormalBasis ι 𝕜 E :=
  OrthonormalBasis.mk hon
    (by
      refine' Eq.ge _
      haveI : FiniteDimensional 𝕜 (span 𝕜 (range v)) :=
        FiniteDimensional.span_of_finite 𝕜 (finite_range v)
      haveI : CompleteSpace (span 𝕜 (range v)) := FiniteDimensional.complete 𝕜 _
      rwa [orthogonal_eq_bot_iff] at hsp)
#align orthonormal_basis.mk_of_orthogonal_eq_bot OrthonormalBasis.mkOfOrthogonalEqBot

@[simp]
protected theorem coe_of_orthogonal_eq_bot_mk (hon : Orthonormal 𝕜 v)
    (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) : ⇑(OrthonormalBasis.mkOfOrthogonalEqBot hon hsp) = v :=
  OrthonormalBasis.coe_mk hon _
#align orthonormal_basis.coe_of_orthogonal_eq_bot_mk OrthonormalBasis.coe_of_orthogonal_eq_bot_mk

variable [Fintype ι']

/-- `b.reindex (e : ι ≃ ι')` is an `orthonormal_basis` indexed by `ι'` -/
def reindex (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') : OrthonormalBasis ι' 𝕜 E :=
  OrthonormalBasis.of_repr (b.repr.trans (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e))
#align orthonormal_basis.reindex OrthonormalBasis.reindex

protected theorem reindex_apply (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') (i' : ι') :
    (b.reindex e) i' = b (e.symm i') := by
  classical
    dsimp [reindex, OrthonormalBasis.hasCoeToFun]
    rw [coe_of_repr]
    dsimp
    rw [← b.repr_symm_single, LinearIsometryEquiv.pi_Lp_congr_left_symm,
      EuclideanSpace.pi_Lp_congr_left_single]
#align orthonormal_basis.reindex_apply OrthonormalBasis.reindex_apply

@[simp]
protected theorem coe_reindex (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') :
    ⇑(b.reindex e) = ⇑b ∘ ⇑e.symm :=
  funext (b.reindex_apply e)
#align orthonormal_basis.coe_reindex OrthonormalBasis.coe_reindex

@[simp]
protected theorem reindex_repr (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') (x : E) (i' : ι') :
    ((b.reindex e).repr x) i' = (b.repr x) (e.symm i') := by
  classical rw [OrthonormalBasis.repr_apply_apply, b.repr_apply_apply, OrthonormalBasis.coe_reindex]
#align orthonormal_basis.reindex_repr OrthonormalBasis.reindex_repr

end OrthonormalBasis

/-- `![1, I]` is an orthonormal basis for `ℂ` considered as a real inner product space. -/
def Complex.orthonormalBasisOneI : OrthonormalBasis (Fin 2) ℝ ℂ :=
  Complex.basisOneI.toOrthonormalBasis
    (by
      rw [orthonormal_iff_ite]
      intro i; fin_cases i <;> intro j <;> fin_cases j <;> simp [real_inner_eq_re_inner])
#align complex.orthonormal_basis_one_I Complex.orthonormalBasisOneI

@[simp]
theorem Complex.orthonormal_basis_one_I_repr_apply (z : ℂ) :
    Complex.orthonormalBasisOneI.repr z = ![z.re, z.im] :=
  rfl
#align complex.orthonormal_basis_one_I_repr_apply Complex.orthonormal_basis_one_I_repr_apply

@[simp]
theorem Complex.orthonormal_basis_one_I_repr_symm_apply (x : EuclideanSpace ℝ (Fin 2)) :
    Complex.orthonormalBasisOneI.repr.symm x = x 0 + x 1 * I :=
  rfl
#align
  complex.orthonormal_basis_one_I_repr_symm_apply Complex.orthonormal_basis_one_I_repr_symm_apply

@[simp]
theorem Complex.to_basis_orthonormal_basis_one_I :
    Complex.orthonormalBasisOneI.toBasis = Complex.basisOneI :=
  Basis.to_basis_to_orthonormal_basis _ _
#align complex.to_basis_orthonormal_basis_one_I Complex.to_basis_orthonormal_basis_one_I

@[simp]
theorem Complex.coe_orthonormal_basis_one_I :
    (Complex.orthonormalBasisOneI : Fin 2 → ℂ) = ![1, i] := by simp [Complex.orthonormalBasisOneI]
#align complex.coe_orthonormal_basis_one_I Complex.coe_orthonormal_basis_one_I

/-- The isometry between `ℂ` and a two-dimensional real inner product space given by a basis. -/
def Complex.isometryOfOrthonormal (v : OrthonormalBasis (Fin 2) ℝ F) : ℂ ≃ₗᵢ[ℝ] F :=
  Complex.orthonormalBasisOneI.repr.trans v.repr.symm
#align complex.isometry_of_orthonormal Complex.isometryOfOrthonormal

@[simp]
theorem Complex.map_isometry_of_orthonormal (v : OrthonormalBasis (Fin 2) ℝ F) (f : F ≃ₗᵢ[ℝ] F') :
    Complex.isometryOfOrthonormal (v.map f) = (Complex.isometryOfOrthonormal v).trans f := by
  simp [Complex.isometryOfOrthonormal, LinearIsometryEquiv.trans_assoc, OrthonormalBasis.map]
#align complex.map_isometry_of_orthonormal Complex.map_isometry_of_orthonormal

theorem Complex.isometry_of_orthonormal_symm_apply (v : OrthonormalBasis (Fin 2) ℝ F) (f : F) :
    (Complex.isometryOfOrthonormal v).symm f =
      (v.toBasis.Coord 0 f : ℂ) + (v.toBasis.Coord 1 f : ℂ) * I :=
  by simp [Complex.isometryOfOrthonormal]
#align complex.isometry_of_orthonormal_symm_apply Complex.isometry_of_orthonormal_symm_apply

theorem Complex.isometry_of_orthonormal_apply (v : OrthonormalBasis (Fin 2) ℝ F) (z : ℂ) :
    Complex.isometryOfOrthonormal v z = z.re • v 0 + z.im • v 1 := by
  simp [Complex.isometryOfOrthonormal, ← v.sum_repr_symm]
#align complex.isometry_of_orthonormal_apply Complex.isometry_of_orthonormal_apply

open FiniteDimensional

/-! ### Matrix representation of an orthonormal basis with respect to another -/


section ToMatrix

variable [DecidableEq ι]

section

variable (a b : OrthonormalBasis ι 𝕜 E)

/-- The change-of-basis matrix between two orthonormal bases `a`, `b` is a unitary matrix. -/
theorem OrthonormalBasis.to_matrix_orthonormal_basis_mem_unitary :
    a.toBasis.toMatrix b ∈ Matrix.unitaryGroup ι 𝕜 :=
  by
  rw [Matrix.mem_unitary_group_iff']
  ext (i j)
  convert a.repr.inner_map_map (b i) (b j)
  rw [orthonormal_iff_ite.mp b.orthonormal i j]
  rfl
#align
  orthonormal_basis.to_matrix_orthonormal_basis_mem_unitary OrthonormalBasis.to_matrix_orthonormal_basis_mem_unitary

/-- The determinant of the change-of-basis matrix between two orthonormal bases `a`, `b` has
unit length. -/
@[simp]
theorem OrthonormalBasis.det_to_matrix_orthonormal_basis : ‖a.toBasis.det b‖ = 1 :=
  by
  have : (norm_sq (a.to_basis.det b) : 𝕜) = 1 := by
    simpa [IsROrC.mul_conj] using
      (Matrix.det_of_mem_unitary (a.to_matrix_orthonormal_basis_mem_unitary b)).2
  norm_cast  at this
  rwa [← sqrt_norm_sq_eq_norm, sqrt_eq_one]
#align
  orthonormal_basis.det_to_matrix_orthonormal_basis OrthonormalBasis.det_to_matrix_orthonormal_basis

end

section Real

variable (a b : OrthonormalBasis ι ℝ F)

/-- The change-of-basis matrix between two orthonormal bases `a`, `b` is an orthogonal matrix. -/
theorem OrthonormalBasis.to_matrix_orthonormal_basis_mem_orthogonal :
    a.toBasis.toMatrix b ∈ Matrix.orthogonalGroup ι ℝ :=
  a.to_matrix_orthonormal_basis_mem_unitary b
#align
  orthonormal_basis.to_matrix_orthonormal_basis_mem_orthogonal OrthonormalBasis.to_matrix_orthonormal_basis_mem_orthogonal

/-- The determinant of the change-of-basis matrix between two orthonormal bases `a`, `b` is ±1. -/
theorem OrthonormalBasis.det_to_matrix_orthonormal_basis_real :
    a.toBasis.det b = 1 ∨ a.toBasis.det b = -1 :=
  by
  rw [← sq_eq_one_iff]
  simpa [unitary, sq] using Matrix.det_of_mem_unitary (a.to_matrix_orthonormal_basis_mem_unitary b)
#align
  orthonormal_basis.det_to_matrix_orthonormal_basis_real OrthonormalBasis.det_to_matrix_orthonormal_basis_real

end Real

end ToMatrix

/-! ### Existence of orthonormal basis, etc. -/


section FiniteDimensional

variable {v : Set E}

variable {A : ι → Submodule 𝕜 E}

/-- Given an internal direct sum decomposition of a module `M`, and an orthonormal basis for each
of the components of the direct sum, the disjoint union of these orthonormal bases is an
orthonormal basis for `M`. -/
noncomputable def DirectSum.IsInternal.collectedOrthonormalBasis
    (hV : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => A i) _ fun i => (A i).subtypeₗᵢ) [DecidableEq ι]
    (hV_sum : DirectSum.IsInternal fun i => A i) {α : ι → Type _} [∀ i, Fintype (α i)]
    (v_family : ∀ i, OrthonormalBasis (α i) 𝕜 (A i)) : OrthonormalBasis (Σi, α i) 𝕜 E :=
  (hV_sum.collectedBasis fun i => (v_family i).toBasis).toOrthonormalBasis <| by
    simpa using
      hV.orthonormal_sigma_orthonormal (show ∀ i, Orthonormal 𝕜 (v_family i).toBasis by simp)
#align
  direct_sum.is_internal.collected_orthonormal_basis DirectSum.IsInternal.collectedOrthonormalBasis

theorem DirectSum.IsInternal.collected_orthonormal_basis_mem [DecidableEq ι]
    (h : DirectSum.IsInternal A) {α : ι → Type _} [∀ i, Fintype (α i)]
    (hV : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => A i) _ fun i => (A i).subtypeₗᵢ)
    (v : ∀ i, OrthonormalBasis (α i) 𝕜 (A i)) (a : Σi, α i) :
    h.collectedOrthonormalBasis hV v a ∈ A a.1 := by
  simp [DirectSum.IsInternal.collectedOrthonormalBasis]
#align
  direct_sum.is_internal.collected_orthonormal_basis_mem DirectSum.IsInternal.collected_orthonormal_basis_mem

variable [FiniteDimensional 𝕜 E]

/-- In a finite-dimensional `inner_product_space`, any orthonormal subset can be extended to an
orthonormal basis. -/
theorem Orthonormal.exists_orthonormal_basis_extension (hv : Orthonormal 𝕜 (coe : v → E)) :
    ∃ (u : Finset E)(b : OrthonormalBasis u 𝕜 E), v ⊆ u ∧ ⇑b = coe :=
  by
  obtain ⟨u₀, hu₀s, hu₀, hu₀_max⟩ := exists_maximal_orthonormal hv
  rw [maximal_orthonormal_iff_orthogonal_complement_eq_bot hu₀] at hu₀_max
  have hu₀_finite : u₀.finite := hu₀.linear_independent.finite
  let u : Finset E := hu₀_finite.to_finset
  let fu : ↥u ≃ ↥u₀ := Equiv.cast (congr_arg coeSort hu₀_finite.coe_to_finset)
  have hfu : (coe : u → E) = (coe : u₀ → E) ∘ fu :=
    by
    ext
    simp
  have hu : Orthonormal 𝕜 (coe : u → E) := by simpa [hfu] using hu₀.comp _ fu.injective
  refine' ⟨u, OrthonormalBasis.mkOfOrthogonalEqBot hu _, _, _⟩
  · simpa using hu₀_max
  · simpa using hu₀s
  · simp
#align orthonormal.exists_orthonormal_basis_extension Orthonormal.exists_orthonormal_basis_extension

theorem Orthonormal.exists_orthonormal_basis_extension_of_card_eq {ι : Type _} [Fintype ι]
    (card_ι : finrank 𝕜 E = Fintype.card ι) {v : ι → E} {s : Set ι}
    (hv : Orthonormal 𝕜 (s.restrict v)) : ∃ b : OrthonormalBasis ι 𝕜 E, ∀ i ∈ s, b i = v i :=
  by
  have hsv : injective (s.restrict v) := hv.linear_independent.injective
  have hX : Orthonormal 𝕜 (coe : Set.range (s.restrict v) → E) := by
    rwa [orthonormal_subtype_range hsv]
  obtain ⟨Y, b₀, hX, hb₀⟩ := hX.exists_orthonormal_basis_extension
  have hιY : Fintype.card ι = Y.card :=
    by
    refine' card_ι.symm.trans _
    exact FiniteDimensional.finrank_eq_card_finset_basis b₀.to_basis
  have hvsY : s.maps_to v Y := (s.maps_to_image v).mono_right (by rwa [← range_restrict])
  have hsv' : Set.InjOn v s := by
    rw [Set.injOn_iff_injective]
    exact hsv
  obtain ⟨g, hg⟩ := hvsY.exists_equiv_extend_of_card_eq hιY hsv'
  use b₀.reindex g.symm
  intro i hi
  · simp [hb₀, hg i hi]
#align
  orthonormal.exists_orthonormal_basis_extension_of_card_eq Orthonormal.exists_orthonormal_basis_extension_of_card_eq

variable (𝕜 E)

/-- A finite-dimensional inner product space admits an orthonormal basis. -/
theorem exists_orthonormal_basis :
    ∃ (w : Finset E)(b : OrthonormalBasis w 𝕜 E), ⇑b = (coe : w → E) :=
  let ⟨w, hw, hw', hw''⟩ := (orthonormalEmpty 𝕜 E).exists_orthonormal_basis_extension
  ⟨w, hw, hw''⟩
#align exists_orthonormal_basis exists_orthonormal_basis

/-- A finite-dimensional `inner_product_space` has an orthonormal basis. -/
irreducible_def stdOrthonormalBasis : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E :=
  by
  let b := Classical.choose (Classical.choose_spec <| exists_orthonormal_basis 𝕜 E)
  rw [finrank_eq_card_basis b.to_basis]
  exact b.reindex (Fintype.equivFinOfCardEq rfl)
#align std_orthonormal_basis stdOrthonormalBasis

/-- An orthonormal basis of `ℝ` is made either of the vector `1`, or of the vector `-1`. -/
theorem orthonormal_basis_one_dim (b : OrthonormalBasis ι ℝ ℝ) :
    (⇑b = fun _ => (1 : ℝ)) ∨ ⇑b = fun _ => (-1 : ℝ) :=
  by
  have : Unique ι := b.to_basis.unique
  have : b default = 1 ∨ b default = -1 :=
    by
    have : ‖b default‖ = 1 := b.orthonormal.1 _
    rwa [Real.norm_eq_abs, abs_eq (zero_le_one : (0 : ℝ) ≤ 1)] at this
  rw [eq_const_of_unique b]
  refine' this.imp _ _ <;> simp
#align orthonormal_basis_one_dim orthonormal_basis_one_dim

variable {𝕜 E}

section SubordinateOrthonormalBasis

open DirectSum

variable {n : ℕ} (hn : finrank 𝕜 E = n) [DecidableEq ι] {V : ι → Submodule 𝕜 E} (hV : IsInternal V)

/-- Exhibit a bijection between `fin n` and the index set of a certain basis of an `n`-dimensional
inner product space `E`.  This should not be accessed directly, but only via the subsequent API. -/
irreducible_def DirectSum.IsInternal.sigmaOrthonormalBasisIndexEquiv
  (hV' : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => V i) _ fun i => (V i).subtypeₗᵢ) :
  (Σi, Fin (finrank 𝕜 (V i))) ≃ Fin n :=
  let b := hV.collectedOrthonormalBasis hV' fun i => stdOrthonormalBasis 𝕜 (V i)
  Fintype.equivFinOfCardEq <| (FiniteDimensional.finrank_eq_card_basis b.toBasis).symm.trans hn
#align
  direct_sum.is_internal.sigma_orthonormal_basis_index_equiv DirectSum.IsInternal.sigmaOrthonormalBasisIndexEquiv

/-- An `n`-dimensional `inner_product_space` equipped with a decomposition as an internal direct
sum has an orthonormal basis indexed by `fin n` and subordinate to that direct sum. -/
irreducible_def DirectSum.IsInternal.subordinateOrthonormalBasis
  (hV' : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => V i) _ fun i => (V i).subtypeₗᵢ) :
  OrthonormalBasis (Fin n) 𝕜 E :=
  (hV.collectedOrthonormalBasis hV' fun i => stdOrthonormalBasis 𝕜 (V i)).reindex
    (hV.sigmaOrthonormalBasisIndexEquiv hn hV')
#align
  direct_sum.is_internal.subordinate_orthonormal_basis DirectSum.IsInternal.subordinateOrthonormalBasis

/-- An `n`-dimensional `inner_product_space` equipped with a decomposition as an internal direct
sum has an orthonormal basis indexed by `fin n` and subordinate to that direct sum. This function
provides the mapping by which it is subordinate. -/
def DirectSum.IsInternal.subordinateOrthonormalBasisIndex (a : Fin n)
    (hV' : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => V i) _ fun i => (V i).subtypeₗᵢ) : ι :=
  ((hV.sigmaOrthonormalBasisIndexEquiv hn hV').symm a).1
#align
  direct_sum.is_internal.subordinate_orthonormal_basis_index DirectSum.IsInternal.subordinateOrthonormalBasisIndex

/-- The basis constructed in `orthogonal_family.subordinate_orthonormal_basis` is subordinate to
the `orthogonal_family` in question. -/
theorem DirectSum.IsInternal.subordinate_orthonormal_basis_subordinate (a : Fin n)
    (hV' : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => V i) _ fun i => (V i).subtypeₗᵢ) :
    hV.subordinateOrthonormalBasis hn hV' a ∈ V (hV.subordinateOrthonormalBasisIndex hn a hV') := by
  simpa only [DirectSum.IsInternal.subordinateOrthonormalBasis, OrthonormalBasis.coe_reindex] using
    hV.collected_orthonormal_basis_mem hV' (fun i => stdOrthonormalBasis 𝕜 (V i))
      ((hV.sigma_orthonormal_basis_index_equiv hn hV').symm a)
#align
  direct_sum.is_internal.subordinate_orthonormal_basis_subordinate DirectSum.IsInternal.subordinate_orthonormal_basis_subordinate

end SubordinateOrthonormalBasis

end FiniteDimensional

attribute [local instance] fact_finite_dimensional_of_finrank_eq_succ

/-- Given a natural number `n` one less than the `finrank` of a finite-dimensional inner product
space, there exists an isometry from the orthogonal complement of a nonzero singleton to
`euclidean_space 𝕜 (fin n)`. -/
def OrthonormalBasis.fromOrthogonalSpanSingleton (n : ℕ) [Fact (finrank 𝕜 E = n + 1)] {v : E}
    (hv : v ≠ 0) : OrthonormalBasis (Fin n) 𝕜 (𝕜 ∙ v)ᗮ :=
  (stdOrthonormalBasis _ _).reindex <| finCongr <| finrank_orthogonal_span_singleton hv
#align orthonormal_basis.from_orthogonal_span_singleton OrthonormalBasis.fromOrthogonalSpanSingleton

section LinearIsometry

variable {V : Type _} [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

variable {S : Submodule 𝕜 V} {L : S →ₗᵢ[𝕜] V}

open FiniteDimensional

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Let `S` be a subspace of a finite-dimensional complex inner product space `V`.  A linear\nisometry mapping `S` into `V` can be extended to a full isometry of `V`.\n\nTODO:  The case when `S` is a finite-dimensional subspace of an infinite-dimensional `V`.-/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `LinearIsometry.extend [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`L]
         [":" (Analysis.NormedSpace.LinearIsometry.«term_→ₗᵢ[_]_» `S " →ₗᵢ[" `𝕜 "] " `V)]
         []
         ")")]
       [(Term.typeSpec
         ":"
         (Analysis.NormedSpace.LinearIsometry.«term_→ₗᵢ[_]_» `V " →ₗᵢ[" `𝕜 "] " `V))])
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `d
              []
              []
              ":="
              (Term.app `finrank [`𝕜 (Analysis.InnerProductSpace.Basic.«term_ᗮ» `S "ᗮ")]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`dim_S_perp []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.app `finrank [`𝕜 (Analysis.InnerProductSpace.Basic.«term_ᗮ» `S "ᗮ")])
                 "="
                 `d))]
              ":="
              `rfl)))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl (Term.letIdDecl `LS [] [] ":=" `L.to_linear_map.range)))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`E []]
              [(Term.typeSpec
                ":"
                (Analysis.NormedSpace.LinearIsometry.«term_≃ₗᵢ[_]_»
                 (Analysis.InnerProductSpace.Basic.«term_ᗮ» `S "ᗮ")
                 " ≃ₗᵢ["
                 `𝕜
                 "] "
                 (Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Mathlib.Tactic.tacticHave_
                   "have"
                   [`dim_LS_perp []]
                   [(Term.typeSpec
                     ":"
                     («term_=_»
                      (Term.app `finrank [`𝕜 (Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ")])
                      "="
                      `d))])
                  []
                  (calcTactic
                   "calc"
                   (calcStep
                    («term_=_»
                     (Term.app `finrank [`𝕜 (Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ")])
                     "="
                     («term_-_» (Term.app `finrank [`𝕜 `V]) "-" (Term.app `finrank [`𝕜 `LS])))
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.simp
                         "simp"
                         []
                         []
                         ["only"]
                         ["["
                          [(Tactic.simpLemma
                            []
                            [(patternIgnore (token.«← » "←"))]
                            `LS.finrank_add_finrank_orthogonal)
                           ","
                           (Tactic.simpLemma [] [] `add_tsub_cancel_left)]
                          "]"]
                         [])]))))
                   [(calcStep
                     («term_=_»
                      (Term.hole "_")
                      "="
                      («term_-_» (Term.app `finrank [`𝕜 `V]) "-" (Term.app `finrank [`𝕜 `S])))
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.simp
                          "simp"
                          []
                          []
                          ["only"]
                          ["["
                           [(Tactic.simpLemma
                             []
                             []
                             (Term.app `LinearMap.finrank_range_of_inj [`L.injective]))]
                           "]"]
                          [])]))))
                    (calcStep
                     («term_=_»
                      (Term.hole "_")
                      "="
                      (Term.app `finrank [`𝕜 (Analysis.InnerProductSpace.Basic.«term_ᗮ» `S "ᗮ")]))
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.simp
                          "simp"
                          []
                          []
                          ["only"]
                          ["["
                           [(Tactic.simpLemma
                             []
                             [(patternIgnore (token.«← » "←"))]
                             `S.finrank_add_finrank_orthogonal)
                            ","
                            (Tactic.simpLemma [] [] `add_tsub_cancel_left)]
                           "]"]
                          [])]))))])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    (Term.proj
                     (Term.proj
                      (Term.app
                       `stdOrthonormalBasis
                       [`𝕜 (Analysis.InnerProductSpace.Basic.«term_ᗮ» `S "ᗮ")])
                      "."
                      `repr)
                     "."
                     `trans)
                    [(Term.proj
                      (Term.proj
                       («term_<|_»
                        (Term.proj
                         (Term.app
                          `stdOrthonormalBasis
                          [`𝕜 (Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ")])
                         "."
                         `reindex)
                        "<|"
                        (Term.app `finCongr [`dim_LS_perp]))
                       "."
                       `repr)
                      "."
                      `symm)]))]))))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `L3
              []
              []
              ":="
              (Term.app
               (Term.proj
                (Term.proj (Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ") "." `subtypeₗᵢ)
                "."
                `comp)
               [`E.to_linear_isometry]))))
           []
           (Std.Tactic.tacticHaveI_
            "haveI"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec ":" (Term.app `CompleteSpace [`S]))]
              ":="
              (Term.app `FiniteDimensional.complete [`𝕜 `S]))))
           []
           (Std.Tactic.tacticHaveI_
            "haveI"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec ":" (Term.app `CompleteSpace [`V]))]
              ":="
              (Term.app `FiniteDimensional.complete [`𝕜 `V]))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `p1
              []
              []
              ":="
              (Term.proj (Term.app `orthogonalProjection [`S]) "." `toLinearMap))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `p2
              []
              []
              ":="
              (Term.proj
               (Term.app `orthogonalProjection [(Analysis.InnerProductSpace.Basic.«term_ᗮ» `S "ᗮ")])
               "."
               `toLinearMap))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `M
              []
              []
              ":="
              («term_+_»
               (Term.app `L.to_linear_map.comp [`p1])
               "+"
               (Term.app `L3.to_linear_map.comp [`p2])))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`M_norm_map []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`x]
                 [(Term.typeSpec ":" `V)]
                 ","
                 («term_=_»
                  (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `M [`x]) "‖")
                  "="
                  (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`x])
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`Mx_decomp []]
                     [(Term.typeSpec
                       ":"
                       («term_=_»
                        (Term.app `M [`x])
                        "="
                        («term_+_»
                         (Term.app `L [(Term.app `p1 [`x])])
                         "+"
                         (Term.app `L3 [(Term.app `p2 [`x])]))))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.simp
                          "simp"
                          []
                          []
                          ["only"]
                          ["["
                           [(Tactic.simpLemma [] [] `LinearMap.add_apply)
                            ","
                            (Tactic.simpLemma [] [] `LinearMap.comp_apply)
                            ","
                            (Tactic.simpLemma [] [] `LinearMap.comp_apply)
                            ","
                            (Tactic.simpLemma [] [] `LinearIsometry.coe_to_linear_map)]
                           "]"]
                          [])]))))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`Mx_orth []]
                     [(Term.typeSpec
                       ":"
                       («term_=_»
                        (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
                         "⟪"
                         (Term.app `L [(Term.app `p1 [`x])])
                         ", "
                         (Term.app `L3 [(Term.app `p2 [`x])])
                         "⟫")
                        "="
                        (num "0")))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            [`Lp1x []]
                            [(Term.typeSpec
                              ":"
                              («term_∈_»
                               (Term.app `L [(Term.app `p1 [`x])])
                               "∈"
                               `L.to_linear_map.range))]
                            ":="
                            (Term.app
                             `LinearMap.mem_range_self
                             [`L.to_linear_map (Term.app `p1 [`x])]))))
                         []
                         (Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            [`Lp2x []]
                            [(Term.typeSpec
                              ":"
                              («term_∈_»
                               (Term.app `L3 [(Term.app `p2 [`x])])
                               "∈"
                               (Analysis.InnerProductSpace.Basic.«term_ᗮ»
                                `L.to_linear_map.range
                                "ᗮ")))]
                            ":="
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Tactic.simp
                                 "simp"
                                 []
                                 []
                                 ["only"]
                                 ["["
                                  [(Tactic.simpLemma [] [] `L3)
                                   ","
                                   (Tactic.simpLemma [] [] `LinearIsometry.coe_comp)
                                   ","
                                   (Tactic.simpLemma [] [] `Function.comp_apply)
                                   ","
                                   (Tactic.simpLemma [] [] `Submodule.coe_subtypeₗᵢ)
                                   ","
                                   (Tactic.simpLemma
                                    []
                                    [(patternIgnore (token.«← » "←"))]
                                    (Term.app
                                     `Submodule.range_subtype
                                     [(Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ")]))]
                                  "]"]
                                 [])
                                []
                                (Tactic.apply "apply" `LinearMap.mem_range_self)]))))))
                         []
                         (Tactic.apply
                          "apply"
                          (Term.app `Submodule.inner_right_of_mem_orthogonal [`Lp1x `Lp2x]))]))))))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app
                       `sq_eq_sq
                       [(Term.app `norm_nonneg [(Term.hole "_")])
                        (Term.app `norm_nonneg [(Term.hole "_")])]))
                     ","
                     (Tactic.rwRule [] (Term.app `norm_sq_eq_add_norm_sq_projection [`x `S]))]
                    "]")
                   [])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["[" [(Tactic.simpLemma [] [] `sq) "," (Tactic.simpLemma [] [] `Mx_decomp)] "]"]
                   [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule
                      []
                      (Term.app
                       `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
                       [(Term.app `L [(Term.app `p1 [`x])])
                        (Term.app `L3 [(Term.app `p2 [`x])])
                        `Mx_orth]))]
                    "]")
                   [])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `LinearIsometry.norm_map)
                     ","
                     (Tactic.simpLemma [] [] `p1)
                     ","
                     (Tactic.simpLemma [] [] `p2)
                     ","
                     (Tactic.simpLemma [] [] `ContinuousLinearMap.to_linear_map_eq_coe)
                     ","
                     (Tactic.simpLemma [] [] `add_left_inj)
                     ","
                     (Tactic.simpLemma [] [] `mul_eq_mul_left_iff)
                     ","
                     (Tactic.simpLemma [] [] `norm_eq_zero)
                     ","
                     (Tactic.simpLemma [] [] `true_or_iff)
                     ","
                     (Tactic.simpLemma [] [] `eq_self_iff_true)
                     ","
                     (Tactic.simpLemma [] [] `ContinuousLinearMap.coe_coe)
                     ","
                     (Tactic.simpLemma [] [] `Submodule.coe_norm)
                     ","
                     (Tactic.simpLemma [] [] `Submodule.coe_eq_zero)]
                    "]"]
                   [])]))))))
           []
           (Tactic.exact
            "exact"
            (Term.structInst
             "{"
             []
             [(Term.structInstField (Term.structInstLVal `toLinearMap []) ":=" `M)
              []
              (Term.structInstField (Term.structInstLVal `norm_map' []) ":=" `M_norm_map)]
             (Term.optEllipsis [])
             []
             "}"))])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `d
             []
             []
             ":="
             (Term.app `finrank [`𝕜 (Analysis.InnerProductSpace.Basic.«term_ᗮ» `S "ᗮ")]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`dim_S_perp []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app `finrank [`𝕜 (Analysis.InnerProductSpace.Basic.«term_ᗮ» `S "ᗮ")])
                "="
                `d))]
             ":="
             `rfl)))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl (Term.letIdDecl `LS [] [] ":=" `L.to_linear_map.range)))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`E []]
             [(Term.typeSpec
               ":"
               (Analysis.NormedSpace.LinearIsometry.«term_≃ₗᵢ[_]_»
                (Analysis.InnerProductSpace.Basic.«term_ᗮ» `S "ᗮ")
                " ≃ₗᵢ["
                `𝕜
                "] "
                (Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Mathlib.Tactic.tacticHave_
                  "have"
                  [`dim_LS_perp []]
                  [(Term.typeSpec
                    ":"
                    («term_=_»
                     (Term.app `finrank [`𝕜 (Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ")])
                     "="
                     `d))])
                 []
                 (calcTactic
                  "calc"
                  (calcStep
                   («term_=_»
                    (Term.app `finrank [`𝕜 (Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ")])
                    "="
                    («term_-_» (Term.app `finrank [`𝕜 `V]) "-" (Term.app `finrank [`𝕜 `LS])))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.simp
                        "simp"
                        []
                        []
                        ["only"]
                        ["["
                         [(Tactic.simpLemma
                           []
                           [(patternIgnore (token.«← » "←"))]
                           `LS.finrank_add_finrank_orthogonal)
                          ","
                          (Tactic.simpLemma [] [] `add_tsub_cancel_left)]
                         "]"]
                        [])]))))
                  [(calcStep
                    («term_=_»
                     (Term.hole "_")
                     "="
                     («term_-_» (Term.app `finrank [`𝕜 `V]) "-" (Term.app `finrank [`𝕜 `S])))
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.simp
                         "simp"
                         []
                         []
                         ["only"]
                         ["["
                          [(Tactic.simpLemma
                            []
                            []
                            (Term.app `LinearMap.finrank_range_of_inj [`L.injective]))]
                          "]"]
                         [])]))))
                   (calcStep
                    («term_=_»
                     (Term.hole "_")
                     "="
                     (Term.app `finrank [`𝕜 (Analysis.InnerProductSpace.Basic.«term_ᗮ» `S "ᗮ")]))
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.simp
                         "simp"
                         []
                         []
                         ["only"]
                         ["["
                          [(Tactic.simpLemma
                            []
                            [(patternIgnore (token.«← » "←"))]
                            `S.finrank_add_finrank_orthogonal)
                           ","
                           (Tactic.simpLemma [] [] `add_tsub_cancel_left)]
                          "]"]
                         [])]))))])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   (Term.proj
                    (Term.proj
                     (Term.app
                      `stdOrthonormalBasis
                      [`𝕜 (Analysis.InnerProductSpace.Basic.«term_ᗮ» `S "ᗮ")])
                     "."
                     `repr)
                    "."
                    `trans)
                   [(Term.proj
                     (Term.proj
                      («term_<|_»
                       (Term.proj
                        (Term.app
                         `stdOrthonormalBasis
                         [`𝕜 (Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ")])
                        "."
                        `reindex)
                       "<|"
                       (Term.app `finCongr [`dim_LS_perp]))
                      "."
                      `repr)
                     "."
                     `symm)]))]))))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `L3
             []
             []
             ":="
             (Term.app
              (Term.proj
               (Term.proj (Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ") "." `subtypeₗᵢ)
               "."
               `comp)
              [`E.to_linear_isometry]))))
          []
          (Std.Tactic.tacticHaveI_
           "haveI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec ":" (Term.app `CompleteSpace [`S]))]
             ":="
             (Term.app `FiniteDimensional.complete [`𝕜 `S]))))
          []
          (Std.Tactic.tacticHaveI_
           "haveI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec ":" (Term.app `CompleteSpace [`V]))]
             ":="
             (Term.app `FiniteDimensional.complete [`𝕜 `V]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `p1
             []
             []
             ":="
             (Term.proj (Term.app `orthogonalProjection [`S]) "." `toLinearMap))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `p2
             []
             []
             ":="
             (Term.proj
              (Term.app `orthogonalProjection [(Analysis.InnerProductSpace.Basic.«term_ᗮ» `S "ᗮ")])
              "."
              `toLinearMap))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `M
             []
             []
             ":="
             («term_+_»
              (Term.app `L.to_linear_map.comp [`p1])
              "+"
              (Term.app `L3.to_linear_map.comp [`p2])))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`M_norm_map []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`x]
                [(Term.typeSpec ":" `V)]
                ","
                («term_=_»
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `M [`x]) "‖")
                 "="
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`x])
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`Mx_decomp []]
                    [(Term.typeSpec
                      ":"
                      («term_=_»
                       (Term.app `M [`x])
                       "="
                       («term_+_»
                        (Term.app `L [(Term.app `p1 [`x])])
                        "+"
                        (Term.app `L3 [(Term.app `p2 [`x])]))))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.simp
                         "simp"
                         []
                         []
                         ["only"]
                         ["["
                          [(Tactic.simpLemma [] [] `LinearMap.add_apply)
                           ","
                           (Tactic.simpLemma [] [] `LinearMap.comp_apply)
                           ","
                           (Tactic.simpLemma [] [] `LinearMap.comp_apply)
                           ","
                           (Tactic.simpLemma [] [] `LinearIsometry.coe_to_linear_map)]
                          "]"]
                         [])]))))))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`Mx_orth []]
                    [(Term.typeSpec
                      ":"
                      («term_=_»
                       (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
                        "⟪"
                        (Term.app `L [(Term.app `p1 [`x])])
                        ", "
                        (Term.app `L3 [(Term.app `p2 [`x])])
                        "⟫")
                       "="
                       (num "0")))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.tacticHave_
                         "have"
                         (Term.haveDecl
                          (Term.haveIdDecl
                           [`Lp1x []]
                           [(Term.typeSpec
                             ":"
                             («term_∈_»
                              (Term.app `L [(Term.app `p1 [`x])])
                              "∈"
                              `L.to_linear_map.range))]
                           ":="
                           (Term.app
                            `LinearMap.mem_range_self
                            [`L.to_linear_map (Term.app `p1 [`x])]))))
                        []
                        (Tactic.tacticHave_
                         "have"
                         (Term.haveDecl
                          (Term.haveIdDecl
                           [`Lp2x []]
                           [(Term.typeSpec
                             ":"
                             («term_∈_»
                              (Term.app `L3 [(Term.app `p2 [`x])])
                              "∈"
                              (Analysis.InnerProductSpace.Basic.«term_ᗮ»
                               `L.to_linear_map.range
                               "ᗮ")))]
                           ":="
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Tactic.simp
                                "simp"
                                []
                                []
                                ["only"]
                                ["["
                                 [(Tactic.simpLemma [] [] `L3)
                                  ","
                                  (Tactic.simpLemma [] [] `LinearIsometry.coe_comp)
                                  ","
                                  (Tactic.simpLemma [] [] `Function.comp_apply)
                                  ","
                                  (Tactic.simpLemma [] [] `Submodule.coe_subtypeₗᵢ)
                                  ","
                                  (Tactic.simpLemma
                                   []
                                   [(patternIgnore (token.«← » "←"))]
                                   (Term.app
                                    `Submodule.range_subtype
                                    [(Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ")]))]
                                 "]"]
                                [])
                               []
                               (Tactic.apply "apply" `LinearMap.mem_range_self)]))))))
                        []
                        (Tactic.apply
                         "apply"
                         (Term.app `Submodule.inner_right_of_mem_orthogonal [`Lp1x `Lp2x]))]))))))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app
                      `sq_eq_sq
                      [(Term.app `norm_nonneg [(Term.hole "_")])
                       (Term.app `norm_nonneg [(Term.hole "_")])]))
                    ","
                    (Tactic.rwRule [] (Term.app `norm_sq_eq_add_norm_sq_projection [`x `S]))]
                   "]")
                  [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["[" [(Tactic.simpLemma [] [] `sq) "," (Tactic.simpLemma [] [] `Mx_decomp)] "]"]
                  [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     []
                     (Term.app
                      `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
                      [(Term.app `L [(Term.app `p1 [`x])])
                       (Term.app `L3 [(Term.app `p2 [`x])])
                       `Mx_orth]))]
                   "]")
                  [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `LinearIsometry.norm_map)
                    ","
                    (Tactic.simpLemma [] [] `p1)
                    ","
                    (Tactic.simpLemma [] [] `p2)
                    ","
                    (Tactic.simpLemma [] [] `ContinuousLinearMap.to_linear_map_eq_coe)
                    ","
                    (Tactic.simpLemma [] [] `add_left_inj)
                    ","
                    (Tactic.simpLemma [] [] `mul_eq_mul_left_iff)
                    ","
                    (Tactic.simpLemma [] [] `norm_eq_zero)
                    ","
                    (Tactic.simpLemma [] [] `true_or_iff)
                    ","
                    (Tactic.simpLemma [] [] `eq_self_iff_true)
                    ","
                    (Tactic.simpLemma [] [] `ContinuousLinearMap.coe_coe)
                    ","
                    (Tactic.simpLemma [] [] `Submodule.coe_norm)
                    ","
                    (Tactic.simpLemma [] [] `Submodule.coe_eq_zero)]
                   "]"]
                  [])]))))))
          []
          (Tactic.exact
           "exact"
           (Term.structInst
            "{"
            []
            [(Term.structInstField (Term.structInstLVal `toLinearMap []) ":=" `M)
             []
             (Term.structInstField (Term.structInstLVal `norm_map' []) ":=" `M_norm_map)]
            (Term.optEllipsis [])
            []
            "}"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.structInst
        "{"
        []
        [(Term.structInstField (Term.structInstLVal `toLinearMap []) ":=" `M)
         []
         (Term.structInstField (Term.structInstLVal `norm_map' []) ":=" `M_norm_map)]
        (Term.optEllipsis [])
        []
        "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField (Term.structInstLVal `toLinearMap []) ":=" `M)
        []
        (Term.structInstField (Term.structInstLVal `norm_map' []) ":=" `M_norm_map)]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `M_norm_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `M
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`M_norm_map []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`x]
            [(Term.typeSpec ":" `V)]
            ","
            («term_=_»
             (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `M [`x]) "‖")
             "="
             (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`x])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`Mx_decomp []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Term.app `M [`x])
                   "="
                   («term_+_»
                    (Term.app `L [(Term.app `p1 [`x])])
                    "+"
                    (Term.app `L3 [(Term.app `p2 [`x])]))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.simp
                     "simp"
                     []
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `LinearMap.add_apply)
                       ","
                       (Tactic.simpLemma [] [] `LinearMap.comp_apply)
                       ","
                       (Tactic.simpLemma [] [] `LinearMap.comp_apply)
                       ","
                       (Tactic.simpLemma [] [] `LinearIsometry.coe_to_linear_map)]
                      "]"]
                     [])]))))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`Mx_orth []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
                    "⟪"
                    (Term.app `L [(Term.app `p1 [`x])])
                    ", "
                    (Term.app `L3 [(Term.app `p2 [`x])])
                    "⟫")
                   "="
                   (num "0")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`Lp1x []]
                       [(Term.typeSpec
                         ":"
                         («term_∈_»
                          (Term.app `L [(Term.app `p1 [`x])])
                          "∈"
                          `L.to_linear_map.range))]
                       ":="
                       (Term.app
                        `LinearMap.mem_range_self
                        [`L.to_linear_map (Term.app `p1 [`x])]))))
                    []
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`Lp2x []]
                       [(Term.typeSpec
                         ":"
                         («term_∈_»
                          (Term.app `L3 [(Term.app `p2 [`x])])
                          "∈"
                          (Analysis.InnerProductSpace.Basic.«term_ᗮ» `L.to_linear_map.range "ᗮ")))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.simp
                            "simp"
                            []
                            []
                            ["only"]
                            ["["
                             [(Tactic.simpLemma [] [] `L3)
                              ","
                              (Tactic.simpLemma [] [] `LinearIsometry.coe_comp)
                              ","
                              (Tactic.simpLemma [] [] `Function.comp_apply)
                              ","
                              (Tactic.simpLemma [] [] `Submodule.coe_subtypeₗᵢ)
                              ","
                              (Tactic.simpLemma
                               []
                               [(patternIgnore (token.«← » "←"))]
                               (Term.app
                                `Submodule.range_subtype
                                [(Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ")]))]
                             "]"]
                            [])
                           []
                           (Tactic.apply "apply" `LinearMap.mem_range_self)]))))))
                    []
                    (Tactic.apply
                     "apply"
                     (Term.app `Submodule.inner_right_of_mem_orthogonal [`Lp1x `Lp2x]))]))))))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app
                  `sq_eq_sq
                  [(Term.app `norm_nonneg [(Term.hole "_")])
                   (Term.app `norm_nonneg [(Term.hole "_")])]))
                ","
                (Tactic.rwRule [] (Term.app `norm_sq_eq_add_norm_sq_projection [`x `S]))]
               "]")
              [])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `sq) "," (Tactic.simpLemma [] [] `Mx_decomp)] "]"]
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.app
                  `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
                  [(Term.app `L [(Term.app `p1 [`x])])
                   (Term.app `L3 [(Term.app `p2 [`x])])
                   `Mx_orth]))]
               "]")
              [])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `LinearIsometry.norm_map)
                ","
                (Tactic.simpLemma [] [] `p1)
                ","
                (Tactic.simpLemma [] [] `p2)
                ","
                (Tactic.simpLemma [] [] `ContinuousLinearMap.to_linear_map_eq_coe)
                ","
                (Tactic.simpLemma [] [] `add_left_inj)
                ","
                (Tactic.simpLemma [] [] `mul_eq_mul_left_iff)
                ","
                (Tactic.simpLemma [] [] `norm_eq_zero)
                ","
                (Tactic.simpLemma [] [] `true_or_iff)
                ","
                (Tactic.simpLemma [] [] `eq_self_iff_true)
                ","
                (Tactic.simpLemma [] [] `ContinuousLinearMap.coe_coe)
                ","
                (Tactic.simpLemma [] [] `Submodule.coe_norm)
                ","
                (Tactic.simpLemma [] [] `Submodule.coe_eq_zero)]
               "]"]
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`x])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`Mx_decomp []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app `M [`x])
                "="
                («term_+_»
                 (Term.app `L [(Term.app `p1 [`x])])
                 "+"
                 (Term.app `L3 [(Term.app `p2 [`x])]))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `LinearMap.add_apply)
                    ","
                    (Tactic.simpLemma [] [] `LinearMap.comp_apply)
                    ","
                    (Tactic.simpLemma [] [] `LinearMap.comp_apply)
                    ","
                    (Tactic.simpLemma [] [] `LinearIsometry.coe_to_linear_map)]
                   "]"]
                  [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`Mx_orth []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
                 "⟪"
                 (Term.app `L [(Term.app `p1 [`x])])
                 ", "
                 (Term.app `L3 [(Term.app `p2 [`x])])
                 "⟫")
                "="
                (num "0")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`Lp1x []]
                    [(Term.typeSpec
                      ":"
                      («term_∈_» (Term.app `L [(Term.app `p1 [`x])]) "∈" `L.to_linear_map.range))]
                    ":="
                    (Term.app `LinearMap.mem_range_self [`L.to_linear_map (Term.app `p1 [`x])]))))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`Lp2x []]
                    [(Term.typeSpec
                      ":"
                      («term_∈_»
                       (Term.app `L3 [(Term.app `p2 [`x])])
                       "∈"
                       (Analysis.InnerProductSpace.Basic.«term_ᗮ» `L.to_linear_map.range "ᗮ")))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.simp
                         "simp"
                         []
                         []
                         ["only"]
                         ["["
                          [(Tactic.simpLemma [] [] `L3)
                           ","
                           (Tactic.simpLemma [] [] `LinearIsometry.coe_comp)
                           ","
                           (Tactic.simpLemma [] [] `Function.comp_apply)
                           ","
                           (Tactic.simpLemma [] [] `Submodule.coe_subtypeₗᵢ)
                           ","
                           (Tactic.simpLemma
                            []
                            [(patternIgnore (token.«← » "←"))]
                            (Term.app
                             `Submodule.range_subtype
                             [(Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ")]))]
                          "]"]
                         [])
                        []
                        (Tactic.apply "apply" `LinearMap.mem_range_self)]))))))
                 []
                 (Tactic.apply
                  "apply"
                  (Term.app `Submodule.inner_right_of_mem_orthogonal [`Lp1x `Lp2x]))]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `sq_eq_sq
               [(Term.app `norm_nonneg [(Term.hole "_")])
                (Term.app `norm_nonneg [(Term.hole "_")])]))
             ","
             (Tactic.rwRule [] (Term.app `norm_sq_eq_add_norm_sq_projection [`x `S]))]
            "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `sq) "," (Tactic.simpLemma [] [] `Mx_decomp)] "]"]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
               [(Term.app `L [(Term.app `p1 [`x])])
                (Term.app `L3 [(Term.app `p2 [`x])])
                `Mx_orth]))]
            "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `LinearIsometry.norm_map)
             ","
             (Tactic.simpLemma [] [] `p1)
             ","
             (Tactic.simpLemma [] [] `p2)
             ","
             (Tactic.simpLemma [] [] `ContinuousLinearMap.to_linear_map_eq_coe)
             ","
             (Tactic.simpLemma [] [] `add_left_inj)
             ","
             (Tactic.simpLemma [] [] `mul_eq_mul_left_iff)
             ","
             (Tactic.simpLemma [] [] `norm_eq_zero)
             ","
             (Tactic.simpLemma [] [] `true_or_iff)
             ","
             (Tactic.simpLemma [] [] `eq_self_iff_true)
             ","
             (Tactic.simpLemma [] [] `ContinuousLinearMap.coe_coe)
             ","
             (Tactic.simpLemma [] [] `Submodule.coe_norm)
             ","
             (Tactic.simpLemma [] [] `Submodule.coe_eq_zero)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `LinearIsometry.norm_map)
         ","
         (Tactic.simpLemma [] [] `p1)
         ","
         (Tactic.simpLemma [] [] `p2)
         ","
         (Tactic.simpLemma [] [] `ContinuousLinearMap.to_linear_map_eq_coe)
         ","
         (Tactic.simpLemma [] [] `add_left_inj)
         ","
         (Tactic.simpLemma [] [] `mul_eq_mul_left_iff)
         ","
         (Tactic.simpLemma [] [] `norm_eq_zero)
         ","
         (Tactic.simpLemma [] [] `true_or_iff)
         ","
         (Tactic.simpLemma [] [] `eq_self_iff_true)
         ","
         (Tactic.simpLemma [] [] `ContinuousLinearMap.coe_coe)
         ","
         (Tactic.simpLemma [] [] `Submodule.coe_norm)
         ","
         (Tactic.simpLemma [] [] `Submodule.coe_eq_zero)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.coe_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.coe_norm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ContinuousLinearMap.coe_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_self_iff_true
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `true_or_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_eq_mul_left_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_left_inj
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ContinuousLinearMap.to_linear_map_eq_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearIsometry.norm_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app
           `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
           [(Term.app `L [(Term.app `p1 [`x])]) (Term.app `L3 [(Term.app `p2 [`x])]) `Mx_orth]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
       [(Term.app `L [(Term.app `p1 [`x])]) (Term.app `L3 [(Term.app `p2 [`x])]) `Mx_orth])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Mx_orth
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `L3 [(Term.app `p2 [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p2 [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p2
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `p2 [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `L3
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `L3 [(Term.paren "(" (Term.app `p2 [`x]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `L [(Term.app `p1 [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p1 [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `p1 [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `L
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `L [(Term.paren "(" (Term.app `p1 [`x]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [] `sq) "," (Tactic.simpLemma [] [] `Mx_decomp)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Mx_decomp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `sq_eq_sq
           [(Term.app `norm_nonneg [(Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])]))
         ","
         (Tactic.rwRule [] (Term.app `norm_sq_eq_add_norm_sq_projection [`x `S]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_sq_eq_add_norm_sq_projection [`x `S])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_sq_eq_add_norm_sq_projection
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `sq_eq_sq
       [(Term.app `norm_nonneg [(Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `norm_nonneg [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `norm_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `norm_nonneg [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sq_eq_sq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`Mx_orth []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
             "⟪"
             (Term.app `L [(Term.app `p1 [`x])])
             ", "
             (Term.app `L3 [(Term.app `p2 [`x])])
             "⟫")
            "="
            (num "0")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`Lp1x []]
                [(Term.typeSpec
                  ":"
                  («term_∈_» (Term.app `L [(Term.app `p1 [`x])]) "∈" `L.to_linear_map.range))]
                ":="
                (Term.app `LinearMap.mem_range_self [`L.to_linear_map (Term.app `p1 [`x])]))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`Lp2x []]
                [(Term.typeSpec
                  ":"
                  («term_∈_»
                   (Term.app `L3 [(Term.app `p2 [`x])])
                   "∈"
                   (Analysis.InnerProductSpace.Basic.«term_ᗮ» `L.to_linear_map.range "ᗮ")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.simp
                     "simp"
                     []
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `L3)
                       ","
                       (Tactic.simpLemma [] [] `LinearIsometry.coe_comp)
                       ","
                       (Tactic.simpLemma [] [] `Function.comp_apply)
                       ","
                       (Tactic.simpLemma [] [] `Submodule.coe_subtypeₗᵢ)
                       ","
                       (Tactic.simpLemma
                        []
                        [(patternIgnore (token.«← » "←"))]
                        (Term.app
                         `Submodule.range_subtype
                         [(Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ")]))]
                      "]"]
                     [])
                    []
                    (Tactic.apply "apply" `LinearMap.mem_range_self)]))))))
             []
             (Tactic.apply
              "apply"
              (Term.app `Submodule.inner_right_of_mem_orthogonal [`Lp1x `Lp2x]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`Lp1x []]
             [(Term.typeSpec
               ":"
               («term_∈_» (Term.app `L [(Term.app `p1 [`x])]) "∈" `L.to_linear_map.range))]
             ":="
             (Term.app `LinearMap.mem_range_self [`L.to_linear_map (Term.app `p1 [`x])]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`Lp2x []]
             [(Term.typeSpec
               ":"
               («term_∈_»
                (Term.app `L3 [(Term.app `p2 [`x])])
                "∈"
                (Analysis.InnerProductSpace.Basic.«term_ᗮ» `L.to_linear_map.range "ᗮ")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `L3)
                    ","
                    (Tactic.simpLemma [] [] `LinearIsometry.coe_comp)
                    ","
                    (Tactic.simpLemma [] [] `Function.comp_apply)
                    ","
                    (Tactic.simpLemma [] [] `Submodule.coe_subtypeₗᵢ)
                    ","
                    (Tactic.simpLemma
                     []
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app
                      `Submodule.range_subtype
                      [(Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ")]))]
                   "]"]
                  [])
                 []
                 (Tactic.apply "apply" `LinearMap.mem_range_self)]))))))
          []
          (Tactic.apply
           "apply"
           (Term.app `Submodule.inner_right_of_mem_orthogonal [`Lp1x `Lp2x]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.app `Submodule.inner_right_of_mem_orthogonal [`Lp1x `Lp2x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Submodule.inner_right_of_mem_orthogonal [`Lp1x `Lp2x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Lp2x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Lp1x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Submodule.inner_right_of_mem_orthogonal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`Lp2x []]
         [(Term.typeSpec
           ":"
           («term_∈_»
            (Term.app `L3 [(Term.app `p2 [`x])])
            "∈"
            (Analysis.InnerProductSpace.Basic.«term_ᗮ» `L.to_linear_map.range "ᗮ")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `L3)
                ","
                (Tactic.simpLemma [] [] `LinearIsometry.coe_comp)
                ","
                (Tactic.simpLemma [] [] `Function.comp_apply)
                ","
                (Tactic.simpLemma [] [] `Submodule.coe_subtypeₗᵢ)
                ","
                (Tactic.simpLemma
                 []
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app
                  `Submodule.range_subtype
                  [(Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ")]))]
               "]"]
              [])
             []
             (Tactic.apply "apply" `LinearMap.mem_range_self)]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `L3)
             ","
             (Tactic.simpLemma [] [] `LinearIsometry.coe_comp)
             ","
             (Tactic.simpLemma [] [] `Function.comp_apply)
             ","
             (Tactic.simpLemma [] [] `Submodule.coe_subtypeₗᵢ)
             ","
             (Tactic.simpLemma
              []
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `Submodule.range_subtype
               [(Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ")]))]
            "]"]
           [])
          []
          (Tactic.apply "apply" `LinearMap.mem_range_self)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `LinearMap.mem_range_self)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.mem_range_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `L3)
         ","
         (Tactic.simpLemma [] [] `LinearIsometry.coe_comp)
         ","
         (Tactic.simpLemma [] [] `Function.comp_apply)
         ","
         (Tactic.simpLemma [] [] `Submodule.coe_subtypeₗᵢ)
         ","
         (Tactic.simpLemma
          []
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `Submodule.range_subtype
           [(Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ")]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Submodule.range_subtype [(Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Basic.«term_ᗮ»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Basic.«term_ᗮ»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Basic.«term_ᗮ» `LS "ᗮ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1200, term))
      `LS
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1200, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1200, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Submodule.range_subtype
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.coe_subtypeₗᵢ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Function.comp_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearIsometry.coe_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `L3
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       (Term.app `L3 [(Term.app `p2 [`x])])
       "∈"
       (Analysis.InnerProductSpace.Basic.«term_ᗮ» `L.to_linear_map.range "ᗮ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Basic.«term_ᗮ» `L.to_linear_map.range "ᗮ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1200, term))
      `L.to_linear_map.range
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1200, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1200, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `L3 [(Term.app `p2 [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p2 [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p2
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `p2 [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `L3
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`Lp1x []]
         [(Term.typeSpec
           ":"
           («term_∈_» (Term.app `L [(Term.app `p1 [`x])]) "∈" `L.to_linear_map.range))]
         ":="
         (Term.app `LinearMap.mem_range_self [`L.to_linear_map (Term.app `p1 [`x])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `LinearMap.mem_range_self [`L.to_linear_map (Term.app `p1 [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p1 [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `p1 [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `L.to_linear_map
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LinearMap.mem_range_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» (Term.app `L [(Term.app `p1 [`x])]) "∈" `L.to_linear_map.range)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `L.to_linear_map.range
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `L [(Term.app `p1 [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p1 [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `p1 [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `L
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
        "⟪"
        (Term.app `L [(Term.app `p1 [`x])])
        ", "
        (Term.app `L3 [(Term.app `p2 [`x])])
        "⟫")
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»
       "⟪"
       (Term.app `L [(Term.app `p1 [`x])])
       ", "
       (Term.app `L3 [(Term.app `p2 [`x])])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.PiL2.term⟪_,_⟫._@.Analysis.InnerProductSpace.PiL2._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Let `S` be a subspace of a finite-dimensional complex inner product space `V`.  A linear
      isometry mapping `S` into `V` can be extended to a full isometry of `V`.
      
      TODO:  The case when `S` is a finite-dimensional subspace of an infinite-dimensional `V`.-/
    noncomputable
  def
    LinearIsometry.extend
    ( L : S →ₗᵢ[ 𝕜 ] V ) : V →ₗᵢ[ 𝕜 ] V
    :=
      by
        let d := finrank 𝕜 S ᗮ
          have dim_S_perp : finrank 𝕜 S ᗮ = d := rfl
          let LS := L.to_linear_map.range
          have
            E
              : S ᗮ ≃ₗᵢ[ 𝕜 ] LS ᗮ
              :=
              by
                have dim_LS_perp : finrank 𝕜 LS ᗮ = d
                  calc
                    finrank 𝕜 LS ᗮ = finrank 𝕜 V - finrank 𝕜 LS
                      :=
                      by simp only [ ← LS.finrank_add_finrank_orthogonal , add_tsub_cancel_left ]
                    _ = finrank 𝕜 V - finrank 𝕜 S
                        :=
                        by simp only [ LinearMap.finrank_range_of_inj L.injective ]
                      _ = finrank 𝕜 S ᗮ
                        :=
                        by simp only [ ← S.finrank_add_finrank_orthogonal , add_tsub_cancel_left ]
                  exact
                    stdOrthonormalBasis 𝕜 S ᗮ . repr . trans
                      stdOrthonormalBasis 𝕜 LS ᗮ . reindex <| finCongr dim_LS_perp . repr . symm
          let L3 := LS ᗮ . subtypeₗᵢ . comp E.to_linear_isometry
          haveI : CompleteSpace S := FiniteDimensional.complete 𝕜 S
          haveI : CompleteSpace V := FiniteDimensional.complete 𝕜 V
          let p1 := orthogonalProjection S . toLinearMap
          let p2 := orthogonalProjection S ᗮ . toLinearMap
          let M := L.to_linear_map.comp p1 + L3.to_linear_map.comp p2
          have
            M_norm_map
              : ∀ x : V , ‖ M x ‖ = ‖ x ‖
              :=
              by
                intro x
                  have
                    Mx_decomp
                      : M x = L p1 x + L3 p2 x
                      :=
                      by
                        simp
                          only
                          [
                            LinearMap.add_apply
                              ,
                              LinearMap.comp_apply
                              ,
                              LinearMap.comp_apply
                              ,
                              LinearIsometry.coe_to_linear_map
                            ]
                  have
                    Mx_orth
                      : ⟪ L p1 x , L3 p2 x ⟫ = 0
                      :=
                      by
                        have
                            Lp1x
                              : L p1 x ∈ L.to_linear_map.range
                              :=
                              LinearMap.mem_range_self L.to_linear_map p1 x
                          have
                            Lp2x
                              : L3 p2 x ∈ L.to_linear_map.range ᗮ
                              :=
                              by
                                simp
                                    only
                                    [
                                      L3
                                        ,
                                        LinearIsometry.coe_comp
                                        ,
                                        Function.comp_apply
                                        ,
                                        Submodule.coe_subtypeₗᵢ
                                        ,
                                        ← Submodule.range_subtype LS ᗮ
                                      ]
                                  apply LinearMap.mem_range_self
                          apply Submodule.inner_right_of_mem_orthogonal Lp1x Lp2x
                  rw
                    [
                      ← sq_eq_sq norm_nonneg _ norm_nonneg _ , norm_sq_eq_add_norm_sq_projection x S
                      ]
                  simp only [ sq , Mx_decomp ]
                  rw [ norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero L p1 x L3 p2 x Mx_orth ]
                  simp
                    only
                    [
                      LinearIsometry.norm_map
                        ,
                        p1
                        ,
                        p2
                        ,
                        ContinuousLinearMap.to_linear_map_eq_coe
                        ,
                        add_left_inj
                        ,
                        mul_eq_mul_left_iff
                        ,
                        norm_eq_zero
                        ,
                        true_or_iff
                        ,
                        eq_self_iff_true
                        ,
                        ContinuousLinearMap.coe_coe
                        ,
                        Submodule.coe_norm
                        ,
                        Submodule.coe_eq_zero
                      ]
          exact { toLinearMap := M norm_map' := M_norm_map }
#align linear_isometry.extend LinearIsometry.extend

theorem LinearIsometry.extend_apply (L : S →ₗᵢ[𝕜] V) (s : S) : L.extend s = L s :=
  by
  haveI : CompleteSpace S := FiniteDimensional.complete 𝕜 S
  simp only [LinearIsometry.extend, ContinuousLinearMap.to_linear_map_eq_coe, ←
    LinearIsometry.coe_to_linear_map]
  simp only [add_right_eq_self, LinearIsometry.coe_to_linear_map,
    LinearIsometryEquiv.coe_to_linear_isometry, LinearIsometry.coe_comp, Function.comp_apply,
    orthogonal_projection_mem_subspace_eq_self, LinearMap.coe_comp, ContinuousLinearMap.coe_coe,
    Submodule.coe_subtype, LinearMap.add_apply, Submodule.coe_eq_zero,
    LinearIsometryEquiv.map_eq_zero_iff, Submodule.coe_subtypeₗᵢ,
    orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero,
    Submodule.orthogonal_orthogonal, Submodule.coe_mem]
#align linear_isometry.extend_apply LinearIsometry.extend_apply

end LinearIsometry

section Matrix

open Matrix

variable {n m : ℕ}

-- mathport name: «expr⟪ , ⟫ₘ»
local notation "⟪" x ", " y "⟫ₘ" => @inner 𝕜 (EuclideanSpace 𝕜 (Fin m)) _ x y

-- mathport name: «expr⟪ , ⟫ₙ»
local notation "⟪" x ", " y "⟫ₙ" => @inner 𝕜 (EuclideanSpace 𝕜 (Fin n)) _ x y

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The inner product of a row of A and a row of B is an entry of B ⬝ Aᴴ. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_matrix_row_row [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`A `B]
         [":" (Term.app `Matrix [(Term.app `Fin [`n]) (Term.app `Fin [`m]) `𝕜])]
         []
         ")")
        (Term.explicitBinder "(" [`i `j] [":" (Term.app `Fin [`n])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫ₘ»
          "⟪"
          (Term.app `A [`i])
          ", "
          (Term.app `B [`j])
          "⟫ₘ")
         "="
         (Term.app
          (Matrix.Data.Matrix.Basic.matrix.mul
           `B
           " ⬝ "
           (Matrix.Data.Matrix.Basic.matrix.conj_transpose `A "ᴴ"))
          [`j `i]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `inner)
              ","
              (Tactic.simpLemma [] [] `Matrix.mul_apply)
              ","
              (Tactic.simpLemma [] [] `star_ring_end_apply)
              ","
              (Tactic.simpLemma [] [] `Matrix.conj_transpose_apply)
              ","
              (Tactic.simpLemma [] [] `mul_comm)]
             "]"]
            [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `inner)
             ","
             (Tactic.simpLemma [] [] `Matrix.mul_apply)
             ","
             (Tactic.simpLemma [] [] `star_ring_end_apply)
             ","
             (Tactic.simpLemma [] [] `Matrix.conj_transpose_apply)
             ","
             (Tactic.simpLemma [] [] `mul_comm)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `inner)
         ","
         (Tactic.simpLemma [] [] `Matrix.mul_apply)
         ","
         (Tactic.simpLemma [] [] `star_ring_end_apply)
         ","
         (Tactic.simpLemma [] [] `Matrix.conj_transpose_apply)
         ","
         (Tactic.simpLemma [] [] `mul_comm)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.conj_transpose_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `star_ring_end_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.mul_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫ₘ»
        "⟪"
        (Term.app `A [`i])
        ", "
        (Term.app `B [`j])
        "⟫ₘ")
       "="
       (Term.app
        (Matrix.Data.Matrix.Basic.matrix.mul
         `B
         " ⬝ "
         (Matrix.Data.Matrix.Basic.matrix.conj_transpose `A "ᴴ"))
        [`j `i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Matrix.Data.Matrix.Basic.matrix.mul
        `B
        " ⬝ "
        (Matrix.Data.Matrix.Basic.matrix.conj_transpose `A "ᴴ"))
       [`j `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Matrix.Data.Matrix.Basic.matrix.mul
       `B
       " ⬝ "
       (Matrix.Data.Matrix.Basic.matrix.conj_transpose `A "ᴴ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Matrix.Data.Matrix.Basic.matrix.conj_transpose `A "ᴴ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 76 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      `B
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 75, (some 76, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Matrix.Data.Matrix.Basic.matrix.mul
      `B
      " ⬝ "
      (Matrix.Data.Matrix.Basic.matrix.conj_transpose `A "ᴴ"))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫ₘ»
       "⟪"
       (Term.app `A [`i])
       ", "
       (Term.app `B [`j])
       "⟫ₘ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫ₘ»', expected 'Analysis.InnerProductSpace.PiL2.term⟪_,_⟫ₘ._@.Analysis.InnerProductSpace.PiL2._hyg.102'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The inner product of a row of A and a row of B is an entry of B ⬝ Aᴴ. -/
  theorem
    inner_matrix_row_row
    ( A B : Matrix Fin n Fin m 𝕜 ) ( i j : Fin n ) : ⟪ A i , B j ⟫ₘ = B ⬝ A ᴴ j i
    :=
      by
        simp
          only
          [
            inner , Matrix.mul_apply , star_ring_end_apply , Matrix.conj_transpose_apply , mul_comm
            ]
#align inner_matrix_row_row inner_matrix_row_row

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The inner product of a column of A and a column of B is an entry of Aᴴ ⬝ B -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_matrix_col_col [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`A `B]
         [":" (Term.app `Matrix [(Term.app `Fin [`n]) (Term.app `Fin [`m]) `𝕜])]
         []
         ")")
        (Term.explicitBinder "(" [`i `j] [":" (Term.app `Fin [`m])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫ₙ»
          "⟪"
          (Term.app (Matrix.Data.Matrix.Basic.matrix.transpose `A "ᵀ") [`i])
          ", "
          (Term.app (Matrix.Data.Matrix.Basic.matrix.transpose `B "ᵀ") [`j])
          "⟫ₙ")
         "="
         (Term.app
          (Matrix.Data.Matrix.Basic.matrix.mul
           (Matrix.Data.Matrix.Basic.matrix.conj_transpose `A "ᴴ")
           " ⬝ "
           `B)
          [`i `j]))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫ₙ»
        "⟪"
        (Term.app (Matrix.Data.Matrix.Basic.matrix.transpose `A "ᵀ") [`i])
        ", "
        (Term.app (Matrix.Data.Matrix.Basic.matrix.transpose `B "ᵀ") [`j])
        "⟫ₙ")
       "="
       (Term.app
        (Matrix.Data.Matrix.Basic.matrix.mul
         (Matrix.Data.Matrix.Basic.matrix.conj_transpose `A "ᴴ")
         " ⬝ "
         `B)
        [`i `j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Matrix.Data.Matrix.Basic.matrix.mul
        (Matrix.Data.Matrix.Basic.matrix.conj_transpose `A "ᴴ")
        " ⬝ "
        `B)
       [`i `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Matrix.Data.Matrix.Basic.matrix.mul
       (Matrix.Data.Matrix.Basic.matrix.conj_transpose `A "ᴴ")
       " ⬝ "
       `B)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B
[PrettyPrinter.parenthesize] ...precedences are 76 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      (Matrix.Data.Matrix.Basic.matrix.conj_transpose `A "ᴴ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 75, (some 76, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Matrix.Data.Matrix.Basic.matrix.mul
      (Matrix.Data.Matrix.Basic.matrix.conj_transpose `A "ᴴ")
      " ⬝ "
      `B)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫ₙ»
       "⟪"
       (Term.app (Matrix.Data.Matrix.Basic.matrix.transpose `A "ᵀ") [`i])
       ", "
       (Term.app (Matrix.Data.Matrix.Basic.matrix.transpose `B "ᵀ") [`j])
       "⟫ₙ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.PiL2.«term⟪_,_⟫ₙ»', expected 'Analysis.InnerProductSpace.PiL2.term⟪_,_⟫ₙ._@.Analysis.InnerProductSpace.PiL2._hyg.157'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The inner product of a column of A and a column of B is an entry of Aᴴ ⬝ B -/
  theorem
    inner_matrix_col_col
    ( A B : Matrix Fin n Fin m 𝕜 ) ( i j : Fin m ) : ⟪ A ᵀ i , B ᵀ j ⟫ₙ = A ᴴ ⬝ B i j
    := rfl
#align inner_matrix_col_col inner_matrix_col_col

end Matrix

