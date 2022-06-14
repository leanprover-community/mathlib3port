/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.FieldTheory.PrimitiveElement
import Mathbin.LinearAlgebra.Determinant
import Mathbin.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathbin.LinearAlgebra.Matrix.ToLinearEquiv
import Mathbin.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Norm for (finite) ring extensions

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the determinant of the linear map given by multiplying by `s` gives information
about the roots of the minimal polynomial of `s` over `R`.

## Implementation notes

Typically, the norm is defined specifically for finite field extensions.
The current definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the norm for left multiplication (`algebra.left_mul_matrix`,
i.e. `algebra.lmul_left`).
For now, the definitions assume `S` is commutative, so the choice doesn't
matter anyway.

See also `algebra.trace`, which is defined similarly as the trace of
`algebra.left_mul_matrix`.

## References

 * https://en.wikipedia.org/wiki/Field_norm

-/


universe u v w

variable {R S T : Type _} [CommRingₓ R] [CommRingₓ S]

variable [Algebra R S]

variable {K L F : Type _} [Field K] [Field L] [Field F]

variable [Algebra K L] [Algebra K F]

variable {ι : Type w} [Fintype ι]

open FiniteDimensional

open LinearMap

open Matrix Polynomial

open BigOperators

open Matrix

namespace Algebra

variable (R)

/-- The norm of an element `s` of an `R`-algebra is the determinant of `(*) s`. -/
noncomputable def norm : S →* R :=
  LinearMap.det.comp (lmul R S).toRingHom.toMonoidHom

theorem norm_apply (x : S) : norm R x = LinearMap.det (lmul R S x) :=
  rfl

theorem norm_eq_one_of_not_exists_basis (h : ¬∃ s : Finset S, Nonempty (Basis s R S)) (x : S) : norm R x = 1 := by
  rw [norm_apply, LinearMap.det]
  split_ifs with h
  rfl

variable {R}

-- Can't be a `simp` lemma because it depends on a choice of basis
theorem norm_eq_matrix_det [DecidableEq ι] (b : Basis ι R S) (s : S) :
    norm R s = Matrix.det (Algebra.leftMulMatrix b s) := by
  rw [norm_apply, ← LinearMap.det_to_matrix b, to_matrix_lmul_eq]

/-- If `x` is in the base field `K`, then the norm is `x ^ [L : K]`. -/
theorem norm_algebra_map_of_basis (b : Basis ι R S) (x : R) : norm R (algebraMap R S x) = x ^ Fintype.card ι := by
  have := Classical.decEq ι
  rw [norm_apply, ← det_to_matrix b, lmul_algebra_map]
  convert @det_diagonal _ _ _ _ _ fun i : ι => x
  · ext i j
    rw [to_matrix_lsmul, Matrix.diagonalₓ]
    
  · rw [Finset.prod_const, Finset.card_univ]
    

/-- If `x` is in the base field `K`, then the norm is `x ^ [L : K]`.

(If `L` is not finite-dimensional over `K`, then `norm = 1 = x ^ 0 = x ^ (finrank L K)`.)
-/
@[simp]
protected theorem norm_algebra_map (x : K) : norm K (algebraMap K L x) = x ^ finrank K L := by
  by_cases' H : ∃ s : Finset L, Nonempty (Basis s K L)
  · rw [norm_algebra_map_of_basis H.some_spec.some, finrank_eq_card_basis H.some_spec.some]
    
  · rw [norm_eq_one_of_not_exists_basis K H, finrank_eq_zero_of_not_exists_basis, pow_zeroₓ]
    rintro ⟨s, ⟨b⟩⟩
    exact H ⟨s, ⟨b⟩⟩
    

section EqProdRoots

/-- Given `pb : power_basis K S`, then the norm of `pb.gen` is
`(-1) ^ pb.dim * coeff (minpoly K pb.gen) 0`. -/
theorem PowerBasis.norm_gen_eq_coeff_zero_minpoly [Algebra K S] (pb : PowerBasis K S) :
    norm K pb.gen = -1 ^ pb.dim * coeff (minpoly K pb.gen) 0 := by
  rw [norm_eq_matrix_det pb.basis, det_eq_sign_charpoly_coeff, charpoly_left_mul_matrix, Fintype.card_fin]

/-- Given `pb : power_basis K S`, then the norm of `pb.gen` is
`((minpoly K pb.gen).map (algebra_map K F)).roots.prod`. -/
theorem PowerBasis.norm_gen_eq_prod_roots [Algebra K S] (pb : PowerBasis K S)
    (hf : (minpoly K pb.gen).Splits (algebraMap K F)) :
    algebraMap K F (norm K pb.gen) = ((minpoly K pb.gen).map (algebraMap K F)).roots.Prod := by
  rw [power_basis.norm_gen_eq_coeff_zero_minpoly, ← pb.nat_degree_minpoly, RingHom.map_mul, ← coeff_map,
    prod_roots_eq_coeff_zero_of_monic_of_split ((minpoly.monic (PowerBasis.is_integral_gen _)).map _)
      ((splits_id_iff_splits _).2 hf),
    nat_degree_map, map_pow, ← mul_assoc, ← mul_powₓ]
  simp

end EqProdRoots

section EqZeroIff

theorem norm_eq_zero_iff_of_basis [IsDomain R] [IsDomain S] (b : Basis ι R S) {x : S} : Algebra.norm R x = 0 ↔ x = 0 :=
  by
  have hι : Nonempty ι := b.index_nonempty
  let this := Classical.decEq ι
  rw [Algebra.norm_eq_matrix_det b]
  constructor
  · rw [← Matrix.exists_mul_vec_eq_zero_iff]
    rintro ⟨v, v_ne, hv⟩
    rw [← b.equiv_fun.apply_symm_apply v, b.equiv_fun_symm_apply, b.equiv_fun_apply,
      Algebra.left_mul_matrix_mul_vec_repr] at hv
    refine' (mul_eq_zero.mp (b.ext_elem fun i => _)).resolve_right (show (∑ i, v i • b i) ≠ 0 from _)
    · simpa only [LinearEquiv.map_zero, Pi.zero_apply] using congr_fun hv i
      
    · contrapose! v_ne with sum_eq
      apply b.equiv_fun.symm.injective
      rw [b.equiv_fun_symm_apply, sum_eq, LinearEquiv.map_zero]
      
    
  · rintro rfl
    rw [AlgHom.map_zero, Matrix.det_zero hι]
    

theorem norm_ne_zero_iff_of_basis [IsDomain R] [IsDomain S] (b : Basis ι R S) {x : S} : Algebra.norm R x ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr (Algebra.norm_eq_zero_iff_of_basis b)

/-- See also `algebra.norm_eq_zero_iff'` if you already have rewritten with `algebra.norm_apply`. -/
@[simp]
theorem norm_eq_zero_iff [FiniteDimensional K L] {x : L} : Algebra.norm K x = 0 ↔ x = 0 :=
  Algebra.norm_eq_zero_iff_of_basis (Basis.ofVectorSpace K L)

/-- This is `algebra.norm_eq_zero_iff` composed with `algebra.norm_apply`. -/
@[simp]
theorem norm_eq_zero_iff' [FiniteDimensional K L] {x : L} : LinearMap.det (Algebra.lmul K L x) = 0 ↔ x = 0 :=
  Algebra.norm_eq_zero_iff_of_basis (Basis.ofVectorSpace K L)

end EqZeroIff

open IntermediateField

variable (K)

-- ././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `norm_eq_norm_adjoin [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `FiniteDimensional [`K `L]) "]")
    (Term.instBinder "[" [] (Term.app `IsSeparable [`K `L]) "]")
    (Term.explicitBinder "(" [`x] [":" `L] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `norm [`K `x])
     "="
     («term_^_»
      (Term.app `norm [`K (Term.app `AdjoinSimple.gen [`K `x])])
      "^"
      (Term.app
       `finrank
       [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         `K
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
         "⟯")
        `L])))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letPatDecl
           (Lean.termThis "this")
           []
           []
           ":="
           (Term.app
            `is_separable_tower_top_of_is_separable
            [`K
             (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
              `K
              "⟮"
              (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
              "⟯")
             `L]))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `pbL
           []
           []
           ":="
           (Term.app
            `Field.powerBasisOfFiniteOfSeparable
            [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
              `K
              "⟮"
              (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
              "⟯")
             `L]))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `pbx
           []
           []
           ":="
           (Term.app `IntermediateField.adjoin.powerBasis [(Term.app `IsSeparable.is_integral [`K `x])]))))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule ["←"] (Term.app `adjoin_simple.algebra_map_gen [`K `x]))
           ","
           (Tactic.rwRule [] (Term.app `norm_eq_matrix_det [(Term.app `pbx.basis.smul [`pbL.basis]) (Term.hole "_")]))
           ","
           (Tactic.rwRule [] `smul_left_mul_matrix_algebra_map)
           ","
           (Tactic.rwRule [] `det_block_diagonal)
           ","
           (Tactic.rwRule [] (Term.app `norm_eq_matrix_det [`pbx.basis]))]
          "]")
         [])
        [])
       (group
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `Finset.card_fin) "," (Tactic.simpLemma [] [] `Finset.prod_const)] "]"]
         [])
        [])
       (group (Tactic.congr "congr" [] []) [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule ["←"] `PowerBasis.finrank)
           ","
           (Tactic.rwRule [] (Term.app `adjoin_simple.algebra_map_gen [`K `x]))]
          "]")
         [])
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
     [(group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letPatDecl
          (Lean.termThis "this")
          []
          []
          ":="
          (Term.app
           `is_separable_tower_top_of_is_separable
           [`K
            (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
             `K
             "⟮"
             (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
             "⟯")
            `L]))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `pbL
          []
          []
          ":="
          (Term.app
           `Field.powerBasisOfFiniteOfSeparable
           [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
             `K
             "⟮"
             (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
             "⟯")
            `L]))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `pbx
          []
          []
          ":="
          (Term.app `IntermediateField.adjoin.powerBasis [(Term.app `IsSeparable.is_integral [`K `x])]))))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] (Term.app `adjoin_simple.algebra_map_gen [`K `x]))
          ","
          (Tactic.rwRule [] (Term.app `norm_eq_matrix_det [(Term.app `pbx.basis.smul [`pbL.basis]) (Term.hole "_")]))
          ","
          (Tactic.rwRule [] `smul_left_mul_matrix_algebra_map)
          ","
          (Tactic.rwRule [] `det_block_diagonal)
          ","
          (Tactic.rwRule [] (Term.app `norm_eq_matrix_det [`pbx.basis]))]
         "]")
        [])
       [])
      (group
       (Tactic.simp
        "simp"
        []
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `Finset.card_fin) "," (Tactic.simpLemma [] [] `Finset.prod_const)] "]"]
        [])
       [])
      (group (Tactic.congr "congr" [] []) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] `PowerBasis.finrank)
          ","
          (Tactic.rwRule [] (Term.app `adjoin_simple.algebra_map_gen [`K `x]))]
         "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule ["←"] `PowerBasis.finrank) "," (Tactic.rwRule [] (Term.app `adjoin_simple.algebra_map_gen [`K `x]))]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `adjoin_simple.algebra_map_gen [`K `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoin_simple.algebra_map_gen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `PowerBasis.finrank
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.congr "congr" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `Finset.card_fin) "," (Tactic.simpLemma [] [] `Finset.prod_const)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.prod_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.card_fin
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule ["←"] (Term.app `adjoin_simple.algebra_map_gen [`K `x]))
     ","
     (Tactic.rwRule [] (Term.app `norm_eq_matrix_det [(Term.app `pbx.basis.smul [`pbL.basis]) (Term.hole "_")]))
     ","
     (Tactic.rwRule [] `smul_left_mul_matrix_algebra_map)
     ","
     (Tactic.rwRule [] `det_block_diagonal)
     ","
     (Tactic.rwRule [] (Term.app `norm_eq_matrix_det [`pbx.basis]))]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `norm_eq_matrix_det [`pbx.basis])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `pbx.basis
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `norm_eq_matrix_det
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `det_block_diagonal
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `smul_left_mul_matrix_algebra_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `norm_eq_matrix_det [(Term.app `pbx.basis.smul [`pbL.basis]) (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app `pbx.basis.smul [`pbL.basis])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `pbL.basis
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `pbx.basis.smul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `pbx.basis.smul [`pbL.basis]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `norm_eq_matrix_det
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `adjoin_simple.algebra_map_gen [`K `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoin_simple.algebra_map_gen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticLet_
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `pbx
     []
     []
     ":="
     (Term.app `IntermediateField.adjoin.powerBasis [(Term.app `IsSeparable.is_integral [`K `x])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IntermediateField.adjoin.powerBasis [(Term.app `IsSeparable.is_integral [`K `x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IsSeparable.is_integral [`K `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IsSeparable.is_integral
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `IsSeparable.is_integral [`K `x]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IntermediateField.adjoin.powerBasis
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticLet_
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `pbL
     []
     []
     ":="
     (Term.app
      `Field.powerBasisOfFiniteOfSeparable
      [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `K
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
        "⟯")
       `L]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Field.powerBasisOfFiniteOfSeparable
   [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `K
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
     "⟯")
    `L])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `L
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `K
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)"»'
theorem
  norm_eq_norm_adjoin
  [ FiniteDimensional K L ] [ IsSeparable K L ] ( x : L )
    :
      norm K x
        =
        norm K AdjoinSimple.gen K x
          ^
          finrank K ⟮ "././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)" ⟯ L
  :=
    by
      let
          this
            :=
            is_separable_tower_top_of_is_separable
              K K ⟮ "././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)" ⟯ L
        let
          pbL
            :=
            Field.powerBasisOfFiniteOfSeparable
              K ⟮ "././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)" ⟯ L
        let pbx := IntermediateField.adjoin.powerBasis IsSeparable.is_integral K x
        rw
          [
            ← adjoin_simple.algebra_map_gen K x
              ,
              norm_eq_matrix_det pbx.basis.smul pbL.basis _
              ,
              smul_left_mul_matrix_algebra_map
              ,
              det_block_diagonal
              ,
              norm_eq_matrix_det pbx.basis
            ]
        simp only [ Finset.card_fin , Finset.prod_const ]
        congr
        rw [ ← PowerBasis.finrank , adjoin_simple.algebra_map_gen K x ]

variable {K}

section IntermediateField

-- ././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `_root_.intermediate_field.adjoin_simple.norm_gen_eq_one [])
  (Command.declSig
   [(Term.implicitBinder "{" [`x] [":" `L] "}")
    (Term.explicitBinder "(" [`hx] [":" («term¬_» "¬" (Term.app `IsIntegral [`K `x]))] [] ")")]
   (Term.typeSpec ":" («term_=_» (Term.app `norm [`K (Term.app `AdjoinSimple.gen [`K `x])]) "=" (num "1"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `norm_eq_one_of_not_exists_basis)] "]") [])
        [])
       (group (Tactic.contrapose! "contrapose!" [`hx []]) [])
       (group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
              ","
              (Tactic.rcasesPatLo
               (Tactic.rcasesPatMed
                [(Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])]
                  "⟩")])
               [])]
             "⟩")])]
         []
         [":=" [`hx]])
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          `is_integral_of_mem_of_fg
          [(Term.proj
            (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
             `K
             "⟮"
             (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
             "⟯")
            "."
            `toSubalgebra)
           (Term.hole "_")
           `x
           (Term.hole "_")]))
        [])
       (group
        («tactic·.__;_»
         "·"
         [(group
           (Tactic.exact
            "exact"
            (Term.app
             (Term.proj (Term.app `Submodule.fg_iff_finite_dimensional [(Term.hole "_")]) "." `mpr)
             [(Term.app `of_finset_basis [`b])]))
           [])])
        [])
       (group
        («tactic·.__;_»
         "·"
         [(group
           (Tactic.exact
            "exact"
            (Term.app `IntermediateField.subset_adjoin [`K (Term.hole "_") (Term.app `Set.mem_singleton [`x])]))
           [])])
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
     [(group
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `norm_eq_one_of_not_exists_basis)] "]") [])
       [])
      (group (Tactic.contrapose! "contrapose!" [`hx []]) [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
             ","
             (Tactic.rcasesPatLo
              (Tactic.rcasesPatMed
               [(Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])]
                 "⟩")])
              [])]
            "⟩")])]
        []
        [":=" [`hx]])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `is_integral_of_mem_of_fg
         [(Term.proj
           (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
            `K
            "⟮"
            (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
            "⟯")
           "."
           `toSubalgebra)
          (Term.hole "_")
          `x
          (Term.hole "_")]))
       [])
      (group
       («tactic·.__;_»
        "·"
        [(group
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj (Term.app `Submodule.fg_iff_finite_dimensional [(Term.hole "_")]) "." `mpr)
            [(Term.app `of_finset_basis [`b])]))
          [])])
       [])
      (group
       («tactic·.__;_»
        "·"
        [(group
          (Tactic.exact
           "exact"
           (Term.app `IntermediateField.subset_adjoin [`K (Term.hole "_") (Term.app `Set.mem_singleton [`x])]))
          [])])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («tactic·.__;_»
   "·"
   [(group
     (Tactic.exact
      "exact"
      (Term.app `IntermediateField.subset_adjoin [`K (Term.hole "_") (Term.app `Set.mem_singleton [`x])]))
     [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app `IntermediateField.subset_adjoin [`K (Term.hole "_") (Term.app `Set.mem_singleton [`x])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IntermediateField.subset_adjoin [`K (Term.hole "_") (Term.app `Set.mem_singleton [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Set.mem_singleton [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Set.mem_singleton
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Set.mem_singleton [`x]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IntermediateField.subset_adjoin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  («tactic·.__;_»
   "·"
   [(group
     (Tactic.exact
      "exact"
      (Term.app
       (Term.proj (Term.app `Submodule.fg_iff_finite_dimensional [(Term.hole "_")]) "." `mpr)
       [(Term.app `of_finset_basis [`b])]))
     [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    (Term.proj (Term.app `Submodule.fg_iff_finite_dimensional [(Term.hole "_")]) "." `mpr)
    [(Term.app `of_finset_basis [`b])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.app `Submodule.fg_iff_finite_dimensional [(Term.hole "_")]) "." `mpr)
   [(Term.app `of_finset_basis [`b])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `of_finset_basis [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `of_finset_basis
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `of_finset_basis [`b]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `Submodule.fg_iff_finite_dimensional [(Term.hole "_")]) "." `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Submodule.fg_iff_finite_dimensional [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Submodule.fg_iff_finite_dimensional
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `Submodule.fg_iff_finite_dimensional [(Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `is_integral_of_mem_of_fg
    [(Term.proj
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `K
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
       "⟯")
      "."
      `toSubalgebra)
     (Term.hole "_")
     `x
     (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `is_integral_of_mem_of_fg
   [(Term.proj
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `K
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
      "⟯")
     "."
     `toSubalgebra)
    (Term.hole "_")
    `x
    (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.proj
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `K
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
    "⟯")
   "."
   `toSubalgebra)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `K
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)"»'
theorem
  _root_.intermediate_field.adjoin_simple.norm_gen_eq_one
  { x : L } ( hx : ¬ IsIntegral K x ) : norm K AdjoinSimple.gen K x = 1
  :=
    by
      rw [ norm_eq_one_of_not_exists_basis ]
        contrapose! hx
        obtain ⟨ s , ⟨ b ⟩ ⟩ := hx
        refine'
          is_integral_of_mem_of_fg
            K ⟮ "././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)" ⟯ . toSubalgebra _ x _
        · exact Submodule.fg_iff_finite_dimensional _ . mpr of_finset_basis b
        · exact IntermediateField.subset_adjoin K _ Set.mem_singleton x

-- ././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `_root_.intermediate_field.adjoin_simple.norm_gen_eq_prod_roots [])
  (Command.declSig
   [(Term.explicitBinder "(" [`x] [":" `L] [] ")")
    (Term.explicitBinder
     "("
     [`hf]
     [":" (Term.app (Term.proj (Term.app `minpoly [`K `x]) "." `Splits) [(Term.app `algebraMap [`K `F])])]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app (Term.app `algebraMap [`K `F]) [(Term.app `norm [`K (Term.app `AdjoinSimple.gen [`K `x])])])
     "="
     (Term.proj
      (Term.proj
       (Term.app (Term.proj (Term.app `minpoly [`K `x]) "." `map) [(Term.app `algebraMap [`K `F])])
       "."
       `roots)
      "."
      `Prod))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`injKxL []]
           []
           ":="
           (Term.proj
            (Term.app
             `algebraMap
             [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
               `K
               "⟮"
               (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
               "⟯")
              `L])
            "."
            `Injective))))
        [])
       (group (Tactic.byCases' "by_cases'" [`hx ":"] (Term.app `_root_.is_integral [`K `x])) [])
       (group (Mathlib.Tactic.tacticSwap "swap") [])
       (group
        («tactic·.__;_»
         "·"
         [(group
           (Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma [] [] (Term.app `minpoly.eq_zero [`hx]))
              ","
              (Tactic.simpLemma [] [] (Term.app `IntermediateField.AdjoinSimple.norm_gen_eq_one [`hx]))]
             "]"]
            [])
           [])])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hx' []]
           [(Term.typeSpec ":" (Term.app `_root_.is_integral [`K (Term.app `adjoin_simple.gen [`K `x])]))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (tacticRwa__
                 "rwa"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule ["←"] (Term.app `is_integral_algebra_map_iff [`injKxL]))
                   ","
                   (Tactic.rwRule [] `adjoin_simple.algebra_map_gen)]
                  "]")
                 [])
                [])
               (group (Tactic.tacticInfer_instance "infer_instance") [])]))))))
        [])
       (group
        (Tactic.«tactic_<;>_»
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule ["←"] (Term.app `adjoin.power_basis_gen [`hx]))
            ","
            (Tactic.rwRule [] `power_basis.norm_gen_eq_prod_roots)]
           "]")
          [])
         "<;>"
         (Tactic.«tactic_<;>_»
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `adjoin.power_basis_gen [`hx]))
             ","
             (Tactic.rwRule [] (Term.app `minpoly.eq_of_algebra_map_eq [`injKxL `hx']))]
            "]")
           [])
          "<;>"
          (Tactic.tacticTry_
           "try"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] (Term.app `adjoin_simple.algebra_map_gen [(Term.hole "_") (Term.hole "_")]))]
                 "]"]
                [])
               [])])))))
        [])
       (group (Tactic.exact "exact" `hf) [])])))
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
     [(group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`injKxL []]
          []
          ":="
          (Term.proj
           (Term.app
            `algebraMap
            [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
              `K
              "⟮"
              (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
              "⟯")
             `L])
           "."
           `Injective))))
       [])
      (group (Tactic.byCases' "by_cases'" [`hx ":"] (Term.app `_root_.is_integral [`K `x])) [])
      (group (Mathlib.Tactic.tacticSwap "swap") [])
      (group
       («tactic·.__;_»
        "·"
        [(group
          (Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] (Term.app `minpoly.eq_zero [`hx]))
             ","
             (Tactic.simpLemma [] [] (Term.app `IntermediateField.AdjoinSimple.norm_gen_eq_one [`hx]))]
            "]"]
           [])
          [])])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hx' []]
          [(Term.typeSpec ":" (Term.app `_root_.is_integral [`K (Term.app `adjoin_simple.gen [`K `x])]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (tacticRwa__
                "rwa"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule ["←"] (Term.app `is_integral_algebra_map_iff [`injKxL]))
                  ","
                  (Tactic.rwRule [] `adjoin_simple.algebra_map_gen)]
                 "]")
                [])
               [])
              (group (Tactic.tacticInfer_instance "infer_instance") [])]))))))
       [])
      (group
       (Tactic.«tactic_<;>_»
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule ["←"] (Term.app `adjoin.power_basis_gen [`hx]))
           ","
           (Tactic.rwRule [] `power_basis.norm_gen_eq_prod_roots)]
          "]")
         [])
        "<;>"
        (Tactic.«tactic_<;>_»
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] (Term.app `adjoin.power_basis_gen [`hx]))
            ","
            (Tactic.rwRule [] (Term.app `minpoly.eq_of_algebra_map_eq [`injKxL `hx']))]
           "]")
          [])
         "<;>"
         (Tactic.tacticTry_
          "try"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] (Term.app `adjoin_simple.algebra_map_gen [(Term.hole "_") (Term.hole "_")]))]
                "]"]
               [])
              [])])))))
       [])
      (group (Tactic.exact "exact" `hf) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `hf)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic_<;>_»
   (Tactic.rwSeq
    "rw"
    []
    (Tactic.rwRuleSeq
     "["
     [(Tactic.rwRule ["←"] (Term.app `adjoin.power_basis_gen [`hx]))
      ","
      (Tactic.rwRule [] `power_basis.norm_gen_eq_prod_roots)]
     "]")
    [])
   "<;>"
   (Tactic.«tactic_<;>_»
    (Tactic.rwSeq
     "rw"
     []
     (Tactic.rwRuleSeq
      "["
      [(Tactic.rwRule [] (Term.app `adjoin.power_basis_gen [`hx]))
       ","
       (Tactic.rwRule [] (Term.app `minpoly.eq_of_algebra_map_eq [`injKxL `hx']))]
      "]")
     [])
    "<;>"
    (Tactic.tacticTry_
     "try"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.simp
          "simp"
          []
          []
          ["only"]
          ["["
           [(Tactic.simpLemma [] [] (Term.app `adjoin_simple.algebra_map_gen [(Term.hole "_") (Term.hole "_")]))]
           "]"]
          [])
         [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.rwSeq
    "rw"
    []
    (Tactic.rwRuleSeq
     "["
     [(Tactic.rwRule [] (Term.app `adjoin.power_basis_gen [`hx]))
      ","
      (Tactic.rwRule [] (Term.app `minpoly.eq_of_algebra_map_eq [`injKxL `hx']))]
     "]")
    [])
   "<;>"
   (Tactic.tacticTry_
    "try"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] (Term.app `adjoin_simple.algebra_map_gen [(Term.hole "_") (Term.hole "_")]))]
          "]"]
         [])
        [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticTry_
   "try"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] (Term.app `adjoin_simple.algebra_map_gen [(Term.hole "_") (Term.hole "_")]))] "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] (Term.app `adjoin_simple.algebra_map_gen [(Term.hole "_") (Term.hole "_")]))] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `adjoin_simple.algebra_map_gen [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoin_simple.algebra_map_gen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] (Term.app `adjoin.power_basis_gen [`hx]))
     ","
     (Tactic.rwRule [] (Term.app `minpoly.eq_of_algebra_map_eq [`injKxL `hx']))]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `minpoly.eq_of_algebra_map_eq [`injKxL `hx'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `injKxL
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minpoly.eq_of_algebra_map_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `adjoin.power_basis_gen [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoin.power_basis_gen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule ["←"] (Term.app `adjoin.power_basis_gen [`hx]))
     ","
     (Tactic.rwRule [] `power_basis.norm_gen_eq_prod_roots)]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `power_basis.norm_gen_eq_prod_roots
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `adjoin.power_basis_gen [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoin.power_basis_gen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`hx' []]
     [(Term.typeSpec ":" (Term.app `_root_.is_integral [`K (Term.app `adjoin_simple.gen [`K `x])]))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule ["←"] (Term.app `is_integral_algebra_map_iff [`injKxL]))
             ","
             (Tactic.rwRule [] `adjoin_simple.algebra_map_gen)]
            "]")
           [])
          [])
         (group (Tactic.tacticInfer_instance "infer_instance") [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (tacticRwa__
        "rwa"
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] (Term.app `is_integral_algebra_map_iff [`injKxL]))
          ","
          (Tactic.rwRule [] `adjoin_simple.algebra_map_gen)]
         "]")
        [])
       [])
      (group (Tactic.tacticInfer_instance "infer_instance") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (tacticRwa__
   "rwa"
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule ["←"] (Term.app `is_integral_algebra_map_iff [`injKxL]))
     ","
     (Tactic.rwRule [] `adjoin_simple.algebra_map_gen)]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `adjoin_simple.algebra_map_gen
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `is_integral_algebra_map_iff [`injKxL])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `injKxL
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `is_integral_algebra_map_iff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `_root_.is_integral [`K (Term.app `adjoin_simple.gen [`K `x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `adjoin_simple.gen [`K `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoin_simple.gen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `adjoin_simple.gen [`K `x]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `_root_.is_integral
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  («tactic·.__;_»
   "·"
   [(group
     (Tactic.simp
      "simp"
      []
      []
      []
      ["["
       [(Tactic.simpLemma [] [] (Term.app `minpoly.eq_zero [`hx]))
        ","
        (Tactic.simpLemma [] [] (Term.app `IntermediateField.AdjoinSimple.norm_gen_eq_one [`hx]))]
       "]"]
      [])
     [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   []
   []
   ["["
    [(Tactic.simpLemma [] [] (Term.app `minpoly.eq_zero [`hx]))
     ","
     (Tactic.simpLemma [] [] (Term.app `IntermediateField.AdjoinSimple.norm_gen_eq_one [`hx]))]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IntermediateField.AdjoinSimple.norm_gen_eq_one [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IntermediateField.AdjoinSimple.norm_gen_eq_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `minpoly.eq_zero [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minpoly.eq_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Mathlib.Tactic.tacticSwap "swap")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.byCases' "by_cases'" [`hx ":"] (Term.app `_root_.is_integral [`K `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `_root_.is_integral [`K `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `_root_.is_integral
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`injKxL []]
     []
     ":="
     (Term.proj
      (Term.app
       `algebraMap
       [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         `K
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
         "⟯")
        `L])
      "."
      `Injective))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.app
    `algebraMap
    [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `K
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
      "⟯")
     `L])
   "."
   `Injective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `algebraMap
   [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `K
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
     "⟯")
    `L])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `L
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `K
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)"»'
theorem
  _root_.intermediate_field.adjoin_simple.norm_gen_eq_prod_roots
  ( x : L ) ( hf : minpoly K x . Splits algebraMap K F )
    : algebraMap K F norm K AdjoinSimple.gen K x = minpoly K x . map algebraMap K F . roots . Prod
  :=
    by
      have
          injKxL
            :=
            algebraMap K ⟮ "././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)" ⟯ L . Injective
        by_cases' hx : _root_.is_integral K x
        swap
        · simp [ minpoly.eq_zero hx , IntermediateField.AdjoinSimple.norm_gen_eq_one hx ]
        have
          hx'
            : _root_.is_integral K adjoin_simple.gen K x
            :=
            by rwa [ ← is_integral_algebra_map_iff injKxL , adjoin_simple.algebra_map_gen ] infer_instance
        rw [ ← adjoin.power_basis_gen hx , power_basis.norm_gen_eq_prod_roots ]
          <;>
          rw [ adjoin.power_basis_gen hx , minpoly.eq_of_algebra_map_eq injKxL hx' ]
            <;>
            try simp only [ adjoin_simple.algebra_map_gen _ _ ]
        exact hf

end IntermediateField

section EqProdEmbeddings

open IntermediateField IntermediateField.AdjoinSimple Polynomial

variable (E : Type _) [Field E] [Algebra K E]

theorem norm_eq_prod_embeddings_gen (pb : PowerBasis K L) (hE : (minpoly K pb.gen).Splits (algebraMap K E))
    (hfx : (minpoly K pb.gen).Separable) :
    algebraMap K E (norm K pb.gen) = (@Finset.univ (PowerBasis.AlgHom.fintype pb)).Prod fun σ => σ pb.gen := by
  let this := Classical.decEq E
  rw [power_basis.norm_gen_eq_prod_roots pb hE, Fintype.prod_equiv pb.lift_equiv', Finset.prod_mem_multiset,
    Finset.prod_eq_multiset_prod, Multiset.to_finset_val, multiset.dedup_eq_self.mpr, Multiset.map_id]
  · exact nodup_roots ((separable_map _).mpr hfx)
    
  · intro x
    rfl
    
  · intro σ
    rw [PowerBasis.lift_equiv'_apply_coe, id.def]
    

-- ././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `norm_eq_prod_roots [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `IsSeparable [`K `L]) "]")
    (Term.instBinder "[" [] (Term.app `FiniteDimensional [`K `L]) "]")
    (Term.implicitBinder "{" [`x] [":" `L] "}")
    (Term.explicitBinder
     "("
     [`hF]
     [":" (Term.app (Term.proj (Term.app `minpoly [`K `x]) "." `Splits) [(Term.app `algebraMap [`K `F])])]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `algebraMap [`K `F (Term.app `norm [`K `x])])
     "="
     («term_^_»
      (Term.proj
       (Term.proj
        (Term.app (Term.proj (Term.app `minpoly [`K `x]) "." `map) [(Term.app `algebraMap [`K `F])])
        "."
        `roots)
       "."
       `Prod)
      "^"
      (Term.app
       `finrank
       [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         `K
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
         "⟯")
        `L])))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app `norm_eq_norm_adjoin [`K `x]))
           ","
           (Tactic.rwRule [] `map_pow)
           ","
           (Tactic.rwRule [] (Term.app `IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots [(Term.hole "_") `hF]))]
          "]")
         [])
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
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] (Term.app `norm_eq_norm_adjoin [`K `x]))
          ","
          (Tactic.rwRule [] `map_pow)
          ","
          (Tactic.rwRule [] (Term.app `IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots [(Term.hole "_") `hF]))]
         "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] (Term.app `norm_eq_norm_adjoin [`K `x]))
     ","
     (Tactic.rwRule [] `map_pow)
     ","
     (Tactic.rwRule [] (Term.app `IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots [(Term.hole "_") `hF]))]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots [(Term.hole "_") `hF])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hF
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `map_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `norm_eq_norm_adjoin [`K `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `norm_eq_norm_adjoin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app `algebraMap [`K `F (Term.app `norm [`K `x])])
   "="
   («term_^_»
    (Term.proj
     (Term.proj (Term.app (Term.proj (Term.app `minpoly [`K `x]) "." `map) [(Term.app `algebraMap [`K `F])]) "." `roots)
     "."
     `Prod)
    "^"
    (Term.app
     `finrank
     [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `K
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
       "⟯")
      `L])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_»
   (Term.proj
    (Term.proj (Term.app (Term.proj (Term.app `minpoly [`K `x]) "." `map) [(Term.app `algebraMap [`K `F])]) "." `roots)
    "."
    `Prod)
   "^"
   (Term.app
    `finrank
    [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `K
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
      "⟯")
     `L]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `finrank
   [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `K
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
     "⟯")
    `L])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `L
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `K
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)"»'
theorem
  norm_eq_prod_roots
  [ IsSeparable K L ] [ FiniteDimensional K L ] { x : L } ( hF : minpoly K x . Splits algebraMap K F )
    :
      algebraMap K F norm K x
        =
        minpoly K x . map algebraMap K F . roots . Prod
          ^
          finrank K ⟮ "././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)" ⟯ L
  := by rw [ norm_eq_norm_adjoin K x , map_pow , IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots _ hF ]

variable (F)

theorem prod_embeddings_eq_finrank_pow [Algebra L F] [IsScalarTower K L F] [IsAlgClosed E] [IsSeparable K F]
    [FiniteDimensional K F] (pb : PowerBasis K L) :
    (∏ σ : F →ₐ[K] E, σ (algebraMap L F pb.gen)) =
      ((@Finset.univ (PowerBasis.AlgHom.fintype pb)).Prod fun σ : L →ₐ[K] E => σ pb.gen) ^ finrank L F :=
  by
  have : FiniteDimensional L F := FiniteDimensional.right K L F
  have : IsSeparable L F := is_separable_tower_top_of_is_separable K L F
  let this : Fintype (L →ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  let this : ∀ f : L →ₐ[K] E, Fintype (@AlgHom L F E _ _ _ _ f.to_ring_hom.to_algebra) := _
  rw [Fintype.prod_equiv algHomEquivSigma (fun σ : F →ₐ[K] E => _) fun σ => σ.1 pb.gen, ← Finset.univ_sigma_univ,
    Finset.prod_sigma, ← Finset.prod_pow]
  refine' Finset.prod_congr rfl fun σ _ => _
  · let this : Algebra L E := σ.to_ring_hom.to_algebra
    simp only [Finset.prod_const, Finset.card_univ]
    congr
    rw [AlgHom.card L F E]
    
  · intro σ
    simp only [algHomEquivSigma, Equivₓ.coe_fn_mk, AlgHom.restrictDomain, AlgHom.comp_apply,
      IsScalarTower.coe_to_alg_hom']
    

variable (K)

-- ././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "For `L/K` a finite separable extension of fields and `E` an algebraically closed extension\nof `K`, the norm (down to `K`) of an element `x` of `L` is equal to the product of the images\nof `x` over all the `K`-embeddings `σ`  of `L` into `E`. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `norm_eq_prod_embeddings [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `FiniteDimensional [`K `L]) "]")
    (Term.instBinder "[" [] (Term.app `IsSeparable [`K `L]) "]")
    (Term.instBinder "[" [] (Term.app `IsAlgClosed [`E]) "]")
    (Term.implicitBinder "{" [`x] [":" `L] "}")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `algebraMap [`K `E (Term.app `norm [`K `x])])
     "="
     (BigOperators.Algebra.BigOperators.Basic.«term∏_,_»
      "∏"
      (Mathlib.ExtendedBinder.extBinders
       (Mathlib.ExtendedBinder.extBinder
        (Lean.binderIdent `σ)
        [":" (Algebra.Algebra.Basic.«term_→ₐ[_]_» `L " →ₐ[" `K "] " `E)]))
      ", "
      (Term.app `σ [`x])))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl (Term.haveIdDecl [`hx []] [] ":=" (Term.app `IsSeparable.is_integral [`K `x]))))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app `norm_eq_norm_adjoin [`K `x]))
           ","
           (Tactic.rwRule [] `RingHom.map_pow)
           ","
           (Tactic.rwRule ["←"] (Term.app `adjoin.power_basis_gen [`hx]))
           ","
           (Tactic.rwRule
            []
            (Term.app
             `norm_eq_prod_embeddings_gen
             [`E (Term.app `adjoin.power_basis [`hx]) (Term.app `IsAlgClosed.splits_codomain [(Term.hole "_")])]))]
          "]")
         [])
        [])
       (group
        («tactic·.__;_»
         "·"
         [(group
           (Tactic.exact
            "exact"
            (Term.proj
             (Term.app `prod_embeddings_eq_finrank_pow [`L `E (Term.app `adjoin.power_basis [`hx])])
             "."
             `symm))
           [])])
        [])
       (group
        («tactic·.__;_»
         "·"
         [(group
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              []
              ":="
              (Term.app
               `is_separable_tower_bot_of_is_separable
               [`K
                (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                 `K
                 "⟮"
                 (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
                 "⟯")
                `L]))))
           [])
          (group (Tactic.exact "exact" (Term.app `IsSeparable.separable [`K (Term.hole "_")])) [])])
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
     [(group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl (Term.haveIdDecl [`hx []] [] ":=" (Term.app `IsSeparable.is_integral [`K `x]))))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] (Term.app `norm_eq_norm_adjoin [`K `x]))
          ","
          (Tactic.rwRule [] `RingHom.map_pow)
          ","
          (Tactic.rwRule ["←"] (Term.app `adjoin.power_basis_gen [`hx]))
          ","
          (Tactic.rwRule
           []
           (Term.app
            `norm_eq_prod_embeddings_gen
            [`E (Term.app `adjoin.power_basis [`hx]) (Term.app `IsAlgClosed.splits_codomain [(Term.hole "_")])]))]
         "]")
        [])
       [])
      (group
       («tactic·.__;_»
        "·"
        [(group
          (Tactic.exact
           "exact"
           (Term.proj
            (Term.app `prod_embeddings_eq_finrank_pow [`L `E (Term.app `adjoin.power_basis [`hx])])
            "."
            `symm))
          [])])
       [])
      (group
       («tactic·.__;_»
        "·"
        [(group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             []
             ":="
             (Term.app
              `is_separable_tower_bot_of_is_separable
              [`K
               (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                `K
                "⟮"
                (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
                "⟯")
               `L]))))
          [])
         (group (Tactic.exact "exact" (Term.app `IsSeparable.separable [`K (Term.hole "_")])) [])])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («tactic·.__;_»
   "·"
   [(group
     (Tactic.tacticHave_
      "have"
      (Term.haveDecl
       (Term.haveIdDecl
        []
        []
        ":="
        (Term.app
         `is_separable_tower_bot_of_is_separable
         [`K
          (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
           `K
           "⟮"
           (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
           "⟯")
          `L]))))
     [])
    (group (Tactic.exact "exact" (Term.app `IsSeparable.separable [`K (Term.hole "_")])) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `IsSeparable.separable [`K (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IsSeparable.separable [`K (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IsSeparable.separable
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     []
     ":="
     (Term.app
      `is_separable_tower_bot_of_is_separable
      [`K
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `K
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
        "⟯")
       `L]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `is_separable_tower_bot_of_is_separable
   [`K
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `K
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
     "⟯")
    `L])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `L
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `K
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)"»'
/--
    For `L/K` a finite separable extension of fields and `E` an algebraically closed extension
    of `K`, the norm (down to `K`) of an element `x` of `L` is equal to the product of the images
    of `x` over all the `K`-embeddings `σ`  of `L` into `E`. -/
  theorem
    norm_eq_prod_embeddings
    [ FiniteDimensional K L ] [ IsSeparable K L ] [ IsAlgClosed E ] { x : L }
      : algebraMap K E norm K x = ∏ σ : L →ₐ[ K ] E , σ x
    :=
      by
        have hx := IsSeparable.is_integral K x
          rw
            [
              norm_eq_norm_adjoin K x
                ,
                RingHom.map_pow
                ,
                ← adjoin.power_basis_gen hx
                ,
                norm_eq_prod_embeddings_gen E adjoin.power_basis hx IsAlgClosed.splits_codomain _
              ]
          · exact prod_embeddings_eq_finrank_pow L E adjoin.power_basis hx . symm
          ·
            have
                :=
                  is_separable_tower_bot_of_is_separable
                    K K ⟮ "././Mathport/Syntax/Translate/Basic.lean:811:11: unsupported (impossible)" ⟯ L
              exact IsSeparable.separable K _

theorem is_integral_norm [Algebra S L] [Algebra S K] [IsScalarTower S K L] [IsSeparable K L] [FiniteDimensional K L]
    {x : L} (hx : IsIntegral S x) : IsIntegral S (norm K x) := by
  have hx' : _root_.is_integral K x := is_integral_of_is_scalar_tower _ hx
  rw [← is_integral_algebra_map_iff (algebraMap K (AlgebraicClosure L)).Injective, norm_eq_prod_roots]
  · refine' (IsIntegral.multiset_prod fun y hy => _).pow _
    rw [mem_roots_map (minpoly.ne_zero hx')] at hy
    use minpoly S x, minpoly.monic hx
    rw [← aeval_def] at hy⊢
    exact minpoly.aeval_of_is_scalar_tower S x y hy
    
  · apply IsAlgClosed.splits_codomain
    
  · infer_instance
    

end EqProdEmbeddings

end Algebra

