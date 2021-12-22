import Mathbin.GroupTheory.Congruence
import Mathbin.GroupTheory.Submonoid.Membership
import Mathbin.Algebra.Group.Units

/-!
# Localizations of commutative monoids

Localizing a commutative ring at one of its submonoids does not rely on the ring's addition, so
we can generalize localizations to commutative monoids.

We characterize the localization of a commutative monoid `M` at a submonoid `S` up to
isomorphism; that is, a commutative monoid `N` is the localization of `M` at `S` iff we can find a
monoid homomorphism `f : M →* N` satisfying 3 properties:
1. For all `y ∈ S`, `f y` is a unit;
2. For all `z : N`, there exists `(x, y) : M × S` such that `z * f y = f x`;
3. For all `x, y : M`, `f x = f y` iff there exists `c ∈ S` such that `x * c = y * c`.

Given such a localization map `f : M →* N`, we can define the surjection
`localization_map.mk'` sending `(x, y) : M × S` to `f x * (f y)⁻¹`, and
`localization_map.lift`, the homomorphism from `N` induced by a homomorphism from `M` which maps
elements of `S` to invertible elements of the codomain. Similarly, given commutative monoids
`P, Q`, a submonoid `T` of `P` and a localization map for `T` from `P` to `Q`, then a homomorphism
`g : M →* P` such that `g(S) ⊆ T` induces a homomorphism of localizations,
`localization_map.map`, from `N` to `Q`.
We treat the special case of localizing away from an element in the sections `away_map` and `away`.

We also define the quotient of `M × S` by the unique congruence relation (equivalence relation
preserving a binary operation) `r` such that for any other congruence relation `s` on `M × S`
satisfying '`∀ y ∈ S`, `(1, 1) ∼ (y, y)` under `s`', we have that `(x₁, y₁) ∼ (x₂, y₂)` by `s`
whenever `(x₁, y₁) ∼ (x₂, y₂)` by `r`. We show this relation is equivalent to the standard
localization relation.
This defines the localization as a quotient type, `localization`, but the majority of
subsequent lemmas in the file are given in terms of localizations up to isomorphism, using maps
which satisfy the characteristic predicate.

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

The infimum form of the localization congruence relation is chosen as 'canonical' here, since it
shortens some proofs.

To apply a localization map `f` as a function, we use `f.to_map`, as coercions don't work well for
this structure.

To reason about the localization as a quotient type, use `mk_eq_monoid_of_mk'` and associated
lemmas. These show the quotient map `mk : M → S → localization S` equals the
surjection `localization_map.mk'` induced by the map
`monoid_of : localization_map S (localization S)` (where `of` establishes the
localization as a quotient type satisfies the characteristic predicate). The lemma
`mk_eq_monoid_of_mk'` hence gives you access to the results in the rest of the file, which are
about the `localization_map.mk'` induced by any localization map.

## Tags
localization, monoid localization, quotient monoid, congruence relation, characteristic predicate,
commutative monoid
-/


namespace AddSubmonoid

variable {M : Type _} [AddCommMonoidₓ M] (S : AddSubmonoid M) (N : Type _) [AddCommMonoidₓ N]

/--  The type of add_monoid homomorphisms satisfying the characteristic predicate: if `f : M →+ N`
satisfies this predicate, then `N` is isomorphic to the localization of `M` at `S`. -/
@[nolint has_inhabited_instance]
structure localization_map extends AddMonoidHom M N where
  map_add_units' : ∀ y : S, IsAddUnit (to_fun y)
  surj' : ∀ z : N, ∃ x : M × S, (z+to_fun x.2) = to_fun x.1
  eq_iff_exists' : ∀ x y, to_fun x = to_fun y ↔ ∃ c : S, (x+c) = y+c

/--  The add_monoid hom underlying a `localization_map` of `add_comm_monoid`s. -/
add_decl_doc localization_map.to_add_monoid_hom

end AddSubmonoid

variable {M : Type _} [CommMonoidₓ M] (S : Submonoid M) (N : Type _) [CommMonoidₓ N] {P : Type _} [CommMonoidₓ P]

namespace Submonoid

/--  The type of monoid homomorphisms satisfying the characteristic predicate: if `f : M →* N`
satisfies this predicate, then `N` is isomorphic to the localization of `M` at `S`. -/
@[nolint has_inhabited_instance]
structure localization_map extends MonoidHom M N where
  map_units' : ∀ y : S, IsUnit (to_fun y)
  surj' : ∀ z : N, ∃ x : M × S, (z*to_fun x.2) = to_fun x.1
  eq_iff_exists' : ∀ x y, to_fun x = to_fun y ↔ ∃ c : S, (x*c) = y*c

attribute [to_additive AddSubmonoid.LocalizationMap] Submonoid.LocalizationMap

attribute [to_additive AddSubmonoid.LocalizationMap.toAddMonoidHom] Submonoid.LocalizationMap.toMonoidHom

/--  The monoid hom underlying a `localization_map`. -/
add_decl_doc localization_map.to_monoid_hom

end Submonoid

namespace Localization

run_cmd
  to_additive.map_namespace `localization `add_localization

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " The congruence relation on `M × S`, `M` a `comm_monoid` and `S` a submonoid of `M`, whose\nquotient is the localization of `M` at `S`, defined as the unique congruence relation on\n`M × S` such that for any other congruence relation `s` on `M × S` where for all `y ∈ S`,\n`(1, 1) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `r` implies\n`(x₁, y₁) ∼ (x₂, y₂)` by `s`. -/")]
  [(Term.attributes
    "@["
    [(Term.attrInstance
      (Term.attrKind [])
      (Attr.toAdditive
       "to_additive"
       []
       [(strLit
         "\"The congruence relation on `M × S`, `M` an `add_comm_monoid` and `S`\\nan `add_submonoid` of `M`, whose quotient is the localization of `M` at `S`, defined as the unique\\ncongruence relation on `M × S` such that for any other congruence relation `s` on `M × S` where\\nfor all `y ∈ S`, `(0, 0) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `r` implies\\n`(x₁, y₁) ∼ (x₂, y₂)` by `s`.\"")]))]
    "]")]
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `r [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`S] [":" (Term.app `Submonoid [`M])] [] ")")]
   [(Term.typeSpec ":" (Term.app `Con [(«term_×_» `M "×" `S)]))])
  (Command.declValSimple
   ":="
   (Term.app
    `Inf
    [(Set.«term{_|_}»
      "{"
      `c
      "|"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`y] [(Term.typeSpec ":" `S)])]
       ","
       (Term.app `c [(numLit "1") (Term.paren "(" [`y [(Term.tupleTail "," [`y])]] ")")]))
      "}")])
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
  (Term.app
   `Inf
   [(Set.«term{_|_}»
     "{"
     `c
     "|"
     (Term.forall
      "∀"
      [(Term.simpleBinder [`y] [(Term.typeSpec ":" `S)])]
      ","
      (Term.app `c [(numLit "1") (Term.paren "(" [`y [(Term.tupleTail "," [`y])]] ")")]))
     "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}»
   "{"
   `c
   "|"
   (Term.forall
    "∀"
    [(Term.simpleBinder [`y] [(Term.typeSpec ":" `S)])]
    ","
    (Term.app `c [(numLit "1") (Term.paren "(" [`y [(Term.tupleTail "," [`y])]] ")")]))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`y] [(Term.typeSpec ":" `S)])]
   ","
   (Term.app `c [(numLit "1") (Term.paren "(" [`y [(Term.tupleTail "," [`y])]] ")")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `c [(numLit "1") (Term.paren "(" [`y [(Term.tupleTail "," [`y])]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [`y [(Term.tupleTail "," [`y])]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tupleTail', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tupleTail', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
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
      The congruence relation on `M × S`, `M` a `comm_monoid` and `S` a submonoid of `M`, whose
      quotient is the localization of `M` at `S`, defined as the unique congruence relation on
      `M × S` such that for any other congruence relation `s` on `M × S` where for all `y ∈ S`,
      `(1, 1) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `r` implies
      `(x₁, y₁) ∼ (x₂, y₂)` by `s`. -/
    @[
      to_additive
        "The congruence relation on `M × S`, `M` an `add_comm_monoid` and `S`\nan `add_submonoid` of `M`, whose quotient is the localization of `M` at `S`, defined as the unique\ncongruence relation on `M × S` such that for any other congruence relation `s` on `M × S` where\nfor all `y ∈ S`, `(0, 0) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `r` implies\n`(x₁, y₁) ∼ (x₂, y₂)` by `s`."
      ]
  def r ( S : Submonoid M ) : Con M × S := Inf { c | ∀ y : S , c 1 ( y , y ) }

/--  An alternate form of the congruence relation on `M × S`, `M` a `comm_monoid` and `S` a
submonoid of `M`, whose quotient is the localization of `M` at `S`. -/
@[to_additive
      "An alternate form of the congruence relation on `M × S`, `M` a `comm_monoid` and\n`S` a submonoid of `M`, whose quotient is the localization of `M` at `S`."]
def r' : Con (M × S) := by
  refine'
    { R := fun a b : M × S => ∃ c : S, ((a.1*b.2)*c) = (b.1*a.2)*c,
      iseqv := ⟨fun a => ⟨1, rfl⟩, fun a b ⟨c, hc⟩ => ⟨c, hc.symm⟩, _⟩, .. }
  ·
    rintro a b c ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
    use (b.2*t₁)*t₂
    simp only [Submonoid.coe_mul]
    calc ((a.1*c.2)*(b.2*t₁)*t₂) = (((a.1*b.2)*t₁)*c.2)*t₂ := by
      ac_rfl _ = (((b.1*c.2)*t₂)*a.2)*t₁ := by
      rw [ht₁]
      ac_rfl _ = (c.1*a.2)*(b.2*t₁)*t₂ := by
      rw [ht₂]
      ac_rfl
  ·
    rintro a b c d ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
    use t₁*t₂
    calc (((a.1*c.1)*b.2*d.2)*t₁*t₂) = ((a.1*b.2)*t₁)*(c.1*d.2)*t₂ := by
      ac_rfl _ = ((b.1*d.1)*a.2*c.2)*t₁*t₂ := by
      rw [ht₁, ht₂]
      ac_rfl

/--  The congruence relation used to localize a `comm_monoid` at a submonoid can be expressed
equivalently as an infimum (see `localization.r`) or explicitly
(see `localization.r'`). -/
@[to_additive
      "The additive congruence relation used to localize an `add_comm_monoid` at a\nsubmonoid can be expressed equivalently as an infimum (see `add_localization.r`) or\nexplicitly (see `add_localization.r'`)."]
theorem r_eq_r' : r S = r' S :=
  le_antisymmₓ
      (Inf_le $ fun _ =>
        ⟨1, by
          simp ⟩) $
    le_Inf $ fun b H ⟨p, q⟩ y ⟨t, ht⟩ => by
      rw [← mul_oneₓ (p, q), ← mul_oneₓ y]
      refine' b.trans (b.mul (b.refl _) (H (y.2*t))) _
      convert b.symm (b.mul (b.refl y) (H (q*t))) using 1
      rw [Prod.mk_mul_mk, Submonoid.coe_mul, ← mul_assocₓ, ht, mul_left_commₓ, mul_assocₓ]
      rfl

variable {S}

@[to_additive]
theorem r_iff_exists {x y : M × S} : r S x y ↔ ∃ c : S, ((x.1*y.2)*c) = (y.1*x.2)*c := by
  rw [r_eq_r' S] <;> rfl

end Localization

/--  The localization of a `comm_monoid` at one of its submonoids (as a quotient type). -/
@[to_additive AddLocalization
      "The localization of an `add_comm_monoid` at one\nof its submonoids (as a quotient type)."]
def Localization :=
  (Localization.r S).Quotient

namespace Localization

@[to_additive]
instance Inhabited : Inhabited (Localization S) :=
  Con.Quotient.inhabited

/--  Multiplication in a localization is defined as `⟨a, b⟩ * ⟨c, d⟩ = ⟨a * c, b * d⟩`. -/
@[to_additive
      "Addition in an `add_localization` is defined as `⟨a, b⟩ + ⟨c, d⟩ = ⟨a + c, b + d⟩`.\n\nShould not be confused with the ring localization counterpart `localization.add`, which maps\n`⟨a, b⟩ + ⟨c, d⟩` to `⟨d * a + b * c, b * d⟩`."]
protected irreducible_def mul : Localization S → Localization S → Localization S :=
  (r S).CommMonoid.mul

@[to_additive]
instance : Mul (Localization S) :=
  ⟨Localization.mul S⟩

/--  The identity element of a localization is defined as `⟨1, 1⟩`. -/
@[to_additive
      "The identity element of an `add_localization` is defined as `⟨0, 0⟩`.\n\nShould not be confused with the ring localization counterpart `localization.zero`,\nwhich is defined as `⟨0, 1⟩`."]
protected irreducible_def one : Localization S :=
  (r S).CommMonoid.one

@[to_additive]
instance : HasOne (Localization S) :=
  ⟨Localization.one S⟩

/--  Exponentiation in a localization is defined as `⟨a, b⟩ ^ n = ⟨a ^ n, b ^ n⟩`.

This is a separate `irreducible` def to ensure the elaborator doesn't waste its time
trying to unify some huge recursive definition with itself, but unfolded one step less.
-/
@[to_additive
      "Multiplication with a natural in an `add_localization` is defined as `n • ⟨a, b⟩ = ⟨n • a, n • b⟩`.\n\nThis is a separate `irreducible` def to ensure the elaborator doesn't waste its time\ntrying to unify some huge recursive definition with itself, but unfolded one step less."]
protected irreducible_def npow : ℕ → Localization S → Localization S :=
  (r S).CommMonoid.npow

attribute [local semireducible] Localization.mul Localization.one Localization.npow

@[to_additive]
instance : CommMonoidₓ (Localization S) where
  mul := ·*·
  one := 1
  mul_assoc := show ∀ x y z : Localization S, ((x*y)*z) = x*y*z from (r S).CommMonoid.mul_assoc
  mul_comm := show ∀ x y : Localization S, (x*y) = y*x from (r S).CommMonoid.mul_comm
  mul_one := show ∀ x : Localization S, (x*1) = x from (r S).CommMonoid.mul_one
  one_mul := show ∀ x : Localization S, (1*x) = x from (r S).CommMonoid.one_mul
  npow := Localization.npow S
  npow_zero' := show ∀ x : Localization S, Localization.npow S 0 x = 1 from pow_zeroₓ
  npow_succ' :=
    show ∀ n : ℕ x : Localization S, Localization.npow S n.succ x = x*Localization.npow S n x from fun n x =>
      pow_succₓ x n

variable {S}

/--  Given a `comm_monoid` `M` and submonoid `S`, `mk` sends `x : M`, `y ∈ S` to the equivalence
class of `(x, y)` in the localization of `M` at `S`. -/
@[to_additive
      "Given an `add_comm_monoid` `M` and submonoid `S`, `mk` sends `x : M`, `y ∈ S` to\nthe equivalence class of `(x, y)` in the localization of `M` at `S`."]
def mk (x : M) (y : S) : Localization S :=
  (r S).mk' (x, y)

@[to_additive]
theorem mk_eq_mk_iff {a c : M} {b d : S} : mk a b = mk c d ↔ r S ⟨a, b⟩ ⟨c, d⟩ :=
  (r S).Eq

universe u

/--  Dependent recursion principle for localizations: given elements `f a b : p (mk a b)`
for all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d` (wih the correct coercions),
then `f` is defined on the whole `localization S`. -/
@[elab_as_eliminator,
  to_additive
      "Dependent recursion principle for `add_localizations`: given elements `f a b : p (mk a b)`\nfor all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d` (wih the correct coercions),\nthen `f` is defined on the whole `add_localization S`."]
def rec {p : Localization S → Sort u} (f : ∀ a : M b : S, p (mk a b))
    (H : ∀ {a c : M} {b d : S} h : r S (a, b) (c, d), (Eq.ndrec (f a b) (mk_eq_mk_iff.mpr h) : p (mk c d)) = f c d) x :
    p x :=
  Quot.recₓ (fun y => Eq.ndrec (f y.1 y.2) (Prod.mk.eta : (y.1, y.2) = y))
    (fun y z h => by
      cases y
      cases z
      exact H h)
    x

@[to_additive]
theorem mk_mul (a c : M) (b d : S) : (mk a b*mk c d) = mk (a*c) (b*d) :=
  rfl

@[to_additive]
theorem mk_one : mk 1 (1 : S) = 1 :=
  rfl

@[simp, to_additive]
theorem rec_mk {p : Localization S → Sort u} (f : ∀ a : M b : S, p (mk a b)) H (a : M) (b : S) :
    (rec f H (mk a b) : p (mk a b)) = f a b :=
  rfl

/--  Non-dependent recursion principle for localizations: given elements `f a b : p`
for all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d`,
then `f` is defined on the whole `localization S`. -/
@[elab_as_eliminator,
  to_additive
      "Non-dependent recursion principle for `add_localizations`: given elements `f a b : p`\nfor all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d`,\nthen `f` is defined on the whole `localization S`."]
def lift_on {p : Sort u} (x : Localization S) (f : M → S → p)
    (H : ∀ {a c : M} {b d : S} h : r S (a, b) (c, d), f a b = f c d) : p :=
  rec f
    (fun a c b d h => by
      rw [eq_rec_constant, H h])
    x

@[to_additive]
theorem lift_on_mk {p : Sort u} (f : ∀ a : M b : S, p) H (a : M) (b : S) : lift_on (mk a b) f H = f a b :=
  rfl

@[elab_as_eliminator, to_additive]
theorem ind {p : Localization S → Prop} (H : ∀ y : M × S, p (mk y.1 y.2)) x : p x :=
  rec (fun a b => H (a, b)) (fun _ _ _ _ _ => rfl) x

@[elab_as_eliminator, to_additive]
theorem induction_on {p : Localization S → Prop} x (H : ∀ y : M × S, p (mk y.1 y.2)) : p x :=
  ind H x

/--  Non-dependent recursion principle for localizations: given elements `f x y : p`
for all `x` and `y`, such that `r S x x'` and `r S y y'` implies `f x y = f x' y'`,
then `f` is defined on the whole `localization S`. -/
@[elab_as_eliminator,
  to_additive
      "Non-dependent recursion principle for localizations: given elements `f x y : p`\nfor all `x` and `y`, such that `r S x x'` and `r S y y'` implies `f x y = f x' y'`,\nthen `f` is defined on the whole `localization S`."]
def lift_on₂ {p : Sort u} (x y : Localization S) (f : M → S → M → S → p)
    (H : ∀ {a a' b b' c c' d d'} hx : r S (a, b) (a', b') hy : r S (c, d) (c', d'), f a b c d = f a' b' c' d') : p :=
  lift_on x (fun a b => lift_on y (f a b) fun c c' d d' hy => H ((r S).refl _) hy) fun a a' b b' hx =>
    induction_on y fun ⟨c, d⟩ => H hx ((r S).refl _)

@[to_additive]
theorem lift_on₂_mk {p : Sort _} (f : M → S → M → S → p) H (a c : M) (b d : S) :
    lift_on₂ (mk a b) (mk c d) f H = f a b c d :=
  rfl

@[elab_as_eliminator, to_additive]
theorem induction_on₂ {p : Localization S → Localization S → Prop} x y
    (H : ∀ x y : M × S, p (mk x.1 x.2) (mk y.1 y.2)) : p x y :=
  induction_on x $ fun x => induction_on y $ H x

@[elab_as_eliminator, to_additive]
theorem induction_on₃ {p : Localization S → Localization S → Localization S → Prop} x y z
    (H : ∀ x y z : M × S, p (mk x.1 x.2) (mk y.1 y.2) (mk z.1 z.2)) : p x y z :=
  induction_on₂ x y $ fun x y => induction_on z $ H x y

@[to_additive]
theorem one_rel (y : S) : r S 1 (y, y) := fun b hb => hb y

@[to_additive]
theorem r_of_eq {x y : M × S} (h : (y.1*x.2) = x.1*y.2) : r S x y :=
  r_iff_exists.2
    ⟨1, by
      rw [h]⟩

@[to_additive]
theorem mk_self (a : S) : mk (a : M) a = 1 := by
  symm
  rw [← mk_one, mk_eq_mk_iff]
  exact one_rel a

section Scalar

variable {R R₁ R₂ : Type _}

/--  Scalar multiplication in a monoid localization is defined as `c • ⟨a, b⟩ = ⟨c • a, b⟩`. -/
protected irreducible_def smul [HasScalar R M] [IsScalarTower R M M] (c : R) (z : Localization S) : Localization S :=
  (Localization.liftOn z fun a b => mk (c • a) b) $ fun a a' b b' h =>
    mk_eq_mk_iff.2
      (by
        cases' b with b hb
        cases' b' with b' hb'
        rw [r_eq_r'] at h⊢
        cases' h with t ht
        use t
        simp only [smul_mul_assoc, ht])

instance [HasScalar R M] [IsScalarTower R M M] : HasScalar R (Localization S) where
  smul := Localization.smul

theorem smul_mk [HasScalar R M] [IsScalarTower R M M] (c : R) a b : c • (mk a b : Localization S) = mk (c • a) b := by
  unfold HasScalar.smul Localization.smul
  apply lift_on_mk

-- failed to format: format: uncaught backtrack exception
instance
  [ HasScalar R₁ M ] [ HasScalar R₂ M ] [ IsScalarTower R₁ M M ] [ IsScalarTower R₂ M M ] [ SmulCommClass R₁ R₂ M ]
    : SmulCommClass R₁ R₂ ( Localization S )
  where smul_comm s t := Localization.ind $ Prod.rec $ by exact fun r x => by simp only [ smul_mk , smul_comm s t r ]

-- failed to format: format: uncaught backtrack exception
instance
  [ HasScalar R₁ M ]
      [ HasScalar R₂ M ]
      [ IsScalarTower R₁ M M ]
      [ IsScalarTower R₂ M M ]
      [ HasScalar R₁ R₂ ]
      [ IsScalarTower R₁ R₂ M ]
    : IsScalarTower R₁ R₂ ( Localization S )
  where smul_assoc s t := Localization.ind $ Prod.rec $ by exact fun r x => by simp only [ smul_mk , smul_assoc s t r ]

-- failed to format: format: uncaught backtrack exception
instance
  smul_comm_class_right
  { R : Type _ } [ HasScalar R M ] [ IsScalarTower R M M ] : SmulCommClass R ( Localization S ) ( Localization S )
  where
    smul_comm
      s
      :=
      Localization.ind
        $
        Prod.rec
          $
          by
            exact
              fun
                r₁ x₁
                  =>
                  Localization.ind
                    $
                    Prod.rec
                      $
                      by
                        exact
                          fun r₂ x₂ => by simp only [ smul_mk , smul_eq_mul , mk_mul , mul_commₓ r₁ , smul_mul_assoc ]

-- failed to format: format: uncaught backtrack exception
instance
  is_scalar_tower_right
  { R : Type _ } [ HasScalar R M ] [ IsScalarTower R M M ] : IsScalarTower R ( Localization S ) ( Localization S )
  where
    smul_assoc
      s
      :=
      Localization.ind
        $
        Prod.rec
          $
          by
            exact
              fun
                r₁ x₁
                  =>
                  Localization.ind
                    $
                    Prod.rec $ by exact fun r₂ x₂ => by simp only [ smul_mk , smul_eq_mul , mk_mul , smul_mul_assoc ]

-- failed to format: format: uncaught backtrack exception
instance
  [ HasScalar R M ]
      [ HasScalar ( R ᵐᵒᵖ ) M ]
      [ IsScalarTower R M M ]
      [ IsScalarTower ( R ᵐᵒᵖ ) M M ]
      [ IsCentralScalar R M ]
    : IsCentralScalar R ( Localization S )
  where
    op_smul_eq_smul s := Localization.ind $ Prod.rec $ by exact fun r x => by simp only [ smul_mk , op_smul_eq_smul ]

-- failed to format: format: uncaught backtrack exception
instance
  [ Monoidₓ R ] [ MulAction R M ] [ IsScalarTower R M M ] : MulAction R ( Localization S )
  where
    one_smul := Localization.ind $ Prod.rec $ by intros simp only [ Localization.smul_mk , one_smul ]
      mul_smul s₁ s₂ := Localization.ind $ Prod.rec $ by intros simp only [ Localization.smul_mk , mul_smul ]

-- failed to format: format: uncaught backtrack exception
instance
  [ Monoidₓ R ] [ MulDistribMulAction R M ] [ IsScalarTower R M M ] : MulDistribMulAction R ( Localization S )
  where
    smul_one s := by simp only [ ← Localization.mk_one , Localization.smul_mk , smul_one ]
      smul_mul
        s x y
        :=
        Localization.induction_on₂ x y
          $
          Prod.rec
            $
            by
              exact
                fun
                  r₁ x₁
                    =>
                    Prod.rec
                      $
                      by exact fun r₂ x₂ => by simp only [ Localization.smul_mk , Localization.mk_mul , smul_mul' ]

end Scalar

end Localization

variable {S N}

namespace MonoidHom

/--  Makes a localization map from a `comm_monoid` hom satisfying the characteristic predicate. -/
@[to_additive "Makes a localization map from an `add_comm_monoid` hom satisfying the characteristic\npredicate."]
def to_localization_map (f : M →* N) (H1 : ∀ y : S, IsUnit (f y)) (H2 : ∀ z, ∃ x : M × S, (z*f x.2) = f x.1)
    (H3 : ∀ x y, f x = f y ↔ ∃ c : S, (x*c) = y*c) : Submonoid.LocalizationMap S N :=
  { f with map_units' := H1, surj' := H2, eq_iff_exists' := H3 }

end MonoidHom

namespace Submonoid

namespace LocalizationMap

/--  Short for `to_monoid_hom`; used to apply a localization map as a function. -/
@[to_additive "Short for `to_add_monoid_hom`; used to apply a localization map as a function."]
abbrev to_map (f : localization_map S N) :=
  f.to_monoid_hom

@[ext, to_additive]
theorem ext {f g : localization_map S N} (h : ∀ x, f.to_map x = g.to_map x) : f = g := by
  rcases f with ⟨⟨⟩⟩
  rcases g with ⟨⟨⟩⟩
  simp only
  exact funext h

@[to_additive]
theorem ext_iff {f g : localization_map S N} : f = g ↔ ∀ x, f.to_map x = g.to_map x :=
  ⟨fun h x => h ▸ rfl, ext⟩

@[to_additive]
theorem to_map_injective : Function.Injective (@localization_map.to_map _ _ S N _) := fun _ _ h =>
  ext $ MonoidHom.ext_iff.1 h

@[to_additive]
theorem map_units (f : localization_map S N) (y : S) : IsUnit (f.to_map y) :=
  f.2 y

@[to_additive]
theorem surj (f : localization_map S N) (z : N) : ∃ x : M × S, (z*f.to_map x.2) = f.to_map x.1 :=
  f.3 z

@[to_additive]
theorem eq_iff_exists (f : localization_map S N) {x y} : f.to_map x = f.to_map y ↔ ∃ c : S, (x*c) = y*c :=
  f.4 x y

/--  Given a localization map `f : M →* N`, a section function sending `z : N` to some
`(x, y) : M × S` such that `f x * (f y)⁻¹ = z`. -/
@[to_additive
      "Given a localization map `f : M →+ N`, a section function sending `z : N`\nto some `(x, y) : M × S` such that `f x - f y = z`."]
noncomputable def sec (f : localization_map S N) (z : N) : M × S :=
  Classical.some $ f.surj z

@[to_additive]
theorem sec_spec {f : localization_map S N} (z : N) : (z*f.to_map (f.sec z).2) = f.to_map (f.sec z).1 :=
  Classical.some_spec $ f.surj z

@[to_additive]
theorem sec_spec' {f : localization_map S N} (z : N) : f.to_map (f.sec z).1 = f.to_map (f.sec z).2*z := by
  rw [mul_commₓ, sec_spec]

/--  Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that `f(S) ⊆ units N`, for all
`w : M, z : N` and `y ∈ S`, we have `w * (f y)⁻¹ = z ↔ w = f y * z`. -/
@[to_additive
      "Given an add_monoid hom `f : M →+ N` and submonoid `S ⊆ M` such that\n`f(S) ⊆ add_units N`, for all `w : M, z : N` and `y ∈ S`, we have `w - f y = z ↔ w = f y + z`."]
theorem mul_inv_left {f : M →* N} (h : ∀ y : S, IsUnit (f y)) (y : S) w z :
    (w*↑IsUnit.liftRight (f.mrestrict S) h y⁻¹) = z ↔ w = f y*z := by
  rw [mul_commₓ] <;> convert Units.inv_mul_eq_iff_eq_mul _ <;> exact (IsUnit.coe_lift_right (f.mrestrict S) h _).symm

/--  Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that `f(S) ⊆ units N`, for all
`w : M, z : N` and `y ∈ S`, we have `z = w * (f y)⁻¹ ↔ z * f y = w`. -/
@[to_additive
      "Given an add_monoid hom `f : M →+ N` and submonoid `S ⊆ M` such that\n`f(S) ⊆ add_units N`, for all `w : M, z : N` and `y ∈ S`, we have `z = w - f y ↔ z + f y = w`."]
theorem mul_inv_right {f : M →* N} (h : ∀ y : S, IsUnit (f y)) (y : S) w z :
    (z = w*↑IsUnit.liftRight (f.mrestrict S) h y⁻¹) ↔ (z*f y) = w := by
  rw [eq_comm, mul_inv_left h, mul_commₓ, eq_comm]

/--  Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that
`f(S) ⊆ units N`, for all `x₁ x₂ : M` and `y₁, y₂ ∈ S`, we have
`f x₁ * (f y₁)⁻¹ = f x₂ * (f y₂)⁻¹ ↔ f (x₁ * y₂) = f (x₂ * y₁)`. -/
@[simp,
  to_additive
      "Given an add_monoid hom `f : M →+ N` and submonoid `S ⊆ M` such that\n`f(S) ⊆ add_units N`, for all `x₁ x₂ : M` and `y₁, y₂ ∈ S`, we have\n`f x₁ - f y₁ = f x₂ - f y₂ ↔ f (x₁ + y₂) = f (x₂ + y₁)`."]
theorem mul_inv {f : M →* N} (h : ∀ y : S, IsUnit (f y)) {x₁ x₂} {y₁ y₂ : S} :
    ((f x₁*↑IsUnit.liftRight (f.mrestrict S) h y₁⁻¹) = f x₂*↑IsUnit.liftRight (f.mrestrict S) h y₂⁻¹) ↔
      f (x₁*y₂) = f (x₂*y₁) :=
  by
  rw [mul_inv_right h, mul_assocₓ, mul_commₓ _ (f y₂), ← mul_assocₓ, mul_inv_left h, mul_commₓ x₂, f.map_mul, f.map_mul]

/--  Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that `f(S) ⊆ units N`, for all
`y, z ∈ S`, we have `(f y)⁻¹ = (f z)⁻¹ → f y = f z`. -/
@[to_additive
      "Given an add_monoid hom `f : M →+ N` and submonoid `S ⊆ M` such that\n`f(S) ⊆ add_units N`, for all `y, z ∈ S`, we have `- (f y) = - (f z) → f y = f z`."]
theorem inv_inj {f : M →* N} (hf : ∀ y : S, IsUnit (f y)) {y z}
    (h : IsUnit.liftRight (f.mrestrict S) hf y⁻¹ = IsUnit.liftRight (f.mrestrict S) hf z⁻¹) : f y = f z := by
  rw [← mul_oneₓ (f y), eq_comm, ← mul_inv_left hf y (f z) 1, h] <;>
    convert Units.inv_mul _ <;> exact (IsUnit.coe_lift_right (f.mrestrict S) hf _).symm

/--  Given a monoid hom `f : M →* N` and submonoid `S ⊆ M` such that `f(S) ⊆ units N`, for all
`y ∈ S`, `(f y)⁻¹` is unique. -/
@[to_additive
      "Given an add_monoid hom `f : M →+ N` and submonoid `S ⊆ M` such that\n`f(S) ⊆ add_units N`, for all `y ∈ S`, `- (f y)` is unique."]
theorem inv_unique {f : M →* N} (h : ∀ y : S, IsUnit (f y)) {y : S} {z} (H : (f y*z) = 1) :
    ↑IsUnit.liftRight (f.mrestrict S) h y⁻¹ = z := by
  rw [← one_mulₓ (↑_⁻¹), mul_inv_left, ← H]

variable (f : localization_map S N)

@[to_additive]
theorem map_right_cancel {x y} {c : S} (h : f.to_map (c*x) = f.to_map (c*y)) : f.to_map x = f.to_map y := by
  rw [f.to_map.map_mul, f.to_map.map_mul] at h
  cases' f.map_units c with u hu
  rw [← hu] at h
  exact (Units.mul_right_inj u).1 h

@[to_additive]
theorem map_left_cancel {x y} {c : S} (h : f.to_map (x*c) = f.to_map (y*c)) : f.to_map x = f.to_map y :=
  f.map_right_cancel $ by
    rw [mul_commₓ _ x, mul_commₓ _ y, h]

/--  Given a localization map `f : M →* N`, the surjection sending `(x, y) : M × S` to
`f x * (f y)⁻¹`. -/
@[to_additive "Given a localization map `f : M →+ N`, the surjection sending `(x, y) : M × S`\nto `f x - f y`."]
noncomputable def mk' (f : localization_map S N) (x : M) (y : S) : N :=
  f.to_map x*↑IsUnit.liftRight (f.to_map.mrestrict S) f.map_units y⁻¹

@[to_additive]
theorem mk'_mul (x₁ x₂ : M) (y₁ y₂ : S) : f.mk' (x₁*x₂) (y₁*y₂) = f.mk' x₁ y₁*f.mk' x₂ y₂ :=
  (mul_inv_left f.map_units _ _ _).2 $
    show _ = _*(_*_)*_*_ by
      rw [← mul_assocₓ, ← mul_assocₓ, mul_inv_right f.map_units, mul_assocₓ, mul_assocₓ, mul_commₓ _ (f.to_map x₂), ←
          mul_assocₓ, ← mul_assocₓ, mul_inv_right f.map_units, Submonoid.coe_mul, f.to_map.map_mul,
          f.to_map.map_mul] <;>
        ac_rfl

@[to_additive]
theorem mk'_one x : f.mk' x (1 : S) = f.to_map x := by
  rw [mk', MonoidHom.map_one] <;> exact mul_oneₓ _

/--  Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, for all `z : N` we have that if
`x : M, y ∈ S` are such that `z * f y = f x`, then `f x * (f y)⁻¹ = z`. -/
@[simp,
  to_additive
      "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M`, for all `z : N`\nwe have that if `x : M, y ∈ S` are such that `z + f y = f x`, then `f x - f y = z`."]
theorem mk'_sec (z : N) : f.mk' (f.sec z).1 (f.sec z).2 = z :=
  show (_*_) = _ by
    rw [← sec_spec, mul_inv_left, mul_commₓ]

@[to_additive]
theorem mk'_surjective (z : N) : ∃ (x : _)(y : S), f.mk' x y = z :=
  ⟨(f.sec z).1, (f.sec z).2, f.mk'_sec z⟩

@[to_additive]
theorem mk'_spec x (y : S) : (f.mk' x y*f.to_map y) = f.to_map x :=
  show ((_*_)*_) = _ by
    rw [mul_assocₓ, mul_commₓ _ (f.to_map y), ← mul_assocₓ, mul_inv_left, mul_commₓ]

@[to_additive]
theorem mk'_spec' x (y : S) : (f.to_map y*f.mk' x y) = f.to_map x := by
  rw [mul_commₓ, mk'_spec]

@[to_additive]
theorem eq_mk'_iff_mul_eq {x} {y : S} {z} : z = f.mk' x y ↔ (z*f.to_map y) = f.to_map x :=
  ⟨fun H => by
    rw [H, mk'_spec], fun H => by
    erw [mul_inv_right, H] <;> rfl⟩

@[to_additive]
theorem mk'_eq_iff_eq_mul {x} {y : S} {z} : f.mk' x y = z ↔ f.to_map x = z*f.to_map y := by
  rw [eq_comm, eq_mk'_iff_mul_eq, eq_comm]

@[to_additive]
theorem mk'_eq_iff_eq {x₁ x₂} {y₁ y₂ : S} : f.mk' x₁ y₁ = f.mk' x₂ y₂ ↔ f.to_map (x₁*y₂) = f.to_map (x₂*y₁) :=
  ⟨fun H => by
    rw [f.to_map.map_mul, f.mk'_eq_iff_eq_mul.1 H, mul_assocₓ, mul_commₓ (f.to_map _), ← mul_assocₓ, mk'_spec,
      f.to_map.map_mul],
    fun H => by
    rw [mk'_eq_iff_eq_mul, mk', mul_assocₓ, mul_commₓ _ (f.to_map y₁), ← mul_assocₓ, ← f.to_map.map_mul, ← H,
      f.to_map.map_mul, mul_inv_right f.map_units]⟩

@[to_additive]
protected theorem Eq {a₁ b₁} {a₂ b₂ : S} : f.mk' a₁ a₂ = f.mk' b₁ b₂ ↔ ∃ c : S, ((a₁*b₂)*c) = (b₁*a₂)*c :=
  f.mk'_eq_iff_eq.trans $ f.eq_iff_exists

@[to_additive]
protected theorem eq' {a₁ b₁} {a₂ b₂ : S} : f.mk' a₁ a₂ = f.mk' b₁ b₂ ↔ Localization.r S (a₁, a₂) (b₁, b₂) := by
  rw [f.eq, Localization.r_iff_exists]

@[to_additive]
theorem eq_iff_eq (g : localization_map S P) {x y} : f.to_map x = f.to_map y ↔ g.to_map x = g.to_map y :=
  f.eq_iff_exists.trans g.eq_iff_exists.symm

@[to_additive]
theorem mk'_eq_iff_mk'_eq (g : localization_map S P) {x₁ x₂} {y₁ y₂ : S} :
    f.mk' x₁ y₁ = f.mk' x₂ y₂ ↔ g.mk' x₁ y₁ = g.mk' x₂ y₂ :=
  f.eq'.trans g.eq'.symm

/--  Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, for all `x₁ : M` and `y₁ ∈ S`,
if `x₂ : M, y₂ ∈ S` are such that `f x₁ * (f y₁)⁻¹ * f y₂ = f x₂`, then there exists `c ∈ S`
such that `x₁ * y₂ * c = x₂ * y₁ * c`. -/
@[to_additive
      "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M`, for all `x₁ : M`\nand `y₁ ∈ S`, if `x₂ : M, y₂ ∈ S` are such that `(f x₁ - f y₁) + f y₂ = f x₂`, then there exists\n`c ∈ S` such that `x₁ + y₂ + c = x₂ + y₁ + c`."]
theorem exists_of_sec_mk' x (y : S) : ∃ c : S, ((x*(f.sec $ f.mk' x y).2)*c) = ((f.sec $ f.mk' x y).1*y)*c :=
  f.eq_iff_exists.1 $ f.mk'_eq_iff_eq.1 $ (mk'_sec _ _).symm

@[to_additive]
theorem mk'_eq_of_eq {a₁ b₁ : M} {a₂ b₂ : S} (H : (b₁*a₂) = a₁*b₂) : f.mk' a₁ a₂ = f.mk' b₁ b₂ :=
  f.mk'_eq_iff_eq.2 $ H ▸ rfl

@[simp, to_additive]
theorem mk'_self' (y : S) : f.mk' (y : M) y = 1 :=
  show (_*_) = _ by
    rw [mul_inv_left, mul_oneₓ]

@[simp, to_additive]
theorem mk'_self x (H : x ∈ S) : f.mk' x ⟨x, H⟩ = 1 := by
  convert mk'_self' _ _ <;> rfl

@[to_additive]
theorem mul_mk'_eq_mk'_of_mul x₁ x₂ (y : S) : (f.to_map x₁*f.mk' x₂ y) = f.mk' (x₁*x₂) y := by
  rw [← mk'_one, ← mk'_mul, one_mulₓ]

@[to_additive]
theorem mk'_mul_eq_mk'_of_mul x₁ x₂ (y : S) : (f.mk' x₂ y*f.to_map x₁) = f.mk' (x₁*x₂) y := by
  rw [mul_commₓ, mul_mk'_eq_mk'_of_mul]

@[to_additive]
theorem mul_mk'_one_eq_mk' x (y : S) : (f.to_map x*f.mk' 1 y) = f.mk' x y := by
  rw [mul_mk'_eq_mk'_of_mul, mul_oneₓ]

@[simp, to_additive]
theorem mk'_mul_cancel_right (x : M) (y : S) : f.mk' (x*y) y = f.to_map x := by
  rw [← mul_mk'_one_eq_mk', f.to_map.map_mul, mul_assocₓ, mul_mk'_one_eq_mk', mk'_self', mul_oneₓ]

@[to_additive]
theorem mk'_mul_cancel_left x (y : S) : f.mk' ((y : M)*x) y = f.to_map x := by
  rw [mul_commₓ, mk'_mul_cancel_right]

@[to_additive]
theorem is_unit_comp (j : N →* P) (y : S) : IsUnit (j.comp f.to_map y) :=
  ⟨Units.map j $ IsUnit.liftRight (f.to_map.mrestrict S) f.map_units y,
    show j _ = j _ from congr_argₓ j $ IsUnit.coe_lift_right (f.to_map.mrestrict S) f.map_units _⟩

variable {g : M →* P}

/--  Given a localization map `f : M →* N` for a submonoid `S ⊆ M` and a map of `comm_monoid`s
`g : M →* P` such that `g(S) ⊆ units P`, `f x = f y → g x = g y` for all `x y : M`. -/
@[to_additive
      "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M` and a map\nof `add_comm_monoid`s `g : M →+ P` such that `g(S) ⊆ add_units P`, `f x = f y → g x = g y`\nfor all `x y : M`."]
theorem eq_of_eq (hg : ∀ y : S, IsUnit (g y)) {x y} (h : f.to_map x = f.to_map y) : g x = g y := by
  obtain ⟨c, hc⟩ := f.eq_iff_exists.1 h
  rw [← mul_oneₓ (g x), ← IsUnit.mul_lift_right_inv (g.mrestrict S) hg c]
  show (_*g c*_) = _
  rw [← mul_assocₓ, ← g.map_mul, hc, mul_inv_left hg, g.map_mul, mul_commₓ]

/--  Given `comm_monoid`s `M, P`, localization maps `f : M →* N, k : P →* Q` for submonoids
`S, T` respectively, and `g : M →* P` such that `g(S) ⊆ T`, `f x = f y` implies
`k (g x) = k (g y)`. -/
@[to_additive
      "Given `add_comm_monoid`s `M, P`, localization maps `f : M →+ N, k : P →+ Q` for\nsubmonoids `S, T` respectively, and `g : M →+ P` such that `g(S) ⊆ T`, `f x = f y`\nimplies `k (g x) = k (g y)`."]
theorem comp_eq_of_eq {T : Submonoid P} {Q : Type _} [CommMonoidₓ Q] (hg : ∀ y : S, g y ∈ T) (k : localization_map T Q)
    {x y} (h : f.to_map x = f.to_map y) : k.to_map (g x) = k.to_map (g y) :=
  f.eq_of_eq (fun y : S => show IsUnit (k.to_map.comp g y) from k.map_units ⟨g y, hg y⟩) h

variable (hg : ∀ y : S, IsUnit (g y))

/--  Given a localization map `f : M →* N` for a submonoid `S ⊆ M` and a map of `comm_monoid`s
`g : M →* P` such that `g y` is invertible for all `y : S`, the homomorphism induced from
`N` to `P` sending `z : N` to `g x * (g y)⁻¹`, where `(x, y) : M × S` are such that
`z = f x * (f y)⁻¹`. -/
@[to_additive
      "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M` and a map\nof `add_comm_monoid`s `g : M →+ P` such that `g y` is invertible for all `y : S`, the homomorphism\ninduced from `N` to `P` sending `z : N` to `g x - g y`, where `(x, y) : M × S` are such that\n`z = f x - f y`."]
noncomputable def lift : N →* P :=
  { toFun := fun z => g (f.sec z).1*↑IsUnit.liftRight (g.mrestrict S) hg (f.sec z).2⁻¹,
    map_one' := by
      rw [mul_inv_left, mul_oneₓ] <;>
        exact
          f.eq_of_eq hg
            (by
              rw [← sec_spec, one_mulₓ]),
    map_mul' := fun x y => by
      rw [mul_inv_left hg, ← mul_assocₓ, ← mul_assocₓ, mul_inv_right hg, mul_commₓ _ (g (f.sec y).1), ← mul_assocₓ, ←
        mul_assocₓ, mul_inv_right hg]
      repeat'
        rw [← g.map_mul]
      exact
        f.eq_of_eq hg
          (by
            repeat'
                first |
                  rw [f.to_map.map_mul]|
                  rw [sec_spec'] <;>
              ac_rfl) }

variable {S g}

/--  Given a localization map `f : M →* N` for a submonoid `S ⊆ M` and a map of `comm_monoid`s
`g : M →* P` such that `g y` is invertible for all `y : S`, the homomorphism induced from
`N` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : M, y ∈ S`. -/
@[to_additive
      "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M` and a map\nof `add_comm_monoid`s `g : M →+ P` such that `g y` is invertible for all `y : S`, the homomorphism\ninduced from `N` to `P` maps `f x - f y` to `g x - g y` for all `x : M, y ∈ S`."]
theorem lift_mk' x y : f.lift hg (f.mk' x y) = g x*↑IsUnit.liftRight (g.mrestrict S) hg y⁻¹ :=
  (mul_inv hg).2 $
    f.eq_of_eq hg $ by
      rw [f.to_map.map_mul, f.to_map.map_mul, sec_spec', mul_assocₓ, f.mk'_spec, mul_commₓ]

/--  Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, if a `comm_monoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N, v : P`, we have
`f.lift hg z = v ↔ g x = g y * v`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive
      "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M`, if\nan `add_comm_monoid` map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all\n`z : N, v : P`, we have `f.lift hg z = v ↔ g x = g y + v`, where `x : M, y ∈ S` are such that\n`z + f y = f x`."]
theorem lift_spec z v : f.lift hg z = v ↔ g (f.sec z).1 = g (f.sec z).2*v :=
  mul_inv_left hg _ _ v

/--  Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, if a `comm_monoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N, v w : P`, we have
`f.lift hg z * w = v ↔ g x * w = g y * v`, where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
      "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M`, if\nan `add_comm_monoid` map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all\n`z : N, v w : P`, we have `f.lift hg z + w = v ↔ g x + w = g y + v`, where `x : M, y ∈ S` are such\nthat `z + f y = f x`."]
theorem lift_spec_mul z w v : (f.lift hg z*w) = v ↔ (g (f.sec z).1*w) = g (f.sec z).2*v := by
  rw [mul_commₓ]
  show (_*_*_) = _ ↔ _
  rw [← mul_assocₓ, mul_inv_left hg, mul_commₓ]

@[to_additive]
theorem lift_mk'_spec x v (y : S) : f.lift hg (f.mk' x y) = v ↔ g x = g y*v := by
  rw [f.lift_mk' hg] <;> exact mul_inv_left hg _ _ _

/--  Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, if a `comm_monoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N`, we have
`f.lift hg z * g y = g x`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive
      "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M`, if\nan `add_comm_monoid` map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all `z : N`, we\nhave `f.lift hg z + g y = g x`, where `x : M, y ∈ S` are such that `z + f y = f x`."]
theorem lift_mul_right z : (f.lift hg z*g (f.sec z).2) = g (f.sec z).1 :=
  show ((_*_)*_) = _ by
    erw [mul_assocₓ, IsUnit.lift_right_inv_mul, mul_oneₓ]

/--  Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, if a `comm_monoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N`, we have
`g y * f.lift hg z = g x`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive
      "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M`, if\nan `add_comm_monoid` map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all `z : N`, we\nhave `g y + f.lift hg z = g x`, where `x : M, y ∈ S` are such that `z + f y = f x`."]
theorem lift_mul_left z : (g (f.sec z).2*f.lift hg z) = g (f.sec z).1 := by
  rw [mul_commₓ, lift_mul_right]

@[simp, to_additive]
theorem lift_eq (x : M) : f.lift hg (f.to_map x) = g x := by
  rw [lift_spec, ← g.map_mul] <;>
    exact
      f.eq_of_eq hg
        (by
          rw [sec_spec', f.to_map.map_mul])

@[to_additive]
theorem lift_eq_iff {x y : M × S} : f.lift hg (f.mk' x.1 x.2) = f.lift hg (f.mk' y.1 y.2) ↔ g (x.1*y.2) = g (y.1*x.2) :=
  by
  rw [lift_mk', lift_mk', mul_inv hg]

@[simp, to_additive]
theorem lift_comp : (f.lift hg).comp f.to_map = g := by
  ext <;> exact f.lift_eq hg _

@[simp, to_additive]
theorem lift_of_comp (j : N →* P) : f.lift (f.is_unit_comp j) = j := by
  ext
  rw [lift_spec]
  show j _ = j _*_
  erw [← j.map_mul, sec_spec']

@[to_additive]
theorem epic_of_localization_map {j k : N →* P} (h : ∀ a, j.comp f.to_map a = k.comp f.to_map a) : j = k := by
  rw [← f.lift_of_comp j, ← f.lift_of_comp k]
  congr 1 with x
  exact h x

@[to_additive]
theorem lift_unique {j : N →* P} (hj : ∀ x, j (f.to_map x) = g x) : f.lift hg = j := by
  ext
  rw [lift_spec, ← hj, ← hj, ← j.map_mul]
  apply congr_argₓ
  rw [← sec_spec']

@[simp, to_additive]
theorem lift_id x : f.lift f.map_units x = x :=
  MonoidHom.ext_iff.1 (f.lift_of_comp $ MonoidHom.id N) x

/--  Given two localization maps `f : M →* N, k : M →* P` for a submonoid `S ⊆ M`,
the hom from `P` to `N` induced by `f` is left inverse to the hom from `N` to `P`
induced by `k`. -/
@[simp, to_additive]
theorem lift_left_inverse {k : localization_map S P} (z : N) : k.lift f.map_units (f.lift k.map_units z) = z := by
  rw [lift_spec]
  cases' f.surj z with x hx
  conv_rhs => congr skip rw [f.eq_mk'_iff_mul_eq.2 hx]
  rw [mk', ← mul_assocₓ, mul_inv_right f.map_units, ← f.to_map.map_mul, ← f.to_map.map_mul]
  apply k.eq_of_eq f.map_units
  rw [k.to_map.map_mul, k.to_map.map_mul, ← sec_spec, mul_assocₓ, lift_spec_mul]
  repeat'
    rw [← k.to_map.map_mul]
  apply f.eq_of_eq k.map_units
  repeat'
    rw [f.to_map.map_mul]
  rw [sec_spec', ← hx]
  ac_rfl

@[to_additive]
theorem lift_surjective_iff : Function.Surjective (f.lift hg) ↔ ∀ v : P, ∃ x : M × S, (v*g x.2) = g x.1 := by
  constructor
  ·
    intro H v
    obtain ⟨z, hz⟩ := H v
    obtain ⟨x, hx⟩ := f.surj z
    use x
    rw [← hz, f.eq_mk'_iff_mul_eq.2 hx, lift_mk', mul_assocₓ, mul_commₓ _ (g (↑x.2))]
    erw [IsUnit.mul_lift_right_inv (g.mrestrict S) hg, mul_oneₓ]
  ·
    intro H v
    obtain ⟨x, hx⟩ := H v
    use f.mk' x.1 x.2
    rw [lift_mk', mul_inv_left hg, mul_commₓ, ← hx]

@[to_additive]
theorem lift_injective_iff : Function.Injective (f.lift hg) ↔ ∀ x y, f.to_map x = f.to_map y ↔ g x = g y := by
  constructor
  ·
    intro H x y
    constructor
    ·
      exact f.eq_of_eq hg
    ·
      intro h
      rw [← f.lift_eq hg, ← f.lift_eq hg] at h
      exact H h
  ·
    intro H z w h
    obtain ⟨x, hx⟩ := f.surj z
    obtain ⟨y, hy⟩ := f.surj w
    rw [← f.mk'_sec z, ← f.mk'_sec w]
    exact (mul_inv f.map_units).2 ((H _ _).2 $ (mul_inv hg).1 h)

variable {T : Submonoid P} (hy : ∀ y : S, g y ∈ T) {Q : Type _} [CommMonoidₓ Q] (k : localization_map T Q)

/--  Given a `comm_monoid` homomorphism `g : M →* P` where for submonoids `S ⊆ M, T ⊆ P` we have
`g(S) ⊆ T`, the induced monoid homomorphism from the localization of `M` at `S` to the
localization of `P` at `T`: if `f : M →* N` and `k : P →* Q` are localization maps for `S` and
`T` respectively, we send `z : N` to `k (g x) * (k (g y))⁻¹`, where `(x, y) : M × S` are such
that `z = f x * (f y)⁻¹`. -/
@[to_additive
      "Given a `add_comm_monoid` homomorphism `g : M →+ P` where for submonoids\n`S ⊆ M, T ⊆ P` we have `g(S) ⊆ T`, the induced add_monoid homomorphism from the localization of `M`\nat `S` to the localization of `P` at `T`: if `f : M →+ N` and `k : P →+ Q` are localization maps\nfor `S` and `T` respectively, we send `z : N` to `k (g x) - k (g y)`, where `(x, y) : M × S` are\nsuch that `z = f x - f y`."]
noncomputable def map : N →* Q :=
  @lift _ _ _ _ _ _ _ f (k.to_map.comp g) $ fun y => k.map_units ⟨g y, hy y⟩

variable {k}

@[to_additive]
theorem map_eq x : f.map hy k (f.to_map x) = k.to_map (g x) :=
  f.lift_eq (fun y => k.map_units ⟨g y, hy y⟩) x

@[simp, to_additive]
theorem map_comp : (f.map hy k).comp f.to_map = k.to_map.comp g :=
  f.lift_comp $ fun y => k.map_units ⟨g y, hy y⟩

@[to_additive]
theorem map_mk' x (y : S) : f.map hy k (f.mk' x y) = k.mk' (g x) ⟨g y, hy y⟩ := by
  rw [map, lift_mk', mul_inv_left]
  ·
    show k.to_map (g x) = k.to_map (g y)*_
    rw [mul_mk'_eq_mk'_of_mul]
    exact (k.mk'_mul_cancel_left (g x) ⟨g y, hy y⟩).symm

/--  Given localization maps `f : M →* N, k : P →* Q` for submonoids `S, T` respectively, if a
`comm_monoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
`u : Q`, we have `f.map hy k z = u ↔ k (g x) = k (g y) * u` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
      "Given localization maps `f : M →+ N, k : P →+ Q` for submonoids `S, T` respectively,\nif an `add_comm_monoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then for all\n`z : N`, `u : Q`, we have `f.map hy k z = u ↔ k (g x) = k (g y) + u` where `x : M, y ∈ S` are such\nthat `z + f y = f x`."]
theorem map_spec z u : f.map hy k z = u ↔ k.to_map (g (f.sec z).1) = k.to_map (g (f.sec z).2)*u :=
  f.lift_spec (fun y => k.map_units ⟨g y, hy y⟩) _ _

/--  Given localization maps `f : M →* N, k : P →* Q` for submonoids `S, T` respectively, if a
`comm_monoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
we have `f.map hy k z * k (g y) = k (g x)` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
      "Given localization maps `f : M →+ N, k : P →+ Q` for submonoids `S, T` respectively,\nif an `add_comm_monoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then\nfor all `z : N`, we have `f.map hy k z + k (g y) = k (g x)` where `x : M, y ∈ S` are such that\n`z + f y = f x`."]
theorem map_mul_right z : (f.map hy k z*k.to_map (g (f.sec z).2)) = k.to_map (g (f.sec z).1) :=
  f.lift_mul_right (fun y => k.map_units ⟨g y, hy y⟩) _

/--  Given localization maps `f : M →* N, k : P →* Q` for submonoids `S, T` respectively, if a
`comm_monoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
we have `k (g y) * f.map hy k z = k (g x)` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
      "Given localization maps `f : M →+ N, k : P →+ Q` for submonoids `S, T` respectively,\nif an `add_comm_monoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then for all\n`z : N`, we have `k (g y) + f.map hy k z = k (g x)` where `x : M, y ∈ S` are such that\n`z + f y = f x`."]
theorem map_mul_left z : (k.to_map (g (f.sec z).2)*f.map hy k z) = k.to_map (g (f.sec z).1) := by
  rw [mul_commₓ, f.map_mul_right]

@[simp, to_additive]
theorem map_id (z : N) : f.map (fun y => show MonoidHom.id M y ∈ S from y.2) f z = z :=
  f.lift_id z

/--  If `comm_monoid` homs `g : M →* P, l : P →* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
@[to_additive
      "If `add_comm_monoid` homs `g : M →+ P, l : P →+ A` induce maps of localizations,\nthe composition of the induced maps equals the map of localizations induced by `l ∘ g`."]
theorem map_comp_map {A : Type _} [CommMonoidₓ A] {U : Submonoid A} {R} [CommMonoidₓ R] (j : localization_map U R)
    {l : P →* A} (hl : ∀ w : T, l w ∈ U) :
    (k.map hl j).comp (f.map hy k) = f.map (fun x => show l.comp g x ∈ U from hl ⟨g x, hy x⟩) j := by
  ext z
  show (j.to_map _*_) = j.to_map (l _)*_
  ·
    rw [mul_inv_left, ← mul_assocₓ, mul_inv_right]
    show (j.to_map _*j.to_map (l (g _))) = j.to_map (l _)*_
    rw [← j.to_map.map_mul, ← j.to_map.map_mul, ← l.map_mul, ← l.map_mul]
    exact
      k.comp_eq_of_eq hl j
        (by
          rw [k.to_map.map_mul, k.to_map.map_mul, sec_spec', mul_assocₓ, map_mul_right])

/--  If `comm_monoid` homs `g : M →* P, l : P →* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
@[to_additive
      "If `add_comm_monoid` homs `g : M →+ P, l : P →+ A` induce maps of localizations,\nthe composition of the induced maps equals the map of localizations induced by `l ∘ g`."]
theorem map_map {A : Type _} [CommMonoidₓ A] {U : Submonoid A} {R} [CommMonoidₓ R] (j : localization_map U R)
    {l : P →* A} (hl : ∀ w : T, l w ∈ U) x :
    k.map hl j (f.map hy k x) = f.map (fun x => show l.comp g x ∈ U from hl ⟨g x, hy x⟩) j x := by
  rw [← f.map_comp_map hy j hl] <;> rfl

section AwayMap

variable (x : M)

/--  Given `x : M`, the type of `comm_monoid` homomorphisms `f : M →* N` such that `N`
is isomorphic to the localization of `M` at the submonoid generated by `x`. -/
@[reducible,
  to_additive
      "Given `x : M`, the type of `add_comm_monoid` homomorphisms `f : M →+ N`\nsuch that `N` is isomorphic to the localization of `M` at the submonoid generated by `x`."]
def away_map (N' : Type _) [CommMonoidₓ N'] :=
  localization_map (powers x) N'

variable (F : away_map x N)

/--  Given `x : M` and a localization map `F : M →* N` away from `x`, `inv_self` is `(F x)⁻¹`. -/
noncomputable def away_map.inv_self : N :=
  F.mk' 1 ⟨x, mem_powers _⟩

/--  Given `x : M`, a localization map `F : M →* N` away from `x`, and a map of `comm_monoid`s
`g : M →* P` such that `g x` is invertible, the homomorphism induced from `N` to `P` sending
`z : N` to `g y * (g x)⁻ⁿ`, where `y : M, n : ℕ` are such that `z = F y * (F x)⁻ⁿ`. -/
noncomputable def away_map.lift (hg : IsUnit (g x)) : N →* P :=
  F.lift $ fun y =>
    show IsUnit (g y.1)by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn, g.map_pow]
      exact IsUnit.pow n hg

@[simp]
theorem away_map.lift_eq (hg : IsUnit (g x)) (a : M) : F.lift x hg (F.to_map a) = g a :=
  lift_eq _ _ _

@[simp]
theorem away_map.lift_comp (hg : IsUnit (g x)) : (F.lift x hg).comp F.to_map = g :=
  lift_comp _ _

/--  Given `x y : M` and localization maps `F : M →* N, G : M →* P` away from `x` and `x * y`
respectively, the homomorphism induced from `N` to `P`. -/
noncomputable def away_to_away_right (y : M) (G : away_map (x*y) P) : N →* P :=
  F.lift x $
    show IsUnit (G.to_map x) from
      is_unit_of_mul_eq_one (G.to_map x) (G.mk' y ⟨x*y, mem_powers _⟩) $ by
        rw [mul_mk'_eq_mk'_of_mul, mk'_self]

end AwayMap

end LocalizationMap

end Submonoid

namespace AddSubmonoid

namespace LocalizationMap

section AwayMap

variable {A : Type _} [AddCommMonoidₓ A] (x : A) {B : Type _} [AddCommMonoidₓ B] (F : away_map x B) {C : Type _}
  [AddCommMonoidₓ C] {g : A →+ C}

/--  Given `x : A` and a localization map `F : A →+ B` away from `x`, `neg_self` is `- (F x)`. -/
noncomputable def away_map.neg_self : B :=
  F.mk' 0 ⟨x, mem_multiples _⟩

/--  Given `x : A`, a localization map `F : A →+ B` away from `x`, and a map of `add_comm_monoid`s
`g : A →+ C` such that `g x` is invertible, the homomorphism induced from `B` to `C` sending
`z : B` to `g y - n • g x`, where `y : A, n : ℕ` are such that `z = F y - n • F x`. -/
noncomputable def away_map.lift (hg : IsAddUnit (g x)) : B →+ C :=
  F.lift $ fun y =>
    show IsAddUnit (g y.1)by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn]
      dsimp
      rw [g.map_nsmul]
      exact IsAddUnit.map (nsmulAddMonoidHom n) hg

@[simp]
theorem away_map.lift_eq (hg : IsAddUnit (g x)) (a : A) : F.lift x hg (F.to_map a) = g a :=
  lift_eq _ _ _

@[simp]
theorem away_map.lift_comp (hg : IsAddUnit (g x)) : (F.lift x hg).comp F.to_map = g :=
  lift_comp _ _

/--  Given `x y : A` and localization maps `F : A →+ B, G : A →+ C` away from `x` and `x + y`
respectively, the homomorphism induced from `B` to `C`. -/
noncomputable def away_to_away_right (y : A) (G : away_map (x+y) C) : B →+ C :=
  F.lift x $
    show IsAddUnit (G.to_map x) from
      is_add_unit_of_add_eq_zero (G.to_map x) (G.mk' y ⟨x+y, mem_multiples _⟩) $ by
        rw [add_mk'_eq_mk'_of_add, mk'_self]

end AwayMap

end LocalizationMap

end AddSubmonoid

namespace Submonoid

namespace LocalizationMap

variable (f : S.localization_map N) {g : M →* P} (hg : ∀ y : S, IsUnit (g y)) {T : Submonoid P} {Q : Type _}
  [CommMonoidₓ Q]

/--  If `f : M →* N` and `k : M →* P` are localization maps for a submonoid `S`, we get an
isomorphism of `N` and `P`. -/
@[to_additive
      "If `f : M →+ N` and `k : M →+ R` are localization maps for a submonoid `S`,\nwe get an isomorphism of `N` and `R`."]
noncomputable def mul_equiv_of_localizations (k : localization_map S P) : N ≃* P :=
  ⟨f.lift k.map_units, k.lift f.map_units, f.lift_left_inverse, k.lift_left_inverse, MonoidHom.map_mul _⟩

@[simp, to_additive]
theorem mul_equiv_of_localizations_apply {k : localization_map S P} {x} :
    f.mul_equiv_of_localizations k x = f.lift k.map_units x :=
  rfl

@[simp, to_additive]
theorem mul_equiv_of_localizations_symm_apply {k : localization_map S P} {x} :
    (f.mul_equiv_of_localizations k).symm x = k.lift f.map_units x :=
  rfl

@[to_additive]
theorem mul_equiv_of_localizations_symm_eq_mul_equiv_of_localizations {k : localization_map S P} :
    (k.mul_equiv_of_localizations f).symm = f.mul_equiv_of_localizations k :=
  rfl

/--  If `f : M →* N` is a localization map for a submonoid `S` and `k : N ≃* P` is an isomorphism
of `comm_monoid`s, `k ∘ f` is a localization map for `M` at `S`. -/
@[to_additive
      "If `f : M →+ N` is a localization map for a submonoid `S` and `k : N ≃+ P` is an\nisomorphism of `add_comm_monoid`s, `k ∘ f` is a localization map for `M` at `S`."]
def of_mul_equiv_of_localizations (k : N ≃* P) : localization_map S P :=
  (k.to_monoid_hom.comp f.to_map).toLocalizationMap (fun y => is_unit_comp f k.to_monoid_hom y)
    (fun v =>
      let ⟨z, hz⟩ := k.to_equiv.surjective v
      let ⟨x, hx⟩ := f.surj z
      ⟨x,
        show (v*k _) = k _ by
          rw [← hx, k.map_mul, ← hz] <;> rfl⟩)
    fun x y => k.apply_eq_iff_eq.trans f.eq_iff_exists

@[simp, to_additive]
theorem of_mul_equiv_of_localizations_apply {k : N ≃* P} x :
    (f.of_mul_equiv_of_localizations k).toMap x = k (f.to_map x) :=
  rfl

@[to_additive]
theorem of_mul_equiv_of_localizations_eq {k : N ≃* P} :
    (f.of_mul_equiv_of_localizations k).toMap = k.to_monoid_hom.comp f.to_map :=
  rfl

@[to_additive]
theorem symm_comp_of_mul_equiv_of_localizations_apply {k : N ≃* P} x :
    k.symm ((f.of_mul_equiv_of_localizations k).toMap x) = f.to_map x :=
  k.symm_apply_apply (f.to_map x)

@[to_additive]
theorem symm_comp_of_mul_equiv_of_localizations_apply' {k : P ≃* N} x :
    k ((f.of_mul_equiv_of_localizations k.symm).toMap x) = f.to_map x :=
  k.apply_symm_apply (f.to_map x)

@[to_additive]
theorem of_mul_equiv_of_localizations_eq_iff_eq {k : N ≃* P} {x y} :
    (f.of_mul_equiv_of_localizations k).toMap x = y ↔ f.to_map x = k.symm y :=
  k.to_equiv.eq_symm_apply.symm

@[to_additive add_equiv_of_localizations_right_inv]
theorem mul_equiv_of_localizations_right_inv (k : localization_map S P) :
    f.of_mul_equiv_of_localizations (f.mul_equiv_of_localizations k) = k :=
  to_map_injective $ f.lift_comp k.map_units

@[simp, to_additive add_equiv_of_localizations_right_inv_apply]
theorem mul_equiv_of_localizations_right_inv_apply {k : localization_map S P} {x} :
    (f.of_mul_equiv_of_localizations (f.mul_equiv_of_localizations k)).toMap x = k.to_map x :=
  ext_iff.1 (f.mul_equiv_of_localizations_right_inv k) x

@[to_additive]
theorem mul_equiv_of_localizations_left_inv (k : N ≃* P) :
    f.mul_equiv_of_localizations (f.of_mul_equiv_of_localizations k) = k :=
  MulEquiv.ext $ MonoidHom.ext_iff.1 $ f.lift_of_comp k.to_monoid_hom

@[simp, to_additive]
theorem mul_equiv_of_localizations_left_inv_apply {k : N ≃* P} x :
    f.mul_equiv_of_localizations (f.of_mul_equiv_of_localizations k) x = k x := by
  rw [mul_equiv_of_localizations_left_inv]

@[simp, to_additive]
theorem of_mul_equiv_of_localizations_id : f.of_mul_equiv_of_localizations (MulEquiv.refl N) = f := by
  ext <;> rfl

@[to_additive]
theorem of_mul_equiv_of_localizations_comp {k : N ≃* P} {j : P ≃* Q} :
    (f.of_mul_equiv_of_localizations (k.trans j)).toMap =
      j.to_monoid_hom.comp (f.of_mul_equiv_of_localizations k).toMap :=
  by
  ext <;> rfl

/--  Given `comm_monoid`s `M, P` and submonoids `S ⊆ M, T ⊆ P`, if `f : M →* N` is a localization
map for `S` and `k : P ≃* M` is an isomorphism of `comm_monoid`s such that `k(T) = S`, `f ∘ k`
is a localization map for `T`. -/
@[to_additive
      "Given `comm_monoid`s `M, P` and submonoids `S ⊆ M, T ⊆ P`, if `f : M →* N` is\na localization map for `S` and `k : P ≃* M` is an isomorphism of `comm_monoid`s such that\n`k(T) = S`, `f ∘ k` is a localization map for `T`."]
def of_mul_equiv_of_dom {k : P ≃* M} (H : T.map k.to_monoid_hom = S) : localization_map T N :=
  let H' : S.comap k.to_monoid_hom = T := H ▸ (SetLike.coe_injective $ T.1.preimage_image_eq k.to_equiv.injective)
  (f.to_map.comp k.to_monoid_hom).toLocalizationMap
    (fun y =>
      let ⟨z, hz⟩ := f.map_units ⟨k y, H ▸ Set.mem_image_of_mem k y.2⟩
      ⟨z, hz⟩)
    (fun z =>
      let ⟨x, hx⟩ := f.surj z
      let ⟨v, hv⟩ := k.to_equiv.surjective x.1
      let ⟨w, hw⟩ := k.to_equiv.surjective x.2
      ⟨(v, ⟨w, H' ▸ show k w ∈ S from hw.symm ▸ x.2.2⟩),
        show (z*f.to_map (k.to_equiv w)) = f.to_map (k.to_equiv v)by
          erw [hv, hw, hx] <;> rfl⟩)
    fun x y =>
    show f.to_map _ = f.to_map _ ↔ _ by
      erw [f.eq_iff_exists] <;>
        exact
          ⟨fun ⟨c, hc⟩ =>
            let ⟨d, hd⟩ := k.to_equiv.surjective c
            ⟨⟨d, H' ▸ show k d ∈ S from hd.symm ▸ c.2⟩, by
              erw [← hd, ← k.map_mul, ← k.map_mul] at hc <;> exact k.to_equiv.injective hc⟩,
            fun ⟨c, hc⟩ =>
            ⟨⟨k c, H ▸ Set.mem_image_of_mem k c.2⟩, by
              erw [← k.map_mul] <;> rw [hc, k.map_mul] <;> rfl⟩⟩

@[simp, to_additive]
theorem of_mul_equiv_of_dom_apply {k : P ≃* M} (H : T.map k.to_monoid_hom = S) x :
    (f.of_mul_equiv_of_dom H).toMap x = f.to_map (k x) :=
  rfl

@[to_additive]
theorem of_mul_equiv_of_dom_eq {k : P ≃* M} (H : T.map k.to_monoid_hom = S) :
    (f.of_mul_equiv_of_dom H).toMap = f.to_map.comp k.to_monoid_hom :=
  rfl

@[to_additive]
theorem of_mul_equiv_of_dom_comp_symm {k : P ≃* M} (H : T.map k.to_monoid_hom = S) x :
    (f.of_mul_equiv_of_dom H).toMap (k.symm x) = f.to_map x :=
  congr_argₓ f.to_map $ k.apply_symm_apply x

@[to_additive]
theorem of_mul_equiv_of_dom_comp {k : M ≃* P} (H : T.map k.symm.to_monoid_hom = S) x :
    (f.of_mul_equiv_of_dom H).toMap (k x) = f.to_map x :=
  congr_argₓ f.to_map $ k.symm_apply_apply x

/--  A special case of `f ∘ id = f`, `f` a localization map. -/
@[simp, to_additive "A special case of `f ∘ id = f`, `f` a localization map."]
theorem of_mul_equiv_of_dom_id :
    f.of_mul_equiv_of_dom
        (show S.map (MulEquiv.refl M).toMonoidHom = S from
          Submonoid.ext $ fun x => ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun h => ⟨x, h, rfl⟩⟩) =
      f :=
  by
  ext <;> rfl

/--  Given localization maps `f : M →* N, k : P →* U` for submonoids `S, T` respectively, an
isomorphism `j : M ≃* P` such that `j(S) = T` induces an isomorphism of localizations
`N ≃* U`. -/
@[to_additive
      "Given localization maps `f : M →+ N, k : P →+ U` for submonoids `S, T` respectively,\nan isomorphism `j : M ≃+ P` such that `j(S) = T` induces an isomorphism of\nlocalizations `N ≃+ U`."]
noncomputable def mul_equiv_of_mul_equiv (k : localization_map T Q) {j : M ≃* P} (H : S.map j.to_monoid_hom = T) :
    N ≃* Q :=
  f.mul_equiv_of_localizations $ k.of_mul_equiv_of_dom H

@[simp, to_additive]
theorem mul_equiv_of_mul_equiv_eq_map_apply {k : localization_map T Q} {j : M ≃* P} (H : S.map j.to_monoid_hom = T) x :
    f.mul_equiv_of_mul_equiv k H x =
      f.map (fun y : S => show j.to_monoid_hom y ∈ T from H ▸ Set.mem_image_of_mem j y.2) k x :=
  rfl

@[to_additive]
theorem mul_equiv_of_mul_equiv_eq_map {k : localization_map T Q} {j : M ≃* P} (H : S.map j.to_monoid_hom = T) :
    (f.mul_equiv_of_mul_equiv k H).toMonoidHom =
      f.map (fun y : S => show j.to_monoid_hom y ∈ T from H ▸ Set.mem_image_of_mem j y.2) k :=
  rfl

@[simp, to_additive]
theorem mul_equiv_of_mul_equiv_eq {k : localization_map T Q} {j : M ≃* P} (H : S.map j.to_monoid_hom = T) x :
    f.mul_equiv_of_mul_equiv k H (f.to_map x) = k.to_map (j x) :=
  f.map_eq (fun y : S => H ▸ Set.mem_image_of_mem j y.2) _

@[simp, to_additive]
theorem mul_equiv_of_mul_equiv_mk' {k : localization_map T Q} {j : M ≃* P} (H : S.map j.to_monoid_hom = T) x y :
    f.mul_equiv_of_mul_equiv k H (f.mk' x y) = k.mk' (j x) ⟨j y, H ▸ Set.mem_image_of_mem j y.2⟩ :=
  f.map_mk' (fun y : S => H ▸ Set.mem_image_of_mem j y.2) _ _

@[simp, to_additive]
theorem of_mul_equiv_of_mul_equiv_apply {k : localization_map T Q} {j : M ≃* P} (H : S.map j.to_monoid_hom = T) x :
    (f.of_mul_equiv_of_localizations (f.mul_equiv_of_mul_equiv k H)).toMap x = k.to_map (j x) :=
  ext_iff.1 (f.mul_equiv_of_localizations_right_inv (k.of_mul_equiv_of_dom H)) x

@[to_additive]
theorem of_mul_equiv_of_mul_equiv {k : localization_map T Q} {j : M ≃* P} (H : S.map j.to_monoid_hom = T) :
    (f.of_mul_equiv_of_localizations (f.mul_equiv_of_mul_equiv k H)).toMap = k.to_map.comp j.to_monoid_hom :=
  MonoidHom.ext $ f.of_mul_equiv_of_mul_equiv_apply H

end LocalizationMap

end Submonoid

namespace Localization

variable (S)

/--  Natural hom sending `x : M`, `M` a `comm_monoid`, to the equivalence class of
`(x, 1)` in the localization of `M` at a submonoid. -/
@[to_additive
      "Natural homomorphism sending `x : M`, `M` an `add_comm_monoid`, to the equivalence\nclass of `(x, 0)` in the localization of `M` at a submonoid."]
def monoid_of : Submonoid.LocalizationMap S (Localization S) :=
  { (r S).mk'.comp $ MonoidHom.inl M S with toFun := fun x => mk x 1, map_one' := mk_one,
    map_mul' := fun x y => by
      rw [mk_mul, mul_oneₓ],
    map_units' := fun y =>
      is_unit_iff_exists_inv.2
        ⟨mk 1 y, by
          rw [mk_mul, mul_oneₓ, one_mulₓ, mk_self]⟩,
    surj' := fun z =>
      induction_on z $ fun x =>
        ⟨x, by
          rw [mk_mul, mul_commₓ x.fst, ← mk_mul, mk_self, one_mulₓ]⟩,
    eq_iff_exists' := fun x y =>
      mk_eq_mk_iff.trans $
        r_iff_exists.trans $
          show (∃ c : S, ((x*1)*c) = (y*1)*c) ↔ _ by
            rw [mul_oneₓ, mul_oneₓ] }

variable {S}

@[to_additive]
theorem mk_one_eq_monoid_of_mk x : mk x 1 = (monoid_of S).toMap x :=
  rfl

@[to_additive]
theorem mk_eq_monoid_of_mk'_apply x y : mk x y = (monoid_of S).mk' x y :=
  show _ = _*_ from
    (Submonoid.LocalizationMap.mul_inv_right (monoid_of S).map_units _ _ _).2 $ by
      rw [← mk_one_eq_monoid_of_mk, ← mk_one_eq_monoid_of_mk,
        show (mk x y*mk y 1) = mk (x*y) (1*y)by
          rw [mul_commₓ 1 y, mk_mul],
        show mk x 1 = mk (x*1) ((1 : S)*1)by
          rw [mul_oneₓ, mul_oneₓ]]
      exact mk_eq_mk_iff.2 (Con.symm _ $ (Localization.r S).mul (Con.refl _ (x, 1)) $ one_rel _)

@[simp, to_additive]
theorem mk_eq_monoid_of_mk' : mk = (monoid_of S).mk' :=
  funext $ fun _ => funext $ fun _ => mk_eq_monoid_of_mk'_apply _ _

universe u

@[simp, to_additive]
theorem lift_on_mk' {p : Sort u} (f : ∀ a : M b : S, p) H (a : M) (b : S) :
    lift_on ((monoid_of S).mk' a b) f H = f a b := by
  rw [← mk_eq_monoid_of_mk', lift_on_mk]

@[simp, to_additive]
theorem lift_on₂_mk' {p : Sort _} (f : M → S → M → S → p) H (a c : M) (b d : S) :
    lift_on₂ ((monoid_of S).mk' a b) ((monoid_of S).mk' c d) f H = f a b c d := by
  rw [← mk_eq_monoid_of_mk', lift_on₂_mk]

variable (f : Submonoid.LocalizationMap S N)

/--  Given a localization map `f : M →* N` for a submonoid `S`, we get an isomorphism between
the localization of `M` at `S` as a quotient type and `N`. -/
@[to_additive
      "Given a localization map `f : M →+ N` for a submonoid `S`, we get an isomorphism\nbetween the localization of `M` at `S` as a quotient type and `N`."]
noncomputable def mul_equiv_of_quotient (f : Submonoid.LocalizationMap S N) : Localization S ≃* N :=
  (monoid_of S).mulEquivOfLocalizations f

variable {f}

@[simp, to_additive]
theorem mul_equiv_of_quotient_apply x : mul_equiv_of_quotient f x = (monoid_of S).lift f.map_units x :=
  rfl

@[simp, to_additive]
theorem mul_equiv_of_quotient_mk' x y : mul_equiv_of_quotient f ((monoid_of S).mk' x y) = f.mk' x y :=
  (monoid_of S).lift_mk' _ _ _

@[to_additive]
theorem mul_equiv_of_quotient_mk x y : mul_equiv_of_quotient f (mk x y) = f.mk' x y := by
  rw [mk_eq_monoid_of_mk'_apply] <;> exact mul_equiv_of_quotient_mk' _ _

@[simp, to_additive]
theorem mul_equiv_of_quotient_monoid_of x : mul_equiv_of_quotient f ((monoid_of S).toMap x) = f.to_map x :=
  (monoid_of S).liftEq _ _

@[simp, to_additive]
theorem mul_equiv_of_quotient_symm_mk' x y : (mul_equiv_of_quotient f).symm (f.mk' x y) = (monoid_of S).mk' x y :=
  f.lift_mk' _ _ _

@[to_additive]
theorem mul_equiv_of_quotient_symm_mk x y : (mul_equiv_of_quotient f).symm (f.mk' x y) = mk x y := by
  rw [mk_eq_monoid_of_mk'_apply] <;> exact mul_equiv_of_quotient_symm_mk' _ _

@[simp, to_additive]
theorem mul_equiv_of_quotient_symm_monoid_of x : (mul_equiv_of_quotient f).symm (f.to_map x) = (monoid_of S).toMap x :=
  f.lift_eq _ _

section Away

variable (x : M)

/--  Given `x : M`, the localization of `M` at the submonoid generated by `x`, as a quotient. -/
@[reducible, to_additive "Given `x : M`, the localization of `M` at the submonoid generated\nby `x`, as a quotient."]
def away :=
  Localization (Submonoid.powers x)

/--  Given `x : M`, `inv_self` is `x⁻¹` in the localization (as a quotient type) of `M` at the
submonoid generated by `x`. -/
@[to_additive
      "Given `x : M`, `neg_self` is `-x` in the localization (as a quotient type) of `M`\nat the submonoid generated by `x`."]
def away.inv_self : away x :=
  mk 1 ⟨x, Submonoid.mem_powers _⟩

/--  Given `x : M`, the natural hom sending `y : M`, `M` a `comm_monoid`, to the equivalence class
of `(y, 1)` in the localization of `M` at the submonoid generated by `x`. -/
@[reducible,
  to_additive
      "Given `x : M`, the natural hom sending `y : M`, `M` an `add_comm_monoid`,\nto the equivalence class of `(y, 0)` in the localization of `M` at the submonoid\ngenerated by `x`."]
def away.monoid_of : Submonoid.LocalizationMap.AwayMap x (away x) :=
  monoid_of (Submonoid.powers x)

@[simp, to_additive]
theorem away.mk_eq_monoid_of_mk' : mk = (away.monoid_of x).mk' :=
  mk_eq_monoid_of_mk'

/--  Given `x : M` and a localization map `f : M →* N` away from `x`, we get an isomorphism between
the localization of `M` at the submonoid generated by `x` as a quotient type and `N`. -/
@[to_additive
      "Given `x : M` and a localization map `f : M →+ N` away from `x`, we get an\nisomorphism between the localization of `M` at the submonoid generated by `x` as a quotient type\nand `N`."]
noncomputable def away.mul_equiv_of_quotient (f : Submonoid.LocalizationMap.AwayMap x N) : away x ≃* N :=
  mul_equiv_of_quotient f

end Away

end Localization

