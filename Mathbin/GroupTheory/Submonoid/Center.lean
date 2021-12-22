import Mathbin.GroupTheory.Submonoid.Operations
import Mathbin.Data.Fintype.Basic

/-!
# Centers of magmas and monoids

## Main definitions

* `set.center`: the center of a magma
* `submonoid.center`: the center of a monoid
* `set.add_center`: the center of an additive magma
* `add_submonoid.center`: the center of an additive monoid

We provide `subgroup.center`, `add_subgroup.center`, `subsemiring.center`, and `subring.center` in
other files.
-/


variable {M : Type _}

namespace Set

variable (M)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" " The center of a magma. -/")]
  [(Term.attributes
    "@["
    [(Term.attrInstance
      (Term.attrKind [])
      (Attr.toAdditive "to_additive" [`add_center] [(strLit "\" The center of an additive magma. \"")]))]
    "]")]
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `center [])
  (Command.optDeclSig [(Term.instBinder "[" [] (Term.app `Mul [`M]) "]")] [(Term.typeSpec ":" (Term.app `Set [`M]))])
  (Command.declValSimple
   ":="
   (Set.«term{_|_}»
    "{"
    `z
    "|"
    (Term.forall
     "∀"
     [(Term.simpleBinder [`m] [])]
     ","
     («term_=_» (Finset.Data.Finset.Fold.«term_*_» `m "*" `z) "=" (Finset.Data.Finset.Fold.«term_*_» `z "*" `m)))
    "}")
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
  (Set.«term{_|_}»
   "{"
   `z
   "|"
   (Term.forall
    "∀"
    [(Term.simpleBinder [`m] [])]
    ","
    («term_=_» (Finset.Data.Finset.Fold.«term_*_» `m "*" `z) "=" (Finset.Data.Finset.Fold.«term_*_» `z "*" `m)))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`m] [])]
   ","
   («term_=_» (Finset.Data.Finset.Fold.«term_*_» `m "*" `z) "=" (Finset.Data.Finset.Fold.«term_*_» `z "*" `m)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Finset.Data.Finset.Fold.«term_*_» `m "*" `z) "=" (Finset.Data.Finset.Fold.«term_*_» `z "*" `m))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» `z "*" `m)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `z
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Finset.Data.Finset.Fold.«term_*_» `m "*" `z)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `z
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Finset.Data.Finset.Fold.«term_*_» `m "*" `z) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
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
/-- The center of a magma. -/ @[ to_additive add_center " The center of an additive magma. " ]
  def center [ Mul M ] : Set M := { z | ∀ m , m * z = z * m }

@[to_additive mem_add_center]
theorem mem_center_iff [Mul M] {z : M} : z ∈ center M ↔ ∀ g, (g*z) = z*g :=
  Iff.rfl

instance decidable_mem_center [Mul M] [DecidableEq M] [Fintype M] : DecidablePred (· ∈ center M) := fun _ =>
  decidableOfIff' _ (mem_center_iff M)

@[simp, to_additive zero_mem_add_center]
theorem one_mem_center [MulOneClass M] : (1 : M) ∈ Set.Center M := by
  simp [mem_center_iff]

@[simp]
theorem zero_mem_center [MulZeroClass M] : (0 : M) ∈ Set.Center M := by
  simp [mem_center_iff]

variable {M}

@[simp, to_additive add_mem_add_center]
theorem mul_mem_center [Semigroupₓ M] {a b : M} (ha : a ∈ Set.Center M) (hb : b ∈ Set.Center M) :
    (a*b) ∈ Set.Center M := fun g => by
  rw [mul_assocₓ, ← hb g, ← mul_assocₓ, ha g, mul_assocₓ]

@[simp, to_additive neg_mem_add_center]
theorem inv_mem_center [Groupₓ M] {a : M} (ha : a ∈ Set.Center M) : a⁻¹ ∈ Set.Center M := fun g => by
  rw [← inv_inj, mul_inv_rev, inv_invₓ, ← ha, mul_inv_rev, inv_invₓ]

@[simp]
theorem add_mem_center [Distrib M] {a b : M} (ha : a ∈ Set.Center M) (hb : b ∈ Set.Center M) : (a+b) ∈ Set.Center M :=
  fun c => by
  rw [add_mulₓ, mul_addₓ, ha c, hb c]

@[simp]
theorem neg_mem_center [Ringₓ M] {a : M} (ha : a ∈ Set.Center M) : -a ∈ Set.Center M := fun c => by
  rw [← neg_mul_comm, ha (-c), neg_mul_comm]

@[to_additive subset_add_center_add_units]
theorem subset_center_units [Monoidₓ M] : (coeₓ : Units M → M) ⁻¹' center M ⊆ Set.Center (Units M) := fun a ha b =>
  Units.ext $ ha _

theorem center_units_subset [GroupWithZeroₓ M] : Set.Center (Units M) ⊆ (coeₓ : Units M → M) ⁻¹' center M :=
  fun a ha b => by
  obtain rfl | hb := eq_or_ne b 0
  ·
    rw [zero_mul, mul_zero]
  ·
    exact units.ext_iff.mp (ha (Units.mk0 _ hb))

/--  In a group with zero, the center of the units is the preimage of the center. -/
theorem center_units_eq [GroupWithZeroₓ M] : Set.Center (Units M) = (coeₓ : Units M → M) ⁻¹' center M :=
  subset.antisymm center_units_subset subset_center_units

@[simp]
theorem inv_mem_center₀ [GroupWithZeroₓ M] {a : M} (ha : a ∈ Set.Center M) : a⁻¹ ∈ Set.Center M := by
  obtain rfl | ha0 := eq_or_ne a 0
  ·
    rw [inv_zero]
    exact zero_mem_center M
  lift a to Units M using ha0
  rw [← Units.coe_inv']
  exact center_units_subset (inv_mem_center (subset_center_units ha))

@[simp, to_additive sub_mem_add_center]
theorem div_mem_center [Groupₓ M] {a b : M} (ha : a ∈ Set.Center M) (hb : b ∈ Set.Center M) : a / b ∈ Set.Center M := by
  rw [div_eq_mul_inv]
  exact mul_mem_center ha (inv_mem_center hb)

@[simp]
theorem div_mem_center₀ [GroupWithZeroₓ M] {a b : M} (ha : a ∈ Set.Center M) (hb : b ∈ Set.Center M) :
    a / b ∈ Set.Center M := by
  rw [div_eq_mul_inv]
  exact mul_mem_center ha (inv_mem_center₀ hb)

variable (M)

@[simp, to_additive add_center_eq_univ]
theorem center_eq_univ [CommSemigroupₓ M] : center M = Set.Univ :=
  subset.antisymm (subset_univ _) $ fun x _ y => mul_commₓ y x

end Set

namespace Submonoid

section

variable (M) [Monoidₓ M]

/--  The center of a monoid `M` is the set of elements that commute with everything in `M` -/
@[to_additive "The center of a monoid `M` is the set of elements that commute with everything in\n`M`"]
def center : Submonoid M :=
  { Carrier := Set.Center M, one_mem' := Set.one_mem_center M, mul_mem' := fun a b => Set.mul_mem_center }

@[to_additive]
theorem coe_center : ↑center M = Set.Center M :=
  rfl

variable {M}

@[to_additive]
theorem mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, (g*z) = z*g :=
  Iff.rfl

instance decidable_mem_center [DecidableEq M] [Fintype M] : DecidablePred (· ∈ center M) := fun _ =>
  decidableOfIff' _ mem_center_iff

/--  The center of a monoid is commutative. -/
instance : CommMonoidₓ (center M) :=
  { (center M).toMonoid with mul_comm := fun a b => Subtype.ext $ b.prop _ }

end

section

variable (M) [CommMonoidₓ M]

@[simp]
theorem center_eq_top : center M = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ M)

end

end Submonoid

