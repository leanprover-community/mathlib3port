import Mathbin.Algebra.Quotient
import Mathbin.GroupTheory.Subgroup.Basic

/-!
# Cosets

This file develops the basic theory of left and right cosets.

## Main definitions

* `left_coset a s`: the left coset `a * s` for an element `a : α` and a subset `s ⊆ α`, for an
  `add_group` this is `left_add_coset a s`.
* `right_coset s a`: the right coset `s * a` for an element `a : α` and a subset `s ⊆ α`, for an
  `add_group` this is `right_add_coset s a`.
* `quotient_group.quotient s`: the quotient type representing the left cosets with respect to a
  subgroup `s`, for an `add_group` this is `quotient_add_group.quotient s`.
* `quotient_group.mk`: the canonical map from `α` to `α/s` for a subgroup `s` of `α`, for an
  `add_group` this is `quotient_add_group.mk`.
* `subgroup.left_coset_equiv_subgroup`: the natural bijection between a left coset and the subgroup,
  for an `add_group` this is `add_subgroup.left_coset_equiv_add_subgroup`.

## Notation

* `a *l s`: for `left_coset a s`.
* `a +l s`: for `left_add_coset a s`.
* `s *r a`: for `right_coset s a`.
* `s +r a`: for `right_add_coset s a`.

* `G ⧸ H` is the quotient of the (additive) group `G` by the (additive) subgroup `H`

## TODO

Add `to_additive` to `preimage_mk_equiv_subgroup_times_set`.
-/


open Set Function

variable {α : Type _}

/--  The left coset `a * s` for an element `a : α` and a subset `s : set α` -/
@[to_additive LeftAddCoset "The left coset `a+s` for an element `a : α`\nand a subset `s : set α`"]
def LeftCoset [Mul α] (a : α) (s : Set α) : Set α :=
  (fun x => a*x) '' s

/--  The right coset `s * a` for an element `a : α` and a subset `s : set α` -/
@[to_additive RightAddCoset "The right coset `s+a` for an element `a : α`\nand a subset `s : set α`"]
def RightCoset [Mul α] (s : Set α) (a : α) : Set α :=
  (fun x => x*a) '' s

localized [Coset] infixl:70 " *l " => LeftCoset

localized [Coset] infixl:70 " +l " => LeftAddCoset

localized [Coset] infixl:70 " *r " => RightCoset

localized [Coset] infixl:70 " +r " => RightAddCoset

section CosetMul

variable [Mul α]

@[to_additive mem_left_add_coset]
theorem mem_left_coset {s : Set α} {x : α} (a : α) (hxS : x ∈ s) : (a*x) ∈ a *l s :=
  mem_image_of_mem (fun b : α => a*b) hxS

@[to_additive mem_right_add_coset]
theorem mem_right_coset {s : Set α} {x : α} (a : α) (hxS : x ∈ s) : (x*a) ∈ s *r a :=
  mem_image_of_mem (fun b : α => b*a) hxS

/--  Equality of two left cosets `a * s` and `b * s`. -/
@[to_additive LeftAddCosetEquivalence "Equality of two left cosets `a + s` and `b + s`."]
def LeftCosetEquivalence (s : Set α) (a b : α) :=
  a *l s = b *l s

@[to_additive left_add_coset_equivalence_rel]
theorem left_coset_equivalence_rel (s : Set α) : Equivalenceₓ (LeftCosetEquivalence s) :=
  mk_equivalence (LeftCosetEquivalence s) (fun a => rfl) (fun a b => Eq.symm) fun a b c => Eq.trans

/--  Equality of two right cosets `s * a` and `s * b`. -/
@[to_additive RightAddCosetEquivalence "Equality of two right cosets `s + a` and `s + b`."]
def RightCosetEquivalence (s : Set α) (a b : α) :=
  s *r a = s *r b

@[to_additive right_add_coset_equivalence_rel]
theorem right_coset_equivalence_rel (s : Set α) : Equivalenceₓ (RightCosetEquivalence s) :=
  mk_equivalence (RightCosetEquivalence s) (fun a => rfl) (fun a b => Eq.symm) fun a b c => Eq.trans

end CosetMul

section CosetSemigroup

variable [Semigroupₓ α]

@[simp, to_additive left_add_coset_assoc]
theorem left_coset_assoc (s : Set α) (a b : α) : a *l (b *l s) = (a*b) *l s := by
  simp [LeftCoset, RightCoset, (image_comp _ _ _).symm, Function.comp, mul_assocₓ]

@[simp, to_additive right_add_coset_assoc]
theorem right_coset_assoc (s : Set α) (a b : α) : s *r a *r b = s *r a*b := by
  simp [LeftCoset, RightCoset, (image_comp _ _ _).symm, Function.comp, mul_assocₓ]

@[to_additive left_add_coset_right_add_coset]
theorem left_coset_right_coset (s : Set α) (a b : α) : a *l s *r b = a *l (s *r b) := by
  simp [LeftCoset, RightCoset, (image_comp _ _ _).symm, Function.comp, mul_assocₓ]

end CosetSemigroup

section CosetMonoid

variable [Monoidₓ α] (s : Set α)

@[simp, to_additive zero_left_add_coset]
theorem one_left_coset : 1 *l s = s :=
  Set.ext $ by
    simp [LeftCoset]

@[simp, to_additive right_add_coset_zero]
theorem right_coset_one : s *r 1 = s :=
  Set.ext $ by
    simp [RightCoset]

end CosetMonoid

section CosetSubmonoid

open Submonoid

variable [Monoidₓ α] (s : Submonoid α)

@[to_additive mem_own_left_add_coset]
theorem mem_own_left_coset (a : α) : a ∈ a *l s :=
  suffices (a*1) ∈ a *l s by
    simpa
  mem_left_coset a (one_mem s)

@[to_additive mem_own_right_add_coset]
theorem mem_own_right_coset (a : α) : a ∈ (s : Set α) *r a :=
  suffices (1*a) ∈ (s : Set α) *r a by
    simpa
  mem_right_coset a (one_mem s)

@[to_additive mem_left_add_coset_left_add_coset]
theorem mem_left_coset_left_coset {a : α} (ha : a *l s = s) : a ∈ s := by
  rw [← SetLike.mem_coe, ← ha] <;> exact mem_own_left_coset s a

@[to_additive mem_right_add_coset_right_add_coset]
theorem mem_right_coset_right_coset {a : α} (ha : (s : Set α) *r a = s) : a ∈ s := by
  rw [← SetLike.mem_coe, ← ha] <;> exact mem_own_right_coset s a

end CosetSubmonoid

section CosetGroup

variable [Groupₓ α] {s : Set α} {x : α}

@[to_additive mem_left_add_coset_iff]
theorem mem_left_coset_iff (a : α) : x ∈ a *l s ↔ (a⁻¹*x) ∈ s :=
  Iff.intro
    (fun ⟨b, hb, Eq⟩ => by
      simp [Eq.symm, hb])
    fun h =>
    ⟨a⁻¹*x, h, by
      simp ⟩

@[to_additive mem_right_add_coset_iff]
theorem mem_right_coset_iff (a : α) : x ∈ s *r a ↔ (x*a⁻¹) ∈ s :=
  Iff.intro
    (fun ⟨b, hb, Eq⟩ => by
      simp [Eq.symm, hb])
    fun h =>
    ⟨x*a⁻¹, h, by
      simp ⟩

end CosetGroup

section CosetSubgroup

open Subgroup

variable [Groupₓ α] (s : Subgroup α)

@[to_additive left_add_coset_mem_left_add_coset]
theorem left_coset_mem_left_coset {a : α} (ha : a ∈ s) : a *l s = s :=
  Set.ext $ by
    simp [mem_left_coset_iff, mul_mem_cancel_left s (s.inv_mem ha)]

@[to_additive right_add_coset_mem_right_add_coset]
theorem right_coset_mem_right_coset {a : α} (ha : a ∈ s) : (s : Set α) *r a = s :=
  Set.ext $ fun b => by
    simp [mem_right_coset_iff, mul_mem_cancel_right s (s.inv_mem ha)]

@[to_additive eq_add_cosets_of_normal]
theorem eq_cosets_of_normal (N : s.normal) (g : α) : g *l s = s *r g :=
  Set.ext $ fun a => by
    simp [mem_left_coset_iff, mem_right_coset_iff] <;> rw [N.mem_comm_iff]

@[to_additive normal_of_eq_add_cosets]
theorem normal_of_eq_cosets (h : ∀ g : α, g *l s = s *r g) : s.normal :=
  ⟨fun a ha g =>
    show ((g*a)*g⁻¹) ∈ (s : Set α)by
      rw [← mem_right_coset_iff, ← h] <;> exact mem_left_coset g ha⟩

@[to_additive normal_iff_eq_add_cosets]
theorem normal_iff_eq_cosets : s.normal ↔ ∀ g : α, g *l s = s *r g :=
  ⟨@eq_cosets_of_normal _ _ s, normal_of_eq_cosets s⟩

@[to_additive left_add_coset_eq_iff]
theorem left_coset_eq_iff {x y : α} : LeftCoset x s = LeftCoset y s ↔ (x⁻¹*y) ∈ s := by
  rw [Set.ext_iff]
  simp_rw [mem_left_coset_iff, SetLike.mem_coe]
  constructor
  ·
    intro h
    apply (h y).mpr
    rw [mul_left_invₓ]
    exact s.one_mem
  ·
    intro h z
    rw [← mul_inv_cancel_rightₓ (x⁻¹) y]
    rw [mul_assocₓ]
    exact s.mul_mem_cancel_left h

@[to_additive right_add_coset_eq_iff]
theorem right_coset_eq_iff {x y : α} : RightCoset (↑s) x = RightCoset s y ↔ (y*x⁻¹) ∈ s := by
  rw [Set.ext_iff]
  simp_rw [mem_right_coset_iff, SetLike.mem_coe]
  constructor
  ·
    intro h
    apply (h y).mpr
    rw [mul_right_invₓ]
    exact s.one_mem
  ·
    intro h z
    rw [← inv_mul_cancel_leftₓ y (x⁻¹)]
    rw [← mul_assocₓ]
    exact s.mul_mem_cancel_right h

end CosetSubgroup

run_cmd
  to_additive.map_namespace `quotient_group `quotient_add_group

namespace QuotientGroup

variable [Groupₓ α] (s : Subgroup α)

/--  The equivalence relation corresponding to the partition of a group by left cosets
of a subgroup.-/
@[to_additive "The equivalence relation corresponding to the partition of a group by left cosets\nof a subgroup."]
def left_rel : Setoidₓ α :=
  ⟨fun x y => (x⁻¹*y) ∈ s, by
    simp_rw [← left_coset_eq_iff]
    exact left_coset_equivalence_rel s⟩

theorem left_rel_r_eq_left_coset_equivalence : @Setoidₓ.R _ (QuotientGroup.leftRel s) = LeftCosetEquivalence s := by
  ext
  exact (left_coset_eq_iff s).symm

@[to_additive]
instance left_rel_decidable [DecidablePred (· ∈ s)] : DecidableRel (left_rel s).R := fun x y =>
  ‹DecidablePred (· ∈ s)› _

/--  `α ⧸ s` is the quotient type representing the left cosets of `s`.
  If `s` is a normal subgroup, `α ⧸ s` is a group -/
@[to_additive
      "`α ⧸ s` is the quotient type representing the left cosets of `s`.  If `s` is a\nnormal subgroup, `α ⧸ s` is a group"]
instance : HasQuotient α (Subgroup α) :=
  ⟨fun s => Quotientₓ (left_rel s)⟩

/--  The equivalence relation corresponding to the partition of a group by right cosets of a
subgroup. -/
@[to_additive "The equivalence relation corresponding to the partition of a group by right cosets of\na subgroup."]
def right_rel : Setoidₓ α :=
  ⟨fun x y => (y*x⁻¹) ∈ s, by
    simp_rw [← right_coset_eq_iff]
    exact right_coset_equivalence_rel s⟩

theorem right_rel_r_eq_right_coset_equivalence : @Setoidₓ.R _ (QuotientGroup.rightRel s) = RightCosetEquivalence s := by
  ext
  exact (right_coset_eq_iff s).symm

@[to_additive]
instance right_rel_decidable [DecidablePred (· ∈ s)] : DecidableRel (right_rel s).R := fun x y =>
  ‹DecidablePred (· ∈ s)› _

end QuotientGroup

namespace QuotientGroup

variable [Groupₓ α] {s : Subgroup α}

@[to_additive]
instance Fintype [Fintype α] (s : Subgroup α) [DecidableRel (left_rel s).R] : Fintype (α ⧸ s) :=
  Quotientₓ.fintype (left_rel s)

/--  The canonical map from a group `α` to the quotient `α ⧸ s`. -/
@[to_additive "The canonical map from an `add_group` `α` to the quotient `α ⧸ s`."]
abbrev mk (a : α) : α ⧸ s :=
  Quotientₓ.mk' a

@[elab_as_eliminator, to_additive]
theorem induction_on {C : α ⧸ s → Prop} (x : α ⧸ s) (H : ∀ z, C (QuotientGroup.mk z)) : C x :=
  Quotientₓ.induction_on' x H

@[to_additive]
instance : CoeTₓ α (α ⧸ s) :=
  ⟨mk⟩

@[elab_as_eliminator, to_additive]
theorem induction_on' {C : α ⧸ s → Prop} (x : α ⧸ s) (H : ∀ z : α, C z) : C x :=
  Quotientₓ.induction_on' x H

@[simp, to_additive]
theorem quotient_lift_on_coe {β} (f : α → β) h (x : α) : Quotientₓ.liftOn' (x : α ⧸ s) f h = f x :=
  rfl

@[to_additive]
theorem forall_coe {C : α ⧸ s → Prop} : (∀ x : α ⧸ s, C x) ↔ ∀ x : α, C x :=
  ⟨fun hx x => hx _, Quot.ind⟩

@[to_additive]
instance (s : Subgroup α) : Inhabited (α ⧸ s) :=
  ⟨((1 : α) : α ⧸ s)⟩

@[to_additive QuotientAddGroup.eq]
protected theorem Eq {a b : α} : (a : α ⧸ s) = b ↔ (a⁻¹*b) ∈ s :=
  Quotientₓ.eq'

@[to_additive QuotientAddGroup.eq']
theorem eq' {a b : α} : (mk a : α ⧸ s) = mk b ↔ (a⁻¹*b) ∈ s :=
  QuotientGroup.eq

@[to_additive QuotientAddGroup.out_eq']
theorem out_eq' (a : α ⧸ s) : mk a.out' = a :=
  Quotientₓ.out_eq' a

variable (s)

@[to_additive QuotientAddGroup.mk_out'_eq_mul]
theorem mk_out'_eq_mul (g : α) : ∃ h : s, (mk g : α ⧸ s).out' = g*h :=
  ⟨⟨g⁻¹*(mk g).out', eq'.mp (mk g).out_eq'.symm⟩, by
    rw [s.coe_mk, mul_inv_cancel_left]⟩

variable {s}

@[to_additive QuotientAddGroup.mk_mul_of_mem]
theorem mk_mul_of_mem (g₁ g₂ : α) (hg₂ : g₂ ∈ s) : (mk (g₁*g₂) : α ⧸ s) = mk g₁ := by
  rwa [eq', mul_inv_rev, inv_mul_cancel_right, s.inv_mem_iff]

@[to_additive]
theorem eq_class_eq_left_coset (s : Subgroup α) (g : α) : { x : α | (x : α ⧸ s) = g } = LeftCoset g s :=
  Set.ext $ fun z => by
    rw [mem_left_coset_iff, Set.mem_set_of_eq, eq_comm, QuotientGroup.eq, SetLike.mem_coe]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.toAdditive "to_additive" [] []))] "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `preimage_image_coe [])
  (Command.declSig
   [(Term.explicitBinder "(" [`N] [":" (Term.app `Subgroup [`α])] [] ")")
    (Term.explicitBinder "(" [`s] [":" (Term.app `Set [`α])] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Set.Data.Set.Basic.«term_⁻¹'_»
      `coeₓ
      " ⁻¹' "
      (Set.Data.Set.Basic.term_''_
       (Term.paren
        "("
        [`coeₓ [(Term.typeAscription ":" (Term.arrow `α "→" (Algebra.Quotient.«term_⧸_» `α " ⧸ " `N)))]]
        ")")
       " '' "
       `s))
     "="
     (Set.Data.Set.Lattice.«term⋃_,_»
      "⋃"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `N]))
      ", "
      (Set.Data.Set.Basic.«term_⁻¹'_»
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`y] [(Term.typeSpec ":" `α)])]
         "=>"
         (Finset.Data.Finset.Fold.«term_*_» `y "*" `x)))
       " ⁻¹' "
       `s)))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `QuotientGroup.eq)
           ","
           (Tactic.simpLemma [] [] `SetLike.exists)
           ","
           (Tactic.simpLemma [] [] `exists_prop)
           ","
           (Tactic.simpLemma [] [] `Set.mem_preimage)
           ","
           (Tactic.simpLemma [] [] `Set.mem_Union)
           ","
           (Tactic.simpLemma [] [] `Set.mem_image)
           ","
           (Tactic.simpLemma [] [] `Subgroup.coe_mk)
           ","
           (Tactic.simpLemma [] ["←"] `eq_inv_mul_iff_mul_eq)]
          "]"]
         [])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [(Term.fun
            "fun"
            (Term.basicFun
             [(Term.anonymousCtor "⟨" [`y "," `hs "," `hN] "⟩")]
             "=>"
             (Term.anonymousCtor
              "⟨"
              [(Term.hole "_")
               ","
               (Term.app `N.inv_mem [`hN])
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hs]) [])])))]
              "⟩")))
           ","
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.anonymousCtor "⟨" [`z "," `hz "," `hxz] "⟩")]
             "=>"
             (Term.anonymousCtor
              "⟨"
              [(Finset.Data.Finset.Fold.«term_*_» `x "*" `z)
               ","
               `hxz
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hz]) [])])))]
              "⟩")))]
          "⟩"))
        [])])))
   [])
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
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `QuotientGroup.eq)
          ","
          (Tactic.simpLemma [] [] `SetLike.exists)
          ","
          (Tactic.simpLemma [] [] `exists_prop)
          ","
          (Tactic.simpLemma [] [] `Set.mem_preimage)
          ","
          (Tactic.simpLemma [] [] `Set.mem_Union)
          ","
          (Tactic.simpLemma [] [] `Set.mem_image)
          ","
          (Tactic.simpLemma [] [] `Subgroup.coe_mk)
          ","
          (Tactic.simpLemma [] ["←"] `eq_inv_mul_iff_mul_eq)]
         "]"]
        [])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.anonymousCtor
         "⟨"
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.anonymousCtor "⟨" [`y "," `hs "," `hN] "⟩")]
            "=>"
            (Term.anonymousCtor
             "⟨"
             [(Term.hole "_")
              ","
              (Term.app `N.inv_mem [`hN])
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hs]) [])])))]
             "⟩")))
          ","
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.anonymousCtor "⟨" [`z "," `hz "," `hxz] "⟩")]
            "=>"
            (Term.anonymousCtor
             "⟨"
             [(Finset.Data.Finset.Fold.«term_*_» `x "*" `z)
              ","
              `hxz
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hz]) [])])))]
             "⟩")))]
         "⟩"))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.anonymousCtor
    "⟨"
    [(Term.fun
      "fun"
      (Term.basicFun
       [(Term.anonymousCtor "⟨" [`y "," `hs "," `hN] "⟩")]
       "=>"
       (Term.anonymousCtor
        "⟨"
        [(Term.hole "_")
         ","
         (Term.app `N.inv_mem [`hN])
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hs]) [])])))]
        "⟩")))
     ","
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.anonymousCtor "⟨" [`z "," `hz "," `hxz] "⟩")]
       "=>"
       (Term.anonymousCtor
        "⟨"
        [(Finset.Data.Finset.Fold.«term_*_» `x "*" `z)
         ","
         `hxz
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hz]) [])])))]
        "⟩")))]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.anonymousCtor "⟨" [`y "," `hs "," `hN] "⟩")]
      "=>"
      (Term.anonymousCtor
       "⟨"
       [(Term.hole "_")
        ","
        (Term.app `N.inv_mem [`hN])
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hs]) [])])))]
       "⟩")))
    ","
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.anonymousCtor "⟨" [`z "," `hz "," `hxz] "⟩")]
      "=>"
      (Term.anonymousCtor
       "⟨"
       [(Finset.Data.Finset.Fold.«term_*_» `x "*" `z)
        ","
        `hxz
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hz]) [])])))]
       "⟩")))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.anonymousCtor "⟨" [`z "," `hz "," `hxz] "⟩")]
    "=>"
    (Term.anonymousCtor
     "⟨"
     [(Finset.Data.Finset.Fold.«term_*_» `x "*" `z)
      ","
      `hxz
      ","
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hz]) [])])))]
     "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Finset.Data.Finset.Fold.«term_*_» `x "*" `z)
    ","
    `hxz
    ","
    (Term.byTactic
     "by"
     (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hz]) [])])))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hz]) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa "simpa" [] [] [] [] ["using" `hz])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hz
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hxz
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» `x "*" `z)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `z
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`z "," `hz "," `hxz] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hxz
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hz
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `z
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.anonymousCtor "⟨" [`y "," `hs "," `hN] "⟩")]
    "=>"
    (Term.anonymousCtor
     "⟨"
     [(Term.hole "_")
      ","
      (Term.app `N.inv_mem [`hN])
      ","
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hs]) [])])))]
     "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.hole "_")
    ","
    (Term.app `N.inv_mem [`hN])
    ","
    (Term.byTactic
     "by"
     (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hs]) [])])))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hs]) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa "simpa" [] [] [] [] ["using" `hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `N.inv_mem [`hN])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hN
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `N.inv_mem
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`y "," `hs "," `hN] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hN
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `QuotientGroup.eq)
     ","
     (Tactic.simpLemma [] [] `SetLike.exists)
     ","
     (Tactic.simpLemma [] [] `exists_prop)
     ","
     (Tactic.simpLemma [] [] `Set.mem_preimage)
     ","
     (Tactic.simpLemma [] [] `Set.mem_Union)
     ","
     (Tactic.simpLemma [] [] `Set.mem_image)
     ","
     (Tactic.simpLemma [] [] `Subgroup.coe_mk)
     ","
     (Tactic.simpLemma [] ["←"] `eq_inv_mul_iff_mul_eq)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eq_inv_mul_iff_mul_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Subgroup.coe_mk
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_image
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_Union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_preimage
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `exists_prop
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `SetLike.exists
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `QuotientGroup.eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Set.Data.Set.Basic.«term_⁻¹'_»
    `coeₓ
    " ⁻¹' "
    (Set.Data.Set.Basic.term_''_
     (Term.paren
      "("
      [`coeₓ [(Term.typeAscription ":" (Term.arrow `α "→" (Algebra.Quotient.«term_⧸_» `α " ⧸ " `N)))]]
      ")")
     " '' "
     `s))
   "="
   (Set.Data.Set.Lattice.«term⋃_,_»
    "⋃"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `N]))
    ", "
    (Set.Data.Set.Basic.«term_⁻¹'_»
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`y] [(Term.typeSpec ":" `α)])]
       "=>"
       (Finset.Data.Finset.Fold.«term_*_» `y "*" `x)))
     " ⁻¹' "
     `s)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Lattice.«term⋃_,_»
   "⋃"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `N]))
   ", "
   (Set.Data.Set.Basic.«term_⁻¹'_»
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`y] [(Term.typeSpec ":" `α)])]
      "=>"
      (Finset.Data.Finset.Fold.«term_*_» `y "*" `x)))
    " ⁻¹' "
    `s))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Basic.«term_⁻¹'_»
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`y] [(Term.typeSpec ":" `α)])]
     "=>"
     (Finset.Data.Finset.Fold.«term_*_» `y "*" `x)))
   " ⁻¹' "
   `s)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.«term_⁻¹'_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`y] [(Term.typeSpec ":" `α)])]
    "=>"
    (Finset.Data.Finset.Fold.«term_*_» `y "*" `x)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» `y "*" `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (some 0, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`y] [(Term.typeSpec ":" `α)])]
    "=>"
    (Finset.Data.Finset.Fold.«term_*_» `y "*" `x)))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 81, term) <=? (none, [anonymous])
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
@[ to_additive ]
  theorem
    preimage_image_coe
    ( N : Subgroup α ) ( s : Set α ) : coeₓ ⁻¹' ( coeₓ : α → α ⧸ N ) '' s = ⋃ x : N , fun y : α => y * x ⁻¹' s
    :=
      by
        ext x
          simp
            only
            [
              QuotientGroup.eq
                ,
                SetLike.exists
                ,
                exists_prop
                ,
                Set.mem_preimage
                ,
                Set.mem_Union
                ,
                Set.mem_image
                ,
                Subgroup.coe_mk
                ,
                ← eq_inv_mul_iff_mul_eq
              ]
          exact
            ⟨
              fun ⟨ y , hs , hN ⟩ => ⟨ _ , N.inv_mem hN , by simpa using hs ⟩
                ,
                fun ⟨ z , hz , hxz ⟩ => ⟨ x * z , hxz , by simpa using hz ⟩
              ⟩

end QuotientGroup

namespace Subgroup

open QuotientGroup

variable [Groupₓ α] {s : Subgroup α}

/--  The natural bijection between a left coset `g * s` and `s`. -/
@[to_additive "The natural bijection between the cosets `g + s` and `s`."]
def left_coset_equiv_subgroup (g : α) : LeftCoset g s ≃ s :=
  ⟨fun x => ⟨g⁻¹*x.1, (mem_left_coset_iff _).1 x.2⟩, fun x => ⟨g*x.1, x.1, x.2, rfl⟩, fun ⟨x, hx⟩ =>
    Subtype.eq $ by
      simp ,
    fun ⟨g, hg⟩ =>
    Subtype.eq $ by
      simp ⟩

/--  The natural bijection between a right coset `s * g` and `s`. -/
@[to_additive "The natural bijection between the cosets `s + g` and `s`."]
def right_coset_equiv_subgroup (g : α) : RightCoset (↑s) g ≃ s :=
  ⟨fun x => ⟨x.1*g⁻¹, (mem_right_coset_iff _).1 x.2⟩, fun x => ⟨x.1*g, x.1, x.2, rfl⟩, fun ⟨x, hx⟩ =>
    Subtype.eq $ by
      simp ,
    fun ⟨g, hg⟩ =>
    Subtype.eq $ by
      simp ⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" " A (non-canonical) bijection between a group `α` and the product `(α/s) × s` -/")]
  [(Term.attributes
    "@["
    [(Term.attrInstance
      (Term.attrKind [])
      (Attr.toAdditive
       "to_additive"
       []
       [(strLit "\"A (non-canonical) bijection between an add_group `α` and the product `(α/s) × s`\"")]))]
    "]")]
  []
  [(Command.noncomputable "noncomputable")]
  []
  [])
 (Command.def
  "def"
  (Command.declId `group_equiv_quotient_times_subgroup [])
  (Command.optDeclSig
   []
   [(Term.typeSpec
     ":"
     (Data.Equiv.Basic.«term_≃_» `α " ≃ " («term_×_» (Algebra.Quotient.«term_⧸_» `α " ⧸ " `s) "×" `s)))])
  (Command.declValSimple
   ":="
   (calc
    "calc"
    [(calcStep
      (Data.Equiv.Basic.«term_≃_»
       `α
       " ≃ "
       (Init.Data.Sigma.Basic.«termΣ_,_»
        "Σ"
        (Lean.explicitBinders
         (Lean.unbracketedExplicitBinders [(Lean.binderIdent `L)] [":" (Algebra.Quotient.«term_⧸_» `α " ⧸ " `s)]))
        ", "
        («term{__:_//_}»
         "{"
         `x
         [":" `α]
         "//"
         («term_=_»
          (Term.paren "(" [`x [(Term.typeAscription ":" (Algebra.Quotient.«term_⧸_» `α " ⧸ " `s))]] ")")
          "="
          `L)
         "}")))
      ":="
      (Term.proj (Term.app `Equivₓ.sigmaPreimageEquiv [`QuotientGroup.mk]) "." `symm))
     (calcStep
      (Data.Equiv.Basic.«term_≃_»
       (Term.hole "_")
       " ≃ "
       (Init.Data.Sigma.Basic.«termΣ_,_»
        "Σ"
        (Lean.explicitBinders
         (Lean.unbracketedExplicitBinders [(Lean.binderIdent `L)] [":" (Algebra.Quotient.«term_⧸_» `α " ⧸ " `s)]))
        ", "
        (Term.app `LeftCoset [(Term.app `Quotientₓ.out' [`L]) `s])))
      ":="
      (Term.app
       `Equivₓ.sigmaCongrRight
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`L] [])]
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `eq_class_eq_left_coset)] "]") [])
               [])
              (group
               (Tactic.tacticShow_
                "show"
                (Data.Equiv.Basic.«term_≃_»
                 (Term.app
                  `_root_.subtype
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`x] [(Term.typeSpec ":" `α)])]
                     "=>"
                     («term_=_» (Term.app `Quotientₓ.mk' [`x]) "=" `L)))])
                 " ≃ "
                 (Term.app
                  `_root_.subtype
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`x] [(Term.typeSpec ":" `α)])]
                     "=>"
                     («term_=_» (Term.app `Quotientₓ.mk' [`x]) "=" (Term.app `Quotientₓ.mk' [(Term.hole "_")]))))])))
               [])
              (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpErase "-" `Quotientₓ.eq')] "]"] []) [])])))))]))
     (calcStep
      (Data.Equiv.Basic.«term_≃_»
       (Term.hole "_")
       " ≃ "
       (Init.Data.Sigma.Basic.«termΣ_,_»
        "Σ"
        (Lean.explicitBinders
         (Lean.unbracketedExplicitBinders [(Lean.binderIdent `L)] [":" (Algebra.Quotient.«term_⧸_» `α " ⧸ " `s)]))
        ", "
        `s))
      ":="
      (Term.app
       `Equivₓ.sigmaCongrRight
       [(Term.fun
         "fun"
         (Term.basicFun [(Term.simpleBinder [`L] [])] "=>" (Term.app `left_coset_equiv_subgroup [(Term.hole "_")])))]))
     (calcStep
      (Data.Equiv.Basic.«term_≃_» (Term.hole "_") " ≃ " («term_×_» (Algebra.Quotient.«term_⧸_» `α " ⧸ " `s) "×" `s))
      ":="
      (Term.app `Equivₓ.sigmaEquivProd [(Term.hole "_") (Term.hole "_")]))])
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
  (calc
   "calc"
   [(calcStep
     (Data.Equiv.Basic.«term_≃_»
      `α
      " ≃ "
      (Init.Data.Sigma.Basic.«termΣ_,_»
       "Σ"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `L)] [":" (Algebra.Quotient.«term_⧸_» `α " ⧸ " `s)]))
       ", "
       («term{__:_//_}»
        "{"
        `x
        [":" `α]
        "//"
        («term_=_»
         (Term.paren "(" [`x [(Term.typeAscription ":" (Algebra.Quotient.«term_⧸_» `α " ⧸ " `s))]] ")")
         "="
         `L)
        "}")))
     ":="
     (Term.proj (Term.app `Equivₓ.sigmaPreimageEquiv [`QuotientGroup.mk]) "." `symm))
    (calcStep
     (Data.Equiv.Basic.«term_≃_»
      (Term.hole "_")
      " ≃ "
      (Init.Data.Sigma.Basic.«termΣ_,_»
       "Σ"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `L)] [":" (Algebra.Quotient.«term_⧸_» `α " ⧸ " `s)]))
       ", "
       (Term.app `LeftCoset [(Term.app `Quotientₓ.out' [`L]) `s])))
     ":="
     (Term.app
      `Equivₓ.sigmaCongrRight
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`L] [])]
         "=>"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `eq_class_eq_left_coset)] "]") [])
              [])
             (group
              (Tactic.tacticShow_
               "show"
               (Data.Equiv.Basic.«term_≃_»
                (Term.app
                 `_root_.subtype
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`x] [(Term.typeSpec ":" `α)])]
                    "=>"
                    («term_=_» (Term.app `Quotientₓ.mk' [`x]) "=" `L)))])
                " ≃ "
                (Term.app
                 `_root_.subtype
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`x] [(Term.typeSpec ":" `α)])]
                    "=>"
                    («term_=_» (Term.app `Quotientₓ.mk' [`x]) "=" (Term.app `Quotientₓ.mk' [(Term.hole "_")]))))])))
              [])
             (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpErase "-" `Quotientₓ.eq')] "]"] []) [])])))))]))
    (calcStep
     (Data.Equiv.Basic.«term_≃_»
      (Term.hole "_")
      " ≃ "
      (Init.Data.Sigma.Basic.«termΣ_,_»
       "Σ"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `L)] [":" (Algebra.Quotient.«term_⧸_» `α " ⧸ " `s)]))
       ", "
       `s))
     ":="
     (Term.app
      `Equivₓ.sigmaCongrRight
      [(Term.fun
        "fun"
        (Term.basicFun [(Term.simpleBinder [`L] [])] "=>" (Term.app `left_coset_equiv_subgroup [(Term.hole "_")])))]))
    (calcStep
     (Data.Equiv.Basic.«term_≃_» (Term.hole "_") " ≃ " («term_×_» (Algebra.Quotient.«term_⧸_» `α " ⧸ " `s) "×" `s))
     ":="
     (Term.app `Equivₓ.sigmaEquivProd [(Term.hole "_") (Term.hole "_")]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calc', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Equivₓ.sigmaEquivProd [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Equivₓ.sigmaEquivProd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Equiv.Basic.«term_≃_» (Term.hole "_") " ≃ " («term_×_» (Algebra.Quotient.«term_⧸_» `α " ⧸ " `s) "×" `s))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Equiv.Basic.«term_≃_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_×_» (Algebra.Quotient.«term_⧸_» `α " ⧸ " `s) "×" `s)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
  (Algebra.Quotient.«term_⧸_» `α " ⧸ " `s)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 34 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
  `α
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 35, (some 34, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Algebra.Quotient.«term_⧸_» `α " ⧸ " `s) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 26 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 26, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app
   `Equivₓ.sigmaCongrRight
   [(Term.fun
     "fun"
     (Term.basicFun [(Term.simpleBinder [`L] [])] "=>" (Term.app `left_coset_equiv_subgroup [(Term.hole "_")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [`L] [])] "=>" (Term.app `left_coset_equiv_subgroup [(Term.hole "_")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `left_coset_equiv_subgroup [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `left_coset_equiv_subgroup
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Equivₓ.sigmaCongrRight
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Equiv.Basic.«term_≃_»
   (Term.hole "_")
   " ≃ "
   (Init.Data.Sigma.Basic.«termΣ_,_»
    "Σ"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders [(Lean.binderIdent `L)] [":" (Algebra.Quotient.«term_⧸_» `α " ⧸ " `s)]))
    ", "
    `s))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Equiv.Basic.«term_≃_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Data.Sigma.Basic.«termΣ_,_»
   "Σ"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders [(Lean.binderIdent `L)] [":" (Algebra.Quotient.«term_⧸_» `α " ⧸ " `s)]))
   ", "
   `s)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
/-- A (non-canonical) bijection between a group `α` and the product `(α/s) × s` -/
    @[ to_additive "A (non-canonical) bijection between an add_group `α` and the product `(α/s) × s`" ]
    noncomputable
  def
    group_equiv_quotient_times_subgroup
    : α ≃ α ⧸ s × s
    :=
      calc
        α ≃ Σ L : α ⧸ s , { x : α // ( x : α ⧸ s ) = L } := Equivₓ.sigmaPreimageEquiv QuotientGroup.mk . symm
          _ ≃ Σ L : α ⧸ s , LeftCoset Quotientₓ.out' L s
            :=
            Equivₓ.sigmaCongrRight
              fun
                L
                  =>
                  by
                    rw [ ← eq_class_eq_left_coset ]
                      show
                        _root_.subtype fun x : α => Quotientₓ.mk' x = L
                          ≃
                          _root_.subtype fun x : α => Quotientₓ.mk' x = Quotientₓ.mk' _
                      simp [ - Quotientₓ.eq' ]
          _ ≃ Σ L : α ⧸ s , s := Equivₓ.sigmaCongrRight fun L => left_coset_equiv_subgroup _
          _ ≃ α ⧸ s × s := Equivₓ.sigmaEquivProd _ _

variable {t : Subgroup α}

/--  If `H ≤ K`, then `G/H ≃ G/K × K/H` constructively, using the provided right inverse
of the quotient map `G → G/K`. The classical version is `quotient_equiv_prod_of_le`. -/
@[to_additive
      "If `H ≤ K`, then `G/H ≃ G/K × K/H` constructively, using the provided right inverse\nof the quotient map `G → G/K`. The classical version is `quotient_equiv_prod_of_le`.",
  simps]
def quotient_equiv_prod_of_le' (h_le : s ≤ t) (f : α ⧸ t → α) (hf : Function.RightInverse f QuotientGroup.mk) :
    α ⧸ s ≃ (α ⧸ t) × t ⧸ s.subgroup_of t :=
  { toFun := fun a =>
      ⟨a.map' id fun b c h => h_le h,
        a.map' (fun g : α => ⟨f (Quotientₓ.mk' g)⁻¹*g, Quotientₓ.exact' (hf g)⟩) fun b c h => by
          change ((f b⁻¹*b)⁻¹*f c⁻¹*c) ∈ s
          have key : f b = f c := congr_argₓ f (Quotientₓ.sound' (h_le h))
          rwa [key, mul_inv_rev, inv_invₓ, mul_assocₓ, mul_inv_cancel_left]⟩,
    invFun := fun a =>
      a.2.map' (fun b => f a.1*b) fun b c h => by
        change ((f a.1*b)⁻¹*f a.1*c) ∈ s
        rwa [mul_inv_rev, mul_assocₓ, inv_mul_cancel_leftₓ],
    left_inv := by
      refine' Quotientₓ.ind' fun a => _
      simp_rw [Quotientₓ.map'_mk', id.def, t.coe_mk, mul_inv_cancel_left],
    right_inv := by
      refine' Prod.rec _
      refine' Quotientₓ.ind' fun a => _
      refine' Quotientₓ.ind' fun b => _
      have key : Quotientₓ.mk' (f (Quotientₓ.mk' a)*b) = Quotientₓ.mk' a :=
        (QuotientGroup.mk_mul_of_mem (f a) (↑b) b.2).trans (hf a)
      simp_rw [Quotientₓ.map'_mk', id.def, key, inv_mul_cancel_leftₓ, Subtype.coe_eta] }

/--  If `H ≤ K`, then `G/H ≃ G/K × K/H` nonconstructively.
The constructive version is `quotient_equiv_prod_of_le'`. -/
@[to_additive
      "If `H ≤ K`, then `G/H ≃ G/K × K/H` nonconstructively.\nThe constructive version is `quotient_equiv_prod_of_le'`.",
  simps]
noncomputable def quotient_equiv_prod_of_le (h_le : s ≤ t) : α ⧸ s ≃ (α ⧸ t) × t ⧸ s.subgroup_of t :=
  quotient_equiv_prod_of_le' h_le Quotientₓ.out' Quotientₓ.out_eq'

/--  If `K ≤ L`, then there is an embedding `K ⧸ (H.subgroup_of K) ↪ L ⧸ (H.subgroup_of L)`. -/
def quotient_subgroup_of_embedding_of_le (H : Subgroup α) {K L : Subgroup α} (h : K ≤ L) :
    K ⧸ H.subgroup_of K ↪ L ⧸ H.subgroup_of L :=
  { toFun := Quotientₓ.map' (Set.inclusion h) fun a b => id,
    inj' := by
      refine' Quotientₓ.ind₂' fun a b => _ <;> exact quotient.eq'.mpr ∘ quotient.eq'.mp }

@[to_additive]
theorem card_eq_card_quotient_mul_card_subgroup [Fintype α] (s : Subgroup α) [Fintype s]
    [DecidablePred fun a => a ∈ s] : Fintype.card α = Fintype.card (α ⧸ s)*Fintype.card s := by
  rw [← Fintype.card_prod] <;> exact Fintype.card_congr Subgroup.groupEquivQuotientTimesSubgroup

/--  **Order of a Subgroup** -/
@[to_additive]
theorem card_subgroup_dvd_card [Fintype α] (s : Subgroup α) [Fintype s] : Fintype.card s ∣ Fintype.card α := by
  classical <;> simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_left ℕ]

@[to_additive]
theorem card_quotient_dvd_card [Fintype α] (s : Subgroup α) [DecidablePred fun a => a ∈ s] [Fintype s] :
    Fintype.card (α ⧸ s) ∣ Fintype.card α := by
  simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_right ℕ]

open Fintype

variable {H : Type _} [Groupₓ H]

@[to_additive]
theorem card_dvd_of_injective [Fintype α] [Fintype H] (f : α →* H) (hf : Function.Injective f) : card α ∣ card H := by
  classical <;>
    calc card α = card (f.range : Subgroup H) := card_congr (Equivₓ.ofInjective f hf)_ ∣ card H :=
      card_subgroup_dvd_card _

@[to_additive]
theorem card_dvd_of_le {H K : Subgroup α} [Fintype H] [Fintype K] (hHK : H ≤ K) : card H ∣ card K :=
  card_dvd_of_injective (inclusion hHK) (inclusion_injective hHK)

@[to_additive]
theorem card_comap_dvd_of_injective (K : Subgroup H) [Fintype K] (f : α →* H) [Fintype (K.comap f)]
    (hf : Function.Injective f) : Fintype.card (K.comap f) ∣ Fintype.card K := by
  have : Fintype ((K.comap f).map f) := Fintype.ofEquiv _ (equiv_map_of_injective _ _ hf).toEquiv <;>
    calc Fintype.card (K.comap f) = Fintype.card ((K.comap f).map f) :=
      Fintype.card_congr (equiv_map_of_injective _ _ hf).toEquiv _ ∣ Fintype.card K := card_dvd_of_le (map_comap_le _ _)

end Subgroup

namespace QuotientGroup

variable [Groupₓ α]

/--  If `s` is a subgroup of the group `α`, and `t` is a subset of `α/s`, then
there is a (typically non-canonical) bijection between the preimage of `t` in
`α` and the product `s × t`. -/
noncomputable def preimage_mk_equiv_subgroup_times_set (s : Subgroup α) (t : Set (α ⧸ s)) :
    QuotientGroup.mk ⁻¹' t ≃ s × t :=
  have h :
    ∀ {x : α ⧸ s} {a : α},
      x ∈ t → a ∈ s → (Quotientₓ.mk' (Quotientₓ.out' x*a) : α ⧸ s) = Quotientₓ.mk' (Quotientₓ.out' x) :=
    fun x a hx ha =>
    Quotientₓ.sound'
      (show ((Quotientₓ.out' x*a)⁻¹*Quotientₓ.out' x) ∈ s from
        s.inv_mem_iff.1 $ by
          rwa [mul_inv_rev, inv_invₓ, ← mul_assocₓ, inv_mul_selfₓ, one_mulₓ])
  { toFun := fun ⟨a, ha⟩ =>
      ⟨⟨Quotientₓ.out' (Quotientₓ.mk' a)⁻¹*a, @Quotientₓ.exact' _ (left_rel s) _ _ $ Quotientₓ.out_eq' _⟩,
        ⟨Quotientₓ.mk' a, ha⟩⟩,
    invFun := fun ⟨⟨a, ha⟩, ⟨x, hx⟩⟩ =>
      ⟨Quotientₓ.out' x*a,
        show Quotientₓ.mk' _ ∈ t by
          simp [h hx ha, hx]⟩,
    left_inv := fun ⟨a, ha⟩ =>
      Subtype.eq $
        show (_*_) = a by
          simp ,
    right_inv := fun ⟨⟨a, ha⟩, ⟨x, hx⟩⟩ =>
      show (_, _) = _ by
        simp [h hx ha] }

end QuotientGroup

/-- 
We use the class `has_coe_t` instead of `has_coe` if the first argument is a variable,
or if the second argument is a variable not occurring in the first.
Using `has_coe` would cause looping of type-class inference. See
<https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/remove.20all.20instances.20with.20variable.20domain>
-/
library_note "use has_coe_t"

