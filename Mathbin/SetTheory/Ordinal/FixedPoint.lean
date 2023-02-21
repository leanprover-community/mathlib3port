/-
Copyright (c) 2018 Violeta Hernández Palacios, Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Mario Carneiro

! This file was ported from Lean 3 source module set_theory.ordinal.fixed_point
! leanprover-community/mathlib commit f1e061e3caef3022f0daa99d670ecf2c30e0b5c6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.SetTheory.Ordinal.Arithmetic
import Mathbin.SetTheory.Ordinal.Exponential

/-!
# Fixed points of normal functions

We prove various statements about the fixed points of normal ordinal functions. We state them in
three forms: as statements about type-indexed families of normal functions, as statements about
ordinal-indexed families of normal functions, and as statements about a single normal function. For
the most part, the first case encompasses the others.

Moreover, we prove some lemmas about the fixed points of specific normal functions.

## Main definitions and results

* `nfp_family`, `nfp_bfamily`, `nfp`: the next fixed point of a (family of) normal function(s).
* `fp_family_unbounded`, `fp_bfamily_unbounded`, `fp_unbounded`: the (common) fixed points of a
  (family of) normal function(s) are unbounded in the ordinals.
* `deriv_add_eq_mul_omega_add`: a characterization of the derivative of addition.
* `deriv_mul_eq_opow_omega_mul`: a characterization of the derivative of multiplication.
-/


noncomputable section

universe u v

open Function Order

namespace Ordinal

/-! ### Fixed points of type-indexed families of ordinals -/


section

variable {ι : Type u} {f : ι → Ordinal.{max u v} → Ordinal.{max u v}}

#print Ordinal.nfpFamily /-
/-- The next common fixed point, at least `a`, for a family of normal functions.

`ordinal.nfp_family_fp` shows this is a fixed point, `ordinal.le_nfp_family` shows it's at
least `a`, and `ordinal.nfp_family_le_fp` shows this is the least ordinal with these properties. -/
def nfpFamily (f : ι → Ordinal → Ordinal) (a) : Ordinal :=
  sup (List.foldr f a)
#align ordinal.nfp_family Ordinal.nfpFamily
-/

#print Ordinal.nfpFamily_eq_sup /-
theorem nfpFamily_eq_sup (f : ι → Ordinal → Ordinal) (a) : nfpFamily f a = sup (List.foldr f a) :=
  rfl
#align ordinal.nfp_family_eq_sup Ordinal.nfpFamily_eq_sup
-/

#print Ordinal.foldr_le_nfpFamily /-
theorem foldr_le_nfpFamily (f : ι → Ordinal → Ordinal) (a l) : List.foldr f a l ≤ nfpFamily f a :=
  le_sup _ _
#align ordinal.foldr_le_nfp_family Ordinal.foldr_le_nfpFamily
-/

/- warning: ordinal.le_nfp_family -> Ordinal.le_nfpFamily is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (f : ι -> Ordinal.{max u1 u2} -> Ordinal.{max u1 u2}) (a : Ordinal.{max u1 u2}), LE.le.{succ (max u1 u2)} Ordinal.{max u1 u2} (Preorder.toLE.{succ (max u1 u2)} Ordinal.{max u1 u2} (PartialOrder.toPreorder.{succ (max u1 u2)} Ordinal.{max u1 u2} Ordinal.partialOrder.{max u1 u2})) a (Ordinal.nfpFamily.{u1, u2} ι f a)
but is expected to have type
  forall {ι : Type.{u2}} (f : ι -> Ordinal.{max u2 u1} -> Ordinal.{max u2 u1}) (a : Ordinal.{max u2 u1}), LE.le.{max (succ u2) (succ u1)} Ordinal.{max u2 u1} (Preorder.toLE.{max (succ u2) (succ u1)} Ordinal.{max u2 u1} (PartialOrder.toPreorder.{max (succ u2) (succ u1)} Ordinal.{max u2 u1} Ordinal.partialOrder.{max u2 u1})) a (Ordinal.nfpFamily.{u2, u1} ι f a)
Case conversion may be inaccurate. Consider using '#align ordinal.le_nfp_family Ordinal.le_nfpFamilyₓ'. -/
theorem le_nfpFamily (f : ι → Ordinal → Ordinal) (a) : a ≤ nfpFamily f a :=
  le_sup _ []
#align ordinal.le_nfp_family Ordinal.le_nfpFamily

#print Ordinal.lt_nfpFamily /-
theorem lt_nfpFamily {a b} : a < nfpFamily f b ↔ ∃ l, a < List.foldr f b l :=
  lt_sup
#align ordinal.lt_nfp_family Ordinal.lt_nfpFamily
-/

#print Ordinal.nfpFamily_le_iff /-
theorem nfpFamily_le_iff {a b} : nfpFamily f a ≤ b ↔ ∀ l, List.foldr f a l ≤ b :=
  sup_le_iff
#align ordinal.nfp_family_le_iff Ordinal.nfpFamily_le_iff
-/

#print Ordinal.nfpFamily_le /-
theorem nfpFamily_le {a b} : (∀ l, List.foldr f a l ≤ b) → nfpFamily f a ≤ b :=
  sup_le
#align ordinal.nfp_family_le Ordinal.nfpFamily_le
-/

#print Ordinal.nfpFamily_monotone /-
theorem nfpFamily_monotone (hf : ∀ i, Monotone (f i)) : Monotone (nfpFamily f) := fun a b h =>
  sup_le fun l => (List.foldr_monotone hf l h).trans (le_sup _ l)
#align ordinal.nfp_family_monotone Ordinal.nfpFamily_monotone
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Ordinal.apply_lt_nfpFamily /-
theorem apply_lt_nfpFamily (H : ∀ i, IsNormal (f i)) {a b} (hb : b < nfpFamily f a) (i) :
    f i b < nfpFamily f a :=
  let ⟨l, hl⟩ := lt_nfpFamily.1 hb
  lt_sup.2 ⟨i::l, (H i).StrictMono hl⟩
#align ordinal.apply_lt_nfp_family Ordinal.apply_lt_nfpFamily
-/

#print Ordinal.apply_lt_nfpFamily_iff /-
theorem apply_lt_nfpFamily_iff [Nonempty ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∀ i, f i b < nfpFamily f a) ↔ b < nfpFamily f a :=
  ⟨fun h =>
    lt_nfpFamily.2 <|
      let ⟨l, hl⟩ := lt_sup.1 (h (Classical.arbitrary ι))
      ⟨l, ((H _).self_le b).trans_lt hl⟩,
    apply_lt_nfpFamily H⟩
#align ordinal.apply_lt_nfp_family_iff Ordinal.apply_lt_nfpFamily_iff
-/

#print Ordinal.nfpFamily_le_apply /-
theorem nfpFamily_le_apply [Nonempty ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∃ i, nfpFamily f a ≤ f i b) ↔ nfpFamily f a ≤ b :=
  by
  rw [← not_iff_not]
  push_neg
  exact apply_lt_nfp_family_iff H
#align ordinal.nfp_family_le_apply Ordinal.nfpFamily_le_apply
-/

#print Ordinal.nfpFamily_le_fp /-
theorem nfpFamily_le_fp (H : ∀ i, Monotone (f i)) {a b} (ab : a ≤ b) (h : ∀ i, f i b ≤ b) :
    nfpFamily f a ≤ b :=
  sup_le fun l => by
    by_cases hι : IsEmpty ι
    · skip
      rwa [Unique.eq_default l]
    · haveI := not_isEmpty_iff.1 hι
      induction' l with i l IH generalizing a
      · exact ab
      exact (H i (IH ab)).trans (h i)
#align ordinal.nfp_family_le_fp Ordinal.nfpFamily_le_fp
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Ordinal.nfpFamily_fp /-
theorem nfpFamily_fp {i} (H : IsNormal (f i)) (a) : f i (nfpFamily f a) = nfpFamily f a :=
  by
  unfold nfp_family
  rw [@is_normal.sup _ H _ _ ⟨[]⟩]
  apply le_antisymm <;> refine' Ordinal.sup_le fun l => _
  · exact le_sup _ (i::l)
  · exact (H.self_le _).trans (le_sup _ _)
#align ordinal.nfp_family_fp Ordinal.nfpFamily_fp
-/

#print Ordinal.apply_le_nfpFamily /-
theorem apply_le_nfpFamily [hι : Nonempty ι] {f : ι → Ordinal → Ordinal} (H : ∀ i, IsNormal (f i))
    {a b} : (∀ i, f i b ≤ nfpFamily f a) ↔ b ≤ nfpFamily f a :=
  by
  refine' ⟨fun h => _, fun h i => _⟩
  · cases' hι with i
    exact ((H i).self_le b).trans (h i)
  rw [← nfp_family_fp (H i)]
  exact (H i).Monotone h
#align ordinal.apply_le_nfp_family Ordinal.apply_le_nfpFamily
-/

/- warning: ordinal.nfp_family_eq_self -> Ordinal.nfpFamily_eq_self is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {f : ι -> Ordinal.{max u1 u2} -> Ordinal.{max u1 u2}} {a : Ordinal.{max u1 u2}}, (forall (i : ι), Eq.{succ (succ (max u1 u2))} Ordinal.{max u1 u2} (f i a) a) -> (Eq.{succ (succ (max u1 u2))} Ordinal.{max u1 u2} (Ordinal.nfpFamily.{u1, u2} ι f a) a)
but is expected to have type
  forall {ι : Type.{u2}} {f : ι -> Ordinal.{max u2 u1} -> Ordinal.{max u2 u1}} {a : Ordinal.{max u2 u1}}, (forall (i : ι), Eq.{succ (succ (max u2 u1))} Ordinal.{max u2 u1} (f i a) a) -> (Eq.{max (succ (succ u2)) (succ (succ u1))} Ordinal.{max u1 u2} (Ordinal.nfpFamily.{u2, u1} ι f a) a)
Case conversion may be inaccurate. Consider using '#align ordinal.nfp_family_eq_self Ordinal.nfpFamily_eq_selfₓ'. -/
theorem nfpFamily_eq_self {f : ι → Ordinal → Ordinal} {a} (h : ∀ i, f i a = a) :
    nfpFamily f a = a :=
  le_antisymm (sup_le fun l => by rw [List.foldr_fixed' h l]) (le_nfpFamily f a)
#align ordinal.nfp_family_eq_self Ordinal.nfpFamily_eq_self

#print Ordinal.fp_family_unbounded /-
/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
theorem fp_family_unbounded (H : ∀ i, IsNormal (f i)) :
    (⋂ i, Function.fixedPoints (f i)).Unbounded (· < ·) := fun a =>
  ⟨_, fun s ⟨i, hi⟩ => by
    rw [← hi]
    exact nfp_family_fp (H i) a, (le_nfpFamily f a).not_lt⟩
#align ordinal.fp_family_unbounded Ordinal.fp_family_unbounded
-/

#print Ordinal.derivFamily /-
/-- The derivative of a family of normal functions is the sequence of their common fixed points. -/
def derivFamily (f : ι → Ordinal → Ordinal) (o : Ordinal) : Ordinal :=
  limitRecOn o (nfpFamily f 0) (fun a IH => nfpFamily f (succ IH)) fun a l => bsup.{max u v, u} a
#align ordinal.deriv_family Ordinal.derivFamily
-/

#print Ordinal.derivFamily_zero /-
@[simp]
theorem derivFamily_zero (f : ι → Ordinal → Ordinal) : derivFamily f 0 = nfpFamily f 0 :=
  limitRecOn_zero _ _ _
#align ordinal.deriv_family_zero Ordinal.derivFamily_zero
-/

#print Ordinal.derivFamily_succ /-
@[simp]
theorem derivFamily_succ (f : ι → Ordinal → Ordinal) (o) :
    derivFamily f (succ o) = nfpFamily f (succ (derivFamily f o)) :=
  limitRecOn_succ _ _ _ _
#align ordinal.deriv_family_succ Ordinal.derivFamily_succ
-/

#print Ordinal.derivFamily_limit /-
theorem derivFamily_limit (f : ι → Ordinal → Ordinal) {o} :
    IsLimit o → derivFamily f o = bsup.{max u v, u} o fun a _ => derivFamily f a :=
  limitRecOn_limit _ _ _ _
#align ordinal.deriv_family_limit Ordinal.derivFamily_limit
-/

/- warning: ordinal.deriv_family_is_normal -> Ordinal.derivFamily_isNormal is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (f : ι -> Ordinal.{max u1 u2} -> Ordinal.{max u1 u2}), Ordinal.IsNormal.{max u1 u2, max u1 u2} (Ordinal.derivFamily.{u1, u2} ι f)
but is expected to have type
  forall {ι : Type.{u2}} (f : ι -> Ordinal.{max u2 u1} -> Ordinal.{max u2 u1}), Ordinal.IsNormal.{max u1 u2, max u1 u2} (Ordinal.derivFamily.{u2, u1} ι f)
Case conversion may be inaccurate. Consider using '#align ordinal.deriv_family_is_normal Ordinal.derivFamily_isNormalₓ'. -/
theorem derivFamily_isNormal (f : ι → Ordinal → Ordinal) : IsNormal (derivFamily f) :=
  ⟨fun o => by rw [deriv_family_succ, ← succ_le_iff] <;> apply le_nfp_family, fun o l a => by
    rw [deriv_family_limit _ l, bsup_le_iff]⟩
#align ordinal.deriv_family_is_normal Ordinal.derivFamily_isNormal

#print Ordinal.derivFamily_fp /-
theorem derivFamily_fp {i} (H : IsNormal (f i)) (o : Ordinal.{max u v}) :
    f i (derivFamily f o) = derivFamily f o :=
  by
  refine' limit_rec_on o _ (fun o IH => _) _
  · rw [deriv_family_zero]
    exact nfp_family_fp H 0
  · rw [deriv_family_succ]
    exact nfp_family_fp H _
  · intro o l IH
    rw [deriv_family_limit _ l,
      IsNormal.bsup.{max u v, u, max u v} H (fun a _ => deriv_family f a) l.1]
    refine' eq_of_forall_ge_iff fun c => _
    simp (config := { contextual := true }) only [bsup_le_iff, IH]
#align ordinal.deriv_family_fp Ordinal.derivFamily_fp
-/

#print Ordinal.le_iff_derivFamily /-
theorem le_iff_derivFamily (H : ∀ i, IsNormal (f i)) {a} :
    (∀ i, f i a ≤ a) ↔ ∃ o, derivFamily f o = a :=
  ⟨fun ha => by
    suffices : ∀ (o) (_ : a ≤ deriv_family f o), ∃ o, deriv_family f o = a
    exact this a ((deriv_family_is_normal _).self_le _)
    refine' fun o =>
      limit_rec_on o (fun h₁ => ⟨0, le_antisymm _ h₁⟩) (fun o IH h₁ => _) fun o l IH h₁ => _
    · rw [deriv_family_zero]
      exact nfp_family_le_fp (fun i => (H i).Monotone) (Ordinal.zero_le _) ha
    · cases le_or_lt a (deriv_family f o)
      · exact IH h
      refine' ⟨succ o, le_antisymm _ h₁⟩
      rw [deriv_family_succ]
      exact nfp_family_le_fp (fun i => (H i).Monotone) (succ_le_of_lt h) ha
    · cases eq_or_lt_of_le h₁
      · exact ⟨_, h.symm⟩
      rw [deriv_family_limit _ l, ← not_le, bsup_le_iff, not_ball] at h
      exact
        let ⟨o', h, hl⟩ := h
        IH o' h (le_of_not_le hl),
    fun ⟨o, e⟩ i => e ▸ le_of_eq (derivFamily_fp (H i) _)⟩
#align ordinal.le_iff_deriv_family Ordinal.le_iff_derivFamily
-/

#print Ordinal.fp_iff_derivFamily /-
theorem fp_iff_derivFamily (H : ∀ i, IsNormal (f i)) {a} :
    (∀ i, f i a = a) ↔ ∃ o, derivFamily f o = a :=
  Iff.trans ⟨fun h i => le_of_eq (h i), fun h i => (H i).le_iff_eq.1 (h i)⟩ (le_iff_derivFamily H)
#align ordinal.fp_iff_deriv_family Ordinal.fp_iff_derivFamily
-/

#print Ordinal.derivFamily_eq_enumOrd /-
theorem derivFamily_eq_enumOrd (H : ∀ i, IsNormal (f i)) :
    derivFamily f = enumOrd (⋂ i, Function.fixedPoints (f i)) :=
  by
  rw [← eq_enum_ord _ (fp_family_unbounded H)]
  use (deriv_family_is_normal f).StrictMono
  rw [Set.range_eq_iff]
  refine' ⟨_, fun a ha => _⟩
  · rintro a S ⟨i, hi⟩
    rw [← hi]
    exact deriv_family_fp (H i) a
  rw [Set.mem_interᵢ] at ha
  rwa [← fp_iff_deriv_family H]
#align ordinal.deriv_family_eq_enum_ord Ordinal.derivFamily_eq_enumOrd
-/

end

/-! ### Fixed points of ordinal-indexed families of ordinals -/


section

variable {o : Ordinal.{u}} {f : ∀ b < o, Ordinal.{max u v} → Ordinal.{max u v}}

#print Ordinal.nfpBFamily /-
/-- The next common fixed point, at least `a`, for a family of normal functions indexed by ordinals.
-/
def nfpBFamily (o : Ordinal) (f : ∀ b < o, Ordinal → Ordinal) : Ordinal → Ordinal :=
  nfpFamily (familyOfBFamily o f)
#align ordinal.nfp_bfamily Ordinal.nfpBFamily
-/

#print Ordinal.nfpBFamily_eq_nfpFamily /-
theorem nfpBFamily_eq_nfpFamily {o : Ordinal} (f : ∀ b < o, Ordinal → Ordinal) :
    nfpBFamily o f = nfpFamily (familyOfBFamily o f) :=
  rfl
#align ordinal.nfp_bfamily_eq_nfp_family Ordinal.nfpBFamily_eq_nfpFamily
-/

#print Ordinal.foldr_le_nfpBFamily /-
theorem foldr_le_nfpBFamily {o : Ordinal} (f : ∀ b < o, Ordinal → Ordinal) (a l) :
    List.foldr (familyOfBFamily o f) a l ≤ nfpBFamily o f a :=
  le_sup _ _
#align ordinal.foldr_le_nfp_bfamily Ordinal.foldr_le_nfpBFamily
-/

#print Ordinal.le_nfpBFamily /-
theorem le_nfpBFamily {o : Ordinal} (f : ∀ b < o, Ordinal → Ordinal) (a) : a ≤ nfpBFamily o f a :=
  le_sup _ []
#align ordinal.le_nfp_bfamily Ordinal.le_nfpBFamily
-/

#print Ordinal.lt_nfpBFamily /-
theorem lt_nfpBFamily {a b} :
    a < nfpBFamily o f b ↔ ∃ l, a < List.foldr (familyOfBFamily o f) b l :=
  lt_sup
#align ordinal.lt_nfp_bfamily Ordinal.lt_nfpBFamily
-/

#print Ordinal.nfpBFamily_le_iff /-
theorem nfpBFamily_le_iff {o : Ordinal} {f : ∀ b < o, Ordinal → Ordinal} {a b} :
    nfpBFamily o f a ≤ b ↔ ∀ l, List.foldr (familyOfBFamily o f) a l ≤ b :=
  sup_le_iff
#align ordinal.nfp_bfamily_le_iff Ordinal.nfpBFamily_le_iff
-/

#print Ordinal.nfpBFamily_le /-
theorem nfpBFamily_le {o : Ordinal} {f : ∀ b < o, Ordinal → Ordinal} {a b} :
    (∀ l, List.foldr (familyOfBFamily o f) a l ≤ b) → nfpBFamily o f a ≤ b :=
  sup_le
#align ordinal.nfp_bfamily_le Ordinal.nfpBFamily_le
-/

#print Ordinal.nfpBFamily_monotone /-
theorem nfpBFamily_monotone (hf : ∀ i hi, Monotone (f i hi)) : Monotone (nfpBFamily o f) :=
  nfpFamily_monotone fun i => hf _ _
#align ordinal.nfp_bfamily_monotone Ordinal.nfpBFamily_monotone
-/

#print Ordinal.apply_lt_nfpBFamily /-
theorem apply_lt_nfpBFamily (ho : o ≠ 0) (H : ∀ i hi, IsNormal (f i hi)) {a b} :
    (∀ i hi, f i hi b < nfpBFamily o f a) ↔ b < nfpBFamily o f a :=
  by
  unfold nfp_bfamily
  rw [←
    @apply_lt_nfp_family_iff _ (family_of_bfamily o f) (out_nonempty_iff_ne_zero.2 ho) fun i =>
      H _ _]
  refine' ⟨fun h i => h _ (typein_lt_self i), fun h i hio => _⟩
  rw [← family_of_bfamily_enum o f]
  apply h
#align ordinal.apply_lt_nfp_bfamily Ordinal.apply_lt_nfpBFamily
-/

#print Ordinal.nfpBFamily_le_apply /-
theorem nfpBFamily_le_apply (ho : o ≠ 0) (H : ∀ i hi, IsNormal (f i hi)) {a b} :
    (∃ i hi, nfpBFamily o f a ≤ f i hi b) ↔ nfpBFamily o f a ≤ b :=
  by
  rw [← not_iff_not]
  push_neg
  convert apply_lt_nfp_bfamily ho H
  simp only [not_le]
#align ordinal.nfp_bfamily_le_apply Ordinal.nfpBFamily_le_apply
-/

#print Ordinal.nfpBFamily_le_fp /-
theorem nfpBFamily_le_fp (H : ∀ i hi, Monotone (f i hi)) {a b} (ab : a ≤ b)
    (h : ∀ i hi, f i hi b ≤ b) : nfpBFamily o f a ≤ b :=
  nfpFamily_le_fp (fun _ => H _ _) ab fun i => h _ _
#align ordinal.nfp_bfamily_le_fp Ordinal.nfpBFamily_le_fp
-/

#print Ordinal.nfpBFamily_fp /-
theorem nfpBFamily_fp {i hi} (H : IsNormal (f i hi)) (a) :
    f i hi (nfpBFamily o f a) = nfpBFamily o f a :=
  by
  rw [← family_of_bfamily_enum o f]
  apply nfp_family_fp
  rw [family_of_bfamily_enum]
  exact H
#align ordinal.nfp_bfamily_fp Ordinal.nfpBFamily_fp
-/

#print Ordinal.apply_le_nfpBFamily /-
theorem apply_le_nfpBFamily (ho : o ≠ 0) (H : ∀ i hi, IsNormal (f i hi)) {a b} :
    (∀ i hi, f i hi b ≤ nfpBFamily o f a) ↔ b ≤ nfpBFamily o f a :=
  by
  refine' ⟨fun h => _, fun h i hi => _⟩
  · have ho' : 0 < o := Ordinal.pos_iff_ne_zero.2 ho
    exact ((H 0 ho').self_le b).trans (h 0 ho')
  rw [← nfp_bfamily_fp (H i hi)]
  exact (H i hi).Monotone h
#align ordinal.apply_le_nfp_bfamily Ordinal.apply_le_nfpBFamily
-/

#print Ordinal.nfpBFamily_eq_self /-
theorem nfpBFamily_eq_self {a} (h : ∀ i hi, f i hi a = a) : nfpBFamily o f a = a :=
  nfpFamily_eq_self fun _ => h _ _
#align ordinal.nfp_bfamily_eq_self Ordinal.nfpBFamily_eq_self
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
#print Ordinal.fp_bfamily_unbounded /-
/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
theorem fp_bfamily_unbounded (H : ∀ i hi, IsNormal (f i hi)) :
    (⋂ (i) (hi), Function.fixedPoints (f i hi)).Unbounded (· < ·) := fun a =>
  ⟨_, by
    rw [Set.mem_interᵢ₂]
    exact fun i hi => nfp_bfamily_fp (H i hi) _, (le_nfpBFamily f a).not_lt⟩
#align ordinal.fp_bfamily_unbounded Ordinal.fp_bfamily_unbounded
-/

#print Ordinal.derivBFamily /-
/-- The derivative of a family of normal functions is the sequence of their common fixed points. -/
def derivBFamily (o : Ordinal) (f : ∀ b < o, Ordinal → Ordinal) : Ordinal → Ordinal :=
  derivFamily (familyOfBFamily o f)
#align ordinal.deriv_bfamily Ordinal.derivBFamily
-/

#print Ordinal.derivBFamily_eq_derivFamily /-
theorem derivBFamily_eq_derivFamily {o : Ordinal} (f : ∀ b < o, Ordinal → Ordinal) :
    derivBFamily o f = derivFamily (familyOfBFamily o f) :=
  rfl
#align ordinal.deriv_bfamily_eq_deriv_family Ordinal.derivBFamily_eq_derivFamily
-/

/- warning: ordinal.deriv_bfamily_is_normal -> Ordinal.derivBFamily_isNormal is a dubious translation:
lean 3 declaration is
  forall {o : Ordinal.{u1}} (f : forall (b : Ordinal.{u1}), (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) b o) -> Ordinal.{max u1 u2} -> Ordinal.{max u1 u2}), Ordinal.IsNormal.{max u1 u2, max u1 u2} (Ordinal.derivBFamily.{u1, u2} o f)
but is expected to have type
  forall {o : Ordinal.{u2}} (f : forall (b : Ordinal.{u2}), (LT.lt.{succ u2} Ordinal.{u2} (Preorder.toLT.{succ u2} Ordinal.{u2} (PartialOrder.toPreorder.{succ u2} Ordinal.{u2} Ordinal.partialOrder.{u2})) b o) -> Ordinal.{max u2 u1} -> Ordinal.{max u2 u1}), Ordinal.IsNormal.{max u1 u2, max u1 u2} (Ordinal.derivBFamily.{u2, u1} o f)
Case conversion may be inaccurate. Consider using '#align ordinal.deriv_bfamily_is_normal Ordinal.derivBFamily_isNormalₓ'. -/
theorem derivBFamily_isNormal {o : Ordinal} (f : ∀ b < o, Ordinal → Ordinal) :
    IsNormal (derivBFamily o f) :=
  derivFamily_isNormal _
#align ordinal.deriv_bfamily_is_normal Ordinal.derivBFamily_isNormal

#print Ordinal.derivBFamily_fp /-
theorem derivBFamily_fp {i hi} (H : IsNormal (f i hi)) (a : Ordinal) :
    f i hi (derivBFamily o f a) = derivBFamily o f a :=
  by
  rw [← family_of_bfamily_enum o f]
  apply deriv_family_fp
  rw [family_of_bfamily_enum]
  exact H
#align ordinal.deriv_bfamily_fp Ordinal.derivBFamily_fp
-/

#print Ordinal.le_iff_derivBFamily /-
theorem le_iff_derivBFamily (H : ∀ i hi, IsNormal (f i hi)) {a} :
    (∀ i hi, f i hi a ≤ a) ↔ ∃ b, derivBFamily o f b = a :=
  by
  unfold deriv_bfamily
  rw [← le_iff_deriv_family]
  · refine' ⟨fun h i => h _ _, fun h i hi => _⟩
    rw [← family_of_bfamily_enum o f]
    apply h
  exact fun _ => H _ _
#align ordinal.le_iff_deriv_bfamily Ordinal.le_iff_derivBFamily
-/

#print Ordinal.fp_iff_derivBFamily /-
theorem fp_iff_derivBFamily (H : ∀ i hi, IsNormal (f i hi)) {a} :
    (∀ i hi, f i hi a = a) ↔ ∃ b, derivBFamily o f b = a :=
  by
  rw [← le_iff_deriv_bfamily H]
  refine' ⟨fun h i hi => le_of_eq (h i hi), fun h i hi => _⟩
  rw [← (H i hi).le_iff_eq]
  exact h i hi
#align ordinal.fp_iff_deriv_bfamily Ordinal.fp_iff_derivBFamily
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
#print Ordinal.derivBFamily_eq_enumOrd /-
theorem derivBFamily_eq_enumOrd (H : ∀ i hi, IsNormal (f i hi)) :
    derivBFamily o f = enumOrd (⋂ (i) (hi), Function.fixedPoints (f i hi)) :=
  by
  rw [← eq_enum_ord _ (fp_bfamily_unbounded H)]
  use (deriv_bfamily_is_normal f).StrictMono
  rw [Set.range_eq_iff]
  refine' ⟨fun a => Set.mem_interᵢ₂.2 fun i hi => deriv_bfamily_fp (H i hi) a, fun a ha => _⟩
  rw [Set.mem_interᵢ₂] at ha
  rwa [← fp_iff_deriv_bfamily H]
#align ordinal.deriv_bfamily_eq_enum_ord Ordinal.derivBFamily_eq_enumOrd
-/

end

/-! ### Fixed points of a single function -/


section

variable {f : Ordinal.{u} → Ordinal.{u}}

#print Ordinal.nfp /-
/-- The next fixed point function, the least fixed point of the normal function `f`, at least `a`.
-/
def nfp (f : Ordinal → Ordinal) : Ordinal → Ordinal :=
  nfpFamily fun _ : Unit => f
#align ordinal.nfp Ordinal.nfp
-/

#print Ordinal.nfp_eq_nfpFamily /-
theorem nfp_eq_nfpFamily (f : Ordinal → Ordinal) : nfp f = nfpFamily fun _ : Unit => f :=
  rfl
#align ordinal.nfp_eq_nfp_family Ordinal.nfp_eq_nfpFamily
-/

#print Ordinal.sup_iterate_eq_nfp /-
@[simp]
theorem sup_iterate_eq_nfp (f : Ordinal.{u} → Ordinal.{u}) :
    (fun a => sup fun n : ℕ => (f^[n]) a) = nfp f :=
  by
  refine' funext fun a => le_antisymm _ (sup_le fun l => _)
  · rw [sup_le_iff]
    intro n
    rw [← List.length_replicate n Unit.unit, ← List.foldr_const f a]
    apply le_sup
  · rw [List.foldr_const f a l]
    exact le_sup _ _
#align ordinal.sup_iterate_eq_nfp Ordinal.sup_iterate_eq_nfp
-/

#print Ordinal.iterate_le_nfp /-
theorem iterate_le_nfp (f a n) : (f^[n]) a ≤ nfp f a :=
  by
  rw [← sup_iterate_eq_nfp]
  exact le_sup _ n
#align ordinal.iterate_le_nfp Ordinal.iterate_le_nfp
-/

#print Ordinal.le_nfp /-
theorem le_nfp (f a) : a ≤ nfp f a :=
  iterate_le_nfp f a 0
#align ordinal.le_nfp Ordinal.le_nfp
-/

#print Ordinal.lt_nfp /-
theorem lt_nfp {a b} : a < nfp f b ↔ ∃ n, a < (f^[n]) b :=
  by
  rw [← sup_iterate_eq_nfp]
  exact lt_sup
#align ordinal.lt_nfp Ordinal.lt_nfp
-/

#print Ordinal.nfp_le_iff /-
theorem nfp_le_iff {a b} : nfp f a ≤ b ↔ ∀ n, (f^[n]) a ≤ b :=
  by
  rw [← sup_iterate_eq_nfp]
  exact sup_le_iff
#align ordinal.nfp_le_iff Ordinal.nfp_le_iff
-/

#print Ordinal.nfp_le /-
theorem nfp_le {a b} : (∀ n, (f^[n]) a ≤ b) → nfp f a ≤ b :=
  nfp_le_iff.2
#align ordinal.nfp_le Ordinal.nfp_le
-/

#print Ordinal.nfp_id /-
@[simp]
theorem nfp_id : nfp id = id :=
  funext fun a => by
    simp_rw [← sup_iterate_eq_nfp, iterate_id]
    exact sup_const a
#align ordinal.nfp_id Ordinal.nfp_id
-/

#print Ordinal.nfp_monotone /-
theorem nfp_monotone (hf : Monotone f) : Monotone (nfp f) :=
  nfpFamily_monotone fun i => hf
#align ordinal.nfp_monotone Ordinal.nfp_monotone
-/

#print Ordinal.IsNormal.apply_lt_nfp /-
theorem IsNormal.apply_lt_nfp {f} (H : IsNormal f) {a b} : f b < nfp f a ↔ b < nfp f a :=
  by
  unfold nfp
  rw [← @apply_lt_nfp_family_iff Unit (fun _ => f) _ (fun _ => H) a b]
  exact ⟨fun h _ => h, fun h => h Unit.unit⟩
#align ordinal.is_normal.apply_lt_nfp Ordinal.IsNormal.apply_lt_nfp
-/

#print Ordinal.IsNormal.nfp_le_apply /-
theorem IsNormal.nfp_le_apply {f} (H : IsNormal f) {a b} : nfp f a ≤ f b ↔ nfp f a ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 H.apply_lt_nfp
#align ordinal.is_normal.nfp_le_apply Ordinal.IsNormal.nfp_le_apply
-/

#print Ordinal.nfp_le_fp /-
theorem nfp_le_fp {f} (H : Monotone f) {a b} (ab : a ≤ b) (h : f b ≤ b) : nfp f a ≤ b :=
  nfpFamily_le_fp (fun _ => H) ab fun _ => h
#align ordinal.nfp_le_fp Ordinal.nfp_le_fp
-/

#print Ordinal.IsNormal.nfp_fp /-
theorem IsNormal.nfp_fp {f} (H : IsNormal f) : ∀ a, f (nfp f a) = nfp f a :=
  @nfpFamily_fp Unit (fun _ => f) Unit.unit H
#align ordinal.is_normal.nfp_fp Ordinal.IsNormal.nfp_fp
-/

#print Ordinal.IsNormal.apply_le_nfp /-
theorem IsNormal.apply_le_nfp {f} (H : IsNormal f) {a b} : f b ≤ nfp f a ↔ b ≤ nfp f a :=
  ⟨le_trans (H.self_le _), fun h => by simpa only [H.nfp_fp] using H.le_iff.2 h⟩
#align ordinal.is_normal.apply_le_nfp Ordinal.IsNormal.apply_le_nfp
-/

#print Ordinal.nfp_eq_self /-
theorem nfp_eq_self {f : Ordinal → Ordinal} {a} (h : f a = a) : nfp f a = a :=
  nfpFamily_eq_self fun _ => h
#align ordinal.nfp_eq_self Ordinal.nfp_eq_self
-/

#print Ordinal.fp_unbounded /-
/-- The fixed point lemma for normal functions: any normal function has an unbounded set of
fixed points. -/
theorem fp_unbounded (H : IsNormal f) : (Function.fixedPoints f).Unbounded (· < ·) :=
  by
  convert fp_family_unbounded fun _ : Unit => H
  exact (Set.interᵢ_const _).symm
#align ordinal.fp_unbounded Ordinal.fp_unbounded
-/

#print Ordinal.deriv /-
/-- The derivative of a normal function `f` is the sequence of fixed points of `f`. -/
def deriv (f : Ordinal → Ordinal) : Ordinal → Ordinal :=
  derivFamily fun _ : Unit => f
#align ordinal.deriv Ordinal.deriv
-/

#print Ordinal.deriv_eq_derivFamily /-
theorem deriv_eq_derivFamily (f : Ordinal → Ordinal) : deriv f = derivFamily fun _ : Unit => f :=
  rfl
#align ordinal.deriv_eq_deriv_family Ordinal.deriv_eq_derivFamily
-/

#print Ordinal.deriv_zero /-
@[simp]
theorem deriv_zero (f) : deriv f 0 = nfp f 0 :=
  derivFamily_zero _
#align ordinal.deriv_zero Ordinal.deriv_zero
-/

#print Ordinal.deriv_succ /-
@[simp]
theorem deriv_succ (f o) : deriv f (succ o) = nfp f (succ (deriv f o)) :=
  derivFamily_succ _ _
#align ordinal.deriv_succ Ordinal.deriv_succ
-/

#print Ordinal.deriv_limit /-
theorem deriv_limit (f) {o} : IsLimit o → deriv f o = bsup.{u, 0} o fun a _ => deriv f a :=
  derivFamily_limit _
#align ordinal.deriv_limit Ordinal.deriv_limit
-/

#print Ordinal.deriv_isNormal /-
theorem deriv_isNormal (f) : IsNormal (deriv f) :=
  derivFamily_isNormal _
#align ordinal.deriv_is_normal Ordinal.deriv_isNormal
-/

#print Ordinal.deriv_id_of_nfp_id /-
theorem deriv_id_of_nfp_id {f : Ordinal → Ordinal} (h : nfp f = id) : deriv f = id :=
  ((deriv_isNormal _).eq_iff_zero_and_succ IsNormal.refl).2 (by simp [h])
#align ordinal.deriv_id_of_nfp_id Ordinal.deriv_id_of_nfp_id
-/

#print Ordinal.IsNormal.deriv_fp /-
theorem IsNormal.deriv_fp {f} (H : IsNormal f) : ∀ o, f (deriv f o) = deriv f o :=
  @derivFamily_fp Unit (fun _ => f) Unit.unit H
#align ordinal.is_normal.deriv_fp Ordinal.IsNormal.deriv_fp
-/

#print Ordinal.IsNormal.le_iff_deriv /-
theorem IsNormal.le_iff_deriv {f} (H : IsNormal f) {a} : f a ≤ a ↔ ∃ o, deriv f o = a :=
  by
  unfold deriv
  rw [← le_iff_deriv_family fun _ : Unit => H]
  exact ⟨fun h _ => h, fun h => h Unit.unit⟩
#align ordinal.is_normal.le_iff_deriv Ordinal.IsNormal.le_iff_deriv
-/

#print Ordinal.IsNormal.fp_iff_deriv /-
theorem IsNormal.fp_iff_deriv {f} (H : IsNormal f) {a} : f a = a ↔ ∃ o, deriv f o = a := by
  rw [← H.le_iff_eq, H.le_iff_deriv]
#align ordinal.is_normal.fp_iff_deriv Ordinal.IsNormal.fp_iff_deriv
-/

#print Ordinal.deriv_eq_enumOrd /-
theorem deriv_eq_enumOrd (H : IsNormal f) : deriv f = enumOrd (Function.fixedPoints f) :=
  by
  convert deriv_family_eq_enum_ord fun _ : Unit => H
  exact (Set.interᵢ_const _).symm
#align ordinal.deriv_eq_enum_ord Ordinal.deriv_eq_enumOrd
-/

#print Ordinal.deriv_eq_id_of_nfp_eq_id /-
theorem deriv_eq_id_of_nfp_eq_id {f : Ordinal → Ordinal} (h : nfp f = id) : deriv f = id :=
  (IsNormal.eq_iff_zero_and_succ (deriv_isNormal _) IsNormal.refl).2 (by simp [h])
#align ordinal.deriv_eq_id_of_nfp_eq_id Ordinal.deriv_eq_id_of_nfp_eq_id
-/

end

/-! ### Fixed points of addition -/


/- warning: ordinal.nfp_add_zero -> Ordinal.nfp_add_zero is a dubious translation:
lean 3 declaration is
  forall (a : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.nfp.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) a) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a Ordinal.omega.{u1})
but is expected to have type
  forall (a : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.nfp.{u1} (fun (x._@.Mathlib.SetTheory.Ordinal.FixedPoint._hyg.5664 : Ordinal.{u1}) => HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) a x._@.Mathlib.SetTheory.Ordinal.FixedPoint._hyg.5664) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a Ordinal.omega.{u1})
Case conversion may be inaccurate. Consider using '#align ordinal.nfp_add_zero Ordinal.nfp_add_zeroₓ'. -/
@[simp]
theorem nfp_add_zero (a) : nfp ((· + ·) a) 0 = a * omega :=
  by
  simp_rw [← sup_iterate_eq_nfp, ← sup_mul_nat]
  congr ; funext
  induction' n with n hn
  · rw [Nat.cast_zero, mul_zero, iterate_zero_apply]
  · nth_rw 2 [Nat.succ_eq_one_add]
    rw [Nat.cast_add, Nat.cast_one, mul_one_add, iterate_succ_apply', hn]
#align ordinal.nfp_add_zero Ordinal.nfp_add_zero

/- warning: ordinal.nfp_add_eq_mul_omega -> Ordinal.nfp_add_eq_mul_omega is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) b (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a Ordinal.omega.{u1})) -> (Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.nfp.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) a) b) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a Ordinal.omega.{u1}))
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) b (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a Ordinal.omega.{u1})) -> (Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.nfp.{u1} (fun (x._@.Mathlib.SetTheory.Ordinal.FixedPoint._hyg.5803 : Ordinal.{u1}) => HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) a x._@.Mathlib.SetTheory.Ordinal.FixedPoint._hyg.5803) b) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a Ordinal.omega.{u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.nfp_add_eq_mul_omega Ordinal.nfp_add_eq_mul_omegaₓ'. -/
theorem nfp_add_eq_mul_omega {a b} (hba : b ≤ a * omega) : nfp ((· + ·) a) b = a * omega :=
  by
  apply le_antisymm (nfp_le_fp (add_is_normal a).Monotone hba _)
  · rw [← nfp_add_zero]
    exact nfp_monotone (add_is_normal a).Monotone (Ordinal.zero_le b)
  · rw [← mul_one_add, one_add_omega]
#align ordinal.nfp_add_eq_mul_omega Ordinal.nfp_add_eq_mul_omega

/- warning: ordinal.add_eq_right_iff_mul_omega_le -> Ordinal.add_eq_right_iff_mul_omega_le is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, Iff (Eq.{succ (succ u1)} Ordinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) a b) b) (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a Ordinal.omega.{u1}) b)
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, Iff (Eq.{succ (succ u1)} Ordinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) a b) b) (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a Ordinal.omega.{u1}) b)
Case conversion may be inaccurate. Consider using '#align ordinal.add_eq_right_iff_mul_omega_le Ordinal.add_eq_right_iff_mul_omega_leₓ'. -/
theorem add_eq_right_iff_mul_omega_le {a b : Ordinal} : a + b = b ↔ a * omega ≤ b :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · rw [← nfp_add_zero a, ← deriv_zero]
    cases' (add_is_normal a).fp_iff_deriv.1 h with c hc
    rw [← hc]
    exact (deriv_is_normal _).Monotone (Ordinal.zero_le _)
  · have := Ordinal.add_sub_cancel_of_le h
    nth_rw 1 [← this]
    rwa [← add_assoc, ← mul_one_add, one_add_omega]
#align ordinal.add_eq_right_iff_mul_omega_le Ordinal.add_eq_right_iff_mul_omega_le

/- warning: ordinal.add_le_right_iff_mul_omega_le -> Ordinal.add_le_right_iff_mul_omega_le is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, Iff (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) a b) b) (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a Ordinal.omega.{u1}) b)
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, Iff (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) a b) b) (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a Ordinal.omega.{u1}) b)
Case conversion may be inaccurate. Consider using '#align ordinal.add_le_right_iff_mul_omega_le Ordinal.add_le_right_iff_mul_omega_leₓ'. -/
theorem add_le_right_iff_mul_omega_le {a b : Ordinal} : a + b ≤ b ↔ a * omega ≤ b :=
  by
  rw [← add_eq_right_iff_mul_omega_le]
  exact (add_is_normal a).le_iff_eq
#align ordinal.add_le_right_iff_mul_omega_le Ordinal.add_le_right_iff_mul_omega_le

/- warning: ordinal.deriv_add_eq_mul_omega_add -> Ordinal.deriv_add_eq_mul_omega_add is a dubious translation:
lean 3 declaration is
  forall (a : Ordinal.{u1}) (b : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.deriv.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) a) b) (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a Ordinal.omega.{u1}) b)
but is expected to have type
  forall (a : Ordinal.{u1}) (b : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.deriv.{u1} (fun (x._@.Mathlib.SetTheory.Ordinal.FixedPoint._hyg.6179 : Ordinal.{u1}) => HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) a x._@.Mathlib.SetTheory.Ordinal.FixedPoint._hyg.6179) b) (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a Ordinal.omega.{u1}) b)
Case conversion may be inaccurate. Consider using '#align ordinal.deriv_add_eq_mul_omega_add Ordinal.deriv_add_eq_mul_omega_addₓ'. -/
theorem deriv_add_eq_mul_omega_add (a b : Ordinal.{u}) : deriv ((· + ·) a) b = a * omega + b :=
  by
  revert b
  rw [← funext_iff, is_normal.eq_iff_zero_and_succ (deriv_is_normal _) (add_is_normal _)]
  refine' ⟨_, fun a h => _⟩
  · rw [deriv_zero, add_zero]
    exact nfp_add_zero a
  · rw [deriv_succ, h, add_succ]
    exact nfp_eq_self (add_eq_right_iff_mul_omega_le.2 ((le_add_right _ _).trans (le_succ _)))
#align ordinal.deriv_add_eq_mul_omega_add Ordinal.deriv_add_eq_mul_omega_add

/-! ### Fixed points of multiplication -/


-- mathport name: ordinal.pow
local infixr:0 "^" => @pow Ordinal Ordinal Ordinal.hasPow

/- warning: ordinal.nfp_mul_one -> Ordinal.nfp_mul_one is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) a) -> (Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.nfp.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1}))
but is expected to have type
  forall {a : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})) a) -> (Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.nfp.{u1} (fun (x._@.Mathlib.SetTheory.Ordinal.FixedPoint._hyg.6348 : Ordinal.{u1}) => HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a x._@.Mathlib.SetTheory.Ordinal.FixedPoint._hyg.6348) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.nfp_mul_one Ordinal.nfp_mul_oneₓ'. -/
@[simp]
theorem nfp_mul_one {a : Ordinal} (ha : 0 < a) : nfp ((· * ·) a) 1 = (a^omega) :=
  by
  rw [← sup_iterate_eq_nfp, ← sup_opow_nat]
  · dsimp
    congr
    funext
    induction' n with n hn
    · rw [Nat.cast_zero, opow_zero, iterate_zero_apply]
    nth_rw 2 [Nat.succ_eq_one_add]
    rw [Nat.cast_add, Nat.cast_one, opow_add, opow_one, iterate_succ_apply', hn]
  · exact ha
#align ordinal.nfp_mul_one Ordinal.nfp_mul_one

/- warning: ordinal.nfp_mul_zero -> Ordinal.nfp_mul_zero is a dubious translation:
lean 3 declaration is
  forall (a : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.nfp.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))
but is expected to have type
  forall (a : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.nfp.{u1} (fun (x._@.Mathlib.SetTheory.Ordinal.FixedPoint._hyg.6509 : Ordinal.{u1}) => HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a x._@.Mathlib.SetTheory.Ordinal.FixedPoint._hyg.6509) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.nfp_mul_zero Ordinal.nfp_mul_zeroₓ'. -/
@[simp]
theorem nfp_mul_zero (a : Ordinal) : nfp ((· * ·) a) 0 = 0 :=
  by
  rw [← Ordinal.le_zero, nfp_le_iff]
  intro n
  induction' n with n hn; · rfl
  rwa [iterate_succ_apply, mul_zero]
#align ordinal.nfp_mul_zero Ordinal.nfp_mul_zero

/- warning: ordinal.nfp_zero_mul -> Ordinal.nfp_zero_mul is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} (Ordinal.{u1} -> Ordinal.{u1}) (Ordinal.nfp.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))))) (id.{succ (succ u1)} Ordinal.{u1})
but is expected to have type
  Eq.{succ (succ u1)} (Ordinal.{u1} -> Ordinal.{u1}) (Ordinal.nfp.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) (id.{succ (succ u1)} Ordinal.{u1})
Case conversion may be inaccurate. Consider using '#align ordinal.nfp_zero_mul Ordinal.nfp_zero_mulₓ'. -/
@[simp]
theorem nfp_zero_mul : nfp ((· * ·) 0) = id :=
  by
  rw [← sup_iterate_eq_nfp]
  refine' funext fun a => (sup_le fun n => _).antisymm (le_sup (fun n => ((· * ·) 0^[n]) a) 0)
  induction' n with n hn; · rfl
  rw [Function.iterate_succ']
  change 0 * _ ≤ a
  rw [zero_mul]
  exact Ordinal.zero_le a
#align ordinal.nfp_zero_mul Ordinal.nfp_zero_mul

/- warning: ordinal.deriv_mul_zero -> Ordinal.deriv_mul_zero is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} (Ordinal.{u1} -> Ordinal.{u1}) (Ordinal.deriv.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))))) (id.{succ (succ u1)} Ordinal.{u1})
but is expected to have type
  Eq.{succ (succ u1)} (Ordinal.{u1} -> Ordinal.{u1}) (Ordinal.deriv.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) (id.{succ (succ u1)} Ordinal.{u1})
Case conversion may be inaccurate. Consider using '#align ordinal.deriv_mul_zero Ordinal.deriv_mul_zeroₓ'. -/
@[simp]
theorem deriv_mul_zero : deriv ((· * ·) 0) = id :=
  deriv_eq_id_of_nfp_eq_id nfp_zero_mul
#align ordinal.deriv_mul_zero Ordinal.deriv_mul_zero

/- warning: ordinal.nfp_mul_eq_opow_omega -> Ordinal.nfp_mul_eq_opow_omega is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) b) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) b (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1})) -> (Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.nfp.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a) b) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1}))
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})) b) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) b (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1})) -> (Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.nfp.{u1} (fun (x._@.Mathlib.SetTheory.Ordinal.FixedPoint._hyg.6825 : Ordinal.{u1}) => HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a x._@.Mathlib.SetTheory.Ordinal.FixedPoint._hyg.6825) b) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.nfp_mul_eq_opow_omega Ordinal.nfp_mul_eq_opow_omegaₓ'. -/
theorem nfp_mul_eq_opow_omega {a b : Ordinal} (hb : 0 < b) (hba : b ≤ (a^omega)) :
    nfp ((· * ·) a) b = (a^omega.{u}) :=
  by
  cases' eq_zero_or_pos a with ha ha
  · rw [ha, zero_opow omega_ne_zero] at *
    rw [Ordinal.le_zero.1 hba, nfp_zero_mul]
    rfl
  apply le_antisymm
  · apply nfp_le_fp (mul_is_normal ha).Monotone hba
    rw [← opow_one_add, one_add_omega]
  rw [← nfp_mul_one ha]
  exact nfp_monotone (mul_is_normal ha).Monotone (one_le_iff_pos.2 hb)
#align ordinal.nfp_mul_eq_opow_omega Ordinal.nfp_mul_eq_opow_omega

/- warning: ordinal.eq_zero_or_opow_omega_le_of_mul_eq_right -> Ordinal.eq_zero_or_opow_omega_le_of_mul_eq_right is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, (Eq.{succ (succ u1)} Ordinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a b) b) -> (Or (Eq.{succ (succ u1)} Ordinal.{u1} b (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1}) b))
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, (Eq.{succ (succ u1)} Ordinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a b) b) -> (Or (Eq.{succ (succ u1)} Ordinal.{u1} b (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1}) b))
Case conversion may be inaccurate. Consider using '#align ordinal.eq_zero_or_opow_omega_le_of_mul_eq_right Ordinal.eq_zero_or_opow_omega_le_of_mul_eq_rightₓ'. -/
theorem eq_zero_or_opow_omega_le_of_mul_eq_right {a b : Ordinal} (hab : a * b = b) :
    b = 0 ∨ (a^omega.{u}) ≤ b :=
  by
  cases' eq_zero_or_pos a with ha ha
  · rw [ha, zero_opow omega_ne_zero]
    exact Or.inr (Ordinal.zero_le b)
  rw [or_iff_not_imp_left]
  intro hb
  change b ≠ 0 at hb
  rw [← nfp_mul_one ha]
  rw [← one_le_iff_ne_zero] at hb
  exact nfp_le_fp (mul_is_normal ha).Monotone hb (le_of_eq hab)
#align ordinal.eq_zero_or_opow_omega_le_of_mul_eq_right Ordinal.eq_zero_or_opow_omega_le_of_mul_eq_right

/- warning: ordinal.mul_eq_right_iff_opow_omega_dvd -> Ordinal.mul_eq_right_iff_opow_omega_dvd is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, Iff (Eq.{succ (succ u1)} Ordinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a b) b) (Dvd.Dvd.{succ u1} Ordinal.{u1} (semigroupDvd.{succ u1} Ordinal.{u1} (SemigroupWithZero.toSemigroup.{succ u1} Ordinal.{u1} (MonoidWithZero.toSemigroupWithZero.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1}))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1}) b)
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, Iff (Eq.{succ (succ u1)} Ordinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a b) b) (Dvd.dvd.{succ u1} Ordinal.{u1} (semigroupDvd.{succ u1} Ordinal.{u1} (SemigroupWithZero.toSemigroup.{succ u1} Ordinal.{u1} (MonoidWithZero.toSemigroupWithZero.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1}))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1}) b)
Case conversion may be inaccurate. Consider using '#align ordinal.mul_eq_right_iff_opow_omega_dvd Ordinal.mul_eq_right_iff_opow_omega_dvdₓ'. -/
theorem mul_eq_right_iff_opow_omega_dvd {a b : Ordinal} : a * b = b ↔ (a^omega) ∣ b :=
  by
  cases' eq_zero_or_pos a with ha ha
  · rw [ha, zero_mul, zero_opow omega_ne_zero, zero_dvd_iff]
    exact eq_comm
  refine' ⟨fun hab => _, fun h => _⟩
  · rw [dvd_iff_mod_eq_zero]
    rw [← div_add_mod b (a^omega), mul_add, ← mul_assoc, ← opow_one_add, one_add_omega,
      add_left_cancel] at hab
    cases' eq_zero_or_opow_omega_le_of_mul_eq_right hab with hab hab
    · exact hab
    refine' (not_lt_of_le hab (mod_lt b (opow_ne_zero omega _))).elim
    rwa [← Ordinal.pos_iff_ne_zero]
  cases' h with c hc
  rw [hc, ← mul_assoc, ← opow_one_add, one_add_omega]
#align ordinal.mul_eq_right_iff_opow_omega_dvd Ordinal.mul_eq_right_iff_opow_omega_dvd

/- warning: ordinal.mul_le_right_iff_opow_omega_dvd -> Ordinal.mul_le_right_iff_opow_omega_dvd is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) a) -> (Iff (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a b) b) (Dvd.Dvd.{succ u1} Ordinal.{u1} (semigroupDvd.{succ u1} Ordinal.{u1} (SemigroupWithZero.toSemigroup.{succ u1} Ordinal.{u1} (MonoidWithZero.toSemigroupWithZero.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1}))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1}) b))
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})) a) -> (Iff (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a b) b) (Dvd.dvd.{succ u1} Ordinal.{u1} (semigroupDvd.{succ u1} Ordinal.{u1} (SemigroupWithZero.toSemigroup.{succ u1} Ordinal.{u1} (MonoidWithZero.toSemigroupWithZero.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1}))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1}) b))
Case conversion may be inaccurate. Consider using '#align ordinal.mul_le_right_iff_opow_omega_dvd Ordinal.mul_le_right_iff_opow_omega_dvdₓ'. -/
theorem mul_le_right_iff_opow_omega_dvd {a b : Ordinal} (ha : 0 < a) : a * b ≤ b ↔ (a^omega) ∣ b :=
  by
  rw [← mul_eq_right_iff_opow_omega_dvd]
  exact (mul_is_normal ha).le_iff_eq
#align ordinal.mul_le_right_iff_opow_omega_dvd Ordinal.mul_le_right_iff_opow_omega_dvd

/- warning: ordinal.nfp_mul_opow_omega_add -> Ordinal.nfp_mul_opow_omega_add is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {c : Ordinal.{u1}} (b : Ordinal.{u1}), (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) a) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) c) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) c (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1})) -> (Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.nfp.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a) (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1}) b) c)) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1}) (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} b)))
but is expected to have type
  forall {a : Ordinal.{u1}} {c : Ordinal.{u1}} (b : Ordinal.{u1}), (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})) a) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})) c) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) c (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1})) -> (Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.nfp.{u1} (fun (x._@.Mathlib.SetTheory.Ordinal.FixedPoint._hyg.7524 : Ordinal.{u1}) => HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a x._@.Mathlib.SetTheory.Ordinal.FixedPoint._hyg.7524) (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1}) b) c)) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1}) (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} b)))
Case conversion may be inaccurate. Consider using '#align ordinal.nfp_mul_opow_omega_add Ordinal.nfp_mul_opow_omega_addₓ'. -/
theorem nfp_mul_opow_omega_add {a c : Ordinal} (b) (ha : 0 < a) (hc : 0 < c) (hca : c ≤ (a^omega)) :
    nfp ((· * ·) a) ((a^omega) * b + c) = (a^omega.{u}) * succ b :=
  by
  apply le_antisymm
  · apply nfp_le_fp (mul_is_normal ha).Monotone
    · rw [mul_succ]
      apply add_le_add_left hca
    · rw [← mul_assoc, ← opow_one_add, one_add_omega]
  · cases' mul_eq_right_iff_opow_omega_dvd.1 ((mul_is_normal ha).nfp_fp ((a^omega) * b + c)) with
      d hd
    rw [hd]
    apply mul_le_mul_left'
    have := le_nfp (Mul.mul a) ((a^omega) * b + c)
    rw [hd] at this
    have := (add_lt_add_left hc ((a^omega) * b)).trans_le this
    rw [add_zero, mul_lt_mul_iff_left (opow_pos omega ha)] at this
    rwa [succ_le_iff]
#align ordinal.nfp_mul_opow_omega_add Ordinal.nfp_mul_opow_omega_add

/- warning: ordinal.deriv_mul_eq_opow_omega_mul -> Ordinal.deriv_mul_eq_opow_omega_mul is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) a) -> (forall (b : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.deriv.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a) b) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1}) b))
but is expected to have type
  forall {a : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})) a) -> (forall (b : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.deriv.{u1} (fun (x._@.Mathlib.SetTheory.Ordinal.FixedPoint._hyg.7884 : Ordinal.{u1}) => HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a x._@.Mathlib.SetTheory.Ordinal.FixedPoint._hyg.7884) b) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a Ordinal.omega.{u1}) b))
Case conversion may be inaccurate. Consider using '#align ordinal.deriv_mul_eq_opow_omega_mul Ordinal.deriv_mul_eq_opow_omega_mulₓ'. -/
theorem deriv_mul_eq_opow_omega_mul {a : Ordinal.{u}} (ha : 0 < a) (b) :
    deriv ((· * ·) a) b = (a^omega) * b := by
  revert b
  rw [← funext_iff,
    is_normal.eq_iff_zero_and_succ (deriv_is_normal _) (mul_is_normal (opow_pos omega ha))]
  refine' ⟨_, fun c h => _⟩
  · rw [deriv_zero, nfp_mul_zero, mul_zero]
  · rw [deriv_succ, h]
    exact nfp_mul_opow_omega_add c ha zero_lt_one (one_le_iff_pos.2 (opow_pos _ ha))
#align ordinal.deriv_mul_eq_opow_omega_mul Ordinal.deriv_mul_eq_opow_omega_mul

end Ordinal

