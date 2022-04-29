/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathbin.SetTheory.Ordinal.Arithmetic

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
-/


noncomputable section

universe u v

open Function

namespace Ordinal

/-! ### Fixed points of type-indexed families of ordinals -/


section

variable {ι : Type u} {f : ι → Ordinal.{max u v} → Ordinal.{max u v}}

/-- The next common fixed point, at least `a`, for a family of normal functions.

`ordinal.nfp_family_fp` shows this is a fixed point, `ordinal.self_le_nfp_family` shows it's at
least `a`, and `ordinal.nfp_family_le_fp` shows this is the least ordinal with these properties. -/
def nfpFamily (f : ι → Ordinal → Ordinal) a : Ordinal :=
  sup (List.foldr f a)

theorem nfp_family_eq_sup (f : ι → Ordinal → Ordinal) a : nfpFamily f a = sup (List.foldr f a) :=
  rfl

theorem foldr_le_nfp_family (f : ι → Ordinal → Ordinal) a l : List.foldr f a l ≤ nfpFamily f a :=
  le_sup _ _

theorem self_le_nfp_family (f : ι → Ordinal → Ordinal) a : a ≤ nfpFamily f a :=
  le_sup _ []

theorem lt_nfp_family {a b} : a < nfpFamily f b ↔ ∃ l, a < List.foldr f b l :=
  lt_sup

theorem nfp_family_le_iff {a b} : nfpFamily f a ≤ b ↔ ∀ l, List.foldr f a l ≤ b :=
  sup_le_iff

theorem nfp_family_le {a b} : (∀ l, List.foldr f a l ≤ b) → nfpFamily f a ≤ b :=
  sup_le

theorem nfp_family_monotone (hf : ∀ i, Monotone (f i)) : Monotone (nfpFamily f) := fun a b h =>
  sup_le fun l => (List.foldr_monotone hf l h).trans (le_sup _ l)

theorem apply_lt_nfp_family (H : ∀ i, IsNormal (f i)) {a b} (hb : b < nfpFamily f a) i : f i b < nfpFamily f a :=
  let ⟨l, hl⟩ := lt_nfp_family.1 hb
  lt_sup.2 ⟨i :: l, (H i).StrictMono hl⟩

theorem apply_lt_nfp_family_iff [Nonempty ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∀ i, f i b < nfpFamily f a) ↔ b < nfpFamily f a :=
  ⟨fun h =>
    lt_nfp_family.2 <|
      let ⟨l, hl⟩ := lt_sup.1 (h (Classical.arbitrary ι))
      ⟨l, ((H _).self_le b).trans_lt hl⟩,
    apply_lt_nfp_family H⟩

theorem nfp_family_le_apply [Nonempty ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∃ i, nfpFamily f a ≤ f i b) ↔ nfpFamily f a ≤ b := by
  rw [← not_iff_not]
  push_neg
  exact apply_lt_nfp_family_iff H

theorem nfp_family_le_fp (H : ∀ i, Monotone (f i)) {a b} (ab : a ≤ b) (h : ∀ i, f i b ≤ b) : nfpFamily f a ≤ b :=
  sup_le fun l => by
    by_cases' hι : IsEmpty ι
    · rwa [@Unique.eq_default _ (@List.uniqueOfIsEmpty ι hι) l]
      
    · have := not_is_empty_iff.1 hι
      induction' l with i l IH generalizing a
      · exact ab
        
      exact (H i (IH ab)).trans (h i)
      

theorem nfp_family_fp {i} (H : IsNormal (f i)) a : f i (nfpFamily f a) = nfpFamily f a := by
  unfold nfp_family
  rw [@is_normal.sup _ H _ _ ⟨[]⟩]
  apply le_antisymmₓ <;> refine' Ordinal.sup_le fun l => _
  · exact le_sup _ (i :: l)
    
  · exact (H.self_le _).trans (le_sup _ _)
    

theorem apply_le_nfp_family [hι : Nonempty ι] {f : ι → Ordinal → Ordinal} (H : ∀ i, IsNormal (f i)) {a b} :
    (∀ i, f i b ≤ nfpFamily f a) ↔ b ≤ nfpFamily f a := by
  refine' ⟨fun h => _, fun h i => _⟩
  · cases' hι with i
    exact ((H i).self_le b).trans (h i)
    
  rw [← nfp_family_fp (H i)]
  exact (H i).Monotone h

theorem nfp_family_eq_self {f : ι → Ordinal → Ordinal} {a} (h : ∀ i, f i a = a) : nfpFamily f a = a :=
  le_antisymmₓ
    (sup_le fun l => by
      rw [List.foldr_fixed' h l])
    (self_le_nfp_family f a)

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
theorem fp_family_unbounded (H : ∀ i, IsNormal (f i)) : (⋂ i, Function.FixedPoints (f i)).Unbounded (· < ·) := fun a =>
  ⟨_, fun s ⟨i, hi⟩ => by
    rw [← hi]
    exact nfp_family_fp (H i) a, (self_le_nfp_family f a).not_lt⟩

/-- The derivative of a family of normal functions is the sequence of their common fixed points. -/
def derivFamily (f : ι → Ordinal → Ordinal) (o : Ordinal) : Ordinal :=
  limitRecOn o (nfpFamily f 0) (fun a IH => nfpFamily f (succ IH)) fun a l => bsup.{max u v, u} a

@[simp]
theorem deriv_family_zero (f : ι → Ordinal → Ordinal) : derivFamily f 0 = nfpFamily f 0 :=
  limit_rec_on_zero _ _ _

@[simp]
theorem deriv_family_succ (f : ι → Ordinal → Ordinal) o :
    derivFamily f (succ o) = nfpFamily f (succ (derivFamily f o)) :=
  limit_rec_on_succ _ _ _ _

theorem deriv_family_limit (f : ι → Ordinal → Ordinal) {o} :
    IsLimit o → derivFamily f o = bsup.{max u v, u} o fun a _ => derivFamily f a :=
  limit_rec_on_limit _ _ _ _

theorem deriv_family_is_normal (f : ι → Ordinal → Ordinal) : IsNormal (derivFamily f) :=
  ⟨fun o => by
    rw [deriv_family_succ, ← succ_le] <;> apply self_le_nfp_family, fun o l a => by
    rw [deriv_family_limit _ l, bsup_le_iff]⟩

theorem deriv_family_fp {i} (H : IsNormal (f i)) (o : Ordinal.{max u v}) : f i (derivFamily f o) = derivFamily f o := by
  refine' limit_rec_on o _ (fun o IH => _) _
  · rw [deriv_family_zero]
    exact nfp_family_fp H 0
    
  · rw [deriv_family_succ]
    exact nfp_family_fp H _
    
  · intro o l IH
    rw [deriv_family_limit _ l, IsNormal.bsup.{max u v, u, max u v} H (fun a _ => deriv_family f a) l.1]
    refine' eq_of_forall_ge_iff fun c => _
    simp (config := { contextual := true })only [bsup_le_iff, IH]
    

theorem le_iff_deriv_family (H : ∀ i, IsNormal (f i)) {a} : (∀ i, f i a ≤ a) ↔ ∃ o, derivFamily f o = a :=
  ⟨fun ha => by
    suffices : ∀ o _ : a ≤ deriv_family f o, ∃ o, deriv_family f o = a
    exact this a ((deriv_family_is_normal _).self_le _)
    refine' fun o => limit_rec_on o (fun h₁ => ⟨0, le_antisymmₓ _ h₁⟩) (fun o IH h₁ => _) fun o l IH h₁ => _
    · rw [deriv_family_zero]
      exact nfp_family_le_fp (fun i => (H i).Monotone) (Ordinal.zero_le _) ha
      
    · cases le_or_ltₓ a (deriv_family f o)
      · exact IH h
        
      refine' ⟨succ o, le_antisymmₓ _ h₁⟩
      rw [deriv_family_succ]
      exact nfp_family_le_fp (fun i => (H i).Monotone) (succ_le.2 h) ha
      
    · cases eq_or_lt_of_le h₁
      · exact ⟨_, h.symm⟩
        
      rw [deriv_family_limit _ l, ← not_leₓ, bsup_le_iff, not_ball] at h
      exact
        let ⟨o', h, hl⟩ := h
        IH o' h (le_of_not_leₓ hl)
      ,
    fun i => e ▸ le_of_eqₓ (deriv_family_fp (H i) _)⟩

theorem fp_iff_deriv_family (H : ∀ i, IsNormal (f i)) {a} : (∀ i, f i a = a) ↔ ∃ o, derivFamily f o = a :=
  Iff.trans ⟨fun h i => le_of_eqₓ (h i), fun h i => (H i).le_iff_eq.1 (h i)⟩ (le_iff_deriv_family H)

theorem deriv_family_eq_enum_ord (H : ∀ i, IsNormal (f i)) :
    derivFamily f = enumOrd (⋂ i, Function.FixedPoints (f i)) := by
  rw [← eq_enum_ord _ (fp_family_unbounded H)]
  use (deriv_family_is_normal f).StrictMono
  rw [Set.range_eq_iff]
  refine' ⟨_, fun a ha => _⟩
  · rintro a S ⟨i, hi⟩
    rw [← hi]
    exact deriv_family_fp (H i) a
    
  rw [Set.mem_Inter] at ha
  rwa [← fp_iff_deriv_family H]

end

/-! ### Fixed points of ordinal-indexed families of ordinals -/


section

variable {o : Ordinal.{u}} {f : ∀, ∀ b < o, ∀, Ordinal.{max u v} → Ordinal.{max u v}}

/-- The next common fixed point, at least `a`, for a family of normal functions indexed by ordinals.
-/
def nfpBfamily (o : Ordinal) (f : ∀, ∀ b < o, ∀, Ordinal → Ordinal) : Ordinal → Ordinal :=
  nfpFamily (familyOfBfamily o f)

theorem nfp_bfamily_eq_nfp_family {o : Ordinal} (f : ∀, ∀ b < o, ∀, Ordinal → Ordinal) :
    nfpBfamily o f = nfpFamily (familyOfBfamily o f) :=
  rfl

theorem foldr_le_nfp_bfamily {o : Ordinal} (f : ∀, ∀ b < o, ∀, Ordinal → Ordinal) a l :
    List.foldr (familyOfBfamily o f) a l ≤ nfpBfamily o f a :=
  le_sup _ _

theorem self_le_nfp_bfamily {o : Ordinal} (f : ∀, ∀ b < o, ∀, Ordinal → Ordinal) a : a ≤ nfpBfamily o f a :=
  le_sup _ []

theorem lt_nfp_bfamily {a b} : a < nfpBfamily o f b ↔ ∃ l, a < List.foldr (familyOfBfamily o f) b l :=
  lt_sup

theorem nfp_bfamily_le_iff {o : Ordinal} {f : ∀, ∀ b < o, ∀, Ordinal → Ordinal} {a b} :
    nfpBfamily o f a ≤ b ↔ ∀ l, List.foldr (familyOfBfamily o f) a l ≤ b :=
  sup_le_iff

theorem nfp_bfamily_le {o : Ordinal} {f : ∀, ∀ b < o, ∀, Ordinal → Ordinal} {a b} :
    (∀ l, List.foldr (familyOfBfamily o f) a l ≤ b) → nfpBfamily o f a ≤ b :=
  sup_le

theorem nfp_bfamily_monotone (hf : ∀ i hi, Monotone (f i hi)) : Monotone (nfpBfamily o f) :=
  nfp_family_monotone fun i => hf _ _

theorem apply_lt_nfp_bfamily (ho : o ≠ 0) (H : ∀ i hi, IsNormal (f i hi)) {a b} :
    (∀ i hi, f i hi b < nfpBfamily o f a) ↔ b < nfpBfamily o f a := by
  unfold nfp_bfamily
  rw [← @apply_lt_nfp_family_iff _ (family_of_bfamily o f) (out_nonempty_iff_ne_zero.2 ho) fun i => H _ _]
  refine' ⟨fun h i => h _ (typein_lt_self i), fun h i hio => _⟩
  rw [← family_of_bfamily_enum o f]
  apply h

theorem nfp_bfamily_le_apply (ho : o ≠ 0) (H : ∀ i hi, IsNormal (f i hi)) {a b} :
    (∃ i hi, nfpBfamily o f a ≤ f i hi b) ↔ nfpBfamily o f a ≤ b := by
  rw [← not_iff_not]
  push_neg
  convert apply_lt_nfp_bfamily ho H
  simp only [not_leₓ]

theorem nfp_bfamily_le_fp (H : ∀ i hi, Monotone (f i hi)) {a b} (ab : a ≤ b) (h : ∀ i hi, f i hi b ≤ b) :
    nfpBfamily o f a ≤ b :=
  nfp_family_le_fp (fun _ => H _ _) ab fun i => h _ _

theorem nfp_bfamily_fp {i hi} (H : IsNormal (f i hi)) a : f i hi (nfpBfamily o f a) = nfpBfamily o f a := by
  rw [← family_of_bfamily_enum o f]
  apply nfp_family_fp
  rw [family_of_bfamily_enum]
  exact H

theorem le_nfp_bfamily (ho : o ≠ 0) (H : ∀ i hi, IsNormal (f i hi)) {a b} :
    (∀ i hi, f i hi b ≤ nfpBfamily o f a) ↔ b ≤ nfpBfamily o f a := by
  refine' ⟨fun h => _, fun h i hi => _⟩
  · have ho' : 0 < o := Ordinal.pos_iff_ne_zero.2 ho
    exact ((H 0 ho').self_le b).trans (h 0 ho')
    
  rw [← nfp_bfamily_fp (H i hi)]
  exact (H i hi).Monotone h

theorem nfp_bfamily_eq_self {a} (h : ∀ i hi, f i hi a = a) : nfpBfamily o f a = a :=
  nfp_family_eq_self fun _ => h _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
theorem fp_bfamily_unbounded (H : ∀ i hi, IsNormal (f i hi)) :
    (⋂ (i) (hi), Function.FixedPoints (f i hi)).Unbounded (· < ·) := fun a =>
  ⟨_, by
    rw [Set.mem_Inter₂]
    exact fun i hi => nfp_bfamily_fp (H i hi) _, (self_le_nfp_bfamily f a).not_lt⟩

/-- The derivative of a family of normal functions is the sequence of their common fixed points. -/
def derivBfamily (o : Ordinal) (f : ∀, ∀ b < o, ∀, Ordinal → Ordinal) : Ordinal → Ordinal :=
  derivFamily (familyOfBfamily o f)

theorem deriv_bfamily_eq_deriv_family {o : Ordinal} (f : ∀, ∀ b < o, ∀, Ordinal → Ordinal) :
    derivBfamily o f = derivFamily (familyOfBfamily o f) :=
  rfl

theorem deriv_bfamily_is_normal {o : Ordinal} (f : ∀, ∀ b < o, ∀, Ordinal → Ordinal) : IsNormal (derivBfamily o f) :=
  deriv_family_is_normal _

theorem deriv_bfamily_fp {i hi} (H : IsNormal (f i hi)) (a : Ordinal) :
    f i hi (derivBfamily o f a) = derivBfamily o f a := by
  rw [← family_of_bfamily_enum o f]
  apply deriv_family_fp
  rw [family_of_bfamily_enum]
  exact H

theorem le_iff_deriv_bfamily (H : ∀ i hi, IsNormal (f i hi)) {a} :
    (∀ i hi, f i hi a ≤ a) ↔ ∃ b, derivBfamily o f b = a := by
  unfold deriv_bfamily
  rw [← le_iff_deriv_family]
  · refine' ⟨fun h i => h _ _, fun h i hi => _⟩
    rw [← family_of_bfamily_enum o f]
    apply h
    
  exact fun _ => H _ _

theorem fp_iff_deriv_bfamily (H : ∀ i hi, IsNormal (f i hi)) {a} :
    (∀ i hi, f i hi a = a) ↔ ∃ b, derivBfamily o f b = a := by
  rw [← le_iff_deriv_bfamily H]
  refine' ⟨fun h i hi => le_of_eqₓ (h i hi), fun h i hi => _⟩
  rw [← (H i hi).le_iff_eq]
  exact h i hi

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i hi)
theorem deriv_bfamily_eq_enum_ord (H : ∀ i hi, IsNormal (f i hi)) :
    derivBfamily o f = enumOrd (⋂ (i) (hi), Function.FixedPoints (f i hi)) := by
  rw [← eq_enum_ord _ (fp_bfamily_unbounded H)]
  use (deriv_bfamily_is_normal f).StrictMono
  rw [Set.range_eq_iff]
  refine' ⟨fun a => Set.mem_Inter₂.2 fun i hi => deriv_bfamily_fp (H i hi) a, fun a ha => _⟩
  rw [Set.mem_Inter₂] at ha
  rwa [← fp_iff_deriv_bfamily H]

end

end Ordinal

