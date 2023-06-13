/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn

! This file was ported from Lean 3 source module order.initial_seg
! leanprover-community/mathlib commit 730c6d4cab72b9d84fcfb9e95e8796e9cd8f40ba
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.RelIso.Set
import Mathbin.Order.WellFounded

/-!
# Initial and principal segments

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines initial and principal segments.

## Main definitions

* `initial_seg r s`: type of order embeddings of `r` into `s` for which the range is an initial
  segment (i.e., if `b` belongs to the range, then any `b' < b` also belongs to the range).
  It is denoted by `r ≼i s`.
* `principal_seg r s`: Type of order embeddings of `r` into `s` for which the range is a principal
  segment, i.e., an interval of the form `(-∞, top)` for some element `top`. It is denoted by
  `r ≺i s`.

## Notations

These notations belong to the `initial_seg` locale.

* `r ≼i s`: the type of initial segment embeddings of `r` into `s`.
* `r ≺i s`: the type of principal segment embeddings of `r` into `s`.
-/


/-!
### Initial segments

Order embeddings whose range is an initial segment of `s` (i.e., if `b` belongs to the range, then
any `b' < b` also belongs to the range). The type of these embeddings from `r` to `s` is called
`initial_seg r s`, and denoted by `r ≼i s`.
-/


variable {α : Type _} {β : Type _} {γ : Type _} {r : α → α → Prop} {s : β → β → Prop}
  {t : γ → γ → Prop}

open Function

#print InitialSeg /-
/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≼i s` is an order
embedding whose range is an initial segment. That is, whenever `b < f a` in `β` then `b` is in the
range of `f`. -/
structure InitialSeg {α β : Type _} (r : α → α → Prop) (s : β → β → Prop) extends r ↪r s where
  init' : ∀ a b, s b (to_rel_embedding a) → ∃ a', to_rel_embedding a' = b
#align initial_seg InitialSeg
-/

scoped[InitialSeg] infixl:25 " ≼i " => InitialSeg

namespace InitialSeg

instance : Coe (r ≼i s) (r ↪r s) :=
  ⟨InitialSeg.toRelEmbedding⟩

instance : EmbeddingLike (r ≼i s) α β where
  coe f := f.toFun
  coe_injective' := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    congr with x
    exact congr_fun h x
  injective' f := f.inj'

#print InitialSeg.ext /-
@[ext]
theorem ext {f g : r ≼i s} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align initial_seg.ext InitialSeg.ext
-/

@[simp]
theorem coeFn_mk (f : r ↪r s) (o) : (@InitialSeg.mk _ _ r s f o : α → β) = f :=
  rfl
#align initial_seg.coe_fn_mk InitialSeg.coeFn_mk

@[simp]
theorem coeFn_toRelEmbedding (f : r ≼i s) : (f.toRelEmbedding : α → β) = f :=
  rfl
#align initial_seg.coe_fn_to_rel_embedding InitialSeg.coeFn_toRelEmbedding

#print InitialSeg.coe_coe_fn /-
@[simp]
theorem coe_coe_fn (f : r ≼i s) : ((f : r ↪r s) : α → β) = f :=
  rfl
#align initial_seg.coe_coe_fn InitialSeg.coe_coe_fn
-/

#print InitialSeg.init /-
theorem init (f : r ≼i s) {a : α} {b : β} : s b (f a) → ∃ a', f a' = b :=
  f.init' _ _
#align initial_seg.init InitialSeg.init
-/

#print InitialSeg.map_rel_iff /-
theorem map_rel_iff (f : r ≼i s) {a b : α} : s (f a) (f b) ↔ r a b :=
  f.1.map_rel_iff
#align initial_seg.map_rel_iff InitialSeg.map_rel_iff
-/

#print InitialSeg.init_iff /-
theorem init_iff (f : r ≼i s) {a : α} {b : β} : s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
  ⟨fun h =>
    let ⟨a', e⟩ := f.dropLast h
    ⟨a', e, f.map_rel_iff.1 (e.symm ▸ h)⟩,
    fun ⟨a', e, h⟩ => e ▸ f.map_rel_iff.2 h⟩
#align initial_seg.init_iff InitialSeg.init_iff
-/

#print InitialSeg.ofIso /-
/-- An order isomorphism is an initial segment -/
def ofIso (f : r ≃r s) : r ≼i s :=
  ⟨f, fun a b h => ⟨f.symm b, RelIso.apply_symm_apply f _⟩⟩
#align initial_seg.of_iso InitialSeg.ofIso
-/

#print InitialSeg.refl /-
/-- The identity function shows that `≼i` is reflexive -/
@[refl]
protected def refl (r : α → α → Prop) : r ≼i r :=
  ⟨RelEmbedding.refl _, fun a b h => ⟨_, rfl⟩⟩
#align initial_seg.refl InitialSeg.refl
-/

instance (r : α → α → Prop) : Inhabited (r ≼i r) :=
  ⟨InitialSeg.refl r⟩

#print InitialSeg.trans /-
/-- Composition of functions shows that `≼i` is transitive -/
@[trans]
protected def trans (f : r ≼i s) (g : s ≼i t) : r ≼i t :=
  ⟨f.1.trans g.1, fun a c h => by
    simp at h ⊢
    rcases g.2 _ _ h with ⟨b, rfl⟩; have h := g.map_rel_iff.1 h
    rcases f.2 _ _ h with ⟨a', rfl⟩; exact ⟨a', rfl⟩⟩
#align initial_seg.trans InitialSeg.trans
-/

#print InitialSeg.refl_apply /-
@[simp]
theorem refl_apply (x : α) : InitialSeg.refl r x = x :=
  rfl
#align initial_seg.refl_apply InitialSeg.refl_apply
-/

#print InitialSeg.trans_apply /-
@[simp]
theorem trans_apply (f : r ≼i s) (g : s ≼i t) (a : α) : (f.trans g) a = g (f a) :=
  rfl
#align initial_seg.trans_apply InitialSeg.trans_apply
-/

#print InitialSeg.subsingleton_of_trichotomous_of_irrefl /-
instance subsingleton_of_trichotomous_of_irrefl [IsTrichotomous β s] [IsIrrefl β s]
    [IsWellFounded α r] : Subsingleton (r ≼i s) :=
  ⟨fun f g => by
    ext a
    apply IsWellFounded.induction r a fun b IH => _
    refine' extensional_of_trichotomous_of_irrefl s fun x => _
    rw [f.init_iff, g.init_iff]
    exact exists_congr fun x => and_congr_left fun hx => IH _ hx ▸ Iff.rfl⟩
#align initial_seg.subsingleton_of_trichotomous_of_irrefl InitialSeg.subsingleton_of_trichotomous_of_irrefl
-/

instance [IsWellOrder β s] : Subsingleton (r ≼i s) :=
  ⟨fun a => by letI := a.is_well_founded; apply Subsingleton.elim⟩

#print InitialSeg.eq /-
protected theorem eq [IsWellOrder β s] (f g : r ≼i s) (a) : f a = g a := by
  rw [Subsingleton.elim f g]
#align initial_seg.eq InitialSeg.eq
-/

#print InitialSeg.Antisymm.aux /-
theorem Antisymm.aux [IsWellOrder α r] (f : r ≼i s) (g : s ≼i r) : LeftInverse g f :=
  InitialSeg.eq (f.trans g) (InitialSeg.refl _)
#align initial_seg.antisymm.aux InitialSeg.Antisymm.aux
-/

#print InitialSeg.antisymm /-
/-- If we have order embeddings between `α` and `β` whose images are initial segments, and `β`
is a well-order then `α` and `β` are order-isomorphic. -/
def antisymm [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) : r ≃r s :=
  haveI := f.to_rel_embedding.is_well_order
  ⟨⟨f, g, antisymm.aux f g, antisymm.aux g f⟩, fun _ _ => f.map_rel_iff'⟩
#align initial_seg.antisymm InitialSeg.antisymm
-/

#print InitialSeg.antisymm_toFun /-
@[simp]
theorem antisymm_toFun [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) : (antisymm f g : α → β) = f :=
  rfl
#align initial_seg.antisymm_to_fun InitialSeg.antisymm_toFun
-/

#print InitialSeg.antisymm_symm /-
@[simp]
theorem antisymm_symm [IsWellOrder α r] [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) :
    (antisymm f g).symm = antisymm g f :=
  RelIso.coe_fn_injective rfl
#align initial_seg.antisymm_symm InitialSeg.antisymm_symm
-/

#print InitialSeg.eq_or_principal /-
theorem eq_or_principal [IsWellOrder β s] (f : r ≼i s) :
    Surjective f ∨ ∃ b, ∀ x, s x b ↔ ∃ y, f y = x :=
  or_iff_not_imp_right.2 fun h b =>
    Acc.recOn (IsWellFounded.wf.apply b : Acc s b) fun x H IH =>
      not_forall_not.1 fun hn =>
        h
          ⟨x, fun y =>
            ⟨IH _, fun ⟨a, e⟩ => by
              rw [← e] <;>
                exact
                  (trichotomous _ _).resolve_right
                    (not_or_of_not (hn a) fun hl => not_exists.2 hn (f.init hl))⟩⟩
#align initial_seg.eq_or_principal InitialSeg.eq_or_principal
-/

#print InitialSeg.codRestrict /-
/-- Restrict the codomain of an initial segment -/
def codRestrict (p : Set β) (f : r ≼i s) (H : ∀ a, f a ∈ p) : r ≼i Subrel s p :=
  ⟨RelEmbedding.codRestrict p f H, fun a ⟨b, m⟩ (h : s b (f a)) =>
    let ⟨a', e⟩ := f.dropLast h
    ⟨a', by clear _let_match <;> subst e <;> rfl⟩⟩
#align initial_seg.cod_restrict InitialSeg.codRestrict
-/

#print InitialSeg.codRestrict_apply /-
@[simp]
theorem codRestrict_apply (p) (f : r ≼i s) (H a) : codRestrict p f H a = ⟨f a, H a⟩ :=
  rfl
#align initial_seg.cod_restrict_apply InitialSeg.codRestrict_apply
-/

#print InitialSeg.ofIsEmpty /-
/-- Initial segment from an empty type. -/
def ofIsEmpty (r : α → α → Prop) (s : β → β → Prop) [IsEmpty α] : r ≼i s :=
  ⟨RelEmbedding.ofIsEmpty r s, isEmptyElim⟩
#align initial_seg.of_is_empty InitialSeg.ofIsEmpty
-/

#print InitialSeg.leAdd /-
/-- Initial segment embedding of an order `r` into the disjoint union of `r` and `s`. -/
def leAdd (r : α → α → Prop) (s : β → β → Prop) : r ≼i Sum.Lex r s :=
  ⟨⟨⟨Sum.inl, fun _ _ => Sum.inl.inj⟩, fun a b => Sum.lex_inl_inl⟩, fun a b => by
    cases b <;> [exact fun _ => ⟨_, rfl⟩; exact False.elim ∘ Sum.lex_inr_inl]⟩
#align initial_seg.le_add InitialSeg.leAdd
-/

#print InitialSeg.leAdd_apply /-
@[simp]
theorem leAdd_apply (r : α → α → Prop) (s : β → β → Prop) (a) : leAdd r s a = Sum.inl a :=
  rfl
#align initial_seg.le_add_apply InitialSeg.leAdd_apply
-/

#print InitialSeg.acc /-
protected theorem acc (f : r ≼i s) (a : α) : Acc r a ↔ Acc s (f a) :=
  ⟨by
    refine' fun h => Acc.recOn h fun a _ ha => Acc.intro _ fun b hb => _
    obtain ⟨a', rfl⟩ := f.init hb
    exact ha _ (f.map_rel_iff.mp hb), f.toRelEmbedding.Acc a⟩
#align initial_seg.acc InitialSeg.acc
-/

end InitialSeg

/-!
### Principal segments

Order embeddings whose range is a principal segment of `s` (i.e., an interval of the form
`(-∞, top)` for some element `top` of `β`). The type of these embeddings from `r` to `s` is called
`principal_seg r s`, and denoted by `r ≺i s`. Principal segments are in particular initial
segments.
-/


#print PrincipalSeg /-
/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≺i s` is an order
embedding whose range is an open interval `(-∞, top)` for some element `top` of `β`. Such order
embeddings are called principal segments -/
@[nolint has_nonempty_instance]
structure PrincipalSeg {α β : Type _} (r : α → α → Prop) (s : β → β → Prop) extends r ↪r s where
  top : β
  down' : ∀ b, s b top ↔ ∃ a, to_rel_embedding a = b
#align principal_seg PrincipalSeg
-/

scoped[InitialSeg] infixl:25 " ≺i " => PrincipalSeg

namespace PrincipalSeg

instance : Coe (r ≺i s) (r ↪r s) :=
  ⟨PrincipalSeg.toRelEmbedding⟩

instance : CoeFun (r ≺i s) fun _ => α → β :=
  ⟨fun f => f⟩

#print PrincipalSeg.coe_fn_mk /-
@[simp]
theorem coe_fn_mk (f : r ↪r s) (t o) : (@PrincipalSeg.mk _ _ r s f t o : α → β) = f :=
  rfl
#align principal_seg.coe_fn_mk PrincipalSeg.coe_fn_mk
-/

@[simp]
theorem coeFn_toRelEmbedding (f : r ≺i s) : (f.toRelEmbedding : α → β) = f :=
  rfl
#align principal_seg.coe_fn_to_rel_embedding PrincipalSeg.coeFn_toRelEmbedding

@[simp]
theorem coe_coeFn (f : r ≺i s) : ((f : r ↪r s) : α → β) = f :=
  rfl
#align principal_seg.coe_coe_fn PrincipalSeg.coe_coeFn

#print PrincipalSeg.down /-
theorem down (f : r ≺i s) : ∀ {b : β}, s b f.top ↔ ∃ a, f a = b :=
  f.down'
#align principal_seg.down PrincipalSeg.down
-/

#print PrincipalSeg.lt_top /-
theorem lt_top (f : r ≺i s) (a : α) : s (f a) f.top :=
  f.down.2 ⟨_, rfl⟩
#align principal_seg.lt_top PrincipalSeg.lt_top
-/

#print PrincipalSeg.init /-
theorem init [IsTrans β s] (f : r ≺i s) {a : α} {b : β} (h : s b (f a)) : ∃ a', f a' = b :=
  f.down.1 <| trans h <| f.lt_top _
#align principal_seg.init PrincipalSeg.init
-/

#print PrincipalSeg.hasCoeInitialSeg /-
/-- A principal segment is in particular an initial segment. -/
instance hasCoeInitialSeg [IsTrans β s] : Coe (r ≺i s) (r ≼i s) :=
  ⟨fun f => ⟨f.toRelEmbedding, fun a b => f.dropLast⟩⟩
#align principal_seg.has_coe_initial_seg PrincipalSeg.hasCoeInitialSeg
-/

#print PrincipalSeg.coe_coe_fn' /-
theorem coe_coe_fn' [IsTrans β s] (f : r ≺i s) : ((f : r ≼i s) : α → β) = f :=
  rfl
#align principal_seg.coe_coe_fn' PrincipalSeg.coe_coe_fn'
-/

#print PrincipalSeg.init_iff /-
theorem init_iff [IsTrans β s] (f : r ≺i s) {a : α} {b : β} : s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
  @InitialSeg.init_iff α β r s f a b
#align principal_seg.init_iff PrincipalSeg.init_iff
-/

#print PrincipalSeg.irrefl /-
theorem irrefl {r : α → α → Prop} [IsWellOrder α r] (f : r ≺i r) : False :=
  by
  have := f.lt_top f.top
  rw [show f f.top = f.top from InitialSeg.eq (↑f) (InitialSeg.refl r) f.top] at this 
  exact irrefl _ this
#align principal_seg.irrefl PrincipalSeg.irrefl
-/

instance (r : α → α → Prop) [IsWellOrder α r] : IsEmpty (r ≺i r) :=
  ⟨fun f => f.irrefl⟩

#print PrincipalSeg.ltLe /-
/-- Composition of a principal segment with an initial segment, as a principal segment -/
def ltLe (f : r ≺i s) (g : s ≼i t) : r ≺i t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g f.top, fun a => by
    simp only [g.init_iff, f.down', exists_and_distrib_left.symm, exists_swap,
        RelEmbedding.trans_apply, exists_eq_right'] <;>
      rfl⟩
#align principal_seg.lt_le PrincipalSeg.ltLe
-/

#print PrincipalSeg.lt_le_apply /-
@[simp]
theorem lt_le_apply (f : r ≺i s) (g : s ≼i t) (a : α) : (f.ltLe g) a = g (f a) :=
  RelEmbedding.trans_apply _ _ _
#align principal_seg.lt_le_apply PrincipalSeg.lt_le_apply
-/

#print PrincipalSeg.lt_le_top /-
@[simp]
theorem lt_le_top (f : r ≺i s) (g : s ≼i t) : (f.ltLe g).top = g f.top :=
  rfl
#align principal_seg.lt_le_top PrincipalSeg.lt_le_top
-/

#print PrincipalSeg.trans /-
/-- Composition of two principal segments as a principal segment -/
@[trans]
protected def trans [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) : r ≺i t :=
  ltLe f g
#align principal_seg.trans PrincipalSeg.trans
-/

#print PrincipalSeg.trans_apply /-
@[simp]
theorem trans_apply [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) (a : α) : (f.trans g) a = g (f a) :=
  lt_le_apply _ _ _
#align principal_seg.trans_apply PrincipalSeg.trans_apply
-/

#print PrincipalSeg.trans_top /-
@[simp]
theorem trans_top [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) : (f.trans g).top = g f.top :=
  rfl
#align principal_seg.trans_top PrincipalSeg.trans_top
-/

#print PrincipalSeg.equivLT /-
/-- Composition of an order isomorphism with a principal segment, as a principal segment -/
def equivLT (f : r ≃r s) (g : s ≺i t) : r ≺i t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g.top, fun c =>
    suffices (∃ a : β, g a = c) ↔ ∃ a : α, g (f a) = c by simpa [g.down]
    ⟨fun ⟨b, h⟩ => ⟨f.symm b, by simp only [h, RelIso.apply_symm_apply, RelIso.coe_coeFn]⟩,
      fun ⟨a, h⟩ => ⟨f a, h⟩⟩⟩
#align principal_seg.equiv_lt PrincipalSeg.equivLT
-/

#print PrincipalSeg.ltEquiv /-
/-- Composition of a principal segment with an order isomorphism, as a principal segment -/
def ltEquiv {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (f : PrincipalSeg r s)
    (g : s ≃r t) : PrincipalSeg r t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g f.top,
    by
    intro x
    rw [← g.apply_symm_apply x, g.map_rel_iff, f.down', exists_congr]
    intro y; exact ⟨congr_arg g, fun h => g.to_equiv.bijective.1 h⟩⟩
#align principal_seg.lt_equiv PrincipalSeg.ltEquiv
-/

#print PrincipalSeg.equivLT_apply /-
@[simp]
theorem equivLT_apply (f : r ≃r s) (g : s ≺i t) (a : α) : (equivLT f g) a = g (f a) :=
  RelEmbedding.trans_apply _ _ _
#align principal_seg.equiv_lt_apply PrincipalSeg.equivLT_apply
-/

#print PrincipalSeg.equivLT_top /-
@[simp]
theorem equivLT_top (f : r ≃r s) (g : s ≺i t) : (equivLT f g).top = g.top :=
  rfl
#align principal_seg.equiv_lt_top PrincipalSeg.equivLT_top
-/

/-- Given a well order `s`, there is a most one principal segment embedding of `r` into `s`. -/
instance [IsWellOrder β s] : Subsingleton (r ≺i s) :=
  ⟨fun f g =>
    by
    have ef : (f : α → β) = g := by
      show ((f : r ≼i s) : α → β) = g
      rw [@Subsingleton.elim _ _ (f : r ≼i s) g]; rfl
    have et : f.top = g.top :=
      by
      refine' extensional_of_trichotomous_of_irrefl s fun x => _
      simp only [f.down, g.down, ef, coe_fn_to_rel_embedding]
    cases f; cases g
    have := RelEmbedding.coe_fn_injective ef <;> congr⟩

#print PrincipalSeg.top_eq /-
theorem top_eq [IsWellOrder γ t] (e : r ≃r s) (f : r ≺i t) (g : s ≺i t) : f.top = g.top := by
  rw [Subsingleton.elim f (PrincipalSeg.equivLT e g)] <;> rfl
#align principal_seg.top_eq PrincipalSeg.top_eq
-/

#print PrincipalSeg.topLTTop /-
theorem topLTTop {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} [IsWellOrder γ t]
    (f : PrincipalSeg r s) (g : PrincipalSeg s t) (h : PrincipalSeg r t) : t h.top g.top := by
  rw [Subsingleton.elim h (f.trans g)]; apply PrincipalSeg.lt_top
#align principal_seg.top_lt_top PrincipalSeg.topLTTop
-/

#print PrincipalSeg.ofElement /-
/-- Any element of a well order yields a principal segment -/
def ofElement {α : Type _} (r : α → α → Prop) (a : α) : Subrel r {b | r b a} ≺i r :=
  ⟨Subrel.relEmbedding _ _, a, fun b => ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨⟨_, h⟩, rfl⟩ => h⟩⟩
#align principal_seg.of_element PrincipalSeg.ofElement
-/

#print PrincipalSeg.ofElement_apply /-
@[simp]
theorem ofElement_apply {α : Type _} (r : α → α → Prop) (a : α) (b) : ofElement r a b = b.1 :=
  rfl
#align principal_seg.of_element_apply PrincipalSeg.ofElement_apply
-/

#print PrincipalSeg.ofElement_top /-
@[simp]
theorem ofElement_top {α : Type _} (r : α → α → Prop) (a : α) : (ofElement r a).top = a :=
  rfl
#align principal_seg.of_element_top PrincipalSeg.ofElement_top
-/

#print PrincipalSeg.codRestrict /-
/-- Restrict the codomain of a principal segment -/
def codRestrict (p : Set β) (f : r ≺i s) (H : ∀ a, f a ∈ p) (H₂ : f.top ∈ p) : r ≺i Subrel s p :=
  ⟨RelEmbedding.codRestrict p f H, ⟨f.top, H₂⟩, fun ⟨b, h⟩ =>
    f.down.trans <|
      exists_congr fun a => show (⟨f a, H a⟩ : p).1 = _ ↔ _ from ⟨Subtype.eq, congr_arg _⟩⟩
#align principal_seg.cod_restrict PrincipalSeg.codRestrict
-/

#print PrincipalSeg.codRestrict_apply /-
@[simp]
theorem codRestrict_apply (p) (f : r ≺i s) (H H₂ a) : codRestrict p f H H₂ a = ⟨f a, H a⟩ :=
  rfl
#align principal_seg.cod_restrict_apply PrincipalSeg.codRestrict_apply
-/

#print PrincipalSeg.codRestrict_top /-
@[simp]
theorem codRestrict_top (p) (f : r ≺i s) (H H₂) : (codRestrict p f H H₂).top = ⟨f.top, H₂⟩ :=
  rfl
#align principal_seg.cod_restrict_top PrincipalSeg.codRestrict_top
-/

#print PrincipalSeg.ofIsEmpty /-
/-- Principal segment from an empty type into a type with a minimal element. -/
def ofIsEmpty (r : α → α → Prop) [IsEmpty α] {b : β} (H : ∀ b', ¬s b' b) : r ≺i s :=
  { RelEmbedding.ofIsEmpty r s with
    top := b
    down' := by simp [H] }
#align principal_seg.of_is_empty PrincipalSeg.ofIsEmpty
-/

#print PrincipalSeg.ofIsEmpty_top /-
@[simp]
theorem ofIsEmpty_top (r : α → α → Prop) [IsEmpty α] {b : β} (H : ∀ b', ¬s b' b) :
    (ofIsEmpty r H).top = b :=
  rfl
#align principal_seg.of_is_empty_top PrincipalSeg.ofIsEmpty_top
-/

#print PrincipalSeg.pemptyToPunit /-
/-- Principal segment from the empty relation on `pempty` to the empty relation on `punit`. -/
@[reducible]
def pemptyToPunit : @EmptyRelation PEmpty ≺i @EmptyRelation PUnit :=
  @ofIsEmpty _ _ EmptyRelation _ _ PUnit.unit fun x => not_false
#align principal_seg.pempty_to_punit PrincipalSeg.pemptyToPunit
-/

#print PrincipalSeg.acc /-
protected theorem acc [IsTrans β s] (f : r ≺i s) (a : α) : Acc r a ↔ Acc s (f a) :=
  (f : r ≼i s).Acc a
#align principal_seg.acc PrincipalSeg.acc
-/

end PrincipalSeg

#print wellFounded_iff_wellFounded_subrel /-
/-- A relation is well-founded iff every principal segment of it is well-founded.

In this lemma we use `subrel` to indicate its principal segments because it's usually more
convenient to use.
-/
theorem wellFounded_iff_wellFounded_subrel {β : Type _} {s : β → β → Prop} [IsTrans β s] :
    WellFounded s ↔ ∀ b, WellFounded (Subrel s {b' | s b' b}) :=
  by
  refine'
    ⟨fun wf b => ⟨fun b' => ((PrincipalSeg.ofElement _ b).Acc b').mpr (wf.apply b')⟩, fun wf =>
      ⟨fun b => Acc.intro _ fun b' hb' => _⟩⟩
  let f := PrincipalSeg.ofElement s b
  obtain ⟨b', rfl⟩ := f.down.mp ((PrincipalSeg.ofElement_top s b).symm ▸ hb' : s b' f.top)
  exact (f.acc b').mp ((wf b).apply b')
#align well_founded_iff_well_founded_subrel wellFounded_iff_wellFounded_subrel
-/

#print wellFounded_iff_principalSeg /-
theorem wellFounded_iff_principalSeg.{u} {β : Type u} {s : β → β → Prop} [IsTrans β s] :
    WellFounded s ↔ ∀ (α : Type u) (r : α → α → Prop) (f : r ≺i s), WellFounded r :=
  ⟨fun wf α r f => RelHomClass.wellFounded f.toRelEmbedding wf, fun h =>
    wellFounded_iff_wellFounded_subrel.mpr fun b => h _ _ (PrincipalSeg.ofElement s b)⟩
#align well_founded_iff_principal_seg wellFounded_iff_principalSeg
-/

/-! ### Properties of initial and principal segments -/


#print InitialSeg.ltOrEq /-
/-- To an initial segment taking values in a well order, one can associate either a principal
segment (if the range is not everything, hence one can take as top the minimum of the complement
of the range) or an order isomorphism (if the range is everything). -/
noncomputable def InitialSeg.ltOrEq [IsWellOrder β s] (f : r ≼i s) : Sum (r ≺i s) (r ≃r s) :=
  by
  by_cases h : surjective f
  · exact Sum.inr (RelIso.ofSurjective f h)
  · have h' : _ := (InitialSeg.eq_or_principal f).resolve_left h
    exact Sum.inl ⟨f, Classical.choose h', Classical.choose_spec h'⟩
#align initial_seg.lt_or_eq InitialSeg.ltOrEq
-/

#print InitialSeg.ltOrEq_apply_left /-
theorem InitialSeg.ltOrEq_apply_left [IsWellOrder β s] (f : r ≼i s) (g : r ≺i s) (a : α) :
    g a = f a :=
  @InitialSeg.eq α β r s _ g f a
#align initial_seg.lt_or_eq_apply_left InitialSeg.ltOrEq_apply_left
-/

#print InitialSeg.ltOrEq_apply_right /-
theorem InitialSeg.ltOrEq_apply_right [IsWellOrder β s] (f : r ≼i s) (g : r ≃r s) (a : α) :
    g a = f a :=
  InitialSeg.eq (InitialSeg.ofIso g) f a
#align initial_seg.lt_or_eq_apply_right InitialSeg.ltOrEq_apply_right
-/

#print InitialSeg.leLT /-
/-- Composition of an initial segment taking values in a well order and a principal segment. -/
noncomputable def InitialSeg.leLT [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t) :
    r ≺i t :=
  match f.lt_or_eq with
  | Sum.inl f' => f'.trans g
  | Sum.inr f' => PrincipalSeg.equivLT f' g
#align initial_seg.le_lt InitialSeg.leLT
-/

#print InitialSeg.leLT_apply /-
@[simp]
theorem InitialSeg.leLT_apply [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t) (a : α) :
    (f.leLT g) a = g (f a) := by
  delta InitialSeg.leLT; cases' h : f.lt_or_eq with f' f'
  · simp only [PrincipalSeg.trans_apply, f.lt_or_eq_apply_left]
  · simp only [PrincipalSeg.equivLT_apply, f.lt_or_eq_apply_right]
#align initial_seg.le_lt_apply InitialSeg.leLT_apply
-/

namespace RelEmbedding

#print RelEmbedding.collapseF /-
/-- Given an order embedding into a well order, collapse the order embedding by filling the
gaps, to obtain an initial segment. Here, we construct the collapsed order embedding pointwise,
but the proof of the fact that it is an initial segment will be given in `collapse`. -/
noncomputable def collapseF [IsWellOrder β s] (f : r ↪r s) : ∀ a, { b // ¬s (f a) b } :=
  (RelEmbedding.wellFounded f <| IsWellFounded.wf).fix fun a IH =>
    by
    let S := {b | ∀ a h, s (IH a h).1 b}
    have : f a ∈ S := fun a' h =>
      ((trichotomous _ _).resolve_left fun h' =>
            (IH a' h).2 <| trans (f.map_rel_iff.2 h) h').resolve_left
        fun h' => (IH a' h).2 <| h' ▸ f.map_rel_iff.2 h
    exact ⟨is_well_founded.wf.min S ⟨_, this⟩, is_well_founded.wf.not_lt_min _ _ this⟩
#align rel_embedding.collapse_F RelEmbedding.collapseF
-/

#print RelEmbedding.collapseF.lt /-
theorem collapseF.lt [IsWellOrder β s] (f : r ↪r s) {a : α} :
    ∀ {a'}, r a' a → s (collapseF f a').1 (collapseF f a).1 :=
  show (collapseF f a).1 ∈ {b | ∀ (a') (h : r a' a), s (collapseF f a').1 b}
    by
    unfold collapse_F; rw [WellFounded.fix_eq]
    apply WellFounded.min_mem _ _
#align rel_embedding.collapse_F.lt RelEmbedding.collapseF.lt
-/

#print RelEmbedding.collapseF.not_lt /-
theorem collapseF.not_lt [IsWellOrder β s] (f : r ↪r s) (a : α) {b}
    (h : ∀ (a') (h : r a' a), s (collapseF f a').1 b) : ¬s b (collapseF f a).1 :=
  by
  unfold collapse_F; rw [WellFounded.fix_eq]
  exact
    WellFounded.not_lt_min _ _ _
      (show b ∈ {b | ∀ (a') (h : r a' a), s (collapse_F f a').1 b} from h)
#align rel_embedding.collapse_F.not_lt RelEmbedding.collapseF.not_lt
-/

#print RelEmbedding.collapse /-
/-- Construct an initial segment from an order embedding into a well order, by collapsing it
to fill the gaps. -/
noncomputable def collapse [IsWellOrder β s] (f : r ↪r s) : r ≼i s :=
  haveI := RelEmbedding.isWellOrder f
  ⟨RelEmbedding.ofMonotone (fun a => (collapse_F f a).1) fun a b => collapse_F.lt f, fun a b =>
    Acc.recOn (is_well_founded.wf.apply b : Acc s b)
      (fun b H IH a h => by
        let S := {a | ¬s (collapse_F f a).1 b}
        have : S.nonempty := ⟨_, asymm h⟩
        exists (IsWellFounded.wf : WellFounded r).min S this
        refine' ((@trichotomous _ s _ _ _).resolve_left _).resolve_right _
        · exact (IsWellFounded.wf : WellFounded r).min_mem S this
        · refine' collapse_F.not_lt f _ fun a' h' => _
          by_contra hn
          exact is_well_founded.wf.not_lt_min S this hn h')
      a⟩
#align rel_embedding.collapse RelEmbedding.collapse
-/

#print RelEmbedding.collapse_apply /-
theorem collapse_apply [IsWellOrder β s] (f : r ↪r s) (a) : collapse f a = (collapseF f a).1 :=
  rfl
#align rel_embedding.collapse_apply RelEmbedding.collapse_apply
-/

end RelEmbedding

