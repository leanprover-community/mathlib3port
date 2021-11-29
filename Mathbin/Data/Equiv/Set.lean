import Mathbin.Data.Equiv.Basic 
import Mathbin.Data.Set.Function

/-!
# Equivalences and sets

In this file we provide lemmas linking equivalences to sets.

Some notable definitions are:

* `equiv.of_injective`: an injective function is (noncomputably) equivalent to its range.
* `equiv.set_congr`: two equal sets are equivalent as types.
* `equiv.set.union`: a disjoint union of sets is equivalent to their `sum`.

This file is separate from `equiv/basic` such that we do not require the full lattice structure
on sets before defining what an equivalence is.
-/


open Function

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

namespace Equiv

@[simp]
theorem range_eq_univ {α : Type _} {β : Type _} (e : α ≃ β) : Set.Range e = Set.Univ :=
  Set.eq_univ_of_forall e.surjective

protected theorem image_eq_preimage {α β} (e : α ≃ β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  Set.ext$ fun x => Set.mem_image_iff_of_inverse e.left_inv e.right_inv

theorem _root_.set.mem_image_equiv {α β} {S : Set α} {f : α ≃ β} {x : β} : x ∈ f '' S ↔ f.symm x ∈ S :=
  Set.ext_iff.mp (f.image_eq_preimage S) x

/-- Alias for `equiv.image_eq_preimage` -/
theorem _root_.set.image_equiv_eq_preimage_symm {α β} (S : Set α) (f : α ≃ β) : f '' S = f.symm ⁻¹' S :=
  f.image_eq_preimage S

/-- Alias for `equiv.image_eq_preimage` -/
theorem _root_.set.preimage_equiv_eq_image_symm {α β} (S : Set α) (f : β ≃ α) : f ⁻¹' S = f.symm '' S :=
  (f.symm.image_eq_preimage S).symm

@[simp]
protected theorem subset_image {α β} (e : α ≃ β) (s : Set α) (t : Set β) : e.symm '' t ⊆ s ↔ t ⊆ e '' s :=
  by 
    rw [Set.image_subset_iff, e.image_eq_preimage]

@[simp]
protected theorem subset_image' {α β} (e : α ≃ β) (s : Set α) (t : Set β) : s ⊆ e.symm '' t ↔ e '' s ⊆ t :=
  calc s ⊆ e.symm '' t ↔ e.symm.symm '' s ⊆ t :=
    by 
      rw [e.symm.subset_image]
    _ ↔ e '' s ⊆ t :=
    by 
      rw [e.symm_symm]
    

@[simp]
theorem symm_image_image {α β} (e : α ≃ β) (s : Set α) : e.symm '' (e '' s) = s :=
  e.left_inverse_symm.image_image s

theorem eq_image_iff_symm_image_eq {α β} (e : α ≃ β) (s : Set α) (t : Set β) : t = e '' s ↔ e.symm '' t = s :=
  (e.symm.injective.image_injective.eq_iff' (e.symm_image_image s)).symm

@[simp]
theorem image_symm_image {α β} (e : α ≃ β) (s : Set β) : e '' (e.symm '' s) = s :=
  e.symm.symm_image_image s

@[simp]
theorem image_preimage {α β} (e : α ≃ β) (s : Set β) : e '' (e ⁻¹' s) = s :=
  e.surjective.image_preimage s

@[simp]
theorem preimage_image {α β} (e : α ≃ β) (s : Set α) : e ⁻¹' (e '' s) = s :=
  e.injective.preimage_image s

protected theorem image_compl {α β} (f : Equiv α β) (s : Set α) : f '' «expr ᶜ» s = «expr ᶜ» (f '' s) :=
  Set.image_compl_eq f.bijective

@[simp]
theorem symm_preimage_preimage {α β} (e : α ≃ β) (s : Set β) : e.symm ⁻¹' (e ⁻¹' s) = s :=
  e.right_inverse_symm.preimage_preimage s

@[simp]
theorem preimage_symm_preimage {α β} (e : α ≃ β) (s : Set α) : e ⁻¹' (e.symm ⁻¹' s) = s :=
  e.left_inverse_symm.preimage_preimage s

@[simp]
theorem preimage_subset {α β} (e : α ≃ β) (s t : Set β) : e ⁻¹' s ⊆ e ⁻¹' t ↔ s ⊆ t :=
  e.surjective.preimage_subset_preimage_iff

@[simp]
theorem image_subset {α β} (e : α ≃ β) (s t : Set α) : e '' s ⊆ e '' t ↔ s ⊆ t :=
  Set.image_subset_image_iff e.injective

@[simp]
theorem image_eq_iff_eq {α β} (e : α ≃ β) (s t : Set α) : e '' s = e '' t ↔ s = t :=
  Set.image_eq_image e.injective

theorem preimage_eq_iff_eq_image {α β} (e : α ≃ β) s t : e ⁻¹' s = t ↔ s = e '' t :=
  Set.preimage_eq_iff_eq_image e.bijective

theorem eq_preimage_iff_image_eq {α β} (e : α ≃ β) s t : s = e ⁻¹' t ↔ e '' s = t :=
  Set.eq_preimage_iff_image_eq e.bijective

theorem prod_assoc_preimage {α β γ} {s : Set α} {t : Set β} {u : Set γ} :
  Equiv.prodAssoc α β γ ⁻¹' s.prod (t.prod u) = (s.prod t).Prod u :=
  by 
    ext 
    simp [and_assoc]

/-- A set `s` in `α × β` is equivalent to the sigma-type `Σ x, {y | (x, y) ∈ s}`. -/
def set_prod_equiv_sigma {α β : Type _} (s : Set (α × β)) : s ≃ Σx : α, { y | (x, y) ∈ s } :=
  { toFun :=
      fun x =>
        ⟨x.1.1, x.1.2,
          by 
            simp ⟩,
    invFun := fun x => ⟨(x.1, x.2.1), x.2.2⟩, left_inv := fun ⟨⟨x, y⟩, h⟩ => rfl, right_inv := fun ⟨x, y, h⟩ => rfl }

/-- The subtypes corresponding to equal sets are equivalent. -/
@[simps apply]
def set_congr {α : Type _} {s t : Set α} (h : s = t) : s ≃ t :=
  subtype_equiv_prop h

/--
A set is equivalent to its image under an equivalence.
-/
@[simps]
def image {α β : Type _} (e : α ≃ β) (s : Set α) : s ≃ e '' s :=
  { toFun :=
      fun x =>
        ⟨e x.1,
          by 
            simp ⟩,
    invFun :=
      fun y =>
        ⟨e.symm y.1,
          by 
            rcases y with ⟨-, ⟨a, ⟨m, rfl⟩⟩⟩
            simpa using m⟩,
    left_inv :=
      fun x =>
        by 
          simp ,
    right_inv :=
      fun y =>
        by 
          simp  }

open Set

namespace Set

/-- `univ α` is equivalent to `α`. -/
@[simps apply symmApply]
protected def univ α : @univ α ≃ α :=
  ⟨coeₓ, fun a => ⟨a, trivialₓ⟩, fun ⟨a, _⟩ => rfl, fun a => rfl⟩

/-- An empty set is equivalent to the `empty` type. -/
protected def Empty α : (∅ : Set α) ≃ Empty :=
  equiv_empty _

/-- An empty set is equivalent to a `pempty` type. -/
protected def Pempty α : (∅ : Set α) ≃ Pempty :=
  equiv_pempty _

/-- If sets `s` and `t` are separated by a decidable predicate, then `s ∪ t` is equivalent to
`s ⊕ t`. -/
protected def union' {α} {s t : Set α} (p : α → Prop) [DecidablePred p] (hs : ∀ x _ : x ∈ s, p x)
  (ht : ∀ x _ : x ∈ t, ¬p x) : (s ∪ t : Set α) ≃ Sum s t :=
  { toFun :=
      fun x =>
        if hp : p x then Sum.inl ⟨_, x.2.resolve_right fun xt => ht _ xt hp⟩ else
          Sum.inr ⟨_, x.2.resolve_left fun xs => hp (hs _ xs)⟩,
    invFun :=
      fun o =>
        match o with 
        | Sum.inl x => ⟨x, Or.inl x.2⟩
        | Sum.inr x => ⟨x, Or.inr x.2⟩,
    left_inv :=
      fun ⟨x, h'⟩ =>
        by 
          byCases' p x <;> simp [union'._match_1, h] <;> congr,
    right_inv :=
      fun o =>
        by 
          rcases o with (⟨x, h⟩ | ⟨x, h⟩) <;> dsimp [union'._match_1] <;> [simp [hs _ h], simp [ht _ h]] }

/-- If sets `s` and `t` are disjoint, then `s ∪ t` is equivalent to `s ⊕ t`. -/
protected def union {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅) : (s ∪ t : Set α) ≃ Sum s t :=
  set.union' (fun x => x ∈ s) (fun _ => id) fun x xt xs => H ⟨xs, xt⟩

theorem union_apply_left {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅) {a : (s ∪ t : Set α)}
  (ha : «expr↑ » a ∈ s) : Equiv.Set.union H a = Sum.inl ⟨a, ha⟩ :=
  dif_pos ha

theorem union_apply_right {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅) {a : (s ∪ t : Set α)}
  (ha : «expr↑ » a ∈ t) : Equiv.Set.union H a = Sum.inr ⟨a, ha⟩ :=
  dif_neg$ fun h => H ⟨h, ha⟩

@[simp]
theorem union_symm_apply_left {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅) (a : s) :
  (Equiv.Set.union H).symm (Sum.inl a) = ⟨a, subset_union_left _ _ a.2⟩ :=
  rfl

@[simp]
theorem union_symm_apply_right {α} {s t : Set α} [DecidablePred fun x => x ∈ s] (H : s ∩ t ⊆ ∅) (a : t) :
  (Equiv.Set.union H).symm (Sum.inr a) = ⟨a, subset_union_right _ _ a.2⟩ :=
  rfl

/-- A singleton set is equivalent to a `punit` type. -/
protected def singleton {α} (a : α) : ({a} : Set α) ≃ PUnit.{u} :=
  ⟨fun _ => PUnit.unit, fun _ => ⟨a, mem_singleton _⟩,
    fun ⟨x, h⟩ =>
      by 
        simp  at h 
        subst x,
    fun ⟨⟩ => rfl⟩

/-- Equal sets are equivalent. -/
@[simps apply symmApply]
protected def of_eq {α : Type u} {s t : Set α} (h : s = t) : s ≃ t :=
  { toFun := fun x => ⟨x, h ▸ x.2⟩, invFun := fun x => ⟨x, h.symm ▸ x.2⟩, left_inv := fun _ => Subtype.eq rfl,
    right_inv := fun _ => Subtype.eq rfl }

/-- If `a ∉ s`, then `insert a s` is equivalent to `s ⊕ punit`. -/
protected def insert {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s) :
  (insert a s : Set α) ≃ Sum s PUnit.{u + 1} :=
  calc (insert a s : Set α) ≃ «expr↥ » (s ∪ {a}) :=
    Equiv.Set.ofEq
      (by 
        simp )
    _ ≃ Sum s ({a} : Set α) :=
    Equiv.Set.union
      (by 
        finish [Set.subset_def])
    _ ≃ Sum s PUnit.{u + 1} := sum_congr (Equiv.refl _) (Equiv.Set.singleton _)
    

@[simp]
theorem insert_symm_apply_inl {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s) (b : s) :
  (Equiv.Set.insert H).symm (Sum.inl b) = ⟨b, Or.inr b.2⟩ :=
  rfl

@[simp]
theorem insert_symm_apply_inr {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s) (b : PUnit.{u + 1}) :
  (Equiv.Set.insert H).symm (Sum.inr b) = ⟨a, Or.inl rfl⟩ :=
  rfl

@[simp]
theorem insert_apply_left {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s) :
  Equiv.Set.insert H ⟨a, Or.inl rfl⟩ = Sum.inr PUnit.unit :=
  (Equiv.Set.insert H).apply_eq_iff_eq_symm_apply.2 rfl

@[simp]
theorem insert_apply_right {α} {s : Set.{u} α} [DecidablePred (· ∈ s)] {a : α} (H : a ∉ s) (b : s) :
  Equiv.Set.insert H ⟨b, Or.inr b.2⟩ = Sum.inl b :=
  (Equiv.Set.insert H).apply_eq_iff_eq_symm_apply.2 rfl

/-- If `s : set α` is a set with decidable membership, then `s ⊕ sᶜ` is equivalent to `α`. -/
protected def sum_compl {α} (s : Set α) [DecidablePred (· ∈ s)] : Sum s («expr ᶜ» s : Set α) ≃ α :=
  calc Sum s («expr ᶜ» s : Set α) ≃ «expr↥ » (s ∪ «expr ᶜ» s) :=
    (Equiv.Set.union
        (by 
          simp [Set.ext_iff])).symm
      
    _ ≃ @univ α :=
    Equiv.Set.ofEq
      (by 
        simp )
    _ ≃ α := Equiv.Set.univ _
    

@[simp]
theorem sum_compl_apply_inl {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : s) :
  Equiv.Set.sumCompl s (Sum.inl x) = x :=
  rfl

@[simp]
theorem sum_compl_apply_inr {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : «expr ᶜ» s) :
  Equiv.Set.sumCompl s (Sum.inr x) = x :=
  rfl

theorem sum_compl_symm_apply_of_mem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α} (hx : x ∈ s) :
  (Equiv.Set.sumCompl s).symm x = Sum.inl ⟨x, hx⟩ :=
  have  : «expr↑ » (⟨x, Or.inl hx⟩ : (s ∪ «expr ᶜ» s : Set α)) ∈ s := hx 
  by 
    rw [Equiv.Set.sumCompl]
    simpa using set.union_apply_left _ this

theorem sum_compl_symm_apply_of_not_mem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α} (hx : x ∉ s) :
  (Equiv.Set.sumCompl s).symm x = Sum.inr ⟨x, hx⟩ :=
  have  : «expr↑ » (⟨x, Or.inr hx⟩ : (s ∪ «expr ᶜ» s : Set α)) ∈ «expr ᶜ» s := hx 
  by 
    rw [Equiv.Set.sumCompl]
    simpa using set.union_apply_right _ this

@[simp]
theorem sum_compl_symm_apply {α : Type _} {s : Set α} [DecidablePred (· ∈ s)] {x : s} :
  (Equiv.Set.sumCompl s).symm x = Sum.inl x :=
  by 
    cases' x with x hx <;> exact set.sum_compl_symm_apply_of_mem hx

@[simp]
theorem sum_compl_symm_apply_compl {α : Type _} {s : Set α} [DecidablePred (· ∈ s)] {x : «expr ᶜ» s} :
  (Equiv.Set.sumCompl s).symm x = Sum.inr x :=
  by 
    cases' x with x hx <;> exact set.sum_compl_symm_apply_of_not_mem hx

/-- `sum_diff_subset s t` is the natural equivalence between
`s ⊕ (t \ s)` and `t`, where `s` and `t` are two sets. -/
protected def sum_diff_subset {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)] : Sum s (t \ s : Set α) ≃ t :=
  calc Sum s (t \ s : Set α) ≃ (s ∪ t \ s : Set α) :=
    (Equiv.Set.union
        (by 
          simp [inter_diff_self])).symm
      
    _ ≃ t :=
    Equiv.Set.ofEq
      (by 
        simp [union_diff_self, union_eq_self_of_subset_left h])
    

@[simp]
theorem sum_diff_subset_apply_inl {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)] (x : s) :
  Equiv.Set.sumDiffSubset h (Sum.inl x) = inclusion h x :=
  rfl

@[simp]
theorem sum_diff_subset_apply_inr {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)] (x : t \ s) :
  Equiv.Set.sumDiffSubset h (Sum.inr x) = inclusion (diff_subset t s) x :=
  rfl

theorem sum_diff_subset_symm_apply_of_mem {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)] {x : t} (hx : x.1 ∈ s) :
  (Equiv.Set.sumDiffSubset h).symm x = Sum.inl ⟨x, hx⟩ :=
  by 
    apply (Equiv.Set.sumDiffSubset h).Injective 
    simp only [apply_symm_apply, sum_diff_subset_apply_inl]
    exact Subtype.eq rfl

theorem sum_diff_subset_symm_apply_of_not_mem {α} {s t : Set α} (h : s ⊆ t) [DecidablePred (· ∈ s)] {x : t}
  (hx : x.1 ∉ s) : (Equiv.Set.sumDiffSubset h).symm x = Sum.inr ⟨x, ⟨x.2, hx⟩⟩ :=
  by 
    apply (Equiv.Set.sumDiffSubset h).Injective 
    simp only [apply_symm_apply, sum_diff_subset_apply_inr]
    exact Subtype.eq rfl

/-- If `s` is a set with decidable membership, then the sum of `s ∪ t` and `s ∩ t` is equivalent
to `s ⊕ t`. -/
protected def union_sum_inter {α : Type u} (s t : Set α) [DecidablePred (· ∈ s)] :
  Sum (s ∪ t : Set α) (s ∩ t : Set α) ≃ Sum s t :=
  calc Sum (s ∪ t : Set α) (s ∩ t : Set α) ≃ Sum (s ∪ t \ s : Set α) (s ∩ t : Set α) :=
    by 
      rw [union_diff_self]
    _ ≃ Sum (Sum s (t \ s : Set α)) (s ∩ t : Set α) :=
    sum_congr (Set.Union$ subset_empty_iff.2 (inter_diff_self _ _)) (Equiv.refl _)
    _ ≃ Sum s (Sum (t \ s : Set α) (s ∩ t : Set α)) := sum_assoc _ _ _ 
    _ ≃ Sum s (t \ s ∪ s ∩ t : Set α) :=
    sum_congr (Equiv.refl _)
      (by 
        refine' (set.union' (· ∉ s) _ _).symm 
        exacts[fun x hx => hx.2, fun x hx => not_not_intro hx.1])
    _ ≃ Sum s t :=
    by 
      rw [(_ : t \ s ∪ s ∩ t = t)]
      rw [union_comm, inter_comm, inter_union_diff]
    

/-- Given an equivalence `e₀` between sets `s : set α` and `t : set β`, the set of equivalences
`e : α ≃ β` such that `e ↑x = ↑(e₀ x)` for each `x : s` is equivalent to the set of equivalences
between `sᶜ` and `tᶜ`. -/
protected def compl {α : Type u} {β : Type v} {s : Set α} {t : Set β} [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
  (e₀ : s ≃ t) : { e : α ≃ β // ∀ x : s, e x = e₀ x } ≃ ((«expr ᶜ» s : Set α) ≃ («expr ᶜ» t : Set β)) :=
  { toFun :=
      fun e =>
        subtype_equiv e
          fun a =>
            not_congr$
              Iff.symm$
                maps_to.mem_iff (maps_to_iff_exists_map_subtype.2 ⟨e₀, e.2⟩)
                  (surj_on.maps_to_compl (surj_on_iff_exists_map_subtype.2 ⟨t, e₀, subset.refl t, e₀.surjective, e.2⟩)
                    e.1.Injective),
    invFun :=
      fun e₁ =>
        Subtype.mk
          (calc α ≃ Sum s («expr ᶜ» s : Set α) := (set.sum_compl s).symm 
            _ ≃ Sum t («expr ᶜ» t : Set β) := e₀.sum_congr e₁ 
            _ ≃ β := set.sum_compl t
            )
          fun x =>
            by 
              simp only [Sum.map_inl, trans_apply, sum_congr_apply, set.sum_compl_apply_inl, set.sum_compl_symm_apply],
    left_inv :=
      fun e =>
        by 
          ext x 
          byCases' hx : x ∈ s
          ·
            simp only [set.sum_compl_symm_apply_of_mem hx, ←e.prop ⟨x, hx⟩, Sum.map_inl, sum_congr_apply, trans_apply,
              Subtype.coe_mk, set.sum_compl_apply_inl]
          ·
            simp only [set.sum_compl_symm_apply_of_not_mem hx, Sum.map_inr, subtype_equiv_apply,
              set.sum_compl_apply_inr, trans_apply, sum_congr_apply, Subtype.coe_mk],
    right_inv :=
      fun e =>
        Equiv.ext$
          fun x =>
            by 
              simp only [Sum.map_inr, subtype_equiv_apply, set.sum_compl_apply_inr, Function.comp_app, sum_congr_apply,
                Equiv.coe_trans, Subtype.coe_eta, Subtype.coe_mk, set.sum_compl_symm_apply_compl] }

/-- The set product of two sets is equivalent to the type product of their coercions to types. -/
protected def Prod {α β} (s : Set α) (t : Set β) : s.prod t ≃ s × t :=
  @subtype_prod_equiv_prod α β s t

/-- If a function `f` is injective on a set `s`, then `s` is equivalent to `f '' s`. -/
protected noncomputable def image_of_inj_on {α β} (f : α → β) (s : Set α) (H : inj_on f s) : s ≃ f '' s :=
  ⟨fun p => ⟨f p, mem_image_of_mem f p.2⟩, fun p => ⟨Classical.some p.2, (Classical.some_spec p.2).1⟩,
    fun ⟨x, h⟩ =>
      Subtype.eq (H (Classical.some_spec (mem_image_of_mem f h)).1 h (Classical.some_spec (mem_image_of_mem f h)).2),
    fun ⟨y, h⟩ => Subtype.eq (Classical.some_spec h).2⟩

/-- If `f` is an injective function, then `s` is equivalent to `f '' s`. -/
@[simps apply]
protected noncomputable def image {α β} (f : α → β) (s : Set α) (H : injective f) : s ≃ f '' s :=
  Equiv.Set.imageOfInjOn f s (H.inj_on s)

@[simp]
protected theorem image_symm_apply {α β} (f : α → β) (s : Set α) (H : injective f) (x : α) (h : x ∈ s) :
  (Set.Image f s H).symm ⟨f x, ⟨x, ⟨h, rfl⟩⟩⟩ = ⟨x, h⟩ :=
  by 
    apply (Set.Image f s H).Injective 
    simp [(Set.Image f s H).apply_symm_apply]

-- error in Data.Equiv.Set: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem image_symm_preimage
{α β}
{f : α → β}
(hf : injective f)
(u
 s : set α) : «expr = »(«expr ⁻¹' »((λ
  x, (set.image f s hf).symm x : «expr '' »(f, s) → α), u), «expr ⁻¹' »(coe, «expr '' »(f, u))) :=
begin
  ext [] ["⟨", ident b, ",", ident a, ",", ident has, ",", ident rfl, "⟩"] [],
  have [] [":", expr ∀
   h : «expr∃ , »((a'), «expr ∧ »(«expr ∈ »(a', s), «expr = »(a', a))), «expr = »(classical.some h, a)] [":=", expr λ
   h, (classical.some_spec h).2],
  simp [] [] [] ["[", expr equiv.set.image, ",", expr equiv.set.image_of_inj_on, ",", expr hf.eq_iff, ",", expr this, "]"] [] []
end

/-- If `α` is equivalent to `β`, then `set α` is equivalent to `set β`. -/
@[simps]
protected def congr {α β : Type _} (e : α ≃ β) : Set α ≃ Set β :=
  ⟨fun s => e '' s, fun t => e.symm '' t, symm_image_image e, symm_image_image e.symm⟩

/-- The set `{x ∈ s | t x}` is equivalent to the set of `x : s` such that `t x`. -/
protected def sep {α : Type u} (s : Set α) (t : α → Prop) : ({ x∈s | t x } : Set α) ≃ { x:s | t x } :=
  (Equiv.subtypeSubtypeEquivSubtypeInter s t).symm

/-- The set `𝒫 S := {x | x ⊆ S}` is equivalent to the type `set S`. -/
protected def powerset {α} (S : Set α) : 𝒫 S ≃ Set S :=
  { toFun := fun x : 𝒫 S => coeₓ ⁻¹' (x : Set α),
    invFun :=
      fun x : Set S =>
        ⟨coeₓ '' x,
          by 
            rintro _ ⟨a : S, _, rfl⟩ <;> exact a.2⟩,
    left_inv :=
      fun x =>
        by 
          ext y <;> exact ⟨fun ⟨⟨_, _⟩, h, rfl⟩ => h, fun h => ⟨⟨_, x.2 h⟩, h, rfl⟩⟩,
    right_inv :=
      fun x =>
        by 
          ext <;> simp  }

/--
If `s` is a set in `range f`,
then its image under `range_splitting f` is in bijection (via `f`) with `s`.
-/
@[simps]
noncomputable def range_splitting_image_equiv {α β : Type _} (f : α → β) (s : Set (range f)) :
  range_splitting f '' s ≃ s :=
  { toFun :=
      fun x =>
        ⟨⟨f x,
            by 
              simp ⟩,
          by 
            rcases x with ⟨x, ⟨y, ⟨m, rfl⟩⟩⟩
            simpa [apply_range_splitting f] using m⟩,
    invFun := fun x => ⟨range_splitting f x, ⟨x, ⟨x.2, rfl⟩⟩⟩,
    left_inv :=
      fun x =>
        by 
          rcases x with ⟨x, ⟨y, ⟨m, rfl⟩⟩⟩
          simp [apply_range_splitting f],
    right_inv :=
      fun x =>
        by 
          simp [apply_range_splitting f] }

end Set

/-- If `f : α → β` has a left-inverse when `α` is nonempty, then `α` is computably equivalent to the
range of `f`.

While awkward, the `nonempty α` hypothesis on `f_inv` and `hf` allows this to be used when `α` is
empty too. This hypothesis is absent on analogous definitions on stronger `equiv`s like
`linear_equiv.of_left_inverse` and `ring_equiv.of_left_inverse` as their typeclass assumptions
are already sufficient to ensure non-emptiness. -/
@[simps]
def of_left_inverse {α β : Sort _} (f : α → β) (f_inv : Nonempty α → β → α)
  (hf : ∀ h : Nonempty α, left_inverse (f_inv h) f) : α ≃ Set.Range f :=
  { toFun := fun a => ⟨f a, a, rfl⟩, invFun := fun b => f_inv (nonempty_of_exists b.2) b, left_inv := fun a => hf ⟨a⟩ a,
    right_inv :=
      fun ⟨b, a, ha⟩ =>
        Subtype.eq$
          show f (f_inv ⟨a⟩ b) = b from
            Eq.trans
              (congr_argₓ f$
                by 
                  exact ha ▸ hf _ a)
              ha }

/-- If `f : α → β` has a left-inverse, then `α` is computably equivalent to the range of `f`.

Note that if `α` is empty, no such `f_inv` exists and so this definition can't be used, unlike
the stronger but less convenient `of_left_inverse`. -/
abbrev of_left_inverse' {α β : Sort _} (f : α → β) (f_inv : β → α) (hf : left_inverse f_inv f) : α ≃ Set.Range f :=
  of_left_inverse f (fun _ => f_inv) fun _ => hf

/-- If `f : α → β` is an injective function, then domain `α` is equivalent to the range of `f`. -/
@[simps apply]
noncomputable def of_injective {α β} (f : α → β) (hf : injective f) : α ≃ Set.Range f :=
  Equiv.ofLeftInverse f
    (fun h =>
      by 
        exact Function.invFun f)
    fun h =>
      by 
        exact Function.left_inverse_inv_fun hf

theorem apply_of_injective_symm {α β} (f : α → β) (hf : injective f) (b : Set.Range f) :
  f ((of_injective f hf).symm b) = b :=
  Subtype.ext_iff.1$ (of_injective f hf).apply_symm_apply b

@[simp]
theorem of_injective_symm_apply {α β} (f : α → β) (hf : injective f) (a : α) :
  (of_injective f hf).symm ⟨f a, ⟨a, rfl⟩⟩ = a :=
  by 
    apply (of_injective f hf).Injective 
    simp [apply_of_injective_symm f hf]

theorem coe_of_injective_symm {α β} (f : α → β) (hf : injective f) :
  ((of_injective f hf).symm : range f → α) = range_splitting f :=
  by 
    ext ⟨y, x, rfl⟩
    apply hf 
    simp [apply_range_splitting f]

@[simp]
theorem self_comp_of_injective_symm {α β} (f : α → β) (hf : injective f) : f ∘ (of_injective f hf).symm = coeₓ :=
  funext fun x => apply_of_injective_symm f hf x

-- error in Data.Equiv.Set: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem of_left_inverse_eq_of_injective
{α β : Type*}
(f : α → β)
(f_inv : nonempty α → β → α)
(hf : ∀
 h : nonempty α, left_inverse (f_inv h) f) : «expr = »(of_left_inverse f f_inv hf, of_injective f ((em (nonempty α)).elim (λ
   h, (hf h).injective) (λ
   h _ _ _, by { haveI [] [":", expr subsingleton α] [":=", expr subsingleton_of_not_nonempty h],
     simp [] [] [] [] [] [] }))) :=
by { ext [] [] [],
  simp [] [] [] [] [] [] }

theorem of_left_inverse'_eq_of_injective {α β : Type _} (f : α → β) (f_inv : β → α) (hf : left_inverse f_inv f) :
  of_left_inverse' f f_inv hf = of_injective f hf.injective :=
  by 
    ext 
    simp 

protected theorem set_forall_iff {α β} (e : α ≃ β) {p : Set α → Prop} : (∀ a, p a) ↔ ∀ a, p (e ⁻¹' a) :=
  by 
    simpa [Equiv.image_eq_preimage] using (Equiv.Set.congr e).forall_congr_left'

protected theorem preimage_sUnion {α β} (f : α ≃ β) {s : Set (Set β)} : f ⁻¹' ⋃₀s = ⋃₀(_root_.set.image f ⁻¹' s) :=
  by 
    ext x 
    simp [(Equiv.Set.congr f).symm.exists_congr_left]

end Equiv

/-- If a function is a bijection between two sets `s` and `t`, then it induces an
equivalence between the types `↥s` and ``↥t`. -/
noncomputable def Set.BijOn.equiv {α : Type _} {β : Type _} {s : Set α} {t : Set β} (f : α → β) (h : Set.BijOn f s t) :
  s ≃ t :=
  Equiv.ofBijective _ h.bijective

-- error in Data.Equiv.Set: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The composition of an updated function with an equiv on a subset can be expressed as an
updated function. -/
theorem dite_comp_equiv_update
{α : Type*}
{β : Sort*}
{γ : Sort*}
{s : set α}
(e : «expr ≃ »(β, s))
(v : β → γ)
(w : α → γ)
(j : β)
(x : γ)
[decidable_eq β]
[decidable_eq α]
[∀
 j, decidable «expr ∈ »(j, s)] : «expr = »(λ
 i : α, if h : «expr ∈ »(i, s) then function.update v j x (e.symm ⟨i, h⟩) else w i, function.update (λ
  i : α, if h : «expr ∈ »(i, s) then v (e.symm ⟨i, h⟩) else w i) (e j) x) :=
begin
  ext [] [ident i] [],
  by_cases [expr h, ":", expr «expr ∈ »(i, s)],
  { rw ["[", expr dif_pos h, ",", expr function.update_apply_equiv_apply, ",", expr equiv.symm_symm, ",", expr function.comp, ",", expr function.update_apply, ",", expr function.update_apply, ",", expr dif_pos h, "]"] [],
    have [ident h_coe] [":", expr «expr ↔ »(«expr = »((⟨i, h⟩ : s), e j), «expr = »(i, e j))] [":=", expr subtype.ext_iff.trans (by rw [expr subtype.coe_mk] [])],
    simp_rw [expr h_coe] [],
    congr },
  { have [] [":", expr «expr ≠ »(i, e j)] [],
    by { contrapose ["!"] [ident h],
      have [] [":", expr «expr ∈ »((e j : α), s)] [":=", expr (e j).2],
      rwa ["<-", expr h] ["at", ident this] },
    simp [] [] [] ["[", expr h, ",", expr this, "]"] [] [] }
end

