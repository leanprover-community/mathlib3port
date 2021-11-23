import Mathbin.Deprecated.Subgroup 
import Mathbin.Deprecated.Group 
import Mathbin.RingTheory.Subring

universe u v

open Groupₓ

variable{R : Type u}[Ringₓ R]

/-- `S` is a subring: a set containing 1 and closed under multiplication, addition and additive
inverse. -/
structure IsSubring(S : Set R) extends IsAddSubgroup S, IsSubmonoid S : Prop

/-- Construct a `subring` from a set satisfying `is_subring`. -/
def IsSubring.subring {S : Set R} (hs : IsSubring S) : Subring R :=
  { Carrier := S, one_mem' := hs.one_mem, mul_mem' := hs.mul_mem, zero_mem' := hs.zero_mem, add_mem' := hs.add_mem,
    neg_mem' := hs.neg_mem }

namespace RingHom

theorem is_subring_preimage {R : Type u} {S : Type v} [Ringₓ R] [Ringₓ S] (f : R →+* S) {s : Set S} (hs : IsSubring s) :
  IsSubring (f ⁻¹' s) :=
  { IsAddGroupHom.preimage f.to_is_add_group_hom hs.to_is_add_subgroup,
    IsSubmonoid.preimage f.to_is_monoid_hom hs.to_is_submonoid with  }

theorem is_subring_image {R : Type u} {S : Type v} [Ringₓ R] [Ringₓ S] (f : R →+* S) {s : Set R} (hs : IsSubring s) :
  IsSubring (f '' s) :=
  { IsAddGroupHom.image_add_subgroup f.to_is_add_group_hom hs.to_is_add_subgroup,
    IsSubmonoid.image f.to_is_monoid_hom hs.to_is_submonoid with  }

theorem is_subring_set_range {R : Type u} {S : Type v} [Ringₓ R] [Ringₓ S] (f : R →+* S) : IsSubring (Set.Range f) :=
  { IsAddGroupHom.range_add_subgroup f.to_is_add_group_hom, Range.is_submonoid f.to_is_monoid_hom with  }

end RingHom

variable{cR : Type u}[CommRingₓ cR]

theorem IsSubring.inter {S₁ S₂ : Set R} (hS₁ : IsSubring S₁) (hS₂ : IsSubring S₂) : IsSubring (S₁ ∩ S₂) :=
  { IsAddSubgroup.inter hS₁.to_is_add_subgroup hS₂.to_is_add_subgroup,
    IsSubmonoid.inter hS₁.to_is_submonoid hS₂.to_is_submonoid with  }

theorem IsSubring.Inter {ι : Sort _} {S : ι → Set R} (h : ∀ y : ι, IsSubring (S y)) : IsSubring (Set.Interₓ S) :=
  { IsAddSubgroup.Inter fun i => (h i).to_is_add_subgroup, IsSubmonoid.Inter fun i => (h i).to_is_submonoid with  }

theorem is_subring_Union_of_directed {ι : Type _} [hι : Nonempty ι] {s : ι → Set R} (h : ∀ i, IsSubring (s i))
  (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) : IsSubring (⋃i, s i) :=
  { to_is_add_subgroup := is_add_subgroup_Union_of_directed (fun i => (h i).to_is_add_subgroup) Directed,
    to_is_submonoid := is_submonoid_Union_of_directed (fun i => (h i).to_is_submonoid) Directed }

namespace Ringₓ

def closure (s : Set R) :=
  AddGroupₓ.Closure (Monoidₓ.Closure s)

variable{s : Set R}

attribute [local reducible] closure

theorem exists_list_of_mem_closure {a : R} (h : a ∈ closure s) :
  ∃ L : List (List R), (∀ l _ : l ∈ L, ∀ x _ : x ∈ l, x ∈ s ∨ x = (-1 : R)) ∧ (L.map List.prod).Sum = a :=
  AddGroupₓ.InClosure.rec_on h
    (fun x hx =>
      match x, Monoidₓ.exists_list_of_mem_closure hx with 
      | _, ⟨L, h1, rfl⟩ => ⟨[L], List.forall_mem_singleton.2 fun r hr => Or.inl (h1 r hr), zero_addₓ _⟩)
    ⟨[], List.forall_mem_nil _, rfl⟩
    (fun b _ ih =>
      match b, ih with 
      | _, ⟨L1, h1, rfl⟩ =>
        ⟨L1.map (List.cons (-1)),
          fun L2 h2 =>
            match L2, List.mem_mapₓ.1 h2 with 
            | _, ⟨L3, h3, rfl⟩ => List.forall_mem_consₓ.2 ⟨Or.inr rfl, h1 L3 h3⟩,
          by 
            simp only [List.map_mapₓ, · ∘ ·, List.prod_cons, neg_one_mul] <;>
              exact
                List.recOn L1 neg_zero.symm
                  fun hd tl ih =>
                    by 
                      rw [List.map_consₓ, List.sum_cons, ih, List.map_consₓ, List.sum_cons, neg_add]⟩)
    fun r1 r2 hr1 hr2 ih1 ih2 =>
      match r1, r2, ih1, ih2 with 
      | _, _, ⟨L1, h1, rfl⟩, ⟨L2, h2, rfl⟩ =>
        ⟨L1 ++ L2, List.forall_mem_appendₓ.2 ⟨h1, h2⟩,
          by 
            rw [List.map_append, List.sum_append]⟩

-- error in Deprecated.Subring: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[elab_as_eliminator]
protected
theorem in_closure.rec_on
{C : R → exprProp()}
{x : R}
(hx : «expr ∈ »(x, closure s))
(h1 : C 1)
(hneg1 : C «expr- »(1))
(hs : ∀ z «expr ∈ » s, ∀ n, C n → C «expr * »(z, n))
(ha : ∀ {x y}, C x → C y → C «expr + »(x, y)) : C x :=
begin
  have [ident h0] [":", expr C 0] [":=", expr «expr ▸ »(add_neg_self (1 : R), ha h1 hneg1)],
  rcases [expr exists_list_of_mem_closure hx, "with", "⟨", ident L, ",", ident HL, ",", ident rfl, "⟩"],
  clear [ident hx],
  induction [expr L] [] ["with", ident hd, ident tl, ident ih] [],
  { exact [expr h0] },
  rw [expr list.forall_mem_cons] ["at", ident HL],
  suffices [] [":", expr C (list.prod hd)],
  { rw ["[", expr list.map_cons, ",", expr list.sum_cons, "]"] [],
    exact [expr ha this (ih HL.2)] },
  replace [ident HL] [] [":=", expr HL.1],
  clear [ident ih, ident tl],
  suffices [] [":", expr «expr∃ , »((L : list R), «expr ∧ »(∀
     x «expr ∈ » L, «expr ∈ »(x, s), «expr ∨ »(«expr = »(list.prod hd, list.prod L), «expr = »(list.prod hd, «expr- »(list.prod L)))))],
  { rcases [expr this, "with", "⟨", ident L, ",", ident HL', ",", ident HP, "|", ident HP, "⟩"],
    { rw [expr HP] [],
      clear [ident HP, ident HL, ident hd],
      induction [expr L] [] ["with", ident hd, ident tl, ident ih] [],
      { exact [expr h1] },
      rw [expr list.forall_mem_cons] ["at", ident HL'],
      rw [expr list.prod_cons] [],
      exact [expr hs _ HL'.1 _ (ih HL'.2)] },
    rw [expr HP] [],
    clear [ident HP, ident HL, ident hd],
    induction [expr L] [] ["with", ident hd, ident tl, ident ih] [],
    { exact [expr hneg1] },
    rw ["[", expr list.prod_cons, ",", expr neg_mul_eq_mul_neg, "]"] [],
    rw [expr list.forall_mem_cons] ["at", ident HL'],
    exact [expr hs _ HL'.1 _ (ih HL'.2)] },
  induction [expr hd] [] ["with", ident hd, ident tl, ident ih] [],
  { exact [expr ⟨«expr[ , ]»([]), list.forall_mem_nil _, or.inl rfl⟩] },
  rw [expr list.forall_mem_cons] ["at", ident HL],
  rcases [expr ih HL.2, "with", "⟨", ident L, ",", ident HL', ",", ident HP, "|", ident HP, "⟩"]; cases [expr HL.1] ["with", ident hhd, ident hhd],
  { exact [expr ⟨[«expr :: »/«expr :: »/«expr :: »](hd, L), list.forall_mem_cons.2 ⟨hhd, HL'⟩, «expr $ »(or.inl, by rw ["[", expr list.prod_cons, ",", expr list.prod_cons, ",", expr HP, "]"] [])⟩] },
  { exact [expr ⟨L, HL', «expr $ »(or.inr, by rw ["[", expr list.prod_cons, ",", expr hhd, ",", expr neg_one_mul, ",", expr HP, "]"] [])⟩] },
  { exact [expr ⟨[«expr :: »/«expr :: »/«expr :: »](hd, L), list.forall_mem_cons.2 ⟨hhd, HL'⟩, «expr $ »(or.inr, by rw ["[", expr list.prod_cons, ",", expr list.prod_cons, ",", expr HP, ",", expr neg_mul_eq_mul_neg, "]"] [])⟩] },
  { exact [expr ⟨L, HL', «expr $ »(or.inl, by rw ["[", expr list.prod_cons, ",", expr hhd, ",", expr HP, ",", expr neg_one_mul, ",", expr neg_neg, "]"] [])⟩] }
end

theorem closure.is_subring : IsSubring (closure s) :=
  { AddGroupₓ.Closure.is_add_subgroup _ with
    one_mem := AddGroupₓ.mem_closure$ IsSubmonoid.one_mem$ Monoidₓ.Closure.is_submonoid _,
    mul_mem :=
      fun a b ha hb =>
        AddGroupₓ.InClosure.rec_on hb
          (fun c hc =>
            AddGroupₓ.InClosure.rec_on ha
              (fun d hd => AddGroupₓ.subset_closure ((Monoidₓ.Closure.is_submonoid _).mul_mem hd hc))
              ((zero_mul c).symm ▸ (AddGroupₓ.Closure.is_add_subgroup _).zero_mem)
              (fun d hd hdc => neg_mul_eq_neg_mul d c ▸ (AddGroupₓ.Closure.is_add_subgroup _).neg_mem hdc)
              fun d e hd he hdc hec => (add_mulₓ d e c).symm ▸ (AddGroupₓ.Closure.is_add_subgroup _).add_mem hdc hec)
          ((mul_zero a).symm ▸ (AddGroupₓ.Closure.is_add_subgroup _).zero_mem)
          (fun c hc hac => neg_mul_eq_mul_neg a c ▸ (AddGroupₓ.Closure.is_add_subgroup _).neg_mem hac)
          fun c d hc hd hac had => (mul_addₓ a c d).symm ▸ (AddGroupₓ.Closure.is_add_subgroup _).add_mem hac had }

theorem mem_closure {a : R} : a ∈ s → a ∈ closure s :=
  AddGroupₓ.mem_closure ∘ @Monoidₓ.subset_closure _ _ _ _

theorem subset_closure : s ⊆ closure s :=
  fun _ => mem_closure

theorem closure_subset {t : Set R} (ht : IsSubring t) : s ⊆ t → closure s ⊆ t :=
  AddGroupₓ.closure_subset ht.to_is_add_subgroup ∘ Monoidₓ.closure_subset ht.to_is_submonoid

theorem closure_subset_iff {s t : Set R} (ht : IsSubring t) : closure s ⊆ t ↔ s ⊆ t :=
  (AddGroupₓ.closure_subset_iff ht.to_is_add_subgroup).trans
    ⟨Set.Subset.trans Monoidₓ.subset_closure, Monoidₓ.closure_subset ht.to_is_submonoid⟩

theorem closure_mono {s t : Set R} (H : s ⊆ t) : closure s ⊆ closure t :=
  closure_subset closure.is_subring$ Set.Subset.trans H subset_closure

-- error in Deprecated.Subring: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
theorem image_closure
{S : Type*}
[ring S]
(f : «expr →+* »(R, S))
(s : set R) : «expr = »(«expr '' »(f, closure s), closure «expr '' »(f, s)) :=
le_antisymm (begin
   rintros ["_", "⟨", ident x, ",", ident hx, ",", ident rfl, "⟩"],
   apply [expr in_closure.rec_on hx]; intros [],
   { rw ["[", expr f.map_one, "]"] [],
     apply [expr closure.is_subring.to_is_submonoid.one_mem] },
   { rw ["[", expr f.map_neg, ",", expr f.map_one, "]"] [],
     apply [expr closure.is_subring.to_is_add_subgroup.neg_mem],
     apply [expr closure.is_subring.to_is_submonoid.one_mem] },
   { rw ["[", expr f.map_mul, "]"] [],
     apply [expr closure.is_subring.to_is_submonoid.mul_mem]; solve_by_elim [] [] ["[", expr subset_closure, ",", expr set.mem_image_of_mem, "]"] [] },
   { rw ["[", expr f.map_add, "]"] [],
     apply [expr closure.is_subring.to_is_add_submonoid.add_mem],
     assumption' }
 end) «expr $ »(closure_subset (ring_hom.is_subring_image _ closure.is_subring), set.image_subset _ subset_closure)

end Ringₓ

