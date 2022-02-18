import Mathbin.Algebra.Algebra.Tower
import Mathbin.LinearAlgebra.Prod
import Mathbin.LinearAlgebra.Finsupp

/-!
# Adjoining elements to form subalgebras

This file develops the basic theory of subalgebras of an R-algebra generated
by a set of elements. A basic interface for `adjoin` is set up.

## Tags

adjoin, algebra

-/


universe u v w

open_locale Pointwise

open Submodule Subsemiring

variable {R : Type u} {A : Type v} {B : Type w}

namespace Algebra

section Semiringₓ

variable [CommSemiringₓ R] [Semiringₓ A] [Semiringₓ B]

variable [Algebra R A] [Algebra R B] {s t : Set A}

theorem subset_adjoin : s ⊆ adjoin R s :=
  Algebra.gc.le_u_l s

theorem adjoin_le {S : Subalgebra R A} (H : s ⊆ S) : adjoin R s ≤ S :=
  Algebra.gc.l_le H

theorem adjoin_eq_Inf : adjoin R s = inf { p | s ⊆ p } :=
  le_antisymmₓ (le_Inf fun _ h => adjoin_le h) (Inf_le subset_adjoin)

theorem adjoin_le_iff {S : Subalgebra R A} : adjoin R s ≤ S ↔ s ⊆ S :=
  Algebra.gc _ _

theorem adjoin_mono (H : s ⊆ t) : adjoin R s ≤ adjoin R t :=
  Algebra.gc.monotone_l H

theorem adjoin_eq_of_le (S : Subalgebra R A) (h₁ : s ⊆ S) (h₂ : S ≤ adjoin R s) : adjoin R s = S :=
  le_antisymmₓ (adjoin_le h₁) h₂

theorem adjoin_eq (S : Subalgebra R A) : adjoin R ↑S = S :=
  adjoin_eq_of_le _ (Set.Subset.refl _) subset_adjoin

theorem adjoin_Union {α : Type _} (s : α → Set A) : adjoin R (Set.Unionₓ s) = ⨆ i : α, adjoin R (s i) :=
  (@Algebra.gc R A _ _ _).l_supr

theorem adjoin_attach_bUnion [DecidableEq A] {α : Type _} {s : Finset α} (f : s → Finset A) :
    adjoin R (s.attach.bUnion f : Set A) = ⨆ x, adjoin R (f x) := by
  simpa [adjoin_Union]

@[elab_as_eliminator]
theorem adjoin_induction {p : A → Prop} {x : A} (h : x ∈ adjoin R s) (Hs : ∀, ∀ x ∈ s, ∀, p x)
    (Halg : ∀ r, p (algebraMap R A r)) (Hadd : ∀ x y, p x → p y → p (x + y)) (Hmul : ∀ x y, p x → p y → p (x * y)) :
    p x :=
  let S : Subalgebra R A := { Carrier := p, mul_mem' := Hmul, add_mem' := Hadd, algebra_map_mem' := Halg }
  adjoin_le (show s ≤ S from Hs) h

/-- The difference with `algebra.adjoin_induction` is that this acts on the subtype. -/
theorem adjoin_induction' {p : adjoin R s → Prop} (Hs : ∀ x h : x ∈ s, p ⟨x, subset_adjoin h⟩)
    (Halg : ∀ r, p (algebraMap R _ r)) (Hadd : ∀ x y, p x → p y → p (x + y)) (Hmul : ∀ x y, p x → p y → p (x * y))
    (x : adjoin R s) : p x :=
  (Subtype.recOn x) fun x hx => by
    refine' Exists.elim _ fun hx : x ∈ adjoin R s hc : p ⟨x, hx⟩ => hc
    exact
      adjoin_induction hx (fun x hx => ⟨subset_adjoin hx, Hs x hx⟩) (fun r => ⟨Subalgebra.algebra_map_mem _ r, Halg r⟩)
        (fun x y hx hy =>
          (Exists.elim hx) fun hx' hx => (Exists.elim hy) fun hy' hy => ⟨Subalgebra.add_mem _ hx' hy', Hadd _ _ hx hy⟩)
        fun x y hx hy =>
        (Exists.elim hx) fun hx' hx => (Exists.elim hy) fun hy' hy => ⟨Subalgebra.mul_mem _ hx' hy', Hmul _ _ hx hy⟩

@[simp]
theorem adjoin_adjoin_coe_preimage {s : Set A} : adjoin R ((coe : adjoin R s → A) ⁻¹' s) = ⊤ := by
  refine' eq_top_iff.2 fun x => adjoin_induction' (fun a ha => _) (fun r => _) (fun _ _ => _) (fun _ _ => _) x
  · exact subset_adjoin ha
    
  · exact Subalgebra.algebra_map_mem _ r
    
  · exact Subalgebra.add_mem _
    
  · exact Subalgebra.mul_mem _
    

theorem adjoin_union (s t : Set A) : adjoin R (s ∪ t) = adjoin R s⊔adjoin R t :=
  (Algebra.gc : GaloisConnection _ (coe : Subalgebra R A → Set A)).l_sup

variable (R A)

@[simp]
theorem adjoin_empty : adjoin R (∅ : Set A) = ⊥ :=
  show adjoin R ⊥ = ⊥ by
    apply GaloisConnection.l_bot
    exact Algebra.gc

@[simp]
theorem adjoin_univ : adjoin R (Set.Univ : Set A) = ⊤ :=
  eq_top_iff.2 fun x => subset_adjoin <| Set.mem_univ _

variable (R) {A} (s)

theorem adjoin_eq_span : (adjoin R s).toSubmodule = span R (Submonoid.closure s) := by
  apply le_antisymmₓ
  · intro r hr
    rcases Subsemiring.mem_closure_iff_exists_list.1 hr with ⟨L, HL, rfl⟩
    clear hr
    induction' L with hd tl ih
    · exact zero_mem _
      
    rw [List.forall_mem_consₓ] at HL
    rw [List.map_cons, List.sum_cons]
    refine' Submodule.add_mem _ _ (ih HL.2)
    replace HL := HL.1
    clear ih tl
    suffices ∃ (z r : _)(hr : r ∈ Submonoid.closure s), HasScalar.smul z r = List.prod hd by
      rcases this with ⟨z, r, hr, hzr⟩
      rw [← hzr]
      exact smul_mem _ _ (subset_span hr)
    induction' hd with hd tl ih
    · exact ⟨1, 1, (Submonoid.closure s).one_mem', one_smul _ _⟩
      
    rw [List.forall_mem_consₓ] at HL
    rcases ih HL.2 with ⟨z, r, hr, hzr⟩
    rw [List.prod_cons, ← hzr]
    rcases HL.1 with (⟨hd, rfl⟩ | hs)
    · refine' ⟨hd * z, r, hr, _⟩
      rw [Algebra.smul_def, Algebra.smul_def, (algebraMap _ _).map_mul, _root_.mul_assoc]
      
    · exact ⟨z, hd * r, Submonoid.mul_mem _ (Submonoid.subset_closure hs) hr, (mul_smul_comm _ _ _).symm⟩
      
    
  refine' span_le.2 _
  change Submonoid.closure s ≤ (adjoin R s).toSubsemiring.toSubmonoid
  exact Submonoid.closure_le.2 subset_adjoin

theorem span_le_adjoin (s : Set A) : span R s ≤ (adjoin R s).toSubmodule :=
  span_le.mpr subset_adjoin

theorem adjoin_to_submodule_le {s : Set A} {t : Submodule R A} :
    (adjoin R s).toSubmodule ≤ t ↔ ↑(Submonoid.closure s) ⊆ (t : Set A) := by
  rw [adjoin_eq_span, span_le]

theorem adjoin_eq_span_of_subset {s : Set A} (hs : ↑(Submonoid.closure s) ⊆ (span R s : Set A)) :
    (adjoin R s).toSubmodule = span R s :=
  le_antisymmₓ ((adjoin_to_submodule_le R).mpr hs) (span_le_adjoin R s)

theorem adjoin_image (f : A →ₐ[R] B) (s : Set A) : adjoin R (f '' s) = (adjoin R s).map f :=
  le_antisymmₓ (adjoin_le <| Set.image_subset _ subset_adjoin) <|
    Subalgebra.map_le.2 <| adjoin_le <| Set.image_subset_iff.1 subset_adjoin

@[simp]
theorem adjoin_insert_adjoin (x : A) : adjoin R (insert x ↑(adjoin R s)) = adjoin R (insert x s) :=
  le_antisymmₓ
    (adjoin_le (Set.insert_subset.mpr ⟨subset_adjoin (Set.mem_insert _ _), adjoin_mono (Set.subset_insert _ _)⟩))
    (Algebra.adjoin_mono (Set.insert_subset_insert Algebra.subset_adjoin))

theorem adjoin_prod_le (s : Set A) (t : Set B) : adjoin R (s ×ˢ t) ≤ (adjoin R s).Prod (adjoin R t) :=
  adjoin_le <| Set.prod_mono subset_adjoin subset_adjoin

theorem mem_adjoin_of_map_mul {s} {x : A} {f : A →ₗ[R] B} (hf : ∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂)
    (h : x ∈ adjoin R s) : f x ∈ adjoin R (f '' (s ∪ {1})) := by
  refine'
    @adjoin_induction R A _ _ _ _ (fun a => f a ∈ adjoin R (f '' (s ∪ {1}))) x h
      (fun a ha => subset_adjoin ⟨a, ⟨Set.subset_union_left _ _ ha, rfl⟩⟩) (fun r => _)
      (fun y z hy hz => by
        simpa [hy, hz] using Subalgebra.add_mem _ hy hz)
      fun y z hy hz => by
      simpa [hy, hz, hf y z] using Subalgebra.mul_mem _ hy hz
  have : f 1 ∈ adjoin R (f '' (s ∪ {1})) := subset_adjoin ⟨1, ⟨Set.subset_union_right _ _ <| Set.mem_singleton 1, rfl⟩⟩
  replace this := Subalgebra.smul_mem (adjoin R (f '' (s ∪ {1}))) this r
  convert this
  rw [algebra_map_eq_smul_one]
  exact f.map_smul _ _

theorem adjoin_inl_union_inr_eq_prod s t :
    adjoin R (LinearMap.inl R A B '' (s ∪ {1}) ∪ LinearMap.inr R A B '' (t ∪ {1})) = (adjoin R s).Prod (adjoin R t) :=
  by
  apply le_antisymmₓ
  · simp only [adjoin_le_iff, Set.insert_subset, Subalgebra.zero_mem, Subalgebra.one_mem, subset_adjoin,
      Set.union_subset_iff, LinearMap.coe_inl, Set.mk_preimage_prod_right, Set.image_subset_iff, SetLike.mem_coe,
      Set.mk_preimage_prod_left, LinearMap.coe_inr, and_selfₓ, Set.union_singleton, Subalgebra.coe_prod]
    
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    let P := adjoin R (LinearMap.inl R A B '' (s ∪ {1}) ∪ LinearMap.inr R A B '' (t ∪ {1}))
    have Ha : (a, (0 : B)) ∈ adjoin R (LinearMap.inl R A B '' (s ∪ {1})) :=
      mem_adjoin_of_map_mul R LinearMap.inl_map_mul ha
    have Hb : ((0 : A), b) ∈ adjoin R (LinearMap.inr R A B '' (t ∪ {1})) :=
      mem_adjoin_of_map_mul R LinearMap.inr_map_mul hb
    replace Ha : (a, (0 : B)) ∈ P := adjoin_mono (Set.subset_union_left _ _) Ha
    replace Hb : ((0 : A), b) ∈ P := adjoin_mono (Set.subset_union_right _ _) Hb
    simpa using Subalgebra.add_mem _ Ha Hb
    

end Semiringₓ

section CommSemiringₓ

variable [CommSemiringₓ R] [CommSemiringₓ A]

variable [Algebra R A] {s t : Set A}

variable (R s t)

theorem adjoin_union_eq_adjoin_adjoin : adjoin R (s ∪ t) = (adjoin (adjoin R s) t).restrictScalars R :=
  le_antisymmₓ
    (closure_mono <|
      Set.union_subset (Set.range_subset_iff.2 fun r => Or.inl ⟨algebraMap R (adjoin R s) r, rfl⟩)
        ((Set.union_subset_union_left _) fun x hxs => ⟨⟨_, subset_adjoin hxs⟩, rfl⟩))
    (closure_le.2 <|
      Set.union_subset (Set.range_subset_iff.2 fun x => adjoin_mono (Set.subset_union_left _ _) x.2)
        (Set.Subset.trans (Set.subset_union_right _ _) subset_adjoin))

theorem adjoin_singleton_one : adjoin R ({1} : Set A) = ⊥ :=
  eq_bot_iff.2 <| adjoin_le <| Set.singleton_subset_iff.2 <| SetLike.mem_coe.2 <| one_mem _

theorem adjoin_union_coe_submodule :
    (adjoin R (s ∪ t)).toSubmodule = (adjoin R s).toSubmodule * (adjoin R t).toSubmodule := by
  rw [adjoin_eq_span, adjoin_eq_span, adjoin_eq_span, span_mul_span]
  congr 1 with z
  simp [Submonoid.closure_union, Submonoid.mem_sup, Set.mem_mul]

theorem pow_smul_mem_adjoin_smul (r : R) (s : Set A) {x : A} (hx : x ∈ adjoin R s) :
    ∃ n₀ : ℕ, ∀, ∀ n ≥ n₀, ∀, r ^ n • x ∈ adjoin R (r • s) := by
  change x ∈ (adjoin R s).toSubmodule at hx
  rw [adjoin_eq_span, Finsupp.mem_span_iff_total] at hx
  rcases hx with ⟨l, rfl : (l.sum fun i : Submonoid.closure s c : R => c • ↑i) = x⟩
  choose n₁ n₂ using fun x : Submonoid.closure s => Submonoid.pow_smul_mem_closure_smul r s x.Prop
  use l.support.sup n₁
  intro n hn
  rw [Finsupp.smul_sum]
  refine' (adjoin R (r • s)).toSubmodule.sum_mem _
  intro a ha
  have : n ≥ n₁ a := le_transₓ (Finset.le_sup ha) hn
  dsimp only
  rw [← tsub_add_cancel_of_le this, pow_addₓ, ← smul_smul, smul_smul _ (l a), mul_comm, ← smul_smul, adjoin_eq_span]
  refine' Submodule.smul_mem _ _ _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (n₂ a))

end CommSemiringₓ

section Ringₓ

variable [CommRingₓ R] [Ringₓ A]

variable [Algebra R A] {s t : Set A}

variable {R s t}

theorem adjoin_int (s : Set R) : adjoin ℤ s = subalgebraOfSubring (Subring.closure s) :=
  le_antisymmₓ (adjoin_le Subring.subset_closure)
    (Subring.closure_le.2 subset_adjoin : Subring.closure s ≤ (adjoin ℤ s).toSubring)

theorem mem_adjoin_iff {s : Set A} {x : A} : x ∈ adjoin R s ↔ x ∈ Subring.closure (Set.Range (algebraMap R A) ∪ s) :=
  ⟨fun hx =>
    Subsemiring.closure_induction hx Subring.subset_closure (Subring.zero_mem _) (Subring.one_mem _)
      (fun _ _ => Subring.add_mem _) fun _ _ => Subring.mul_mem _,
    suffices Subring.closure (Set.Range (⇑algebraMap R A) ∪ s) ≤ (adjoin R s).toSubring from @this x
    Subring.closure_le.2 Subsemiring.subset_closure⟩

theorem adjoin_eq_ring_closure (s : Set A) :
    (adjoin R s).toSubring = Subring.closure (Set.Range (algebraMap R A) ∪ s) :=
  Subring.ext fun x => mem_adjoin_iff

end Ringₓ

end Algebra

open Algebra Subalgebra

namespace AlgHom

variable [CommSemiringₓ R] [Semiringₓ A] [Semiringₓ B] [Algebra R A] [Algebra R B]

theorem map_adjoin (φ : A →ₐ[R] B) (s : Set A) : (adjoin R s).map φ = adjoin R (φ '' s) :=
  (adjoin_image _ _ _).symm

theorem adjoin_le_equalizer (φ₁ φ₂ : A →ₐ[R] B) {s : Set A} (h : s.EqOn φ₁ φ₂) : adjoin R s ≤ φ₁.equalizer φ₂ :=
  adjoin_le h

theorem ext_of_adjoin_eq_top {s : Set A} (h : adjoin R s = ⊤) ⦃φ₁ φ₂ : A →ₐ[R] B⦄ (hs : s.EqOn φ₁ φ₂) : φ₁ = φ₂ :=
  ext fun x => adjoin_le_equalizer φ₁ φ₂ hs <| h.symm ▸ trivialₓ

end AlgHom

