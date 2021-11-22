import Mathbin.LinearAlgebra.Basic 
import Mathbin.LinearAlgebra.Prod 
import Mathbin.LinearAlgebra.Pi 
import Mathbin.Data.SetLike.Fintype 
import Mathbin.LinearAlgebra.LinearIndependent 
import Mathbin.Tactic.Linarith.Default 
import Mathbin.Algebra.Algebra.Basic 
import Mathbin.RingTheory.Noetherian 
import Mathbin.RingTheory.JacobsonIdeal 
import Mathbin.RingTheory.Nilpotent 
import Mathbin.RingTheory.Nakayama

/-!
# Artinian rings and modules


A module satisfying these equivalent conditions is said to be an *Artinian* R-module
if every decreasing chain of submodules is eventually constant, or equivalently,
if the relation `<` on submodules is well founded.

A ring is an *Artinian ring* if it is Artinian as a module over itself.

(Note that we do not assume yet that our rings are commutative,
so perhaps this should be called "left Artinian".
To avoid cumbersome names once we specialize to the commutative case,
we don't make this explicit in the declaration names.)

## Main definitions

Let `R` be a ring and let `M` and `P` be `R`-modules. Let `N` be an `R`-submodule of `M`.

* `is_artinian R M` is the proposition that `M` is a Artinian `R`-module. It is a class,
  implemented as the predicate that the `<` relation on submodules is well founded.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [samuel]

## Tags

Artinian, artinian, Artinian ring, Artinian module, artinian ring, artinian module

-/


open Set

open_locale BigOperators Pointwise

/--
`is_artinian R M` is the proposition that `M` is an Artinian `R`-module,
implemented as the well-foundedness of submodule inclusion.
-/
class IsArtinian(R M)[Semiringₓ R][AddCommMonoidₓ M][Module R M] : Prop where 
  well_founded_submodule_lt{} : WellFounded (· < · : Submodule R M → Submodule R M → Prop)

section 

variable{R : Type _}{M : Type _}{P : Type _}{N : Type _}

variable[Ringₓ R][AddCommGroupₓ M][AddCommGroupₓ P][AddCommGroupₓ N]

variable[Module R M][Module R P][Module R N]

open IsArtinian

include R

theorem is_artinian_of_injective (f : M →ₗ[R] P) (h : Function.Injective f) [IsArtinian R P] : IsArtinian R M :=
  ⟨Subrelation.wfₓ (fun A B hAB => show A.map f < B.map f from Submodule.map_strict_mono_of_injective h hAB)
      (InvImage.wfₓ (Submodule.map f) (IsArtinian.well_founded_submodule_lt R P))⟩

instance is_artinian_submodule' [IsArtinian R M] (N : Submodule R M) : IsArtinian R N :=
  is_artinian_of_injective N.subtype Subtype.val_injective

theorem is_artinian_of_le {s t : Submodule R M} [ht : IsArtinian R t] (h : s ≤ t) : IsArtinian R s :=
  is_artinian_of_injective (Submodule.ofLe h) (Submodule.of_le_injective h)

variable(M)

theorem is_artinian_of_surjective (f : M →ₗ[R] P) (hf : Function.Surjective f) [IsArtinian R M] : IsArtinian R P :=
  ⟨Subrelation.wfₓ (fun A B hAB => show A.comap f < B.comap f from Submodule.comap_strict_mono_of_surjective hf hAB)
      (InvImage.wfₓ (Submodule.comap f) (IsArtinian.well_founded_submodule_lt _ _))⟩

variable{M}

theorem is_artinian_of_linear_equiv (f : M ≃ₗ[R] P) [IsArtinian R M] : IsArtinian R P :=
  is_artinian_of_surjective _ f.to_linear_map f.to_equiv.surjective

theorem is_artinian_of_range_eq_ker [IsArtinian R M] [IsArtinian R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
  (hf : Function.Injective f) (hg : Function.Surjective g) (h : f.range = g.ker) : IsArtinian R N :=
  ⟨well_founded_lt_exact_sequence (IsArtinian.well_founded_submodule_lt _ _) (IsArtinian.well_founded_submodule_lt _ _)
      f.range (Submodule.map f) (Submodule.comap f) (Submodule.comap g) (Submodule.map g) (Submodule.gciMapComap hf)
      (Submodule.giMapComap hg)
      (by 
        simp [Submodule.map_comap_eq, inf_comm])
      (by 
        simp [Submodule.comap_map_eq, h])⟩

instance is_artinian_prod [IsArtinian R M] [IsArtinian R P] : IsArtinian R (M × P) :=
  is_artinian_of_range_eq_ker (LinearMap.inl R M P) (LinearMap.snd R M P) LinearMap.inl_injective
    LinearMap.snd_surjective (LinearMap.range_inl R M P)

@[instance]
theorem is_artinian_of_fintype [Fintype M] : IsArtinian R M :=
  ⟨Fintype.well_founded_of_trans_of_irrefl _⟩

attribute [local elab_as_eliminator] Fintype.induction_empty_option

instance is_artinian_pi {R ι : Type _} [Fintype ι] :
  ∀ {M : ι → Type _} [Ringₓ R] [∀ i, AddCommGroupₓ (M i)],
    by 
      exactI
        ∀ [∀ i, Module R (M i)],
          by 
            exactI ∀ [∀ i, IsArtinian R (M i)], IsArtinian R (∀ i, M i) :=
  Fintype.induction_empty_option
    (by 
      introI α β e hα M _ _ _ _ 
      exact is_artinian_of_linear_equiv (LinearEquiv.piCongrLeft R M e))
    (by 
      introI M _ _ _ _ 
      infer_instance)
    (by 
      introI α _ ih M _ _ _ _ 
      exact is_artinian_of_linear_equiv (LinearEquiv.piOptionEquivProd R).symm)
    ι

/-- A version of `is_artinian_pi` for non-dependent functions. We need this instance because
sometimes Lean fails to apply the dependent version in non-dependent settings (e.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`). -/
instance is_artinian_pi' {R ι M : Type _} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [Fintype ι] [IsArtinian R M] :
  IsArtinian R (ι → M) :=
  is_artinian_pi

end 

open IsArtinian Submodule Function

section 

variable{R M : Type _}[Ringₓ R][AddCommGroupₓ M][Module R M]

theorem is_artinian_iff_well_founded : IsArtinian R M ↔ WellFounded (· < · : Submodule R M → Submodule R M → Prop) :=
  ⟨fun h => h.1, IsArtinian.mk⟩

variable{R M}

-- error in RingTheory.Artinian: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_artinian.finite_of_linear_independent
[nontrivial R]
[is_artinian R M]
{s : set M}
(hs : linear_independent R (coe : s → M)) : s.finite :=
begin
  refine [expr classical.by_contradiction (λ
    hf, (rel_embedding.well_founded_iff_no_descending_seq.1 (well_founded_submodule_lt R M)).elim' _)],
  have [ident f] [":", expr «expr ↪ »(exprℕ(), s)] [],
  from [expr @infinite.nat_embedding s ⟨λ f, hf ⟨f⟩⟩],
  have [] [":", expr ∀ n, «expr ⊆ »(«expr '' »(«expr ∘ »(coe, f), {m | «expr ≤ »(n, m)}), s)] [],
  { rintros [ident n, ident x, "⟨", ident y, ",", ident hy₁, ",", ident hy₂, "⟩"],
    subst [expr hy₂],
    exact [expr (f y).2] },
  have [] [":", expr ∀
   a
   b : exprℕ(), «expr ↔ »(«expr ≤ »(a, b), «expr ≤ »(span R «expr '' »(«expr ∘ »(coe, f), {m | «expr ≤ »(b, m)}), span R «expr '' »(«expr ∘ »(coe, f), {m | «expr ≤ »(a, m)})))] [],
  { assume [binders (a b)],
    rw ["[", expr span_le_span_iff hs (this b) (this a), ",", expr set.image_subset_image_iff (subtype.coe_injective.comp f.injective), ",", expr set.subset_def, "]"] [],
    simp [] [] ["only"] ["[", expr set.mem_set_of_eq, "]"] [] [],
    exact [expr ⟨λ hab x, le_trans hab, λ h, h _ (le_refl _)⟩] },
  exact [expr ⟨⟨λ
     n, span R «expr '' »(«expr ∘ »(coe, f), {m | «expr ≤ »(n, m)}), λ
     x
     y, by simp [] [] [] ["[", expr le_antisymm_iff, ",", expr (this _ _).symm, "]"] [] [] { contextual := tt }⟩, begin
      intros [ident a, ident b],
      conv_rhs [] [] { rw ["[", expr gt, ",", expr lt_iff_le_not_le, ",", expr this, ",", expr this, ",", "<-", expr lt_iff_le_not_le, "]"] },
      simp [] [] [] [] [] []
    end⟩]
end

/-- A module is Artinian iff every nonempty set of submodules has a minimal submodule among them.
-/
theorem set_has_minimal_iff_artinian :
  (∀ a : Set$ Submodule R M, a.nonempty → ∃ (M' : _)(_ : M' ∈ a), ∀ I _ : I ∈ a, I ≤ M' → I = M') ↔ IsArtinian R M :=
  by 
    rw [is_artinian_iff_well_founded, WellFounded.well_founded_iff_has_min']

theorem IsArtinian.set_has_minimal [IsArtinian R M] (a : Set$ Submodule R M) (ha : a.nonempty) :
  ∃ (M' : _)(_ : M' ∈ a), ∀ I _ : I ∈ a, I ≤ M' → I = M' :=
  set_has_minimal_iff_artinian.mpr ‹_› a ha

/-- A module is Artinian iff every decreasing chain of submodules stabilizes. -/
theorem monotone_stabilizes_iff_artinian :
  (∀ f : ℕ →ₘ OrderDual (Submodule R M), ∃ n, ∀ m, n ≤ m → f n = f m) ↔ IsArtinian R M :=
  by 
    rw [is_artinian_iff_well_founded] <;> exact (WellFounded.monotone_chain_condition (OrderDual (Submodule R M))).symm

theorem IsArtinian.monotone_stabilizes [IsArtinian R M] (f : ℕ →ₘ OrderDual (Submodule R M)) :
  ∃ n, ∀ m, n ≤ m → f n = f m :=
  monotone_stabilizes_iff_artinian.mpr ‹_› f

/-- If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules. -/
theorem IsArtinian.induction [IsArtinian R M] {P : Submodule R M → Prop} (hgt : ∀ I, (∀ J _ : J < I, P J) → P I)
  (I : Submodule R M) : P I :=
  WellFounded.recursionₓ (well_founded_submodule_lt R M) I hgt

/--
For any endomorphism of a Artinian module, there is some nontrivial iterate
with disjoint kernel and range.
-/
theorem IsArtinian.exists_endomorphism_iterate_ker_sup_range_eq_top [I : IsArtinian R M] (f : M →ₗ[R] M) :
  ∃ n : ℕ, n ≠ 0 ∧ (f^n).ker⊔(f^n).range = ⊤ :=
  by 
    obtain ⟨n, w⟩ :=
      monotone_stabilizes_iff_artinian.mpr I
        (f.iterate_range.comp
          ⟨fun n => n+1,
            fun n m w =>
              by 
                linarith⟩)
    specialize
      w ((n+1)+n)
        (by 
          linarith)
    dsimp  at w 
    refine' ⟨n+1, Nat.succ_ne_zero _, _⟩
    simpRw [eq_top_iff', mem_sup]
    intro x 
    have  : (f^n+1) x ∈ (f^((n+1)+n)+1).range
    ·
      rw [←w]
      exact mem_range_self _ 
    rcases this with ⟨y, hy⟩
    use x - (f^n+1) y 
    split 
    ·
      rw [LinearMap.mem_ker, LinearMap.map_sub, ←hy, sub_eq_zero, pow_addₓ]
      simp [iterate_add_apply]
    ·
      use (f^n+1) y 
      simp 

/-- Any injective endomorphism of an Artinian module is surjective. -/
theorem IsArtinian.surjective_of_injective_endomorphism [IsArtinian R M] (f : M →ₗ[R] M) (s : injective f) :
  surjective f :=
  by 
    obtain ⟨n, ne, w⟩ := IsArtinian.exists_endomorphism_iterate_ker_sup_range_eq_top f 
    rw [linear_map.ker_eq_bot.mpr (LinearMap.iterate_injective s n), bot_sup_eq, LinearMap.range_eq_top] at w 
    exact LinearMap.surjective_of_iterate_surjective Ne w

/-- Any injective endomorphism of an Artinian module is bijective. -/
theorem IsArtinian.bijective_of_injective_endomorphism [IsArtinian R M] (f : M →ₗ[R] M) (s : injective f) :
  bijective f :=
  ⟨s, IsArtinian.surjective_of_injective_endomorphism f s⟩

/--
A sequence `f` of submodules of a artinian module,
with the supremum `f (n+1)` and the infinum of `f 0`, ..., `f n` being ⊤,
is eventually ⊤.
-/
theorem IsArtinian.disjoint_partial_infs_eventually_top [I : IsArtinian R M] (f : ℕ → Submodule R M)
  (h : ∀ n, Disjoint (partialSups (OrderDual.toDual ∘ f) n) (OrderDual.toDual (f (n+1)))) :
  ∃ n : ℕ, ∀ m, n ≤ m → f m = ⊤ :=
  by 
    suffices t : ∃ n : ℕ, ∀ m, n ≤ m → OrderDual.toDual f (m+1) = ⊤
    ·
      obtain ⟨n, w⟩ := t 
      use n+1
      rintro (_ | m) p
      ·
        cases p
      ·
        apply w 
        exact nat.succ_le_succ_iff.mp p 
    obtain ⟨n, w⟩ := monotone_stabilizes_iff_artinian.mpr I (partialSups (OrderDual.toDual ∘ f))
    exact ⟨n, fun m p => eq_bot_of_disjoint_absorbs (h m) ((Eq.symm (w (m+1) (le_add_right p))).trans (w m p))⟩

universe w

variable{N : Type w}[AddCommGroupₓ N][Module R N]

end 

/--
A ring is Artinian if it is Artinian as a module over itself.
-/
class IsArtinianRing(R)[Ringₓ R] extends IsArtinian R R : Prop

theorem is_artinian_ring_iff {R} [Ringₓ R] : IsArtinianRing R ↔ IsArtinian R R :=
  ⟨fun h => h.1, @IsArtinianRing.mk _ _⟩

theorem Ringₓ.is_artinian_of_zero_eq_one {R} [Ringₓ R] (h01 : (0 : R) = 1) : IsArtinianRing R :=
  by 
    haveI  := subsingleton_of_zero_eq_one h01 <;> haveI  := Fintype.ofSubsingleton (0 : R) <;> split  <;> infer_instance

theorem is_artinian_of_submodule_of_artinian R M [Ringₓ R] [AddCommGroupₓ M] [Module R M] (N : Submodule R M)
  (h : IsArtinian R M) : IsArtinian R N :=
  by 
    infer_instance

theorem is_artinian_of_quotient_of_artinian R [Ringₓ R] M [AddCommGroupₓ M] [Module R M] (N : Submodule R M)
  (h : IsArtinian R M) : IsArtinian R N.quotient :=
  is_artinian_of_surjective M (Submodule.mkq N) (Submodule.Quotient.mk_surjective N)

/-- If `M / S / R` is a scalar tower, and `M / R` is Artinian, then `M / S` is
also Artinian. -/
theorem is_artinian_of_tower R {S M} [CommRingₓ R] [Ringₓ S] [AddCommGroupₓ M] [Algebra R S] [Module S M] [Module R M]
  [IsScalarTower R S M] (h : IsArtinian R M) : IsArtinian S M :=
  by 
    rw [is_artinian_iff_well_founded] at h⊢
    refine' (Submodule.restrictScalarsEmbedding R S M).WellFounded h

theorem is_artinian_of_fg_of_artinian {R M} [Ringₓ R] [AddCommGroupₓ M] [Module R M] (N : Submodule R M)
  [IsArtinianRing R] (hN : N.fg) : IsArtinian R N :=
  let ⟨s, hs⟩ := hN 
  by 
    haveI  := Classical.decEq M 
    haveI  := Classical.decEq R 
    letI this : IsArtinian R R :=
      by 
        infer_instance 
    have  : ∀ x _ : x ∈ s, x ∈ N 
    exact fun x hx => hs ▸ Submodule.subset_span hx 
    refine' @is_artinian_of_surjective ((«expr↑ » s : Set M) → R) _ _ _ (Pi.module _ _ _) _ _ _ is_artinian_pi
    ·
      fapply LinearMap.mk
      ·
        exact fun f => ⟨∑i in s.attach, f i • i.1, N.sum_mem fun c _ => N.smul_mem _$ this _ c.2⟩
      ·
        intro f g 
        apply Subtype.eq 
        change (∑i in s.attach, (f i+g i) • _) = _ 
        simp only [add_smul, Finset.sum_add_distrib]
        rfl
      ·
        intro c f 
        apply Subtype.eq 
        change (∑i in s.attach, (c • f i) • _) = _ 
        simp only [smul_eq_mul, mul_smul]
        exact finset.smul_sum.symm 
    rintro ⟨n, hn⟩
    change n ∈ N at hn 
    rw [←hs, ←Set.image_id («expr↑ » s), Finsupp.mem_span_image_iff_total] at hn 
    rcases hn with ⟨l, hl1, hl2⟩
    refine' ⟨fun x => l x, Subtype.ext _⟩
    change (∑i in s.attach, l i • (i : M)) = n 
    rw [@Finset.sum_attach M M s _ fun i => l i • i, ←hl2, Finsupp.total_apply, Finsupp.sum, eq_comm]
    refine' Finset.sum_subset hl1 fun x _ hx => _ 
    rw [Finsupp.not_mem_support_iff.1 hx, zero_smul]

theorem is_artinian_of_fg_of_artinian' {R M} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [IsArtinianRing R]
  (h : (⊤ : Submodule R M).Fg) : IsArtinian R M :=
  have  : IsArtinian R (⊤ : Submodule R M) := is_artinian_of_fg_of_artinian _ h 
  by 
    exactI is_artinian_of_linear_equiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl)

/-- In a module over a artinian ring, the submodule generated by finitely many vectors is
artinian. -/
theorem is_artinian_span_of_finite R {M} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [IsArtinianRing R] {A : Set M}
  (hA : finite A) : IsArtinian R (Submodule.span R A) :=
  is_artinian_of_fg_of_artinian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)

theorem is_artinian_ring_of_surjective R [CommRingₓ R] S [CommRingₓ S] (f : R →+* S) (hf : Function.Surjective f)
  [H : IsArtinianRing R] : IsArtinianRing S :=
  by 
    rw [is_artinian_ring_iff, is_artinian_iff_well_founded] at H⊢
    exact OrderEmbedding.well_founded (Ideal.orderEmbeddingOfSurjective f hf) H

instance is_artinian_ring_range {R} [CommRingₓ R] {S} [CommRingₓ S] (f : R →+* S) [IsArtinianRing R] :
  IsArtinianRing f.range :=
  is_artinian_ring_of_surjective R f.range f.range_restrict f.range_restrict_surjective

theorem is_artinian_ring_of_ring_equiv R [CommRingₓ R] {S} [CommRingₓ S] (f : R ≃+* S) [IsArtinianRing R] :
  IsArtinianRing S :=
  is_artinian_ring_of_surjective R S f.to_ring_hom f.to_equiv.surjective

namespace IsArtinianRing

open IsArtinian

variable{R : Type _}[CommRingₓ R][IsArtinianRing R]

-- error in RingTheory.Artinian: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contradiction: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem is_nilpotent_jacobson_bot : is_nilpotent (ideal.jacobson («expr⊥»() : ideal R)) :=
begin
  let [ident Jac] [] [":=", expr ideal.jacobson («expr⊥»() : ideal R)],
  let [ident f] [":", expr «expr →ₘ »(exprℕ(), order_dual (ideal R))] [":=", expr ⟨λ
    n, «expr ^ »(Jac, n), λ _ _ h, ideal.pow_le_pow h⟩],
  obtain ["⟨", ident n, ",", ident hn, "⟩", ":", expr «expr∃ , »((n), ∀
    m, «expr ≤ »(n, m) → «expr = »(«expr ^ »(Jac, n), «expr ^ »(Jac, m))), ":=", expr is_artinian.monotone_stabilizes f],
  refine [expr ⟨n, _⟩],
  let [ident J] [":", expr ideal R] [":=", expr annihilator «expr ^ »(Jac, n)],
  suffices [] [":", expr «expr = »(J, «expr⊤»())],
  { have [ident hJ] [":", expr «expr = »(«expr • »(J, «expr ^ »(Jac, n)), «expr⊥»())] [":=", expr annihilator_smul «expr ^ »(Jac, n)],
    simpa [] [] ["only"] ["[", expr this, ",", expr top_smul, ",", expr ideal.zero_eq_bot, "]"] [] ["using", expr hJ] },
  by_contradiction [ident hJ],
  change [expr «expr ≠ »(J, «expr⊤»())] [] ["at", ident hJ],
  rcases [expr is_artinian.set_has_minimal {J' : ideal R | «expr < »(J, J')} ⟨«expr⊤»(), hJ.lt_top⟩, "with", "⟨", ident J', ",", ident hJJ', ":", expr «expr < »(J, J'), ",", ident hJ', ":", expr ∀
   I, «expr < »(J, I) → «expr ≤ »(I, J') → «expr = »(I, J'), "⟩"],
  rcases [expr set_like.exists_of_lt hJJ', "with", "⟨", ident x, ",", ident hxJ', ",", ident hxJ, "⟩"],
  obtain [ident rfl, ":", expr «expr = »(«expr ⊔ »(J, ideal.span {x}), J')],
  { refine [expr hJ' «expr ⊔ »(J, ideal.span {x}) _ _],
    { rw [expr set_like.lt_iff_le_and_exists] [],
      exact [expr ⟨le_sup_left, ⟨x, mem_sup_right (mem_span_singleton_self x), hxJ⟩⟩] },
    { exact [expr sup_le hJJ'.le (span_le.2 (singleton_subset_iff.2 hxJ'))] } },
  have [] [":", expr «expr ≤ »(«expr ⊔ »(J, «expr • »(Jac, ideal.span {x})), «expr ⊔ »(J, ideal.span {x}))] [],
  from [expr sup_le_sup_left (smul_le.2 (λ _ _ _, submodule.smul_mem _ _)) _],
  have [] [":", expr «expr ≤ »(«expr * »(Jac, ideal.span {x}), J)] [],
  { classical,
    by_contradiction [ident H],
    refine [expr H (smul_sup_le_of_le_smul_of_le_jacobson_bot (fg_span_singleton _) le_rfl (hJ' _ _ this).ge)],
    exact [expr lt_of_le_of_ne le_sup_left (λ h, «expr $ »(H, «expr ▸ »(h.symm, le_sup_right)))] },
  have [] [":", expr «expr ≤ »(«expr * »(ideal.span {x}, «expr ^ »(Jac, «expr + »(n, 1))), «expr⊥»())] [],
  calc
    «expr = »(«expr * »(ideal.span {x}, «expr ^ »(Jac, «expr + »(n, 1))), «expr * »(«expr * »(ideal.span {x}, Jac), «expr ^ »(Jac, n))) : by rw ["[", expr pow_succ, ",", "<-", expr mul_assoc, "]"] []
    «expr ≤ »(..., «expr * »(J, «expr ^ »(Jac, n))) : mul_le_mul (by rwa [expr mul_comm] []) (le_refl _)
    «expr = »(..., «expr⊥»()) : by simp [] [] [] ["[", expr J, "]"] [] [],
  refine [expr hxJ (mem_annihilator.2 (λ y hy, (mem_bot R).1 _))],
  refine [expr this (mul_mem_mul (mem_span_singleton_self x) _)],
  rwa ["[", "<-", expr hn «expr + »(n, 1) (nat.le_succ _), "]"] []
end

end IsArtinianRing

