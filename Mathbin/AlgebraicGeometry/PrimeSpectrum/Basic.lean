import Mathbin.Topology.Opens 
import Mathbin.RingTheory.Ideal.Prod 
import Mathbin.RingTheory.Ideal.Over 
import Mathbin.LinearAlgebra.Finsupp 
import Mathbin.Algebra.PunitInstances

/-!
# Prime spectrum of a commutative ring

The prime spectrum of a commutative ring is the type of all prime ideals.
It is naturally endowed with a topology: the Zariski topology.

(It is also naturally endowed with a sheaf of rings,
which is constructed in `algebraic_geometry.structure_sheaf`.)

## Main definitions

* `prime_spectrum R`: The prime spectrum of a commutative ring `R`,
  i.e., the set of all prime ideals of `R`.
* `zero_locus s`: The zero locus of a subset `s` of `R`
  is the subset of `prime_spectrum R` consisting of all prime ideals that contain `s`.
* `vanishing_ideal t`: The vanishing ideal of a subset `t` of `prime_spectrum R`
  is the intersection of points in `t` (viewed as prime ideals).

## Conventions

We denote subsets of rings with `s`, `s'`, etc...
whereas we denote subsets of prime spectra with `t`, `t'`, etc...

## Inspiration/contributors

The contents of this file draw inspiration from
<https://github.com/ramonfmir/lean-scheme>
which has contributions from Ramon Fernandez Mir, Kevin Buzzard, Kenny Lau,
and Chris Hughes (on an earlier repository).

-/


noncomputable theory

open_locale Classical

universe u v

variable(R : Type u)[CommRingₓ R]

/-- The prime spectrum of a commutative ring `R`
is the type of all prime ideals of `R`.

It is naturally endowed with a topology (the Zariski topology),
and a sheaf of commutative rings (see `algebraic_geometry.structure_sheaf`).
It is a fundamental building block in algebraic geometry. -/
@[nolint has_inhabited_instance]
def PrimeSpectrum :=
  { I : Ideal R // I.is_prime }

variable{R}

namespace PrimeSpectrum

/-- A method to view a point in the prime spectrum of a commutative ring
as an ideal of that ring. -/
abbrev as_ideal (x : PrimeSpectrum R) : Ideal R :=
  x.val

instance is_prime (x : PrimeSpectrum R) : x.as_ideal.is_prime :=
  x.2

/--
The prime spectrum of the zero ring is empty.
-/
theorem PUnit (x : PrimeSpectrum PUnit) : False :=
  x.1.ne_top_iff_one.1 x.2.1$ Subsingleton.elimₓ (0 : PUnit) 1 ▸ x.1.zero_mem

section 

variable(R)(S : Type v)[CommRingₓ S]

/-- The prime spectrum of `R × S` is in bijection with the disjoint unions of the prime spectrum of
    `R` and the prime spectrum of `S`. -/
noncomputable def prime_spectrum_prod : PrimeSpectrum (R × S) ≃ Sum (PrimeSpectrum R) (PrimeSpectrum S) :=
  Ideal.primeIdealsEquiv R S

variable{R S}

@[simp]
theorem prime_spectrum_prod_symm_inl_as_ideal (x : PrimeSpectrum R) :
  ((prime_spectrum_prod R S).symm (Sum.inl x)).asIdeal = Ideal.prod x.as_ideal ⊤ :=
  by 
    cases x 
    rfl

@[simp]
theorem prime_spectrum_prod_symm_inr_as_ideal (x : PrimeSpectrum S) :
  ((prime_spectrum_prod R S).symm (Sum.inr x)).asIdeal = Ideal.prod ⊤ x.as_ideal :=
  by 
    cases x 
    rfl

end 

@[ext]
theorem ext {x y : PrimeSpectrum R} : x = y ↔ x.as_ideal = y.as_ideal :=
  Subtype.ext_iff_val

/-- The zero locus of a set `s` of elements of a commutative ring `R`
is the set of all prime ideals of the ring that contain the set `s`.

An element `f` of `R` can be thought of as a dependent function
on the prime spectrum of `R`.
At a point `x` (a prime ideal)
the function (i.e., element) `f` takes values in the quotient ring `R` modulo the prime ideal `x`.
In this manner, `zero_locus s` is exactly the subset of `prime_spectrum R`
where all "functions" in `s` vanish simultaneously.
-/
def zero_locus (s : Set R) : Set (PrimeSpectrum R) :=
  { x | s ⊆ x.as_ideal }

@[simp]
theorem mem_zero_locus (x : PrimeSpectrum R) (s : Set R) : x ∈ zero_locus s ↔ s ⊆ x.as_ideal :=
  Iff.rfl

@[simp]
theorem zero_locus_span (s : Set R) : zero_locus (Ideal.span s : Set R) = zero_locus s :=
  by 
    ext x 
    exact (Submodule.gi R R).gc s x.as_ideal

/-- The vanishing ideal of a set `t` of points
of the prime spectrum of a commutative ring `R`
is the intersection of all the prime ideals in the set `t`.

An element `f` of `R` can be thought of as a dependent function
on the prime spectrum of `R`.
At a point `x` (a prime ideal)
the function (i.e., element) `f` takes values in the quotient ring `R` modulo the prime ideal `x`.
In this manner, `vanishing_ideal t` is exactly the ideal of `R`
consisting of all "functions" that vanish on all of `t`.
-/
def vanishing_ideal (t : Set (PrimeSpectrum R)) : Ideal R :=
  ⨅(x : PrimeSpectrum R)(h : x ∈ t), x.as_ideal

theorem coe_vanishing_ideal (t : Set (PrimeSpectrum R)) :
  (vanishing_ideal t : Set R) = { f : R | ∀ x : PrimeSpectrum R, x ∈ t → f ∈ x.as_ideal } :=
  by 
    ext f 
    rw [vanishing_ideal, SetLike.mem_coe, Submodule.mem_infi]
    apply forall_congrₓ 
    intro x 
    rw [Submodule.mem_infi]

theorem mem_vanishing_ideal (t : Set (PrimeSpectrum R)) (f : R) :
  f ∈ vanishing_ideal t ↔ ∀ x : PrimeSpectrum R, x ∈ t → f ∈ x.as_ideal :=
  by 
    rw [←SetLike.mem_coe, coe_vanishing_ideal, Set.mem_set_of_eq]

@[simp]
theorem vanishing_ideal_singleton (x : PrimeSpectrum R) : vanishing_ideal ({x} : Set (PrimeSpectrum R)) = x.as_ideal :=
  by 
    simp [vanishing_ideal]

theorem subset_zero_locus_iff_le_vanishing_ideal (t : Set (PrimeSpectrum R)) (I : Ideal R) :
  t ⊆ zero_locus I ↔ I ≤ vanishing_ideal t :=
  ⟨fun h f k => (mem_vanishing_ideal _ _).mpr fun x j => (mem_zero_locus _ _).mpr (h j) k,
    fun h => fun x j => (mem_zero_locus _ _).mpr (le_transₓ h fun f h => ((mem_vanishing_ideal _ _).mp h) x j)⟩

section Gc

variable(R)

/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
theorem gc :
  @GaloisConnection (Ideal R) (OrderDual (Set (PrimeSpectrum R))) _ _ (fun I => zero_locus I)
    fun t => vanishing_ideal t :=
  fun I t => subset_zero_locus_iff_le_vanishing_ideal t I

/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
theorem gc_set :
  @GaloisConnection (Set R) (OrderDual (Set (PrimeSpectrum R))) _ _ (fun s => zero_locus s)
    fun t => vanishing_ideal t :=
  have ideal_gc : GaloisConnection Ideal.span coeₓ := (Submodule.gi R R).gc 
  by 
    simpa [zero_locus_span, Function.comp] using ideal_gc.compose (gc R)

theorem subset_zero_locus_iff_subset_vanishing_ideal (t : Set (PrimeSpectrum R)) (s : Set R) :
  t ⊆ zero_locus s ↔ s ⊆ vanishing_ideal t :=
  (gc_set R) s t

end Gc

theorem subset_vanishing_ideal_zero_locus (s : Set R) : s ⊆ vanishing_ideal (zero_locus s) :=
  (gc_set R).le_u_l s

theorem le_vanishing_ideal_zero_locus (I : Ideal R) : I ≤ vanishing_ideal (zero_locus I) :=
  (gc R).le_u_l I

@[simp]
theorem vanishing_ideal_zero_locus_eq_radical (I : Ideal R) : vanishing_ideal (zero_locus (I : Set R)) = I.radical :=
  Ideal.ext$
    fun f =>
      by 
        rw [mem_vanishing_ideal, Ideal.radical_eq_Inf, Submodule.mem_Inf]
        exact ⟨fun h x hx => h ⟨x, hx.2⟩ hx.1, fun h x hx => h x.1 ⟨hx, x.2⟩⟩

@[simp]
theorem zero_locus_radical (I : Ideal R) : zero_locus (I.radical : Set R) = zero_locus I :=
  vanishing_ideal_zero_locus_eq_radical I ▸ (gc R).l_u_l_eq_l I

theorem subset_zero_locus_vanishing_ideal (t : Set (PrimeSpectrum R)) : t ⊆ zero_locus (vanishing_ideal t) :=
  (gc R).l_u_le t

theorem zero_locus_anti_mono {s t : Set R} (h : s ⊆ t) : zero_locus t ⊆ zero_locus s :=
  (gc_set R).monotone_l h

theorem zero_locus_anti_mono_ideal {s t : Ideal R} (h : s ≤ t) : zero_locus (t : Set R) ⊆ zero_locus (s : Set R) :=
  (gc R).monotone_l h

theorem vanishing_ideal_anti_mono {s t : Set (PrimeSpectrum R)} (h : s ⊆ t) : vanishing_ideal t ≤ vanishing_ideal s :=
  (gc R).monotone_u h

theorem zero_locus_subset_zero_locus_iff (I J : Ideal R) :
  zero_locus (I : Set R) ⊆ zero_locus (J : Set R) ↔ J ≤ I.radical :=
  ⟨fun h =>
      Ideal.radical_le_radical_iff.mp
        (vanishing_ideal_zero_locus_eq_radical I ▸
          vanishing_ideal_zero_locus_eq_radical J ▸ vanishing_ideal_anti_mono h),
    fun h => zero_locus_radical I ▸ zero_locus_anti_mono_ideal h⟩

theorem zero_locus_subset_zero_locus_singleton_iff (f g : R) :
  zero_locus ({f} : Set R) ⊆ zero_locus {g} ↔ g ∈ (Ideal.span ({f} : Set R)).radical :=
  by 
    rw [←zero_locus_span {f}, ←zero_locus_span {g}, zero_locus_subset_zero_locus_iff, Ideal.span_le,
      Set.singleton_subset_iff, SetLike.mem_coe]

theorem zero_locus_bot : zero_locus ((⊥ : Ideal R) : Set R) = Set.Univ :=
  (gc R).l_bot

@[simp]
theorem zero_locus_singleton_zero : zero_locus ({0} : Set R) = Set.Univ :=
  zero_locus_bot

@[simp]
theorem zero_locus_empty : zero_locus (∅ : Set R) = Set.Univ :=
  (gc_set R).l_bot

@[simp]
theorem vanishing_ideal_univ : vanishing_ideal (∅ : Set (PrimeSpectrum R)) = ⊤ :=
  by 
    simpa using (gc R).u_top

theorem zero_locus_empty_of_one_mem {s : Set R} (h : (1 : R) ∈ s) : zero_locus s = ∅ :=
  by 
    rw [Set.eq_empty_iff_forall_not_mem]
    intro x hx 
    rw [mem_zero_locus] at hx 
    have x_prime : x.as_ideal.is_prime :=
      by 
        infer_instance 
    have eq_top : x.as_ideal = ⊤
    ·
      rw [Ideal.eq_top_iff_one]
      exact hx h 
    apply x_prime.ne_top eq_top

@[simp]
theorem zero_locus_singleton_one : zero_locus ({1} : Set R) = ∅ :=
  zero_locus_empty_of_one_mem (Set.mem_singleton (1 : R))

theorem zero_locus_empty_iff_eq_top {I : Ideal R} : zero_locus (I : Set R) = ∅ ↔ I = ⊤ :=
  by 
    split 
    ·
      contrapose! 
      intro h 
      apply set.ne_empty_iff_nonempty.mpr 
      rcases Ideal.exists_le_maximal I h with ⟨M, hM, hIM⟩
      exact ⟨⟨M, hM.is_prime⟩, hIM⟩
    ·
      rintro rfl 
      apply zero_locus_empty_of_one_mem 
      trivial

@[simp]
theorem zero_locus_univ : zero_locus (Set.Univ : Set R) = ∅ :=
  zero_locus_empty_of_one_mem (Set.mem_univ 1)

theorem zero_locus_sup (I J : Ideal R) : zero_locus ((I⊔J : Ideal R) : Set R) = zero_locus I ∩ zero_locus J :=
  (gc R).l_sup

theorem zero_locus_union (s s' : Set R) : zero_locus (s ∪ s') = zero_locus s ∩ zero_locus s' :=
  (gc_set R).l_sup

theorem vanishing_ideal_union (t t' : Set (PrimeSpectrum R)) :
  vanishing_ideal (t ∪ t') = vanishing_ideal t⊓vanishing_ideal t' :=
  (gc R).u_inf

theorem zero_locus_supr {ι : Sort _} (I : ι → Ideal R) :
  zero_locus ((⨆i, I i : Ideal R) : Set R) = ⋂i, zero_locus (I i) :=
  (gc R).l_supr

theorem zero_locus_Union {ι : Sort _} (s : ι → Set R) : zero_locus (⋃i, s i) = ⋂i, zero_locus (s i) :=
  (gc_set R).l_supr

theorem zero_locus_bUnion (s : Set (Set R)) :
  zero_locus (⋃(s' : _)(_ : s' ∈ s), s' : Set R) = ⋂(s' : _)(_ : s' ∈ s), zero_locus s' :=
  by 
    simp only [zero_locus_Union]

theorem vanishing_ideal_Union {ι : Sort _} (t : ι → Set (PrimeSpectrum R)) :
  vanishing_ideal (⋃i, t i) = ⨅i, vanishing_ideal (t i) :=
  (gc R).u_infi

theorem zero_locus_inf (I J : Ideal R) : zero_locus ((I⊓J : Ideal R) : Set R) = zero_locus I ∪ zero_locus J :=
  Set.ext$
    fun x =>
      by 
        simpa using x.2.inf_le

theorem union_zero_locus (s s' : Set R) :
  zero_locus s ∪ zero_locus s' = zero_locus (Ideal.span s⊓Ideal.span s' : Ideal R) :=
  by 
    rw [zero_locus_inf]
    simp 

theorem zero_locus_mul (I J : Ideal R) : zero_locus ((I*J : Ideal R) : Set R) = zero_locus I ∪ zero_locus J :=
  Set.ext$
    fun x =>
      by 
        simpa using x.2.mul_le

theorem zero_locus_singleton_mul (f g : R) : zero_locus ({f*g} : Set R) = zero_locus {f} ∪ zero_locus {g} :=
  Set.ext$
    fun x =>
      by 
        simpa using x.2.mul_mem_iff_mem_or_mem

@[simp]
theorem zero_locus_pow (I : Ideal R) {n : ℕ} (hn : 0 < n) : zero_locus ((I^n : Ideal R) : Set R) = zero_locus I :=
  zero_locus_radical (I^n) ▸ (I.radical_pow n hn).symm ▸ zero_locus_radical I

@[simp]
theorem zero_locus_singleton_pow (f : R) (n : ℕ) (hn : 0 < n) : zero_locus ({f^n} : Set R) = zero_locus {f} :=
  Set.ext$
    fun x =>
      by 
        simpa using x.2.pow_mem_iff_mem n hn

-- error in AlgebraicGeometry.PrimeSpectrum.Basic: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
theorem sup_vanishing_ideal_le
(t
 t' : set (prime_spectrum R)) : «expr ≤ »(«expr ⊔ »(vanishing_ideal t, vanishing_ideal t'), vanishing_ideal «expr ∩ »(t, t')) :=
begin
  intros [ident r],
  rw ["[", expr submodule.mem_sup, ",", expr mem_vanishing_ideal, "]"] [],
  rintro ["⟨", ident f, ",", ident hf, ",", ident g, ",", ident hg, ",", ident rfl, "⟩", ident x, "⟨", ident hxt, ",", ident hxt', "⟩"],
  rw [expr mem_vanishing_ideal] ["at", ident hf, ident hg],
  apply [expr submodule.add_mem]; solve_by_elim [] [] [] []
end

theorem mem_compl_zero_locus_iff_not_mem {f : R} {I : PrimeSpectrum R} :
  I ∈ «expr ᶜ» (zero_locus {f} : Set (PrimeSpectrum R)) ↔ f ∉ I.as_ideal :=
  by 
    rw [Set.mem_compl_eq, mem_zero_locus, Set.singleton_subset_iff] <;> rfl

/-- The Zariski topology on the prime spectrum of a commutative ring
is defined via the closed sets of the topology:
they are exactly those sets that are the zero locus of a subset of the ring. -/
instance zariski_topology : TopologicalSpace (PrimeSpectrum R) :=
  TopologicalSpace.ofClosed (Set.Range PrimeSpectrum.ZeroLocus)
    ⟨Set.Univ,
      by 
        simp ⟩
    (by 
      intro Zs h 
      rw [Set.sInter_eq_Inter]
      let f : Zs → Set R := fun i => Classical.some (h i.2)
      have hf : ∀ i : Zs, «expr↑ » i = zero_locus (f i) := fun i => (Classical.some_spec (h i.2)).symm 
      simp only [hf]
      exact ⟨_, zero_locus_Union _⟩)
    (by 
      rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
      exact ⟨_, (union_zero_locus s t).symm⟩)

theorem is_open_iff (U : Set (PrimeSpectrum R)) : IsOpen U ↔ ∃ s, «expr ᶜ» U = zero_locus s :=
  by 
    simp only [@eq_comm _ («expr ᶜ» U)] <;> rfl

theorem is_closed_iff_zero_locus (Z : Set (PrimeSpectrum R)) : IsClosed Z ↔ ∃ s, Z = zero_locus s :=
  by 
    rw [←is_open_compl_iff, is_open_iff, compl_compl]

theorem is_closed_zero_locus (s : Set R) : IsClosed (zero_locus s) :=
  by 
    rw [is_closed_iff_zero_locus]
    exact ⟨s, rfl⟩

theorem is_closed_singleton_iff_is_maximal (x : PrimeSpectrum R) :
  IsClosed ({x} : Set (PrimeSpectrum R)) ↔ x.as_ideal.is_maximal :=
  by 
    refine' (is_closed_iff_zero_locus _).trans ⟨fun h => _, fun h => _⟩
    ·
      obtain ⟨s, hs⟩ := h 
      rw [eq_comm, Set.eq_singleton_iff_unique_mem] at hs 
      refine'
        ⟨⟨x.2.1,
            fun I hI => not_not.1 (mt (Ideal.exists_le_maximal I)$ not_exists.2 fun J => not_and.2$ fun hJ hIJ => _)⟩⟩
      exact
        ne_of_ltₓ (lt_of_lt_of_leₓ hI hIJ)
          (symm$ congr_argₓ PrimeSpectrum.asIdeal (hs.2 ⟨J, hJ.is_prime⟩ fun r hr => hIJ (le_of_ltₓ hI$ hs.1 hr)))
    ·
      refine' ⟨x.as_ideal.1, _⟩
      rw [eq_comm, Set.eq_singleton_iff_unique_mem]
      refine' ⟨fun _ h => h, fun y hy => PrimeSpectrum.ext.2 (h.eq_of_le y.2.ne_top hy).symm⟩

theorem zero_locus_vanishing_ideal_eq_closure (t : Set (PrimeSpectrum R)) :
  zero_locus (vanishing_ideal t : Set R) = Closure t :=
  by 
    apply Set.Subset.antisymm
    ·
      rintro x hx t' ⟨ht', ht⟩
      obtain ⟨fs, rfl⟩ : ∃ s, t' = zero_locus s
      ·
        rwa [is_closed_iff_zero_locus] at ht' 
      rw [subset_zero_locus_iff_subset_vanishing_ideal] at ht 
      exact Set.Subset.trans ht hx
    ·
      rw [(is_closed_zero_locus _).closure_subset_iff]
      exact subset_zero_locus_vanishing_ideal t

theorem vanishing_ideal_closure (t : Set (PrimeSpectrum R)) : vanishing_ideal (Closure t) = vanishing_ideal t :=
  zero_locus_vanishing_ideal_eq_closure t ▸ (gc R).u_l_u_eq_u t

theorem t1_space_iff_is_field [IsDomain R] : T1Space (PrimeSpectrum R) ↔ IsField R :=
  by 
    refine' ⟨_, fun h => _⟩
    ·
      introI h 
      have hbot : Ideal.IsPrime (⊥ : Ideal R) := Ideal.bot_prime 
      exact
        not_not.1
          (mt
            (Ringₓ.ne_bot_of_is_maximal_of_not_is_field$
              (is_closed_singleton_iff_is_maximal _).1 (T1Space.t1 ⟨⊥, hbot⟩))
            (not_not.2 rfl))
    ·
      refine' ⟨fun x => (is_closed_singleton_iff_is_maximal x).2 _⟩
      byCases' hx : x.as_ideal = ⊥
      ·
        exact hx.symm ▸ @Ideal.bot_is_maximal R (@Field.toDivisionRing _$ IsField.toField R h)
      ·
        exact absurd h (Ringₓ.not_is_field_iff_exists_prime.2 ⟨x.as_ideal, ⟨hx, x.2⟩⟩)

section Comap

variable{S : Type v}[CommRingₓ S]{S' : Type _}[CommRingₓ S']

/-- The function between prime spectra of commutative rings induced by a ring homomorphism.
This function is continuous. -/
def comap (f : R →+* S) : PrimeSpectrum S → PrimeSpectrum R :=
  fun y => ⟨Ideal.comap f y.as_ideal, inferInstance⟩

variable(f : R →+* S)

@[simp]
theorem comap_as_ideal (y : PrimeSpectrum S) : (comap f y).asIdeal = Ideal.comap f y.as_ideal :=
  rfl

@[simp]
theorem comap_id : comap (RingHom.id R) = id :=
  funext$ fun _ => Subtype.ext$ Ideal.ext$ fun _ => Iff.rfl

@[simp]
theorem comap_comp (f : R →+* S) (g : S →+* S') : comap (g.comp f) = (comap f ∘ comap g) :=
  funext$ fun _ => Subtype.ext$ Ideal.ext$ fun _ => Iff.rfl

@[simp]
theorem preimage_comap_zero_locus (s : Set R) : comap f ⁻¹' zero_locus s = zero_locus (f '' s) :=
  by 
    ext x 
    simp only [mem_zero_locus, Set.mem_preimage, comap_as_ideal, Set.image_subset_iff]
    rfl

theorem comap_injective_of_surjective (f : R →+* S) (hf : Function.Surjective f) : Function.Injective (comap f) :=
  fun x y h =>
    PrimeSpectrum.ext.2
      (Ideal.comap_injective_of_surjective f hf
        (congr_argₓ PrimeSpectrum.asIdeal h : (comap f x).asIdeal = (comap f y).asIdeal))

theorem comap_continuous (f : R →+* S) : Continuous (comap f) :=
  by 
    rw [continuous_iff_is_closed]
    simp only [is_closed_iff_zero_locus]
    rintro _ ⟨s, rfl⟩
    exact ⟨_, preimage_comap_zero_locus f s⟩

theorem comap_singleton_is_closed_of_surjective (f : R →+* S) (hf : Function.Surjective f) (x : PrimeSpectrum S)
  (hx : IsClosed ({x} : Set (PrimeSpectrum S))) : IsClosed ({comap f x} : Set (PrimeSpectrum R)) :=
  by 
    haveI  : x.as_ideal.is_maximal := (is_closed_singleton_iff_is_maximal x).1 hx 
    exact (is_closed_singleton_iff_is_maximal _).2 (Ideal.comap_is_maximal_of_surjective f hf)

theorem comap_singleton_is_closed_of_is_integral (f : R →+* S) (hf : f.is_integral) (x : PrimeSpectrum S)
  (hx : IsClosed ({x} : Set (PrimeSpectrum S))) : IsClosed ({comap f x} : Set (PrimeSpectrum R)) :=
  (is_closed_singleton_iff_is_maximal _).2
    (Ideal.is_maximal_comap_of_is_integral_of_is_maximal' f hf x.as_ideal$ (is_closed_singleton_iff_is_maximal x).1 hx)

end Comap

section BasicOpen

/-- `basic_open r` is the open subset containing all prime ideals not containing `r`. -/
def basic_open (r : R) : TopologicalSpace.Opens (PrimeSpectrum R) :=
  { val := { x | r ∉ x.as_ideal }, property := ⟨{r}, Set.ext$ fun x => Set.singleton_subset_iff.trans$ not_not.symm⟩ }

@[simp]
theorem mem_basic_open (f : R) (x : PrimeSpectrum R) : x ∈ basic_open f ↔ f ∉ x.as_ideal :=
  Iff.rfl

theorem is_open_basic_open {a : R} : IsOpen (basic_open a : Set (PrimeSpectrum R)) :=
  (basic_open a).property

@[simp]
theorem basic_open_eq_zero_locus_compl (r : R) : (basic_open r : Set (PrimeSpectrum R)) = «expr ᶜ» (zero_locus {r}) :=
  Set.ext$
    fun x =>
      by 
        simpa only [Set.mem_compl_eq, mem_zero_locus, Set.singleton_subset_iff]

@[simp]
theorem basic_open_one : basic_open (1 : R) = ⊤ :=
  TopologicalSpace.Opens.ext$
    by 
      simp 
      rfl

@[simp]
theorem basic_open_zero : basic_open (0 : R) = ⊥ :=
  TopologicalSpace.Opens.ext$
    by 
      simp 
      rfl

theorem basic_open_le_basic_open_iff (f g : R) : basic_open f ≤ basic_open g ↔ f ∈ (Ideal.span ({g} : Set R)).radical :=
  by 
    rw [TopologicalSpace.Opens.le_def, basic_open_eq_zero_locus_compl, basic_open_eq_zero_locus_compl, Set.le_eq_subset,
      Set.compl_subset_compl, zero_locus_subset_zero_locus_singleton_iff]

theorem basic_open_mul (f g : R) : basic_open (f*g) = basic_open f⊓basic_open g :=
  TopologicalSpace.Opens.ext$
    by 
      simp [zero_locus_singleton_mul]

theorem basic_open_mul_le_left (f g : R) : basic_open (f*g) ≤ basic_open f :=
  by 
    rw [basic_open_mul f g]
    exact inf_le_left

theorem basic_open_mul_le_right (f g : R) : basic_open (f*g) ≤ basic_open g :=
  by 
    rw [basic_open_mul f g]
    exact inf_le_right

@[simp]
theorem basic_open_pow (f : R) (n : ℕ) (hn : 0 < n) : basic_open (f^n) = basic_open f :=
  TopologicalSpace.Opens.ext$
    by 
      simpa using zero_locus_singleton_pow f n hn

theorem is_topological_basis_basic_opens :
  TopologicalSpace.IsTopologicalBasis (Set.Range fun r : R => (basic_open r : Set (PrimeSpectrum R))) :=
  by 
    apply TopologicalSpace.is_topological_basis_of_open_of_nhds
    ·
      rintro _ ⟨r, rfl⟩
      exact is_open_basic_open
    ·
      rintro p U hp ⟨s, hs⟩
      rw [←compl_compl U, Set.mem_compl_eq, ←hs, mem_zero_locus, Set.not_subset] at hp 
      obtain ⟨f, hfs, hfp⟩ := hp 
      refine' ⟨basic_open f, ⟨f, rfl⟩, hfp, _⟩
      rw [←Set.compl_subset_compl, ←hs, basic_open_eq_zero_locus_compl, compl_compl]
      exact zero_locus_anti_mono (set.singleton_subset_iff.mpr hfs)

theorem is_basis_basic_opens : TopologicalSpace.Opens.IsBasis (Set.Range (@basic_open R _)) :=
  by 
    unfold TopologicalSpace.Opens.IsBasis 
    convert is_topological_basis_basic_opens 
    rw [←Set.range_comp]

theorem is_compact_basic_open (f : R) : IsCompact (basic_open f : Set (PrimeSpectrum R)) :=
  is_compact_of_finite_subfamily_closed$
    fun ι Z hZc hZ =>
      by 
        let I : ι → Ideal R := fun i => vanishing_ideal (Z i)
        have hI : ∀ i, Z i = zero_locus (I i) :=
          fun i =>
            by 
              simpa only [zero_locus_vanishing_ideal_eq_closure] using (hZc i).closure_eq.symm 
        rw [basic_open_eq_zero_locus_compl f, Set.inter_comm, ←Set.diff_eq, Set.diff_eq_empty, funext hI,
          ←zero_locus_supr] at hZ 
        obtain ⟨n, hn⟩ : f ∈ (⨆i : ι, I i).radical
        ·
          rw [←vanishing_ideal_zero_locus_eq_radical]
          apply vanishing_ideal_anti_mono hZ 
          exact subset_vanishing_ideal_zero_locus {f} (Set.mem_singleton f)
        rcases Submodule.exists_finset_of_mem_supr I hn with ⟨s, hs⟩
        use s 
        simpRw [basic_open_eq_zero_locus_compl f, Set.inter_comm, ←Set.diff_eq, Set.diff_eq_empty, hI, ←zero_locus_supr]
        rw [←zero_locus_radical]
        apply zero_locus_anti_mono 
        rw [Set.singleton_subset_iff]
        exact ⟨n, hs⟩

end BasicOpen

/-- The prime spectrum of a commutative ring is a compact topological space. -/
instance  : CompactSpace (PrimeSpectrum R) :=
  { compact_univ :=
      by 
        convert is_compact_basic_open (1 : R)
        rw [basic_open_one]
        rfl }

section Order

/-!
## The specialization order

We endow `prime_spectrum R` with a partial order,
where `x ≤ y` if and only if `y ∈ closure {x}`.

TODO: maybe define sober topological spaces, and generalise this instance to those
-/


instance  : PartialOrderₓ (PrimeSpectrum R) :=
  Subtype.partialOrder _

@[simp]
theorem as_ideal_le_as_ideal (x y : PrimeSpectrum R) : x.as_ideal ≤ y.as_ideal ↔ x ≤ y :=
  Subtype.coe_le_coe

@[simp]
theorem as_ideal_lt_as_ideal (x y : PrimeSpectrum R) : x.as_ideal < y.as_ideal ↔ x < y :=
  Subtype.coe_lt_coe

theorem le_iff_mem_closure (x y : PrimeSpectrum R) : x ≤ y ↔ y ∈ Closure ({x} : Set (PrimeSpectrum R)) :=
  by 
    rw [←as_ideal_le_as_ideal, ←zero_locus_vanishing_ideal_eq_closure, mem_zero_locus, vanishing_ideal_singleton,
      SetLike.coe_subset_coe]

end Order

end PrimeSpectrum

namespace LocalRing

variable(R)[LocalRing R]

/--
The closed point in the prime spectrum of a local ring.
-/
def closed_point : PrimeSpectrum R :=
  ⟨maximal_ideal R, (maximal_ideal.is_maximal R).IsPrime⟩

variable{R}

theorem local_hom_iff_comap_closed_point {S : Type v} [CommRingₓ S] [LocalRing S] {f : R →+* S} :
  IsLocalRingHom f ↔ (closed_point S).comap f = closed_point R :=
  by 
    rw [(local_hom_tfae f).out 0 4, Subtype.ext_iff]
    rfl

end LocalRing

