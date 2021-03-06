/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Johan Commelin
-/
import Mathbin.Topology.Category.Top.Default
import Mathbin.RingTheory.GradedAlgebra.HomogeneousIdeal

/-!
# Projective spectrum of a graded ring

The projective spectrum of a graded commutative ring is the subtype of all homogenous ideals that
are prime and do not contain the irrelevant ideal.
It is naturally endowed with a topology: the Zariski topology.

## Notation
- `R` is a commutative semiring;
- `A` is a commutative ring and an `R`-algebra;
- `π : β β submodule R A` is the grading of `A`;

## Main definitions

* `projective_spectrum π`: The projective spectrum of a graded ring `A`, or equivalently, the set of
  all homogeneous ideals of `A` that is both prime and relevant i.e. not containing irrelevant
  ideal. Henceforth, we call elements of projective spectrum *relevant homogeneous prime ideals*.
* `projective_spectrum.zero_locus π s`: The zero locus of a subset `s` of `A`
  is the subset of `projective_spectrum π` consisting of all relevant homogeneous prime ideals that
  contain `s`.
* `projective_spectrum.vanishing_ideal t`: The vanishing ideal of a subset `t` of
  `projective_spectrum π` is the intersection of points in `t` (viewed as relevant homogeneous prime
  ideals).
* `projective_spectrum.Top`: the topological space of `projective_spectrum π` endowed with the
  Zariski topology

-/


noncomputable section

open DirectSum BigOperators Pointwise

open DirectSum SetLike Top TopologicalSpace CategoryTheory Opposite

variable {R A : Type _}

variable [CommSemiringβ R] [CommRingβ A] [Algebra R A]

variable (π : β β Submodule R A) [GradedAlgebra π]

/-- The projective spectrum of a graded commutative ring is the subtype of all homogenous ideals that
are prime and do not contain the irrelevant ideal.
-/
@[nolint has_inhabited_instance]
def ProjectiveSpectrum :=
  { I : HomogeneousIdeal π // I.toIdeal.IsPrime β§ Β¬HomogeneousIdeal.irrelevant π β€ I }

namespace ProjectiveSpectrum

variable {π}

/-- A method to view a point in the projective spectrum of a graded ring
as a homogeneous ideal of that ring. -/
abbrev asHomogeneousIdeal (x : ProjectiveSpectrum π) : HomogeneousIdeal π :=
  x.1

theorem as_homogeneous_ideal_def (x : ProjectiveSpectrum π) : x.asHomogeneousIdeal = x.1 :=
  rfl

instance is_prime (x : ProjectiveSpectrum π) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.2.1

@[ext]
theorem ext {x y : ProjectiveSpectrum π} : x = y β x.asHomogeneousIdeal = y.asHomogeneousIdeal :=
  Subtype.ext_iff_val

variable (π)

/-- The zero locus of a set `s` of elements of a commutative ring `A`
is the set of all relevant homogeneous prime ideals of the ring that contain the set `s`.

An element `f` of `A` can be thought of as a dependent function on the projective spectrum of `π`.
At a point `x` (a homogeneous prime ideal)
the function (i.e., element) `f` takes values in the quotient ring `A` modulo the prime ideal `x`.
In this manner, `zero_locus s` is exactly the subset of `projective_spectrum π`
where all "functions" in `s` vanish simultaneously. -/
def ZeroLocus (s : Set A) : Set (ProjectiveSpectrum π) :=
  { x | s β x.asHomogeneousIdeal }

@[simp]
theorem mem_zero_locus (x : ProjectiveSpectrum π) (s : Set A) : x β ZeroLocus π s β s β x.asHomogeneousIdeal :=
  Iff.rfl

@[simp]
theorem zero_locus_span (s : Set A) : ZeroLocus π (Ideal.span s) = ZeroLocus π s := by
  ext x
  exact (Submodule.gi _ _).gc s x.as_homogeneous_ideal.to_ideal

variable {π}

/-- The vanishing ideal of a set `t` of points
of the prime spectrum of a commutative ring `R`
is the intersection of all the prime ideals in the set `t`.

An element `f` of `A` can be thought of as a dependent function on the projective spectrum of `π`.
At a point `x` (a homogeneous prime ideal)
the function (i.e., element) `f` takes values in the quotient ring `A` modulo the prime ideal `x`.
In this manner, `vanishing_ideal t` is exactly the ideal of `A`
consisting of all "functions" that vanish on all of `t`. -/
def vanishingIdeal (t : Set (ProjectiveSpectrum π)) : HomogeneousIdeal π :=
  β¨ (x : ProjectiveSpectrum π) (h : x β t), x.asHomogeneousIdeal

theorem coe_vanishing_ideal (t : Set (ProjectiveSpectrum π)) :
    (vanishingIdeal t : Set A) = { f | β x : ProjectiveSpectrum π, x β t β f β x.asHomogeneousIdeal } := by
  ext f
  rw [vanishing_ideal, SetLike.mem_coe, β HomogeneousIdeal.mem_iff, HomogeneousIdeal.to_ideal_infi, Submodule.mem_infi]
  apply forall_congrβ fun x => _
  rw [HomogeneousIdeal.to_ideal_infi, Submodule.mem_infi, HomogeneousIdeal.mem_iff]

theorem mem_vanishing_ideal (t : Set (ProjectiveSpectrum π)) (f : A) :
    f β vanishingIdeal t β β x : ProjectiveSpectrum π, x β t β f β x.asHomogeneousIdeal := by
  rw [β SetLike.mem_coe, coe_vanishing_ideal, Set.mem_set_of_eq]

@[simp]
theorem vanishing_ideal_singleton (x : ProjectiveSpectrum π) :
    vanishingIdeal ({x} : Set (ProjectiveSpectrum π)) = x.asHomogeneousIdeal := by
  simp [β vanishing_ideal]

theorem subset_zero_locus_iff_le_vanishing_ideal (t : Set (ProjectiveSpectrum π)) (I : Ideal A) :
    t β ZeroLocus π I β I β€ (vanishingIdeal t).toIdeal :=
  β¨fun h f k => (mem_vanishing_ideal _ _).mpr fun x j => (mem_zero_locus _ _ _).mpr (h j) k, fun h => fun x j =>
    (mem_zero_locus _ _ _).mpr (le_transβ h fun f h => ((mem_vanishing_ideal _ _).mp h) x j)β©

variable (π)

/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
theorem gc_ideal :
    @GaloisConnection (Ideal A) (Set (ProjectiveSpectrum π))α΅α΅ _ _ (fun I => ZeroLocus π I) fun t =>
      (vanishingIdeal t).toIdeal :=
  fun I t => subset_zero_locus_iff_le_vanishing_ideal t I

/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
theorem gc_set :
    @GaloisConnection (Set A) (Set (ProjectiveSpectrum π))α΅α΅ _ _ (fun s => ZeroLocus π s) fun t => vanishingIdeal t :=
  by
  have ideal_gc : GaloisConnection Ideal.span coe := (Submodule.gi A _).gc
  simpa [β zero_locus_span, β Function.comp] using GaloisConnection.compose ideal_gc (gc_ideal π)

theorem gc_homogeneous_ideal :
    @GaloisConnection (HomogeneousIdeal π) (Set (ProjectiveSpectrum π))α΅α΅ _ _ (fun I => ZeroLocus π I) fun t =>
      vanishingIdeal t :=
  fun I t => by
  simpa [β show I.to_ideal β€ (vanishing_ideal t).toIdeal β I β€ vanishing_ideal t from Iff.rfl] using
    subset_zero_locus_iff_le_vanishing_ideal t I.to_ideal

theorem subset_zero_locus_iff_subset_vanishing_ideal (t : Set (ProjectiveSpectrum π)) (s : Set A) :
    t β ZeroLocus π s β s β vanishingIdeal t :=
  (gc_set _) s t

theorem subset_vanishing_ideal_zero_locus (s : Set A) : s β vanishingIdeal (ZeroLocus π s) :=
  (gc_set _).le_u_l s

theorem ideal_le_vanishing_ideal_zero_locus (I : Ideal A) : I β€ (vanishingIdeal (ZeroLocus π I)).toIdeal :=
  (gc_ideal _).le_u_l I

theorem homogeneous_ideal_le_vanishing_ideal_zero_locus (I : HomogeneousIdeal π) : I β€ vanishingIdeal (ZeroLocus π I) :=
  (gc_homogeneous_ideal _).le_u_l I

theorem subset_zero_locus_vanishing_ideal (t : Set (ProjectiveSpectrum π)) : t β ZeroLocus π (vanishingIdeal t) :=
  (gc_ideal _).l_u_le t

theorem zero_locus_anti_mono {s t : Set A} (h : s β t) : ZeroLocus π t β ZeroLocus π s :=
  (gc_set _).monotone_l h

theorem zero_locus_anti_mono_ideal {s t : Ideal A} (h : s β€ t) : ZeroLocus π (t : Set A) β ZeroLocus π (s : Set A) :=
  (gc_ideal _).monotone_l h

theorem zero_locus_anti_mono_homogeneous_ideal {s t : HomogeneousIdeal π} (h : s β€ t) :
    ZeroLocus π (t : Set A) β ZeroLocus π (s : Set A) :=
  (gc_homogeneous_ideal _).monotone_l h

theorem vanishing_ideal_anti_mono {s t : Set (ProjectiveSpectrum π)} (h : s β t) :
    vanishingIdeal t β€ vanishingIdeal s :=
  (gc_ideal _).monotone_u h

theorem zero_locus_bot : ZeroLocus π ((β₯ : Ideal A) : Set A) = Set.Univ :=
  (gc_ideal π).l_bot

@[simp]
theorem zero_locus_singleton_zero : ZeroLocus π ({0} : Set A) = Set.Univ :=
  zero_locus_bot _

@[simp]
theorem zero_locus_empty : ZeroLocus π (β : Set A) = Set.Univ :=
  (gc_set π).l_bot

@[simp]
theorem vanishing_ideal_univ : vanishingIdeal (β : Set (ProjectiveSpectrum π)) = β€ := by
  simpa using (gc_ideal _).u_top

theorem zero_locus_empty_of_one_mem {s : Set A} (h : (1 : A) β s) : ZeroLocus π s = β :=
  Set.eq_empty_iff_forall_not_mem.mpr fun x hx =>
    (inferInstance : x.asHomogeneousIdeal.toIdeal.IsPrime).ne_top <|
      x.asHomogeneousIdeal.toIdeal.eq_top_iff_one.mpr <| hx h

@[simp]
theorem zero_locus_singleton_one : ZeroLocus π ({1} : Set A) = β :=
  zero_locus_empty_of_one_mem π (Set.mem_singleton (1 : A))

@[simp]
theorem zero_locus_univ : ZeroLocus π (Set.Univ : Set A) = β :=
  zero_locus_empty_of_one_mem _ (Set.mem_univ 1)

theorem zero_locus_sup_ideal (I J : Ideal A) : ZeroLocus π ((IβJ : Ideal A) : Set A) = ZeroLocus _ I β© ZeroLocus _ J :=
  (gc_ideal π).l_sup

theorem zero_locus_sup_homogeneous_ideal (I J : HomogeneousIdeal π) :
    ZeroLocus π ((IβJ : HomogeneousIdeal π) : Set A) = ZeroLocus _ I β© ZeroLocus _ J :=
  (gc_homogeneous_ideal π).l_sup

theorem zero_locus_union (s s' : Set A) : ZeroLocus π (s βͺ s') = ZeroLocus _ s β© ZeroLocus _ s' :=
  (gc_set π).l_sup

theorem vanishing_ideal_union (t t' : Set (ProjectiveSpectrum π)) :
    vanishingIdeal (t βͺ t') = vanishingIdeal tβvanishingIdeal t' := by
  ext1 <;> convert (gc_ideal π).u_inf

theorem zero_locus_supr_ideal {Ξ³ : Sort _} (I : Ξ³ β Ideal A) :
    ZeroLocus _ ((β¨ i, I i : Ideal A) : Set A) = β i, ZeroLocus π (I i) :=
  (gc_ideal π).l_supr

theorem zero_locus_supr_homogeneous_ideal {Ξ³ : Sort _} (I : Ξ³ β HomogeneousIdeal π) :
    ZeroLocus _ ((β¨ i, I i : HomogeneousIdeal π) : Set A) = β i, ZeroLocus π (I i) :=
  (gc_homogeneous_ideal π).l_supr

theorem zero_locus_Union {Ξ³ : Sort _} (s : Ξ³ β Set A) : ZeroLocus π (β i, s i) = β i, ZeroLocus π (s i) :=
  (gc_set π).l_supr

theorem zero_locus_bUnion (s : Set (Set A)) : ZeroLocus π (β s' β s, s' : Set A) = β s' β s, ZeroLocus π s' := by
  simp only [β zero_locus_Union]

theorem vanishing_ideal_Union {Ξ³ : Sort _} (t : Ξ³ β Set (ProjectiveSpectrum π)) :
    vanishingIdeal (β i, t i) = β¨ i, vanishingIdeal (t i) :=
  HomogeneousIdeal.to_ideal_injective <| by
    convert (gc_ideal π).u_infi <;> exact HomogeneousIdeal.to_ideal_infi _

theorem zero_locus_inf (I J : Ideal A) : ZeroLocus π ((IβJ : Ideal A) : Set A) = ZeroLocus π I βͺ ZeroLocus π J :=
  Set.ext fun x => by
    simpa using x.2.1.inf_le

theorem union_zero_locus (s s' : Set A) :
    ZeroLocus π s βͺ ZeroLocus π s' = ZeroLocus π (Ideal.span sβIdeal.span s' : Ideal A) := by
  rw [zero_locus_inf]
  simp

theorem zero_locus_mul_ideal (I J : Ideal A) :
    ZeroLocus π ((I * J : Ideal A) : Set A) = ZeroLocus π I βͺ ZeroLocus π J :=
  Set.ext fun x => by
    simpa using x.2.1.mul_le

theorem zero_locus_mul_homogeneous_ideal (I J : HomogeneousIdeal π) :
    ZeroLocus π ((I * J : HomogeneousIdeal π) : Set A) = ZeroLocus π I βͺ ZeroLocus π J :=
  Set.ext fun x => by
    simpa using x.2.1.mul_le

theorem zero_locus_singleton_mul (f g : A) : ZeroLocus π ({f * g} : Set A) = ZeroLocus π {f} βͺ ZeroLocus π {g} :=
  Set.ext fun x => by
    simpa using x.2.1.mul_mem_iff_mem_or_mem

@[simp]
theorem zero_locus_singleton_pow (f : A) (n : β) (hn : 0 < n) : ZeroLocus π ({f ^ n} : Set A) = ZeroLocus π {f} :=
  Set.ext fun x => by
    simpa using x.2.1.pow_mem_iff_mem n hn

theorem sup_vanishing_ideal_le (t t' : Set (ProjectiveSpectrum π)) :
    vanishingIdeal tβvanishingIdeal t' β€ vanishingIdeal (t β© t') := by
  intro r
  rw [β HomogeneousIdeal.mem_iff, HomogeneousIdeal.to_ideal_sup, mem_vanishing_ideal, Submodule.mem_sup]
  rintro β¨f, hf, g, hg, rflβ© x β¨hxt, hxt'β©
  erw [mem_vanishing_ideal] at hf hg
  apply Submodule.add_mem <;> solve_by_elim

theorem mem_compl_zero_locus_iff_not_mem {f : A} {I : ProjectiveSpectrum π} :
    I β (ZeroLocus π {f} : Set (ProjectiveSpectrum π))αΆ β f β I.asHomogeneousIdeal := by
  rw [Set.mem_compl_eq, mem_zero_locus, Set.singleton_subset_iff] <;> rfl

/-- The Zariski topology on the prime spectrum of a commutative ring
is defined via the closed sets of the topology:
they are exactly those sets that are the zero locus of a subset of the ring. -/
instance zariskiTopology : TopologicalSpace (ProjectiveSpectrum π) :=
  TopologicalSpace.ofClosed (Set.Range (ProjectiveSpectrum.ZeroLocus π))
    β¨Set.Univ, by
      simp β©
    (by
      intro Zs h
      rw [Set.sInter_eq_Inter]
      let f : Zs β Set _ := fun i => Classical.some (h i.2)
      have hf : β i : Zs, βi = zero_locus π (f i) := fun i => (Classical.some_spec (h i.2)).symm
      simp only [β hf]
      exact β¨_, zero_locus_Union π _β©)
    (by
      rintro _ β¨s, rflβ© _ β¨t, rflβ©
      exact β¨_, (union_zero_locus π s t).symmβ©)

/-- The underlying topology of `Proj` is the projective spectrum of graded ring `A`.
-/
def top : Top :=
  Top.of (ProjectiveSpectrum π)

theorem is_open_iff (U : Set (ProjectiveSpectrum π)) : IsOpen U β β s, UαΆ = ZeroLocus π s := by
  simp only [β @eq_comm _ (UαΆ)] <;> rfl

theorem is_closed_iff_zero_locus (Z : Set (ProjectiveSpectrum π)) : IsClosed Z β β s, Z = ZeroLocus π s := by
  rw [β is_open_compl_iff, is_open_iff, compl_compl]

theorem is_closed_zero_locus (s : Set A) : IsClosed (ZeroLocus π s) := by
  rw [is_closed_iff_zero_locus]
  exact β¨s, rflβ©

theorem zero_locus_vanishing_ideal_eq_closure (t : Set (ProjectiveSpectrum π)) :
    ZeroLocus π (vanishingIdeal t : Set A) = Closure t := by
  apply Set.Subset.antisymm
  Β· rintro x hx t' β¨ht', htβ©
    obtain β¨fs, rflβ© : β s, t' = zero_locus π s := by
      rwa [is_closed_iff_zero_locus] at ht'
    rw [subset_zero_locus_iff_subset_vanishing_ideal] at ht
    exact Set.Subset.trans ht hx
    
  Β· rw [(is_closed_zero_locus _ _).closure_subset_iff]
    exact subset_zero_locus_vanishing_ideal π t
    

theorem vanishing_ideal_closure (t : Set (ProjectiveSpectrum π)) : vanishingIdeal (Closure t) = vanishingIdeal t := by
  have := (gc_ideal π).u_l_u_eq_u t
  dsimp' only  at this
  ext1
  erw [zero_locus_vanishing_ideal_eq_closure π t] at this
  exact this

section BasicOpen

/-- `basic_open r` is the open subset containing all prime ideals not containing `r`. -/
def basicOpen (r : A) : TopologicalSpace.Opens (ProjectiveSpectrum π) where
  val := { x | r β x.asHomogeneousIdeal }
  property := β¨{r}, Set.ext fun x => Set.singleton_subset_iff.trans <| not_not.symmβ©

@[simp]
theorem mem_basic_open (f : A) (x : ProjectiveSpectrum π) : x β basicOpen π f β f β x.asHomogeneousIdeal :=
  Iff.rfl

theorem mem_coe_basic_open (f : A) (x : ProjectiveSpectrum π) :
    x β (β(basicOpen π f) : Set (ProjectiveSpectrum π)) β f β x.asHomogeneousIdeal :=
  Iff.rfl

theorem is_open_basic_open {a : A} : IsOpen (basicOpen π a : Set (ProjectiveSpectrum π)) :=
  (basicOpen π a).property

@[simp]
theorem basic_open_eq_zero_locus_compl (r : A) : (basicOpen π r : Set (ProjectiveSpectrum π)) = ZeroLocus π {r}αΆ :=
  Set.ext fun x => by
    simpa only [β Set.mem_compl_eq, β mem_zero_locus, β Set.singleton_subset_iff]

@[simp]
theorem basic_open_one : basicOpen π (1 : A) = β€ :=
  TopologicalSpace.Opens.ext <| by
    simp

@[simp]
theorem basic_open_zero : basicOpen π (0 : A) = β₯ :=
  TopologicalSpace.Opens.ext <| by
    simp

theorem basic_open_mul (f g : A) : basicOpen π (f * g) = basicOpen π fβbasicOpen π g :=
  TopologicalSpace.Opens.ext <| by
    simp [β zero_locus_singleton_mul]

theorem basic_open_mul_le_left (f g : A) : basicOpen π (f * g) β€ basicOpen π f := by
  rw [basic_open_mul π f g]
  exact inf_le_left

theorem basic_open_mul_le_right (f g : A) : basicOpen π (f * g) β€ basicOpen π g := by
  rw [basic_open_mul π f g]
  exact inf_le_right

@[simp]
theorem basic_open_pow (f : A) (n : β) (hn : 0 < n) : basicOpen π (f ^ n) = basicOpen π f :=
  TopologicalSpace.Opens.ext <| by
    simpa using zero_locus_singleton_pow π f n hn

theorem basic_open_eq_union_of_projection (f : A) : basicOpen π f = β¨ i : β, basicOpen π (GradedAlgebra.proj π i f) :=
  TopologicalSpace.Opens.ext <|
    Set.ext fun z => by
      erw [mem_coe_basic_open, TopologicalSpace.Opens.mem_Sup]
      constructor <;> intro hz
      Β· rcases show β i, GradedAlgebra.proj π i f β z.as_homogeneous_ideal by
            contrapose! hz with H
            classical
            rw [β DirectSum.sum_support_decompose π f]
            apply Ideal.sum_mem _ fun i hi => H i with
          β¨i, hiβ©
        exact
          β¨basic_open π (GradedAlgebra.proj π i f), β¨i, rflβ©, by
            rwa [mem_basic_open]β©
        
      Β· obtain β¨_, β¨i, rflβ©, hzβ© := hz
        exact fun rid => hz (z.1.2 i rid)
        

theorem is_topological_basis_basic_opens :
    TopologicalSpace.IsTopologicalBasis (Set.Range fun r : A => (basicOpen π r : Set (ProjectiveSpectrum π))) := by
  apply TopologicalSpace.is_topological_basis_of_open_of_nhds
  Β· rintro _ β¨r, rflβ©
    exact is_open_basic_open π
    
  Β· rintro p U hp β¨s, hsβ©
    rw [β compl_compl U, Set.mem_compl_eq, β hs, mem_zero_locus, Set.not_subset] at hp
    obtain β¨f, hfs, hfpβ© := hp
    refine' β¨basic_open π f, β¨f, rflβ©, hfp, _β©
    rw [β Set.compl_subset_compl, β hs, basic_open_eq_zero_locus_compl, compl_compl]
    exact zero_locus_anti_mono π (set.singleton_subset_iff.mpr hfs)
    

end BasicOpen

section Order

/-!
## The specialization order

We endow `projective_spectrum π` with a partial order,
where `x β€ y` if and only if `y β closure {x}`.
-/


instance : PartialOrderβ (ProjectiveSpectrum π) :=
  Subtype.partialOrder _

@[simp]
theorem as_ideal_le_as_ideal (x y : ProjectiveSpectrum π) : x.asHomogeneousIdeal β€ y.asHomogeneousIdeal β x β€ y :=
  Subtype.coe_le_coe

@[simp]
theorem as_ideal_lt_as_ideal (x y : ProjectiveSpectrum π) : x.asHomogeneousIdeal < y.asHomogeneousIdeal β x < y :=
  Subtype.coe_lt_coe

theorem le_iff_mem_closure (x y : ProjectiveSpectrum π) : x β€ y β y β Closure ({x} : Set (ProjectiveSpectrum π)) := by
  rw [β as_ideal_le_as_ideal, β zero_locus_vanishing_ideal_eq_closure, mem_zero_locus, vanishing_ideal_singleton]
  simp only [β coe_subset_coe, β Subtype.coe_le_coe, β coe_coe]

end Order

end ProjectiveSpectrum

