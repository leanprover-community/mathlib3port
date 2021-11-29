import Mathbin.Algebra.Homology.Additive 
import Mathbin.Tactic.Abel

/-!
# Chain homotopies

We define chain homotopies, and prove that homotopic chain maps induce the same map on homology.
-/


universe v u

open_locale Classical

noncomputable theory

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {ι : Type _}

variable {V : Type u} [category.{v} V] [preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

section 

/-- The composition of `C.d i i' ≫ f i' i` if there is some `i'` coming after `i`,
and `0` otherwise. -/
def dNext (i : ι) : (∀ i j, C.X i ⟶ D.X j) →+ (C.X i ⟶ D.X i) :=
  AddMonoidHom.mk'
    (fun f =>
      match c.next i with 
      | none => 0
      | some ⟨i', w⟩ => C.d i i' ≫ f i' i)
    (by 
      intro f g 
      rcases c.next i with (_ | ⟨i', w⟩)
      exact (zero_addₓ _).symm 
      exact preadditive.comp_add _ _ _ _ _ _)

/-- `f i' i` if `i'` comes after `i`, and 0 if there's no such `i'`.
Hopefully there won't be much need for this, except in `d_next_eq_d_from_from_next`
to see that `d_next` factors through `C.d_from i`. -/
def fromNext [has_zero_object V] (i : ι) : (∀ i j, C.X i ⟶ D.X j) →+ (C.X_next i ⟶ D.X i) :=
  AddMonoidHom.mk'
    (fun f =>
      match c.next i with 
      | none => 0
      | some ⟨i', w⟩ => (C.X_next_iso w).Hom ≫ f i' i)
    (by 
      intro f g 
      rcases c.next i with (_ | ⟨i', w⟩)
      exact (zero_addₓ _).symm 
      exact preadditive.comp_add _ _ _ _ _ _)

theorem d_next_eq_d_from_from_next [has_zero_object V] (f : ∀ i j, C.X i ⟶ D.X j) (i : ι) :
  dNext i f = C.d_from i ≫ fromNext i f :=
  by 
    dsimp [dNext, fromNext]
    rcases c.next i with (⟨⟩ | ⟨⟨i', w⟩⟩) <;>
      ·
        dsimp [dNext, fromNext]
        simp 

theorem d_next_eq (f : ∀ i j, C.X i ⟶ D.X j) {i i' : ι} (w : c.rel i i') : dNext i f = C.d i i' ≫ f i' i :=
  by 
    dsimp [dNext]
    rw [c.next_eq_some w]
    rfl

@[simp]
theorem d_next_comp_left (f : C ⟶ D) (g : ∀ i j, D.X i ⟶ E.X j) (i : ι) :
  (dNext i fun i j => f.f i ≫ g i j) = f.f i ≫ dNext i g :=
  by 
    dsimp [dNext]
    rcases c.next i with (_ | ⟨i', w⟩)
    ·
      exact comp_zero.symm
    ·
      dsimp [dNext]
      simp 

@[simp]
theorem d_next_comp_right (f : ∀ i j, C.X i ⟶ D.X j) (g : D ⟶ E) (i : ι) :
  (dNext i fun i j => f i j ≫ g.f j) = dNext i f ≫ g.f i :=
  by 
    dsimp [dNext]
    rcases c.next i with (_ | ⟨i', w⟩)
    ·
      exact zero_comp.symm
    ·
      dsimp [dNext]
      simp 

/-- The composition of `f j j' ≫ D.d j' j` if there is some `j'` coming before `j`,
and `0` otherwise. -/
def prevD (j : ι) : (∀ i j, C.X i ⟶ D.X j) →+ (C.X j ⟶ D.X j) :=
  AddMonoidHom.mk'
    (fun f =>
      match c.prev j with 
      | none => 0
      | some ⟨j', w⟩ => f j j' ≫ D.d j' j)
    (by 
      intro f g 
      rcases c.prev j with (_ | ⟨j', w⟩)
      exact (zero_addₓ _).symm 
      exact preadditive.add_comp _ _ _ _ _ _)

/-- `f j j'` if `j'` comes after `j`, and 0 if there's no such `j'`.
Hopefully there won't be much need for this, except in `d_next_eq_d_from_from_next`
to see that `d_next` factors through `C.d_from i`. -/
def toPrev [has_zero_object V] (j : ι) : (∀ i j, C.X i ⟶ D.X j) →+ (C.X j ⟶ D.X_prev j) :=
  AddMonoidHom.mk'
    (fun f =>
      match c.prev j with 
      | none => 0
      | some ⟨j', w⟩ => f j j' ≫ (D.X_prev_iso w).inv)
    (by 
      intro f g 
      rcases c.prev j with (_ | ⟨j', w⟩)
      exact (zero_addₓ _).symm 
      exact preadditive.add_comp _ _ _ _ _ _)

theorem prev_d_eq_to_prev_d_to [has_zero_object V] (f : ∀ i j, C.X i ⟶ D.X j) (j : ι) :
  prevD j f = toPrev j f ≫ D.d_to j :=
  by 
    dsimp [prevD, toPrev]
    rcases c.prev j with (⟨⟩ | ⟨⟨j', w⟩⟩) <;>
      ·
        dsimp [prevD, toPrev]
        simp 

theorem prev_d_eq (f : ∀ i j, C.X i ⟶ D.X j) {j j' : ι} (w : c.rel j' j) : prevD j f = f j j' ≫ D.d j' j :=
  by 
    dsimp [prevD]
    rw [c.prev_eq_some w]
    rfl

@[simp]
theorem prev_d_comp_left (f : C ⟶ D) (g : ∀ i j, D.X i ⟶ E.X j) (j : ι) :
  (prevD j fun i j => f.f i ≫ g i j) = f.f j ≫ prevD j g :=
  by 
    dsimp [prevD]
    rcases c.prev j with (_ | ⟨j', w⟩)
    ·
      exact comp_zero.symm
    ·
      dsimp [prevD, hom.prev]
      simp 

@[simp]
theorem to_prev'_comp_right (f : ∀ i j, C.X i ⟶ D.X j) (g : D ⟶ E) (j : ι) :
  (prevD j fun i j => f i j ≫ g.f j) = prevD j f ≫ g.f j :=
  by 
    dsimp [prevD]
    rcases c.prev j with (_ | ⟨j', w⟩)
    ·
      exact zero_comp.symm
    ·
      dsimp [prevD]
      simp 

theorem d_next_nat (C D : ChainComplex V ℕ) (i : ℕ) (f : ∀ i j, C.X i ⟶ D.X j) :
  dNext i f = C.d i (i - 1) ≫ f (i - 1) i :=
  by 
    cases i
    ·
      dsimp [dNext]
      rcases(ComplexShape.down ℕ).next 0 with (_ | ⟨j, hj⟩) <;> dsimp [dNext]
      ·
        rw [C.shape, zero_comp]
        dsimp 
        decide
      ·
        dsimp  at hj 
        exact (Nat.succ_ne_zero _ hj).elim 
    rw [d_next_eq]
    dsimp 
    rfl

theorem prev_d_nat (C D : CochainComplex V ℕ) (i : ℕ) (f : ∀ i j, C.X i ⟶ D.X j) :
  prevD i f = f i (i - 1) ≫ D.d (i - 1) i :=
  by 
    cases i
    ·
      dsimp [prevD]
      rcases(ComplexShape.up ℕ).prev 0 with (_ | ⟨j, hj⟩) <;> dsimp [prevD]
      ·
        rw [D.shape, comp_zero]
        dsimp 
        decide
      ·
        dsimp  at hj 
        exact (Nat.succ_ne_zero _ hj).elim 
    rw [prev_d_eq]
    dsimp 
    rfl

/--
A homotopy `h` between chain maps `f` and `g` consists of components `h i j : C.X i ⟶ D.X j`
which are zero unless `c.rel j i`, satisfying the homotopy condition.
-/
@[ext, nolint has_inhabited_instance]
structure Homotopy (f g : C ⟶ D) where 
  Hom : ∀ i j, C.X i ⟶ D.X j 
  zero' : ∀ i j, ¬c.rel j i → hom i j = 0 :=  by 
  runTac 
    obviously 
  comm : ∀ i, f.f i = (dNext i hom+prevD i hom)+g.f i :=  by 
  runTac 
    obviously'

variable {f g}

namespace Homotopy

restate_axiom Homotopy.zero'

/--
`f` is homotopic to `g` iff `f - g` is homotopic to `0`.
-/
def equiv_sub_zero : Homotopy f g ≃ Homotopy (f - g) 0 :=
  { toFun :=
      fun h =>
        { Hom := fun i j => h.hom i j, zero' := fun i j w => h.zero _ _ w,
          comm :=
            fun i =>
              by 
                simp [h.comm] },
    invFun :=
      fun h =>
        { Hom := fun i j => h.hom i j, zero' := fun i j w => h.zero _ _ w,
          comm :=
            fun i =>
              by 
                simpa [sub_eq_iff_eq_add] using h.comm i },
    left_inv :=
      by 
        tidy,
    right_inv :=
      by 
        tidy }

/-- Equal chain maps are homotopic. -/
@[simps]
def of_eq (h : f = g) : Homotopy f g :=
  { Hom := 0, zero' := fun _ _ _ => rfl,
    comm :=
      fun _ =>
        by 
          simp only [AddMonoidHom.map_zero, zero_addₓ, h] }

/-- Every chain map is homotopic to itself. -/
@[simps, refl]
def refl (f : C ⟶ D) : Homotopy f f :=
  of_eq (rfl : f = f)

/-- `f` is homotopic to `g` iff `g` is homotopic to `f`. -/
@[simps, symm]
def symm {f g : C ⟶ D} (h : Homotopy f g) : Homotopy g f :=
  { Hom := -h.hom,
    zero' :=
      fun i j w =>
        by 
          rw [Pi.neg_apply, Pi.neg_apply, h.zero i j w, neg_zero],
    comm :=
      fun i =>
        by 
          rw [AddMonoidHom.map_neg, AddMonoidHom.map_neg, h.comm, ←neg_add, ←add_assocₓ, neg_add_selfₓ, zero_addₓ] }

/-- homotopy is a transitive relation. -/
@[simps, trans]
def trans {e f g : C ⟶ D} (h : Homotopy e f) (k : Homotopy f g) : Homotopy e g :=
  { Hom := h.hom+k.hom,
    zero' :=
      fun i j w =>
        by 
          rw [Pi.add_apply, Pi.add_apply, h.zero i j w, k.zero i j w, zero_addₓ],
    comm :=
      fun i =>
        by 
          rw [AddMonoidHom.map_add, AddMonoidHom.map_add, h.comm, k.comm]
          abel }

/-- homotopy is closed under composition (on the right) -/
@[simps]
def comp_right {e f : C ⟶ D} (h : Homotopy e f) (g : D ⟶ E) : Homotopy (e ≫ g) (f ≫ g) :=
  { Hom := fun i j => h.hom i j ≫ g.f j,
    zero' :=
      fun i j w =>
        by 
          rw [h.zero i j w, zero_comp],
    comm :=
      fun i =>
        by 
          simp only [h.comm i, d_next_comp_right, preadditive.add_comp, to_prev'_comp_right, comp_f] }

/-- homotopy is closed under composition (on the left) -/
@[simps]
def comp_left {f g : D ⟶ E} (h : Homotopy f g) (e : C ⟶ D) : Homotopy (e ≫ f) (e ≫ g) :=
  { Hom := fun i j => e.f i ≫ h.hom i j,
    zero' :=
      fun i j w =>
        by 
          rw [h.zero i j w, comp_zero],
    comm :=
      fun i =>
        by 
          simp only [h.comm i, d_next_comp_left, preadditive.comp_add, prev_d_comp_left, comp_f] }

/-- homotopy is closed under composition -/
@[simps]
def comp {C₁ C₂ C₃ : HomologicalComplex V c} {f₁ g₁ : C₁ ⟶ C₂} {f₂ g₂ : C₂ ⟶ C₃} (h₁ : Homotopy f₁ g₁)
  (h₂ : Homotopy f₂ g₂) : Homotopy (f₁ ≫ f₂) (g₁ ≫ g₂) :=
  (h₁.comp_right _).trans (h₂.comp_left _)

/-- a variant of `homotopy.comp_right` useful for dealing with homotopy equivalences. -/
@[simps]
def comp_right_id {f : C ⟶ C} (h : Homotopy f (𝟙 C)) (g : C ⟶ D) : Homotopy (f ≫ g) g :=
  (h.comp_right g).trans (of_eq$ category.id_comp _)

/-- a variant of `homotopy.comp_left` useful for dealing with homotopy equivalences. -/
@[simps]
def comp_left_id {f : D ⟶ D} (h : Homotopy f (𝟙 D)) (g : C ⟶ D) : Homotopy (g ≫ f) g :=
  (h.comp_left g).trans (of_eq$ category.comp_id _)

/-!
`homotopy.mk_inductive` allows us to build a homotopy inductively,
so that as we construct each component, we have available the previous two components,
and the fact that they satisfy the homotopy condition.

To simplify the situation, we only construct homotopies of the form `homotopy e 0`.
`homotopy.equiv_sub_zero` can provide the general case.

Notice however, that this construction does not have particularly good definitional properties:
we have to insert `eq_to_hom` in several places.
Hopefully this is okay in most applications, where we only need to have the existence of some
homotopy.
-/


section MkInductive

variable {P Q : ChainComplex V ℕ}

@[simp]
theorem prev_d_chain_complex (f : ∀ i j, P.X i ⟶ Q.X j) (j : ℕ) : prevD j f = f j (j+1) ≫ Q.d _ _ :=
  by 
    dsimp [prevD]
    simp only [ChainComplex.prev]
    rfl

@[simp]
theorem d_next_succ_chain_complex (f : ∀ i j, P.X i ⟶ Q.X j) (i : ℕ) : dNext (i+1) f = P.d _ _ ≫ f i (i+1) :=
  by 
    dsimp [dNext]
    simp only [ChainComplex.next_nat_succ]
    rfl

@[simp]
theorem d_next_zero_chain_complex (f : ∀ i j, P.X i ⟶ Q.X j) : dNext 0 f = 0 :=
  by 
    dsimp [dNext]
    simp only [ChainComplex.next_nat_zero]
    rfl

variable (e : P ⟶ Q) (zero : P.X 0 ⟶ Q.X 1) (comm_zero : e.f 0 = zero ≫ Q.d 1 0) (one : P.X 1 ⟶ Q.X 2)
  (comm_one : e.f 1 = (P.d 1 0 ≫ zero)+one ≫ Q.d 2 1)
  (succ :
    ∀ n : ℕ p :
      Σ'(f : P.X n ⟶ Q.X (n+1))(f' : P.X (n+1) ⟶ Q.X (n+2)), e.f (n+1) = (P.d (n+1) n ≫ f)+f' ≫ Q.d (n+2) (n+1),
      Σ'f'' : P.X (n+2) ⟶ Q.X (n+3), e.f (n+2) = (P.d (n+2) (n+1) ≫ p.2.1)+f'' ≫ Q.d (n+3) (n+2))

include comm_one comm_zero

/--
An auxiliary construction for `mk_inductive`.

Here we build by induction a family of diagrams,
but don't require at the type level that these successive diagrams actually agree.
They do in fact agree, and we then capture that at the type level (i.e. by constructing a homotopy)
in `mk_inductive`.

At this stage, we don't check the homotopy condition in degree 0,
because it "falls off the end", and is easier to treat using `X_next` and `X_prev`,
which we do in `mk_inductive_aux₂`.
-/
@[simp, nolint unused_arguments]
def mk_inductive_aux₁ :
  ∀ n, Σ'(f : P.X n ⟶ Q.X (n+1))(f' : P.X (n+1) ⟶ Q.X (n+2)), e.f (n+1) = (P.d (n+1) n ≫ f)+f' ≫ Q.d (n+2) (n+1)
| 0 => ⟨zero, one, comm_one⟩
| 1 => ⟨one, (succ 0 ⟨zero, one, comm_one⟩).1, (succ 0 ⟨zero, one, comm_one⟩).2⟩
| n+2 =>
  ⟨(mk_inductive_aux₁ (n+1)).2.1, (succ (n+1) (mk_inductive_aux₁ (n+1))).1, (succ (n+1) (mk_inductive_aux₁ (n+1))).2⟩

section 

variable [has_zero_object V]

/--
An auxiliary construction for `mk_inductive`.
-/
@[simp]
def mk_inductive_aux₂ : ∀ n, Σ'(f : P.X_next n ⟶ Q.X n)(f' : P.X n ⟶ Q.X_prev n), e.f n = (P.d_from n ≫ f)+f' ≫ Q.d_to n
| 0 =>
  ⟨0, zero ≫ (Q.X_prev_iso rfl).inv,
    by 
      simpa using comm_zero⟩
| n+1 =>
  let I := mk_inductive_aux₁ e zero comm_zero one comm_one succ n
  ⟨(P.X_next_iso rfl).Hom ≫ I.1, I.2.1 ≫ (Q.X_prev_iso rfl).inv,
    by 
      simpa using I.2.2⟩

theorem mk_inductive_aux₃ (i : ℕ) :
  (mk_inductive_aux₂ e zero comm_zero one comm_one succ i).2.1 ≫ (Q.X_prev_iso rfl).Hom =
    (P.X_next_iso rfl).inv ≫ (mk_inductive_aux₂ e zero comm_zero one comm_one succ (i+1)).1 :=
  by 
    rcases i with (_ | _ | i) <;>
      ·
        dsimp 
        simp 

/--
A constructor for a `homotopy e 0`, for `e` a chain map between `ℕ`-indexed chain complexes,
working by induction.

You need to provide the components of the homotopy in degrees 0 and 1,
show that these satisfy the homotopy condition,
and then give a construction of each component,
and the fact that it satisfies the homotopy condition,
using as an inductive hypothesis the data and homotopy condition for the previous two components.
-/
def mk_inductive : Homotopy e 0 :=
  { Hom :=
      fun i j =>
        if h : (i+1) = j then (mk_inductive_aux₂ e zero comm_zero one comm_one succ i).2.1 ≫ (Q.X_prev_iso h).Hom else
          0,
    zero' :=
      fun i j w =>
        by 
          rwa [dif_neg],
    comm :=
      fun i =>
        by 
          dsimp 
          simp only [add_zeroₓ]
          convert (mk_inductive_aux₂ e zero comm_zero one comm_one succ i).2.2
          ·
            rcases i with (_ | _ | _ | i)
            ·
              dsimp 
              simp only [d_next_zero_chain_complex, d_from_eq_zero, limits.comp_zero]
            all_goals 
              simp only [d_next_succ_chain_complex]
              dsimp 
              simp only [category.comp_id, category.assoc, iso.inv_hom_id, d_from_comp_X_next_iso_assoc, dite_eq_ite,
                if_true, eq_self_iff_true]
          ·
            cases i 
            all_goals 
              simp only [prev_d_chain_complex]
              dsimp 
              simp only [category.comp_id, category.assoc, iso.inv_hom_id, X_prev_iso_comp_d_to, dite_eq_ite, if_true,
                eq_self_iff_true] }

end 

end MkInductive

end Homotopy

/--
A homotopy equivalence between two chain complexes consists of a chain map each way,
and homotopies from the compositions to the identity chain maps.

Note that this contains data;
arguably it might be more useful for many applications if we truncated it to a Prop.
-/
structure HomotopyEquiv (C D : HomologicalComplex V c) where 
  Hom : C ⟶ D 
  inv : D ⟶ C 
  homotopyHomInvId : Homotopy (hom ≫ inv) (𝟙 C)
  homotopyInvHomId : Homotopy (inv ≫ hom) (𝟙 D)

namespace HomotopyEquiv

/-- Any complex is homotopy equivalent to itself. -/
@[refl]
def refl (C : HomologicalComplex V c) : HomotopyEquiv C C :=
  { Hom := 𝟙 C, inv := 𝟙 C,
    homotopyHomInvId :=
      by 
        simp ,
    homotopyInvHomId :=
      by 
        simp  }

instance : Inhabited (HomotopyEquiv C C) :=
  ⟨refl C⟩

/-- Being homotopy equivalent is a symmetric relation. -/
@[symm]
def symm {C D : HomologicalComplex V c} (f : HomotopyEquiv C D) : HomotopyEquiv D C :=
  { Hom := f.inv, inv := f.hom, homotopyHomInvId := f.homotopy_inv_hom_id, homotopyInvHomId := f.homotopy_hom_inv_id }

/-- Homotopy equivalence is a transitive relation. -/
@[trans]
def trans {C D E : HomologicalComplex V c} (f : HomotopyEquiv C D) (g : HomotopyEquiv D E) : HomotopyEquiv C E :=
  { Hom := f.hom ≫ g.hom, inv := g.inv ≫ f.inv,
    homotopyHomInvId :=
      by 
        simpa using ((g.homotopy_hom_inv_id.comp_right_id f.inv).compLeft f.hom).trans f.homotopy_hom_inv_id,
    homotopyInvHomId :=
      by 
        simpa using ((f.homotopy_inv_hom_id.comp_right_id g.hom).compLeft g.inv).trans g.homotopy_inv_hom_id }

end HomotopyEquiv

variable [has_equalizers V] [has_cokernels V] [has_images V] [has_image_maps V]

variable [has_zero_object V]

/--
Homotopic maps induce the same map on homology.
-/
theorem homology_map_eq_of_homotopy (h : Homotopy f g) (i : ι) :
  (homologyFunctor V c i).map f = (homologyFunctor V c i).map g :=
  by 
    dsimp [homologyFunctor]
    apply eq_of_sub_eq_zero 
    ext 
    simp only [homology.π_map, comp_zero, preadditive.comp_sub]
    dsimp [kernel_subobject_map]
    simpRw [h.comm i]
    simp only [zero_addₓ, zero_comp, d_next_eq_d_from_from_next, kernel_subobject_arrow_comp_assoc,
      preadditive.comp_add]
    rw [←preadditive.sub_comp]
    simp only [CategoryTheory.Subobject.factor_thru_add_sub_factor_thru_right]
    erw [subobject.factor_thru_of_le (D.boundaries_le_cycles i)]
    ·
      simp 
    ·
      rw [prev_d_eq_to_prev_d_to, ←category.assoc]
      apply image_subobject_factors_comp_self

/-- Homotopy equivalent complexes have isomorphic homologies. -/
def homologyObjIsoOfHomotopyEquiv (f : HomotopyEquiv C D) (i : ι) :
  (homologyFunctor V c i).obj C ≅ (homologyFunctor V c i).obj D :=
  { Hom := (homologyFunctor V c i).map f.hom, inv := (homologyFunctor V c i).map f.inv,
    hom_inv_id' :=
      by 
        rw [←functor.map_comp, homology_map_eq_of_homotopy f.homotopy_hom_inv_id, CategoryTheory.Functor.map_id],
    inv_hom_id' :=
      by 
        rw [←functor.map_comp, homology_map_eq_of_homotopy f.homotopy_inv_hom_id, CategoryTheory.Functor.map_id] }

end 

namespace CategoryTheory

variable {W : Type _} [category W] [preadditive W]

-- error in Algebra.Homology.Homotopy: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An additive functor takes homotopies to homotopies. -/
@[simps #[]]
def functor.map_homotopy
(F : «expr ⥤ »(V, W))
[F.additive]
{f g : «expr ⟶ »(C, D)}
(h : homotopy f g) : homotopy ((F.map_homological_complex c).map f) ((F.map_homological_complex c).map g) :=
{ hom := λ i j, F.map (h.hom i j),
  zero' := λ i j w, by { rw ["[", expr h.zero i j w, ",", expr F.map_zero, "]"] [] },
  comm := λ i, begin
    have [] [] [":=", expr h.comm i],
    dsimp [] ["[", expr d_next, ",", expr prev_d, "]"] [] ["at", "*"],
    rcases [expr c.next i, "with", "_", "|", "⟨", ident inext, ",", ident wn, "⟩"]; rcases [expr c.prev i, "with", "_", "|", "⟨", ident iprev, ",", ident wp, "⟩"]; dsimp [] ["[", expr d_next, ",", expr prev_d, "]"] [] ["at", "*"]; { intro [ident h],
      simp [] [] [] ["[", expr h, "]"] [] [] }
  end }

/-- An additive functor preserves homotopy equivalences. -/
@[simps]
def functor.map_homotopy_equiv (F : V ⥤ W) [F.additive] (h : HomotopyEquiv C D) :
  HomotopyEquiv ((F.map_homological_complex c).obj C) ((F.map_homological_complex c).obj D) :=
  { Hom := (F.map_homological_complex c).map h.hom, inv := (F.map_homological_complex c).map h.inv,
    homotopyHomInvId :=
      by 
        rw [←(F.map_homological_complex c).map_comp, ←(F.map_homological_complex c).map_id]
        exact F.map_homotopy h.homotopy_hom_inv_id,
    homotopyInvHomId :=
      by 
        rw [←(F.map_homological_complex c).map_comp, ←(F.map_homological_complex c).map_id]
        exact F.map_homotopy h.homotopy_inv_hom_id }

end CategoryTheory

