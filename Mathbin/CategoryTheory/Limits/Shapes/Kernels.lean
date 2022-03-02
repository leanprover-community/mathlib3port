/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Kernels and cokernels

In a category with zero morphisms, the kernel of a morphism `f : X ⟶ Y` is
the equalizer of `f` and `0 : X ⟶ Y`. (Similarly the cokernel is the coequalizer.)

The basic definitions are
* `kernel : (X ⟶ Y) → C`
* `kernel.ι : kernel f ⟶ X`
* `kernel.condition : kernel.ι f ≫ f = 0` and
* `kernel.lift (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f` (as well as the dual versions)

## Main statements

Besides the definition and lifts, we prove
* `kernel.ι_zero_is_iso`: a kernel map of a zero morphism is an isomorphism
* `kernel.eq_zero_of_epi_kernel`: if `kernel.ι f` is an epimorphism, then `f = 0`
* `kernel.of_mono`: the kernel of a monomorphism is the zero object
* `kernel.lift_mono`: the lift of a monomorphism `k : W ⟶ X` such that `k ≫ f = 0`
  is still a monomorphism
* `kernel.is_limit_cone_zero_cone`: if our category has a zero object, then the map from the zero
  obect is a kernel map of any monomorphism
* `kernel.ι_of_zero`: `kernel.ι (0 : X ⟶ Y)` is an isomorphism

and the corresponding dual statements.

## Future work
* TODO: connect this with existing working in the group theory and ring theory libraries.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/


noncomputable section

universe v u u'

open CategoryTheory

open CategoryTheory.Limits.WalkingParallelPair

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

variable [HasZeroMorphisms C]

/-- A morphism `f` has a kernel if the functor `parallel_pair f 0` has a limit. -/
abbrev HasKernel {X Y : C} (f : X ⟶ Y) : Prop :=
  HasLimit (parallelPair f 0)

/-- A morphism `f` has a cokernel if the functor `parallel_pair f 0` has a colimit. -/
abbrev HasCokernel {X Y : C} (f : X ⟶ Y) : Prop :=
  HasColimit (parallelPair f 0)

variable {X Y : C} (f : X ⟶ Y)

section

/-- A kernel fork is just a fork where the second morphism is a zero morphism. -/
abbrev KernelFork :=
  Fork f 0

variable {f}

@[simp, reassoc]
theorem KernelFork.condition (s : KernelFork f) : Fork.ι s ≫ f = 0 := by
  erw [fork.condition, has_zero_morphisms.comp_zero]

@[simp]
theorem KernelFork.app_one (s : KernelFork f) : s.π.app one = 0 := by
  rw [← fork.app_zero_left, kernel_fork.condition]

/-- A morphism `ι` satisfying `ι ≫ f = 0` determines a kernel fork over `f`. -/
abbrev KernelFork.ofι {Z : C} (ι : Z ⟶ X) (w : ι ≫ f = 0) : KernelFork f :=
  Fork.ofι ι <| by
    rw [w, has_zero_morphisms.comp_zero]

@[simp]
theorem KernelFork.ι_of_ι {X Y P : C} (f : X ⟶ Y) (ι : P ⟶ X) (w : ι ≫ f = 0) : Fork.ι (KernelFork.ofι ι w) = ι :=
  rfl

section

attribute [local tidy] tactic.case_bash

/-- Every kernel fork `s` is isomorphic (actually, equal) to `fork.of_ι (fork.ι s) _`. -/
def isoOfι (s : Fork f 0) : s ≅ Fork.ofι (Fork.ι s) (Fork.condition s) :=
  Cones.ext (Iso.refl _) <| by
    tidy

/-- If `ι = ι'`, then `fork.of_ι ι _` and `fork.of_ι ι' _` are isomorphic. -/
def ofιCongr {P : C} {ι ι' : P ⟶ X} {w : ι ≫ f = 0} (h : ι = ι') :
    KernelFork.ofι ι w ≅
      KernelFork.ofι ι'
        (by
          rw [← h, w]) :=
  Cones.ext (Iso.refl _) <| by
    tidy

/-- If `F` is an equivalence, then applying `F` to a diagram indexing a (co)kernel of `f` yields
    the diagram indexing the (co)kernel of `F.map f`. -/
def compNatIso {D : Type u'} [Category.{v} D] [HasZeroMorphisms D] (F : C ⥤ D) [IsEquivalence F] :
    parallelPair f 0 ⋙ F ≅ parallelPair (F.map f) 0 :=
  (NatIso.ofComponents fun j =>
      match j with
      | zero => Iso.refl _
      | one => Iso.refl _) <|
    by
    tidy

end

/-- If `s` is a limit kernel fork and `k : W ⟶ X` satisfies ``k ≫ f = 0`, then there is some
    `l : W ⟶ s.X` such that `l ≫ fork.ι s = k`. -/
def KernelFork.IsLimit.lift' {s : KernelFork f} (hs : IsLimit s) {W : C} (k : W ⟶ X) (h : k ≫ f = 0) :
    { l : W ⟶ s.x // l ≫ Fork.ι s = k } :=
  ⟨hs.lift <| KernelFork.ofι _ h, hs.fac _ _⟩

/-- This is a slightly more convenient method to verify that a kernel fork is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def isLimitAux (t : KernelFork f) (lift : ∀ s : KernelFork f, s.x ⟶ t.x) (fac : ∀ s : KernelFork f, lift s ≫ t.ι = s.ι)
    (uniq : ∀ s : KernelFork f m : s.x ⟶ t.x w : m ≫ t.ι = s.ι, m = lift s) : IsLimit t :=
  { lift,
    fac' := fun s j => by
      cases j
      · exact fac s
        
      · simp
        ,
    uniq' := fun s m w => uniq s m (w Limits.WalkingParallelPair.zero) }

/-- This is a more convenient formulation to show that a `kernel_fork` constructed using
`kernel_fork.of_ι` is a limit cone.
-/
def IsLimit.ofι {W : C} (g : W ⟶ X) (eq : g ≫ f = 0) (lift : ∀ {W' : C} g' : W' ⟶ X eq' : g' ≫ f = 0, W' ⟶ W)
    (fac : ∀ {W' : C} g' : W' ⟶ X eq' : g' ≫ f = 0, lift g' eq' ≫ g = g')
    (uniq : ∀ {W' : C} g' : W' ⟶ X eq' : g' ≫ f = 0 m : W' ⟶ W w : m ≫ g = g', m = lift g' eq') :
    IsLimit (KernelFork.ofι g Eq) :=
  isLimitAux _ (fun s => lift s.ι s.condition) (fun s => fac s.ι s.condition) fun s => uniq s.ι s.condition

end

section

variable [HasKernel f]

/-- The kernel of a morphism, expressed as the equalizer with the 0 morphism. -/
abbrev kernel : C :=
  equalizer f 0

/-- The map from `kernel f` into the source of `f`. -/
abbrev kernel.ι : kernel f ⟶ X :=
  equalizer.ι f 0

@[simp]
theorem equalizer_as_kernel : equalizer.ι f 0 = kernel.ι f :=
  rfl

@[simp, reassoc]
theorem kernel.condition : kernel.ι f ≫ f = 0 :=
  KernelFork.condition _

/-- Given any morphism `k : W ⟶ X` satisfying `k ≫ f = 0`, `k` factors through `kernel.ι f`
    via `kernel.lift : W ⟶ kernel f`. -/
abbrev kernel.lift {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f :=
  limit.lift (parallelPair f 0) (KernelFork.ofι k h)

@[simp, reassoc]
theorem kernel.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : kernel.lift f k h ≫ kernel.ι f = k :=
  limit.lift_π _ _

@[simp]
theorem kernel.lift_zero {W : C} {h} : kernel.lift f (0 : W ⟶ X) h = 0 := by
  ext
  simp

instance kernel.lift_mono {W : C} (k : W ⟶ X) (h : k ≫ f = 0) [Mono k] : Mono (kernel.lift f k h) :=
  ⟨fun Z g g' w => by
    replace w := w =≫ kernel.ι f
    simp only [category.assoc, kernel.lift_ι] at w
    exact (cancel_mono k).1 w⟩

/-- Any morphism `k : W ⟶ X` satisfying `k ≫ f = 0` induces a morphism `l : W ⟶ kernel f` such that
    `l ≫ kernel.ι f = k`. -/
def kernel.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : { l : W ⟶ kernel f // l ≫ kernel.ι f = k } :=
  ⟨kernel.lift f k h, kernel.lift_ι _ _ _⟩

/-- A commuting square induces a morphism of kernels. -/
abbrev kernel.map {X' Y' : C} (f' : X' ⟶ Y') [HasKernel f'] (p : X ⟶ X') (q : Y ⟶ Y') (w : f ≫ q = p ≫ f') :
    kernel f ⟶ kernel f' :=
  kernel.lift f' (kernel.ι f ≫ p)
    (by
      simp [← w])

/-- Given a commutative diagram
    X --f--> Y --g--> Z
    |        |        |
    |        |        |
    v        v        v
    X' -f'-> Y' -g'-> Z'
with horizontal arrows composing to zero,
then we obtain a commutative square
   X ---> kernel g
   |         |
   |         | kernel.map
   |         |
   v         v
   X' --> kernel g'
-/
theorem kernel.lift_map {X Y Z X' Y' Z' : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel g] (w : f ≫ g = 0) (f' : X' ⟶ Y')
    (g' : Y' ⟶ Z') [HasKernel g'] (w' : f' ≫ g' = 0) (p : X ⟶ X') (q : Y ⟶ Y') (r : Z ⟶ Z') (h₁ : f ≫ q = p ≫ f')
    (h₂ : g ≫ r = q ≫ g') : kernel.lift g f w ≫ kernel.map g g' q r h₂ = p ≫ kernel.lift g' f' w' := by
  ext
  simp [h₁]

/-- Every kernel of the zero morphism is an isomorphism -/
instance kernel.ι_zero_is_iso : IsIso (kernel.ι (0 : X ⟶ Y)) :=
  equalizer.ι_of_self _

theorem eq_zero_of_epi_kernel [Epi (kernel.ι f)] : f = 0 :=
  (cancel_epi (kernel.ι f)).1
    (by
      simp )

/-- The kernel of a zero morphism is isomorphic to the source. -/
def kernelZeroIsoSource : kernel (0 : X ⟶ Y) ≅ X :=
  equalizer.isoSourceOfSelf 0

@[simp]
theorem kernel_zero_iso_source_hom : kernelZeroIsoSource.Hom = kernel.ι (0 : X ⟶ Y) :=
  rfl

@[simp]
theorem kernel_zero_iso_source_inv :
    kernelZeroIsoSource.inv =
      kernel.lift (0 : X ⟶ Y) (𝟙 X)
        (by
          simp ) :=
  by
  ext
  simp [kernel_zero_iso_source]

/-- If two morphisms are known to be equal, then their kernels are isomorphic. -/
def kernelIsoOfEq {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) : kernel f ≅ kernel g :=
  HasLimit.isoOfNatIso
    (by
      simp [h])

@[simp]
theorem kernel_iso_of_eq_refl {h : f = f} : kernelIsoOfEq h = Iso.refl (kernel f) := by
  ext
  simp [kernel_iso_of_eq]

@[simp, reassoc]
theorem kernel_iso_of_eq_hom_comp_ι {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) :
    (kernelIsoOfEq h).Hom ≫ kernel.ι _ = kernel.ι _ := by
  induction h
  simp

@[simp, reassoc]
theorem kernel_iso_of_eq_inv_comp_ι {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) :
    (kernelIsoOfEq h).inv ≫ kernel.ι _ = kernel.ι _ := by
  induction h
  simp

@[simp, reassoc]
theorem lift_comp_kernel_iso_of_eq_hom {Z} {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) (e : Z ⟶ X) he :
    kernel.lift _ e he ≫ (kernelIsoOfEq h).Hom =
      kernel.lift _ e
        (by
          simp [← h, he]) :=
  by
  induction h
  simp

@[simp, reassoc]
theorem lift_comp_kernel_iso_of_eq_inv {Z} {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) (e : Z ⟶ X) he :
    kernel.lift _ e he ≫ (kernelIsoOfEq h).inv =
      kernel.lift _ e
        (by
          simp [h, he]) :=
  by
  induction h
  simp

@[simp]
theorem kernel_iso_of_eq_trans {f g h : X ⟶ Y} [HasKernel f] [HasKernel g] [HasKernel h] (w₁ : f = g) (w₂ : g = h) :
    kernelIsoOfEq w₁ ≪≫ kernelIsoOfEq w₂ = kernelIsoOfEq (w₁.trans w₂) := by
  induction w₁
  induction w₂
  ext
  simp [kernel_iso_of_eq]

variable {f}

theorem kernel_not_epi_of_nonzero (w : f ≠ 0) : ¬Epi (kernel.ι f) := fun I => w (eq_zero_of_epi_kernel f)

theorem kernel_not_iso_of_nonzero (w : f ≠ 0) : IsIso (kernel.ι f) → False := fun I =>
  kernel_not_epi_of_nonzero w <| by
    skip
    infer_instance

-- TODO the remainder of this section has obvious generalizations to `has_equalizer f g`.
instance has_kernel_comp_mono {X Y Z : C} (f : X ⟶ Y) [HasKernel f] (g : Y ⟶ Z) [Mono g] : HasKernel (f ≫ g) where
  exists_limit :=
    ⟨{ Cone :=
          KernelFork.ofι (kernel.ι f)
            (by
              simp ),
        IsLimit :=
          isLimitAux _
            (fun s =>
              kernel.lift _ s.ι
                ((cancel_mono g).mp
                  (by
                    simp )))
            (by
              tidy)
            (by
              tidy) }⟩

/-- When `g` is a monomorphism, the kernel of `f ≫ g` is isomorphic to the kernel of `f`.
-/
@[simps]
def kernelCompMono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel f] [Mono g] : kernel (f ≫ g) ≅ kernel f where
  Hom :=
    kernel.lift _ (kernel.ι _)
      (by
        rw [← cancel_mono g]
        simp )
  inv :=
    kernel.lift _ (kernel.ι _)
      (by
        simp )

instance has_kernel_iso_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [HasKernel g] : HasKernel (f ≫ g) where
  exists_limit :=
    ⟨{ Cone :=
          KernelFork.ofι (kernel.ι g ≫ inv f)
            (by
              simp ),
        IsLimit :=
          isLimitAux _
            (fun s =>
              kernel.lift _ (s.ι ≫ f)
                (by
                  tidy))
            (by
              tidy)
            fun s m w => by
            simp_rw [← w]
            ext
            simp }⟩

/-- When `f` is an isomorphism, the kernel of `f ≫ g` is isomorphic to the kernel of `g`.
-/
@[simps]
def kernelIsIsoComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [HasKernel g] : kernel (f ≫ g) ≅ kernel g where
  Hom :=
    kernel.lift _ (kernel.ι _ ≫ f)
      (by
        simp )
  inv :=
    kernel.lift _ (kernel.ι _ ≫ inv f)
      (by
        simp )

end

section HasZeroObject

variable [HasZeroObject C]

open_locale ZeroObject

/-- The morphism from the zero object determines a cone on a kernel diagram -/
def kernel.zeroCone : Cone (parallelPair f 0) where
  x := 0
  π := { app := fun j => 0 }

/-- The map from the zero object is a kernel of a monomorphism -/
def kernel.isLimitConeZeroCone [Mono f] : IsLimit (kernel.zeroCone f) :=
  Fork.IsLimit.mk _ (fun s => 0)
    (fun s => by
      erw [zero_comp]
      convert (zero_of_comp_mono f _).symm
      exact kernel_fork.condition _)
    fun _ _ _ => zero_of_to_zero _

/-- The kernel of a monomorphism is isomorphic to the zero object -/
def kernel.ofMono [HasKernel f] [Mono f] : kernel f ≅ 0 :=
  Functor.mapIso (Cones.forget _) <|
    IsLimit.uniqueUpToIso (limit.isLimit (parallelPair f 0)) (kernel.isLimitConeZeroCone f)

/-- The kernel morphism of a monomorphism is a zero morphism -/
theorem kernel.ι_of_mono [HasKernel f] [Mono f] : kernel.ι f = 0 :=
  zero_of_source_iso_zero _ (kernel.ofMono f)

end HasZeroObject

section Transport

/-- If `i` is an isomorphism such that `l ≫ i.hom = f`, then any kernel of `f` is a kernel of `l`.-/
def IsKernel.ofCompIso {Z : C} (l : X ⟶ Z) (i : Z ≅ Y) (h : l ≫ i.Hom = f) {s : KernelFork f} (hs : IsLimit s) :
    IsLimit
      (KernelFork.ofι (Fork.ι s) <|
        show Fork.ι s ≫ l = 0 by
          simp [← i.comp_inv_eq.2 h.symm]) :=
  Fork.IsLimit.mk _
    (fun s =>
      hs.lift <|
        KernelFork.ofι (Fork.ι s) <| by
          simp [← h])
    (fun s => by
      simp )
    fun s m h => by
    apply fork.is_limit.hom_ext hs
    simpa using h walking_parallel_pair.zero

/-- If `i` is an isomorphism such that `l ≫ i.hom = f`, then the kernel of `f` is a kernel of `l`.-/
def kernel.ofCompIso [HasKernel f] {Z : C} (l : X ⟶ Z) (i : Z ≅ Y) (h : l ≫ i.Hom = f) :
    IsLimit
      (KernelFork.ofι (kernel.ι f) <|
        show kernel.ι f ≫ l = 0 by
          simp [← i.comp_inv_eq.2 h.symm]) :=
  IsKernel.ofCompIso f l i h <| limit.isLimit _

/-- If `s` is any limit kernel cone over `f` and if  `i` is an isomorphism such that
    `i.hom ≫ s.ι  = l`, then `l` is a kernel of `f`. -/
def IsKernel.isoKernel {Z : C} (l : Z ⟶ X) {s : KernelFork f} (hs : IsLimit s) (i : Z ≅ s.x)
    (h : i.Hom ≫ Fork.ι s = l) :
    IsLimit
      (KernelFork.ofι l <|
        show l ≫ f = 0 by
          simp [← h]) :=
  IsLimit.ofIsoLimit hs <|
    (Cones.ext i.symm) fun j => by
      cases j
      · exact (iso.eq_inv_comp i).2 h
        
      · simp
        

/-- If `i` is an isomorphism such that `i.hom ≫ kernel.ι f = l`, then `l` is a kernel of `f`. -/
def kernel.isoKernel [HasKernel f] {Z : C} (l : Z ⟶ X) (i : Z ≅ kernel f) (h : i.Hom ≫ kernel.ι f = l) :
    IsLimit
      (KernelFork.ofι l <| by
        simp [← h]) :=
  IsKernel.isoKernel f l (limit.isLimit _) i h

end Transport

section

variable (X Y)

/-- The kernel morphism of a zero morphism is an isomorphism -/
theorem kernel.ι_of_zero : IsIso (kernel.ι (0 : X ⟶ Y)) :=
  equalizer.ι_of_self _

end

section

/-- A cokernel cofork is just a cofork where the second morphism is a zero morphism. -/
abbrev CokernelCofork :=
  Cofork f 0

variable {f}

@[simp, reassoc]
theorem CokernelCofork.condition (s : CokernelCofork f) : f ≫ Cofork.π s = 0 := by
  rw [cofork.condition, zero_comp]

@[simp]
theorem CokernelCofork.app_zero (s : CokernelCofork f) : s.ι.app zero = 0 := by
  rw [← cofork.left_app_one, cokernel_cofork.condition]

/-- A morphism `π` satisfying `f ≫ π = 0` determines a cokernel cofork on `f`. -/
abbrev CokernelCofork.ofπ {Z : C} (π : Y ⟶ Z) (w : f ≫ π = 0) : CokernelCofork f :=
  Cofork.ofπ π <| by
    rw [w, zero_comp]

@[simp]
theorem CokernelCofork.π_of_π {X Y P : C} (f : X ⟶ Y) (π : Y ⟶ P) (w : f ≫ π = 0) :
    Cofork.π (CokernelCofork.ofπ π w) = π :=
  rfl

/-- Every cokernel cofork `s` is isomorphic (actually, equal) to `cofork.of_π (cofork.π s) _`. -/
def isoOfπ (s : Cofork f 0) : s ≅ Cofork.ofπ (Cofork.π s) (Cofork.condition s) :=
  (Cocones.ext (Iso.refl _)) fun j => by
    cases j <;> tidy

/-- If `π = π'`, then `cokernel_cofork.of_π π _` and `cokernel_cofork.of_π π' _` are isomorphic. -/
def ofπCongr {P : C} {π π' : Y ⟶ P} {w : f ≫ π = 0} (h : π = π') :
    CokernelCofork.ofπ π w ≅
      CokernelCofork.ofπ π'
        (by
          rw [← h, w]) :=
  (Cocones.ext (Iso.refl _)) fun j => by
    cases j <;> tidy

/-- If `s` is a colimit cokernel cofork, then every `k : Y ⟶ W` satisfying `f ≫ k = 0` induces
    `l : s.X ⟶ W` such that `cofork.π s ≫ l = k`. -/
def CokernelCofork.IsColimit.desc' {s : CokernelCofork f} (hs : IsColimit s) {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) :
    { l : s.x ⟶ W // Cofork.π s ≫ l = k } :=
  ⟨hs.desc <| CokernelCofork.ofπ _ h, hs.fac _ _⟩

/-- This is a slightly more convenient method to verify that a cokernel cofork is a colimit cocone.
It only asks for a proof of facts that carry any mathematical content -/
def isColimitAux (t : CokernelCofork f) (desc : ∀ s : CokernelCofork f, t.x ⟶ s.x)
    (fac : ∀ s : CokernelCofork f, t.π ≫ desc s = s.π)
    (uniq : ∀ s : CokernelCofork f m : t.x ⟶ s.x w : t.π ≫ m = s.π, m = desc s) : IsColimit t :=
  { desc,
    fac' := fun s j => by
      cases j
      · simp
        
      · exact fac s
        ,
    uniq' := fun s m w => uniq s m (w Limits.WalkingParallelPair.one) }

/-- This is a more convenient formulation to show that a `cokernel_cofork` constructed using
`cokernel_cofork.of_π` is a limit cone.
-/
def IsColimit.ofπ {Z : C} (g : Y ⟶ Z) (eq : f ≫ g = 0) (desc : ∀ {Z' : C} g' : Y ⟶ Z' eq' : f ≫ g' = 0, Z ⟶ Z')
    (fac : ∀ {Z' : C} g' : Y ⟶ Z' eq' : f ≫ g' = 0, g ≫ desc g' eq' = g')
    (uniq : ∀ {Z' : C} g' : Y ⟶ Z' eq' : f ≫ g' = 0 m : Z ⟶ Z' w : g ≫ m = g', m = desc g' eq') :
    IsColimit (CokernelCofork.ofπ g Eq) :=
  isColimitAux _ (fun s => desc s.π s.condition) (fun s => fac s.π s.condition) fun s => uniq s.π s.condition

end

section

variable [HasCokernel f]

/-- The cokernel of a morphism, expressed as the coequalizer with the 0 morphism. -/
abbrev cokernel : C :=
  coequalizer f 0

/-- The map from the target of `f` to `cokernel f`. -/
abbrev cokernel.π : Y ⟶ cokernel f :=
  coequalizer.π f 0

@[simp]
theorem coequalizer_as_cokernel : coequalizer.π f 0 = cokernel.π f :=
  rfl

@[simp, reassoc]
theorem cokernel.condition : f ≫ cokernel.π f = 0 :=
  CokernelCofork.condition _

/-- Given any morphism `k : Y ⟶ W` such that `f ≫ k = 0`, `k` factors through `cokernel.π f`
    via `cokernel.desc : cokernel f ⟶ W`. -/
abbrev cokernel.desc {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) : cokernel f ⟶ W :=
  colimit.desc (parallelPair f 0) (CokernelCofork.ofπ k h)

@[simp, reassoc]
theorem cokernel.π_desc {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) : cokernel.π f ≫ cokernel.desc f k h = k :=
  colimit.ι_desc _ _

@[simp]
theorem cokernel.desc_zero {W : C} {h} : cokernel.desc f (0 : Y ⟶ W) h = 0 := by
  ext
  simp

instance cokernel.desc_epi {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) [Epi k] : Epi (cokernel.desc f k h) :=
  ⟨fun Z g g' w => by
    replace w := cokernel.π f ≫= w
    simp only [cokernel.π_desc_assoc] at w
    exact (cancel_epi k).1 w⟩

/-- Any morphism `k : Y ⟶ W` satisfying `f ≫ k = 0` induces `l : cokernel f ⟶ W` such that
    `cokernel.π f ≫ l = k`. -/
def cokernel.desc' {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) : { l : cokernel f ⟶ W // cokernel.π f ≫ l = k } :=
  ⟨cokernel.desc f k h, cokernel.π_desc _ _ _⟩

/-- A commuting square induces a morphism of cokernels. -/
abbrev cokernel.map {X' Y' : C} (f' : X' ⟶ Y') [HasCokernel f'] (p : X ⟶ X') (q : Y ⟶ Y') (w : f ≫ q = p ≫ f') :
    cokernel f ⟶ cokernel f' :=
  cokernel.desc f (q ≫ cokernel.π f')
    (by
      simp [reassoc_of w])

/-- Given a commutative diagram
    X --f--> Y --g--> Z
    |        |        |
    |        |        |
    v        v        v
    X' -f'-> Y' -g'-> Z'
with horizontal arrows composing to zero,
then we obtain a commutative square
   cokernel f ---> Z
   |               |
   | cokernel.map  |
   |               |
   v               v
   cokernel f' --> Z'
-/
theorem cokernel.map_desc {X Y Z X' Y' Z' : C} (f : X ⟶ Y) [HasCokernel f] (g : Y ⟶ Z) (w : f ≫ g = 0) (f' : X' ⟶ Y')
    [HasCokernel f'] (g' : Y' ⟶ Z') (w' : f' ≫ g' = 0) (p : X ⟶ X') (q : Y ⟶ Y') (r : Z ⟶ Z') (h₁ : f ≫ q = p ≫ f')
    (h₂ : g ≫ r = q ≫ g') : cokernel.map f f' p q h₁ ≫ cokernel.desc f' g' w' = cokernel.desc f g w ≫ r := by
  ext
  simp [h₂]

/-- The cokernel of the zero morphism is an isomorphism -/
instance cokernel.π_zero_is_iso : IsIso (cokernel.π (0 : X ⟶ Y)) :=
  coequalizer.π_of_self _

theorem eq_zero_of_mono_cokernel [Mono (cokernel.π f)] : f = 0 :=
  (cancel_mono (cokernel.π f)).1
    (by
      simp )

/-- The cokernel of a zero morphism is isomorphic to the target. -/
def cokernelZeroIsoTarget : cokernel (0 : X ⟶ Y) ≅ Y :=
  coequalizer.isoTargetOfSelf 0

@[simp]
theorem cokernel_zero_iso_target_hom :
    cokernelZeroIsoTarget.Hom =
      cokernel.desc (0 : X ⟶ Y) (𝟙 Y)
        (by
          simp ) :=
  by
  ext
  simp [cokernel_zero_iso_target]

@[simp]
theorem cokernel_zero_iso_target_inv : cokernelZeroIsoTarget.inv = cokernel.π (0 : X ⟶ Y) :=
  rfl

/-- If two morphisms are known to be equal, then their cokernels are isomorphic. -/
def cokernelIsoOfEq {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g) : cokernel f ≅ cokernel g :=
  HasColimit.isoOfNatIso
    (by
      simp [h])

@[simp]
theorem cokernel_iso_of_eq_refl {h : f = f} : cokernelIsoOfEq h = Iso.refl (cokernel f) := by
  ext
  simp [cokernel_iso_of_eq]

@[simp, reassoc]
theorem π_comp_cokernel_iso_of_eq_hom {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g) :
    cokernel.π _ ≫ (cokernelIsoOfEq h).Hom = cokernel.π _ := by
  induction h
  simp

@[simp, reassoc]
theorem π_comp_cokernel_iso_of_eq_inv {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g) :
    cokernel.π _ ≫ (cokernelIsoOfEq h).inv = cokernel.π _ := by
  induction h
  simp

@[simp, reassoc]
theorem cokernel_iso_of_eq_hom_comp_desc {Z} {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g) (e : Y ⟶ Z) he :
    (cokernelIsoOfEq h).Hom ≫ cokernel.desc _ e he =
      cokernel.desc _ e
        (by
          simp [h, he]) :=
  by
  induction h
  simp

@[simp, reassoc]
theorem cokernel_iso_of_eq_inv_comp_desc {Z} {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g) (e : Y ⟶ Z) he :
    (cokernelIsoOfEq h).inv ≫ cokernel.desc _ e he =
      cokernel.desc _ e
        (by
          simp [← h, he]) :=
  by
  induction h
  simp

@[simp]
theorem cokernel_iso_of_eq_trans {f g h : X ⟶ Y} [HasCokernel f] [HasCokernel g] [HasCokernel h] (w₁ : f = g)
    (w₂ : g = h) : cokernelIsoOfEq w₁ ≪≫ cokernelIsoOfEq w₂ = cokernelIsoOfEq (w₁.trans w₂) := by
  induction w₁
  induction w₂
  ext
  simp [cokernel_iso_of_eq]

variable {f}

theorem cokernel_not_mono_of_nonzero (w : f ≠ 0) : ¬Mono (cokernel.π f) := fun I => w (eq_zero_of_mono_cokernel f)

theorem cokernel_not_iso_of_nonzero (w : f ≠ 0) : IsIso (cokernel.π f) → False := fun I =>
  cokernel_not_mono_of_nonzero w <| by
    skip
    infer_instance

-- TODO the remainder of this section has obvious generalizations to `has_coequalizer f g`.
instance has_cokernel_comp_iso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCokernel f] [IsIso g] : HasCokernel (f ≫ g) where
  exists_colimit :=
    ⟨{ Cocone :=
          CokernelCofork.ofπ (inv g ≫ cokernel.π f)
            (by
              simp ),
        IsColimit :=
          isColimitAux _
            (fun s =>
              cokernel.desc _ (g ≫ s.π)
                (by
                  rw [← category.assoc, cokernel_cofork.condition]))
            (by
              tidy)
            fun s m w => by
            simp_rw [← w]
            ext
            simp }⟩

/-- When `g` is an isomorphism, the cokernel of `f ≫ g` is isomorphic to the cokernel of `f`.
-/
@[simps]
def cokernelCompIsIso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCokernel f] [IsIso g] :
    cokernel (f ≫ g) ≅ cokernel f where
  Hom :=
    cokernel.desc _ (inv g ≫ cokernel.π f)
      (by
        simp )
  inv :=
    cokernel.desc _ (g ≫ cokernel.π (f ≫ g))
      (by
        rw [← category.assoc, cokernel.condition])

instance has_cokernel_epi_comp {X Y Z : C} (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) [HasCokernel g] : HasCokernel (f ≫ g) where
  exists_colimit :=
    ⟨{ Cocone :=
          CokernelCofork.ofπ (cokernel.π g)
            (by
              simp ),
        IsColimit :=
          isColimitAux _
            (fun s =>
              cokernel.desc _ s.π
                ((cancel_epi f).mp
                  (by
                    rw [← category.assoc]
                    simp )))
            (by
              tidy)
            (by
              tidy) }⟩

/-- When `f` is an epimorphism, the cokernel of `f ≫ g` is isomorphic to the cokernel of `g`.
-/
@[simps]
def cokernelEpiComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] [HasCokernel g] : cokernel (f ≫ g) ≅ cokernel g where
  Hom :=
    cokernel.desc _ (cokernel.π g)
      (by
        simp )
  inv :=
    cokernel.desc _ (cokernel.π (f ≫ g))
      (by
        rw [← cancel_epi f, ← category.assoc]
        simp )

end

section HasZeroObject

variable [HasZeroObject C]

open_locale ZeroObject

/-- The morphism to the zero object determines a cocone on a cokernel diagram -/
def cokernel.zeroCocone : Cocone (parallelPair f 0) where
  x := 0
  ι := { app := fun j => 0 }

/-- The morphism to the zero object is a cokernel of an epimorphism -/
def cokernel.isColimitCoconeZeroCocone [Epi f] : IsColimit (cokernel.zeroCocone f) :=
  Cofork.IsColimit.mk _ (fun s => 0)
    (fun s => by
      erw [zero_comp]
      convert (zero_of_epi_comp f _).symm
      exact cokernel_cofork.condition _)
    fun _ _ _ => zero_of_from_zero _

/-- The cokernel of an epimorphism is isomorphic to the zero object -/
def cokernel.ofEpi [HasCokernel f] [Epi f] : cokernel f ≅ 0 :=
  Functor.mapIso (Cocones.forget _) <|
    IsColimit.uniqueUpToIso (colimit.isColimit (parallelPair f 0)) (cokernel.isColimitCoconeZeroCocone f)

/-- The cokernel morphism of an epimorphism is a zero morphism -/
theorem cokernel.π_of_epi [HasCokernel f] [Epi f] : cokernel.π f = 0 :=
  zero_of_target_iso_zero _ (cokernel.ofEpi f)

end HasZeroObject

section HasImage

/-- The cokernel of the image inclusion of a morphism `f` is isomorphic to the cokernel of `f`.

(This result requires that the factorisation through the image is an epimorphism.
This holds in any category with equalizers.)
-/
@[simps]
def cokernelImageι {X Y : C} (f : X ⟶ Y) [HasImage f] [HasCokernel (image.ι f)] [HasCokernel f]
    [Epi (factorThruImage f)] : cokernel (image.ι f) ≅ cokernel f where
  Hom :=
    cokernel.desc _ (cokernel.π f)
      (by
        have w := cokernel.condition f
        conv at w => lhs congr rw [← image.fac f]
        rw [← has_zero_morphisms.comp_zero (limits.factor_thru_image f), category.assoc, cancel_epi] at w
        exact w)
  inv :=
    cokernel.desc _ (cokernel.π _)
      (by
        conv => lhs congr rw [← image.fac f]
        rw [category.assoc, cokernel.condition, has_zero_morphisms.comp_zero])

end HasImage

section

variable (X Y)

/-- The cokernel of a zero morphism is an isomorphism -/
theorem cokernel.π_of_zero : IsIso (cokernel.π (0 : X ⟶ Y)) :=
  coequalizer.π_of_self _

end

section HasZeroObject

variable [HasZeroObject C]

open_locale ZeroObject

/-- The kernel of the cokernel of an epimorphism is an isomorphism -/
instance kernel.of_cokernel_of_epi [HasCokernel f] [HasKernel (cokernel.π f)] [Epi f] :
    IsIso (kernel.ι (cokernel.π f)) :=
  equalizer.ι_of_eq <| cokernel.π_of_epi f

/-- The cokernel of the kernel of a monomorphism is an isomorphism -/
instance cokernel.of_kernel_of_mono [HasKernel f] [HasCokernel (kernel.ι f)] [Mono f] :
    IsIso (cokernel.π (kernel.ι f)) :=
  coequalizer.π_of_eq <| kernel.ι_of_mono f

end HasZeroObject

section Transport

/-- If `i` is an isomorphism such that `i.hom ≫ l = f`, then any cokernel of `f` is a cokernel of
    `l`. -/
def IsCokernel.ofIsoComp {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.Hom ≫ l = f) {s : CokernelCofork f} (hs : IsColimit s) :
    IsColimit
      (CokernelCofork.ofπ (Cofork.π s) <|
        show l ≫ Cofork.π s = 0 by
          simp [i.eq_inv_comp.2 h]) :=
  Cofork.IsColimit.mk _
    (fun s =>
      hs.desc <|
        CokernelCofork.ofπ (Cofork.π s) <| by
          simp [← h])
    (fun s => by
      simp )
    fun s m h => by
    apply cofork.is_colimit.hom_ext hs
    simpa using h walking_parallel_pair.one

/-- If `i` is an isomorphism such that `i.hom ≫ l = f`, then the cokernel of `f` is a cokernel of
    `l`. -/
def cokernel.ofIsoComp [HasCokernel f] {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.Hom ≫ l = f) :
    IsColimit
      (CokernelCofork.ofπ (cokernel.π f) <|
        show l ≫ cokernel.π f = 0 by
          simp [i.eq_inv_comp.2 h]) :=
  IsCokernel.ofIsoComp f l i h <| colimit.isColimit _

/-- If `s` is any colimit cokernel cocone over `f` and `i` is an isomorphism such that
    `s.π ≫ i.hom = l`, then `l` is a cokernel of `f`. -/
def IsCokernel.cokernelIso {Z : C} (l : Y ⟶ Z) {s : CokernelCofork f} (hs : IsColimit s) (i : s.x ≅ Z)
    (h : Cofork.π s ≫ i.Hom = l) :
    IsColimit
      (CokernelCofork.ofπ l <|
        show f ≫ l = 0 by
          simp [← h]) :=
  IsColimit.ofIsoColimit hs <|
    (Cocones.ext i) fun j => by
      cases j
      · simp
        
      · exact h
        

/-- If `i` is an isomorphism such that `cokernel.π f ≫ i.hom = l`, then `l` is a cokernel of `f`. -/
def cokernel.cokernelIso [HasCokernel f] {Z : C} (l : Y ⟶ Z) (i : cokernel f ≅ Z) (h : cokernel.π f ≫ i.Hom = l) :
    IsColimit
      (CokernelCofork.ofπ l <| by
        simp [← h]) :=
  IsCokernel.cokernelIso f l (colimit.isColimit _) i h

end Transport

end CategoryTheory.Limits

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

variable [HasZeroMorphisms C]

/-- `has_kernels` represents the existence of kernels for every morphism. -/
class HasKernels : Prop where
  HasLimit : ∀ {X Y : C} f : X ⟶ Y, HasKernel f := by
    run_tac
      tactic.apply_instance

/-- `has_cokernels` represents the existence of cokernels for every morphism. -/
class HasCokernels : Prop where
  HasColimit : ∀ {X Y : C} f : X ⟶ Y, HasCokernel f := by
    run_tac
      tactic.apply_instance

attribute [instance] has_kernels.has_limit has_cokernels.has_colimit

instance (priority := 100) has_kernels_of_has_equalizers [HasEqualizers C] : HasKernels C :=
  {  }

instance (priority := 100) has_cokernels_of_has_coequalizers [HasCoequalizers C] : HasCokernels C :=
  {  }

end CategoryTheory.Limits

