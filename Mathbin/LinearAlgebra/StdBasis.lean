import Mathbin.LinearAlgebra.Basis 
import Mathbin.LinearAlgebra.Pi 
import Mathbin.Data.Matrix.Basis

/-!
# The standard basis

This file defines the standard basis `std_basis R φ i b j`, which is `b` where `i = j` and `0`
elsewhere.

To give a concrete example, `std_basis R (λ (i : fin 3), R) i 1` gives the `i`th unit basis vector
in `R³`, and `pi.is_basis_fun` proves this is a basis over `fin 3 → R`.

## Main definitions

 - `linear_map.std_basis R ϕ i b`: the `i`'th standard `R`-basis vector on `Π i, ϕ i`,
   scaled by `b`.

## Main results

 - `pi.is_basis_std_basis`: `std_basis` turns a component-wise basis into a basis on the product
   type.
 - `pi.is_basis_fun`: `std_basis R (λ _, R) i 1` is a basis for `n → R`.

-/


open Function Submodule

open_locale BigOperators

open_locale BigOperators

namespace LinearMap

variable(R :
    Type _){ι : Type _}[Semiringₓ R](φ : ι → Type _)[∀ i, AddCommMonoidₓ (φ i)][∀ i, Module R (φ i)][DecidableEq ι]

/-- The standard basis of the product of `φ`. -/
def std_basis : ∀ i : ι, φ i →ₗ[R] ∀ i, φ i :=
  single

theorem std_basis_apply (i : ι) (b : φ i) : std_basis R φ i b = update 0 i b :=
  rfl

theorem coe_std_basis (i : ι) : «expr⇑ » (std_basis R φ i) = Pi.single i :=
  funext$ std_basis_apply R φ i

@[simp]
theorem std_basis_same (i : ι) (b : φ i) : std_basis R φ i b i = b :=
  by 
    rw [std_basis_apply, update_same]

theorem std_basis_ne (i j : ι) (h : j ≠ i) (b : φ i) : std_basis R φ i b j = 0 :=
  by 
    rw [std_basis_apply, update_noteq h] <;> rfl

theorem std_basis_eq_pi_diag (i : ι) : std_basis R φ i = pi (diag i) :=
  by 
    ext x j 
    convert (update_apply 0 x i j _).symm 
    rfl

theorem ker_std_basis (i : ι) : ker (std_basis R φ i) = ⊥ :=
  ker_eq_bot_of_injective$
    fun f g hfg =>
      have  : std_basis R φ i f i = std_basis R φ i g i := hfg ▸ rfl 
      by 
        simpa only [std_basis_same]

theorem proj_comp_std_basis (i j : ι) : (proj i).comp (std_basis R φ j) = diag j i :=
  by 
    rw [std_basis_eq_pi_diag, proj_pi]

theorem proj_std_basis_same (i : ι) : (proj i).comp (std_basis R φ i) = id :=
  by 
    ext b <;> simp 

theorem proj_std_basis_ne (i j : ι) (h : i ≠ j) : (proj i).comp (std_basis R φ j) = 0 :=
  by 
    ext b <;> simp [std_basis_ne R φ _ _ h]

theorem supr_range_std_basis_le_infi_ker_proj (I J : Set ι) (h : Disjoint I J) :
  (⨆(i : _)(_ : i ∈ I), range (std_basis R φ i)) ≤ ⨅(i : _)(_ : i ∈ J), ker (proj i) :=
  by 
    refine' supr_le$ fun i => supr_le$ fun hi => range_le_iff_comap.2 _ 
    simp only [(ker_comp _ _).symm, eq_top_iff, SetLike.le_def, mem_ker, comap_infi, mem_infi]
    intro b hb j hj 
    have  : i ≠ j := fun eq => h ⟨hi, Eq.symm ▸ hj⟩
    rw [mem_comap, mem_ker, ←comp_apply, proj_std_basis_ne R φ j i this.symm, zero_apply]

theorem infi_ker_proj_le_supr_range_std_basis {I : Finset ι} {J : Set ι} (hu : Set.Univ ⊆ «expr↑ » I ∪ J) :
  (⨅(i : _)(_ : i ∈ J), ker (proj i)) ≤ ⨆(i : _)(_ : i ∈ I), range (std_basis R φ i) :=
  SetLike.le_def.2
    (by 
      intro b hb 
      simp only [mem_infi, mem_ker, proj_apply] at hb 
      rw
        [←show (∑i in I, std_basis R φ i (b i)) = b by 
          ext i 
          rw [Finset.sum_apply, ←std_basis_same R φ i (b i)]
          refine' Finset.sum_eq_single i (fun j hjI ne => std_basis_ne _ _ _ _ Ne.symm _) _ 
          intro hiI 
          rw [std_basis_same]
          exact hb _ ((hu trivialₓ).resolve_left hiI)]
      exact sum_mem _ fun i hiI => mem_supr_of_mem i$ mem_supr_of_mem hiI$ (std_basis R φ i).mem_range_self (b i))

theorem supr_range_std_basis_eq_infi_ker_proj {I J : Set ι} (hd : Disjoint I J) (hu : Set.Univ ⊆ I ∪ J)
  (hI : Set.Finite I) : (⨆(i : _)(_ : i ∈ I), range (std_basis R φ i)) = ⨅(i : _)(_ : i ∈ J), ker (proj i) :=
  by 
    refine' le_antisymmₓ (supr_range_std_basis_le_infi_ker_proj _ _ _ _ hd) _ 
    have  : Set.Univ ⊆ «expr↑ » hI.to_finset ∪ J
    ·
      rwa [hI.coe_to_finset]
    refine' le_transₓ (infi_ker_proj_le_supr_range_std_basis R φ this) (supr_le_supr$ fun i => _)
    rw [Set.Finite.mem_to_finset]
    exact le_reflₓ _

theorem supr_range_std_basis [Fintype ι] : (⨆i : ι, range (std_basis R φ i)) = ⊤ :=
  have  : (Set.Univ : Set ι) ⊆ «expr↑ » (Finset.univ : Finset ι) ∪ ∅ :=
    by 
      rw [Finset.coe_univ, Set.union_empty]
  by 
    apply top_unique 
    convert infi_ker_proj_le_supr_range_std_basis R φ this 
    exact infi_emptyset.symm 
    exact funext$ fun i => ((@supr_pos _ _ _ fun h => range (std_basis R φ i))$ Finset.mem_univ i).symm

theorem disjoint_std_basis_std_basis (I J : Set ι) (h : Disjoint I J) :
  Disjoint (⨆(i : _)(_ : i ∈ I), range (std_basis R φ i)) (⨆(i : _)(_ : i ∈ J), range (std_basis R φ i)) :=
  by 
    refine'
      Disjoint.mono (supr_range_std_basis_le_infi_ker_proj _ _ _ _$ disjoint_compl_right)
        (supr_range_std_basis_le_infi_ker_proj _ _ _ _$ disjoint_compl_right) _ 
    simp only [Disjoint, SetLike.le_def, mem_infi, mem_inf, mem_ker, mem_bot, proj_apply, funext_iff]
    rintro b ⟨hI, hJ⟩ i 
    classical 
    byCases' hiI : i ∈ I
    ·
      byCases' hiJ : i ∈ J
      ·
        exact (h ⟨hiI, hiJ⟩).elim
      ·
        exact hJ i hiJ
    ·
      exact hI i hiI

theorem std_basis_eq_single {a : R} :
  (fun i : ι => (std_basis R (fun _ : ι => R) i) a) = fun i : ι => Finsupp.single i a :=
  by 
    ext i j 
    rw [std_basis_apply, Finsupp.single_apply]
    splitIfs
    ·
      rw [h, Function.update_same]
    ·
      rw [Function.update_noteq (Ne.symm h)]
      rfl

end LinearMap

namespace Pi

open LinearMap

open Set

variable{R : Type _}

section Module

variable{η : Type _}{ιs : η → Type _}{Ms : η → Type _}

theorem linear_independent_std_basis [Ringₓ R] [∀ i, AddCommGroupₓ (Ms i)] [∀ i, Module R (Ms i)] [DecidableEq η]
  (v : ∀ j, ιs j → Ms j) (hs : ∀ i, LinearIndependent R (v i)) :
  LinearIndependent R fun ji : Σj, ιs j => std_basis R Ms ji.1 (v ji.1 ji.2) :=
  by 
    have hs' : ∀ j : η, LinearIndependent R fun i : ιs j => std_basis R Ms j (v j i)
    ·
      intro j 
      exact (hs j).map' _ (ker_std_basis _ _ _)
    apply linear_independent_Union_finite hs'
    ·
      intro j J _ hiJ 
      simp [(Set.Unionₓ.equations._eqn_1 _).symm, Submodule.span_image, Submodule.span_Union]
      have h₀ : ∀ j, span R (range fun i : ιs j => std_basis R Ms j (v j i)) ≤ range (std_basis R Ms j)
      ·
        intro j 
        rw [span_le, LinearMap.range_coe]
        apply range_comp_subset_range 
      have h₁ :
        span R (range fun i : ιs j => std_basis R Ms j (v j i)) ≤ ⨆(i : _)(_ : i ∈ {j}), range (std_basis R Ms i)
      ·
        rw [@supr_singleton _ _ _ fun i => LinearMap.range (std_basis R (fun j : η => Ms j) i)]
        apply h₀ 
      have h₂ :
        (⨆(j : _)(_ : j ∈ J), span R (range fun i : ιs j => std_basis R Ms j (v j i))) ≤
          ⨆(j : _)(_ : j ∈ J), range (std_basis R (fun j : η => Ms j) j) :=
        supr_le_supr fun i => supr_le_supr fun H => h₀ i 
      have h₃ : Disjoint (fun i : η => i ∈ {j}) J
      ·
        convert Set.disjoint_singleton_left.2 hiJ using 0 
      exact (disjoint_std_basis_std_basis _ _ _ _ h₃).mono h₁ h₂

variable[Semiringₓ R][∀ i, AddCommMonoidₓ (Ms i)][∀ i, Module R (Ms i)]

variable[Fintype η]

section 

open LinearEquiv

/-- `pi.basis (s : ∀ j, basis (ιs j) R (Ms j))` is the `Σ j, ιs j`-indexed basis on `Π j, Ms j`
given by `s j` on each component. -/
protected noncomputable def Basis (s : ∀ j, Basis (ιs j) R (Ms j)) : Basis (Σj, ιs j) R (∀ j, Ms j) :=
  by 
    refine' Basis.of_repr (_ ≪≫ₗ (Finsupp.sigmaFinsuppLequivPiFinsupp R).symm)
    exact LinearEquiv.piCongrRight fun j => (s j).repr

@[simp]
theorem basis_repr_std_basis [DecidableEq η] (s : ∀ j, Basis (ιs j) R (Ms j)) j i :
  (Pi.basis s).repr (std_basis R _ j (s j i)) = Finsupp.single ⟨j, i⟩ 1 :=
  by 
    ext ⟨j', i'⟩
    byCases' hj : j = j'
    ·
      subst hj 
      simp only [Pi.basis, LinearEquiv.trans_apply, Basis.repr_self, std_basis_same, LinearEquiv.Pi_congr_right_apply,
        Finsupp.sigma_finsupp_lequiv_pi_finsupp_symm_apply]
      symm 
      exact
        Basis.Finsupp.single_apply_left (fun i i' h : (⟨j, i⟩ : Σj, ιs j) = ⟨j, i'⟩ => eq_of_heq (Sigma.mk.inj h).2) _ _
          _ 
    simp only [Pi.basis, LinearEquiv.trans_apply, Finsupp.sigma_finsupp_lequiv_pi_finsupp_symm_apply,
      LinearEquiv.Pi_congr_right_apply]
    dsimp 
    rw [std_basis_ne _ _ _ _ (Ne.symm hj), LinearEquiv.map_zero, Finsupp.zero_apply, Finsupp.single_eq_of_ne]
    rintro ⟨⟩
    contradiction

@[simp]
theorem basis_apply [DecidableEq η] (s : ∀ j, Basis (ιs j) R (Ms j)) ji :
  Pi.basis s ji = std_basis R _ ji.1 (s ji.1 ji.2) :=
  Basis.apply_eq_iff.mpr
    (by 
      simp )

@[simp]
theorem basis_repr (s : ∀ j, Basis (ιs j) R (Ms j)) x ji : (Pi.basis s).repr x ji = (s ji.1).repr (x ji.1) ji.2 :=
  rfl

end 

section 

variable(R η)

/-- The basis on `η → R` where the `i`th basis vector is `function.update 0 i 1`. -/
noncomputable def basis_fun : Basis η R (∀ j : η, R) :=
  Basis.ofEquivFun (LinearEquiv.refl _ _)

@[simp]
theorem basis_fun_apply [DecidableEq η] i : basis_fun R η i = std_basis R (fun i : η => R) i 1 :=
  by 
    simp only [basis_fun, Basis.coe_of_equiv_fun, LinearEquiv.refl_symm, LinearEquiv.refl_apply, std_basis_apply]
    congr

@[simp]
theorem basis_fun_repr (x : η → R) (i : η) : (Pi.basisFun R η).repr x i = x i :=
  by 
    simp [basis_fun]

end 

end Module

end Pi

namespace Matrix

variable(R : Type _)(n : Type _)(m : Type _)[Fintype m][Fintype n][Semiringₓ R]

/-- The standard basis of `matrix n m R`. -/
noncomputable def std_basis : Basis (n × m) R (Matrix n m R) :=
  Basis.reindex (Pi.basis fun i : n => Pi.basisFun R m) (Equiv.sigmaEquivProd _ _)

variable{n m}

theorem std_basis_eq_std_basis_matrix (i : n) (j : m) [DecidableEq n] [DecidableEq m] :
  std_basis R n m (i, j) = std_basis_matrix i j (1 : R) :=
  by 
    ext a b 
    byCases' hi : i = a <;> byCases' hj : j = b
    ·
      simp [std_basis, hi, hj]
    ·
      simp [std_basis, hi, hj, Ne.symm hj, LinearMap.std_basis_ne]
    ·
      simp [std_basis, hi, hj, Ne.symm hi, LinearMap.std_basis_ne]
    ·
      simp [std_basis, hi, hj, Ne.symm hj, Ne.symm hi, LinearMap.std_basis_ne]

end Matrix

