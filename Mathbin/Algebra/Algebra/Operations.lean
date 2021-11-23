import Mathbin.Algebra.Algebra.Bilinear 
import Mathbin.Algebra.Module.SubmodulePointwise

/-!
# Multiplication and division of submodules of an algebra.

An interface for multiplication and division of sub-R-modules of an R-algebra A is developed.

## Main definitions

Let `R` be a commutative ring (or semiring) and aet `A` be an `R`-algebra.

* `1 : submodule R A`       : the R-submodule R of the R-algebra A
* `has_mul (submodule R A)` : multiplication of two sub-R-modules M and N of A is defined to be
                              the smallest submodule containing all the products `m * n`.
* `has_div (submodule R A)` : `I / J` is defined to be the submodule consisting of all `a : A` such
                              that `a • J ⊆ I`

It is proved that `submodule R A` is a semiring, and also an algebra over `set A`.

## Tags

multiplication of submodules, division of subodules, submodule semiring
-/


universe uι u v

open Algebra Set

open_locale BigOperators

open_locale Pointwise

namespace Submodule

variable{ι : Sort uι}

variable{R : Type u}[CommSemiringₓ R]

section Ringₓ

variable{A : Type v}[Semiringₓ A][Algebra R A]

variable(S T : Set A){M N P Q : Submodule R A}{m n : A}

/-- `1 : submodule R A` is the submodule R of A. -/
instance  : HasOne (Submodule R A) :=
  ⟨(Algebra.linearMap R A).range⟩

theorem one_eq_range : (1 : Submodule R A) = (Algebra.linearMap R A).range :=
  rfl

theorem algebra_map_mem (r : R) : algebraMap R A r ∈ (1 : Submodule R A) :=
  LinearMap.mem_range_self _ _

@[simp]
theorem mem_one {x : A} : x ∈ (1 : Submodule R A) ↔ ∃ y, algebraMap R A y = x :=
  by 
    simp only [one_eq_range, LinearMap.mem_range, Algebra.linear_map_apply]

theorem one_eq_span : (1 : Submodule R A) = R∙1 :=
  by 
    apply Submodule.ext 
    intro a 
    simp only [mem_one, mem_span_singleton, Algebra.smul_def, mul_oneₓ]

theorem one_le : (1 : Submodule R A) ≤ P ↔ (1 : A) ∈ P :=
  by 
    simpa only [one_eq_span, span_le, Set.singleton_subset_iff]

/-- Multiplication of sub-R-modules of an R-algebra A. The submodule `M * N` is the
smallest R-submodule of `A` containing the elements `m * n` for `m ∈ M` and `n ∈ N`. -/
instance  : Mul (Submodule R A) :=
  ⟨fun M N => ⨆s : M, N.map$ Algebra.lmul R A s.1⟩

theorem mul_mem_mul (hm : m ∈ M) (hn : n ∈ N) : (m*n) ∈ M*N :=
  (le_supr _ ⟨m, hm⟩ : _ ≤ M*N) ⟨n, hn, rfl⟩

theorem mul_le : (M*N) ≤ P ↔ ∀ m _ : m ∈ M n _ : n ∈ N, (m*n) ∈ P :=
  ⟨fun H m hm n hn => H$ mul_mem_mul hm hn,
    fun H => supr_le$ fun ⟨m, hm⟩ => map_le_iff_le_comap.2$ fun n hn => H m hm n hn⟩

@[elab_as_eliminator]
protected theorem mul_induction_on {C : A → Prop} {r : A} (hr : r ∈ M*N) (hm : ∀ m _ : m ∈ M n _ : n ∈ N, C (m*n))
  (h0 : C 0) (ha : ∀ x y, C x → C y → C (x+y)) (hs : ∀ r : R x, C x → C (r • x)) : C r :=
  (@mul_le _ _ _ _ _ _ _ ⟨C, h0, ha, hs⟩).2 hm hr

variable(R)

theorem span_mul_span : (span R S*span R T) = span R (S*T) :=
  by 
    apply le_antisymmₓ
    ·
      rw [mul_le]
      intro a ha b hb 
      apply span_induction ha 
      workOnGoal 0
        intros 
        apply span_induction hb 
        workOnGoal 0
          intros 
          exact subset_span ⟨_, _, ‹_›, ‹_›, rfl⟩
      all_goals 
        intros 
        simp only [mul_zero, zero_mul, zero_mem, left_distrib, right_distrib, mul_smul_comm, smul_mul_assoc]
        try 
          apply add_mem _ _ _ 
        try 
          apply smul_mem _ _ _ 
      assumption'
    ·
      rw [span_le]
      rintro _ ⟨a, b, ha, hb, rfl⟩
      exact mul_mem_mul (subset_span ha) (subset_span hb)

variable{R}

variable(M N P Q)

protected theorem mul_assocₓ : ((M*N)*P) = M*N*P :=
  le_antisymmₓ
    (mul_le.2$
      fun mn hmn p hp =>
        suffices (M*N) ≤ (M*N*P).comap (Algebra.lmulRight R p) from this hmn 
        mul_le.2$
          fun m hm n hn => show ((m*n)*p) ∈ M*N*P from (mul_assocₓ m n p).symm ▸ mul_mem_mul hm (mul_mem_mul hn hp))
    (mul_le.2$
      fun m hm np hnp =>
        suffices (N*P) ≤ ((M*N)*P).comap (Algebra.lmulLeft R m) from this hnp 
        mul_le.2$ fun n hn p hp => show (m*n*p) ∈ (M*N)*P from mul_assocₓ m n p ▸ mul_mem_mul (mul_mem_mul hm hn) hp)

@[simp]
theorem mul_bot : (M*⊥) = ⊥ :=
  eq_bot_iff.2$
    mul_le.2$
      fun m hm n hn =>
        by 
          rw [Submodule.mem_bot] at hn⊢ <;> rw [hn, mul_zero]

@[simp]
theorem bot_mul : (⊥*M) = ⊥ :=
  eq_bot_iff.2$
    mul_le.2$
      fun m hm n hn =>
        by 
          rw [Submodule.mem_bot] at hm⊢ <;> rw [hm, zero_mul]

@[simp]
protected theorem one_mulₓ : ((1 : Submodule R A)*M) = M :=
  by 
    convLHS => rw [one_eq_span, ←span_eq M]
    erw [span_mul_span, one_mulₓ, span_eq]

@[simp]
protected theorem mul_oneₓ : (M*1) = M :=
  by 
    convLHS => rw [one_eq_span, ←span_eq M]
    erw [span_mul_span, mul_oneₓ, span_eq]

variable{M N P Q}

@[mono]
theorem mul_le_mul (hmp : M ≤ P) (hnq : N ≤ Q) : (M*N) ≤ P*Q :=
  mul_le.2$ fun m hm n hn => mul_mem_mul (hmp hm) (hnq hn)

theorem mul_le_mul_left (h : M ≤ N) : (M*P) ≤ N*P :=
  mul_le_mul h (le_reflₓ P)

theorem mul_le_mul_right (h : N ≤ P) : (M*N) ≤ M*P :=
  mul_le_mul (le_reflₓ M) h

variable(M N P)

theorem mul_sup : (M*N⊔P) = (M*N)⊔M*P :=
  le_antisymmₓ
    (mul_le.2$
      fun m hm np hnp =>
        let ⟨n, hn, p, hp, hnp⟩ := mem_sup.1 hnp 
        mem_sup.2 ⟨_, mul_mem_mul hm hn, _, mul_mem_mul hm hp, hnp ▸ (mul_addₓ m n p).symm⟩)
    (sup_le (mul_le_mul_right le_sup_left) (mul_le_mul_right le_sup_right))

theorem sup_mul : ((M⊔N)*P) = (M*P)⊔N*P :=
  le_antisymmₓ
    (mul_le.2$
      fun mn hmn p hp =>
        let ⟨m, hm, n, hn, hmn⟩ := mem_sup.1 hmn 
        mem_sup.2 ⟨_, mul_mem_mul hm hp, _, mul_mem_mul hn hp, hmn ▸ (add_mulₓ m n p).symm⟩)
    (sup_le (mul_le_mul_left le_sup_left) (mul_le_mul_left le_sup_right))

theorem mul_subset_mul : ((«expr↑ » M : Set A)*(«expr↑ » N : Set A)) ⊆ («expr↑ » (M*N) : Set A) :=
  by 
    rintro _ ⟨i, j, hi, hj, rfl⟩
    exact mul_mem_mul hi hj

theorem map_mul {A'} [Semiringₓ A'] [Algebra R A'] (f : A →ₐ[R] A') :
  map f.to_linear_map (M*N) = map f.to_linear_map M*map f.to_linear_map N :=
  calc map f.to_linear_map (M*N) = ⨆i : M, (N.map (lmul R A i)).map f.to_linear_map := map_supr _ _ 
    _ = map f.to_linear_map M*map f.to_linear_map N :=
    by 
      apply congr_argₓ Sup 
      ext S 
      split  <;> rintro ⟨y, hy⟩
      ·
        use f y, mem_map.mpr ⟨y.1, y.2, rfl⟩
        refine' trans _ hy 
        ext 
        simp 
      ·
        obtain ⟨y', hy', fy_eq⟩ := mem_map.mp y.2
        use y', hy' 
        refine' trans _ hy 
        rw [f.to_linear_map_apply] at fy_eq 
        ext 
        simp [fy_eq]
    

section DecidableEq

open_locale Classical

-- error in Algebra.Algebra.Operations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_span_mul_finite_of_mem_span_mul
{S : set A}
{S' : set A}
{x : A}
(hx : «expr ∈ »(x, span R «expr * »(S, S'))) : «expr∃ , »((T
  T' : finset A), «expr ∧ »(«expr ⊆ »(«expr↑ »(T), S), «expr ∧ »(«expr ⊆ »(«expr↑ »(T'), S'), «expr ∈ »(x, span R («expr * »(T, T') : set A))))) :=
begin
  obtain ["⟨", ident U, ",", ident h, ",", ident hU, "⟩", ":=", expr mem_span_finite_of_mem_span hx],
  obtain ["⟨", ident T, ",", ident T', ",", ident hS, ",", ident hS', ",", ident h, "⟩", ":=", expr finset.subset_mul h],
  use ["[", expr T, ",", expr T', ",", expr hS, ",", expr hS', "]"],
  have [ident h'] [":", expr «expr ⊆ »((U : set A), «expr * »(T, T'))] [],
  { assumption_mod_cast },
  have [ident h''] [] [":=", expr span_mono h' hU],
  assumption
end

end DecidableEq

theorem mul_eq_span_mul_set (s t : Submodule R A) : (s*t) = span R ((s : Set A)*(t : Set A)) :=
  by 
    rw [←span_mul_span, span_eq, span_eq]

theorem supr_mul (s : ι → Submodule R A) (t : Submodule R A) : ((⨆i, s i)*t) = ⨆i, s i*t :=
  by 
    suffices  : ((⨆i, span R (s i : Set A))*span R t) = ⨆i, span R (s i)*span R t
    ·
      simpa only [span_eq] using this 
    simpRw [span_mul_span, ←span_Union, span_mul_span, Set.Union_mul]

theorem mul_supr (t : Submodule R A) (s : ι → Submodule R A) : (t*⨆i, s i) = ⨆i, t*s i :=
  by 
    suffices  : (span R (t : Set A)*⨆i, span R (s i)) = ⨆i, span R t*span R (s i)
    ·
      simpa only [span_eq] using this 
    simpRw [span_mul_span, ←span_Union, span_mul_span, Set.mul_Union]

theorem mem_span_mul_finite_of_mem_mul {P Q : Submodule R A} {x : A} (hx : x ∈ P*Q) :
  ∃ T T' : Finset A, (T : Set A) ⊆ P ∧ (T' : Set A) ⊆ Q ∧ x ∈ span R (T*T' : Set A) :=
  Submodule.mem_span_mul_finite_of_mem_span_mul
    (by 
      rwa [←Submodule.span_eq P, ←Submodule.span_eq Q, Submodule.span_mul_span] at hx)

variable{M N P}

/-- Sub-R-modules of an R-algebra form a semiring. -/
instance  : Semiringₓ (Submodule R A) :=
  { Submodule.pointwiseAddCommMonoid, Submodule.hasOne, Submodule.hasMul with one_mul := Submodule.one_mul,
    mul_one := Submodule.mul_one, mul_assoc := Submodule.mul_assoc, zero_mul := bot_mul, mul_zero := mul_bot,
    left_distrib := mul_sup, right_distrib := sup_mul }

variable(M)

theorem pow_subset_pow {n : ℕ} : («expr↑ » M : Set A) ^ n ⊆ «expr↑ » (M ^ n : Submodule R A) :=
  by 
    induction' n with n ih
    ·
      erw [pow_zeroₓ, pow_zeroₓ, Set.singleton_subset_iff]
      rw [SetLike.mem_coe, ←one_le]
      exact le_reflₓ _
    ·
      rw [pow_succₓ, pow_succₓ]
      refine' Set.Subset.trans (Set.mul_subset_mul (subset.refl _) ih) _ 
      apply mul_subset_mul

/-- `span` is a semiring homomorphism (recall multiplication is pointwise multiplication of subsets
on either side). -/
def span.ring_hom : set_semiring A →+* Submodule R A :=
  { toFun := Submodule.span R, map_zero' := span_empty, map_one' := one_eq_span.symm, map_add' := span_union,
    map_mul' :=
      fun s t =>
        by 
          erw [span_mul_span, ←image_mul_prod] }

end Ringₓ

section CommRingₓ

variable{A : Type v}[CommSemiringₓ A][Algebra R A]

variable{M N : Submodule R A}{m n : A}

theorem mul_mem_mul_rev (hm : m ∈ M) (hn : n ∈ N) : (n*m) ∈ M*N :=
  mul_commₓ m n ▸ mul_mem_mul hm hn

variable(M N)

protected theorem mul_commₓ : (M*N) = N*M :=
  le_antisymmₓ (mul_le.2$ fun r hrm s hsn => mul_mem_mul_rev hsn hrm)
    (mul_le.2$ fun r hrn s hsm => mul_mem_mul_rev hsm hrn)

/-- Sub-R-modules of an R-algebra A form a semiring. -/
instance  : CommSemiringₓ (Submodule R A) :=
  { Submodule.semiring with mul_comm := Submodule.mul_comm }

-- error in Algebra.Algebra.Operations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prod_span
{ι : Type*}
(s : finset ι)
(M : ι → set A) : «expr = »(«expr∏ in , »((i), s, submodule.span R (M i)), submodule.span R «expr∏ in , »((i), s, M i)) :=
begin
  letI [] [] [":=", expr classical.dec_eq ι],
  refine [expr finset.induction_on s _ _],
  { simp [] [] [] ["[", expr one_eq_span, ",", expr set.singleton_one, "]"] [] [] },
  { intros ["_", "_", ident H, ident ih],
    rw ["[", expr finset.prod_insert H, ",", expr finset.prod_insert H, ",", expr ih, ",", expr span_mul_span, "]"] [] }
end

theorem prod_span_singleton {ι : Type _} (s : Finset ι) (x : ι → A) :
  (∏i in s, span R ({x i} : Set A)) = span R {∏i in s, x i} :=
  by 
    rw [prod_span, Set.finset_prod_singleton]

variable(R A)

/-- R-submodules of the R-algebra A are a module over `set A`. -/
instance module_set : Module (set_semiring A) (Submodule R A) :=
  { smul := fun s P => span R s*P, smul_add := fun _ _ _ => mul_addₓ _ _ _,
    add_smul :=
      fun s t P =>
        show (span R (s⊔t)*P) = _ by 
          erw [span_union, right_distrib],
    mul_smul :=
      fun s t P =>
        show _ = _*_*_ by 
          rw [←mul_assocₓ, span_mul_span, ←image_mul_prod],
    one_smul :=
      fun P =>
        show (span R {(1 : A)}*P) = _ by 
          convLHS => erw [←span_eq P]
          erw [span_mul_span, one_mulₓ, span_eq],
    zero_smul :=
      fun P =>
        show (span R ∅*P) = ⊥by 
          erw [span_empty, bot_mul],
    smul_zero := fun _ => mul_bot _ }

variable{R A}

theorem smul_def {s : set_semiring A} {P : Submodule R A} : s • P = span R s*P :=
  rfl

theorem smul_le_smul {s t : set_semiring A} {M N : Submodule R A} (h₁ : s.down ≤ t.down) (h₂ : M ≤ N) : s • M ≤ t • N :=
  mul_le_mul (span_mono h₁) h₂

theorem smul_singleton (a : A) (M : Submodule R A) : ({a} : Set A).up • M = M.map (lmul_left _ a) :=
  by 
    convLHS => rw [←span_eq M]
    change (span _ _*span _ _) = _ 
    rw [span_mul_span]
    apply le_antisymmₓ
    ·
      rw [span_le]
      rintro _ ⟨b, m, hb, hm, rfl⟩
      rw [SetLike.mem_coe, mem_map, set.mem_singleton_iff.mp hb]
      exact ⟨m, hm, rfl⟩
    ·
      rintro _ ⟨m, hm, rfl⟩
      exact subset_span ⟨a, m, Set.mem_singleton a, hm, rfl⟩

section Quotientₓ

/-- The elements of `I / J` are the `x` such that `x • J ⊆ I`.

In fact, we define `x ∈ I / J` to be `∀ y ∈ J, x * y ∈ I` (see `mem_div_iff_forall_mul_mem`),
which is equivalent to `x • J ⊆ I` (see `mem_div_iff_smul_subset`), but nicer to use in proofs.

This is the general form of the ideal quotient, traditionally written $I : J$.
-/
instance  : Div (Submodule R A) :=
  ⟨fun I J =>
      { Carrier := { x | ∀ y _ : y ∈ J, (x*y) ∈ I },
        zero_mem' :=
          fun y hy =>
            by 
              rw [zero_mul]
              apply Submodule.zero_mem,
        add_mem' :=
          fun a b ha hb y hy =>
            by 
              rw [add_mulₓ]
              exact Submodule.add_mem _ (ha _ hy) (hb _ hy),
        smul_mem' :=
          fun r x hx y hy =>
            by 
              rw [Algebra.smul_mul_assoc]
              exact Submodule.smul_mem _ _ (hx _ hy) }⟩

theorem mem_div_iff_forall_mul_mem {x : A} {I J : Submodule R A} : x ∈ I / J ↔ ∀ y _ : y ∈ J, (x*y) ∈ I :=
  Iff.refl _

theorem mem_div_iff_smul_subset {x : A} {I J : Submodule R A} : x ∈ I / J ↔ x • (J : Set A) ⊆ I :=
  ⟨fun h y ⟨y', hy', xy'_eq_y⟩ =>
      by 
        rw [←xy'_eq_y]
        apply h 
        assumption,
    fun h y hy => h (Set.smul_mem_smul_set hy)⟩

theorem le_div_iff {I J K : Submodule R A} : I ≤ J / K ↔ ∀ x _ : x ∈ I z _ : z ∈ K, (x*z) ∈ J :=
  Iff.refl _

theorem le_div_iff_mul_le {I J K : Submodule R A} : I ≤ J / K ↔ (I*K) ≤ J :=
  by 
    rw [le_div_iff, mul_le]

@[simp]
theorem one_le_one_div {I : Submodule R A} : 1 ≤ 1 / I ↔ I ≤ 1 :=
  by 
    split 
    all_goals 
      intro hI
    ·
      rwa [le_div_iff_mul_le, one_mulₓ] at hI
    ·
      rwa [le_div_iff_mul_le, one_mulₓ]

theorem le_self_mul_one_div {I : Submodule R A} (hI : I ≤ 1) : I ≤ I*1 / I :=
  by 
    rw [←mul_oneₓ I]
    apply mul_le_mul_right (one_le_one_div.mpr hI)

theorem mul_one_div_le_one {I : Submodule R A} : (I*1 / I) ≤ 1 :=
  by 
    rw [Submodule.mul_le]
    intro m hm n hn 
    rw [Submodule.mem_div_iff_forall_mul_mem] at hn 
    rw [mul_commₓ]
    exact hn m hm

@[simp]
theorem map_div {B : Type _} [CommRingₓ B] [Algebra R B] (I J : Submodule R A) (h : A ≃ₐ[R] B) :
  (I / J).map h.to_linear_map = I.map h.to_linear_map / J.map h.to_linear_map :=
  by 
    ext x 
    simp only [mem_map, mem_div_iff_forall_mul_mem]
    split 
    ·
      rintro ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact ⟨x*y, hx _ hy, h.map_mul x y⟩
    ·
      rintro hx 
      refine' ⟨h.symm x, fun z hz => _, h.apply_symm_apply x⟩
      obtain ⟨xz, xz_mem, hxz⟩ := hx (h z) ⟨z, hz, rfl⟩
      convert xz_mem 
      apply h.injective 
      erw [h.map_mul, h.apply_symm_apply, hxz]

end Quotientₓ

end CommRingₓ

end Submodule

