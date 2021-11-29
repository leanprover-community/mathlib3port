import Mathbin.Analysis.SpecialFunctions.Pow 
import Mathbin.RingTheory.ClassGroup 
import Mathbin.RingTheory.Norm 
import Mathbin.LinearAlgebra.FreeModule.Pid 
import Mathbin.LinearAlgebra.Matrix.AbsoluteValue 
import Mathbin.NumberTheory.ClassNumber.AdmissibleAbsoluteValue

/-!
# Class numbers of global fields
In this file, we use the notion of "admissible absolute value" to prove
finiteness of the class group for number fields and function fields,
and define `class_number` as the order of this group.
## Main definitions
 - `class_group.fintype_of_admissible`: if `R` has an admissible absolute value,
   its integral closure has a finite class group
-/


open_locale BigOperators

open_locale nonZeroDivisors

namespace ClassGroup

open Ringₓ

open_locale BigOperators

section EuclideanDomain

variable (R S K L : Type _) [EuclideanDomain R] [CommRingₓ S] [IsDomain S]

variable [Field K] [Field L]

variable [Algebra R K] [IsFractionRing R K]

variable [Algebra K L] [FiniteDimensional K L] [IsSeparable K L]

variable [algRL : Algebra R L] [IsScalarTower R K L]

variable [Algebra R S] [Algebra S L]

variable [ist : IsScalarTower R S L] [iic : IsIntegralClosure S R L]

variable {R S} (abv : AbsoluteValue R ℤ)

variable {ι : Type _} [DecidableEq ι] [Fintype ι] (bS : Basis ι R S)

/-- If `b` is an `R`-basis of `S` of cardinality `n`, then `norm_bound abv b` is an integer
such that for every `R`-integral element `a : S` with coordinates `≤ y`,
we have algebra.norm a ≤ norm_bound abv b * y ^ n`. (See also `norm_le` and `norm_lt`). -/
noncomputable def norm_bound : ℤ :=
  let n := Fintype.card ι 
  let i : ι := Nonempty.some bS.index_nonempty 
  let m : ℤ :=
    Finset.max' (Finset.univ.Image fun ijk : ι × ι × ι => abv (Algebra.leftMulMatrix bS (bS ijk.1) ijk.2.1 ijk.2.2))
      ⟨_, Finset.mem_image.mpr ⟨⟨i, i, i⟩, Finset.mem_univ _, rfl⟩⟩
  Nat.factorial n • (n • m^n)

theorem norm_bound_pos : 0 < norm_bound abv bS :=
  by 
    obtain ⟨i, j, k, hijk⟩ : ∃ i j k, Algebra.leftMulMatrix bS (bS i) j k ≠ 0
    ·
      byContra h 
      pushNeg  at h 
      obtain ⟨i⟩ := bS.index_nonempty 
      apply bS.ne_zero i 
      apply (Algebra.leftMulMatrix bS).injective_iff.mp (Algebra.left_mul_matrix_injective bS)
      ext j k 
      simp [h, Dmatrix.zero_apply]
    simp only [norm_bound, Algebra.smul_def, RingHom.eq_nat_cast, Int.nat_cast_eq_coe_nat]
    refine' mul_pos (int.coe_nat_pos.mpr (Nat.factorial_pos _)) _ 
    refine' pow_pos (mul_pos (int.coe_nat_pos.mpr (fintype.card_pos_iff.mpr ⟨i⟩)) _) _ 
    refine' lt_of_lt_of_leₓ (abv.pos hijk) (Finset.le_max' _ _ _)
    exact finset.mem_image.mpr ⟨⟨i, j, k⟩, Finset.mem_univ _, rfl⟩

/-- If the `R`-integral element `a : S` has coordinates `≤ y` with respect to some basis `b`,
its norm is less than `norm_bound abv b * y ^ dim S`. -/
theorem norm_le (a : S) {y : ℤ} (hy : ∀ k, abv (bS.repr a k) ≤ y) :
  abv (Algebra.norm R a) ≤ norm_bound abv bS*y^Fintype.card ι :=
  by 
    convLHS => rw [←bS.sum_repr a]
    rw [Algebra.norm_apply, ←LinearMap.det_to_matrix bS]
    simp only [Algebra.norm_apply, AlgHom.map_sum, AlgHom.map_smul, LinearEquiv.map_sum, LinearEquiv.map_smul,
      Algebra.to_matrix_lmul_eq, norm_bound, smul_mul_assoc, ←mul_powₓ]
    convert Matrix.det_sum_smul_le Finset.univ _ hy using 3
    ·
      rw [Finset.card_univ, smul_mul_assoc, mul_commₓ]
    ·
      intro i j k 
      apply Finset.le_max' 
      exact finset.mem_image.mpr ⟨⟨i, j, k⟩, Finset.mem_univ _, rfl⟩

-- error in NumberTheory.ClassNumber.Finite: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If the `R`-integral element `a : S` has coordinates `< y` with respect to some basis `b`,
its norm is strictly less than `norm_bound abv b * y ^ dim S`. -/
theorem norm_lt
{T : Type*}
[linear_ordered_comm_ring T]
(a : S)
{y : T}
(hy : ∀
 k, «expr < »((abv (bS.repr a k) : T), y)) : «expr < »((abv (algebra.norm R a) : T), «expr * »(norm_bound abv bS, «expr ^ »(y, fintype.card ι))) :=
begin
  obtain ["⟨", ident i, "⟩", ":=", expr bS.index_nonempty],
  have [ident him] [":", expr (finset.univ.image (λ
     k, abv (bS.repr a k))).nonempty] [":=", expr ⟨_, finset.mem_image.mpr ⟨i, finset.mem_univ _, rfl⟩⟩],
  set [] [ident y'] [":", expr exprℤ()] [":="] [expr finset.max' _ him] ["with", ident y'_def],
  have [ident hy'] [":", expr ∀ k, «expr ≤ »(abv (bS.repr a k), y')] [],
  { intro [ident k],
    exact [expr finset.le_max' _ _ (finset.mem_image.mpr ⟨k, finset.mem_univ _, rfl⟩)] },
  have [] [":", expr «expr < »((y' : T), y)] [],
  { rw ["[", expr y'_def, ",", "<-", expr finset.max'_image (show monotone (coe : exprℤ() → T), from λ
      x y h, int.cast_le.mpr h), "]"] [],
    apply [expr (finset.max'_lt_iff _ (him.image _)).mpr],
    simp [] [] ["only"] ["[", expr finset.mem_image, ",", expr exists_prop, "]"] [] [],
    rintros ["_", "⟨", ident x, ",", "⟨", ident k, ",", "-", ",", ident rfl, "⟩", ",", ident rfl, "⟩"],
    exact [expr hy k] },
  have [ident y'_nonneg] [":", expr «expr ≤ »(0, y')] [":=", expr le_trans (abv.nonneg _) (hy' i)],
  apply [expr (int.cast_le.mpr (norm_le abv bS a hy')).trans_lt],
  simp [] [] ["only"] ["[", expr int.cast_mul, ",", expr int.cast_pow, "]"] [] [],
  apply [expr mul_lt_mul' (le_refl _)],
  { exact [expr pow_lt_pow_of_lt_left this (int.cast_nonneg.mpr y'_nonneg) (fintype.card_pos_iff.mpr ⟨i⟩)] },
  { exact [expr pow_nonneg (int.cast_nonneg.mpr y'_nonneg) _] },
  { exact [expr int.cast_pos.mpr (norm_bound_pos abv bS)] },
  { apply_instance }
end

/-- A nonzero ideal has an element of minimal norm. -/
theorem exists_min (I : (Ideal S)⁰) :
  ∃ (b : _)(_ : b ∈ (I : Ideal S)),
    b ≠ 0 ∧ ∀ c _ : c ∈ (I : Ideal S), abv (Algebra.norm R c) < abv (Algebra.norm R b) → c = (0 : S) :=
  by 
    obtain ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩, min⟩ :=
      @Int.exists_least_of_bdd (fun a => ∃ (b : _)(_ : b ∈ (I : Ideal S)), b ≠ (0 : S) ∧ abv (Algebra.norm R b) = a) _ _
    ·
      refine' ⟨b, b_mem, b_ne_zero, _⟩
      intro c hc lt 
      contrapose! lt with c_ne_zero 
      exact min _ ⟨c, hc, c_ne_zero, rfl⟩
    ·
      use 0
      rintro _ ⟨b, b_mem, b_ne_zero, rfl⟩
      apply abv.nonneg
    ·
      obtain ⟨b, b_mem, b_ne_zero⟩ := (I : Ideal S).ne_bot_iff.mp (nonZeroDivisors.coe_ne_zero I)
      exact ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩⟩

section IsAdmissible

variable (L) {abv} (adm : abv.is_admissible)

include adm

/-- If we have a large enough set of elements in `R^ι`, then there will be a pair
whose remainders are close together. We'll show that all sets of cardinality
at least `cardM bS adm` elements satisfy this condition.

The value of `cardM` is not at all optimal: for specific choices of `R`,
the minimum cardinality can be exponentially smaller.
-/
noncomputable def cardM : ℕ :=
  adm.card (norm_bound abv bS^(-1 / Fintype.card ι : ℝ))^Fintype.card ι

variable [Infinite R]

/-- In the following results, we need a large set of distinct elements of `R`. -/
noncomputable def distinct_elems : Finₓ (cardM bS adm).succ ↪ R :=
  Function.Embedding.trans (Finₓ.coeEmbedding _).toEmbedding (Infinite.natEmbedding R)

variable [DecidableEq R]

/-- `finset_approx` is a finite set such that each fractional ideal in the integral closure
contains an element close to `finset_approx`. -/
noncomputable def finset_approx : Finset R :=
  ((Finset.univ.product Finset.univ).Image
        fun xy : _ × _ => distinct_elems bS adm xy.1 - distinct_elems bS adm xy.2).erase
    0

theorem finset_approx.zero_not_mem : (0 : R) ∉ finset_approx bS adm :=
  Finset.not_mem_erase _ _

@[simp]
theorem mem_finset_approx {x : R} :
  x ∈ finset_approx bS adm ↔ ∃ i j, i ≠ j ∧ distinct_elems bS adm i - distinct_elems bS adm j = x :=
  by 
    simp only [finset_approx, Finset.mem_erase, Finset.mem_image]
    split 
    ·
      rintro ⟨hx, ⟨i, j⟩, _, rfl⟩
      refine' ⟨i, j, _, rfl⟩
      rintro rfl 
      simpa using hx
    ·
      rintro ⟨i, j, hij, rfl⟩
      refine' ⟨_, ⟨i, j⟩, finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩
      rw [Ne.def, sub_eq_zero]
      exact fun h => hij ((distinct_elems bS adm).Injective h)

section Real

open Real

attribute [-instance] Real.decidableEq

-- error in NumberTheory.ClassNumber.Finite: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- We can approximate `a / b : L` with `q / r`, where `r` has finitely many options for `L`. -/
theorem exists_mem_finset_approx
(a : S)
{b}
(hb : «expr ≠ »(b, (0 : R))) : «expr∃ , »((q : S)
 (r «expr ∈ » finset_approx bS adm), «expr < »(abv (algebra.norm R «expr - »(«expr • »(r, a), «expr • »(b, q))), abv (algebra.norm R (algebra_map R S b)))) :=
begin
  have [ident dim_pos] [] [":=", expr fintype.card_pos_iff.mpr bS.index_nonempty],
  set [] [ident ε] [":", expr exprℝ()] [":="] [expr «expr ^ »(norm_bound abv bS, («expr / »(«expr- »(1), fintype.card ι) : exprℝ()))] ["with", ident ε_eq],
  have [ident hε] [":", expr «expr < »(0, ε)] [":=", expr real.rpow_pos_of_pos (int.cast_pos.mpr (norm_bound_pos abv bS)) _],
  have [ident ε_le] [":", expr «expr ≤ »(«expr * »((norm_bound abv bS : exprℝ()), «expr ^ »(«expr • »(abv b, ε), fintype.card ι)), «expr ^ »(abv b, fintype.card ι))] [],
  { have [] [] [":=", expr norm_bound_pos abv bS],
    have [] [] [":=", expr abv.nonneg b],
    rw ["[", expr ε_eq, ",", expr algebra.smul_def, ",", expr ring_hom.eq_int_cast, ",", "<-", expr rpow_nat_cast, ",", expr mul_rpow, ",", "<-", expr rpow_mul, ",", expr div_mul_cancel, ",", expr rpow_neg_one, ",", expr mul_left_comm, ",", expr mul_inv_cancel, ",", expr mul_one, ",", expr rpow_nat_cast, "]"] []; try { norm_cast [],
      linarith [] [] [] },
    { apply [expr rpow_nonneg_of_nonneg],
      norm_cast [],
      linarith [] [] [] } },
  let [ident μ] [":", expr «expr ↪ »(fin (cardM bS adm).succ, R)] [":=", expr distinct_elems bS adm],
  set [] [ident s] [] [":="] [expr bS.repr a] [],
  have [ident s_eq] [":", expr ∀ i, «expr = »(s i, bS.repr a i)] [":=", expr λ i, rfl],
  set [] [ident qs] [] [":="] [expr λ j i, «expr / »(«expr * »(μ j, s i), b)] [],
  have [ident q_eq] [":", expr ∀ j i, «expr = »(qs j i, «expr / »(«expr * »(μ j, s i), b))] [":=", expr λ i j, rfl],
  set [] [ident rs] [] [":="] [expr λ j i, «expr % »(«expr * »(μ j, s i), b)] ["with", ident r_eq],
  have [ident r_eq] [":", expr ∀ j i, «expr = »(rs j i, «expr % »(«expr * »(μ j, s i), b))] [":=", expr λ i j, rfl],
  have [ident μ_eq] [":", expr ∀ i j, «expr = »(«expr * »(μ j, s i), «expr + »(«expr * »(b, qs j i), rs j i))] [],
  { intros [ident i, ident j],
    rw ["[", expr q_eq, ",", expr r_eq, ",", expr euclidean_domain.div_add_mod, "]"] [] },
  have [ident μ_mul_a_eq] [":", expr ∀
   j, «expr = »(«expr • »(μ j, a), «expr + »(«expr • »(b, «expr∑ , »((i), «expr • »(qs j i, bS i))), «expr∑ , »((i), «expr • »(rs j i, bS i))))] [],
  { intro [ident j],
    rw ["<-", expr bS.sum_repr a] [],
    simp [] [] ["only"] ["[", expr finset.smul_sum, ",", "<-", expr finset.sum_add_distrib, "]"] [] [],
    refine [expr finset.sum_congr rfl (λ i _, _)],
    rw ["[", "<-", expr s_eq, ",", "<-", expr mul_smul, ",", expr μ_eq, ",", expr add_smul, ",", expr mul_smul, "]"] [] },
  obtain ["⟨", ident j, ",", ident k, ",", ident j_ne_k, ",", ident hjk, "⟩", ":=", expr adm.exists_approx hε hb (λ
    j i, «expr * »(μ j, s i))],
  have [ident hjk'] [":", expr ∀ i, «expr < »((abv «expr - »(rs k i, rs j i) : exprℝ()), «expr • »(abv b, ε))] [],
  { simpa [] [] ["only"] ["[", expr r_eq, "]"] [] ["using", expr hjk] },
  set [] [ident q] [] [":="] [expr «expr∑ , »((i), «expr • »(«expr - »(qs k i, qs j i), bS i))] ["with", ident q_eq],
  set [] [ident r] [] [":="] [expr «expr - »(μ k, μ j)] ["with", ident r_eq],
  refine [expr ⟨q, r, (mem_finset_approx bS adm).mpr _, _⟩],
  { exact [expr ⟨k, j, j_ne_k.symm, rfl⟩] },
  have [] [":", expr «expr = »(«expr - »(«expr • »(r, a), «expr • »(b, q)), «expr∑ , »((x : ι), «expr - »(«expr • »(rs k x, bS x), «expr • »(rs j x, bS x))))] [],
  { simp [] [] ["only"] ["[", expr r_eq, ",", expr sub_smul, ",", expr μ_mul_a_eq, ",", expr q_eq, ",", expr finset.smul_sum, ",", "<-", expr finset.sum_add_distrib, ",", "<-", expr finset.sum_sub_distrib, ",", expr smul_sub, "]"] [] [],
    refine [expr finset.sum_congr rfl (λ x _, _)],
    ring [] },
  rw ["[", expr this, ",", expr algebra.norm_algebra_map_of_basis bS, ",", expr abv.map_pow, "]"] [],
  refine [expr int.cast_lt.mp ((norm_lt abv bS _ (λ i, lt_of_le_of_lt _ (hjk' i))).trans_le _)],
  { apply [expr le_of_eq],
    congr,
    simp_rw ["[", expr linear_equiv.map_sum, ",", expr linear_equiv.map_sub, ",", expr linear_equiv.map_smul, ",", expr finset.sum_apply', ",", expr finsupp.sub_apply, ",", expr finsupp.smul_apply, ",", expr finset.sum_sub_distrib, ",", expr basis.repr_self_apply, ",", expr smul_eq_mul, ",", expr mul_boole, ",", expr finset.sum_ite_eq', ",", expr finset.mem_univ, ",", expr if_true, "]"] [] },
  { exact_mod_cast [expr ε_le] }
end

include ist iic

-- error in NumberTheory.ClassNumber.Finite: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- We can approximate `a / b : L` with `q / r`, where `r` has finitely many options for `L`. -/
theorem exists_mem_finset_approx'
(h : algebra.is_algebraic R L)
(a : S)
{b : S}
(hb : «expr ≠ »(b, 0)) : «expr∃ , »((q : S)
 (r «expr ∈ » finset_approx bS adm), «expr < »(abv (algebra.norm R «expr - »(«expr • »(r, a), «expr * »(q, b))), abv (algebra.norm R b))) :=
begin
  have [ident inj] [":", expr function.injective (algebra_map R L)] [],
  { rw [expr is_scalar_tower.algebra_map_eq R S L] [],
    exact [expr (is_integral_closure.algebra_map_injective S R L).comp bS.algebra_map_injective] },
  obtain ["⟨", ident a', ",", ident b', ",", ident hb', ",", ident h, "⟩", ":=", expr is_integral_closure.exists_smul_eq_mul h inj a hb],
  obtain ["⟨", ident q, ",", ident r, ",", ident hr, ",", ident hqr, "⟩", ":=", expr exists_mem_finset_approx bS adm a' hb'],
  refine [expr ⟨q, r, hr, _⟩],
  refine [expr lt_of_mul_lt_mul_left _ (show «expr ≤ »(0, abv (algebra.norm R (algebra_map R S b'))), from abv.nonneg _)],
  refine [expr lt_of_le_of_lt (le_of_eq _) (mul_lt_mul hqr (le_refl _) (abv.pos ((algebra.norm_ne_zero_iff_of_basis bS).mpr hb)) (abv.nonneg _))],
  rw ["[", "<-", expr abv.map_mul, ",", "<-", expr monoid_hom.map_mul, ",", "<-", expr abv.map_mul, ",", "<-", expr monoid_hom.map_mul, ",", "<-", expr algebra.smul_def, ",", expr smul_sub b', ",", expr sub_mul, ",", expr smul_comm, ",", expr h, ",", expr mul_comm b a', ",", expr algebra.smul_mul_assoc r a' b, ",", expr algebra.smul_mul_assoc b' q b, "]"] []
end

end Real

theorem prod_finset_approx_ne_zero : algebraMap R S (∏m in finset_approx bS adm, m) ≠ 0 :=
  by 
    refine' mt ((RingHom.injective_iff _).mp bS.algebra_map_injective _) _ 
    simp only [Finset.prod_eq_zero_iff, not_exists]
    rintro x hx rfl 
    exact finset_approx.zero_not_mem bS adm hx

theorem ne_bot_of_prod_finset_approx_mem (J : Ideal S) (h : algebraMap _ _ (∏m in finset_approx bS adm, m) ∈ J) :
  J ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, h, prod_finset_approx_ne_zero _ _⟩

include ist iic

-- error in NumberTheory.ClassNumber.Finite: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Each class in the class group contains an ideal `J`
such that `M := Π m ∈ finset_approx` is in `J`. -/
theorem exists_mk0_eq_mk0
[is_dedekind_domain S]
[is_fraction_ring S L]
(h : algebra.is_algebraic R L)
(I : «expr ⁰»(ideal S)) : «expr∃ , »((J : «expr ⁰»(ideal S)), «expr ∧ »(«expr = »(class_group.mk0 L I, class_group.mk0 L J), «expr ∈ »(algebra_map _ _ «expr∏ in , »((m), finset_approx bS adm, m), (J : ideal S)))) :=
begin
  set [] [ident M] [] [":="] [expr «expr∏ in , »((m), finset_approx bS adm, m)] ["with", ident M_eq],
  have [ident hM] [":", expr «expr ≠ »(algebra_map R S M, 0)] [":=", expr prod_finset_approx_ne_zero bS adm],
  obtain ["⟨", ident b, ",", ident b_mem, ",", ident b_ne_zero, ",", ident b_min, "⟩", ":=", expr exists_min abv I],
  suffices [] [":", expr «expr ∣ »(ideal.span {b}, «expr * »(ideal.span {algebra_map _ _ M}, I.1))],
  { obtain ["⟨", ident J, ",", ident hJ, "⟩", ":=", expr this],
    refine [expr ⟨⟨J, _⟩, _, _⟩],
    { rw [expr mem_non_zero_divisors_iff_ne_zero] [],
      rintro [ident rfl],
      rw ["[", expr ideal.zero_eq_bot, ",", expr ideal.mul_bot, "]"] ["at", ident hJ],
      exact [expr hM (ideal.span_singleton_eq_bot.mp (I.2 _ hJ))] },
    { rw [expr class_group.mk0_eq_mk0_iff] [],
      exact [expr ⟨algebra_map _ _ M, b, hM, b_ne_zero, hJ⟩] },
    rw ["[", "<-", expr set_like.mem_coe, ",", "<-", expr set.singleton_subset_iff, ",", "<-", expr ideal.span_le, ",", "<-", expr ideal.dvd_iff_le, "]"] [],
    refine [expr (mul_dvd_mul_iff_left _).mp _],
    swap,
    { exact [expr mt ideal.span_singleton_eq_bot.mp b_ne_zero] },
    rw ["[", expr subtype.coe_mk, ",", expr ideal.dvd_iff_le, ",", "<-", expr hJ, ",", expr mul_comm, "]"] [],
    apply [expr ideal.mul_mono le_rfl],
    rw ["[", expr ideal.span_le, ",", expr set.singleton_subset_iff, "]"] [],
    exact [expr b_mem] },
  rw ["[", expr ideal.dvd_iff_le, ",", expr ideal.mul_le, "]"] [],
  intros [ident r', ident hr', ident a, ident ha],
  rw [expr ideal.mem_span_singleton] ["at", "⊢", ident hr'],
  obtain ["⟨", ident q, ",", ident r, ",", ident r_mem, ",", ident lt, "⟩", ":=", expr exists_mem_finset_approx' L bS adm h a b_ne_zero],
  apply [expr @dvd_of_mul_left_dvd _ _ q],
  simp [] [] ["only"] ["[", expr algebra.smul_def, "]"] [] ["at", ident lt],
  rw ["<-", expr sub_eq_zero.mp (b_min _ (I.1.sub_mem (I.1.mul_mem_left _ ha) (I.1.mul_mem_left _ b_mem)) lt)] [],
  refine [expr mul_dvd_mul_right (dvd_trans (ring_hom.map_dvd _ _) hr') _],
  exact [expr multiset.dvd_prod (multiset.mem_map.mpr ⟨_, r_mem, rfl⟩)]
end

omit iic ist

/-- `class_group.mk_M_mem` is a specialization of `class_group.mk0` to (the finite set of)
ideals that contain `M := ∏ m in finset_approx L f abs, m`.
By showing this function is surjective, we prove that the class group is finite. -/
noncomputable def mk_M_mem [IsFractionRing S L] [IsDedekindDomain S]
  (J : { J : Ideal S // algebraMap _ _ (∏m in finset_approx bS adm, m) ∈ J }) : ClassGroup S L :=
  ClassGroup.mk0 _ ⟨J.1, mem_non_zero_divisors_iff_ne_zero.mpr (ne_bot_of_prod_finset_approx_mem bS adm J.1 J.2)⟩

include iic ist

theorem mk_M_mem_surjective [IsFractionRing S L] [IsDedekindDomain S] (h : Algebra.IsAlgebraic R L) :
  Function.Surjective (ClassGroup.mkMMem L bS adm) :=
  by 
    intro I' 
    obtain ⟨⟨I, hI⟩, rfl⟩ := ClassGroup.mk0_surjective I' 
    obtain ⟨J, mk0_eq_mk0, J_dvd⟩ := exists_mk0_eq_mk0 L bS adm h ⟨I, hI⟩
    exact ⟨⟨J, J_dvd⟩, mk0_eq_mk0.symm⟩

open_locale Classical

/-- The main theorem: the class group of an integral closure `S` of `R` in an
algebraic extension `L` is finite if there is an admissible absolute value.

See also `class_group.fintype_of_admissible_of_finite` where `L` is a finite
extension of `K = Frac(R)`, supplying most of the required assumptions automatically.
-/
noncomputable def fintype_of_admissible_of_algebraic [IsFractionRing S L] [IsDedekindDomain S]
  (h : Algebra.IsAlgebraic R L) : Fintype (ClassGroup S L) :=
  @Fintype.ofSurjective _ _ _
    (@Fintype.ofEquiv _ { J // J ∣ Ideal.span ({algebraMap R S (∏m : R in finset_approx bS adm, m)} : Set S) }
      (UniqueFactorizationMonoid.fintypeSubtypeDvd _
        (by 
          rw [Ne.def, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
          exact prod_finset_approx_ne_zero bS adm))
      ((Equiv.refl _).subtypeEquiv
        fun I =>
          Ideal.dvd_iff_le.trans
            (by 
              rw [Equiv.refl_apply, Ideal.span_le, Set.singleton_subset_iff])))
    (ClassGroup.mkMMem L bS adm) (ClassGroup.mk_M_mem_surjective L bS adm h)

-- error in NumberTheory.ClassNumber.Finite: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The main theorem: the class group of an integral closure `S` of `R` in a
finite extension `L` of `K = Frac(R)` is finite if there is an admissible
absolute value.

See also `class_group.fintype_of_admissible_of_algebraic` where `L` is an
algebraic extension of `R`, that includes some extra assumptions.
-/
noncomputable
def fintype_of_admissible_of_finite
[is_dedekind_domain R] : fintype (@class_group S L _ _ _ (is_integral_closure.is_fraction_ring_of_finite_extension R K L S)) :=
begin
  letI [] [] [":=", expr classical.dec_eq L],
  letI [] [] [":=", expr is_integral_closure.is_fraction_ring_of_finite_extension R K L S],
  letI [] [] [":=", expr is_integral_closure.is_dedekind_domain R K L S],
  choose [] [ident s] [ident b, ident hb_int] ["using", expr finite_dimensional.exists_is_basis_integral R K L],
  obtain ["⟨", ident n, ",", ident b, "⟩", ":=", expr submodule.basis_of_pid_of_le_span _ (is_integral_closure.range_le_span_dual_basis S b hb_int)],
  let [ident bS] [] [":=", expr b.map «expr ≪≫ₗ »((linear_map.quot_ker_equiv_range _).symm, _)],
  refine [expr fintype_of_admissible_of_algebraic L bS adm (λ
    x, (is_fraction_ring.is_algebraic_iff R K).mpr (algebra.is_algebraic_of_finite x))],
  { rw [expr linear_map.ker_eq_bot.mpr] [],
    { exact [expr submodule.quot_equiv_of_eq_bot _ rfl] },
    { exact [expr is_integral_closure.algebra_map_injective _ R _] } },
  { refine [expr (basis.linear_independent _).restrict_scalars _],
    simp [] [] ["only"] ["[", expr algebra.smul_def, ",", expr mul_one, "]"] [] [],
    apply [expr is_fraction_ring.injective] }
end

end IsAdmissible

end EuclideanDomain

end ClassGroup

