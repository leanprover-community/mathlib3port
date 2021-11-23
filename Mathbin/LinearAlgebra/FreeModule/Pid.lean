import Mathbin.LinearAlgebra.Dimension 
import Mathbin.RingTheory.PrincipalIdealDomain 
import Mathbin.RingTheory.Finiteness

/-! # Free modules over PID

A free `R`-module `M` is a module with a basis over `R`,
equivalently it is an `R`-module linearly equivalent to `ι →₀ R` for some `ι`.

This file proves a submodule of a free `R`-module of finite rank is also
a free `R`-module of finite rank, if `R` is a principal ideal domain (PID),
i.e. we have instances `[is_domain R] [is_principal_ideal_ring R]`.
We express "free `R`-module of finite rank" as a module `M` which has a basis
`b : ι → R`, where `ι` is a `fintype`.
We call the cardinality of `ι` the rank of `M` in this file;
it would be equal to `finrank R M` if `R` is a field and `M` is a vector space.

## Main results

In this section, `M` is a free and finitely generated `R`-module, and
`N` is a submodule of `M`.

 - `submodule.induction_on_rank`: if `P` holds for `⊥ : submodule R M` and if
  `P N` follows from `P N'` for all `N'` that are of lower rank, then `P` holds
   on all submodules

 - `submodule.exists_basis_of_pid`: if `R` is a PID, then `N : submodule R M` is
   free and finitely generated. This is the first part of the structure theorem
   for modules.

- `submodule.smith_normal_form`: if `R` is a PID, then `M` has a basis
  `bM` and `N` has a basis `bN` such that `bN i = a i • bM i`.
  Equivalently, a linear map `f : M →ₗ M` with `range f = N` can be written as
  a matrix in Smith normal form, a diagonal matrix with the coefficients `a i`
  along the diagonal.

## Tags

free module, finitely generated module, rank, structure theorem

-/


open_locale BigOperators

universe u v

section Ringₓ

variable{R : Type u}{M : Type v}[Ringₓ R][AddCommGroupₓ M][Module R M]

variable{ι : Type _}(b : Basis ι R M)

open Submodule.IsPrincipal Submodule

theorem eq_bot_of_generator_maximal_map_eq_zero (b : Basis ι R M) {N : Submodule R M} {ϕ : M →ₗ[R] R}
  (hϕ : ∀ ψ : M →ₗ[R] R, N.map ϕ ≤ N.map ψ → N.map ψ = N.map ϕ) [(N.map ϕ).IsPrincipal]
  (hgen : generator (N.map ϕ) = 0) : N = ⊥ :=
  by 
    rw [Submodule.eq_bot_iff]
    intro x hx 
    refine' b.ext_elem fun i => _ 
    rw [(eq_bot_iff_generator_eq_zero _).mpr hgen] at hϕ 
    rw [LinearEquiv.map_zero, Finsupp.zero_apply]
    exact (Submodule.eq_bot_iff _).mp (hϕ (Finsupp.lapply i ∘ₗ «expr↑ » b.repr) bot_le) _ ⟨x, hx, rfl⟩

theorem eq_bot_of_generator_maximal_submodule_image_eq_zero {N O : Submodule R M} (b : Basis ι R O) (hNO : N ≤ O)
  {ϕ : O →ₗ[R] R}
  (hϕ : ∀ ψ : O →ₗ[R] R, ϕ.submodule_image N ≤ ψ.submodule_image N → ψ.submodule_image N = ϕ.submodule_image N)
  [(ϕ.submodule_image N).IsPrincipal] (hgen : generator (ϕ.submodule_image N) = 0) : N = ⊥ :=
  by 
    rw [Submodule.eq_bot_iff]
    intro x hx 
    refine' congr_argₓ coeₓ (show (⟨x, hNO hx⟩ : O) = 0 from b.ext_elem fun i => _)
    rw [(eq_bot_iff_generator_eq_zero _).mpr hgen] at hϕ 
    rw [LinearEquiv.map_zero, Finsupp.zero_apply]
    refine' (Submodule.eq_bot_iff _).mp (hϕ (Finsupp.lapply i ∘ₗ «expr↑ » b.repr) bot_le) _ _ 
    exact (LinearMap.mem_submodule_image_of_le hNO).mpr ⟨x, hx, rfl⟩

end Ringₓ

section IsDomain

variable{ι : Type _}{R : Type _}[CommRingₓ R][IsDomain R]

variable{M : Type _}[AddCommGroupₓ M][Module R M]{b : ι → M}

open Submodule.IsPrincipal Set Submodule

theorem dvd_generator_iff {I : Ideal R} [I.is_principal] {x : R} (hx : x ∈ I) : x ∣ generator I ↔ I = Ideal.span {x} :=
  by 
    convRHS => rw [←span_singleton_generator I]
    erw [Ideal.span_singleton_eq_span_singleton, ←dvd_dvd_iff_associated, ←mem_iff_generator_dvd]
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩

end IsDomain

section PrincipalIdealDomain

open Submodule.IsPrincipal Set Submodule

variable{ι : Type _}{R : Type _}[CommRingₓ R][IsDomain R][IsPrincipalIdealRing R]

variable{M : Type _}[AddCommGroupₓ M][Module R M]{b : ι → M}

open Submodule.IsPrincipal

-- error in LinearAlgebra.FreeModule.Pid: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem generator_maximal_submodule_image_dvd
{N O : submodule R M}
(hNO : «expr ≤ »(N, O))
{ϕ : «expr →ₗ[ ] »(O, R, R)}
(hϕ : ∀
 ψ : «expr →ₗ[ ] »(O, R, R), «expr ≤ »(ϕ.submodule_image N, ψ.submodule_image N) → «expr = »(ψ.submodule_image N, ϕ.submodule_image N))
[(ϕ.submodule_image N).is_principal]
(y : M)
(yN : «expr ∈ »(y, N))
(ϕy_eq : «expr = »(ϕ ⟨y, hNO yN⟩, generator (ϕ.submodule_image N)))
(ψ : «expr →ₗ[ ] »(O, R, R)) : «expr ∣ »(generator (ϕ.submodule_image N), ψ ⟨y, hNO yN⟩) :=
begin
  let [ident a] [":", expr R] [":=", expr generator (ϕ.submodule_image N)],
  let [ident d] [":", expr R] [":=", expr is_principal.generator (submodule.span R {a, ψ ⟨y, hNO yN⟩})],
  have [ident d_dvd_left] [":", expr «expr ∣ »(d, a)] [":=", expr (mem_iff_generator_dvd _).mp (subset_span (mem_insert _ _))],
  have [ident d_dvd_right] [":", expr «expr ∣ »(d, ψ ⟨y, hNO yN⟩)] [":=", expr (mem_iff_generator_dvd _).mp (subset_span (mem_insert_of_mem _ (mem_singleton _)))],
  refine [expr dvd_trans _ d_dvd_right],
  rw ["[", expr dvd_generator_iff, ",", expr ideal.span, ",", "<-", expr span_singleton_generator (submodule.span R {a, ψ ⟨y, hNO yN⟩}), "]"] [],
  obtain ["⟨", ident r₁, ",", ident r₂, ",", ident d_eq, "⟩", ":", expr «expr∃ , »((r₁
     r₂ : R), «expr = »(d, «expr + »(«expr * »(r₁, a), «expr * »(r₂, ψ ⟨y, hNO yN⟩))))],
  { obtain ["⟨", ident r₁, ",", ident r₂', ",", ident hr₂', ",", ident hr₁, "⟩", ":=", expr mem_span_insert.mp (is_principal.generator_mem (submodule.span R {a, ψ ⟨y, hNO yN⟩}))],
    obtain ["⟨", ident r₂, ",", ident rfl, "⟩", ":=", expr mem_span_singleton.mp hr₂'],
    exact [expr ⟨r₁, r₂, hr₁⟩] },
  let [ident ψ'] [":", expr «expr →ₗ[ ] »(O, R, R)] [":=", expr «expr + »(«expr • »(r₁, ϕ), «expr • »(r₂, ψ))],
  have [] [":", expr «expr ≤ »(span R {d}, ψ'.submodule_image N)] [],
  { rw ["[", expr span_le, ",", expr singleton_subset_iff, ",", expr set_like.mem_coe, ",", expr linear_map.mem_submodule_image_of_le hNO, "]"] [],
    refine [expr ⟨y, yN, _⟩],
    change [expr «expr = »(«expr + »(«expr * »(r₁, ϕ ⟨y, hNO yN⟩), «expr * »(r₂, ψ ⟨y, hNO yN⟩)), d)] [] [],
    rw ["[", expr d_eq, ",", expr ϕy_eq, "]"] [] },
  refine [expr le_antisymm (this.trans (le_of_eq _)) (ideal.span_singleton_le_span_singleton.mpr d_dvd_left)],
  rw [expr span_singleton_generator] [],
  refine [expr hϕ ψ' (le_trans _ this)],
  rw ["[", "<-", expr span_singleton_generator (ϕ.submodule_image N), "]"] [],
  exact [expr ideal.span_singleton_le_span_singleton.mpr d_dvd_left],
  { exact [expr subset_span (mem_insert _ _)] }
end

-- error in LinearAlgebra.FreeModule.Pid: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The induction hypothesis of `submodule.basis_of_pid` and `submodule.smith_normal_form`.

Basically, it says: let `N ≤ M` be a pair of submodules, then we can find a pair of
submodules `N' ≤ M'` of strictly smaller rank, whose basis we can extend to get a basis
of `N` and `M`. Moreover, if the basis for `M'` is up to scalars a basis for `N'`,
then the basis we find for `M` is up to scalars a basis for `N`.

For `basis_of_pid` we only need the first half and can fix `M = ⊤`,
for `smith_normal_form` we need the full statement,
but must also feed in a basis for `M` using `basis_of_pid` to keep the induction going.
-/
theorem submodule.basis_of_pid_aux
[fintype ι]
{O : Type*}
[add_comm_group O]
[module R O]
(M N : submodule R O)
(b'M : basis ι R M)
(N_bot : «expr ≠ »(N, «expr⊥»()))
(N_le_M : «expr ≤ »(N, M)) : «expr∃ , »((y «expr ∈ » M)
 (a : R)
 (hay : «expr ∈ »(«expr • »(a, y), N))
 (M' «expr ≤ » M)
 (N' «expr ≤ » N)
 (N'_le_M' : «expr ≤ »(N', M'))
 (y_ortho_M' : ∀ (c : R) (z : O), «expr ∈ »(z, M') → «expr = »(«expr + »(«expr • »(c, y), z), 0) → «expr = »(c, 0))
 (ay_ortho_N' : ∀
  (c : R)
  (z : O), «expr ∈ »(z, N') → «expr = »(«expr + »(«expr • »(c, «expr • »(a, y)), z), 0) → «expr = »(c, 0)), ∀
 (n')
 (bN' : basis (fin n') R N'), «expr∃ , »((bN : basis (fin «expr + »(n', 1)) R N), ∀
  (m')
  (hn'm' : «expr ≤ »(n', m'))
  (bM' : basis (fin m') R M'), «expr∃ , »((hnm : «expr ≤ »(«expr + »(n', 1), «expr + »(m', 1)))
   (bM : basis (fin «expr + »(m', 1)) R M), ∀
   (as : fin n' → R)
   (h : ∀
    i : fin n', «expr = »((bN' i : O), «expr • »(as i, (bM' (fin.cast_le hn'm' i) : O)))), «expr∃ , »((as' : fin «expr + »(n', 1) → R), ∀
    i : fin «expr + »(n', 1), «expr = »((bN i : O), «expr • »(as' i, (bM (fin.cast_le hnm i) : O))))))) :=
begin
  have [] [":", expr «expr∃ , »((ϕ : «expr →ₗ[ ] »(M, R, R)), ∀
    ψ : «expr →ₗ[ ] »(M, R, R), «expr ≤ »(ϕ.submodule_image N, ψ.submodule_image N) → «expr = »(ψ.submodule_image N, ϕ.submodule_image N))] [],
  { obtain ["⟨", ident P, ",", ident P_eq, ",", ident P_max, "⟩", ":=", expr set_has_maximal_iff_noetherian.mpr (infer_instance : is_noetherian R R) _ (show (set.range (λ
        ψ : «expr →ₗ[ ] »(M, R, R), ψ.submodule_image N)).nonempty, from ⟨_, set.mem_range.mpr ⟨0, rfl⟩⟩)],
    obtain ["⟨", ident ϕ, ",", ident rfl, "⟩", ":=", expr set.mem_range.mp P_eq],
    exact [expr ⟨ϕ, λ ψ hψ, P_max _ ⟨_, rfl⟩ hψ⟩] },
  let [ident ϕ] [] [":=", expr this.some],
  have [ident ϕ_max] [] [":=", expr this.some_spec],
  let [ident a] [] [":=", expr generator (ϕ.submodule_image N)],
  have [ident a_mem] [":", expr «expr ∈ »(a, ϕ.submodule_image N)] [":=", expr generator_mem _],
  by_cases [expr a_zero, ":", expr «expr = »(a, 0)],
  { have [] [] [":=", expr eq_bot_of_generator_maximal_submodule_image_eq_zero b'M N_le_M ϕ_max a_zero],
    contradiction },
  obtain ["⟨", ident y, ",", ident yN, ",", ident ϕy_eq, "⟩", ":=", expr (linear_map.mem_submodule_image_of_le N_le_M).mp a_mem],
  have [ident ϕy_ne_zero] [":", expr «expr ≠ »(ϕ ⟨y, N_le_M yN⟩, 0)] [":=", expr λ h, a_zero (ϕy_eq.symm.trans h)],
  have [ident hdvd] [":", expr ∀
   i, «expr ∣ »(a, b'M.coord i ⟨y, N_le_M yN⟩)] [":=", expr λ
   i, generator_maximal_submodule_image_dvd N_le_M ϕ_max y yN ϕy_eq (b'M.coord i)],
  choose [] [ident c] [ident hc] ["using", expr hdvd],
  let [ident y'] [":", expr O] [":=", expr «expr∑ , »((i), «expr • »(c i, b'M i))],
  have [ident y'M] [":", expr «expr ∈ »(y', M)] [":=", expr M.sum_mem (λ i _, M.smul_mem (c i) (b'M i).2)],
  have [ident mk_y'] [":", expr «expr = »((⟨y', y'M⟩ : M), «expr∑ , »((i), «expr • »(c i, b'M i)))] [":=", expr subtype.ext (show «expr = »(y', M.subtype _), by { simp [] [] ["only"] ["[", expr linear_map.map_sum, ",", expr linear_map.map_smul, "]"] [] [],
      refl })],
  have [ident a_smul_y'] [":", expr «expr = »(«expr • »(a, y'), y)] [],
  { refine [expr congr_arg coe (show «expr = »((«expr • »(a, ⟨y', y'M⟩) : M), ⟨y, N_le_M yN⟩), from _)],
    rw ["[", "<-", expr b'M.sum_repr ⟨y, N_le_M yN⟩, ",", expr mk_y', ",", expr finset.smul_sum, "]"] [],
    refine [expr finset.sum_congr rfl (λ i _, _)],
    rw ["[", "<-", expr mul_smul, ",", "<-", expr hc, "]"] [],
    refl },
  refine [expr ⟨y', y'M, a, «expr ▸ »(a_smul_y'.symm, yN), _⟩],
  have [ident ϕy'_eq] [":", expr «expr = »(ϕ ⟨y', y'M⟩, 1)] [":=", expr mul_left_cancel₀ a_zero (calc
      «expr = »(«expr • »(a, ϕ ⟨y', y'M⟩), ϕ ⟨«expr • »(a, y'), _⟩) : (ϕ.map_smul a ⟨y', y'M⟩).symm
      «expr = »(..., ϕ ⟨y, N_le_M yN⟩) : by simp [] [] ["only"] ["[", expr a_smul_y', "]"] [] []
      «expr = »(..., a) : ϕy_eq
      «expr = »(..., «expr * »(a, 1)) : (mul_one a).symm)],
  have [ident ϕy'_ne_zero] [":", expr «expr ≠ »(ϕ ⟨y', y'M⟩, 0)] [":=", expr by simpa [] [] ["only"] ["[", expr ϕy'_eq, "]"] [] ["using", expr one_ne_zero]],
  let [ident M'] [":", expr submodule R O] [":=", expr ϕ.ker.map M.subtype],
  let [ident N'] [":", expr submodule R O] [":=", expr (ϕ.comp (of_le N_le_M)).ker.map N.subtype],
  have [ident M'_le_M] [":", expr «expr ≤ »(M', M)] [":=", expr M.map_subtype_le ϕ.ker],
  have [ident N'_le_M'] [":", expr «expr ≤ »(N', M')] [],
  { intros [ident x, ident hx],
    simp [] [] ["only"] ["[", expr mem_map, ",", expr linear_map.mem_ker, "]"] [] ["at", ident hx, "⊢"],
    obtain ["⟨", "⟨", ident x, ",", ident xN, "⟩", ",", ident hx, ",", ident rfl, "⟩", ":=", expr hx],
    exact [expr ⟨⟨x, N_le_M xN⟩, hx, rfl⟩] },
  have [ident N'_le_N] [":", expr «expr ≤ »(N', N)] [":=", expr N.map_subtype_le (ϕ.comp (of_le N_le_M)).ker],
  refine [expr ⟨M', M'_le_M, N', N'_le_N, N'_le_M', _⟩],
  have [ident y'_ortho_M'] [":", expr ∀
   (c : R)
   (z «expr ∈ » M'), «expr = »(«expr + »(«expr • »(c, y'), z), 0) → «expr = »(c, 0)] [],
  { intros [ident c, ident x, ident xM', ident hc],
    obtain ["⟨", "⟨", ident x, ",", ident xM, "⟩", ",", ident hx', ",", ident rfl, "⟩", ":=", expr submodule.mem_map.mp xM'],
    rw [expr linear_map.mem_ker] ["at", ident hx'],
    have [ident hc'] [":", expr «expr = »((«expr + »(«expr • »(c, ⟨y', y'M⟩), ⟨x, xM⟩) : M), 0)] [":=", expr subtype.coe_injective hc],
    simpa [] [] ["only"] ["[", expr linear_map.map_add, ",", expr linear_map.map_zero, ",", expr linear_map.map_smul, ",", expr smul_eq_mul, ",", expr add_zero, ",", expr mul_eq_zero, ",", expr ϕy'_ne_zero, ",", expr hx', ",", expr or_false, "]"] [] ["using", expr congr_arg ϕ hc'] },
  have [ident ay'_ortho_N'] [":", expr ∀
   (c : R)
   (z «expr ∈ » N'), «expr = »(«expr + »(«expr • »(c, «expr • »(a, y')), z), 0) → «expr = »(c, 0)] [],
  { intros [ident c, ident z, ident zN', ident hc],
    refine [expr (mul_eq_zero.mp (y'_ortho_M' «expr * »(a, c) z (N'_le_M' zN') _)).resolve_left a_zero],
    rw ["[", expr mul_comm, ",", expr mul_smul, ",", expr hc, "]"] [] },
  refine [expr ⟨y'_ortho_M', ay'_ortho_N', λ n' bN', ⟨_, _⟩⟩],
  { refine [expr basis.mk_fin_cons_of_le y yN bN' N'_le_N _ _],
    { intros [ident c, ident z, ident zN', ident hc],
      refine [expr ay'_ortho_N' c z zN' _],
      rwa ["<-", expr a_smul_y'] ["at", ident hc] },
    { intros [ident z, ident zN],
      obtain ["⟨", ident b, ",", ident hb, "⟩", ":", expr «expr ∣ »(_, ϕ ⟨z, N_le_M zN⟩), ":=", expr generator_submodule_image_dvd_of_mem N_le_M ϕ zN],
      refine [expr ⟨«expr- »(b), submodule.mem_map.mpr ⟨⟨_, N.sub_mem zN (N.smul_mem b yN)⟩, _, _⟩⟩],
      { refine [expr linear_map.mem_ker.mpr (show «expr = »(ϕ «expr - »(⟨z, N_le_M zN⟩, «expr • »(b, ⟨y, N_le_M yN⟩)), 0), from _)],
        rw ["[", expr linear_map.map_sub, ",", expr linear_map.map_smul, ",", expr hb, ",", expr ϕy_eq, ",", expr smul_eq_mul, ",", expr mul_comm, ",", expr sub_self, "]"] [] },
      { simp [] [] ["only"] ["[", expr sub_eq_add_neg, ",", expr neg_smul, "]"] [] [],
        refl } } },
  intros [ident m', ident hn'm', ident bM'],
  refine [expr ⟨nat.succ_le_succ hn'm', _, _⟩],
  { refine [expr basis.mk_fin_cons_of_le y' y'M bM' M'_le_M y'_ortho_M' _],
    intros [ident z, ident zM],
    refine [expr ⟨«expr- »(ϕ ⟨z, zM⟩), ⟨«expr - »(⟨z, zM⟩, «expr • »(ϕ ⟨z, zM⟩, ⟨y', y'M⟩)), linear_map.mem_ker.mpr _, _⟩⟩],
    { rw ["[", expr linear_map.map_sub, ",", expr linear_map.map_smul, ",", expr ϕy'_eq, ",", expr smul_eq_mul, ",", expr mul_one, ",", expr sub_self, "]"] [] },
    { rw ["[", expr linear_map.map_sub, ",", expr linear_map.map_smul, ",", expr sub_eq_add_neg, ",", expr neg_smul, "]"] [],
      refl } },
  intros [ident as, ident h],
  refine [expr ⟨fin.cons a as, _⟩],
  intro [ident i],
  rw ["[", expr basis.coe_mk_fin_cons_of_le, ",", expr basis.coe_mk_fin_cons_of_le, "]"] [],
  refine [expr fin.cases _ (λ i, _) i],
  { simp [] [] ["only"] ["[", expr fin.cons_zero, ",", expr fin.cast_le_zero, "]"] [] [],
    exact [expr a_smul_y'.symm] },
  { rw [expr fin.cast_le_succ] [],
    simp [] [] ["only"] ["[", expr fin.cons_succ, ",", expr coe_of_le, ",", expr h i, "]"] [] [] }
end

-- error in LinearAlgebra.FreeModule.Pid: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A submodule of a free `R`-module of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain.

This is a `lemma` to make the induction a bit easier. To actually access the basis,
see `submodule.basis_of_pid`.

See also the stronger version `submodule.smith_normal_form`.
-/
theorem submodule.nonempty_basis_of_pid
{ι : Type*}
[fintype ι]
(b : basis ι R M)
(N : submodule R M) : «expr∃ , »((n : exprℕ()), nonempty (basis (fin n) R N)) :=
begin
  haveI [] [] [":=", expr classical.dec_eq M],
  refine [expr N.induction_on_rank b _ _],
  intros [ident N, ident ih],
  let [ident b'] [] [":=", expr (b.reindex (fintype.equiv_fin ι)).map (linear_equiv.of_top _ rfl).symm],
  by_cases [expr N_bot, ":", expr «expr = »(N, «expr⊥»())],
  { subst [expr N_bot],
    exact [expr ⟨0, ⟨basis.empty _⟩⟩] },
  obtain ["⟨", ident y, ",", "-", ",", ident a, ",", ident hay, ",", ident M', ",", "-", ",", ident N', ",", ident N'_le_N, ",", "-", ",", "-", ",", ident ay_ortho, ",", ident h', "⟩", ":=", expr submodule.basis_of_pid_aux «expr⊤»() N b' N_bot le_top],
  obtain ["⟨", ident n', ",", "⟨", ident bN', "⟩", "⟩", ":=", expr ih N' N'_le_N _ hay ay_ortho],
  obtain ["⟨", ident bN, ",", ident hbN, "⟩", ":=", expr h' n' bN'],
  exact [expr ⟨«expr + »(n', 1), ⟨bN⟩⟩]
end

/-- A submodule of a free `R`-module of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain.

See also the stronger version `submodule.smith_normal_form`.
-/
noncomputable def Submodule.basisOfPid {ι : Type _} [Fintype ι] (b : Basis ι R M) (N : Submodule R M) :
  Σn : ℕ, Basis (Finₓ n) R N :=
  ⟨_, (N.nonempty_basis_of_pid b).some_spec.some⟩

-- error in LinearAlgebra.FreeModule.Pid: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem submodule.basis_of_pid_bot
{ι : Type*}
[fintype ι]
(b : basis ι R M) : «expr = »(submodule.basis_of_pid b «expr⊥»(), ⟨0, basis.empty _⟩) :=
begin
  obtain ["⟨", ident n, ",", ident b', "⟩", ":=", expr submodule.basis_of_pid b «expr⊥»()],
  let [ident e] [":", expr «expr ≃ »(fin n, fin 0)] [":=", expr b'.index_equiv (basis.empty _ : basis (fin 0) R («expr⊥»() : submodule R M))],
  have [] [":", expr «expr = »(n, 0)] [":=", expr by simpa [] [] [] [] [] ["using", expr fintype.card_eq.mpr ⟨e⟩]],
  subst [expr this],
  exact [expr sigma.eq rfl «expr $ »(basis.eq_of_apply_eq, fin_zero_elim)]
end

/-- A submodule inside a free `R`-submodule of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain.

See also the stronger version `submodule.smith_normal_form_of_le`.
-/
noncomputable def Submodule.basisOfPidOfLe {ι : Type _} [Fintype ι] {N O : Submodule R M} (hNO : N ≤ O)
  (b : Basis ι R O) : Σn : ℕ, Basis (Finₓ n) R N :=
  let ⟨n, bN'⟩ := Submodule.basisOfPid b (N.comap O.subtype)
  ⟨n, bN'.map (Submodule.comapSubtypeEquivOfLe hNO)⟩

/-- A submodule inside the span of a linear independent family is a free `R`-module of finite rank,
if `R` is a principal ideal domain. -/
noncomputable def Submodule.basisOfPidOfLeSpan {ι : Type _} [Fintype ι] {b : ι → M} (hb : LinearIndependent R b)
  {N : Submodule R M} (le : N ≤ Submodule.span R (Set.Range b)) : Σn : ℕ, Basis (Finₓ n) R N :=
  Submodule.basisOfPidOfLe le (Basis.span hb)

variable{M}

-- error in LinearAlgebra.FreeModule.Pid: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A finite type torsion free module over a PID is free. -/
noncomputable
def module.free_of_finite_type_torsion_free
[fintype ι]
{s : ι → M}
(hs : «expr = »(span R (range s), «expr⊤»()))
[no_zero_smul_divisors R M] : «exprΣ , »((n : exprℕ()), basis (fin n) R M) :=
begin
  classical,
  have [] [] [":=", expr exists_maximal_independent R s],
  let [ident I] [":", expr set ι] [":=", expr this.some],
  obtain ["⟨", ident indepI, ":", expr linear_independent R («expr ∘ »(s, coe) : I → M), ",", ident hI, ":", expr ∀
   i «expr ∉ » I, «expr∃ , »((a : R), «expr ∧ »(«expr ≠ »(a, 0), «expr ∈ »(«expr • »(a, s i), span R «expr '' »(s, I)))), "⟩", ":=", expr this.some_spec],
  let [ident N] [] [":=", expr span R «expr $ »(range, («expr ∘ »(s, coe) : I → M))],
  let [ident sI] [":", expr I → N] [":=", expr λ i, ⟨s i.1, subset_span (mem_range_self i)⟩],
  let [ident sI_basis] [":", expr basis I R N] [],
  from [expr basis.span indepI],
  have [ident exists_a] [":", expr ∀
   i : ι, «expr∃ , »((a : R), «expr ∧ »(«expr ≠ »(a, 0), «expr ∈ »(«expr • »(a, s i), N)))] [],
  { intro [ident i],
    by_cases [expr hi, ":", expr «expr ∈ »(i, I)],
    { use ["[", expr 1, ",", expr zero_ne_one.symm, "]"],
      rw [expr one_smul] [],
      exact [expr subset_span (mem_range_self (⟨i, hi⟩ : I))] },
    { simpa [] [] [] ["[", expr image_eq_range s I, "]"] [] ["using", expr hI i hi] } },
  choose [] [ident a] [ident ha, ident ha'] ["using", expr exists_a],
  let [ident A] [] [":=", expr «expr∏ , »((i), a i)],
  have [ident hA] [":", expr «expr ≠ »(A, 0)] [],
  { rw [expr finset.prod_ne_zero_iff] [],
    simpa [] [] [] [] [] ["using", expr ha] },
  let [ident φ] [":", expr «expr →ₗ[ ] »(M, R, M)] [":=", expr linear_map.lsmul R M A],
  have [] [":", expr «expr = »(φ.ker, «expr⊥»())] [],
  from [expr linear_map.ker_lsmul hA],
  let [ident ψ] [":", expr «expr ≃ₗ[ ] »(M, R, φ.range)] [":=", expr linear_equiv.of_injective φ (linear_map.ker_eq_bot.mp this)],
  have [] [":", expr «expr ≤ »(φ.range, N)] [],
  { suffices [] [":", expr ∀ i, «expr ∈ »(φ (s i), N)],
    { rw ["[", expr linear_map.range_eq_map, ",", "<-", expr hs, ",", expr φ.map_span_le, "]"] [],
      rintros ["_", "⟨", ident i, ",", ident rfl, "⟩"],
      apply [expr this] },
    intro [ident i],
    calc
      «expr = »(«expr • »(«expr∏ , »((j), a j), s i), «expr • »(«expr∏ in , »((j), «expr ᶜ»({i}), a j), «expr • »(a i, s i))) : by rw ["[", expr fintype.prod_eq_prod_compl_mul i, ",", expr mul_smul, "]"] []
      «expr ∈ »(..., N) : N.smul_mem _ (ha' i) },
  obtain ["⟨", ident n, ",", ident b, ":", expr basis (fin n) R φ.range, "⟩", ":=", expr submodule.basis_of_pid_of_le this sI_basis],
  exact [expr ⟨n, b.map ψ.symm⟩]
end

/-- A finite type torsion free module over a PID is free. -/
noncomputable def Module.freeOfFiniteTypeTorsionFree' [Module.Finite R M] [NoZeroSmulDivisors R M] :
  Σn : ℕ, Basis (Finₓ n) R M :=
  Module.freeOfFiniteTypeTorsionFree Module.Finite.exists_fin.some_spec.some_spec

section SmithNormal

/-- A Smith normal form basis for a submodule `N` of a module `M` consists of
bases for `M` and `N` such that the inclusion map `N → M` can be written as a
(rectangular) matrix with `a` along the diagonal: in Smith normal form. -/
@[nolint has_inhabited_instance]
structure Basis.SmithNormalForm(N : Submodule R M)(ι : Type _)(n : ℕ) where 
  bM : Basis ι R M 
  bN : Basis (Finₓ n) R N 
  f : Finₓ n ↪ ι 
  a : Finₓ n → R 
  snf : ∀ i, (bN i : M) = a i • bM (f i)

/-- If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagonal matrix
in Smith normal form.

See `submodule.smith_normal_form_of_le` for a version of this theorem that returns
a `basis.smith_normal_form`.

This is a strengthening of `submodule.basis_of_pid_of_le`.
-/
theorem Submodule.exists_smith_normal_form_of_le [Fintype ι] (b : Basis ι R M) (N O : Submodule R M) (N_le_O : N ≤ O) :
  ∃ (n o : ℕ)(hno : n ≤ o)(bO : Basis (Finₓ o) R O)(bN : Basis (Finₓ n) R N)(a : Finₓ n → R),
    ∀ i, (bN i : M) = a i • bO (Finₓ.castLe hno i) :=
  by 
    revert N 
    refine' induction_on_rank b _ _ O 
    intro M ih N N_le_M 
    obtain ⟨m, b'M⟩ := M.basis_of_pid b 
    byCases' N_bot : N = ⊥
    ·
      subst N_bot 
      exact ⟨0, m, Nat.zero_leₓ _, b'M, Basis.empty _, finZeroElim, finZeroElim⟩
    obtain ⟨y, hy, a, hay, M', M'_le_M, N', N'_le_N, N'_le_M', y_ortho, ay_ortho, h⟩ :=
      Submodule.basis_of_pid_aux M N b'M N_bot N_le_M 
    obtain ⟨n', m', hn'm', bM', bN', as', has'⟩ := ih M' M'_le_M y hy y_ortho N' N'_le_M' 
    obtain ⟨bN, h'⟩ := h n' bN' 
    obtain ⟨hmn, bM, h''⟩ := h' m' hn'm' bM' 
    obtain ⟨as, has⟩ := h'' as' has' 
    exact ⟨_, _, hmn, bM, bN, as, has⟩

/-- If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagonal matrix
in Smith normal form.

See `submodule.exists_smith_normal_form_of_le` for a version of this theorem that doesn't
need to map `N` into a submodule of `O`.

This is a strengthening of `submodule.basis_of_pid_of_le`.
-/
noncomputable def Submodule.smithNormalFormOfLe [Fintype ι] (b : Basis ι R M) (N O : Submodule R M) (N_le_O : N ≤ O) :
  Σo n : ℕ, Basis.SmithNormalForm (N.comap O.subtype) (Finₓ o) n :=
  by 
    choose n o hno bO bN a snf using N.exists_smith_normal_form_of_le b O N_le_O 
    refine' ⟨o, n, bO, bN.map (comap_subtype_equiv_of_le N_le_O).symm, (Finₓ.castLe hno).toEmbedding, a, fun i => _⟩
    ext 
    simp only [snf, Basis.map_apply, Submodule.comap_subtype_equiv_of_le_symm_apply_coe_coe,
      Submodule.coe_smul_of_tower, RelEmbedding.coe_fn_to_embedding]

/-- If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagonal matrix
in Smith normal form.

This is a strengthening of `submodule.basis_of_pid`.

See also `ideal.smith_normal_form`, which moreover proves that the dimension of
an ideal is the same as the dimension of the whole ring.
-/
noncomputable def Submodule.smithNormalForm [Fintype ι] (b : Basis ι R M) (N : Submodule R M) :
  Σn : ℕ, Basis.SmithNormalForm N ι n :=
  let ⟨m, n, bM, bN, f, a, snf⟩ := N.smith_normal_form_of_le b ⊤ le_top 
  let bM' := bM.map (LinearEquiv.ofTop _ rfl)
  let e := bM'.index_equiv b
  ⟨n, bM'.reindex e, bN.map (comap_subtype_equiv_of_le le_top), f.trans e.to_embedding, a,
    fun i =>
      by 
        simp only [snf, Basis.map_apply, LinearEquiv.of_top_apply, Submodule.coe_smul_of_tower,
          Submodule.comap_subtype_equiv_of_le_apply_coe, coe_coe, Basis.reindex_apply, Equiv.to_embedding_apply,
          Function.Embedding.trans_apply, Equiv.symm_apply_apply]⟩

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix.

See `ideal.exists_smith_normal_form` for a version of this theorem that doesn't
need to map `I` into a submodule of `R`.

This is a strengthening of `submodule.basis_of_pid`.
-/
noncomputable def Ideal.smithNormalForm [Fintype ι] {S : Type _} [CommRingₓ S] [IsDomain S] [Algebra R S]
  (b : Basis ι R S) (I : Ideal S) (hI : I ≠ ⊥) : Basis.SmithNormalForm (I.restrict_scalars R) ι (Fintype.card ι) :=
  let ⟨n, bS, bI, f, a, snf⟩ := (I.restrict_scalars R).SmithNormalForm b 
  have eq := Ideal.rank_eq bS hI (bI.map ((restrict_scalars_equiv R S S I).restrictScalars _))
  let e : Finₓ n ≃ Finₓ (Fintype.card ι) :=
    Fintype.equivOfCardEq
      (by 
        rw [Eq, Fintype.card_fin])
  ⟨bS, bI.reindex e, e.symm.to_embedding.trans f, a ∘ e.symm,
    fun i =>
      by 
        simp only [snf, Basis.coe_reindex, Function.Embedding.trans_apply, Equiv.to_embedding_apply]⟩

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix.

See also `ideal.smith_normal_form` for a version of this theorem that returns
a `basis.smith_normal_form`.
-/
theorem Ideal.exists_smith_normal_form [Fintype ι] {S : Type _} [CommRingₓ S] [IsDomain S] [Algebra R S]
  (b : Basis ι R S) (I : Ideal S) (hI : I ≠ ⊥) :
  ∃ (b' : Basis ι R S)(a : ι → R)(ab' : Basis ι R I), ∀ i, (ab' i : S) = a i • b' i :=
  let ⟨bS, bI, f, a, snf⟩ := I.smith_normal_form b hI 
  let e : Finₓ (Fintype.card ι) ≃ ι :=
    Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, Fintype.card_fin _⟩)
  have fe : ∀ i, f (e.symm i) = i := e.apply_symm_apply
  ⟨bS, a ∘ e.symm, (bI.reindex e).map ((restrict_scalars_equiv _ _ _ _).restrictScalars R),
    fun i =>
      by 
        simp only [snf, fe, Basis.map_apply, LinearEquiv.restrict_scalars_apply, Submodule.restrict_scalars_equiv_apply,
          Basis.coe_reindex]⟩

end SmithNormal

end PrincipalIdealDomain

/-- A set of linearly independent vectors in a module `M` over a semiring `S` is also linearly
independent over a subring `R` of `K`. -/
theorem LinearIndependent.restrict_scalars_algebras {R S M ι : Type _} [CommSemiringₓ R] [Semiringₓ S]
  [AddCommMonoidₓ M] [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]
  (hinj : Function.Injective (algebraMap R S)) {v : ι → M} (li : LinearIndependent S v) : LinearIndependent R v :=
  LinearIndependent.restrict_scalars
    (by 
      rwa [Algebra.algebra_map_eq_smul_one'] at hinj)
    li

