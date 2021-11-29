import Mathbin.Algebra.Lie.Submodule

/-!
# Ideal operations for Lie algebras

Given a Lie module `M` over a Lie algebra `L`, there is a natural action of the Lie ideals of `L`
on the Lie submodules of `M`. In the special case that `M = L` with the adjoint action, this
provides a pairing of Lie ideals which is especially important. For example, it can be used to
define solvability / nilpotency of a Lie algebra via the derived / lower-central series.

## Main definitions

  * `lie_submodule.has_bracket`
  * `lie_submodule.lie_ideal_oper_eq_linear_span`
  * `lie_ideal.map_bracket_le`
  * `lie_ideal.comap_bracket_le`

## Notation

Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M` and a Lie
ideal `I ⊆ L`, we introduce the notation `⁅I, N⁆` for the Lie submodule of `M` corresponding to
the action defined in this file.

## Tags

lie algebra, ideal operation
-/


universe u v w w₁ w₂

namespace LieSubmodule

variable{R : Type u}{L : Type v}{M : Type w}

variable[CommRingₓ R][LieRing L][LieAlgebra R L][AddCommGroupₓ M][Module R M]

variable[LieRingModule L M][LieModule R L M]

variable(N N' : LieSubmodule R L M)(I J : LieIdeal R L)

section LieIdealOperations

/-- Given a Lie module `M` over a Lie algebra `L`, the set of Lie ideals of `L` acts on the set
of submodules of `M`. -/
instance HasBracket : HasBracket (LieIdeal R L) (LieSubmodule R L M) :=
  ⟨fun I N => lie_span R L { m | ∃ (x : I)(n : N), ⁅(x : L),(n : M)⁆ = m }⟩

theorem lie_ideal_oper_eq_span : ⁅I,N⁆ = lie_span R L { m | ∃ (x : I)(n : N), ⁅(x : L),(n : M)⁆ = m } :=
  rfl

-- error in Algebra.Lie.IdealOperations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- See also `lie_submodule.lie_ideal_oper_eq_tensor_map_range`. -/
theorem lie_ideal_oper_eq_linear_span : «expr = »((«expr↑ »(«expr⁅ , ⁆»(I, N)) : submodule R M), submodule.span R {m | «expr∃ , »((x : I)
  (n : N), «expr = »(«expr⁅ , ⁆»((x : L), (n : M)), m))}) :=
begin
  apply [expr le_antisymm],
  { let [ident s] [] [":=", expr {m : M | «expr∃ , »((x : «expr↥ »(I))
      (n : «expr↥ »(N)), «expr = »(«expr⁅ , ⁆»((x : L), (n : M)), m))}],
    have [ident aux] [":", expr ∀
     (y : L)
     (m' «expr ∈ » submodule.span R s), «expr ∈ »(«expr⁅ , ⁆»(y, m'), submodule.span R s)] [],
    { intros [ident y, ident m', ident hm'],
      apply [expr submodule.span_induction hm'],
      { rintros [ident m'', "⟨", ident x, ",", ident n, ",", ident hm'', "⟩"],
        rw ["[", "<-", expr hm'', ",", expr leibniz_lie, "]"] [],
        refine [expr submodule.add_mem _ _ _]; apply [expr submodule.subset_span],
        { use ["[", expr ⟨«expr⁅ , ⁆»(y, «expr↑ »(x)), I.lie_mem x.property⟩, ",", expr n, "]"],
          refl },
        { use ["[", expr x, ",", expr ⟨«expr⁅ , ⁆»(y, «expr↑ »(n)), N.lie_mem n.property⟩, "]"],
          refl } },
      { simp [] [] ["only"] ["[", expr lie_zero, ",", expr submodule.zero_mem, "]"] [] [] },
      { intros [ident m₁, ident m₂, ident hm₁, ident hm₂],
        rw [expr lie_add] [],
        exact [expr submodule.add_mem _ hm₁ hm₂] },
      { intros [ident t, ident m'', ident hm''],
        rw [expr lie_smul] [],
        exact [expr submodule.smul_mem _ t hm''] } },
    change [expr «expr ≤ »(_, «expr↑ »(({ lie_mem := aux, ..submodule.span R s } : lie_submodule R L M)))] [] [],
    rw ["[", expr coe_submodule_le_coe_submodule, ",", expr lie_ideal_oper_eq_span, ",", expr lie_span_le, "]"] [],
    exact [expr submodule.subset_span] },
  { rw [expr lie_ideal_oper_eq_span] [],
    apply [expr submodule_span_le_lie_span] }
end

theorem lie_coe_mem_lie (x : I) (m : N) : ⁅(x : L),(m : M)⁆ ∈ ⁅I,N⁆ :=
  by 
    rw [lie_ideal_oper_eq_span]
    apply subset_lie_span 
    use x, m

theorem lie_mem_lie {x : L} {m : M} (hx : x ∈ I) (hm : m ∈ N) : ⁅x,m⁆ ∈ ⁅I,N⁆ :=
  N.lie_coe_mem_lie I ⟨x, hx⟩ ⟨m, hm⟩

theorem lie_comm : ⁅I,J⁆ = ⁅J,I⁆ :=
  by 
    suffices  : ∀ (I J : LieIdeal R L), ⁅I,J⁆ ≤ ⁅J,I⁆
    ·
      exact le_antisymmₓ (this I J) (this J I)
    clear I J 
    intro I J 
    rw [lie_ideal_oper_eq_span, lie_span_le]
    rintro x ⟨y, z, h⟩
    rw [←h]
    rw [←lie_skew, ←lie_neg, ←Submodule.coe_neg]
    apply lie_coe_mem_lie

theorem lie_le_right : ⁅I,N⁆ ≤ N :=
  by 
    rw [lie_ideal_oper_eq_span, lie_span_le]
    rintro m ⟨x, n, hn⟩
    rw [←hn]
    exact N.lie_mem n.property

theorem lie_le_left : ⁅I,J⁆ ≤ I :=
  by 
    rw [lie_comm]
    exact lie_le_right I J

theorem lie_le_inf : ⁅I,J⁆ ≤ I⊓J :=
  by 
    rw [le_inf_iff]
    exact ⟨lie_le_left I J, lie_le_right J I⟩

@[simp]
theorem lie_bot : ⁅I,(⊥ : LieSubmodule R L M)⁆ = ⊥ :=
  by 
    rw [eq_bot_iff]
    apply lie_le_right

@[simp]
theorem bot_lie : ⁅(⊥ : LieIdeal R L),N⁆ = ⊥ :=
  by 
    suffices  : ⁅(⊥ : LieIdeal R L),N⁆ ≤ ⊥
    ·
      exact le_bot_iff.mp this 
    rw [lie_ideal_oper_eq_span, lie_span_le]
    rintro m ⟨⟨x, hx⟩, n, hn⟩
    rw [←hn]
    change x ∈ (⊥ : LieIdeal R L) at hx 
    rw [mem_bot] at hx 
    simp [hx]

theorem mono_lie (h₁ : I ≤ J) (h₂ : N ≤ N') : ⁅I,N⁆ ≤ ⁅J,N'⁆ :=
  by 
    intro m h 
    rw [lie_ideal_oper_eq_span, mem_lie_span] at h 
    rw [lie_ideal_oper_eq_span, mem_lie_span]
    intro N hN 
    apply h 
    rintro m' ⟨⟨x, hx⟩, ⟨n, hn⟩, hm⟩
    rw [←hm]
    apply hN 
    use ⟨x, h₁ hx⟩, ⟨n, h₂ hn⟩
    rfl

theorem mono_lie_left (h : I ≤ J) : ⁅I,N⁆ ≤ ⁅J,N⁆ :=
  mono_lie _ _ _ _ h (le_reflₓ N)

theorem mono_lie_right (h : N ≤ N') : ⁅I,N⁆ ≤ ⁅I,N'⁆ :=
  mono_lie _ _ _ _ (le_reflₓ I) h

-- error in Algebra.Lie.IdealOperations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem lie_sup : «expr = »(«expr⁅ , ⁆»(I, «expr ⊔ »(N, N')), «expr ⊔ »(«expr⁅ , ⁆»(I, N), «expr⁅ , ⁆»(I, N'))) :=
begin
  have [ident h] [":", expr «expr ≤ »(«expr ⊔ »(«expr⁅ , ⁆»(I, N), «expr⁅ , ⁆»(I, N')), «expr⁅ , ⁆»(I, «expr ⊔ »(N, N')))] [],
  { rw [expr sup_le_iff] [],
    split; apply [expr mono_lie_right]; [exact [expr le_sup_left], exact [expr le_sup_right]] },
  suffices [] [":", expr «expr ≤ »(«expr⁅ , ⁆»(I, «expr ⊔ »(N, N')), «expr ⊔ »(«expr⁅ , ⁆»(I, N), «expr⁅ , ⁆»(I, N')))],
  { exact [expr le_antisymm this h] },
  clear [ident h],
  rw ["[", expr lie_ideal_oper_eq_span, ",", expr lie_span_le, "]"] [],
  rintros [ident m, "⟨", ident x, ",", "⟨", ident n, ",", ident hn, "⟩", ",", ident h, "⟩"],
  erw [expr lie_submodule.mem_sup] [],
  erw [expr lie_submodule.mem_sup] ["at", ident hn],
  rcases [expr hn, "with", "⟨", ident n₁, ",", ident hn₁, ",", ident n₂, ",", ident hn₂, ",", ident hn', "⟩"],
  use [expr «expr⁅ , ⁆»((x : L), (⟨n₁, hn₁⟩ : N))],
  split,
  { apply [expr lie_coe_mem_lie] },
  use [expr «expr⁅ , ⁆»((x : L), (⟨n₂, hn₂⟩ : N'))],
  split,
  { apply [expr lie_coe_mem_lie] },
  simp [] [] [] ["[", "<-", expr h, ",", "<-", expr hn', "]"] [] []
end

-- error in Algebra.Lie.IdealOperations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem sup_lie : «expr = »(«expr⁅ , ⁆»(«expr ⊔ »(I, J), N), «expr ⊔ »(«expr⁅ , ⁆»(I, N), «expr⁅ , ⁆»(J, N))) :=
begin
  have [ident h] [":", expr «expr ≤ »(«expr ⊔ »(«expr⁅ , ⁆»(I, N), «expr⁅ , ⁆»(J, N)), «expr⁅ , ⁆»(«expr ⊔ »(I, J), N))] [],
  { rw [expr sup_le_iff] [],
    split; apply [expr mono_lie_left]; [exact [expr le_sup_left], exact [expr le_sup_right]] },
  suffices [] [":", expr «expr ≤ »(«expr⁅ , ⁆»(«expr ⊔ »(I, J), N), «expr ⊔ »(«expr⁅ , ⁆»(I, N), «expr⁅ , ⁆»(J, N)))],
  { exact [expr le_antisymm this h] },
  clear [ident h],
  rw ["[", expr lie_ideal_oper_eq_span, ",", expr lie_span_le, "]"] [],
  rintros [ident m, "⟨", "⟨", ident x, ",", ident hx, "⟩", ",", ident n, ",", ident h, "⟩"],
  erw [expr lie_submodule.mem_sup] [],
  erw [expr lie_submodule.mem_sup] ["at", ident hx],
  rcases [expr hx, "with", "⟨", ident x₁, ",", ident hx₁, ",", ident x₂, ",", ident hx₂, ",", ident hx', "⟩"],
  use [expr «expr⁅ , ⁆»(((⟨x₁, hx₁⟩ : I) : L), (n : N))],
  split,
  { apply [expr lie_coe_mem_lie] },
  use [expr «expr⁅ , ⁆»(((⟨x₂, hx₂⟩ : J) : L), (n : N))],
  split,
  { apply [expr lie_coe_mem_lie] },
  simp [] [] [] ["[", "<-", expr h, ",", "<-", expr hx', "]"] [] []
end

@[simp]
theorem lie_inf : ⁅I,N⊓N'⁆ ≤ ⁅I,N⁆⊓⁅I,N'⁆ :=
  by 
    rw [le_inf_iff]
    split  <;> apply mono_lie_right <;> [exact inf_le_left, exact inf_le_right]

@[simp]
theorem inf_lie : ⁅I⊓J,N⁆ ≤ ⁅I,N⁆⊓⁅J,N⁆ :=
  by 
    rw [le_inf_iff]
    split  <;> apply mono_lie_left <;> [exact inf_le_left, exact inf_le_right]

end LieIdealOperations

end LieSubmodule

namespace LieIdeal

open LieAlgebra

variable{R : Type u}{L : Type v}{L' : Type w₂}

variable[CommRingₓ R][LieRing L][LieAlgebra R L][LieRing L'][LieAlgebra R L']

variable(f : L →ₗ⁅R⁆ L')(I : LieIdeal R L)(J : LieIdeal R L')

/-- Note that the inequality can be strict; e.g., the inclusion of an Abelian subalgebra of a
simple algebra. -/
theorem map_bracket_le {I₁ I₂ : LieIdeal R L} : map f ⁅I₁,I₂⁆ ≤ ⁅map f I₁,map f I₂⁆ :=
  by 
    rw [map_le_iff_le_comap]
    erw [LieSubmodule.lie_span_le]
    intro x hx 
    obtain ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩, hx⟩ := hx 
    rw [←hx]
    let fy₁ : «expr↥ » (map f I₁) := ⟨f y₁, mem_map hy₁⟩
    let fy₂ : «expr↥ » (map f I₂) := ⟨f y₂, mem_map hy₂⟩
    change _ ∈ comap f ⁅map f I₁,map f I₂⁆
    simp only [Submodule.coe_mk, mem_comap, LieHom.map_lie]
    exact LieSubmodule.lie_coe_mem_lie _ _ fy₁ fy₂

theorem map_bracket_eq {I₁ I₂ : LieIdeal R L} (h : Function.Surjective f) : map f ⁅I₁,I₂⁆ = ⁅map f I₁,map f I₂⁆ :=
  by 
    suffices  : ⁅map f I₁,map f I₂⁆ ≤ map f ⁅I₁,I₂⁆
    ·
      exact le_antisymmₓ (map_bracket_le f) this 
    rw [←LieSubmodule.coe_submodule_le_coe_submodule, coe_map_of_surjective h,
      LieSubmodule.lie_ideal_oper_eq_linear_span, LieSubmodule.lie_ideal_oper_eq_linear_span, LinearMap.map_span]
    apply Submodule.span_mono 
    rintro x ⟨⟨z₁, h₁⟩, ⟨z₂, h₂⟩, rfl⟩
    obtain ⟨y₁, rfl⟩ := mem_map_of_surjective h h₁ 
    obtain ⟨y₂, rfl⟩ := mem_map_of_surjective h h₂ 
    use ⁅(y₁ : L),(y₂ : L)⁆, y₁, y₂ 
    apply f.map_lie

theorem comap_bracket_le {J₁ J₂ : LieIdeal R L'} : ⁅comap f J₁,comap f J₂⁆ ≤ comap f ⁅J₁,J₂⁆ :=
  by 
    rw [←map_le_iff_le_comap]
    exact le_transₓ (map_bracket_le f) (LieSubmodule.mono_lie _ _ _ _ map_comap_le map_comap_le)

variable{f}

theorem map_comap_incl {I₁ I₂ : LieIdeal R L} : map I₁.incl (comap I₁.incl I₂) = I₁⊓I₂ :=
  by 
    convRHS => rw [←I₁.incl_ideal_range]
    rw [←map_comap_eq]
    exact I₁.incl_is_ideal_morphism

-- error in Algebra.Lie.IdealOperations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem comap_bracket_eq
{J₁ J₂ : lie_ideal R L'}
(h : f.is_ideal_morphism) : «expr = »(comap f «expr⁅ , ⁆»(«expr ⊓ »(f.ideal_range, J₁), «expr ⊓ »(f.ideal_range, J₂)), «expr ⊔ »(«expr⁅ , ⁆»(comap f J₁, comap f J₂), f.ker)) :=
begin
  rw ["[", "<-", expr lie_submodule.coe_to_submodule_eq_iff, ",", expr comap_coe_submodule, ",", expr lie_submodule.sup_coe_to_submodule, ",", expr f.ker_coe_submodule, ",", "<-", expr submodule.comap_map_eq, ",", expr lie_submodule.lie_ideal_oper_eq_linear_span, ",", expr lie_submodule.lie_ideal_oper_eq_linear_span, ",", expr linear_map.map_span, "]"] [],
  congr,
  simp [] [] ["only"] ["[", expr lie_hom.coe_to_linear_map, ",", expr set.mem_set_of_eq, "]"] [] [],
  ext [] [ident y] [],
  split,
  { rintros ["⟨", "⟨", ident x₁, ",", ident hx₁, "⟩", ",", "⟨", ident x₂, ",", ident hx₂, "⟩", ",", ident hy, "⟩"],
    rw ["<-", expr hy] [],
    erw ["[", expr lie_submodule.mem_inf, ",", expr f.mem_ideal_range_iff h, "]"] ["at", ident hx₁, ident hx₂],
    obtain ["⟨", "⟨", ident z₁, ",", ident hz₁, "⟩", ",", ident hz₁', "⟩", ":=", expr hx₁],
    rw ["<-", expr hz₁] ["at", ident hz₁'],
    obtain ["⟨", "⟨", ident z₂, ",", ident hz₂, "⟩", ",", ident hz₂', "⟩", ":=", expr hx₂],
    rw ["<-", expr hz₂] ["at", ident hz₂'],
    use ["[", expr «expr⁅ , ⁆»(z₁, z₂), ",", expr ⟨z₁, hz₁'⟩, ",", expr ⟨z₂, hz₂'⟩, ",", expr rfl, "]"],
    simp [] [] ["only"] ["[", expr hz₁, ",", expr hz₂, ",", expr submodule.coe_mk, ",", expr lie_hom.map_lie, "]"] [] [] },
  { rintros ["⟨", ident x, ",", "⟨", "⟨", ident z₁, ",", ident hz₁, "⟩", ",", "⟨", ident z₂, ",", ident hz₂, "⟩", ",", ident hx, "⟩", ",", ident hy, "⟩"],
    rw ["[", "<-", expr hy, ",", "<-", expr hx, "]"] [],
    have [ident hz₁'] [":", expr «expr ∈ »(f z₁, «expr ⊓ »(f.ideal_range, J₁))] [],
    { rw [expr lie_submodule.mem_inf] [],
      exact [expr ⟨f.mem_ideal_range, hz₁⟩] },
    have [ident hz₂'] [":", expr «expr ∈ »(f z₂, «expr ⊓ »(f.ideal_range, J₂))] [],
    { rw [expr lie_submodule.mem_inf] [],
      exact [expr ⟨f.mem_ideal_range, hz₂⟩] },
    use ["[", expr ⟨f z₁, hz₁'⟩, ",", expr ⟨f z₂, hz₂'⟩, "]"],
    simp [] [] ["only"] ["[", expr submodule.coe_mk, ",", expr lie_hom.map_lie, "]"] [] [] }
end

theorem map_comap_bracket_eq {J₁ J₂ : LieIdeal R L'} (h : f.is_ideal_morphism) :
  map f ⁅comap f J₁,comap f J₂⁆ = ⁅f.ideal_range⊓J₁,f.ideal_range⊓J₂⁆ :=
  by 
    rw [←map_sup_ker_eq_map, ←comap_bracket_eq h, map_comap_eq h, inf_eq_right]
    exact le_transₓ (LieSubmodule.lie_le_left _ _) inf_le_left

theorem comap_bracket_incl {I₁ I₂ : LieIdeal R L} : ⁅comap I.incl I₁,comap I.incl I₂⁆ = comap I.incl ⁅I⊓I₁,I⊓I₂⁆ :=
  by 
    convRHS => congr skip rw [←I.incl_ideal_range]
    rw [comap_bracket_eq]
    simp only [ker_incl, sup_bot_eq]
    exact I.incl_is_ideal_morphism

/-- This is a very useful result; it allows us to use the fact that inclusion distributes over the
Lie bracket operation on ideals, subject to the conditions shown. -/
theorem comap_bracket_incl_of_le {I₁ I₂ : LieIdeal R L} (h₁ : I₁ ≤ I) (h₂ : I₂ ≤ I) :
  ⁅comap I.incl I₁,comap I.incl I₂⁆ = comap I.incl ⁅I₁,I₂⁆ :=
  by 
    rw [comap_bracket_incl]
    rw [←inf_eq_right] at h₁ h₂ 
    rw [h₁, h₂]

end LieIdeal

