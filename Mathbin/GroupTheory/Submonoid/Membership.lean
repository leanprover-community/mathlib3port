import Mathbin.GroupTheory.Submonoid.Operations 
import Mathbin.Algebra.BigOperators.Basic 
import Mathbin.Algebra.FreeMonoid

/-!
# Submonoids: membership criteria

In this file we prove various facts about membership in a submonoid:

* `list_prod_mem`, `multiset_prod_mem`, `prod_mem`: if each element of a collection belongs
  to a multiplicative submonoid, then so does their product;
* `list_sum_mem`, `multiset_sum_mem`, `sum_mem`: if each element of a collection belongs
  to an additive submonoid, then so does their sum;
* `pow_mem`, `nsmul_mem`: if `x ∈ S` where `S` is a multiplicative (resp., additive) submonoid and
  `n` is a natural number, then `x^n` (resp., `n • x`) belongs to `S`;
* `mem_supr_of_directed`, `coe_supr_of_directed`, `mem_Sup_of_directed_on`,
  `coe_Sup_of_directed_on`: the supremum of a directed collection of submonoid is their union.
* `sup_eq_range`, `mem_sup`: supremum of two submonoids `S`, `T` of a commutative monoid is the set
  of products;
* `closure_singleton_eq`, `mem_closure_singleton`: the multiplicative (resp., additive) closure
  of `{x}` consists of powers (resp., natural multiples) of `x`.

## Tags
submonoid, submonoids
-/


open_locale BigOperators

variable{M : Type _}

variable{A : Type _}

namespace Submonoid

section Assoc

variable[Monoidₓ M](S : Submonoid M)

@[simp, normCast, toAdditive coe_nsmul]
theorem coe_pow (x : S) (n : ℕ) : «expr↑ » (x ^ n) = (x ^ n : M) :=
  S.subtype.map_pow x n

@[simp, normCast, toAdditive]
theorem coe_list_prod (l : List S) : (l.prod : M) = (l.map coeₓ).Prod :=
  S.subtype.map_list_prod l

@[simp, normCast, toAdditive]
theorem coe_multiset_prod {M} [CommMonoidₓ M] (S : Submonoid M) (m : Multiset S) : (m.prod : M) = (m.map coeₓ).Prod :=
  S.subtype.map_multiset_prod m

@[simp, normCast, toAdditive]
theorem coe_finset_prod {ι M} [CommMonoidₓ M] (S : Submonoid M) (f : ι → S) (s : Finset ι) :
  «expr↑ » (∏i in s, f i) = (∏i in s, f i : M) :=
  S.subtype.map_prod f s

/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[toAdditive "Sum of a list of elements in an `add_submonoid` is in the `add_submonoid`."]
theorem list_prod_mem {l : List M} (hl : ∀ x _ : x ∈ l, x ∈ S) : l.prod ∈ S :=
  by 
    lift l to List S using hl 
    rw [←coe_list_prod]
    exact l.prod.coe_prop

/-- Product of a multiset of elements in a submonoid of a `comm_monoid` is in the submonoid. -/
@[toAdditive "Sum of a multiset of elements in an `add_submonoid` of an `add_comm_monoid` is\nin the `add_submonoid`."]
theorem multiset_prod_mem {M} [CommMonoidₓ M] (S : Submonoid M) (m : Multiset M) (hm : ∀ a _ : a ∈ m, a ∈ S) :
  m.prod ∈ S :=
  by 
    lift m to Multiset S using hm 
    rw [←coe_multiset_prod]
    exact m.prod.coe_prop

/-- Product of elements of a submonoid of a `comm_monoid` indexed by a `finset` is in the
    submonoid. -/
@[toAdditive
      "Sum of elements in an `add_submonoid` of an `add_comm_monoid` indexed by a `finset`\nis in the `add_submonoid`."]
theorem prod_mem {M : Type _} [CommMonoidₓ M] (S : Submonoid M) {ι : Type _} {t : Finset ι} {f : ι → M}
  (h : ∀ c _ : c ∈ t, f c ∈ S) : (∏c in t, f c) ∈ S :=
  S.multiset_prod_mem (t.1.map f)$
    fun x hx =>
      let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx 
      hix ▸ h i hi

@[toAdditive nsmul_mem]
theorem pow_mem {x : M} (hx : x ∈ S) (n : ℕ) : x ^ n ∈ S :=
  by 
    simpa only [coe_pow] using ((⟨x, hx⟩ : S) ^ n).coe_prop

end Assoc

section NonAssoc

variable[MulOneClass M](S : Submonoid M)

open Set

@[toAdditive]
theorem mem_supr_of_directed {ι} [hι : Nonempty ι] {S : ι → Submonoid M} (hS : Directed (· ≤ ·) S) {x : M} :
  (x ∈ ⨆i, S i) ↔ ∃ i, x ∈ S i :=
  by 
    refine' ⟨_, fun ⟨i, hi⟩ => (SetLike.le_def.1$ le_supr S i) hi⟩
    suffices  : x ∈ closure (⋃i, (S i : Set M)) → ∃ i, x ∈ S i
    ·
      simpa only [closure_Union, closure_eq (S _)] using this 
    refine' fun hx => closure_induction hx (fun _ => mem_Union.1) _ _
    ·
      exact hι.elim fun i => ⟨i, (S i).one_mem⟩
    ·
      rintro x y ⟨i, hi⟩ ⟨j, hj⟩
      rcases hS i j with ⟨k, hki, hkj⟩
      exact ⟨k, (S k).mul_mem (hki hi) (hkj hj)⟩

@[toAdditive]
theorem coe_supr_of_directed {ι} [Nonempty ι] {S : ι → Submonoid M} (hS : Directed (· ≤ ·) S) :
  ((⨆i, S i : Submonoid M) : Set M) = ⋃i, «expr↑ » (S i) :=
  Set.ext$
    fun x =>
      by 
        simp [mem_supr_of_directed hS]

-- error in GroupTheory.Submonoid.Membership: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem mem_Sup_of_directed_on
{S : set (submonoid M)}
(Sne : S.nonempty)
(hS : directed_on ((«expr ≤ »)) S)
{x : M} : «expr ↔ »(«expr ∈ »(x, Sup S), «expr∃ , »((s «expr ∈ » S), «expr ∈ »(x, s))) :=
begin
  haveI [] [":", expr nonempty S] [":=", expr Sne.to_subtype],
  simp [] [] ["only"] ["[", expr Sup_eq_supr', ",", expr mem_supr_of_directed hS.directed_coe, ",", expr set_coe.exists, ",", expr subtype.coe_mk, "]"] [] []
end

@[toAdditive]
theorem coe_Sup_of_directed_on {S : Set (Submonoid M)} (Sne : S.nonempty) (hS : DirectedOn (· ≤ ·) S) :
  («expr↑ » (Sup S) : Set M) = ⋃(s : _)(_ : s ∈ S), «expr↑ » s :=
  Set.ext$
    fun x =>
      by 
        simp [mem_Sup_of_directed_on Sne hS]

@[toAdditive]
theorem mem_sup_left {S T : Submonoid M} : ∀ {x : M}, x ∈ S → x ∈ S⊔T :=
  show S ≤ S⊔T from le_sup_left

@[toAdditive]
theorem mem_sup_right {S T : Submonoid M} : ∀ {x : M}, x ∈ T → x ∈ S⊔T :=
  show T ≤ S⊔T from le_sup_right

@[toAdditive]
theorem mul_mem_sup {S T : Submonoid M} {x y : M} (hx : x ∈ S) (hy : y ∈ T) : (x*y) ∈ S⊔T :=
  (S⊔T).mul_mem (mem_sup_left hx) (mem_sup_right hy)

@[toAdditive]
theorem mem_supr_of_mem {ι : Type _} {S : ι → Submonoid M} (i : ι) : ∀ {x : M}, x ∈ S i → x ∈ supr S :=
  show S i ≤ supr S from le_supr _ _

@[toAdditive]
theorem mem_Sup_of_mem {S : Set (Submonoid M)} {s : Submonoid M} (hs : s ∈ S) : ∀ {x : M}, x ∈ s → x ∈ Sup S :=
  show s ≤ Sup S from le_Sup hs

end NonAssoc

end Submonoid

namespace FreeMonoid

variable{α : Type _}

open Submonoid

@[toAdditive]
theorem closure_range_of : closure (Set.Range$ @of α) = ⊤ :=
  eq_top_iff.2$
    fun x hx => FreeMonoid.recOn x (one_mem _)$ fun x xs hxs => mul_mem _ (subset_closure$ Set.mem_range_self _) hxs

end FreeMonoid

namespace Submonoid

variable[Monoidₓ M]

open MonoidHom

theorem closure_singleton_eq (x : M) : closure ({x} : Set M) = (powersHom M x).mrange :=
  closure_eq_of_le (Set.singleton_subset_iff.2 ⟨Multiplicative.ofAdd 1, pow_oneₓ x⟩)$
    fun x ⟨n, hn⟩ => hn ▸ pow_mem _ (subset_closure$ Set.mem_singleton _) _

/-- The submonoid generated by an element of a monoid equals the set of natural number powers of
    the element. -/
theorem mem_closure_singleton {x y : M} : y ∈ closure ({x} : Set M) ↔ ∃ n : ℕ, x ^ n = y :=
  by 
    rw [closure_singleton_eq, mem_mrange] <;> rfl

theorem mem_closure_singleton_self {y : M} : y ∈ closure ({y} : Set M) :=
  mem_closure_singleton.2 ⟨1, pow_oneₓ y⟩

theorem closure_singleton_one : closure ({1} : Set M) = ⊥ :=
  by 
    simp [eq_bot_iff_forall, mem_closure_singleton]

@[toAdditive]
theorem closure_eq_mrange (s : Set M) : closure s = (FreeMonoid.lift (coeₓ : s → M)).mrange :=
  by 
    rw [mrange_eq_map, ←FreeMonoid.closure_range_of, map_mclosure, ←Set.range_comp, FreeMonoid.lift_comp_of,
      Subtype.range_coe]

@[toAdditive]
theorem exists_list_of_mem_closure {s : Set M} {x : M} (hx : x ∈ closure s) :
  ∃ (l : List M)(hl : ∀ y _ : y ∈ l, y ∈ s), l.prod = x :=
  by 
    rw [closure_eq_mrange, mem_mrange] at hx 
    rcases hx with ⟨l, hx⟩
    exact
      ⟨List.map coeₓ l,
        fun y hy =>
          let ⟨z, hz, hy⟩ := List.mem_mapₓ.1 hy 
          hy ▸ z.2,
        hx⟩

@[toAdditive]
theorem exists_multiset_of_mem_closure {M : Type _} [CommMonoidₓ M] {s : Set M} {x : M} (hx : x ∈ closure s) :
  ∃ (l : Multiset M)(hl : ∀ y _ : y ∈ l, y ∈ s), l.prod = x :=
  by 
    obtain ⟨l, h1, h2⟩ := exists_list_of_mem_closure hx 
    exact ⟨l, h1, (Multiset.coe_prod l).trans h2⟩

/-- The submonoid generated by an element. -/
def powers (n : M) : Submonoid M :=
  Submonoid.copy (powersHom M n).mrange (Set.Range ((· ^ ·) n : ℕ → M))$
    Set.ext
      fun n =>
        exists_congr$
          fun i =>
            by 
              simp  <;> rfl

@[simp]
theorem mem_powers (n : M) : n ∈ powers n :=
  ⟨1, pow_oneₓ _⟩

theorem mem_powers_iff (x z : M) : x ∈ powers z ↔ ∃ n : ℕ, z ^ n = x :=
  Iff.rfl

theorem powers_eq_closure (n : M) : powers n = closure {n} :=
  by 
    ext 
    exact mem_closure_singleton.symm

theorem powers_subset {n : M} {P : Submonoid M} (h : n ∈ P) : powers n ≤ P :=
  fun x hx =>
    match x, hx with 
    | _, ⟨i, rfl⟩ => P.pow_mem h i

/-- Exponentiation map from natural numbers to powers. -/
def pow (n : M) (m : ℕ) : powers n :=
  ⟨n ^ m, m, rfl⟩

/-- Logarithms from powers to natural numbers. -/
def log [DecidableEq M] {n : M} (p : powers n) : ℕ :=
  Nat.findₓ$ (mem_powers_iff p.val n).mp p.prop

@[simp]
theorem pow_log_eq_self [DecidableEq M] {n : M} (p : powers n) : pow n (log p) = p :=
  Subtype.ext$ Nat.find_specₓ p.prop

theorem pow_right_injective_iff_pow_injective {n : M} :
  (Function.Injective fun m : ℕ => n ^ m) ↔ Function.Injective (pow n) :=
  Subtype.coe_injective.of_comp_iff (pow n)

theorem log_pow_eq_self [DecidableEq M] {n : M} (h : Function.Injective fun m : ℕ => n ^ m) (m : ℕ) :
  log (pow n m) = m :=
  pow_right_injective_iff_pow_injective.mp h$ pow_log_eq_self _

theorem log_pow_int_eq_self {x : ℤ} (h : 1 < x.nat_abs) (m : ℕ) : log (pow x m) = m :=
  log_pow_eq_self (Int.pow_right_injective h) _

end Submonoid

namespace Submonoid

variable{N : Type _}[CommMonoidₓ N]

open MonoidHom

@[toAdditive]
theorem sup_eq_range (s t : Submonoid N) : s⊔t = (s.subtype.coprod t.subtype).mrange :=
  by 
    rw [mrange_eq_map, ←mrange_inl_sup_mrange_inr, map_sup, map_mrange, coprod_comp_inl, map_mrange, coprod_comp_inr,
      range_subtype, range_subtype]

@[toAdditive]
theorem mem_sup {s t : Submonoid N} {x : N} : x ∈ s⊔t ↔ ∃ (y : _)(_ : y ∈ s)(z : _)(_ : z ∈ t), (y*z) = x :=
  by 
    simp only [sup_eq_range, mem_mrange, coprod_apply, Prod.exists, SetLike.exists, coeSubtype, Subtype.coe_mk]

end Submonoid

namespace AddSubmonoid

variable[AddMonoidₓ A]

open Set

theorem closure_singleton_eq (x : A) : closure ({x} : Set A) = (multiplesHom A x).mrange :=
  closure_eq_of_le (Set.singleton_subset_iff.2 ⟨1, one_nsmul x⟩)$
    fun x ⟨n, hn⟩ => hn ▸ nsmul_mem _ (subset_closure$ Set.mem_singleton _) _

/-- The `add_submonoid` generated by an element of an `add_monoid` equals the set of
natural number multiples of the element. -/
theorem mem_closure_singleton {x y : A} : y ∈ closure ({x} : Set A) ↔ ∃ n : ℕ, n • x = y :=
  by 
    rw [closure_singleton_eq, AddMonoidHom.mem_mrange] <;> rfl

theorem closure_singleton_zero : closure ({0} : Set A) = ⊥ :=
  by 
    simp [eq_bot_iff_forall, mem_closure_singleton, nsmul_zero]

/-- The additive submonoid generated by an element. -/
def multiples (x : A) : AddSubmonoid A :=
  AddSubmonoid.copy (multiplesHom A x).mrange (Set.Range (fun i => i • x : ℕ → A))$
    Set.ext
      fun n =>
        exists_congr$
          fun i =>
            by 
              simp  <;> rfl

@[simp]
theorem mem_multiples (x : A) : x ∈ multiples x :=
  ⟨1, one_nsmul _⟩

theorem mem_multiples_iff (x z : A) : x ∈ multiples z ↔ ∃ n : ℕ, n • z = x :=
  Iff.rfl

theorem multiples_eq_closure (x : A) : multiples x = closure {x} :=
  by 
    ext 
    exact mem_closure_singleton.symm

theorem multiples_subset {x : A} {P : AddSubmonoid A} (h : x ∈ P) : multiples x ≤ P :=
  fun x hx =>
    match x, hx with 
    | _, ⟨i, rfl⟩ => P.nsmul_mem h i

attribute [toAdditive AddSubmonoid.multiples] Submonoid.powers

attribute [toAdditive AddSubmonoid.mem_multiples] Submonoid.mem_powers

attribute [toAdditive AddSubmonoid.mem_multiples_iff] Submonoid.mem_powers_iff

attribute [toAdditive AddSubmonoid.multiples_eq_closure] Submonoid.powers_eq_closure

attribute [toAdditive AddSubmonoid.multiples_subset] Submonoid.powers_subset

end AddSubmonoid

/-! Lemmas about additive closures of `submonoid`. -/


namespace Submonoid

variable{R : Type _}[NonAssocSemiring R](S : Submonoid R){a b : R}

/-- The product of an element of the additive closure of a multiplicative submonoid `M`
and an element of `M` is contained in the additive closure of `M`. -/
theorem mul_right_mem_add_closure (ha : a ∈ AddSubmonoid.closure (S : Set R)) (hb : b ∈ S) :
  (a*b) ∈ AddSubmonoid.closure (S : Set R) :=
  by 
    revert b 
    refine' AddSubmonoid.closure_induction ha _ _ _ <;> clear ha a
    ·
      exact fun r hr b hb => add_submonoid.mem_closure.mpr fun y hy => hy (S.mul_mem hr hb)
    ·
      exact
        fun b hb =>
          by 
            simp only [zero_mul, (AddSubmonoid.closure (S : Set R)).zero_mem]
    ·
      simpRw [add_mulₓ]
      exact fun r s hr hs b hb => (AddSubmonoid.closure (S : Set R)).add_mem (hr hb) (hs hb)

/-- The product of two elements of the additive closure of a submonoid `M` is an element of the
additive closure of `M`. -/
theorem mul_mem_add_closure (ha : a ∈ AddSubmonoid.closure (S : Set R)) (hb : b ∈ AddSubmonoid.closure (S : Set R)) :
  (a*b) ∈ AddSubmonoid.closure (S : Set R) :=
  by 
    revert a 
    refine' AddSubmonoid.closure_induction hb _ _ _ <;> clear hb b
    ·
      exact fun r hr b hb => S.mul_right_mem_add_closure hb hr
    ·
      exact
        fun b hb =>
          by 
            simp only [mul_zero, (AddSubmonoid.closure (S : Set R)).zero_mem]
    ·
      simpRw [mul_addₓ]
      exact fun r s hr hs b hb => (AddSubmonoid.closure (S : Set R)).add_mem (hr hb) (hs hb)

/-- The product of an element of `S` and an element of the additive closure of a multiplicative
submonoid `S` is contained in the additive closure of `S`. -/
theorem mul_left_mem_add_closure (ha : a ∈ S) (hb : b ∈ AddSubmonoid.closure (S : Set R)) :
  (a*b) ∈ AddSubmonoid.closure (S : Set R) :=
  S.mul_mem_add_closure (AddSubmonoid.mem_closure.mpr fun sT hT => hT ha) hb

end Submonoid

section mul_addₓ

theorem of_mul_image_powers_eq_multiples_of_mul [Monoidₓ M] {x : M} :
  Additive.ofMul '' (Submonoid.powers x : Set M) = AddSubmonoid.multiples (Additive.ofMul x) :=
  by 
    ext 
    split 
    ·
      rintro ⟨y, ⟨n, hy1⟩, hy2⟩
      use n 
      simpa [←of_mul_pow, hy1]
    ·
      rintro ⟨n, hn⟩
      refine' ⟨x ^ n, ⟨n, rfl⟩, _⟩
      rwa [of_mul_pow]

theorem of_add_image_multiples_eq_powers_of_add [AddMonoidₓ A] {x : A} :
  Multiplicative.ofAdd '' (AddSubmonoid.multiples x : Set A) = Submonoid.powers (Multiplicative.ofAdd x) :=
  by 
    symm 
    rw [Equiv.eq_image_iff_symm_image_eq]
    exact of_mul_image_powers_eq_multiples_of_mul

end mul_addₓ

