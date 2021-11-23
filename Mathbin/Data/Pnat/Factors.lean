import Mathbin.Data.Pnat.Prime 
import Mathbin.Data.Multiset.Sort

/-!
# Prime factors of nonzero naturals

This file defines the factorization of a nonzero natural number `n` as a multiset of primes,
the multiplicity of `p` in this factors multiset being the p-adic valuation of `n`.

## Main declarations

* `prime_multiset`: Type of multisets of prime numbers.
* `factor_multiset n`: Multiset of prime factors of `n`.
-/


-- error in Data.Pnat.Factors: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler inhabited
/-- The type of multisets of prime numbers.  Unique factorization
 gives an equivalence between this set and ℕ+, as we will formalize
 below. -/
@[derive #["[", expr inhabited, ",", expr has_repr, ",", expr canonically_ordered_add_monoid, ",", expr distrib_lattice,
   ",", expr semilattice_sup_bot, ",", expr has_sub, ",", expr has_ordered_sub, "]"]]
def prime_multiset :=
multiset nat.primes

namespace PrimeMultiset

/-- The multiset consisting of a single prime -/
def of_prime (p : Nat.Primes) : PrimeMultiset :=
  ({p} : Multiset Nat.Primes)

theorem card_of_prime (p : Nat.Primes) : Multiset.card (of_prime p) = 1 :=
  rfl

/-- We can forget the primality property and regard a multiset
 of primes as just a multiset of positive integers, or a multiset
 of natural numbers.  In the opposite direction, if we have a
 multiset of positive integers or natural numbers, together with
 a proof that all the elements are prime, then we can regard it
 as a multiset of primes.  The next block of results records
 obvious properties of these coercions.
-/
def to_nat_multiset : PrimeMultiset → Multiset ℕ :=
  fun v => v.map fun p => (p : ℕ)

instance coe_nat : Coe PrimeMultiset (Multiset ℕ) :=
  ⟨to_nat_multiset⟩

/-- `prime_multiset.coe`, the coercion from a multiset of primes to a multiset of
naturals, promoted to an `add_monoid_hom`. -/
def coe_nat_monoid_hom : PrimeMultiset →+ Multiset ℕ :=
  { Multiset.mapAddMonoidHom coeₓ with toFun := coeₓ }

@[simp]
theorem coe_coe_nat_monoid_hom : (coe_nat_monoid_hom : PrimeMultiset → Multiset ℕ) = coeₓ :=
  rfl

theorem coe_nat_injective : Function.Injective (coeₓ : PrimeMultiset → Multiset ℕ) :=
  Multiset.map_injective Nat.Primes.coe_nat_inj

theorem coe_nat_of_prime (p : Nat.Primes) : (of_prime p : Multiset ℕ) = {p} :=
  rfl

theorem coe_nat_prime (v : PrimeMultiset) (p : ℕ) (h : p ∈ (v : Multiset ℕ)) : p.prime :=
  by 
    rcases multiset.mem_map.mp h with ⟨⟨p', hp'⟩, ⟨h_mem, h_eq⟩⟩
    exact h_eq ▸ hp'

/-- Converts a `prime_multiset` to a `multiset ℕ+`. -/
def to_pnat_multiset : PrimeMultiset → Multiset ℕ+ :=
  fun v => v.map fun p => (p : ℕ+)

instance coe_pnat : Coe PrimeMultiset (Multiset ℕ+) :=
  ⟨to_pnat_multiset⟩

/-- `coe_pnat`, the coercion from a multiset of primes to a multiset of positive
naturals, regarded as an `add_monoid_hom`. -/
def coe_pnat_monoid_hom : PrimeMultiset →+ Multiset ℕ+ :=
  { Multiset.mapAddMonoidHom coeₓ with toFun := coeₓ }

@[simp]
theorem coe_coe_pnat_monoid_hom : (coe_pnat_monoid_hom : PrimeMultiset → Multiset ℕ+) = coeₓ :=
  rfl

theorem coe_pnat_injective : Function.Injective (coeₓ : PrimeMultiset → Multiset ℕ+) :=
  Multiset.map_injective Nat.Primes.coe_pnat_inj

theorem coe_pnat_of_prime (p : Nat.Primes) : (of_prime p : Multiset ℕ+) = {(p : ℕ+)} :=
  rfl

theorem coe_pnat_prime (v : PrimeMultiset) (p : ℕ+) (h : p ∈ (v : Multiset ℕ+)) : p.prime :=
  by 
    rcases multiset.mem_map.mp h with ⟨⟨p', hp'⟩, ⟨h_mem, h_eq⟩⟩
    exact h_eq ▸ hp'

instance coe_multiset_pnat_nat : Coe (Multiset ℕ+) (Multiset ℕ) :=
  ⟨fun v => v.map fun n => (n : ℕ)⟩

theorem coePnatNat (v : PrimeMultiset) : ((v : Multiset ℕ+) : Multiset ℕ) = (v : Multiset ℕ) :=
  by 
    change (v.map (coeₓ : Nat.Primes → ℕ+)).map Subtype.val = v.map Subtype.val 
    rw [Multiset.map_map]
    congr

/-- The product of a `prime_multiset`, as a `ℕ+`. -/
def Prod (v : PrimeMultiset) : ℕ+ :=
  (v : Multiset Pnat).Prod

-- error in Data.Pnat.Factors: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem coe_prod (v : prime_multiset) : «expr = »((v.prod : exprℕ()), (v : multiset exprℕ()).prod) :=
begin
  let [ident h] [":", expr «expr = »((v.prod : exprℕ()), ((v.map coe).map coe).prod)] [":=", expr pnat.coe_monoid_hom.map_multiset_prod v.to_pnat_multiset],
  rw ["[", expr multiset.map_map, "]"] ["at", ident h],
  have [] [":", expr «expr = »(«expr ∘ »((coe : «exprℕ+»() → exprℕ()), (coe : nat.primes → «exprℕ+»())), coe)] [":=", expr funext (λ
    p, rfl)],
  rw ["[", expr this, "]"] ["at", ident h],
  exact [expr h]
end

theorem prod_of_prime (p : Nat.Primes) : (of_prime p).Prod = (p : ℕ+) :=
  Multiset.prod_singleton _

/-- If a `multiset ℕ` consists only of primes, it can be recast as a `prime_multiset`. -/
def of_nat_multiset (v : Multiset ℕ) (h : ∀ p : ℕ, p ∈ v → p.prime) : PrimeMultiset :=
  @Multiset.pmap ℕ Nat.Primes Nat.Prime (fun p hp => ⟨p, hp⟩) v h

-- error in Data.Pnat.Factors: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem to_of_nat_multiset (v : multiset exprℕ()) (h) : «expr = »((of_nat_multiset v h : multiset exprℕ()), v) :=
begin
  unfold_coes [],
  dsimp [] ["[", expr of_nat_multiset, ",", expr to_nat_multiset, "]"] [] [],
  have [] [":", expr «expr = »(λ
    (p : exprℕ())
    (h : p.prime), ((⟨p, h⟩ : nat.primes) : exprℕ()), λ p h, id p)] [":=", expr by { funext [ident p, ident h], refl }],
  rw ["[", expr multiset.map_pmap, ",", expr this, ",", expr multiset.pmap_eq_map, ",", expr multiset.map_id, "]"] []
end

theorem prod_of_nat_multiset (v : Multiset ℕ) h : ((of_nat_multiset v h).Prod : ℕ) = (v.prod : ℕ) :=
  by 
    rw [coe_prod, to_of_nat_multiset]

/-- If a `multiset ℕ+` consists only of primes, it can be recast as a `prime_multiset`. -/
def of_pnat_multiset (v : Multiset ℕ+) (h : ∀ p : ℕ+, p ∈ v → p.prime) : PrimeMultiset :=
  @Multiset.pmap ℕ+ Nat.Primes Pnat.Prime (fun p hp => ⟨(p : ℕ), hp⟩) v h

-- error in Data.Pnat.Factors: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem to_of_pnat_multiset
(v : multiset «exprℕ+»())
(h) : «expr = »((of_pnat_multiset v h : multiset «exprℕ+»()), v) :=
begin
  unfold_coes [],
  dsimp [] ["[", expr of_pnat_multiset, ",", expr to_pnat_multiset, "]"] [] [],
  have [] [":", expr «expr = »(λ
    (p : «exprℕ+»())
    (h : p.prime), (coe : nat.primes → «exprℕ+»()) ⟨p, h⟩, λ
    p h, id p)] [":=", expr by { funext [ident p, ident h], apply [expr subtype.eq], refl }],
  rw ["[", expr multiset.map_pmap, ",", expr this, ",", expr multiset.pmap_eq_map, ",", expr multiset.map_id, "]"] []
end

theorem prod_of_pnat_multiset (v : Multiset ℕ+) h : ((of_pnat_multiset v h).Prod : ℕ+) = v.prod :=
  by 
    dsimp [Prod]
    rw [to_of_pnat_multiset]

/-- Lists can be coerced to multisets; here we have some results
about how this interacts with our constructions on multisets. -/
def of_nat_list (l : List ℕ) (h : ∀ p : ℕ, p ∈ l → p.prime) : PrimeMultiset :=
  of_nat_multiset (l : Multiset ℕ) h

-- error in Data.Pnat.Factors: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prod_of_nat_list (l : list exprℕ()) (h) : «expr = »(((of_nat_list l h).prod : exprℕ()), l.prod) :=
by { have [] [] [":=", expr prod_of_nat_multiset (l : multiset exprℕ()) h],
  rw ["[", expr multiset.coe_prod, "]"] ["at", ident this],
  exact [expr this] }

/-- If a `list ℕ+` consists only of primes, it can be recast as a `prime_multiset` with
the coercion from lists to multisets. -/
def of_pnat_list (l : List ℕ+) (h : ∀ p : ℕ+, p ∈ l → p.prime) : PrimeMultiset :=
  of_pnat_multiset (l : Multiset ℕ+) h

-- error in Data.Pnat.Factors: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prod_of_pnat_list (l : list «exprℕ+»()) (h) : «expr = »((of_pnat_list l h).prod, l.prod) :=
by { have [] [] [":=", expr prod_of_pnat_multiset (l : multiset «exprℕ+»()) h],
  rw ["[", expr multiset.coe_prod, "]"] ["at", ident this],
  exact [expr this] }

/-- The product map gives a homomorphism from the additive monoid
of multisets to the multiplicative monoid ℕ+. -/
theorem prod_zero : (0 : PrimeMultiset).Prod = 1 :=
  by 
    dsimp [Prod]
    exact Multiset.prod_zero

theorem prod_add (u v : PrimeMultiset) : (u+v).Prod = u.prod*v.prod :=
  by 
    change (coe_pnat_monoid_hom (u+v)).Prod = _ 
    rw [coe_pnat_monoid_hom.map_add]
    exact Multiset.prod_add _ _

theorem prod_smul (d : ℕ) (u : PrimeMultiset) : (d • u).Prod = u.prod ^ d :=
  by 
    induction' d with d ih 
    rfl 
    rw [succ_nsmul, prod_add, ih, Nat.succ_eq_add_one, pow_succₓ, mul_commₓ]

end PrimeMultiset

namespace Pnat

/-- The prime factors of n, regarded as a multiset -/
def factor_multiset (n : ℕ+) : PrimeMultiset :=
  PrimeMultiset.ofNatList (Nat.factors n) (@Nat.prime_of_mem_factors n)

/-- The product of the factors is the original number -/
theorem prod_factor_multiset (n : ℕ+) : (factor_multiset n).Prod = n :=
  Eq$
    by 
      dsimp [factor_multiset]
      rw [PrimeMultiset.prod_of_nat_list]
      exact Nat.prod_factors n.pos

theorem coe_nat_factor_multiset (n : ℕ+) : (factor_multiset n : Multiset ℕ) = (Nat.factors n : Multiset ℕ) :=
  PrimeMultiset.to_of_nat_multiset (Nat.factors n) (@Nat.prime_of_mem_factors n)

end Pnat

namespace PrimeMultiset

-- error in Data.Pnat.Factors: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If we start with a multiset of primes, take the product and
 then factor it, we get back the original multiset. -/
theorem factor_multiset_prod (v : prime_multiset) : «expr = »(v.prod.factor_multiset, v) :=
begin
  apply [expr prime_multiset.coe_nat_injective],
  rw ["[", expr v.prod.coe_nat_factor_multiset, ",", expr prime_multiset.coe_prod, "]"] [],
  rcases [expr v, "with", "⟨", ident l, "⟩"],
  unfold_coes [],
  dsimp [] ["[", expr prime_multiset.to_nat_multiset, "]"] [] [],
  rw ["[", expr multiset.coe_prod, "]"] [],
  let [ident l'] [] [":=", expr l.map (coe : nat.primes → exprℕ())],
  have [] [":", expr ∀
   p : exprℕ(), «expr ∈ »(p, l') → p.prime] [":=", expr λ
   p
   hp, by { rcases [expr list.mem_map.mp hp, "with", "⟨", "⟨", ident p', ",", ident hp', "⟩", ",", "⟨", ident h_mem, ",", ident h_eq, "⟩", "⟩"],
     exact [expr «expr ▸ »(h_eq, hp')] }],
  exact [expr multiset.coe_eq_coe.mpr (@nat.factors_unique _ l' rfl this).symm]
end

end PrimeMultiset

namespace Pnat

/-- Positive integers biject with multisets of primes. -/
def factor_multiset_equiv : ℕ+ ≃ PrimeMultiset :=
  { toFun := factor_multiset, invFun := PrimeMultiset.prod, left_inv := prod_factor_multiset,
    right_inv := PrimeMultiset.factor_multiset_prod }

/-- Factoring gives a homomorphism from the multiplicative
 monoid ℕ+ to the additive monoid of multisets. -/
theorem factor_multiset_one : factor_multiset 1 = 0 :=
  by 
    simp [factor_multiset, PrimeMultiset.ofNatList, PrimeMultiset.ofNatMultiset]

-- error in Data.Pnat.Factors: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem factor_multiset_mul
(n m : «exprℕ+»()) : «expr = »(factor_multiset «expr * »(n, m), «expr + »(factor_multiset n, factor_multiset m)) :=
begin
  let [ident u] [] [":=", expr factor_multiset n],
  let [ident v] [] [":=", expr factor_multiset m],
  have [] [":", expr «expr = »(n, u.prod)] [":=", expr (prod_factor_multiset n).symm],
  rw ["[", expr this, "]"] [],
  have [] [":", expr «expr = »(m, v.prod)] [":=", expr (prod_factor_multiset m).symm],
  rw ["[", expr this, "]"] [],
  rw ["[", "<-", expr prime_multiset.prod_add, "]"] [],
  repeat { rw ["[", expr prime_multiset.factor_multiset_prod, "]"] [] }
end

-- error in Data.Pnat.Factors: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem factor_multiset_pow
(n : «exprℕ+»())
(m : exprℕ()) : «expr = »(factor_multiset «expr ^ »(n, m), «expr • »(m, factor_multiset n)) :=
begin
  let [ident u] [] [":=", expr factor_multiset n],
  have [] [":", expr «expr = »(n, u.prod)] [":=", expr (prod_factor_multiset n).symm],
  rw ["[", expr this, ",", "<-", expr prime_multiset.prod_smul, "]"] [],
  repeat { rw ["[", expr prime_multiset.factor_multiset_prod, "]"] [] }
end

/-- Factoring a prime gives the corresponding one-element multiset. -/
theorem factor_multiset_of_prime (p : Nat.Primes) : (p : ℕ+).factorMultiset = PrimeMultiset.ofPrime p :=
  by 
    apply factor_multiset_equiv.symm.injective 
    change (p : ℕ+).factorMultiset.Prod = (PrimeMultiset.ofPrime p).Prod 
    rw [(p : ℕ+).prod_factor_multiset, PrimeMultiset.prod_of_prime]

/-- We now have four different results that all encode the
 idea that inequality of multisets corresponds to divisibility
 of positive integers. -/
theorem factor_multiset_le_iff {m n : ℕ+} : factor_multiset m ≤ factor_multiset n ↔ m ∣ n :=
  by 
    split 
    ·
      intro h 
      rw [←prod_factor_multiset m, ←prod_factor_multiset m]
      apply Dvd.intro (n.factor_multiset - m.factor_multiset).Prod 
      rw [←PrimeMultiset.prod_add, PrimeMultiset.factor_multiset_prod, add_tsub_cancel_of_le h, prod_factor_multiset]
    ·
      intro h 
      rw [←mul_div_exact h, factor_multiset_mul]
      exact le_self_add

theorem factor_multiset_le_iff' {m : ℕ+} {v : PrimeMultiset} : factor_multiset m ≤ v ↔ m ∣ v.prod :=
  by 
    let h := @factor_multiset_le_iff m v.prod 
    rw [v.factor_multiset_prod] at h 
    exact h

end Pnat

namespace PrimeMultiset

theorem prod_dvd_iff {u v : PrimeMultiset} : u.prod ∣ v.prod ↔ u ≤ v :=
  by 
    let h := @Pnat.factor_multiset_le_iff' u.prod v 
    rw [u.factor_multiset_prod] at h 
    exact h.symm

theorem prod_dvd_iff' {u : PrimeMultiset} {n : ℕ+} : u.prod ∣ n ↔ u ≤ n.factor_multiset :=
  by 
    let h := @prod_dvd_iff u n.factor_multiset 
    rw [n.prod_factor_multiset] at h 
    exact h

end PrimeMultiset

namespace Pnat

/-- The gcd and lcm operations on positive integers correspond
 to the inf and sup operations on multisets. -/
theorem factor_multiset_gcd (m n : ℕ+) : factor_multiset (gcd m n) = factor_multiset m⊓factor_multiset n :=
  by 
    apply le_antisymmₓ
    ·
      apply le_inf_iff.mpr <;> split  <;> apply factor_multiset_le_iff.mpr 
      exact gcd_dvd_left m n 
      exact gcd_dvd_right m n
    ·
      rw [←PrimeMultiset.prod_dvd_iff, prod_factor_multiset]
      apply dvd_gcd <;> rw [PrimeMultiset.prod_dvd_iff']
      exact inf_le_left 
      exact inf_le_right

theorem factor_multiset_lcm (m n : ℕ+) : factor_multiset (lcm m n) = factor_multiset m⊔factor_multiset n :=
  by 
    apply le_antisymmₓ
    ·
      rw [←PrimeMultiset.prod_dvd_iff, prod_factor_multiset]
      apply lcm_dvd <;> rw [←factor_multiset_le_iff']
      exact le_sup_left 
      exact le_sup_right
    ·
      apply sup_le_iff.mpr <;> split  <;> apply factor_multiset_le_iff.mpr 
      exact dvd_lcm_left m n 
      exact dvd_lcm_right m n

/-- The number of occurrences of p in the factor multiset of m
 is the same as the p-adic valuation of m. -/
theorem count_factor_multiset (m : ℕ+) (p : Nat.Primes) (k : ℕ) : (p : ℕ+) ^ k ∣ m ↔ k ≤ m.factor_multiset.count p :=
  by 
    intros 
    rw [Multiset.le_count_iff_repeat_le]
    rw [←factor_multiset_le_iff, factor_multiset_pow, factor_multiset_of_prime]
    congr 2
    apply multiset.eq_repeat.mpr 
    split 
    ·
      rw [Multiset.card_nsmul, PrimeMultiset.card_of_prime, mul_oneₓ]
    ·
      intro q h 
      rw [PrimeMultiset.ofPrime, Multiset.nsmul_singleton _ k] at h 
      exact Multiset.eq_of_mem_repeat h

end Pnat

namespace PrimeMultiset

-- error in Data.Pnat.Factors: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prod_inf (u v : prime_multiset) : «expr = »(«expr ⊓ »(u, v).prod, pnat.gcd u.prod v.prod) :=
begin
  let [ident n] [] [":=", expr u.prod],
  let [ident m] [] [":=", expr v.prod],
  change [expr «expr = »(«expr ⊓ »(u, v).prod, pnat.gcd n m)] [] [],
  have [] [":", expr «expr = »(u, n.factor_multiset)] [":=", expr u.factor_multiset_prod.symm],
  rw ["[", expr this, "]"] [],
  have [] [":", expr «expr = »(v, m.factor_multiset)] [":=", expr v.factor_multiset_prod.symm],
  rw ["[", expr this, "]"] [],
  rw ["[", "<-", expr pnat.factor_multiset_gcd n m, ",", expr pnat.prod_factor_multiset, "]"] []
end

-- error in Data.Pnat.Factors: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prod_sup (u v : prime_multiset) : «expr = »(«expr ⊔ »(u, v).prod, pnat.lcm u.prod v.prod) :=
begin
  let [ident n] [] [":=", expr u.prod],
  let [ident m] [] [":=", expr v.prod],
  change [expr «expr = »(«expr ⊔ »(u, v).prod, pnat.lcm n m)] [] [],
  have [] [":", expr «expr = »(u, n.factor_multiset)] [":=", expr u.factor_multiset_prod.symm],
  rw ["[", expr this, "]"] [],
  have [] [":", expr «expr = »(v, m.factor_multiset)] [":=", expr v.factor_multiset_prod.symm],
  rw ["[", expr this, "]"] [],
  rw ["[", "<-", expr pnat.factor_multiset_lcm n m, ",", expr pnat.prod_factor_multiset, "]"] []
end

end PrimeMultiset

