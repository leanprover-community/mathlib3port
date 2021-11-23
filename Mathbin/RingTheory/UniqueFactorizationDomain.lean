import Mathbin.RingTheory.Noetherian 
import Mathbin.Algebra.GcdMonoid.Basic 
import Mathbin.RingTheory.Multiplicity

/-!

# Unique factorization

## Main Definitions
* `wf_dvd_monoid` holds for `monoid`s for which a strict divisibility relation is
  well-founded.
* `unique_factorization_monoid` holds for `wf_dvd_monoid`s where
  `irreducible` is equivalent to `prime`

## To do
* set up the complete lattice structure on `factor_set`.

-/


variable{α : Type _}

local infixl:50 " ~ᵤ " => Associated

/-- Well-foundedness of the strict version of |, which is equivalent to the descending chain
condition on divisibility and to the ascending chain condition on
principal ideals in an integral domain.
  -/
class WfDvdMonoid(α : Type _)[CommMonoidWithZero α] : Prop where 
  well_founded_dvd_not_unit : WellFounded (@DvdNotUnit α _)

export WfDvdMonoid(well_founded_dvd_not_unit)

instance (priority := 100)IsNoetherianRing.wf_dvd_monoid [CommRingₓ α] [IsDomain α] [IsNoetherianRing α] :
  WfDvdMonoid α :=
  ⟨by 
      convert InvImage.wfₓ (fun a => Ideal.span ({a} : Set α)) (well_founded_submodule_gt _ _)
      ext 
      exact ideal.span_singleton_lt_span_singleton.symm⟩

namespace WfDvdMonoid

variable[CommMonoidWithZero α]

open Associates Nat

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem of_wf_dvd_monoid_associates (h : wf_dvd_monoid (associates α)) : wf_dvd_monoid α :=
⟨begin
   haveI [] [] [":=", expr h],
   refine [expr (surjective.well_founded_iff mk_surjective _).2 wf_dvd_monoid.well_founded_dvd_not_unit],
   intros [],
   rw [expr mk_dvd_not_unit_mk_iff] []
 end⟩

variable[WfDvdMonoid α]

instance wf_dvd_monoid_associates : WfDvdMonoid (Associates α) :=
  ⟨by 
      refine' (Surjective.well_founded_iff mk_surjective _).1 WfDvdMonoid.well_founded_dvd_not_unit 
      intros 
      rw [mk_dvd_not_unit_mk_iff]⟩

theorem well_founded_associates : WellFounded (· < · : Associates α → Associates α → Prop) :=
  Subrelation.wfₓ (fun x y => dvd_not_unit_of_lt) WfDvdMonoid.well_founded_dvd_not_unit

attribute [local elab_as_eliminator] WellFounded.fix

theorem exists_irreducible_factor {a : α} (ha : ¬IsUnit a) (ha0 : a ≠ 0) : ∃ i, Irreducible i ∧ i ∣ a :=
  (irreducible_or_factor a ha).elim (fun hai => ⟨a, hai, dvd_rfl⟩)
    (WellFounded.fix WfDvdMonoid.well_founded_dvd_not_unit
      (fun a ih ha ha0 ⟨x, y, hx, hy, hxy⟩ =>
        have hx0 : x ≠ 0 :=
          fun hx0 =>
            ha0
              (by 
                rw [←hxy, hx0, zero_mul])
        (irreducible_or_factor x hx).elim
          (fun hxi =>
            ⟨x, hxi,
              hxy ▸
                by 
                  simp ⟩)
          fun hxf =>
            let ⟨i, hi⟩ := ih x ⟨hx0, y, hy, hxy.symm⟩ hx hx0 hxf
            ⟨i, hi.1,
              hi.2.trans
                (hxy ▸
                  by 
                    simp )⟩)
      a ha ha0)

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[elab_as_eliminator]
theorem induction_on_irreducible
{P : α → exprProp()}
(a : α)
(h0 : P 0)
(hu : ∀ u : α, is_unit u → P u)
(hi : ∀ a i : α, «expr ≠ »(a, 0) → irreducible i → P a → P «expr * »(i, a)) : P a :=
by haveI [] [] [":=", expr classical.dec]; exact [expr well_founded.fix wf_dvd_monoid.well_founded_dvd_not_unit (λ
  a
  ih, if ha0 : «expr = »(a, 0) then «expr ▸ »(ha0.symm, h0) else if hau : is_unit a then hu a hau else let ⟨i, hii, ⟨b, hb⟩⟩ := exists_irreducible_factor hau ha0 in
  have hb0 : «expr ≠ »(b, 0), from λ hb0, by simp [] [] [] ["*"] [] ["at", "*"],
  «expr ▸ »(hb.symm, hi _ _ hb0 hii (ih _ ⟨hb0, i, hii.1, by rw ["[", expr hb, ",", expr mul_comm, "]"] []⟩))) a]

theorem exists_factors (a : α) : a ≠ 0 → ∃ f : Multiset α, (∀ b _ : b ∈ f, Irreducible b) ∧ Associated f.prod a :=
  WfDvdMonoid.induction_on_irreducible a (fun h => (h rfl).elim)
    (fun u hu _ =>
      ⟨0,
        ⟨by 
            simp [hu],
          Associated.symm
            (by 
              simp [hu, associated_one_iff_is_unit])⟩⟩)
    fun a i ha0 hii ih hia0 =>
      let ⟨s, hs⟩ := ih ha0
      ⟨i ::ₘ s,
        ⟨by 
            clear _let_match <;> finish,
          by 
            rw [Multiset.prod_cons]
            exact hs.2.mul_left _⟩⟩

end WfDvdMonoid

theorem WfDvdMonoid.of_well_founded_associates [CommCancelMonoidWithZero α]
  (h : WellFounded (· < · : Associates α → Associates α → Prop)) : WfDvdMonoid α :=
  WfDvdMonoid.of_wf_dvd_monoid_associates
    ⟨by 
        convert h 
        ext 
        exact Associates.dvd_not_unit_iff_lt⟩

theorem WfDvdMonoid.iff_well_founded_associates [CommCancelMonoidWithZero α] :
  WfDvdMonoid α ↔ WellFounded (· < · : Associates α → Associates α → Prop) :=
  ⟨by 
      apply WfDvdMonoid.well_founded_associates,
    WfDvdMonoid.of_well_founded_associates⟩

section Prio

set_option default_priority 100

/-- unique factorization monoids.

These are defined as `comm_cancel_monoid_with_zero`s with well-founded strict divisibility
relations, but this is equivalent to more familiar definitions:

Each element (except zero) is uniquely represented as a multiset of irreducible factors.
Uniqueness is only up to associated elements.

Each element (except zero) is non-uniquely represented as a multiset
of prime factors.

To define a UFD using the definition in terms of multisets
of irreducible factors, use the definition `of_exists_unique_irreducible_factors`

To define a UFD using the definition in terms of multisets
of prime factors, use the definition `of_exists_prime_factors`

-/
class UniqueFactorizationMonoid(α : Type _)[CommCancelMonoidWithZero α] extends WfDvdMonoid α : Prop where 
  irreducible_iff_prime : ∀ {a : α}, Irreducible a ↔ Prime a

/-- Can't be an instance because it would cause a loop `ufm → wf_dvd_monoid → ufm → ...`. -/
@[reducible]
theorem ufm_of_gcd_of_wf_dvd_monoid [CommCancelMonoidWithZero α] [WfDvdMonoid α] [GcdMonoid α] :
  UniqueFactorizationMonoid α :=
  { ‹WfDvdMonoid α› with irreducible_iff_prime := fun _ => GcdMonoid.irreducible_iff_prime }

instance Associates.ufm [CommCancelMonoidWithZero α] [UniqueFactorizationMonoid α] :
  UniqueFactorizationMonoid (Associates α) :=
  { (WfDvdMonoid.wf_dvd_monoid_associates : WfDvdMonoid (Associates α)) with
    irreducible_iff_prime :=
      by 
        rw [←Associates.irreducible_iff_prime_iff]
        apply UniqueFactorizationMonoid.irreducible_iff_prime }

end Prio

namespace UniqueFactorizationMonoid

variable[CommCancelMonoidWithZero α][UniqueFactorizationMonoid α]

theorem exists_prime_factors (a : α) : a ≠ 0 → ∃ f : Multiset α, (∀ b _ : b ∈ f, Prime b) ∧ f.prod ~ᵤ a :=
  by 
    simpRw [←UniqueFactorizationMonoid.irreducible_iff_prime]
    apply WfDvdMonoid.exists_factors a

@[elab_as_eliminator]
theorem induction_on_prime {P : α → Prop} (a : α) (h₁ : P 0) (h₂ : ∀ x : α, IsUnit x → P x)
  (h₃ : ∀ a p : α, a ≠ 0 → Prime p → P a → P (p*a)) : P a :=
  by 
    simpRw [←UniqueFactorizationMonoid.irreducible_iff_prime]  at h₃ 
    exact WfDvdMonoid.induction_on_irreducible a h₁ h₂ h₃

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem factors_unique : ∀
{f
 g : multiset α}, ∀
x «expr ∈ » f, irreducible x → ∀
x «expr ∈ » g, irreducible x → «expr ~ᵤ »(f.prod, g.prod) → multiset.rel associated f g :=
by haveI [] [] [":=", expr classical.dec_eq α]; exact [expr λ
 f, multiset.induction_on f (λ
  g
  _
  hg
  h, «expr $ »(multiset.rel_zero_left.2, multiset.eq_zero_of_forall_not_mem (λ
    x hx, have is_unit g.prod, by simpa [] [] [] ["[", expr associated_one_iff_is_unit, "]"] [] ["using", expr h.symm],
    (hg x hx).not_unit (is_unit_iff_dvd_one.2 ((multiset.dvd_prod hx).trans (is_unit_iff_dvd_one.1 this)))))) (λ
  p
  f
  ih
  g
  hf
  hg
  hfg, let ⟨b, hbg, hb⟩ := «expr $ »(exists_associated_mem_of_dvd_prod (irreducible_iff_prime.1 (hf p (by simp [] [] [] [] [] []))) (λ
        q
        hq, irreducible_iff_prime.1 (hg _ hq)), hfg.dvd_iff_dvd_right.1 (show «expr ∣ »(p, «expr ::ₘ »(p, f).prod), by simp [] [] [] [] [] [])) in
  begin
    rw ["<-", expr multiset.cons_erase hbg] [],
    exact [expr multiset.rel.cons hb (ih (λ
       q
       hq, hf _ (by simp [] [] [] ["[", expr hq, "]"] [] [])) (λ
       (q)
       (hq : «expr ∈ »(q, g.erase b)), hg q (multiset.mem_of_mem_erase hq)) (associated.of_mul_left (by rwa ["[", "<-", expr multiset.prod_cons, ",", "<-", expr multiset.prod_cons, ",", expr multiset.cons_erase hbg, "]"] []) hb (hf p (by simp [] [] [] [] [] [])).ne_zero))]
  end)]

end UniqueFactorizationMonoid

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prime_factors_unique
[comm_cancel_monoid_with_zero α] : ∀
{f
 g : multiset α}, ∀
x «expr ∈ » f, prime x → ∀ x «expr ∈ » g, prime x → «expr ~ᵤ »(f.prod, g.prod) → multiset.rel associated f g :=
by haveI [] [] [":=", expr classical.dec_eq α]; exact [expr λ
 f, multiset.induction_on f (λ
  g
  _
  hg
  h, «expr $ »(multiset.rel_zero_left.2, «expr $ »(multiset.eq_zero_of_forall_not_mem, λ
    x hx, have is_unit g.prod, by simpa [] [] [] ["[", expr associated_one_iff_is_unit, "]"] [] ["using", expr h.symm],
    «expr $ »((hg x hx).not_unit, «expr $ »(is_unit_iff_dvd_one.2, (multiset.dvd_prod hx).trans (is_unit_iff_dvd_one.1 this)))))) (λ
  p
  f
  ih
  g
  hf
  hg
  hfg, let ⟨b, hbg, hb⟩ := «expr $ »(exists_associated_mem_of_dvd_prod (hf p (by simp [] [] [] [] [] [])) (λ
        q
        hq, hg _ hq), hfg.dvd_iff_dvd_right.1 (show «expr ∣ »(p, «expr ::ₘ »(p, f).prod), by simp [] [] [] [] [] [])) in
  begin
    rw ["<-", expr multiset.cons_erase hbg] [],
    exact [expr multiset.rel.cons hb (ih (λ
       q
       hq, hf _ (by simp [] [] [] ["[", expr hq, "]"] [] [])) (λ
       (q)
       (hq : «expr ∈ »(q, g.erase b)), hg q (multiset.mem_of_mem_erase hq)) (associated.of_mul_left (by rwa ["[", "<-", expr multiset.prod_cons, ",", "<-", expr multiset.prod_cons, ",", expr multiset.cons_erase hbg, "]"] []) hb (hf p (by simp [] [] [] [] [] [])).ne_zero))]
  end)]

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If an irreducible has a prime factorization,
  then it is an associate of one of its prime factors. -/
theorem prime_factors_irreducible
[comm_cancel_monoid_with_zero α]
{a : α}
{f : multiset α}
(ha : irreducible a)
(pfa : «expr ∧ »(∀
  b «expr ∈ » f, prime b, «expr ~ᵤ »(f.prod, a))) : «expr∃ , »((p), «expr ∧ »(«expr ~ᵤ »(a, p), «expr = »(f, {p}))) :=
begin
  haveI [] [] [":=", expr classical.dec_eq α],
  refine [expr multiset.induction_on f (λ
    h, (ha.not_unit (associated_one_iff_is_unit.1 (associated.symm h))).elim) _ pfa.2 pfa.1],
  rintros [ident p, ident s, "_", "⟨", ident u, ",", ident hu, "⟩", ident hs],
  use [expr p],
  have [ident hs0] [":", expr «expr = »(s, 0)] [],
  { by_contra [ident hs0],
    obtain ["⟨", ident q, ",", ident hq, "⟩", ":=", expr multiset.exists_mem_of_ne_zero hs0],
    apply [expr (hs q (by simp [] [] [] ["[", expr hq, "]"] [] [])).2.1],
    refine [expr (ha.is_unit_or_is_unit (_ : «expr = »(_, «expr * »(«expr * »(«expr * »(p, «expr↑ »(u)), (s.erase q).prod), _)))).resolve_left _],
    { rw ["[", expr mul_right_comm _ _ q, ",", expr mul_assoc, ",", "<-", expr multiset.prod_cons, ",", expr multiset.cons_erase hq, ",", "<-", expr hu, ",", expr mul_comm, ",", expr mul_comm p _, ",", expr mul_assoc, "]"] [],
      simp [] [] [] [] [] [] },
    apply [expr mt is_unit_of_mul_is_unit_left (mt is_unit_of_mul_is_unit_left _)],
    apply [expr (hs p (multiset.mem_cons_self _ _)).2.1] },
  simp [] [] ["only"] ["[", expr mul_one, ",", expr multiset.prod_cons, ",", expr multiset.prod_zero, ",", expr hs0, "]"] [] ["at", "*"],
  exact [expr ⟨associated.symm ⟨u, hu⟩, rfl⟩]
end

section ExistsPrimeFactors

variable[CommCancelMonoidWithZero α]

variable(pf : ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀ b _ : b ∈ f, Prime b) ∧ f.prod ~ᵤ a)

include pf

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem wf_dvd_monoid.of_exists_prime_factors : wf_dvd_monoid α :=
⟨begin
   classical,
   apply [expr rel_hom.well_founded (rel_hom.mk _ _) (with_top.well_founded_lt nat.lt_wf)],
   { intro [ident a],
     by_cases [expr h, ":", expr «expr = »(a, 0)],
     { exact [expr «expr⊤»()] },
     exact [expr (classical.some (pf a h)).card] },
   rintros [ident a, ident b, "⟨", ident ane0, ",", "⟨", ident c, ",", ident hc, ",", ident b_eq, "⟩", "⟩"],
   rw [expr dif_neg ane0] [],
   by_cases [expr h, ":", expr «expr = »(b, 0)],
   { simp [] [] [] ["[", expr h, ",", expr lt_top_iff_ne_top, "]"] [] [] },
   rw ["[", expr dif_neg h, ",", expr with_top.coe_lt_coe, "]"] [],
   have [ident cne0] [":", expr «expr ≠ »(c, 0)] [],
   { refine [expr mt (λ con, _) h],
     rw ["[", expr b_eq, ",", expr con, ",", expr mul_zero, "]"] [] },
   calc
     «expr < »(multiset.card (classical.some (pf a ane0)), «expr + »(_, multiset.card (classical.some (pf c cne0)))) : lt_add_of_pos_right _ (multiset.card_pos.mpr (λ
       con, hc (associated_one_iff_is_unit.mp _)))
     «expr = »(..., multiset.card «expr + »(classical.some (pf a ane0), classical.some (pf c cne0))) : (multiset.card_add _ _).symm
     «expr = »(..., multiset.card (classical.some (pf b h))) : multiset.card_eq_card_of_rel (prime_factors_unique _ (classical.some_spec (pf _ h)).1 _),
   { convert [] [expr (classical.some_spec (pf c cne0)).2.symm] [],
     rw ["[", expr con, ",", expr multiset.prod_zero, "]"] [] },
   { intros [ident x, ident hadd],
     rw [expr multiset.mem_add] ["at", ident hadd],
     cases [expr hadd] []; apply [expr (classical.some_spec (pf _ _)).1 _ hadd] },
   { rw [expr multiset.prod_add] [],
     transitivity [expr «expr * »(a, c)],
     { apply [expr associated.mul_mul]; apply [expr (classical.some_spec (pf _ _)).2] },
     { rw ["<-", expr b_eq] [],
       apply [expr (classical.some_spec (pf _ _)).2.symm] } }
 end⟩

theorem irreducible_iff_prime_of_exists_prime_factors {p : α} : Irreducible p ↔ Prime p :=
  by 
    byCases' hp0 : p = 0
    ·
      simp [hp0]
    refine' ⟨fun h => _, Prime.irreducible⟩
    obtain ⟨f, hf⟩ := pf p hp0 
    obtain ⟨q, hq, rfl⟩ := prime_factors_irreducible h hf 
    rw [hq.prime_iff]
    exact hf.1 q (Multiset.mem_singleton_self _)

theorem UniqueFactorizationMonoid.of_exists_prime_factors : UniqueFactorizationMonoid α :=
  { WfDvdMonoid.of_exists_prime_factors pf with
    irreducible_iff_prime := fun _ => irreducible_iff_prime_of_exists_prime_factors pf }

end ExistsPrimeFactors

theorem UniqueFactorizationMonoid.iff_exists_prime_factors [CommCancelMonoidWithZero α] :
  UniqueFactorizationMonoid α ↔ ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀ b _ : b ∈ f, Prime b) ∧ f.prod ~ᵤ a :=
  ⟨fun h => @UniqueFactorizationMonoid.exists_prime_factors _ _ h, UniqueFactorizationMonoid.of_exists_prime_factors⟩

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem irreducible_iff_prime_of_exists_unique_irreducible_factors
[comm_cancel_monoid_with_zero α]
(eif : ∀
 a : α, «expr ≠ »(a, 0) → «expr∃ , »((f : multiset α), «expr ∧ »(∀
   b «expr ∈ » f, irreducible b, «expr ~ᵤ »(f.prod, a))))
(uif : ∀
 f
 g : multiset α, ∀
 x «expr ∈ » f, irreducible x → ∀
 x «expr ∈ » g, irreducible x → «expr ~ᵤ »(f.prod, g.prod) → multiset.rel associated f g)
(p : α) : «expr ↔ »(irreducible p, prime p) :=
⟨by letI [] [] [":=", expr classical.dec_eq α]; exact [expr λ
  hpi, ⟨hpi.ne_zero, hpi.1, λ
   (a b)
   ⟨x, hx⟩, if hab0 : «expr = »(«expr * »(a, b), 0) then (eq_zero_or_eq_zero_of_mul_eq_zero hab0).elim (λ
    ha0, by simp [] [] [] ["[", expr ha0, "]"] [] []) (λ
    hb0, by simp [] [] [] ["[", expr hb0, "]"] [] []) else have hx0 : «expr ≠ »(x, 0), from λ
   hx0, by simp [] [] [] ["*"] [] ["at", "*"],
   have ha0 : «expr ≠ »(a, 0), from left_ne_zero_of_mul hab0,
   have hb0 : «expr ≠ »(b, 0), from right_ne_zero_of_mul hab0,
   begin
     cases [expr eif x hx0] ["with", ident fx, ident hfx],
     cases [expr eif a ha0] ["with", ident fa, ident hfa],
     cases [expr eif b hb0] ["with", ident fb, ident hfb],
     have [ident h] [":", expr multiset.rel associated «expr ::ₘ »(p, fx) «expr + »(fa, fb)] [],
     { apply [expr uif],
       { exact [expr λ i hi, (multiset.mem_cons.1 hi).elim (λ hip, «expr ▸ »(hip.symm, hpi)) (hfx.1 _)] },
       { exact [expr λ i hi, (multiset.mem_add.1 hi).elim (hfa.1 _) (hfb.1 _)] },
       calc
         «expr ~ᵤ »(multiset.prod «expr ::ₘ »(p, fx), «expr * »(a, b)) : by rw ["[", expr hx, ",", expr multiset.prod_cons, "]"] []; exact [expr hfx.2.mul_left _]
         «expr ~ᵤ »(..., «expr * »(fa.prod, fb.prod)) : hfa.2.symm.mul_mul hfb.2.symm
         «expr = »(..., _) : by rw [expr multiset.prod_add] [] },
     exact [expr let ⟨q, hqf, hq⟩ := multiset.exists_mem_of_rel_of_mem h (multiset.mem_cons_self p _) in
      (multiset.mem_add.1 hqf).elim (λ
       hqa, «expr $ »(or.inl, «expr $ »(hq.dvd_iff_dvd_left.2, hfa.2.dvd_iff_dvd_right.1 (multiset.dvd_prod hqa)))) (λ
       hqb, «expr $ »(or.inr, «expr $ »(hq.dvd_iff_dvd_left.2, hfb.2.dvd_iff_dvd_right.1 (multiset.dvd_prod hqb))))]
   end⟩], prime.irreducible⟩

theorem UniqueFactorizationMonoid.of_exists_unique_irreducible_factors [CommCancelMonoidWithZero α]
  (eif : ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀ b _ : b ∈ f, Irreducible b) ∧ f.prod ~ᵤ a)
  (uif :
    ∀ f g : Multiset α,
      (∀ x _ : x ∈ f, Irreducible x) →
        (∀ x _ : x ∈ g, Irreducible x) → f.prod ~ᵤ g.prod → Multiset.Rel Associated f g) :
  UniqueFactorizationMonoid α :=
  UniqueFactorizationMonoid.of_exists_prime_factors
    (by 
      convert eif 
      simpRw [irreducible_iff_prime_of_exists_unique_irreducible_factors eif uif])

namespace UniqueFactorizationMonoid

variable[CommCancelMonoidWithZero α][DecidableEq α]

variable[UniqueFactorizationMonoid α]

/-- Noncomputably determines the multiset of prime factors. -/
noncomputable def factors (a : α) : Multiset α :=
  if h : a = 0 then 0 else Classical.some (UniqueFactorizationMonoid.exists_prime_factors a h)

theorem factors_prod {a : α} (ane0 : a ≠ 0) : Associated (factors a).Prod a :=
  by 
    rw [factors, dif_neg ane0]
    exact (Classical.some_spec (exists_prime_factors a ane0)).2

theorem prime_of_factor {a : α} : ∀ x : α, x ∈ factors a → Prime x :=
  by 
    rw [factors]
    splitIfs with ane0
    ·
      simp only [Multiset.not_mem_zero, forall_false_left, forall_const]
    intro x hx 
    exact (Classical.some_spec (UniqueFactorizationMonoid.exists_prime_factors a ane0)).1 x hx

theorem irreducible_of_factor {a : α} : ∀ x : α, x ∈ factors a → Irreducible x :=
  fun x h => (prime_of_factor x h).Irreducible

theorem exists_mem_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
  p ∣ a → ∃ (q : _)(_ : q ∈ factors a), p ~ᵤ q :=
  fun ⟨b, hb⟩ =>
    have hb0 : b ≠ 0 :=
      fun hb0 =>
        by 
          simp_all 
    have  : Multiset.Rel Associated (p ::ₘ factors b) (factors a) :=
      factors_unique (fun x hx => (Multiset.mem_cons.1 hx).elim (fun h => h.symm ▸ hp) (irreducible_of_factor _))
        irreducible_of_factor
        (Associated.symm$
          calc Multiset.prod (factors a) ~ᵤ a := factors_prod ha0 
            _ = p*b := hb 
            _ ~ᵤ Multiset.prod (p ::ₘ factors b) :=
            by 
              rw [Multiset.prod_cons] <;> exact (factors_prod hb0).symm.mul_left _
            )
    Multiset.exists_mem_of_rel_of_mem this
      (by 
        simp )

end UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

variable[CommCancelMonoidWithZero α][DecidableEq α][NormalizationMonoid α]

variable[UniqueFactorizationMonoid α]

/-- Noncomputably determines the multiset of prime factors. -/
noncomputable def normalized_factors (a : α) : Multiset α :=
  Multiset.map normalize$ factors a

theorem normalized_factors_prod {a : α} (ane0 : a ≠ 0) : Associated (normalized_factors a).Prod a :=
  by 
    rw [normalized_factors, factors, dif_neg ane0]
    refine' Associated.trans _ (Classical.some_spec (exists_prime_factors a ane0)).2
    rw [←Associates.mk_eq_mk_iff_associated, ←Associates.prod_mk, ←Associates.prod_mk, Multiset.map_map]
    congr 2 
    ext 
    rw [Function.comp_apply, Associates.mk_normalize]

theorem prime_of_normalized_factor {a : α} : ∀ x : α, x ∈ normalized_factors a → Prime x :=
  by 
    rw [normalized_factors, factors]
    splitIfs with ane0
    ·
      simp 
    intro x hx 
    rcases Multiset.mem_map.1 hx with ⟨y, ⟨hy, rfl⟩⟩
    rw [(normalize_associated _).prime_iff]
    exact (Classical.some_spec (UniqueFactorizationMonoid.exists_prime_factors a ane0)).1 y hy

theorem irreducible_of_normalized_factor {a : α} : ∀ x : α, x ∈ normalized_factors a → Irreducible x :=
  fun x h => (prime_of_normalized_factor x h).Irreducible

theorem normalize_normalized_factor {a : α} : ∀ x : α, x ∈ normalized_factors a → normalize x = x :=
  by 
    rw [normalized_factors, factors]
    splitIfs with h
    ·
      simp 
    intro x hx 
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx 
    apply normalize_idem

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem normalized_factors_irreducible {a : α} (ha : irreducible a) : «expr = »(normalized_factors a, {normalize a}) :=
begin
  obtain ["⟨", ident p, ",", ident a_assoc, ",", ident hp, "⟩", ":=", expr prime_factors_irreducible ha ⟨prime_of_normalized_factor, normalized_factors_prod ha.ne_zero⟩],
  have [ident p_mem] [":", expr «expr ∈ »(p, normalized_factors a)] [],
  { rw [expr hp] [],
    exact [expr multiset.mem_singleton_self _] },
  convert [] [expr hp] [],
  rwa ["[", "<-", expr normalize_normalized_factor p p_mem, ",", expr normalize_eq_normalize_iff, ",", expr dvd_dvd_iff_associated, "]"] []
end

theorem exists_mem_normalized_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
  p ∣ a → ∃ (q : _)(_ : q ∈ normalized_factors a), p ~ᵤ q :=
  fun ⟨b, hb⟩ =>
    have hb0 : b ≠ 0 :=
      fun hb0 =>
        by 
          simp_all 
    have  : Multiset.Rel Associated (p ::ₘ normalized_factors b) (normalized_factors a) :=
      factors_unique
        (fun x hx => (Multiset.mem_cons.1 hx).elim (fun h => h.symm ▸ hp) (irreducible_of_normalized_factor _))
        irreducible_of_normalized_factor
        (Associated.symm$
          calc Multiset.prod (normalized_factors a) ~ᵤ a := normalized_factors_prod ha0 
            _ = p*b := hb 
            _ ~ᵤ Multiset.prod (p ::ₘ normalized_factors b) :=
            by 
              rw [Multiset.prod_cons] <;> exact (normalized_factors_prod hb0).symm.mul_left _
            )
    Multiset.exists_mem_of_rel_of_mem this
      (by 
        simp )

@[simp]
theorem normalized_factors_zero : normalized_factors (0 : α) = 0 :=
  by 
    simp [normalized_factors, factors]

@[simp]
theorem normalized_factors_one : normalized_factors (1 : α) = 0 :=
  by 
    nontriviality α using normalized_factors, factors 
    rw [←Multiset.rel_zero_right]
    apply factors_unique irreducible_of_normalized_factor
    ·
      intro x hx 
      exfalso 
      apply Multiset.not_mem_zero x hx
    ·
      simp [normalized_factors_prod (@one_ne_zero α _ _)]
    infer_instance

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem normalized_factors_mul
{x y : α}
(hx : «expr ≠ »(x, 0))
(hy : «expr ≠ »(y, 0)) : «expr = »(normalized_factors «expr * »(x, y), «expr + »(normalized_factors x, normalized_factors y)) :=
begin
  have [ident h] [":", expr «expr = »((normalize : α → α), «expr ∘ »(associates.out, associates.mk))] [],
  { ext [] [] [],
    rw ["[", expr function.comp_apply, ",", expr associates.out_mk, "]"] [] },
  rw ["[", "<-", expr multiset.map_id' (normalized_factors «expr * »(x, y)), ",", "<-", expr multiset.map_id' (normalized_factors x), ",", "<-", expr multiset.map_id' (normalized_factors y), ",", "<-", expr multiset.map_congr normalize_normalized_factor, ",", "<-", expr multiset.map_congr normalize_normalized_factor, ",", "<-", expr multiset.map_congr normalize_normalized_factor, ",", "<-", expr multiset.map_add, ",", expr h, ",", "<-", expr multiset.map_map associates.out, ",", expr eq_comm, ",", "<-", expr multiset.map_map associates.out, "]"] [],
  refine [expr congr rfl _],
  apply [expr multiset.map_mk_eq_map_mk_of_rel],
  apply [expr factors_unique],
  { intros [ident x, ident hx],
    rcases [expr multiset.mem_add.1 hx, "with", ident hx, "|", ident hx]; exact [expr irreducible_of_normalized_factor x hx] },
  { exact [expr irreducible_of_normalized_factor] },
  { rw [expr multiset.prod_add] [],
    exact [expr ((normalized_factors_prod hx).mul_mul (normalized_factors_prod hy)).trans (normalized_factors_prod (mul_ne_zero hx hy)).symm] }
end

@[simp]
theorem normalized_factors_pow {x : α} (n : ℕ) : normalized_factors (x^n) = n • normalized_factors x :=
  by 
    induction' n with n ih
    ·
      simp 
    byCases' h0 : x = 0
    ·
      simp [h0, zero_pow n.succ_pos, smul_zero]
    rw [pow_succₓ, succ_nsmul, normalized_factors_mul h0 (pow_ne_zero _ h0), ih]

theorem dvd_iff_normalized_factors_le_normalized_factors {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
  x ∣ y ↔ normalized_factors x ≤ normalized_factors y :=
  by 
    split 
    ·
      rintro ⟨c, rfl⟩
      simp [hx, right_ne_zero_of_mul hy]
    ·
      rw [←(normalized_factors_prod hx).dvd_iff_dvd_left, ←(normalized_factors_prod hy).dvd_iff_dvd_right]
      apply Multiset.prod_dvd_prod

theorem zero_not_mem_normalized_factors (x : α) : (0 : α) ∉ normalized_factors x :=
  fun h => Prime.ne_zero (prime_of_normalized_factor _ h) rfl

theorem dvd_of_mem_normalized_factors {a p : α} (H : p ∈ normalized_factors a) : p ∣ a :=
  by 
    byCases' hcases : a = 0
    ·
      rw [hcases]
      exact dvd_zero p
    ·
      exact dvd_trans (Multiset.dvd_prod H) (Associated.dvd (normalized_factors_prod hcases))

end UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

open_locale Classical

open Multiset Associates

noncomputable theory

variable[CommCancelMonoidWithZero α][Nontrivial α][UniqueFactorizationMonoid α]

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Noncomputably defines a `normalization_monoid` structure on a `unique_factorization_monoid`. -/
protected
def normalization_monoid : normalization_monoid α :=
normalization_monoid_of_monoid_hom_right_inverse { to_fun := λ
  a : associates α, if «expr = »(a, 0) then 0 else ((normalized_factors a).map (classical.some mk_surjective.has_right_inverse : associates α → α)).prod,
  map_one' := by simp [] [] [] [] [] [],
  map_mul' := λ x y, by { by_cases [expr hx, ":", expr «expr = »(x, 0)],
    { simp [] [] [] ["[", expr hx, "]"] [] [] },
    by_cases [expr hy, ":", expr «expr = »(y, 0)],
    { simp [] [] [] ["[", expr hy, "]"] [] [] },
    simp [] [] [] ["[", expr hx, ",", expr hy, "]"] [] [] } } (begin
   intro [ident x],
   dsimp [] [] [] [],
   by_cases [expr hx, ":", expr «expr = »(x, 0)],
   { simp [] [] [] ["[", expr hx, "]"] [] [] },
   have [ident h] [":", expr «expr = »(«expr ∘ »(associates.mk_monoid_hom, classical.some mk_surjective.has_right_inverse), (id : associates α → associates α))] [],
   { ext [] [ident x] [],
     rw ["[", expr function.comp_apply, ",", expr mk_monoid_hom_apply, ",", expr classical.some_spec mk_surjective.has_right_inverse x, "]"] [],
     refl },
   rw ["[", expr if_neg hx, ",", "<-", expr mk_monoid_hom_apply, ",", expr monoid_hom.map_multiset_prod, ",", expr map_map, ",", expr h, ",", expr map_id, ",", "<-", expr associated_iff_eq, "]"] [],
   apply [expr normalized_factors_prod hx]
 end)

instance  : Inhabited (NormalizationMonoid α) :=
  ⟨UniqueFactorizationMonoid.normalizationMonoid⟩

end UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

variable{R : Type _}[CommCancelMonoidWithZero R][UniqueFactorizationMonoid R]

theorem no_factors_of_no_prime_factors {a b : R} (ha : a ≠ 0) (h : ∀ {d}, d ∣ a → d ∣ b → ¬Prime d) :
  ∀ {d}, d ∣ a → d ∣ b → IsUnit d :=
  fun d =>
    induction_on_prime d
      (by 
        simp only [zero_dvd_iff]
        intros 
        contradiction)
      (fun x hx _ _ => hx)
      fun d q hp hq ih dvd_a dvd_b => absurd hq (h (dvd_of_mul_right_dvd dvd_a) (dvd_of_mul_right_dvd dvd_b))

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Euclid's lemma: if `a ∣ b * c` and `a` and `c` have no common prime factors, `a ∣ b`.
Compare `is_coprime.dvd_of_dvd_mul_left`. -/
theorem dvd_of_dvd_mul_left_of_no_prime_factors
{a b c : R}
(ha : «expr ≠ »(a, 0)) : ∀
{d}, «expr ∣ »(d, a) → «expr ∣ »(d, c) → «expr¬ »(prime d) → «expr ∣ »(a, «expr * »(b, c)) → «expr ∣ »(a, b) :=
begin
  refine [expr induction_on_prime c _ _ _],
  { intro [ident no_factors],
    simp [] [] ["only"] ["[", expr dvd_zero, ",", expr mul_zero, ",", expr forall_prop_of_true, "]"] [] [],
    haveI [] [] [":=", expr classical.prop_decidable],
    exact [expr is_unit_iff_forall_dvd.mp (no_factors_of_no_prime_factors ha @no_factors (dvd_refl a) (dvd_zero a)) _] },
  { rintros ["_", "⟨", ident x, ",", ident rfl, "⟩", "_", ident a_dvd_bx],
    apply [expr units.dvd_mul_right.mp a_dvd_bx] },
  { intros [ident c, ident p, ident hc, ident hp, ident ih, ident no_factors, ident a_dvd_bpc],
    apply [expr ih (λ q dvd_a dvd_c hq, no_factors dvd_a (dvd_c.mul_left _) hq)],
    rw [expr mul_left_comm] ["at", ident a_dvd_bpc],
    refine [expr or.resolve_left (hp.left_dvd_or_dvd_right_of_dvd_mul a_dvd_bpc) (λ h, _)],
    exact [expr no_factors h (dvd_mul_right p c) hp] }
end

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `b` have no common prime factors, `a ∣ c`.
Compare `is_coprime.dvd_of_dvd_mul_right`. -/
theorem dvd_of_dvd_mul_right_of_no_prime_factors {a b c : R} (ha : a ≠ 0)
  (no_factors : ∀ {d}, d ∣ a → d ∣ b → ¬Prime d) : (a ∣ b*c) → a ∣ c :=
  by 
    simpa [mul_commₓ b c] using dvd_of_dvd_mul_left_of_no_prime_factors ha @no_factors

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `a ≠ 0, b` are elements of a unique factorization domain, then dividing
out their common factor `c'` gives `a'` and `b'` with no factors in common. -/
theorem exists_reduced_factors : ∀
(a «expr ≠ » (0 : R))
(b), «expr∃ , »((a'
  b'
  c'), «expr ∧ »(∀
  {d}, «expr ∣ »(d, a') → «expr ∣ »(d, b') → is_unit d, «expr ∧ »(«expr = »(«expr * »(c', a'), a), «expr = »(«expr * »(c', b'), b)))) :=
begin
  haveI [] [] [":=", expr classical.prop_decidable],
  intros [ident a],
  refine [expr induction_on_prime a _ _ _],
  { intros [],
    contradiction },
  { intros [ident a, ident a_unit, ident a_ne_zero, ident b],
    use ["[", expr a, ",", expr b, ",", expr 1, "]"],
    split,
    { intros [ident p, ident p_dvd_a, "_"],
      exact [expr is_unit_of_dvd_unit p_dvd_a a_unit] },
    { simp [] [] [] [] [] [] } },
  { intros [ident a, ident p, ident a_ne_zero, ident p_prime, ident ih_a, ident pa_ne_zero, ident b],
    by_cases [expr «expr ∣ »(p, b)],
    { rcases [expr h, "with", "⟨", ident b, ",", ident rfl, "⟩"],
      obtain ["⟨", ident a', ",", ident b', ",", ident c', ",", ident no_factor, ",", ident ha', ",", ident hb', "⟩", ":=", expr ih_a a_ne_zero b],
      refine [expr ⟨a', b', «expr * »(p, c'), @no_factor, _, _⟩],
      { rw ["[", expr mul_assoc, ",", expr ha', "]"] [] },
      { rw ["[", expr mul_assoc, ",", expr hb', "]"] [] } },
    { obtain ["⟨", ident a', ",", ident b', ",", ident c', ",", ident coprime, ",", ident rfl, ",", ident rfl, "⟩", ":=", expr ih_a a_ne_zero b],
      refine [expr ⟨«expr * »(p, a'), b', c', _, mul_left_comm _ _ _, rfl⟩],
      intros [ident q, ident q_dvd_pa', ident q_dvd_b'],
      cases [expr p_prime.left_dvd_or_dvd_right_of_dvd_mul q_dvd_pa'] ["with", ident p_dvd_q, ident q_dvd_a'],
      { have [] [":", expr «expr ∣ »(p, «expr * »(c', b'))] [":=", expr dvd_mul_of_dvd_right (p_dvd_q.trans q_dvd_b') _],
        contradiction },
      exact [expr coprime q_dvd_a' q_dvd_b'] } }
end

theorem exists_reduced_factors' (a b : R) (hb : b ≠ 0) :
  ∃ a' b' c', (∀ {d}, d ∣ a' → d ∣ b' → IsUnit d) ∧ (c'*a') = a ∧ (c'*b') = b :=
  let ⟨b', a', c', no_factor, hb, ha⟩ := exists_reduced_factors b hb a
  ⟨a', b', c', fun _ hpb hpa => no_factor hpa hpb, ha, hb⟩

section multiplicity

variable[Nontrivial R][NormalizationMonoid R][DecidableEq R]

variable[DecidableRel (HasDvd.Dvd : R → R → Prop)]

open multiplicity Multiset

theorem le_multiplicity_iff_repeat_le_normalized_factors {a b : R} {n : ℕ} (ha : Irreducible a) (hb : b ≠ 0) :
  «expr↑ » n ≤ multiplicity a b ↔ repeat (normalize a) n ≤ normalized_factors b :=
  by 
    rw [←pow_dvd_iff_le_multiplicity]
    revert b 
    induction' n with n ih
    ·
      simp 
    intro b hb 
    split 
    ·
      rintro ⟨c, rfl⟩
      rw [Ne.def, pow_succₓ, mul_assocₓ, mul_eq_zero, Decidable.not_or_iff_and_not] at hb 
      rw [pow_succₓ, mul_assocₓ, normalized_factors_mul hb.1 hb.2, repeat_succ, normalized_factors_irreducible ha,
        singleton_add, cons_le_cons_iff, ←ih hb.2]
      apply Dvd.intro _ rfl
    ·
      rw [Multiset.le_iff_exists_add]
      rintro ⟨u, hu⟩
      rw [←(normalized_factors_prod hb).dvd_iff_dvd_right, hu, prod_add, prod_repeat]
      exact (Associated.pow_pow$ associated_normalize a).Dvd.trans (Dvd.intro u.prod rfl)

theorem multiplicity_eq_count_normalized_factors {a b : R} (ha : Irreducible a) (hb : b ≠ 0) :
  multiplicity a b = (normalized_factors b).count (normalize a) :=
  by 
    apply le_antisymmₓ
    ·
      apply Enat.le_of_lt_add_one 
      rw [←Nat.cast_one, ←Nat.cast_add, lt_iff_not_geₓ, ge_iff_le,
        le_multiplicity_iff_repeat_le_normalized_factors ha hb, ←le_count_iff_repeat_le]
      simp 
    rw [le_multiplicity_iff_repeat_le_normalized_factors ha hb, ←le_count_iff_repeat_le]

end multiplicity

end UniqueFactorizationMonoid

namespace Associates

open UniqueFactorizationMonoid Associated Multiset

variable[CommCancelMonoidWithZero α]

/-- `factor_set α` representation elements of unique factorization domain as multisets.
`multiset α` produced by `normalized_factors` are only unique up to associated elements, while the
multisets in `factor_set α` are unique by equality and restricted to irreducible elements. This
gives us a representation of each element as a unique multisets (or the added ⊤ for 0), which has a
complete lattice struture. Infimum is the greatest common divisor and supremum is the least common
multiple.
-/
@[reducible]
def factor_set.{u} (α : Type u) [CommCancelMonoidWithZero α] : Type u :=
  WithTop (Multiset { a : Associates α // Irreducible a })

attribute [local instance] Associated.setoid

theorem factor_set.coe_add {a b : Multiset { a : Associates α // Irreducible a }} :
  («expr↑ » (a+b) : factor_set α) = a+b :=
  by 
    normCast

theorem factor_set.sup_add_inf_eq_add [DecidableEq (Associates α)] : ∀ a b : factor_set α, ((a⊔b)+a⊓b) = a+b
| none, b =>
  show ((⊤⊔b)+⊤⊓b) = ⊤+b by 
    simp 
| a, none =>
  show ((a⊔⊤)+a⊓⊤) = a+⊤by 
    simp 
| some a, some b =>
  show (((a : factor_set α)⊔b)+a⊓b) = a+b from
    by 
      rw [←WithTop.coe_sup, ←WithTop.coe_inf, ←WithTop.coe_add, ←WithTop.coe_add, WithTop.coe_eq_coe]
      exact Multiset.union_add_inter _ _

/-- Evaluates the product of a `factor_set` to be the product of the corresponding multiset,
  or `0` if there is none. -/
def factor_set.prod : factor_set α → Associates α
| none => 0
| some s => (s.map coeₓ).Prod

@[simp]
theorem prod_top : (⊤ : factor_set α).Prod = 0 :=
  rfl

@[simp]
theorem prod_coe {s : Multiset { a : Associates α // Irreducible a }} : (s : factor_set α).Prod = (s.map coeₓ).Prod :=
  rfl

@[simp]
theorem prod_add : ∀ a b : factor_set α, (a+b).Prod = a.prod*b.prod
| none, b =>
  show (⊤+b).Prod = (⊤ : factor_set α).Prod*b.prod by 
    simp 
| a, none =>
  show (a+⊤).Prod = a.prod*(⊤ : factor_set α).Prod by 
    simp 
| some a, some b =>
  show
    («expr↑ » a+«expr↑ » b : factor_set α).Prod = («expr↑ » a : factor_set α).Prod*(«expr↑ » b : factor_set α).Prod by 
    rw [←factor_set.coe_add, prod_coe, prod_coe, prod_coe, Multiset.map_add, Multiset.prod_add]

theorem prod_mono : ∀ {a b : factor_set α}, a ≤ b → a.prod ≤ b.prod
| none, b, h =>
  have  : b = ⊤ := top_unique h 
  by 
    rw [this, prod_top] <;> exact le_reflₓ _
| a, none, h =>
  show a.prod ≤ (⊤ : factor_set α).Prod by 
    simp  <;> exact le_top
| some a, some b, h => prod_le_prod$ Multiset.map_le_map$ WithTop.coe_le_coe.1$ h

theorem factor_set.prod_eq_zero_iff [Nontrivial α] (p : factor_set α) : p.prod = 0 ↔ p = ⊤ :=
  by 
    induction p using WithTop.recTopCoe
    ·
      simp only [iff_selfₓ, eq_self_iff_true, Associates.prod_top]
    simp only [prod_coe, WithTop.coe_ne_top, iff_falseₓ, prod_eq_zero_iff, Multiset.mem_map]
    rintro ⟨⟨a, ha⟩, -, eq⟩
    rw [Subtype.coe_mk] at eq 
    exact ha.ne_zero Eq

/-- `bcount p s` is the multiplicity of `p` in the factor_set `s` (with bundled `p`)-/
def bcount [DecidableEq (Associates α)] (p : { a : Associates α // Irreducible a }) : factor_set α → ℕ
| none => 0
| some s => s.count p

variable[dec_irr : ∀ p : Associates α, Decidable (Irreducible p)]

include dec_irr

/-- `count p s` is the multiplicity of the irreducible `p` in the factor_set `s`.

If `p` is not irreducible, `count p s` is defined to be `0`. -/
def count [DecidableEq (Associates α)] (p : Associates α) : factor_set α → ℕ :=
  if hp : Irreducible p then bcount ⟨p, hp⟩ else 0

@[simp]
theorem count_some [DecidableEq (Associates α)] {p : Associates α} (hp : Irreducible p) (s : Multiset _) :
  count p (some s) = s.count ⟨p, hp⟩ :=
  by 
    dunfold count 
    splitIfs 
    rfl

@[simp]
theorem count_zero [DecidableEq (Associates α)] {p : Associates α} (hp : Irreducible p) :
  count p (0 : factor_set α) = 0 :=
  by 
    dunfold count 
    splitIfs 
    rfl

theorem count_reducible [DecidableEq (Associates α)] {p : Associates α} (hp : ¬Irreducible p) : count p = 0 :=
  dif_neg hp

omit dec_irr

/-- membership in a factor_set (bundled version) -/
def bfactor_set_mem : { a : Associates α // Irreducible a } → factor_set α → Prop
| _, ⊤ => True
| p, some l => p ∈ l

include dec_irr

/-- `factor_set_mem p s` is the predicate that the irreducible `p` is a member of
`s : factor_set α`.

If `p` is not irreducible, `p` is not a member of any `factor_set`. -/
def factor_set_mem (p : Associates α) (s : factor_set α) : Prop :=
  if hp : Irreducible p then bfactor_set_mem ⟨p, hp⟩ s else False

instance  : HasMem (Associates α) (factor_set α) :=
  ⟨factor_set_mem⟩

@[simp]
theorem factor_set_mem_eq_mem (p : Associates α) (s : factor_set α) : factor_set_mem p s = (p ∈ s) :=
  rfl

theorem mem_factor_set_top {p : Associates α} {hp : Irreducible p} : p ∈ (⊤ : factor_set α) :=
  by 
    dunfold HasMem.Mem 
    dunfold factor_set_mem 
    splitIfs 
    exact trivialₓ

theorem mem_factor_set_some {p : Associates α} {hp : Irreducible p}
  {l : Multiset { a : Associates α // Irreducible a }} : p ∈ (l : factor_set α) ↔ Subtype.mk p hp ∈ l :=
  by 
    dunfold HasMem.Mem 
    dunfold factor_set_mem 
    splitIfs 
    rfl

theorem reducible_not_mem_factor_set {p : Associates α} (hp : ¬Irreducible p) (s : factor_set α) : ¬p ∈ s :=
  fun h : if hp : Irreducible p then bfactor_set_mem ⟨p, hp⟩ s else False =>
    by 
      rwa [dif_neg hp] at h

omit dec_irr

variable[UniqueFactorizationMonoid α]

theorem unique' {p q : Multiset (Associates α)} :
  (∀ a _ : a ∈ p, Irreducible a) → (∀ a _ : a ∈ q, Irreducible a) → p.prod = q.prod → p = q :=
  by 
    apply Multiset.induction_on_multiset_quot p 
    apply Multiset.induction_on_multiset_quot q 
    intro s t hs ht eq 
    refine' Multiset.map_mk_eq_map_mk_of_rel (UniqueFactorizationMonoid.factors_unique _ _ _)
    ·
      exact fun a ha => (irreducible_mk _).1$ hs _$ Multiset.mem_map_of_mem _ ha
    ·
      exact fun a ha => (irreducible_mk _).1$ ht _$ Multiset.mem_map_of_mem _ ha 
    simpa [quot_mk_eq_mk, prod_mk, mk_eq_mk_iff_associated] using Eq

theorem factor_set.unique [Nontrivial α] {p q : factor_set α} (h : p.prod = q.prod) : p = q :=
  by 
    induction p using WithTop.recTopCoe <;> induction q using WithTop.recTopCoe
    ·
      rfl
    ·
      rw [eq_comm, ←factor_set.prod_eq_zero_iff, ←h, Associates.prod_top]
    ·
      rw [←factor_set.prod_eq_zero_iff, h, Associates.prod_top]
    ·
      congr 1
      rw [←Multiset.map_eq_map Subtype.coe_injective]
      apply unique' _ _ h <;>
        ·
          intro a ha 
          obtain ⟨⟨a', irred⟩, -, rfl⟩ := multiset.mem_map.mp ha 
          rwa [Subtype.coe_mk]

theorem prod_le_prod_iff_le [Nontrivial α] {p q : Multiset (Associates α)} (hp : ∀ a _ : a ∈ p, Irreducible a)
  (hq : ∀ a _ : a ∈ q, Irreducible a) : p.prod ≤ q.prod ↔ p ≤ q :=
  Iff.intro
    (by 
      classical 
      rintro ⟨c, eqc⟩
      refine' Multiset.le_iff_exists_add.2 ⟨factors c, unique' hq (fun x hx => _) _⟩
      ·
        obtain h | h := Multiset.mem_add.1 hx
        ·
          exact hp x h
        ·
          exact irreducible_of_factor _ h
      ·
        rw [eqc, Multiset.prod_add]
        congr 
        refine' associated_iff_eq.mp (factors_prod fun hc => _).symm 
        refine' not_irreducible_zero (hq _ _)
        rw [←prod_eq_zero_iff, eqc, hc, mul_zero])
    prod_le_prod

variable[dec : DecidableEq α][dec' : DecidableEq (Associates α)]

include dec

/-- This returns the multiset of irreducible factors as a `factor_set`,
  a multiset of irreducible associates `with_top`. -/
noncomputable def factors' (a : α) : Multiset { a : Associates α // Irreducible a } :=
  (factors a).pmap (fun a ha => ⟨Associates.mk a, (irreducible_mk _).2 ha⟩) irreducible_of_factor

@[simp]
theorem map_subtype_coe_factors' {a : α} : (factors' a).map coeₓ = (factors a).map Associates.mk :=
  by 
    simp [factors', Multiset.map_pmap, Multiset.pmap_eq_map]

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem factors'_cong {a b : α} (h : «expr ~ᵤ »(a, b)) : «expr = »(factors' a, factors' b) :=
begin
  obtain [ident rfl, "|", ident hb, ":=", expr eq_or_ne b 0],
  { rw [expr associated_zero_iff_eq_zero] ["at", ident h],
    rw [expr h] [] },
  have [ident ha] [":", expr «expr ≠ »(a, 0)] [],
  { contrapose ["!"] [ident hb, "with", ident ha],
    rw ["[", "<-", expr associated_zero_iff_eq_zero, ",", "<-", expr ha, "]"] [],
    exact [expr h.symm] },
  rw ["[", "<-", expr multiset.map_eq_map subtype.coe_injective, ",", expr map_subtype_coe_factors', ",", expr map_subtype_coe_factors', ",", "<-", expr rel_associated_iff_map_eq_map, "]"] [],
  exact [expr factors_unique irreducible_of_factor irreducible_of_factor «expr $ »((factors_prod ha).trans, «expr $ »(h.trans, (factors_prod hb).symm))]
end

include dec'

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- This returns the multiset of irreducible factors of an associate as a `factor_set`,
  a multiset of irreducible associates `with_top`. -/ noncomputable def factors (a : associates α) : factor_set α :=
begin
  refine [expr if h : «expr = »(a, 0) then «expr⊤»() else quotient.hrec_on a (λ x h, «expr $ »(some, factors' x)) _ h],
  assume [binders (a b hab)],
  apply [expr function.hfunext],
  { have [] [":", expr «expr ↔ »(«expr ~ᵤ »(a, 0), «expr ~ᵤ »(b, 0))] [],
    from [expr iff.intro (assume ha0, hab.symm.trans ha0) (assume hb0, hab.trans hb0)],
    simp [] [] ["only"] ["[", expr associated_zero_iff_eq_zero, "]"] [] ["at", ident this],
    simp [] [] ["only"] ["[", expr quotient_mk_eq_mk, ",", expr this, ",", expr mk_eq_zero, "]"] [] [] },
  exact [expr assume ha hb eq, «expr $ »(heq_of_eq, «expr $ »(congr_arg some, factors'_cong hab))]
end

@[simp]
theorem factors_0 : (0 : Associates α).factors = ⊤ :=
  dif_pos rfl

@[simp]
theorem factors_mk (a : α) (h : a ≠ 0) : (Associates.mk a).factors = factors' a :=
  by 
    classical 
    apply dif_neg 
    apply mt mk_eq_zero.1 h

@[simp]
theorem factors_prod (a : Associates α) : a.factors.prod = a :=
  Quotientₓ.induction_on a$
    fun a =>
      Decidable.byCases
        (fun this : Associates.mk a = 0 =>
          by 
            simp [quotient_mk_eq_mk, this])
        fun this : Associates.mk a ≠ 0 =>
          have  : a ≠ 0 :=
            by 
              simp_all 
          by 
            simp [this, quotient_mk_eq_mk, prod_mk, mk_eq_mk_iff_associated.2 (factors_prod this)]

theorem prod_factors [Nontrivial α] (s : factor_set α) : s.prod.factors = s :=
  factor_set.unique$ factors_prod _

theorem eq_of_factors_eq_factors {a b : Associates α} (h : a.factors = b.factors) : a = b :=
  have  : a.factors.prod = b.factors.prod :=
    by 
      rw [h]
  by 
    rwa [factors_prod, factors_prod] at this

omit dec dec'

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_of_prod_eq_prod [nontrivial α] {a b : factor_set α} (h : «expr = »(a.prod, b.prod)) : «expr = »(a, b) :=
begin
  classical,
  have [] [":", expr «expr = »(a.prod.factors, b.prod.factors)] [],
  by rw [expr h] [],
  rwa ["[", expr prod_factors, ",", expr prod_factors, "]"] ["at", ident this]
end

include dec dec'

@[simp]
theorem factors_mul [Nontrivial α] (a b : Associates α) : (a*b).factors = a.factors+b.factors :=
  eq_of_prod_eq_prod$
    eq_of_factors_eq_factors$
      by 
        rw [prod_add, factors_prod, factors_prod, factors_prod]

theorem factors_mono [Nontrivial α] : ∀ {a b : Associates α}, a ≤ b → a.factors ≤ b.factors
| s, t, ⟨d, rfl⟩ =>
  by 
    rw [factors_mul] <;> exact le_add_of_nonneg_right bot_le

theorem factors_le [Nontrivial α] {a b : Associates α} : a.factors ≤ b.factors ↔ a ≤ b :=
  Iff.intro
    (fun h =>
      have  : a.factors.prod ≤ b.factors.prod := prod_mono h 
      by 
        rwa [factors_prod, factors_prod] at this)
    factors_mono

omit dec dec'

theorem prod_le [Nontrivial α] {a b : factor_set α} : a.prod ≤ b.prod ↔ a ≤ b :=
  by 
    classical 
    exact
      Iff.intro
        (fun h =>
          have  : a.prod.factors ≤ b.prod.factors := factors_mono h 
          by 
            rwa [prod_factors, prod_factors] at this)
        prod_mono

include dec dec'

noncomputable instance  : HasSup (Associates α) :=
  ⟨fun a b => (a.factors⊔b.factors).Prod⟩

noncomputable instance  : HasInf (Associates α) :=
  ⟨fun a b => (a.factors⊓b.factors).Prod⟩

noncomputable instance  [Nontrivial α] : BoundedLattice (Associates α) :=
  { Associates.partialOrder, Associates.orderTop, Associates.orderBot with sup := ·⊔·, inf := ·⊓·,
    sup_le := fun a b c hac hbc => factors_prod c ▸ prod_mono (sup_le (factors_mono hac) (factors_mono hbc)),
    le_sup_left := fun a b => le_transₓ (le_of_eqₓ (factors_prod a).symm)$ prod_mono$ le_sup_left,
    le_sup_right := fun a b => le_transₓ (le_of_eqₓ (factors_prod b).symm)$ prod_mono$ le_sup_right,
    le_inf := fun a b c hac hbc => factors_prod a ▸ prod_mono (le_inf (factors_mono hac) (factors_mono hbc)),
    inf_le_left := fun a b => le_transₓ (prod_mono inf_le_left) (le_of_eqₓ (factors_prod a)),
    inf_le_right := fun a b => le_transₓ (prod_mono inf_le_right) (le_of_eqₓ (factors_prod b)) }

theorem sup_mul_inf [Nontrivial α] (a b : Associates α) : ((a⊔b)*a⊓b) = a*b :=
  show ((a.factors⊔b.factors).Prod*(a.factors⊓b.factors).Prod) = a*b by 
    refine' eq_of_factors_eq_factors _ 
    rw [←prod_add, prod_factors, factors_mul, factor_set.sup_add_inf_eq_add]

include dec_irr

theorem dvd_of_mem_factors {a p : Associates α} {hp : Irreducible p} (hm : p ∈ factors a) : p ∣ a :=
  by 
    byCases' ha0 : a = 0
    ·
      rw [ha0]
      exact dvd_zero p 
    obtain ⟨a0, nza, ha'⟩ := exists_non_zero_rep ha0 
    rw [←Associates.factors_prod a]
    rw [←ha', factors_mk a0 nza] at hm⊢
    erw [prod_coe]
    apply Multiset.dvd_prod 
    apply multiset.mem_map.mpr 
    exact ⟨⟨p, hp⟩, mem_factor_set_some.mp hm, rfl⟩

omit dec'

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dvd_of_mem_factors'
{a : α}
{p : associates α}
{hp : irreducible p}
{hz : «expr ≠ »(a, 0)}
(h_mem : «expr ∈ »(subtype.mk p hp, factors' a)) : «expr ∣ »(p, associates.mk a) :=
by { haveI [] [] [":=", expr classical.dec_eq (associates α)],
  apply [expr @dvd_of_mem_factors _ _ _ _ _ _ _ _ hp],
  rw [expr factors_mk _ hz] [],
  apply [expr mem_factor_set_some.2 h_mem] }

omit dec_irr

theorem mem_factors'_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) (hd : p ∣ a) :
  Subtype.mk (Associates.mk p) ((irreducible_mk _).2 hp) ∈ factors' a :=
  by 
    obtain ⟨q, hq, hpq⟩ := exists_mem_factors_of_dvd ha0 hp hd 
    apply multiset.mem_pmap.mpr 
    use q 
    use hq 
    exact Subtype.eq (Eq.symm (mk_eq_mk_iff_associated.mpr hpq))

include dec_irr

theorem mem_factors'_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
  Subtype.mk (Associates.mk p) ((irreducible_mk _).2 hp) ∈ factors' a ↔ p ∣ a :=
  by 
    split 
    ·
      rw [←mk_dvd_mk]
      apply dvd_of_mem_factors' 
      apply ha0
    ·
      apply mem_factors'_of_dvd ha0

include dec'

theorem mem_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) (hd : p ∣ a) :
  Associates.mk p ∈ factors (Associates.mk a) :=
  by 
    rw [factors_mk _ ha0]
    exact mem_factor_set_some.mpr (mem_factors'_of_dvd ha0 hp hd)

theorem mem_factors_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
  Associates.mk p ∈ factors (Associates.mk a) ↔ p ∣ a :=
  by 
    split 
    ·
      rw [←mk_dvd_mk]
      apply dvd_of_mem_factors 
      exact (irreducible_mk p).mpr hp
    ·
      apply mem_factors_of_dvd ha0 hp

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_prime_dvd_of_not_inf_one
{a b : α}
(ha : «expr ≠ »(a, 0))
(hb : «expr ≠ »(b, 0))
(h : «expr ≠ »(«expr ⊓ »(associates.mk a, associates.mk b), 1)) : «expr∃ , »((p : α), «expr ∧ »(prime p, «expr ∧ »(«expr ∣ »(p, a), «expr ∣ »(p, b)))) :=
begin
  have [ident hz] [":", expr «expr ≠ »(«expr ⊓ »(factors (associates.mk a), factors (associates.mk b)), 0)] [],
  { contrapose ["!"] [ident h, "with", ident hf],
    change [expr «expr = »(«expr ⊓ »(factors (associates.mk a), factors (associates.mk b)).prod, 1)] [] [],
    rw [expr hf] [],
    exact [expr multiset.prod_zero] },
  rw ["[", expr factors_mk a ha, ",", expr factors_mk b hb, ",", "<-", expr with_top.coe_inf, "]"] ["at", ident hz],
  obtain ["⟨", "⟨", ident p0, ",", ident p0_irr, "⟩", ",", ident p0_mem, "⟩", ":=", expr multiset.exists_mem_of_ne_zero (mt with_top.coe_eq_coe.mpr hz)],
  rw [expr multiset.inf_eq_inter] ["at", ident p0_mem],
  obtain ["⟨", ident p, ",", ident rfl, "⟩", ":", expr «expr∃ , »((p), «expr = »(associates.mk p, p0)), ":=", expr quot.exists_rep p0],
  refine [expr ⟨p, _, _, _⟩],
  { rw ["[", "<-", expr irreducible_iff_prime, ",", "<-", expr irreducible_mk, "]"] [],
    exact [expr p0_irr] },
  { apply [expr dvd_of_mk_le_mk],
    apply [expr dvd_of_mem_factors' (multiset.mem_inter.mp p0_mem).left],
    apply [expr ha] },
  { apply [expr dvd_of_mk_le_mk],
    apply [expr dvd_of_mem_factors' (multiset.mem_inter.mp p0_mem).right],
    apply [expr hb] }
end

theorem coprime_iff_inf_one [Nontrivial α] {a b : α} (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
  Associates.mk a⊓Associates.mk b = 1 ↔ ∀ {d : α}, d ∣ a → d ∣ b → ¬Prime d :=
  by 
    split 
    ·
      intro hg p ha hb hp 
      refine' ((Associates.prime_mk _).mpr hp).not_unit (is_unit_of_dvd_one _ _)
      rw [←hg]
      exact le_inf (mk_le_mk_of_dvd ha) (mk_le_mk_of_dvd hb)
    ·
      contrapose 
      intro hg hc 
      obtain ⟨p, hp, hpa, hpb⟩ := exists_prime_dvd_of_not_inf_one ha0 hb0 hg 
      exact hc hpa hpb hp

omit dec_irr

theorem factors_prime_pow [Nontrivial α] {p : Associates α} (hp : Irreducible p) (k : ℕ) :
  factors (p^k) = some (Multiset.repeat ⟨p, hp⟩ k) :=
  eq_of_prod_eq_prod
    (by 
      rw [Associates.factors_prod, factor_set.prod, Multiset.map_repeat, Multiset.prod_repeat, Subtype.coe_mk])

include dec_irr

theorem prime_pow_dvd_iff_le [Nontrivial α] {m p : Associates α} (h₁ : m ≠ 0) (h₂ : Irreducible p) {k : ℕ} :
  (p^k) ≤ m ↔ k ≤ count p m.factors :=
  by 
    obtain ⟨a, nz, rfl⟩ := Associates.exists_non_zero_rep h₁ 
    rw [factors_mk _ nz, ←WithTop.some_eq_coe, count_some, Multiset.le_count_iff_repeat_le, ←factors_le,
      factors_prime_pow h₂, factors_mk _ nz]
    exact WithTop.coe_le_coe

theorem le_of_count_ne_zero [Nontrivial α] {m p : Associates α} (h0 : m ≠ 0) (hp : Irreducible p) :
  count p m.factors ≠ 0 → p ≤ m :=
  by 
    rw [←pos_iff_ne_zero]
    intro h 
    rw [←pow_oneₓ p]
    apply (prime_pow_dvd_iff_le h0 hp).2
    simpa only

theorem count_mul [Nontrivial α] {a : Associates α} (ha : a ≠ 0) {b : Associates α} (hb : b ≠ 0) {p : Associates α}
  (hp : Irreducible p) : count p (factors (a*b)) = count p a.factors+count p b.factors :=
  by 
    obtain ⟨a0, nza, ha'⟩ := exists_non_zero_rep ha 
    obtain ⟨b0, nzb, hb'⟩ := exists_non_zero_rep hb 
    rw [factors_mul, ←ha', ←hb', factors_mk a0 nza, factors_mk b0 nzb, ←factor_set.coe_add, ←WithTop.some_eq_coe,
      ←WithTop.some_eq_coe, ←WithTop.some_eq_coe, count_some hp, Multiset.count_add, count_some hp, count_some hp]

theorem count_of_coprime [Nontrivial α] {a : Associates α} (ha : a ≠ 0) {b : Associates α} (hb : b ≠ 0)
  (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) {p : Associates α} (hp : Irreducible p) :
  count p a.factors = 0 ∨ count p b.factors = 0 :=
  by 
    rw [or_iff_not_imp_left, ←Ne.def]
    intro hca 
    contrapose! hab with hcb 
    exact ⟨p, le_of_count_ne_zero ha hp hca, le_of_count_ne_zero hb hp hcb, irreducible_iff_prime.mp hp⟩

theorem count_mul_of_coprime [Nontrivial α] {a : Associates α} (ha : a ≠ 0) {b : Associates α} (hb : b ≠ 0)
  {p : Associates α} (hp : Irreducible p) (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) :
  count p a.factors = 0 ∨ count p a.factors = count p (a*b).factors :=
  by 
    cases' count_of_coprime ha hb hab hp with hz hb0
    ·
      tauto 
    apply Or.intro_rightₓ 
    rw [count_mul ha hb hp, hb0, add_zeroₓ]

theorem count_mul_of_coprime' [Nontrivial α] {a : Associates α} (ha : a ≠ 0) {b : Associates α} (hb : b ≠ 0)
  {p : Associates α} (hp : Irreducible p) (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) :
  count p (a*b).factors = count p a.factors ∨ count p (a*b).factors = count p b.factors :=
  by 
    rw [count_mul ha hb hp]
    cases' count_of_coprime ha hb hab hp with ha0 hb0
    ·
      apply Or.intro_rightₓ 
      rw [ha0, zero_addₓ]
    ·
      apply Or.intro_left 
      rw [hb0, add_zeroₓ]

theorem dvd_count_of_dvd_count_mul [Nontrivial α] {a b : Associates α} (ha : a ≠ 0) (hb : b ≠ 0) {p : Associates α}
  (hp : Irreducible p) (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) {k : ℕ} (habk : k ∣ count p (a*b).factors) :
  k ∣ count p a.factors :=
  by 
    cases' count_of_coprime ha hb hab hp with hz h
    ·
      rw [hz]
      exact dvd_zero k
    ·
      rw [count_mul ha hb hp, h] at habk 
      exact habk

omit dec_irr

@[simp]
theorem factors_one [Nontrivial α] : factors (1 : Associates α) = 0 :=
  by 
    apply eq_of_prod_eq_prod 
    rw [Associates.factors_prod]
    exact Multiset.prod_zero

@[simp]
theorem pow_factors [Nontrivial α] {a : Associates α} {k : ℕ} : (a^k).factors = k • a.factors :=
  by 
    induction' k with n h
    ·
      rw [zero_nsmul, pow_zeroₓ]
      exact factors_one
    ·
      rw [pow_succₓ, succ_nsmul, factors_mul, h]

include dec_irr

theorem count_pow [Nontrivial α] {a : Associates α} (ha : a ≠ 0) {p : Associates α} (hp : Irreducible p) (k : ℕ) :
  count p (a^k).factors = k*count p a.factors :=
  by 
    induction' k with n h
    ·
      rw [pow_zeroₓ, factors_one, zero_mul, count_zero hp]
    ·
      rw [pow_succₓ, count_mul ha (pow_ne_zero _ ha) hp, h, Nat.succ_eq_add_one]
      ring

theorem dvd_count_pow [Nontrivial α] {a : Associates α} (ha : a ≠ 0) {p : Associates α} (hp : Irreducible p) (k : ℕ) :
  k ∣ count p (a^k).factors :=
  by 
    rw [count_pow ha hp]
    apply dvd_mul_right

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_pow_of_dvd_count
[nontrivial α]
{a : associates α}
(ha : «expr ≠ »(a, 0))
{k : exprℕ()}
(hk : ∀
 (p : associates α)
 (hp : irreducible p), «expr ∣ »(k, count p a.factors)) : «expr∃ , »((b : associates α), «expr = »(a, «expr ^ »(b, k))) :=
begin
  obtain ["⟨", ident a0, ",", ident hz, ",", ident rfl, "⟩", ":=", expr exists_non_zero_rep ha],
  rw ["[", expr factors_mk a0 hz, "]"] ["at", ident hk],
  have [ident hk'] [":", expr ∀ p, «expr ∈ »(p, factors' a0) → «expr ∣ »(k, (factors' a0).count p)] [],
  { rintros [ident p, "-"],
    have [ident pp] [":", expr «expr = »(p, ⟨p.val, p.2⟩)] [],
    { simp [] [] ["only"] ["[", expr subtype.coe_eta, ",", expr subtype.val_eq_coe, "]"] [] [] },
    rw ["[", expr pp, ",", "<-", expr count_some p.2, "]"] [],
    exact [expr hk p.val p.2] },
  obtain ["⟨", ident u, ",", ident hu, "⟩", ":=", expr multiset.exists_smul_of_dvd_count _ hk'],
  use [expr (u : factor_set α).prod],
  apply [expr eq_of_factors_eq_factors],
  rw ["[", expr pow_factors, ",", expr prod_factors, ",", expr factors_mk a0 hz, ",", "<-", expr with_top.some_eq_coe, ",", expr hu, "]"] [],
  exact [expr with_bot.coe_nsmul u k]
end

omit dec

omit dec_irr

omit dec'

theorem eq_pow_of_mul_eq_pow [Nontrivial α] {a b c : Associates α} (ha : a ≠ 0) (hb : b ≠ 0)
  (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) {k : ℕ} (h : (a*b) = (c^k)) : ∃ d : Associates α, a = (d^k) :=
  by 
    classical 
    byCases' hk0 : k = 0
    ·
      use 1
      rw [hk0, pow_zeroₓ] at h⊢
      apply (mul_eq_one_iff.1 h).1
    ·
      refine' is_pow_of_dvd_count ha _ 
      intro p hp 
      apply dvd_count_of_dvd_count_mul ha hb hp hab 
      rw [h]
      apply dvd_count_pow _ hp 
      rintro rfl 
      rw [zero_pow' _ hk0] at h 
      cases mul_eq_zero.mp h <;> contradiction

end Associates

section 

open Associates UniqueFactorizationMonoid

theorem Associates.quot_out {α : Type _} [CommMonoidₓ α] (a : Associates α) : Associates.mk (Quot.out a) = a :=
  by 
    rw [←quot_mk_eq_mk, Quot.out_eq]

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `to_gcd_monoid` constructs a GCD monoid out of a unique factorization domain. -/
noncomputable
def unique_factorization_monoid.to_gcd_monoid
(α : Type*)
[comm_cancel_monoid_with_zero α]
[nontrivial α]
[unique_factorization_monoid α]
[decidable_eq (associates α)]
[decidable_eq α] : gcd_monoid α :=
{ gcd := λ a b, quot.out («expr ⊓ »(associates.mk a, associates.mk b) : associates α),
  lcm := λ a b, quot.out («expr ⊔ »(associates.mk a, associates.mk b) : associates α),
  gcd_dvd_left := λ
  a
  b, by { rw ["[", "<-", expr mk_dvd_mk, ",", expr «expr ⊓ »(associates.mk a, associates.mk b).quot_out, ",", expr dvd_eq_le, "]"] [],
    exact [expr inf_le_left] },
  gcd_dvd_right := λ
  a
  b, by { rw ["[", "<-", expr mk_dvd_mk, ",", expr «expr ⊓ »(associates.mk a, associates.mk b).quot_out, ",", expr dvd_eq_le, "]"] [],
    exact [expr inf_le_right] },
  dvd_gcd := λ
  a
  b
  c
  hac
  hab, by { rw ["[", "<-", expr mk_dvd_mk, ",", expr «expr ⊓ »(associates.mk c, associates.mk b).quot_out, ",", expr dvd_eq_le, ",", expr le_inf_iff, ",", expr mk_le_mk_iff_dvd_iff, ",", expr mk_le_mk_iff_dvd_iff, "]"] [],
    exact [expr ⟨hac, hab⟩] },
  lcm_zero_left := λ a, by { have [] [":", expr «expr = »(associates.mk (0 : α), «expr⊤»())] [":=", expr rfl],
    rw ["[", expr this, ",", expr top_sup_eq, ",", "<-", expr this, ",", "<-", expr associated_zero_iff_eq_zero, ",", "<-", expr mk_eq_mk_iff_associated, ",", "<-", expr associated_iff_eq, ",", expr associates.quot_out, "]"] [] },
  lcm_zero_right := λ a, by { have [] [":", expr «expr = »(associates.mk (0 : α), «expr⊤»())] [":=", expr rfl],
    rw ["[", expr this, ",", expr sup_top_eq, ",", "<-", expr this, ",", "<-", expr associated_zero_iff_eq_zero, ",", "<-", expr mk_eq_mk_iff_associated, ",", "<-", expr associated_iff_eq, ",", expr associates.quot_out, "]"] [] },
  gcd_mul_lcm := λ
  a
  b, by { rw ["[", "<-", expr mk_eq_mk_iff_associated, ",", "<-", expr associates.mk_mul_mk, ",", "<-", expr associated_iff_eq, ",", expr associates.quot_out, ",", expr associates.quot_out, ",", expr mul_comm, ",", expr sup_mul_inf, ",", expr associates.mk_mul_mk, "]"] [] } }

/-- `to_normalized_gcd_monoid` constructs a GCD monoid out of a normalization on a
  unique factorization domain. -/
noncomputable def UniqueFactorizationMonoid.toNormalizedGcdMonoid (α : Type _) [CommCancelMonoidWithZero α]
  [Nontrivial α] [UniqueFactorizationMonoid α] [NormalizationMonoid α] [DecidableEq (Associates α)] [DecidableEq α] :
  NormalizedGcdMonoid α :=
  { ‹NormalizationMonoid α› with gcd := fun a b => (Associates.mk a⊓Associates.mk b).out,
    lcm := fun a b => (Associates.mk a⊔Associates.mk b).out,
    gcd_dvd_left := fun a b => (out_dvd_iff a (Associates.mk a⊓Associates.mk b)).2$ inf_le_left,
    gcd_dvd_right := fun a b => (out_dvd_iff b (Associates.mk a⊓Associates.mk b)).2$ inf_le_right,
    dvd_gcd :=
      fun a b c hac hab =>
        show a ∣ (Associates.mk c⊓Associates.mk b).out by 
          rw [dvd_out_iff, le_inf_iff, mk_le_mk_iff_dvd_iff, mk_le_mk_iff_dvd_iff] <;> exact ⟨hac, hab⟩,
    lcm_zero_left :=
      fun a =>
        show (⊤⊔Associates.mk a).out = 0 by 
          simp ,
    lcm_zero_right :=
      fun a =>
        show (Associates.mk a⊔⊤).out = 0 by 
          simp ,
    gcd_mul_lcm :=
      fun a b =>
        by 
          rw [←out_mul, mul_commₓ, sup_mul_inf, mk_mul_mk, out_mk]
          exact normalize_associated (a*b),
    normalize_gcd :=
      fun a b =>
        by 
          convert normalize_out _,
    normalize_lcm :=
      fun a b =>
        by 
          convert normalize_out _ }

end 

namespace UniqueFactorizationMonoid

-- error in RingTheory.UniqueFactorizationDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `y` is a nonzero element of a unique factorization monoid with finitely
many units (e.g. `ℤ`, `ideal (ring_of_integers K)`), it has finitely many divisors. -/
noncomputable
def fintype_subtype_dvd
{M : Type*}
[comm_cancel_monoid_with_zero M]
[unique_factorization_monoid M]
[fintype (units M)]
(y : M)
(hy : «expr ≠ »(y, 0)) : fintype {x // «expr ∣ »(x, y)} :=
begin
  haveI [] [":", expr nontrivial M] [":=", expr ⟨⟨y, 0, hy⟩⟩],
  haveI [] [":", expr normalization_monoid M] [":=", expr unique_factorization_monoid.normalization_monoid],
  haveI [] [] [":=", expr classical.dec_eq M],
  haveI [] [] [":=", expr classical.dec_eq (associates M)],
  refine [expr fintype.of_finset (((normalized_factors y).powerset.to_finset.product (finset.univ : finset (units M))).image (λ
     s, «expr * »((s.snd : M), s.fst.prod))) (λ x, _)],
  simp [] [] ["only"] ["[", expr exists_prop, ",", expr finset.mem_image, ",", expr finset.mem_product, ",", expr finset.mem_univ, ",", expr and_true, ",", expr multiset.mem_to_finset, ",", expr multiset.mem_powerset, ",", expr exists_eq_right, ",", expr multiset.mem_map, "]"] [] [],
  split,
  { rintros ["⟨", ident s, ",", ident hs, ",", ident rfl, "⟩"],
    have [ident prod_s_ne] [":", expr «expr ≠ »(s.fst.prod, 0)] [],
    { intro [ident hz],
      apply [expr hy (eq_zero_of_zero_dvd _)],
      have [ident hz] [] [":=", expr (@multiset.prod_eq_zero_iff M _ _ _ s.fst).mp hz],
      rw ["<-", expr (normalized_factors_prod hy).dvd_iff_dvd_right] [],
      exact [expr multiset.dvd_prod (multiset.mem_of_le hs hz)] },
    show [expr «expr ∣ »(«expr * »((s.snd : M), s.fst.prod), y)],
    rw ["[", expr (unit_associated_one.mul_right s.fst.prod).dvd_iff_dvd_left, ",", expr one_mul, ",", "<-", expr (normalized_factors_prod hy).dvd_iff_dvd_right, "]"] [],
    exact [expr multiset.prod_dvd_prod hs] },
  { rintro ["(", ident h, ":", expr «expr ∣ »(x, y), ")"],
    have [ident hx] [":", expr «expr ≠ »(x, 0)] [],
    { refine [expr mt (λ hx, _) hy],
      rwa ["[", expr hx, ",", expr zero_dvd_iff, "]"] ["at", ident h] },
    obtain ["⟨", ident u, ",", ident hu, "⟩", ":=", expr normalized_factors_prod hx],
    refine [expr ⟨⟨normalized_factors x, u⟩, _, (mul_comm _ _).trans hu⟩],
    exact [expr (dvd_iff_normalized_factors_le_normalized_factors hx hy).mp h] }
end

end UniqueFactorizationMonoid

