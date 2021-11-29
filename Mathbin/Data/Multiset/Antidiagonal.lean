import Mathbin.Data.Multiset.Powerset

/-!
# The antidiagonal on a multiset.

The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
such that `t₁ + t₂ = s`. These pairs are counted with multiplicities.
-/


namespace Multiset

open List

variable {α β : Type _}

/-- The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
    such that `t₁ + t₂ = s`. These pairs are counted with multiplicities. -/
def antidiagonal (s : Multiset α) : Multiset (Multiset α × Multiset α) :=
  Quot.liftOn s (fun l => (revzip (powerset_aux l) : Multiset (Multiset α × Multiset α)))
    fun l₁ l₂ h => Quot.sound (revzip_powerset_aux_perm h)

theorem antidiagonal_coe (l : List α) : @antidiagonal α l = revzip (powerset_aux l) :=
  rfl

@[simp]
theorem antidiagonal_coe' (l : List α) : @antidiagonal α l = revzip (powerset_aux' l) :=
  Quot.sound revzip_powerset_aux_perm_aux'

-- error in Data.Multiset.Antidiagonal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A pair `(t₁, t₂)` of multisets is contained in `antidiagonal s`
    if and only if `t₁ + t₂ = s`. -/
@[simp]
theorem mem_antidiagonal
{s : multiset α}
{x : «expr × »(multiset α, multiset α)} : «expr ↔ »(«expr ∈ »(x, antidiagonal s), «expr = »(«expr + »(x.1, x.2), s)) :=
«expr $ »(quotient.induction_on s, λ l, begin
   simp [] [] [] ["[", expr antidiagonal_coe, "]"] [] [],
   refine [expr ⟨λ h, revzip_powerset_aux h, λ h, _⟩],
   haveI [] [] [":=", expr classical.dec_eq α],
   simp [] [] [] ["[", expr revzip_powerset_aux_lemma l revzip_powerset_aux, ",", expr h.symm, "]"] [] [],
   cases [expr x] ["with", ident x₁, ident x₂],
   dsimp ["only"] [] [] [],
   exact [expr ⟨x₁, le_add_right _ _, by rw [expr add_tsub_cancel_left x₁ x₂] []⟩]
 end)

@[simp]
theorem antidiagonal_map_fst (s : Multiset α) : (antidiagonal s).map Prod.fst = powerset s :=
  Quotientₓ.induction_on s$
    fun l =>
      by 
        simp [powerset_aux']

@[simp]
theorem antidiagonal_map_snd (s : Multiset α) : (antidiagonal s).map Prod.snd = powerset s :=
  Quotientₓ.induction_on s$
    fun l =>
      by 
        simp [powerset_aux']

@[simp]
theorem antidiagonal_zero : @antidiagonal α 0 = {(0, 0)} :=
  rfl

@[simp]
theorem antidiagonal_cons (a : α) s :
  antidiagonal (a ::ₘ s) = map (Prod.map id (cons a)) (antidiagonal s)+map (Prod.map (cons a) id) (antidiagonal s) :=
  Quotientₓ.induction_on s$
    fun l =>
      by 
        simp only [revzip, reverse_append, quot_mk_to_coe, coe_eq_coe, powerset_aux'_cons, cons_coe, coe_map,
          antidiagonal_coe', coe_add]
        rw [←zip_map, ←zip_map, zip_append, (_ : _ ++ _ = _)]
        ·
          congr <;> simp 
        ·
          simp 

-- error in Data.Multiset.Antidiagonal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem card_antidiagonal (s : multiset α) : «expr = »(card (antidiagonal s), «expr ^ »(2, card s)) :=
by have [] [] [":=", expr card_powerset s]; rwa ["[", "<-", expr antidiagonal_map_fst, ",", expr card_map, "]"] ["at", ident this]

-- error in Data.Multiset.Antidiagonal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prod_map_add
[comm_semiring β]
{s : multiset α}
{f
 g : α → β} : «expr = »(prod (s.map (λ
   a, «expr + »(f a, g a))), sum ((antidiagonal s).map (λ p, «expr * »((p.1.map f).prod, (p.2.map g).prod)))) :=
begin
  refine [expr s.induction_on _ _],
  { simp [] [] [] [] [] [] },
  { assume [binders (a s ih)],
    have [] [] [":=", expr @sum_map_mul_left α β _],
    simp [] [] [] ["[", expr ih, ",", expr add_mul, ",", expr mul_comm, ",", expr mul_left_comm (f a), ",", expr mul_left_comm (g a), ",", expr mul_assoc, ",", expr sum_map_mul_left.symm, "]"] [] [],
    cc }
end

end Multiset

