import Mathbin.Data.Multiset.Basic

/-!
# Sections of a multiset
-/


namespace Multiset

variable{α : Type _}

section Sections

/--
The sections of a multiset of multisets `s` consists of all those multisets
which can be put in bijection with `s`, so each element is an member of the corresponding multiset.
-/
def sections (s : Multiset (Multiset α)) : Multiset (Multiset α) :=
  Multiset.recOn s {0} (fun s _ c => s.bind$ fun a => c.map (Multiset.cons a))
    fun a₀ a₁ s pi =>
      by 
        simp [map_bind, bind_bind a₀ a₁, cons_swap]

@[simp]
theorem sections_zero : sections (0 : Multiset (Multiset α)) = {0} :=
  rfl

@[simp]
theorem sections_cons (s : Multiset (Multiset α)) (m : Multiset α) :
  sections (m ::ₘ s) = m.bind fun a => (sections s).map (Multiset.cons a) :=
  rec_on_cons m s

-- error in Data.Multiset.Sections: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem coe_sections : ∀
l : list (list α), «expr = »(sections (l.map (λ
  l : list α, (l : multiset α)) : multiset (multiset α)), (l.sections.map (λ
  l : list α, (l : multiset α)) : multiset (multiset α)))
| «expr[ , ]»([]) := rfl
| «expr :: »(a, l) := begin
  simp [] [] [] [] [] [],
  rw ["[", "<-", expr cons_coe, ",", expr sections_cons, ",", expr bind_map_comm, ",", expr coe_sections l, "]"] [],
  simp [] [] [] ["[", expr list.sections, ",", expr («expr ∘ »), ",", expr list.bind, "]"] [] []
end

@[simp]
theorem sections_add (s t : Multiset (Multiset α)) :
  sections (s+t) = (sections s).bind fun m => (sections t).map ((·+·) m) :=
  Multiset.induction_on s
    (by 
      simp )
    fun a s ih =>
      by 
        simp [ih, bind_assoc, map_bind, bind_map, -add_commₓ]

theorem mem_sections {s : Multiset (Multiset α)} : ∀ {a}, a ∈ sections s ↔ s.rel (fun s a => a ∈ s) a :=
  Multiset.induction_on s
    (by 
      simp )
    fun a s ih a' =>
      by 
        simp [ih, rel_cons_left, -exists_and_distrib_left, exists_and_distrib_left.symm, eq_comm]

-- error in Data.Multiset.Sections: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem card_sections {s : multiset (multiset α)} : «expr = »(card (sections s), prod (s.map card)) :=
multiset.induction_on s (by simp [] [] [] [] [] []) (by simp [] [] [] [] [] [] { contextual := tt })

theorem prod_map_sum [CommSemiringₓ α] {s : Multiset (Multiset α)} : Prod (s.map Sum) = Sum ((sections s).map Prod) :=
  Multiset.induction_on s
    (by 
      simp )
    fun a s ih =>
      by 
        simp [ih, map_bind, sum_map_mul_left, sum_map_mul_right]

end Sections

end Multiset

