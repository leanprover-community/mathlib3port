import Mathbin.Data.Multiset.Basic 
import Mathbin.Control.Traversable.Lemmas 
import Mathbin.Control.Traversable.Instances

/-!
# Functoriality of `multiset`.
-/


universe u

namespace Multiset

open List

instance  : Functor Multiset :=
  { map := @map }

@[simp]
theorem fmap_def {α' β'} {s : Multiset α'} (f : α' → β') : f <$> s = s.map f :=
  rfl

instance  : IsLawfulFunctor Multiset :=
  by 
    refine' { .. } <;> intros  <;> simp 

open IsLawfulTraversable IsCommApplicative

variable{F : Type u → Type u}[Applicativeₓ F][IsCommApplicative F]

variable{α' β' : Type u}(f : α' → F β')

-- error in Data.Multiset.Functor: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
def traverse : multiset α' → F (multiset β') :=
quotient.lift «expr ∘ »(functor.map coe, traversable.traverse f) (begin
   introv [ident p],
   unfold [ident function.comp] [],
   induction [expr p] [] [] [],
   case [ident perm.nil] { refl },
   case [ident perm.cons] { have [] [":", expr «expr = »(«expr <*> »(«expr <$> »(multiset.cons, f p_x), «expr <$> »(coe, traverse f p_l₁)), «expr <*> »(«expr <$> »(multiset.cons, f p_x), «expr <$> »(coe, traverse f p_l₂)))] [],
     { rw ["[", expr p_ih, "]"] [] },
     simpa [] [] [] [] ["with", ident functor_norm] [] },
   case [ident perm.swap] { have [] [":", expr «expr = »(«expr <*> »(«expr <$> »(λ
         (a b)
         (l : list β'), («expr↑ »(«expr :: »(a, «expr :: »(b, l))) : multiset β'), f p_y), f p_x), «expr <*> »(«expr <$> »(λ
         a b l, «expr↑ »(«expr :: »(a, «expr :: »(b, l))), f p_x), f p_y))] [],
     { rw ["[", expr is_comm_applicative.commutative_map, "]"] [],
       congr,
       funext [ident a, ident b, ident l],
       simpa [] [] [] ["[", expr flip, "]"] [] ["using", expr perm.swap b a l] },
     simp [] [] [] ["[", expr («expr ∘ »), ",", expr this, "]"] ["with", ident functor_norm] [] },
   case [ident perm.trans] { simp [] [] [] ["[", "*", "]"] [] [] }
 end)

instance  : Monadₓ Multiset :=
  { Multiset.functor with pure := fun α x => {x}, bind := @bind }

@[simp]
theorem pure_def {α} : (pure : α → Multiset α) = singleton :=
  rfl

@[simp]
theorem bind_def {α β} : · >>= · = @bind α β :=
  rfl

instance  : IsLawfulMonad Multiset :=
  { bind_pure_comp_eq_map :=
      fun α β f s =>
        Multiset.induction_on s rfl$
          fun a s ih =>
            by 
              simp ,
    pure_bind :=
      fun α β x f =>
        by 
          simp [pure],
    bind_assoc := @bind_assoc }

open Functor

open Traversable IsLawfulTraversable

@[simp]
theorem lift_coe {α β : Type _} (x : List α) (f : List α → β) (h : ∀ a b : List α, a ≈ b → f a = f b) :
  Quotientₓ.lift f h (x : Multiset α) = f x :=
  Quotientₓ.lift_mk _ _ _

@[simp]
theorem map_comp_coe {α β} (h : α → β) : Functor.map h ∘ coeₓ = (coeₓ ∘ Functor.map h : List α → Multiset β) :=
  by 
    funext  <;> simp [Functor.map]

theorem id_traverse {α : Type _} (x : Multiset α) : traverse id.mk x = x :=
  Quotientₓ.induction_on x
    (by 
      intro 
      simp [traverse]
      rfl)

theorem comp_traverse {G H : Type _ → Type _} [Applicativeₓ G] [Applicativeₓ H] [IsCommApplicative G]
  [IsCommApplicative H] {α β γ : Type _} (g : α → G β) (h : β → H γ) (x : Multiset α) :
  traverse (comp.mk ∘ Functor.map h ∘ g) x = comp.mk (Functor.map (traverse h) (traverse g x)) :=
  Quotientₓ.induction_on x
    (by 
      intro  <;> simp' [traverse, comp_traverse] with functor_norm <;> simp' [· <$> ·, · ∘ ·] with functor_norm)

theorem map_traverse {G : Type _ → Type _} [Applicativeₓ G] [IsCommApplicative G] {α β γ : Type _} (g : α → G β)
  (h : β → γ) (x : Multiset α) : Functor.map (Functor.map h) (traverse g x) = traverse (Functor.map h ∘ g) x :=
  Quotientₓ.induction_on x
    (by 
      intro  <;> simp' [traverse] with functor_norm <;> rw [IsLawfulFunctor.comp_map, map_traverse])

theorem traverse_map {G : Type _ → Type _} [Applicativeₓ G] [IsCommApplicative G] {α β γ : Type _} (g : α → β)
  (h : β → G γ) (x : Multiset α) : traverse h (map g x) = traverse (h ∘ g) x :=
  Quotientₓ.induction_on x
    (by 
      intro  <;> simp [traverse] <;> rw [←Traversable.traverse_map h g] <;> [rfl, infer_instance])

theorem naturality {G H : Type _ → Type _} [Applicativeₓ G] [Applicativeₓ H] [IsCommApplicative G] [IsCommApplicative H]
  (eta : ApplicativeTransformation G H) {α β : Type _} (f : α → G β) (x : Multiset α) :
  eta (traverse f x) = traverse (@eta _ ∘ f) x :=
  Quotientₓ.induction_on x
    (by 
      intro  <;> simp' [traverse, IsLawfulTraversable.naturality] with functor_norm)

end Multiset

