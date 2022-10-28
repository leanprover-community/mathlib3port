/-
Copyright (c) 2021 David Wärn,. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Scott Morrison
-/
import Mathbin.Combinatorics.Quiver.Basic
import Mathbin.Data.List.Basic
import Mathbin.Logic.Lemmas

/-!
# Paths in quivers

Given a quiver `V`, we define the type of paths from `a : V` to `b : V` as an inductive
family. We define composition of paths and the action of prefunctors on paths.
-/


open Function

universe v v₁ v₂ u u₁ u₂

namespace Quiver

/-- `G.path a b` is the type of paths from `a` to `b` through the arrows of `G`. -/
inductive Path {V : Type u} [Quiver.{v} V] (a : V) : V → Sort max (u + 1) v
  | nil : path a
  | cons : ∀ {b c : V}, path b → (b ⟶ c) → path c

/-- An arrow viewed as a path of length one. -/
def Hom.toPath {V} [Quiver V] {a b : V} (e : a ⟶ b) : Path a b :=
  Path.nil.cons e

namespace Path

variable {V : Type u} [Quiver V] {a b c : V}

/-- The length of a path is the number of arrows it uses. -/
def length {a : V} : ∀ {b : V}, Path a b → ℕ
  | _, path.nil => 0
  | _, path.cons p _ => p.length + 1

instance {a : V} : Inhabited (Path a a) :=
  ⟨Path.nil⟩

@[simp]
theorem length_nil {a : V} : (Path.nil : Path a a).length = 0 :=
  rfl

@[simp]
theorem length_cons (a b c : V) (p : Path a b) (e : b ⟶ c) : (p.cons e).length = p.length + 1 :=
  rfl

theorem eq_of_length_zero (p : Path a b) (hzero : p.length = 0) : a = b := by
  cases p
  · rfl
    
  · cases Nat.succ_ne_zero _ hzero
    

/-- Composition of paths. -/
def comp {a b : V} : ∀ {c}, Path a b → Path b c → Path a c
  | _, p, path.nil => p
  | _, p, path.cons q e => (p.comp q).cons e

@[simp]
theorem comp_cons {a b c d : V} (p : Path a b) (q : Path b c) (e : c ⟶ d) : p.comp (q.cons e) = (p.comp q).cons e :=
  rfl

@[simp]
theorem comp_nil {a b : V} (p : Path a b) : p.comp Path.nil = p :=
  rfl

@[simp]
theorem nil_comp {a : V} : ∀ {b} (p : Path a b), Path.nil.comp p = p
  | a, path.nil => rfl
  | b, path.cons p e => by rw [comp_cons, nil_comp]

@[simp]
theorem comp_assoc {a b c : V} :
    ∀ {d} (p : Path a b) (q : Path b c) (r : Path c d), (p.comp q).comp r = p.comp (q.comp r)
  | c, p, q, path.nil => rfl
  | d, p, q, path.cons r e => by rw [comp_cons, comp_cons, comp_cons, comp_assoc]

@[simp]
theorem length_comp (p : Path a b) : ∀ {c} (q : Path b c), (p.comp q).length = p.length + q.length
  | c, nil => rfl
  | c, cons q h => congr_arg Nat.succ q.length_comp

theorem comp_inj {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (hq : q₁.length = q₂.length) :
    p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ := by
  refine'
    ⟨fun h => _, by
      rintro ⟨rfl, rfl⟩
      rfl⟩
  induction' q₁ with d₁ e₁ q₁ f₁ ih generalizing q₂ <;> obtain _ | ⟨q₂, f₂⟩ := q₂
  · exact ⟨h, rfl⟩
    
  · cases hq
    
  · cases hq
    
  simp only [comp_cons] at h
  obtain rfl := h.1
  obtain ⟨rfl, rfl⟩ := ih (Nat.succ_injective hq) h.2.1.Eq
  rw [h.2.2.Eq]
  exact ⟨rfl, rfl⟩

theorem comp_inj' {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (h : p₁.length = p₂.length) :
    p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ :=
  ⟨fun h_eq => (comp_inj <| add_left_injective p₁.length <| by simpa [h] using congr_arg length h_eq).1 h_eq, by
    rintro ⟨rfl, rfl⟩
    rfl⟩

theorem comp_injective_left (q : Path b c) : Injective fun p : Path a b => p.comp q := fun p₁ p₂ h =>
  ((comp_inj rfl).1 h).1

theorem comp_injective_right (p : Path a b) : Injective (p.comp : Path b c → Path a c) := fun q₁ q₂ h =>
  ((comp_inj' rfl).1 h).2

@[simp]
theorem comp_inj_left {p₁ p₂ : Path a b} {q : Path b c} : p₁.comp q = p₂.comp q ↔ p₁ = p₂ :=
  q.comp_injective_left.eq_iff

@[simp]
theorem comp_inj_right {p : Path a b} {q₁ q₂ : Path b c} : p.comp q₁ = p.comp q₂ ↔ q₁ = q₂ :=
  p.comp_injective_right.eq_iff

/-- Turn a path into a list. The list contains `a` at its head, but not `b` a priori. -/
@[simp]
def toList : ∀ {b : V}, Path a b → List V
  | b, nil => []
  | b, @cons _ _ _ c _ p f => c :: p.toList

/-- `quiver.path.to_list` is a contravariant functor. The inversion comes from `quiver.path` and
`list` having different preferred directions for adding elements. -/
@[simp]
theorem to_list_comp (p : Path a b) : ∀ {c} (q : Path b c), (p.comp q).toList = q.toList ++ p.toList
  | c, nil => by simp
  | c, @cons _ _ _ d _ q f => by simp [to_list_comp]

theorem to_list_chain_nonempty : ∀ {b} (p : Path a b), p.toList.Chain (fun x y => Nonempty (y ⟶ x)) b
  | b, nil => List.Chain.nil
  | b, cons p f => p.to_list_chain_nonempty.cons ⟨f⟩

variable [∀ a b : V, Subsingleton (a ⟶ b)]

theorem to_list_injective (a : V) : ∀ b, Injective (toList : Path a b → List V)
  | b, nil, nil, h => rfl
  | b, nil, @cons _ _ _ c _ p f, h => (List.cons_ne_nil _ _ h.symm).elim
  | b, @cons _ _ _ c _ p f, nil, h => (List.cons_ne_nil _ _ h).elim
  | b, @cons _ _ _ c _ p f, @cons _ _ s t u C D, h => by
    simp only [to_list] at h
    obtain ⟨rfl, hAC⟩ := h
    simp [to_list_injective _ hAC]

@[simp]
theorem to_list_inj {p q : Path a b} : p.toList = q.toList ↔ p = q :=
  (to_list_injective _ _).eq_iff

end Path

end Quiver

namespace Prefunctor

open Quiver

variable {V : Type u₁} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W] (F : Prefunctor V W)

/- warning: prefunctor.map_path -> Prefunctor.mapPath is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u₁}} [_inst_1 : Quiver.{v₁ u₁} V] {W : Type.{u₂}} [_inst_2 : Quiver.{v₂ u₂} W] (F : Prefunctor.{v₁ v₂ u₁ u₂} V _inst_1 W _inst_2) {a : V} {b : V}, (Quiver.Path.{v₁ u₁} V _inst_1 a b) -> (Quiver.Path.{v₂ u₂} W _inst_2 (Prefunctor.obj.{v₁ v₂ u₁ u₂} V _inst_1 W _inst_2 F a) (Prefunctor.obj.{v₁ v₂ u₁ u₂} V _inst_1 W _inst_2 F b))
but is expected to have type
  forall {V : Type.{u₁}} [_inst_1 : Quiver.{v₁ u₁} V] {W : Type.{u₂}} [_inst_2 : Quiver.{v₂ u₂} W] (F : Prefunctor.{v₁ v₂ u₁ u₂} V _inst_1 W _inst_2) {a : V} {b : V}, (Quiver.Path.{v₁ u₁} V _inst_1 a b) -> (Quiver.Path.{v₂ u₂} W _inst_2 (Prefunctor.obj.{v₁ v₂ u₁ u₂} V _inst_1 W _inst_2 F a) (Prefunctor.obj.{v₁ v₂ u₁ u₂} V _inst_1 W _inst_2 F b))
Case conversion may be inaccurate. Consider using '#align prefunctor.map_path Prefunctor.mapPathₓ'. -/
/-- The image of a path under a prefunctor. -/
def mapPath {a : V} : ∀ {b : V}, Path a b → Path (F.obj a) (F.obj b)
  | _, path.nil => Path.nil
  | _, path.cons p e => Path.cons (map_path p) (F.map e)

@[simp]
theorem map_path_nil (a : V) : F.mapPath (Path.nil : Path a a) = path.nil :=
  rfl

@[simp]
theorem map_path_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
    F.mapPath (Path.cons p e) = Path.cons (F.mapPath p) (F.map e) :=
  rfl

@[simp]
theorem map_path_comp {a b : V} (p : Path a b) :
    ∀ {c : V} (q : Path b c), F.mapPath (p.comp q) = (F.mapPath p).comp (F.mapPath q)
  | _, path.nil => rfl
  | _, path.cons p e => by
    dsimp
    rw [map_path_comp]

@[simp]
theorem map_path_to_path {a b : V} (f : a ⟶ b) : F.mapPath f.toPath = (F.map f).toPath :=
  rfl

end Prefunctor

