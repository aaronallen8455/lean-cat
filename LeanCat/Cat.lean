import LeanCat.Core
import LeanCat.Mor
import LeanCat.Funct

def poset_cat : Cat :=
  { obj := Nat
  , mor := (· ≤ ·)
  , comp := λ a b => Nat.le_trans b a
  , iden := Nat.le_refl
  , left_id := by
      intros
      rfl
  , right_id := by
      intros
      rfl
  , comp_assoc := by
      intros
      rfl
  }

-- A dependent pair that is fully parametric over universes
inductive DepPair.{u1, u2} {ty : Sort u1} (p : ty → Sort u2) : Sort (max 1 u1 u2)
  | mk : (foc : ty) → p foc → DepPair p

-- The comma category
def comma_cat (F : Funct D C) (G : Funct E C) : Cat :=
  { obj := DepPair (λ (d, e) => C.mor (F.map_obj d) (G.map_obj e))
  , mor := λ ⟨(d1, e1), f⟩ ⟨(d2, e2), g⟩ =>
            ∃ (p : (D.mor d1 d2) × (E.mor e1 e2)),
              C.comp (G.map_mor p.2) f = C.comp g (F.map_mor p.1)
  , comp := λ ⟨(f, g), h1⟩ ⟨(h, i), h2⟩ =>
      ⟨(D.comp f h, E.comp g i)
      , by
        simp at h2 h1
        simp
        rw [←G.fmap_law, ←C.comp_assoc, h2, C.comp_assoc, h1, ←C.comp_assoc, F.fmap_law]
      ⟩
  , iden := λ ⟨(d, e), m⟩ =>
      ⟨(D.iden d, E.iden e)
      , by simp
           rw [G.fmap_id, F.fmap_id, C.left_id, C.right_id]
      ⟩
  , left_id := by simp
  , right_id := by simp
  , comp_assoc := by simp
  }

-- Category of elements for a covariant set valued functor
-- objects are a pair of an object c ∈ C and an element of F c
-- morphisms are a morphism f : a → b in C such that F f (x ∈ F a) = y ∈ F b
def cat_of_elems (F : Funct C type_cat) : Cat :=
  { obj := DepPair F.map_obj
  , mor := λ ⟨a, x⟩ ⟨b, y⟩ => ∃ (f : C.mor a b), F.map_mor f x = y
  , comp := λ ⟨f, h1⟩ ⟨g, h2⟩ =>
      ⟨C.comp f g
      , by rw [←F.fmap_law]
           simp [type_cat]
           rw [h2, h1]
      ⟩
  , iden := λ ⟨c, x⟩ => ⟨C.iden c, by rw [F.fmap_id]; simp [type_cat]⟩
  , comp_assoc := by simp
  , left_id := by simp
  , right_id := by simp
  }

def slice_cat {C : Cat} (c : C.obj) : Cat := cat_of_elems (Hom c)

def empty_cat : Cat :=
  { obj := False
  , mor := λ _x _y => False
  , comp := λ {a b c} _m _n => a.elim
  , iden := λ x => x.elim
  , comp_assoc := by simp
  , left_id := by simp
  , right_id := by simp
  }

def unit_cat : Cat :=
  { obj := Unit
  , mor := λ () () => Unit
  , comp := λ () () => ()
  , iden := λ () => ()
  , comp_assoc := by simp
  , left_id := by simp
  , right_id := by simp
  }

def EmptyDiagram (C : Cat) : Funct empty_cat C :=
  { map_obj := False.elim
  , map_mor := λ {x _} _ => x.elim
  , fmap_id := by
      intro a
      exact a.elim
  , fmap_law := by
      intros a
      exact a.elim
  }

def groupoid (C : Cat) : Prop := ∀ {a b : C.obj} (m : C.mor a b), isomorphism m

def discrete (C : Cat) : Prop := ∀ (a b : C.obj), ∃ (_ : C.mor a b), a = b

def thin (C : Cat) : Prop := ∀ (a b : C.obj) (m n : C.mor a b), m = n

def skeletal (C : Cat) : Prop := ∀ {a b : C.obj} (m : C.mor a b), isomorphism m → automorphism m

def sub_cat (Sub : Cat) (D : Cat) : Prop :=
  ∃ F : Funct Sub D, faithful F

def full_sub_cat (Sub : Cat) (D : Cat) : Prop :=
  ∃ F : Funct Sub D, fully_faithful F

theorem thin_poset : thin poset_cat := by
  intro _a _b m _n
  rfl

theorem skeletal_poset : skeletal poset_cat := by
  intro _a _b m iso
  constructor
  . assumption
  . have ⟨n, _⟩ := iso
    exact Nat.le_antisymm m n