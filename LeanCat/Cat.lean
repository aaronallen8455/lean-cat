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

-- | A dependent pair that is fully parametric over universes
inductive DepPair.{u1, u2} {ty : Sort u1} (p : ty → Sort u2) : Sort (max 1 u1 u2)
  | mk : (foc : ty) → p foc → DepPair p

def slice_cat {C : Cat} (c : C.obj) : Cat :=
  { obj := DepPair (C.mor c ·)
  , mor := λ ⟨a, m⟩ ⟨b, n⟩ => ∃ (f : C.mor a b), C.comp f m = n
  , comp := λ ⟨f, h1⟩ ⟨g, h2⟩ => ⟨C.comp f g, by rw [←C.comp_assoc, h2, h1]⟩
  , iden := λ ⟨x, m⟩ => ⟨C.iden x, by rw [C.left_id]⟩
  , comp_assoc := by simp
  , left_id := by simp
  , right_id := by simp
  }

def empty_cat : Cat :=
  { obj := False
  , mor := λ _x _y => False
  , comp := λ {a b c} _m _n => a.elim
  , iden := λ x => x.elim
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