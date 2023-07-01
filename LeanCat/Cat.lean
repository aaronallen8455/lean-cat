import LeanCat.Core
import LeanCat.Mor

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

def groupoid (C : Cat) : Prop := ∀ {a b : C.obj} (m : C.mor a b), isomorphism m

def discrete (C : Cat) : Prop := ∀ (a b : C.obj), ∃ (_ : C.mor a b), a = b

def thin (C : Cat) : Prop := ∀ (a b : C.obj) (m n : C.mor a b), m = n

def skeletal (C : Cat) : Prop := ∀ {a b : C.obj} (m : C.mor a b), isomorphism m → automorphism m

theorem thin_poset : thin poset_cat := by
  intro _a _b m _n
  rfl

theorem skeletal_poset : skeletal poset_cat := by
  intro _a _b m iso
  constructor
  . assumption
  . have ⟨n, _⟩ := iso
    exact Nat.le_antisymm m n