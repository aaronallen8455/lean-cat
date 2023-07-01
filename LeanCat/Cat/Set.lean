import LeanCat.Core

-- The category of types, can be thought of as Set
def type_cat.{u} : Cat :=
  { obj := Type u
  , mor := (· → ·)
  , iden := λ a => @id a
  , comp_assoc := λ _ _ _ => rfl
  , comp := (· ∘ ·)
  , left_id := λ _ => rfl
  , right_id := λ _ => rfl 
  }