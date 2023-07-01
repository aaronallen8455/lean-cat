import LeanCat.Core
import LeanCat.Funct

-- The category of categories
def category_cat : Cat :=
  { obj := Cat
  , mor := Funct
  , comp := funct_comp
  , iden := I
  , comp_assoc := by
      intro _A _B _C _D
      intro _F _G _H
      simp
      constructor <;> rfl
  , left_id := by
      intro _A _B
      intro _F
      simp
      conv =>
        lhs
        args
  , right_id := by
      intro _A _B
      intro _F
      simp
      conv =>
        lhs
        args
  }