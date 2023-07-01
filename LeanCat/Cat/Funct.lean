import LeanCat.Core
import LeanCat.Cat.Set

-- The category of functors
def funct_cat {Dom : Cat.{u1, u2}} {Cod : Cat.{u3, u4}} : Cat :=
  { obj := Funct Dom Cod
  , mor := NT
  , comp := λ {F G H} α β =>
      { eta := λ x => Cod.comp (α.eta x) (β.eta x)
      , nt_law := λ {a b} mor => by
          simp
          exact (Eq.symm (Cod.comp_assoc (α.eta b) (β.eta b) (F.map_mor mor))).trans
                $ (congrArg (Cat.comp Cod (NT.eta α b)) (β.nt_law mor)).trans
                $ (Cod.comp_assoc (α.eta b) (G.map_mor mor) (β.eta a)).trans
                $ (congrArg (λ x => Cod.comp x (NT.eta β a)) (α.nt_law mor)).trans
                $ Eq.symm (Cod.comp_assoc (H.map_mor mor) (α.eta a) (β.eta a))
          -- rw [←Cod.comp_assoc, β.nt_law mor, Cod.comp_assoc, α.nt_law mor, Cod.comp_assoc]
          -- ^ this is correct but very slow to compile for some reason.
      }
  , iden := λ F =>
    { eta := λ a => F.map_mor (Dom.iden a)
    , nt_law := by
        intro a b mor
        simp
        rw [F.fmap_id, Cod.left_id, F.fmap_id, Cod.right_id]
    }
  , comp_assoc := by
      intros
      simp
      conv =>
        lhs
        intro x
        rw [Cod.comp_assoc]
  , left_id := by
      intro _F G _α
      simp
      conv =>
        lhs
        arg 1
        intro _x
        rw [G.fmap_id, Cod.left_id]
  , right_id := by
      intro F _G _α
      simp
      conv =>
        lhs
        arg 1
        intro _x
        rw [F.fmap_id, Cod.right_id]
  }

-- Category of presheaves
def presheaves (C : Cat) : Cat := @funct_cat (Op C) type_cat