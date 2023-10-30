import LeanCat.Core
import LeanCat.Cat.Set

-- The category of functors
def funct_cat.{u1, u2, u3, u4} {Dom : Cat.{u1, u2}} {Cod : Cat.{u3, u4}}
      : Cat.{max 1 u4 u3 u2 u1, max 1 u1 u4} :=
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
def presheaves.{u1, u2} (C : Cat.{u1, u2+1}) :
      Cat.{max 1 (u2+1) (u2+2) u2 u1, max u1 (u2+1)} :=
  @funct_cat.{u1, u2+1, u2+2, u2+1} (Op C) type_cat.{u2}

def precomp_funct {C D E : Cat} (F : Funct C D) : Funct (@funct_cat D E) (@funct_cat C E) :=
  { map_obj := λ G => funct_comp G F
  , map_mor := by
      simp [*, funct_cat]
      intro x y α
      exact { eta := λ c => α.eta (F.map_obj c)
            , nt_law := λ mor => α.nt_law (F.map_mor mor)
            }
  , fmap_id := by
      intro G
      simp [funct_cat, funct_comp]
      conv =>
        lhs
        intro c
        rw [G.fmap_id]
      conv =>
        rhs
        intro a
        rw [F.fmap_id, G.fmap_id]
  , fmap_law := by simp [funct_cat]
  }

def postcomp_funct {C D E : Cat} (F : Funct C D) : Funct (@funct_cat E C) (@funct_cat E D) :=
  { map_obj := λ G => funct_comp F G
  , map_mor := by
      simp [*, funct_cat]
      intro x y α
      exact { eta := λ c => F.map_mor $ α.eta c
            , nt_law := by
                intro a b mor
                simp [*, funct_comp]
                rw [F.fmap_law, α.nt_law mor, ←F.fmap_law]
            }
  , fmap_id := by
      intro G
      simp [funct_cat, funct_comp]
  , fmap_law := by
      intro G H I α β
      simp [funct_cat]
      conv =>
        lhs
        intro x
        rw [F.fmap_law]
  }