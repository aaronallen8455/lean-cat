structure Cat where
  obj : Type u1
  mor : obj -> obj -> Type u2
  comp : {a b c : obj} → mor b c → mor a b → mor a c
  iden : (a : obj) -> mor a a
  mor_assoc : ∀ {a b c d} (f : mor c d) (g : mor b c) (h : mor a b),
              comp f (comp g h) = comp (comp f g) h
  left_id : ∀ {a b} (f : mor a b), comp (iden b) f = f
  right_id : ∀ {a b} (f : mor a b), comp f (iden a) = f

instance : CoeSort Cat (Type u1) where
  coe C := C.obj

structure Funct (Dom : Cat) (Cod : Cat) where
  map_obj : Dom → Cod
  map_mor : {x y : Dom} → Dom.mor x y → Cod.mor (map_obj x) (map_obj y)
  fmap_id : {α : Dom} → map_mor (Dom.iden α) = Cod.iden (map_obj α)
  fmap_law : ∀ {a b c} (f : Dom.mor b c) (g : Dom.mor a b), Cod.comp (map_mor f) (map_mor g) = map_mor (Dom.comp f g)

instance (C D : Cat) : CoeFun (Funct C D) (λ _ => C → D) where
  coe F := F.map_obj

def funct_comp (F : Funct D E) (G : Funct C D) : Funct C E :=
  { map_obj := F.map_obj ∘ G.map_obj
  , map_mor := F.map_mor ∘ G.map_mor
  , fmap_id := by
      simp
      intro _x
      rw [G.fmap_id, F.fmap_id]
  , fmap_law := by
      intro _a _b _c _f _g
      simp
      rw [F.fmap_law, G.fmap_law]
  }

-- Identity functor
def I (C : Cat) : Funct C C :=
  { map_obj := id
  , map_mor := id
  , fmap_id := by simp
  , fmap_law := by simp
  }

structure NT (Dom : Cat) (Cod : Cat) (F : Funct Dom Cod) (G : Funct Dom Cod) where
  eta : ∀ (a : Dom), Cod.mor (F.map_obj a) (G.map_obj a)
  nt_law : ∀ {a b} (mor : Dom.mor a b),
             Cod.comp (eta b) (F.map_mor mor) = Cod.comp (G.map_mor mor) (eta a)

def vert_nt_comp (α : NT B C F₂ G₂) (β : NT A B F₁ G₁) : NT A C (funct_comp F₂ F₁) (funct_comp G₂ G₁) :=
  { eta := λ x =>
      let f := α.eta (F₁.map_obj x)
      let g := G₂.map_mor (β.eta x)
      C.comp g f
  , nt_law := by
      intro a b fab
      simp
      have f_comp_def (f : A.mor a b) : (funct_comp F₂ F₁).map_mor f = F₂.map_mor (F₁.map_mor f) := by rfl
      rw [ ←(α.nt_law (β.eta b))
         , f_comp_def
         , ←C.mor_assoc
         , F₂.fmap_law
         , β.nt_law fab
         , ←F₂.fmap_law
         , C.mor_assoc
         , α.nt_law (G₁.map_mor fab)
         , ←C.mor_assoc
         , α.nt_law (β.eta a)
         ]
      rfl
  }

-- The category of types
def type_cat : Cat :=
  { obj := Type
  , mor := (· → ·)
  , iden := λ a => @id a
  , mor_assoc := λ _ _ _ => rfl
  , comp := (· ∘ ·)
  , left_id := λ _ => rfl
  , right_id := λ _ => rfl 
  }

-- The category of functors
def functor_cat (Dom : Cat) (Cod : Cat) : Cat :=
  { obj := Funct Dom Cod
  , mor := NT Dom Cod
  , comp := λ α β =>
      { eta := λ x => Cod.comp (α.eta x) (β.eta x)
      , nt_law := λ C => by
          simp
          have l1 := α.nt_law C
          have l2 := β.nt_law C
          sorry
          --rw [←Cod.mor_assoc, l2, Cod.mor_assoc, l1, Cod.mor_assoc] -- this is correct but slow!
      }
  , iden := λ F =>
    { eta := λ a => F.map_mor (Dom.iden a)
    , nt_law := by
        intro a b mor
        simp
        rw [F.fmap_id, Cod.left_id, F.fmap_id, Cod.right_id]
    }
  , mor_assoc := by simp [Cod.mor_assoc]
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

-- The category of categories
def category_cat : Cat :=
  { obj := Cat
  , mor := Funct
  , comp := funct_comp
  , iden := I
  , mor_assoc := by
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