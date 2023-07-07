import LeanCat.Core.Cat

-- Covariant functor
structure Funct.{u1, u2, u3, u4} (Dom : Cat.{u1, u2}) (Cod : Cat.{u3, u4}) where
  map_obj : Dom.obj → Cod.obj
  map_mor : {x y : Dom.obj} → Dom.mor x y → Cod.mor (map_obj x) (map_obj y)
  fmap_id : {a : Dom.obj} → map_mor (Dom.iden a) = Cod.iden (map_obj a)
  fmap_law : ∀ {a b c} (f : Dom.mor b c) (g : Dom.mor a b),
               Cod.comp (map_mor f) (map_mor g) = map_mor (Dom.comp f g)

--instance (C D : Cat) : CoeFun (Funct C D) (λ _ => C → D) where
  --coe F := F.map_obj

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

theorem funct_comp_assoc : funct_comp C (funct_comp D E) = funct_comp (funct_comp C D) E := by
  simp [funct_comp]
  constructor <;> rfl

theorem funct_map_assoc {F : Funct E F} {G : Funct D E} {H : Funct C D} (x : C.obj)
          : F.map_obj ((funct_comp G H).map_obj x)
          = (funct_comp F G).map_obj (H.map_obj x) := rfl

-- Contravariant functor
def ContraFunct (Dom : Cat.{u1, u2}) (Cod : Cat.{u3, u4}) := Funct (Op Dom) Cod