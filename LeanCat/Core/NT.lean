import LeanCat.Core.Funct

-- Natural transformation
structure NT {Dom Cod : Cat} (F : Funct Dom Cod) (G : Funct Dom Cod) where
  eta : ∀ (a : Dom.obj), Cod.mor (F.map_obj a) (G.map_obj a)
  nt_law : ∀ {a b} (mor : Dom.mor a b),
             Cod.comp (eta b) (F.map_mor mor) = Cod.comp (G.map_mor mor) (eta a)
