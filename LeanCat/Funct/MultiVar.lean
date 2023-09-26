import LeanCat.Cat
import LeanCat.Core.Funct

def Bifunct (A : Cat) (B : Cat) (C : Cat) := Funct (prod A B) C

def app_bifunct (F : Bifunct A B C) (a : A.obj) : Funct B C :=
  { map_obj := λ b => F.map_obj (a, b)
  , map_mor := λ f => F.map_mor (A.iden a, f)
  , fmap_id := by
      intros
      simp
      rw [←F.fmap_id]
      simp [prod]
  , fmap_law := by
      intros
      simp
      rw [F.fmap_law]
      simp [prod]
      rw [A.left_id]
  }

-- Profunctor from A to B
def Profunct (A : Cat) (B : Cat) := Bifunct (Op B) A type_cat

def funct_profuncts {C : Cat} {D : Cat} (F : Funct C D) : Profunct C D × Profunct D C :=
  ( { map_obj := λ o => D.mor o.1 (F.map_obj o.2)
    , map_mor := λ f => by
        simp
        intro g
        exact D.comp (F.map_mor f.2) $ D.comp g f.1
    , fmap_id := by
        intros
        simp [*, type_cat, prod, Op]
        conv =>
          lhs
          intro g
          rw [F.fmap_id, D.left_id, D.right_id]
    , fmap_law := by
        intros
        simp [*, type_cat, prod, Op]
        conv =>
          lhs
          intro g_1
          simp
          rw [D.comp_assoc, D.comp_assoc, F.fmap_law, ←D.comp_assoc, ←D.comp_assoc]
    }
  , { map_obj := λ o => D.mor (F.map_obj o.1) o.2
    , map_mor := λ f => by
        simp
        intro g
        exact D.comp f.2 $ D.comp g (F.map_mor f.1)
    , fmap_id := by
        intros
        simp [*, type_cat, prod, Op]
        conv =>
          lhs
          intro g
          rw [D.left_id, F.fmap_id, D.right_id]
    , fmap_law := by
        intros
        simp [*, type_cat, prod, Op]
        conv =>
          lhs
          intro g_1
          simp
          arg 3
          arg 2
          rw [D.comp_assoc]
        conv =>
          lhs
          intro g_1
          arg 3
          rw [←D.comp_assoc, F.fmap_law, ←D.comp_assoc]
        conv =>
          lhs
          intro g_1
          rw [D.comp_assoc]
    }
  )

def BiHom (C : Cat) : Bifunct (Op C) C type_cat :=
  { map_obj := λ x => C.mor x.fst x.snd
  , map_mor := λ {x y} f h =>
      C.comp f.snd (C.comp h f.fst)
  , fmap_id := by
      intro a
      simp [*, type_cat, prod, Op]
      conv =>
        lhs
        intro h
        rw [C.left_id, C.right_id]
  , fmap_law := by
      intro a b c f g
      simp [*, prod, Op, type_cat]
      conv =>
        lhs
        intro h
        simp
        rw [C.comp_assoc, C.comp_assoc, C.comp_assoc, ←C.comp_assoc, ←C.comp_assoc]
  }

def FunctProd (F : Funct A B) (G : Funct C D) : Bifunct A C (prod B D) :=
  { map_obj := λ x => (F.map_obj x.1, G.map_obj x.2)
  , map_mor := λ f => (F.map_mor f.1, G.map_mor f.2)
  , fmap_id := by
      intro a
      simp [*, prod]
      apply And.intro
      . rw [F.fmap_id]
      . rw [G.fmap_id]
  , fmap_law := by
      intro a b c f g
      simp [*, prod]
      apply And.intro
      . rw [F.fmap_law]
      . rw [G.fmap_law]
  }