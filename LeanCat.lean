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
  fmap_id : {a : Dom} → map_mor (Dom.iden a) = Cod.iden (map_obj a)
  fmap_law : ∀ {a b c} (f : Dom.mor b c) (g : Dom.mor a b),
               Cod.comp (map_mor f) (map_mor g) = map_mor (Dom.comp f g)

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

structure ContraFunct (Dom : Cat) (Cod : Cat) where
  map_obj : Dom → Cod
  map_mor : Dom.mor x y → Cod.mor (map_obj y) (map_obj x)
  fmap_id : {a : Dom} → map_mor (Dom.iden a) = Cod.iden (map_obj a)
  fmap_law : ∀ {a b c} (f : Dom.mor b c) (g : Dom.mor a b),
               Cod.comp (map_mor g) (map_mor f) = map_mor (Dom.comp f g)

structure NT {Dom Cod : Cat} (F : Funct Dom Cod) (G : Funct Dom Cod) where
  eta : ∀ (a : Dom), Cod.mor (F.map_obj a) (G.map_obj a)
  nt_law : ∀ {a b} (mor : Dom.mor a b),
             Cod.comp (eta b) (F.map_mor mor) = Cod.comp (G.map_mor mor) (eta a)

-- a natural isomorphism between functors
def nat_iso (F : Funct C D) (G : Funct C D) : Prop :=
  ∃ (α : NT F G) (β : NT G F), ∀ (c : C),
    (D.comp (β.eta c) (α.eta c) = D.iden (F.map_obj c))
    ∧
    (D.comp (α.eta c) (β.eta c) = D.iden (G.map_obj c)) 

def vert_nt_comp {A B C : Cat} {F₁ G₁ : Funct A B} {F₂ G₂ : Funct B C}
      (α : NT F₂ G₂) (β : NT F₁ G₁) : NT (funct_comp F₂ F₁) (funct_comp G₂ G₁) :=
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

def id_nt (F : Funct C D) : NT F F :=
  { eta := λ a => F.map_mor (C.iden a)
  , nt_law := by
      intros
      simp
      rw [F.fmap_id, D.left_id, F.fmap_id, D.right_id]
  }

def whisker_left (F : Funct C D) (α : NT G H) : NT (funct_comp G F) (funct_comp H F) :=
  vert_nt_comp α (id_nt F)

def whisker_right {F G : Funct C D} (α : NT F G) (H : Funct D E) : NT (funct_comp H F) (funct_comp H G) :=
  vert_nt_comp (id_nt H) α

-- The category of types
def type_cat.{u} : Cat :=
  { obj := Type u
  , mor := (· → ·)
  , iden := λ a => @id a
  , mor_assoc := λ _ _ _ => rfl
  , comp := (· ∘ ·)
  , left_id := λ _ => rfl
  , right_id := λ _ => rfl 
  }

-- Covariant hom functor
def Hom {C : Cat} (c : C) : Funct C type_cat :=
  { map_obj := λ d => C.mor c d
  , map_mor := λ f g => C.comp f g
  , fmap_id := by
      intro _a
      simp
      conv =>
        lhs
        intro g
        rw [C.left_id]
  , fmap_law := by
      intro a b d f g
      simp
      have comp_def a b c (x : b → c) (y : a → b) : type_cat.comp x y = x ∘ y := by rfl 
      rw [comp_def]
      have arg_def : ((fun g => C.comp f g) ∘ fun (g_1 : C.mor c a) => C.comp g g_1) = fun g_1 => C.comp f (C.comp g g_1) := by rfl
      rw [arg_def]
      conv =>
        lhs
        intro g1
        rw [C.mor_assoc]
  }

def precomp_hom {C : Cat} {c d : C} (f : C.mor c d) : NT (Hom d) (Hom c) :=
  { eta := λ a g => C.comp g f
  , nt_law := by
      intro a b g
      simp
      have comp_def a b c (x : b → c) (y : a → b) : type_cat.comp x y = x ∘ y := by rfl 
      rw [comp_def, comp_def]
      have map_def x y z (f : C.mor y z) : (Hom x).map_mor f = λ g => C.comp f g := by rfl
      rw [map_def, map_def]
      have arg_def : ((fun g => C.comp g f) ∘ fun (g_1 : C.mor d a) => C.comp g g_1)
                      = fun g_1 => C.comp (C.comp g g_1) f := by rfl

      have rearrange : (fun (g_1 : C.mor d a) => C.comp (C.comp g g_1) f)
                      = fun g_1 => C.comp g (C.comp g_1 f)
                      := by conv =>
                              lhs
                              intro g1
                              rw [←C.mor_assoc]

      have un_arg_def : (fun g_1 => C.comp g (C.comp g_1 f))
                      = (fun g_1 => Cat.comp C g g_1) ∘ fun g => Cat.comp C g f
                      := by rfl
      -- can't rw with arg_def for some reason...
      exact Eq.trans arg_def (Eq.trans rearrange un_arg_def)
  }

-- Contravariant hom functor
def ContraHom {C : Cat} (c : C) : ContraFunct C type_cat :=
  { map_obj := λ d => C.mor d c
  , map_mor := λ f g => C.comp g f
  , fmap_id := by
      intro _a
      simp
      conv =>
        lhs
        intro g
        rw [C.right_id]
  , fmap_law := by
      intro a b d f g
      simp
      have comp_def a b c (x : b → c) (y : a → b) : type_cat.comp x y = x ∘ y := by rfl 
      rw [comp_def]
      have arg_def : ((fun g_1 => C.comp g_1 g) ∘ fun (g : C.mor d c) => C.comp g f) = fun g_1 => C.comp (C.comp g_1 f) g := by rfl
      rw [arg_def]
      conv =>
        lhs
        intro g1
        rw [←C.mor_assoc]
  }

-- The category of functors
def funct_cat {Dom Cod : Cat} : Cat :=
  { obj := Funct Dom Cod
  , mor := NT
  , comp := λ α β =>
      { eta := λ x => Cod.comp (α.eta x) (β.eta x)
      , nt_law := λ C => by
          simp
          have l1 := α.nt_law C
          have l2 := β.nt_law C
          sorry
          --rw [←Cod.mor_assoc, l2, Cod.mor_assoc, l1, Cod.mor_assoc] -- this is correct but slow to compile!
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

-- Representable functor
def representable (F : Funct C type_cat) : Prop := ∃ (c : C), nat_iso F (Hom c)

theorem yoneda_lemma :
    ∃ (Φ : ∀ F c, NT (Hom c) F → F.map_obj c)
      (Ψ : ∀ F c, F.map_obj c → NT (Hom c) F),
      ∀ (F : Funct C type_cat) (c : C),
        -- Φ and Ψ form a bijection
        (∀ (d : F.map_obj c), Φ F c (Ψ F c d) = d)
        ∧
        (∀ (α : NT (Hom c) F), Ψ F c (Φ F c α) = α)
        ∧
        -- natural in F
        (∀ G (α : NT (Hom c) F) (β : NT F G),
          Φ G c (funct_cat.comp β α)
            = β.eta c (Φ F c α)
        )
        ∧
        -- natural in c
        (∀ (f : C.mor c d) (α : NT (Hom c) F),
          Φ F d (funct_cat.comp α (precomp_hom f))
            = F.map_mor f (Φ F c α)
        ) :=
  ⟨ λ _F c nt => nt.eta c (C.iden c)
  , ⟨ λ F c fc =>
        { eta := λ _a ca => F.map_mor ca fc
        , nt_law := by
            intro a b f
            simp
            have comp_def a b c (x : b → c) (y : a → b) : type_cat.comp x y = x ∘ y := by rfl 
            rw [comp_def, comp_def]
            have c_comp y : (Hom c).map_mor f y = C.comp f y := by rfl
            conv =>
              lhs
              intro x
              simp
              rw [c_comp, ←F.fmap_law]
        }
    , by
      intro F c
      constructor
      . sorry
      . constructor
        . sorry
        . constructor
          . sorry
          . sorry
    ⟩⟩

structure Adjunction (L : Funct C D) (R : Funct D C) where
  unit : NT (I C) (funct_comp R L)
  counit : NT (funct_comp L R) (I D)
  -- triangle identities
  tri_L : id_nt L = funct_cat.comp (whisker_left L counit) (whisker_right unit L)
  tri_R : id_nt R = funct_cat.comp (whisker_right counit R) (whisker_left R unit)