import LeanCat.Funct
import LeanCat.Cat.Funct
import LeanCat.Cat

structure Yoneda (C : Cat) where
  Φ : ∀ (F : Funct C type_cat) c, NT (Hom c) F → F.map_obj c
  Ψ : ∀ (F : Funct C type_cat) c, F.map_obj c → NT (Hom c) F
  laws :
    ∀ (F : Funct C type_cat) (c : C.obj),
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
      (∀ {d : C.obj} (f : C.mor c d) (α : NT (Hom c) F),
        Φ F d (funct_cat.comp α (precomp_hom f))
          = F.map_mor f (Φ F c α)
      )

def yoneda_lemma (C : Cat) : Yoneda C :=
  { Φ := λ _F c nt => nt.eta c (C.iden c)
  , Ψ := λ F c fc =>
        { eta := λ _a ca => F.map_mor ca fc
        , nt_law := by
            intro a b f
            simp
            simp [type_cat, Hom]
            conv =>
              lhs
              intro x
              simp
              rw [←F.fmap_law]
        }
  , laws := by
      intro F c
      constructor
      . intro d
        simp
        rw [F.fmap_id]
        rfl
      . constructor
        . intro α
          simp
          have rw_lem a (ca : C.mor c a) : F.map_mor ca (α.eta c (C.iden c)) = type_cat.comp (F.map_mor ca) (α.eta c) (C.iden c) := by rfl
          have rw_lem2 a (ca : C.mor c a) : type_cat.comp (α.eta a) ((Hom c).map_mor ca) (C.iden c) = α.eta a (C.comp ca (C.iden c)) := by rfl
          conv =>
            lhs
            arg 1
            intro a ca
            rw [rw_lem, ←α.nt_law, rw_lem2, C.right_id]
        . constructor
          . intro G α β 
            rfl
          . intro d f α
            simp [*, funct_cat, precomp_hom, type_cat]
            rw [C.left_id]
            have rw_lem : F.map_mor f (α.eta c (C.iden c)) = (type_cat.comp (F.map_mor f) (α.eta c)) (C.iden c) := by rfl
            rw [rw_lem, ←α.nt_law]
            have rw_lem2 : type_cat.comp (α.eta d) ((Hom c).map_mor f) (C.iden c) = α.eta d (C.comp f (C.iden c)) := by rfl
            rw [rw_lem2, C.right_id]
  }

def yoneda_embedding.{u1, u2} (C : Cat.{u1, u2+1}) : Funct.{u1, u2+1} C (presheaves.{u1, u2} C) :=
  { map_obj := λ a => ContraHom' a
  , map_mor := λ m => precomp_hom m
  , fmap_id := by
      intro a
      simp [*, precomp_hom]
      conv =>
        lhs
        arg 1
        simp [Op]
        intro a g
        rw [C.left_id]
      simp [presheaves, ContraHom', ContraHom, Hom, funct_cat]
      conv =>
        rhs
        intro a g
        rw [(Op C).left_id]
  , fmap_law := by
      intro a b c f g
      simp [*, presheaves, precomp_hom, funct_cat, type_cat, Op]
      conv =>
        lhs
        intro x
        intro g_1
        simp
        rw [C.comp_assoc]
  }

theorem yoneda_embedding_fully_faithful :
  ∀ (C : Cat.{u1, u1+1}),
    @fully_faithful
      C
      (presheaves C)
      (yoneda_embedding C) := by
  intro C
  simp [fully_faithful]
  constructor
  . simp [full]
    intro a b
    simp [surjective]
    intro m
    simp [presheaves, funct_cat, yoneda_embedding, ContraHom', ContraHom] at m
    simp [yoneda_embedding]
    let y := yoneda_lemma (Op C)
    let n := y.Φ (Hom b) a m
    simp [Hom] at n
    exists n
    have lem : precomp_hom n = y.Ψ (Hom b) a n := by
      simp [precomp_hom, yoneda_lemma, Hom]
    have y_lem := (y.laws (Hom b) a).2.1 m
    rw [lem, y_lem]
  . simp [faithful]
    intro a b
    simp [injective]
    intro m n h
    simp [yoneda_embedding] at h
    let y := yoneda_lemma (Op C)
    have lem f : @precomp_hom (Op C) b a f = y.Ψ (@Hom (Op C) b) a f := by
      simp [precomp_hom, yoneda_lemma, Hom]
    rw [lem m, lem n] at h
    have h2 := congrArg (y.Φ (Hom b) a) h
    have y_lem := (y.laws (Hom b) a).1
    rw [y_lem m, y_lem n] at h2
    exact h2

theorem yoneda_embed_sub_cat (C : Cat.{u1, u1+1}) : full_sub_cat C (presheaves C) := by
  exists yoneda_embedding C
  exact yoneda_embedding_fully_faithful C

def cat_of_elems' (F : Funct C type_cat) : Cat :=
      comma_cat' (yoneda_embedding (Op C)) (Const (presheaves (Op C)) F)

def slice_cat' {C : Cat} (c : C.obj) : Cat := cat_of_elems' (Hom c)

def forget_slice {C : Cat} {c : C.obj} : Funct (slice_cat' c) (Op C) :=
  { map_obj := λ o => by
      simp [cat_of_elems', slice_cat', comma_cat'] at o
      exact o.left
  , map_mor := λ m => by
      simp
      exact m.dm
  , fmap_id := by
      intro a
      simp [*, slice_cat', cat_of_elems', comma_cat']
  , fmap_law := by
      intro a b c f g
      simp [*, slice_cat', cat_of_elems', comma_cat']
  }