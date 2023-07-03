import LeanCat.Funct
import LeanCat.Cat.Funct

theorem yoneda_lemma :
    ∃ (Φ : ∀ F c, NT (Hom c) F → F.map_obj c)
      (Ψ : ∀ F c, F.map_obj c → NT (Hom c) F),
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
        (∀ (f : C.mor c d) (α : NT (Hom c) F),
          Φ F d (funct_cat.comp α (precomp_hom f))
            = F.map_mor f (Φ F c α)
        ) :=
  ⟨ λ _F c nt => nt.eta c (C.iden c)
  , λ F c fc =>
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
        . intro f α
          simp
          have eta_def : NT.eta (Cat.comp funct_cat α (precomp_hom f)) d
                        = α.eta d ∘ (λ g => C.comp g f) := by rfl
          rw [eta_def]
          simp
          rw [C.left_id]
          have rw_lem : F.map_mor f (α.eta c (C.iden c)) = (type_cat.comp (F.map_mor f) (α.eta c)) (C.iden c) := by rfl
          rw [rw_lem, ←α.nt_law]
          have rw_lem2 : type_cat.comp (α.eta d) ((Hom c).map_mor f) (C.iden c) = α.eta d (C.comp f (C.iden c)) := by rfl
          rw [rw_lem2, C.right_id]
    ⟩

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
  ∀ (C : Cat.{u1+1, u2+1}),
    @fully_faithful'.{u1+1, u2, max (u2+2) (u1+1), max u1 u2}
      C
      (presheaves.{u1+1, u2} C)
      (yoneda_embedding.{u1+1, u2} C) := by
  intro C
  constructor
  . simp [full]
    intro a b
    sorry
    --intro a b
    --simp [surjective]
    --intro m
    --simp [yoneda_embedding, precomp_hom]
    --simp [presheaves, yoneda_embedding, ContraHom', ContraHom, funct_cat] at m
    --have h := m.eta a (C.iden a)
    --simp [Hom, Op] at h
    --exists h
    ----simp [Op]
    --simp [Op]
    --have h2 := m.nt_law h
    --simp [Hom, Op, type_cat] at h2
    --have h3 := m.nt_law (C.iden a) 
    --sorry
    --exists (m (C.iden b))
    --simp [presheaves, yoneda_embedding, ContraHom', ContraHom, Hom, funct_cat] at m

  . sorry -- simp [faithful]