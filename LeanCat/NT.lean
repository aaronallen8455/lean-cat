import LeanCat.Core

def id_nt (F : Funct C D) : NT F F :=
  { eta := λ a => F.map_mor (C.iden a)
  , nt_law := by
      intros
      simp
      rw [F.fmap_id, D.left_id, F.fmap_id, D.right_id]
  }

def horiz_nt_comp {A B C : Cat} {F₁ G₁ : Funct A B} {F₂ G₂ : Funct B C}
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
         , ←C.comp_assoc
         , F₂.fmap_law
         , β.nt_law fab
         , ←F₂.fmap_law
         , C.comp_assoc
         , α.nt_law (G₁.map_mor fab)
         , ←C.comp_assoc
         , α.nt_law (β.eta a)
         ]
      rfl
  }

def whisker_left (F : Funct C D) (α : NT G H) : NT (funct_comp G F) (funct_comp H F) :=
  horiz_nt_comp α (id_nt F)

def whisker_right {F G : Funct C D} (α : NT F G) (H : Funct D E) : NT (funct_comp H F) (funct_comp H G) :=
  horiz_nt_comp (id_nt H) α