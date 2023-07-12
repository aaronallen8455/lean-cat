import LeanCat.Core
import LeanCat.Funct
import LeanCat.Cat
import LeanCat.Yoneda

-- TODO define in terms of Kan extensions instead?

structure Cone {C : Cat} {D : Cat} (F : Funct C D) where
  lim : D.obj
  legs : NT (Const C lim) F

def get_leg {C : Cat} {D : Cat} {F : Funct C D}
      (n : Cone F) (c : C.obj) : D.mor n.lim (F.map_obj c) := n.legs.eta c

structure Lim {C : Cat} {D : Cat} (F : Funct C D) extends Cone F where
  univ_prop : ∀ (l : Cone F), ∃ (m : D.mor l.lim lim), ∀ (n : D.mor l.lim lim), m = n

def Colim {C : Cat} {D : Cat} (F : Funct C D) := Lim (FOp F)

def initial (C : Cat) := Lim (I C)

def has_initial_obj (C : Cat) : Prop := ∃ (_ : initial C), true

def terminal (C : Cat) := Colim (I C)

def has_terminal_obj (C : Cat) : Prop := ∃ (_ : terminal C), true

def preserves_lims.{u1, u2, u3, u4, u5, u6} {C : Cat.{u1, u2}} {D : Cat.{u3, u4}}
    (F : Funct C D) : Prop :=
  ∀ {J : Cat.{u5, u6}} (G : Funct J C) (l : Lim G), ∃ (lfg : Lim (funct_comp F G)),
    lfg.lim = F.map_obj l.lim

def preserves_colims.{u1, u2, u3, u4, u5, u6} {C : Cat.{u1, u2}} {D : Cat.{u3, u4}}
    (F : Funct C D) : Prop :=
  ∀ {J : Cat.{u5, u6}} (G : Funct J C) (l : Colim G), ∃ (lfg : Colim (funct_comp F G)),
    lfg.lim = F.map_obj l.lim

def reflects_lims.{u1, u2, u3, u4, u5, u6} {C : Cat.{u1, u2}} {D : Cat.{u3, u4}} (F : Funct C D) : Prop :=
  ∀ {J : Cat.{u5, u6}} (G : Funct J C) (c : Cone G) (l : Lim (funct_comp F G)),
    l.lim = F.map_obj c.lim → ∃ (lg : Lim G), lg.toCone = c

def creates_lims.{u1,u2,u3,u4,u5,u6} {C : Cat.{u1, u2}} {D : Cat.{u3, u4}} (F : Funct C D) : Prop
  := preserves_lims.{u1,u2,u3,u4,u5,u6} F ∧ reflects_lims.{u1,u2,u3,u4,u5,6} F

theorem lim_colim_duals : ∀ {C : Cat} {D : Cat} (F : Funct C D), Lim F = Colim (FOp F) := by
  intro C D F
  simp [Colim, FOp]
  conv =>
    rhs

-- Riehl 2.4.8
theorem univ_elems : ∀ (F : Funct C type_cat),
    representable F ↔ has_initial_obj (cat_of_elems F) := by
  intro F
  constructor
  . intro ⟨c, ⟨α, β, h⟩⟩
    simp [funct_cat] at h
    let clim := DepPair.mk c (β.eta c (C.iden c))
    have term : initial (cat_of_elems F) :=
      { lim := clim
      , legs :=
          { eta := by
              intro ⟨d, x⟩
              simp [Op, cat_of_elems, FOp, I, Const]
              let f : C.mor c d := α.eta d x
              exists f
              have l : Funct.map_mor F f (β.eta c (C.iden c)) = (type_cat.comp (Funct.map_mor F f) (β.eta c)) (C.iden c) := rfl
              rw [l, ←β.nt_law f]
              simp [Hom]
              have l2 : type_cat.comp (β.eta d) (fun g => Cat.comp C (NT.eta α d x) g) (Cat.iden C c)
                      = (β.eta d) (C.comp (α.eta d x) (C.iden c))
                      := rfl
              rw [l2, C.right_id]
              have l3 : NT.eta β d (NT.eta α d x)
                      = (λ z => type_cat.comp (β.eta z) (α.eta z)) d x
                      := rfl
              rw [l3, h.1]
              simp
              rw [F.fmap_id]
              simp [type_cat]
          , nt_law := by simp
          }
      , univ_prop := by
          simp
          intro l
          exists l.legs.eta clim
      }
    exists term
  . intro ⟨init, _⟩
    simp [initial] at init
    simp [representable]
    let ⟨c, fc⟩ := init.lim
    exists c
    simp [nat_iso]
    have α : NT F (Hom c) :=
      { eta := by
          simp [Hom]
          intro a
          intro fa
          let h := init.legs.eta ⟨a, fa⟩
          simp [Const, I, cat_of_elems] at h
          --let y := (yoneda_lemma C).Ψ F c fc
          --let y2 := (yoneda_lemma C)
          
      , nt_law := sorry
      }
    exists α
    constructor
    . sorry
    . sorry
