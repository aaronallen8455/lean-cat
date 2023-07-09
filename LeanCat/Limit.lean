import LeanCat.Core
import LeanCat.Funct
import LeanCat.Cat

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

def terminal (C : Cat) := Colim (I C)

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