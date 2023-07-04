import LeanCat.Cat.Set
import LeanCat.Mor

-- Identity functor
def I (C : Cat) : Funct C C :=
  { map_obj := id
  , map_mor := id
  , fmap_id := by simp
  , fmap_law := by simp
  }

-- Covariant hom functor
def Hom {C : Cat.{u1, u2+1}} (c : C.obj) : Funct C type_cat.{u2} :=
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
        rw [C.comp_assoc]
  }

def precomp_hom {C : Cat} {c d : C.obj} (f : C.mor c d) : NT (Hom d) (Hom c) :=
  { eta := λ _a g => C.comp g f
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
                              rw [←C.comp_assoc]

      have un_arg_def : (fun g_1 => C.comp g (C.comp g_1 f))
                      = (fun g_1 => Cat.comp C g g_1) ∘ fun g => Cat.comp C g f
                      := by rfl
      -- can't rw with arg_def for some reason...
      exact Eq.trans arg_def (Eq.trans rearrange un_arg_def)
  }

-- Contravariant hom functor
def ContraHom {C : Cat} (c : C.obj) : ContraFunct C type_cat := Hom c

def ContraHom' {C : Cat} (c : C.obj) : Funct (Op C) type_cat := @ContraHom C c

-- Representable functor
def representable (F : Funct C type_cat) : Prop := ∃ (c : C.obj), nat_iso F (Hom c)

def full.{u1, u2, u3, u4} {C : Cat.{u1, u2+1}} {D : Cat.{u3, u4+1}} (F : Funct C D) : Prop :=
  ∀ a b, surjective (λ (f : C.mor a b) => F.map_mor f)

def faithful.{u1, u2, u3, u4} {C : Cat.{u1, u2+1}} {D : Cat.{u3, u4+1}} (F : Funct C D) : Prop :=
  ∀ a b, injective (λ (f : C.mor a b) => F.map_mor f)

def fully_faithful.{u1, u2, u3, u4} {C : Cat.{u1, u2+1}} {D : Cat.{u3, u4+1}} (F : Funct C D) : Prop :=
  full.{u1, u2, u3} F ∧ faithful.{u1, u2, u3} F