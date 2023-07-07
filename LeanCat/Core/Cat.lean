-- Small category
structure Cat.{u1, u2} where
  obj : Sort u1
  mor : obj → obj → Sort u2
  comp : {a b c : obj} → mor b c → mor a b → mor a c
  iden : (a : obj) → mor a a
  comp_assoc : ∀ {a b c d} (f : mor c d) (g : mor b c) (h : mor a b),
              comp f (comp g h) = comp (comp f g) h
  left_id : ∀ {a b} (f : mor a b), comp (iden b) f = f
  right_id : ∀ {a b} (f : mor a b), comp f (iden a) = f

-- Opposite category
def Op.{u1, u2} (C : Cat.{u1, u2}) : Cat.{u1, u2} :=
  { obj := C.obj
  , mor := λ a b => C.mor b a
  , comp := λ f g => C.comp g f
  , iden := C.iden
  , comp_assoc := by
      intros
      simp
      rw [C.comp_assoc]
  , left_id := by
      intros
      simp
      rw [C.right_id]
  , right_id := by
      intros
      simp
      rw [C.left_id]
  }

theorem op_op : ∀ C, Op (Op C) = C := by
  intro C
  rfl

--instance : CoeSort Cat (Sort u1) where
  --coe C := C.obj