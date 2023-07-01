import LeanCat.Core
import LeanCat.Cat.Funct
import LeanCat.Cat.Set

def monomorphism {C : Cat} {a b : C.obj} (m : C.mor a b) : Prop :=
  ∀ {a'} (n p : C.mor a' a), C.comp m n = C.comp m p → n = p

def epimorphism {C : Cat} {a b : C.obj} (m : C.mor a b) : Prop :=
  ∀ {b'} (n p : C.mor b b'), C.comp n m = C.comp p m → n = p

def isomorphism {C : Cat} {a b : C.obj} (m : C.mor a b) : Prop :=
  ∃ (n : C.mor b a), C.comp n m = C.iden a ∧ C.comp m n = C.iden b

def endomorphism {C : Cat} {a b : C.obj} (_ : C.mor a b) : Prop := a = b

def automorphism {C : Cat} {a b : C.obj} (m : C.mor a b) : Prop := isomorphism m ∧ endomorphism m

-- a natural isomorphism between functors
-- TODO what can be done about these universe params?
def nat_iso {C : Cat.{u1 + 1, u1}} {D : Cat.{u2 + 1, u2}} (F : Funct C D) (G : Funct C D) : Prop :=
  ∃ (α : NT F G), @isomorphism funct_cat F G α

theorem mono_mono {C : Cat} {a b c : C.obj} : ∀ (m : C.mor a b) (n : C.mor b c),
    monomorphism m → monomorphism n → monomorphism (C.comp n m) := by
  intro m n monoM monoN _x _o _p h
  rw [←C.comp_assoc, ←C.comp_assoc] at h
  have h2 := monoN _ _ h
  exact monoM _ _ h2

theorem mono_impl_mono {C : Cat} {a b c : C.obj} : ∀ (m : C.mor a b) (n : C.mor b c),
    monomorphism (C.comp n m) → monomorphism m := by
  intro m n mono x p q h
  have h2 := congrArg (C.comp n) h
  rw [C.comp_assoc, C.comp_assoc] at h2
  exact mono p q h2

theorem epi_epi {C : Cat} {a b c : C.obj} : ∀ (m : C.mor a b) (n : C.mor b c),
    epimorphism m → epimorphism n → epimorphism (C.comp n m) := by
  intro m n epiM epiN x p o h
  rw [C.comp_assoc, C.comp_assoc] at h
  have h2 := epiM _ _ h
  exact epiN _ _ h2

theorem epi_impl_epi {C : Cat} {a b c : C.obj} : ∀ (m : C.mor a b) (n : C.mor b c),
    epimorphism (C.comp n m) → epimorphism n := by
  intro m n epiC x o p h
  have h2 := congrArg (λ x => C.comp x m) h
  simp at h2
  rw [←C.comp_assoc, ←C.comp_assoc] at h2
  exact epiC o p h2

theorem iso_impl_epi_mono {C : Cat} {a b : C.obj} : ∀ (m : C.mor a b),
    isomorphism m → epimorphism m ∧ monomorphism m := by
  intro m ⟨n, hl, hr⟩
  constructor
  . intro x o p h2
    have h3 := congrArg (λ f => C.comp f n) h2
    simp at h3
    rw [←C.comp_assoc, ←C.comp_assoc, hr, C.right_id, C.right_id] at h3
    exact h3
  . intro x o p h2
    have h3 := congrArg (C.comp n) h2
    rw [C.comp_assoc, C.comp_assoc, hl, C.left_id, C.left_id] at h3
    exact h3

theorem epi_mono_factor {C : Cat} {a b : C.obj} : ∀ (m : C.mor a b) (n : C.mor b a),
    C.comp n m = C.iden a → monomorphism m ∧ epimorphism n := by
  intro m n h
  constructor
  . intro x p q h2
    have h3 := congrArg (C.comp n) h2
    rw [C.comp_assoc, C.comp_assoc, h, C.left_id, C.left_id] at h3
    exact h3
  . intro x p q h2
    have h3 := congrArg (λ f => C.comp f m) h2
    simp at h3
    rw [←C.comp_assoc, ←C.comp_assoc, h, C.right_id, C.right_id] at h3
    exact h3

def injective {A B : type_cat.obj} (f : A → B) : Prop := ∀ (x y : A) (z : B), f x = z ∧ f y = z → x = y
def surjective {A B : type_cat.obj} (f : A → B) : Prop := ∀ (x : B), ∃ (y : A), f y = x

theorem mono_inj_post {C : Cat} {a b : C.obj} (f : C.mor a b) :
    monomorphism f ↔ (∀ c, injective (λ (g : C.mor c a) => C.comp f g)) := by
  constructor
  . intro mono _ x y _ h
    simp at h
    have ⟨hl, hr⟩ := h
    exact mono x y (hl.trans hr.symm)
  . intro h x n p h2
    have h3 := h x n p (C.comp f p)
    simp at h3
    exact h3 h2

theorem epi_inj_pre {C : Cat} {a b : C.obj} (f : C.mor a b) :
    epimorphism f ↔ (∀ c, injective (λ (g : C.mor b c) => C.comp g f)) := by
  constructor
  . intro epi c x y z h
    simp at h
    have ⟨hl, hr⟩ := h
    exact epi x y (hl.trans hr.symm)
  . intro h x n p h2
    have h3 := h x n p (C.comp n f)
    simp at h3
    exact h3 h2.symm