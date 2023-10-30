import LeanCat.NT
import LeanCat.Funct
import LeanCat.Limit
import LeanCat.Funct.MultiVar
import LeanCat.UnivProp

structure Adjunction (L : Funct C D) (R : Funct D C) where
  unit : NT (I C) (funct_comp R L)
  counit : NT (funct_comp L R) (I D)
  -- triangle identities
  tri_L : id_nt L = funct_cat.comp (whisker_left L counit) (whisker_right unit L)
  tri_R : id_nt R = funct_cat.comp (whisker_right counit R) (whisker_left R unit)

def adj_op {C : Cat} {D : Cat} {L : Funct C D} {R : Funct D C}
           (adj : Adjunction L R)
    : Adjunction (FOp R) (FOp L) :=
  { unit := op_nt adj.counit
  , counit := op_nt adj.unit
  , tri_L := by
      have h := adj.tri_R
      have coun a := adj.counit.nt_law (D.iden a)
      simp [funct_comp] at coun
      conv at h =>
        simp [whisker_right, whisker_left, horiz_nt_comp, funct_cat, id_nt]
        conv =>
          lhs
          intro a
          rw [R.fmap_id]
        conv =>
          rhs
          intro x
          simp [funct_comp]
          rw [R.fmap_id, C.right_id, C.comp_assoc, R.fmap_law, coun]
          simp [I]
          rw [D.left_id]
      simp [whisker_left, whisker_right, horiz_nt_comp, funct_cat, id_nt, I, Op, FOp]
      conv =>
        lhs
        intro a
        rw [R.fmap_id]
      conv =>
        rhs
        intro x
        rw [R.fmap_id, C.left_id, ←op_nt_eq, ←op_nt_eq]
        arg 3
        simp [funct_comp]
        rw [C.right_id]
      exact h
  , tri_R := by
      -- TODO factor out a proof of triangle ID equality and use for both tri_L and tri_R
      have h := adj.tri_L
      conv at h =>
        simp [whisker_left, whisker_right, horiz_nt_comp, funct_cat, id_nt, I]
        conv =>
          rhs
          intro x
          simp [funct_comp]
          rw [L.fmap_id, D.left_id, D.right_id]
      simp [whisker_left, whisker_right, horiz_nt_comp, funct_cat, id_nt]
      conv =>
        lhs
        intro a
        simp [FOp, Op]
      have un a := adj.unit.nt_law (C.iden a)
      simp [funct_comp] at un
      conv =>
        rhs
        intro x
        simp [Op, funct_comp, FOp]
        rw [L.fmap_law, C.left_id, ←D.comp_assoc, L.fmap_law, ←op_nt_eq, ←op_nt_eq, ←un]
        simp [I, C.right_id]
      exact h
  }

theorem adj_right_preserve_lim {C : Cat} {D : Cat} {L : Funct C D} {R : Funct D C} (adj : Adjunction L R) : preserves_lims R := by
  simp [preserves_lims]
  intro J G l
  let lfg : Lim (funct_comp R G) :=
    { lim := R.map_obj l.lim
    , legs :=
      { eta := λ a => R.map_mor $ get_leg l.toCone a
      , nt_law := by
          intro a b mor
          simp
          have h := l.legs.nt_law mor
          simp [Const]
          rw [C.right_id]
          simp [funct_comp, get_leg]
          rw [R.fmap_law, ←h]
          simp [Const]
          rw [D.right_id]
      }
    , univ_prop := by
        intro oc
        let occ : Cone (funct_comp (funct_comp L R) G) :=
          { lim := L.map_obj oc.lim
          , legs :=
              let h : NT (funct_comp L (Const J oc.lim)) (funct_comp L (funct_comp R G))
                    = NT (Const J (Funct.map_obj L oc.lim)) (funct_comp (funct_comp L R) G) := by
                        rw [funct_comp_assoc]
                        have l : funct_comp L (Const J oc.lim) = Const J (Funct.map_obj L oc.lim) := by
                          simp [Const, funct_comp]
                          constructor
                          . rfl
                          . rw [←L.fmap_id]
                            rfl
                        rw [l]
              cast h $ whisker_right oc.legs L
          }
        have ls := funct_cat.comp (whisker_left G adj.counit) occ.legs
        let occc : Cone G :=
          { lim := occ.lim
          , legs := ls
          }
        have ⟨m, h⟩ := l.univ_prop occc
        let m' := R.map_mor m
        let need : Cat.mor C oc.lim (Funct.map_obj (funct_comp R L) oc.lim) :=
              adj.unit.eta oc.lim
        let the_one : C.mor oc.lim (Funct.map_obj R l.lim) := C.comp m' need
        exists the_one
        intro n
        let toLim := adj.counit.eta l.lim
        let n' := D.comp toLim (L.map_mor n)
        have h2 := congrArg ((C.comp · need) ∘ R.map_mor) $ h n'
        simp at h2
        have the_one_def : Cat.comp C (Funct.map_mor R m) (NT.eta adj.unit oc.lim) = the_one := rfl
        rw [the_one_def] at h2

        let need2 :
              Cat.comp C (Funct.map_mor R (Cat.comp D (NT.eta adj.counit l.lim) (Funct.map_mor L n))) (NT.eta adj.unit oc.lim)
              = n := by
              { have fc : R.map_mor (L.map_mor n) = (funct_comp R L).map_mor n := rfl
                rw [←R.fmap_law, ←C.comp_assoc, fc, ←adj.unit.nt_law n]
                simp [*, I]
                rw [C.comp_assoc]
                have test : id_nt R = funct_cat.comp (whisker_right adj.counit R) (whisker_left R adj.unit) := adj.tri_R
                have test2 := congrArg (NT.eta · l.lim) test
                simp at test2
                simp [id_nt, whisker_left, whisker_right, funct_cat, horiz_nt_comp] at test2
                rw [R.fmap_id, ←adj.unit.nt_law (Cat.iden C (Funct.map_obj R l.lim))] at test2
                simp [I] at test2
                rw [C.right_id, R.fmap_id, ←C.comp_assoc] at test2
                conv at test2 =>
                  rhs
                  simp [funct_comp]
                  rw [C.left_id]
                rw [←test2, C.left_id]
              }
        rw [need2] at h2
        exact h2
    }
  exists lfg

theorem adj_left_preserve_colim {L : Funct C D} (adj : Adjunction L R) : preserves_colims L := by
  simp [preserves_colims]
  intro J G l
  simp [Colim] at l
  have opAdj := adj_op adj
  let h : preserves_lims (FOp L) := adj_right_preserve_lim opAdj
  simp [preserves_lims, FOp] at h
  exact h (FOp G) l

theorem adj_lim_preservation {L : Funct C D} (adj : Adjunction L R)
    : preserves_lims R ∧ preserves_colims L :=
  ⟨adj_right_preserve_lim adj, adj_left_preserve_colim adj⟩

-- Given two abutting adjunctions, there is a cannonicle adjunction of the endofunctors
-- resulting from these functor compositions.
-- Riehl exercise 4.1.iii
theorem adj_triple_endo : ∀ (U : Funct C D) (L R : Funct D C),
    Adjunction L U → Adjunction U R → Adjunction (funct_comp L U) (funct_comp R U) := by
  intro U L R adjLU adjUR
  exact { unit := by
            have h1 := whisker_right (whisker_left U adjLU.unit) R
            have h2 := funct_cat.comp h1 adjUR.unit
            exact h2
        , counit := by
            have h1 := whisker_right (whisker_left U adjUR.counit) L
            have h2 := funct_cat.comp adjLU.counit h1
            exact h2
        , tri_L := by
            have h2 := adjUR.tri_L
            simp [id_nt, funct_cat, funct_comp, whisker_left, whisker_right, horiz_nt_comp, I] at h2
            conv at h2 =>
              rhs
              intro x
              rw [U.fmap_id, D.left_id, D.right_id]
            have h3 := adjLU.tri_L
            simp [id_nt, funct_cat, funct_comp, whisker_left, whisker_right, horiz_nt_comp, I] at h3
            conv at h3 =>
              rhs
              intro x
              rw [L.fmap_id, C.left_id, C.right_id]
            simp [*, id_nt, funct_cat, funct_comp, whisker_left, whisker_right, horiz_nt_comp, I]
            have lem {a b} (m : D.mor a b) : U.map_mor (R.map_mor m) = (funct_comp U R).map_mor m := by rfl
            conv =>
              rhs
              intro x
              rw [U.fmap_id, L.fmap_id, C.left_id, R.fmap_id, C.right_id, C.right_id]
              rw [←congrFun h2, U.fmap_id, D.left_id, ←congrFun h2, U.fmap_id, L.fmap_id, U.fmap_id, D.left_id]
              rw [←congrFun h3, L.fmap_id, C.right_id]
              rw [←C.comp_assoc, L.fmap_law]
              rw [←U.fmap_law, D.comp_assoc, lem, adjUR.counit.nt_law]
              simp [I]
              rw [←D.comp_assoc, ←congrFun h2, U.fmap_id, D.right_id]
              rw [←congrFun h3, ←U.fmap_id]
        , tri_R := by
            have h2 := adjUR.tri_R
            simp [id_nt, funct_cat, funct_comp, whisker_left, whisker_right, horiz_nt_comp, I] at h2
            conv at h2 =>
              rhs
              intro x
              rw [R.fmap_id, C.right_id, R.fmap_id, U.fmap_id, R.fmap_id, C.left_id]
            have h3 := adjLU.tri_R
            simp [id_nt, funct_cat, funct_comp, whisker_left, whisker_right, horiz_nt_comp, I] at h3
            conv at h3 =>
              rhs
              intro x
              rw [U.fmap_id, D.right_id, U.fmap_id, L.fmap_id, U.fmap_id, D.left_id]

            simp [*, id_nt, funct_cat, funct_comp, whisker_left, whisker_right, horiz_nt_comp, I]
            have lem {a b} (m : D.mor a b) : U.map_mor (L.map_mor m) = (funct_comp U L).map_mor m := by rfl
            conv =>
              rhs
              intro x
              rw [L.fmap_id, C.right_id, U.fmap_id, R.fmap_id, C.right_id, U.fmap_id, R.fmap_id
                 ,U.fmap_id, L.fmap_id, U.fmap_id, R.fmap_id, C.left_id]
              rw [←congrFun h2, R.fmap_id, C.right_id, ←congrFun h3, U.fmap_id, D.left_id
                 ,←congrFun h3, U.fmap_id, L.fmap_id, U.fmap_id, D.left_id]
              rw [C.comp_assoc, R.fmap_law, ←U.fmap_law]
              rw [←D.comp_assoc, lem, ←adjLU.unit.nt_law]
              simp [I]
              rw [D.comp_assoc, ←congrFun h3, U.fmap_id, D.left_id, ←congrFun h2]
            conv =>
              lhs
              intro a
              rw [U.fmap_id]
        }

def extract_lam : ∀ {l r : α → β}, (∀ x, l x = r x) → (fun x => l x) = (fun x => r x) := by
  intro l r h
  conv =>
    lhs
    intro x
    rw [h x]

-- Alternate definition using equality of hom sets instead of natural transformations
structure Adjunction' (L : Funct C D) (R : Funct D C) where
  m : ∀ c d, (C.mor c (R.map_obj d)) → (D.mor (L.map_obj c) d)
  n : ∀ c d, (D.mor (L.map_obj c) d) → (C.mor c (R.map_obj d))
  iso : ∀ c d, n c d ∘ m c d = id ∧ m c d ∘ n c d = id
  -- the collection of isomorphisms is natural in C and D:
  nat_C : ∀ {c c'} {d} (f : D.mor (L.map_obj c) d) (h : C.mor c' c),
    C.comp (n c d f) h = n c' d (D.comp f (L.map_mor h))
  nat_D : ∀ {c} {d d'} (f : D.mor (L.map_obj c) d) (k : D.mor d d'),
    C.comp (R.map_mor k) (n c d f) = n c d' (D.comp k f)

structure Adjunction''' (L : Funct C D) (R : Funct D C) where
  n : NT (funct_comp (BiHom C) (FunctProd (I (Op C)) R))
         (funct_comp (BiHom D) (FunctProd (FOp L) (I D)))
  m : NT (funct_comp (BiHom D) (FunctProd (FOp L) (I D)))
         (funct_comp (BiHom C) (FunctProd (I (Op C)) R))
  -- Components of the NT are isomorphisms
  iso : ∀ c d, n.eta (c, d) ∘ m.eta (c, d) = id
             ∧ m.eta (c, d) ∘ n.eta (c, d) = id

def jeez {L : Funct C D} (adj : Adjunction''' L R) : Adjunction' L R :=
  { m := λ c d => adj.n.eta (c, d)
  , n := λ c d => adj.m.eta (c, d)
  , iso := by
      intro c d
      apply And.intro
      . simp
        exact (adj.iso c d).2
      . simp
        exact (adj.iso c d).1
  , nat_C := by
      intro c c' d f h
      simp
      let hhh := adj.m.nt_law ((h, D.iden _) : (prod (Op C) D).mor (c, d) (c', d))
      simp [BiHom, prod, Op, funct_comp, type_cat, FunctProd, I] at hhh
      let hhh' := congrFun hhh f
      simp [*, FOp] at hhh'
      rw [D.left_id, R.fmap_id, C.left_id] at hhh'
      exact hhh'.symm
  , nat_D := by
      intro c d d' f k
      simp
      let hhh := adj.m.nt_law ((C.iden _, k) : (prod (Op C) D).mor (c, d) (c, d'))
      simp [BiHom, prod, Op, funct_comp, type_cat, FunctProd, I] at hhh
      let hhh' := congrFun hhh f
      simp [*, FOp] at hhh'
      rw [L.fmap_id, D.right_id, C.right_id] at hhh'
      exact hhh'.symm
  }

def conv_adj_1'' (L : Funct C D) (R : Funct D C) (adj : Adjunction L R) : Adjunction''' L R :=
  { n := { eta := λ x => by
             simp [BiHom, funct_comp, FunctProd, FOp, I]
             intro f
             let f' := L.map_mor f
             let h := adj.counit.eta x.snd
             exact D.comp h f'
         , nt_law := by
              intro a b mor
              simp [*, type_cat, BiHom, funct_comp, FunctProd, I, FOp]
              conv =>
                lhs
                intro f
                simp
              conv =>
                rhs
                intro f
                simp
              apply extract_lam
              intro f
              let h := adj.counit.nt_law mor.2
              simp [I, funct_comp] at h
              rw [←L.fmap_law, D.comp_assoc, h, D.comp_assoc]
              conv =>
                rhs
                rw [D.comp_assoc, ←D.comp_assoc, L.fmap_law]
         }
  , m := { eta := λ x => by
            simp [BiHom, funct_comp, FunctProd, FOp, I, type_cat]
            intro f
            let f' := R.map_mor f
            let h := adj.unit.eta x.fst
            exact C.comp f' h
         , nt_law := by
            intro a b mor
            simp [*, type_cat, BiHom, funct_comp, FunctProd, I, FOp]
            conv =>
              lhs
              intro f
              simp
            conv =>
              rhs
              intro f
              simp
            apply extract_lam
            intro f
            let h := adj.unit.nt_law mor.1
            simp [I, funct_comp] at h
            rw [C.comp_assoc, C.comp_assoc, ←C.comp_assoc, h, ←R.fmap_law, C.comp_assoc]
            conv =>
              rhs
              rw [←C.comp_assoc, ←C.comp_assoc]
              arg 3
              rw [C.comp_assoc, R.fmap_law]
            rw [C.comp_assoc]
         }
  , iso := by
      intro c d
      simp
      apply And.intro
      . conv =>
          lhs
          intro f
          simp
        conv =>
          rhs
          intro f
        apply extract_lam
        intro f
        simp [BiHom, FunctProd, funct_comp, FOp, I] at f
        rw [←L.fmap_law, D.comp_assoc]
        let hh := adj.counit.nt_law f
        simp [*, I, funct_comp] at hh
        rw [hh]
        let hhh := congrArg (λ n => n.eta c) adj.tri_L
        simp [*, whisker_right, whisker_left, horiz_nt_comp, funct_cat, id_nt, funct_comp, I] at hhh
        rw [L.fmap_id, D.left_id, D.right_id] at hhh
        rw [←D.comp_assoc, ←hhh, D.right_id]
        simp
      . conv =>
          lhs
          intro f
          simp
        conv =>
          rhs
          intro f
          simp
        apply extract_lam
        intro f
        simp [BiHom, FunctProd, funct_comp, FOp, I] at f
        rw [←R.fmap_law, ←C.comp_assoc]
        let hh := adj.unit.nt_law f
        simp [*, I, funct_comp] at hh
        rw [←hh]
        let hhh := congrArg (λ n => n.eta d) adj.tri_R
        simp [*, whisker_right, whisker_left, horiz_nt_comp, funct_cat, id_nt, funct_comp, I] at hhh
        rw [R.fmap_id, R.fmap_id, C.right_id, L.fmap_id, R.fmap_id, C.left_id] at hhh
        rw [C.comp_assoc, ←hhh, C.left_id]
  }

-- Show that the two definitions are equivalent
def conv_adj_1 (L : Funct C D) (R : Funct D C) (adj : Adjunction L R) : Adjunction' L R :=
  { m := λ c d f => D.comp (adj.counit.eta d) (L.map_mor f)
  , n := λ c d f => C.comp (R.map_mor f) (adj.unit.eta c)
  , iso := by
      intro c d
      simp
      constructor
      . conv =>
          lhs
          intro f
          simp
        have h := congrArg (λ α => α.eta d) adj.tri_R
        simp [id_nt, funct_cat, whisker_right, whisker_left, horiz_nt_comp] at h
        rw [R.fmap_id, R.fmap_id] at h
        conv at h =>
          rhs
          rw [(funct_comp R L).fmap_id, C.left_id] 
          arg 2
          rw [C.right_id (R.map_mor (adj.counit.eta d))]
        conv =>
          lhs
          intro f
          rw [←R.fmap_law, ←C.comp_assoc, funct_comp_map, ←adj.unit.nt_law]
          simp [I]
          rw [C.comp_assoc, ←h, C.left_id]

      . conv =>
          lhs
          intro f
          simp
        have h := congrArg (λ α => α.eta c) adj.tri_L
        simp [id_nt, funct_cat, whisker_right, whisker_left, horiz_nt_comp, I] at h
        rw [L.fmap_id, D.left_id] at h
        let hh := D.right_id (L.map_mor (adj.unit.eta c))
        simp [I] at hh
        conv at h =>
          rhs
          arg 3
          rw [hh]
        conv =>
          lhs
          intro f
          rw [←L.fmap_law, D.comp_assoc, funct_comp_map, adj.counit.nt_law]
          simp [I]
          rw [←D.comp_assoc, ←h, D.right_id]
  , nat_D := by
      intro c d d' f k
      simp
      rw [C.comp_assoc, R.fmap_law]
  , nat_C := by
      intro c c' d f h
      simp
      rw [←R.fmap_law]
      conv =>
        rhs
        rw [←C.comp_assoc, funct_comp_map, ←adj.unit.nt_law]
        simp [I]
      rw [C.comp_assoc]
  }

theorem transpose_sqr :
  ∀ {L : Funct C D} {R : Funct D C}
    (adj : Adjunction' L R)
    (c c' : C.obj)
    (d d' : D.obj)
    (h : C.mor c c')
    (k : D.mor d d')
    (f : D.mor (L.map_obj c) d)
    (g : D.mor (L.map_obj c') d'),
      D.comp k f = D.comp g (L.map_mor h)
    ↔ C.comp (R.map_mor k) (adj.n c d f) = C.comp (adj.n c' d' g) h := by
  intro L R adj c c' d d' h k f g
  constructor
  . intro hyp
    rw [adj.nat_D, hyp, ←adj.nat_C]
  . intro hyp
    rw [adj.nat_D, adj.nat_C] at hyp
    have hyp' := congrArg (λ f => adj.m c d' f) hyp
    simp at hyp'
    have blah : ∀ z, adj.m c d' (adj.n c d' z) = (adj.m c d' ∘ adj.n c d') z := by {intros; rfl}
    rw [blah, (adj.iso c d').2] at hyp'
    simp at hyp'
    rw [hyp', blah, (adj.iso c d').2]
    simp

--theorem transpose_sqr' :
  --∀ {L : Funct C D} {R : Funct D C}
    --(adj : Adjunction'' L R)
    --(c c' : C.obj)
    --(d d' : D.obj)
    --(h : C.mor c c')
    --(k : D.mor d d')
    --(f : D.mor (L.map_obj c) d)
    --(g : D.mor (L.map_obj c') d'),
      --D.comp k f = D.comp g (L.map_mor h)
    --↔ C.comp (R.map_mor k) ((adj.n d).eta c f) = C.comp ((adj.n d').eta c' g) h := by
  --intro L R adj c c' d d' h k f g
  --constructor
  --. intro hyp

    --let h := (adj.n d).nt_law (R.map_mor k)
    --simp [type_cat, ContraHom, Hom, funct_comp, Op, FOp] at h
    ----rw [adj.nat_D, hyp, ←adj.nat_C]
  --. intro hyp
    --rw [adj.nat_D, adj.nat_C] at hyp
    --have hyp' := congrArg (λ f => adj.m c d' f) hyp
    --simp at hyp'
    --have blah : ∀ z, adj.m c d' (adj.n c d' z) = (adj.m c d' ∘ adj.n c d') z := by {intros; rfl}
    --rw [blah, (adj.iso c d').2] at hyp'
    --simp at hyp'
    --rw [hyp', blah, (adj.iso c d').2]
    --simp

def conv_adj_2 (L : Funct C D) (R : Funct D C) (adj : Adjunction' L R) : Adjunction L R :=
  { unit :=
    { eta := λ c => adj.n c (L.map_obj c) (D.iden (L.map_obj c))
    , nt_law := by
        intro a b mor
        simp [*, I]
        have tsqr := (transpose_sqr adj a b (L.map_obj a) (L.map_obj b)
                        mor (L.map_mor mor)
                        (D.iden (L.map_obj a)) (D.iden (L.map_obj b))
                     ).1
        apply Eq.symm
        simp [funct_comp]
        apply tsqr
        rw [D.left_id, D.right_id]
    }
  , counit :=
    { eta := λ d => adj.m (R.map_obj d) d (C.iden (R.map_obj d))
    , nt_law := by
        intro a b mor
        simp [*, I]
        have tsqr := (transpose_sqr adj (R.map_obj a) (R.map_obj b) a b
                        (R.map_mor mor) mor
                        (adj.m (R.map_obj a) a (C.iden (R.map_obj a)))
                        (adj.m (R.map_obj b) b (C.iden (R.map_obj b)))
                     ).2
        have blah : ∀ a b z, adj.n a b (adj.m a b z) = (adj.n a b ∘ adj.m a b) z := by {intros; rfl}
        rw [blah, blah, (adj.iso (R.map_obj a) a).1, (adj.iso (R.map_obj b) b).1] at tsqr
        simp at tsqr
        rw [C.left_id, C.right_id] at tsqr
        simp [funct_comp]
        apply Eq.symm
        apply tsqr
        rfl
    }
  , tri_L := by
      simp [id_nt, funct_cat, whisker_left, horiz_nt_comp, whisker_right, I]
      conv =>
        rhs
        intro x
        rw [L.fmap_id, D.left_id, D.right_id (Funct.map_mor L (Adjunction'.n adj x (Funct.map_obj L x) (Cat.iden D (Funct.map_obj L x))))]
      have tsqr := λ x =>
                   (transpose_sqr adj x _ _ _
                      (Adjunction'.n adj x (Funct.map_obj L x) (Cat.iden D (Funct.map_obj L x)))
                      (D.iden (L.map_obj x))
                      (D.iden (L.map_obj x))
                      (Adjunction'.m adj (Funct.map_obj R (Funct.map_obj L x)) (Funct.map_obj L x)
                        (Cat.iden C (Funct.map_obj R (Funct.map_obj L x))))
                   ).2
      conv at tsqr =>
        intro x
        rw [D.left_id]
      
      have omg : (∀ x,
                    Funct.map_mor L (Cat.iden C x) = 
                    Cat.comp D
                      (Adjunction'.m adj (Funct.map_obj R (Funct.map_obj L x)) (Funct.map_obj L x)
                        (Cat.iden C (Funct.map_obj R (Funct.map_obj L x))))
                      (Funct.map_mor L (Adjunction'.n adj x (Funct.map_obj L x) (Cat.iden D (Funct.map_obj L x))))
                 ) →
                 (fun a => Funct.map_mor L (Cat.iden C a)) = fun x =>
                    Cat.comp D
                      (Adjunction'.m adj (Funct.map_obj R (Funct.map_obj L x)) (Funct.map_obj L x)
                        (Cat.iden C (Funct.map_obj R (Funct.map_obj L x))))
                      (Funct.map_mor L (Adjunction'.n adj x (Funct.map_obj L x) (Cat.iden D (Funct.map_obj L x))))
                := by
              intro h
              conv =>
                lhs
                intro x
                rw [h x]
      apply omg
      intro x
      rw [L.fmap_id]
      apply tsqr x
      have blah : ∀ a b z, adj.n a b (adj.m a b z) = (adj.n a b ∘ adj.m a b) z := by {intros; rfl}
      rw [blah, (adj.iso (R.map_obj (L.map_obj x)) (L.map_obj x)).1]
      simp
      rw [C.left_id, R.fmap_id, C.left_id]
  , tri_R := by
      simp [id_nt, funct_cat, whisker_left, horiz_nt_comp, whisker_right, I, funct_comp]
      conv =>
        rhs
        intro x
        rw [R.fmap_id, C.right_id, R.fmap_id, L.fmap_id, R.fmap_id, C.left_id]
      have omg : (∀ x,
                    Funct.map_mor R (Cat.iden D x) =
                      Cat.comp C (Funct.map_mor R (Adjunction'.m adj (Funct.map_obj R x) x (Cat.iden C (Funct.map_obj R x))))
                        (Adjunction'.n adj (Funct.map_obj R x) (Funct.map_obj L (Funct.map_obj R x))
                          (Cat.iden D (Funct.map_obj L (Funct.map_obj R x))))
                 ) →
                 (fun a => Funct.map_mor R (Cat.iden D a)) = fun x =>
                    Cat.comp C (Funct.map_mor R (Adjunction'.m adj (Funct.map_obj R x) x (Cat.iden C (Funct.map_obj R x))))
                      (Adjunction'.n adj (Funct.map_obj R x) (Funct.map_obj L (Funct.map_obj R x))
                        (Cat.iden D (Funct.map_obj L (Funct.map_obj R x)))
                 ) := by
            intro h
            conv =>
              lhs
              intro x
              rw [h x]
      apply omg
      intro x
      have tsqr := (transpose_sqr adj _ _ _ _
                     (Funct.map_mor R (Cat.iden D x))
                     (Adjunction'.m adj (Funct.map_obj R x) x (Cat.iden C (Funct.map_obj R x)))
                     (Cat.iden D (Funct.map_obj L (Funct.map_obj R x)))
                     (adj.m _ _ (R.map_mor (D.iden x)))
                   ).1
      have blah : ∀ a b z, adj.n a b (adj.m a b z) = (adj.n a b ∘ adj.m a b) z := by {intros; rfl}
      rw [blah, (adj.iso (R.map_obj x) x).1] at tsqr
      simp at tsqr
      rw [R.fmap_id, C.left_id] at tsqr
      rw [R.fmap_id]
      apply Eq.symm
      apply tsqr
      rw [D.right_id, L.fmap_id, D.right_id]
  }

-- TODO define this without jeez
def conv_adj_2' (L : Funct C D) (R : Funct D C) (adj : Adjunction''' L R) : Adjunction L R :=
  conv_adj_2 L R $ jeez adj

structure MutualRightAdjoint (L : Funct (Op C) D) (R : Funct (Op D) C) where
  unitC : NT (I C) (funct_comp R (FOp L))
  unitD : NT (I D) (funct_comp L (FOp R))
  -- triangle identities
  tri_L : id_nt (FOp L)
        = funct_cat.comp
            (whisker_left (FOp L) (op_nt unitD))
            (whisker_right unitC (FOp L))
  tri_R : id_nt (FOp R)
        = funct_cat.comp
            (whisker_left (FOp R) (op_nt unitC))
            (whisker_right unitD (FOp R))

--def cast_op_op (F : Funct (Op (Op C)) D) : Funct C D := by
  --rw [op_op] at F
  --exact F

--def testing (ra : MutualRightAdjoint L R) : Adjunction L (cast_op_op (FOp R)) :=
  --{ unit := ra.unitC
  --}

structure MutualLeftAdjoint (L : Funct (Op C) D) (R : Funct (Op D) C) where
  counitC : NT (funct_comp R (FOp L)) (I C)
  counitD : NT (funct_comp L (FOp R)) (I D)
  -- triangle identities
  tri_L : id_nt (FOp L)
        = funct_cat.comp
            (whisker_right counitC (FOp L))
            (whisker_left (FOp L) (op_nt counitD))
  tri_R : id_nt (FOp R)
        = funct_cat.comp
            (whisker_right counitD (FOp R))
            (whisker_left (FOp R) (op_nt counitC))

-- Riehl 4.3.4
def induced_funct {A : Cat.{2, 1}} {B : Cat.{2, 1}}
  : ∀ (F : Funct A B),
    (m : (b : B.obj) → Σ (Gb : A.obj),
      (NT (funct_comp (ContraHom b) (FOp F)) (ContraHom Gb))
      × NT (ContraHom Gb) (funct_comp (ContraHom b) (FOp F)))
    → (h : ∀ b, funct_cat.comp (m b).2.2 (m b).2.1 = funct_cat.iden (funct_comp (ContraHom b) (FOp F))
              ∧ funct_cat.comp (m b).2.1 (m b).2.2 = funct_cat.iden (ContraHom (m b).1)
      )
    → Σ (G : Funct B A), Adjunction F G := by
  intro F m h
  let yon := yoneda_lemma (Op A)
  let G : Funct B A :=
    { map_obj := λ b =>
        let ⟨a, α⟩ := (m b)
        a
    , map_mor := λ {x y} f => by
        let (t1, _) := (m y).2
        let (_, t2) := (m x).2
        let t3 := whisker_left (FOp F) $ precomp_hom f
        let t4 := funct_cat.comp t3 t2
        let t5 := funct_cat.comp t1 t4
        let t6 := yon.Φ (ContraHom (m y).fst) (m x).1 t5
        exact t6
    , fmap_id := by
        intro a
        let hh := (h a).2
        let hhh := congrArg NT.eta hh
        simp [*, precomp_hom, whisker_left, horiz_nt_comp, Hom, funct_cat, id_nt, FOp, Op, type_cat, yoneda_lemma]
        rw [F.fmap_id, B.left_id, B.right_id]
        simp [funct_cat, ContraHom, Hom, type_cat, Op] at hhh
        let hhhh := congrArg (λ f => f (m a).1 (A.iden (m a).1)) hhh
        simp at hhhh
        rw [hhhh, A.left_id]
    , fmap_law := by
        intro a b c f g
        simp [*]--, ContraHom]

        --let h1 := (yon.laws (funct_comp (ContraHom c) (FOp F)) (m b).fst).2.2.1
        --              (Hom (m c).fst)
        --              (Cat.comp funct_cat (whisker_left (FOp F) (precomp_hom f)) (m b).2.snd)
        --              (m c).2.fst
        --let h2 := (yon.laws (funct_comp (ContraHom b) (FOp F)) (m a).fst).2.2.1
        --              (Hom (m b).fst)
        --              (Cat.comp funct_cat (whisker_left (FOp F) (precomp_hom g)) (m a).2.snd)
        --              (m b).2.fst
        --simp [ContraHom]
        --simp [ContraHom] at h1
        --rw [h1, h2]

        --let e : NT (funct_comp (Hom b) (FOp F)) (Hom (m c).fst)
                --= NT (funct_comp (Hom b) (FOp F)) (funct_comp (Hom c) (FOp F)) := by

        -- funct_comp (Hom c) (FOp F) = Hom (m c).1
        -- whisker_left (FOp F) (precomp_hom f) = 
        -- let wanted : funct_cat.mor (funct_comp (ContraHom b) (FOp F)) (Hom (m c).fst) := sorry
        --let hh := (yon.laws (Hom (m c).1) (m b).1).2.2.1
        --            (Hom (m c).1)
        --            (funct_cat.comp () (m b).2.snd)
        --            (m c).2.1
        simp [*, precomp_hom, Hom, whisker_left, horiz_nt_comp, funct_cat, id_nt, type_cat, FOp, Op, yoneda_lemma]
        rw [F.fmap_id, B.right_id, F.fmap_id, B.right_id, B.right_id]
        sorry

        --let hh := congrArg NT.eta (h c).2
        --simp [funct_cat, ContraHom, Hom, type_cat, Op] at hh
        --let hhh := congrArg (λ f => f (m b).1) hh
        --simp at hhh
    }
  let adj : Adjunction F G := sorry
  exact ⟨G, adj⟩

--theorem induced_bifunct :
      --∀ (F : Bifunct A B C),
      --(f : ∀ (a : A.obj), Σ (Ga : Funct C B), Adjunction (app_bifunct F a) Ga)
      --→ ∃ (G : Bifunct (Op A) C B), ∀ a c,
          --univ_prop (λ Z => Z.map_obj (a, c) = (f a).1.map_obj c) G
  --:= by
  --intro F f
  --let G : Bifunct (Op A) C B :=
    --{ map_obj := λ ⟨a, c⟩ =>
        --let ⟨Ga, _⟩ := f a
        --Ga.map_obj c
    --, map_mor := λ {x y} ⟨m, n⟩ => by
        --simp
        --let ⟨Gx, adjX⟩ := f x.1
        --let ⟨Gy, adjY⟩ := f y.1
        --let t1 := adjY.unit.eta (Gx.map_obj y.2)
        --let t2 := adjX.counit.eta y.2
        --let t3 := adjY.counit.eta y.2
        --let t4 := adjY.unit.eta (Gx.map_obj x.2)
        ---- can define an NT between F x.1 and F y.1
        --simp [I, funct_comp] at t4
        ----let nt : NT (app_bifunct F x.1) (app_bifunct F y.1) :=
          ----{ eta := λ b => by
              ----simp [app_bifunct]
          ----}
        ----let fm o : C.mor ((app_bifunct F x.1).map_obj o) ((app_bifunct F y.1).map_obj o) :=
          ----let xy := F.map_mor (m, B.iden o)
        ----let n' := Gx.map_mor ((app_bifunct F x.1).map_mor (Gx.map_mor n))
        ----let t5 := B.comp n' t4
        
        --sorry

    --}
  --exists G
  --sorry

-- Riehl Proposition 4.4.1
theorem iso_left_adj : ∀ (C : Cat.{2, 1}) (D : Cat.{2, 1}) (F F' : Funct C D) (G : Funct D C),
          (adj : Adjunction F G) → (adj' : Adjunction F' G)
          → ∃ (θ : funct_cat.mor F F'),
              nat_iso' θ ∧
                univ_prop (λ t => adj'.unit = funct_cat.comp (whisker_right t G) adj.unit
                                ∧ adj.counit = funct_cat.comp adj'.counit (whisker_left G t))
                  θ
                := by
  intro C D F F' G adj adj'
  let adjl := conv_adj_1'' _ _ adj
  let ff := adjl.m
  let gg := adjl.n
  let adjl' := conv_adj_1'' _ _ adj'
  let fff := adjl'.n
  let ggg := adjl'.m
  let ntt := funct_cat.comp adjl.n adjl'.m
  let ntt' := funct_cat.comp adjl'.n adjl.m
  -- in order to use yoneda here, would need a natural transformation
  -- between the hom set of natural transforms with codmain F' to the
  -- hom set of natural transformations with codomain F.
  let yon := yoneda_lemma $ @funct_cat C D
  let nt : NT F' F :=
        { eta := λ c => by
            let h := ntt'.eta (c, F.map_obj c)
            simp [type_cat, BiHom, funct_comp, FunctProd, FOp, I] at h
            exact h $ D.iden (F.map_obj c)
        , nt_law := by
            intro a b mor
            simp [*, funct_cat, type_cat, conv_adj_1'']
            rw [G.fmap_id, C.left_id, G.fmap_id, C.left_id]
            let h := ntt'.nt_law ((mor, D.iden (F.map_obj b)) : (prod (Op C) D).mor (b, F.map_obj b) (a, F.map_obj b))
            simp [type_cat, funct_cat, conv_adj_1'', BiHom, funct_comp, FunctProd, I] at h
            conv at h =>
              lhs
              intro f
              simp
              rw [D.left_id]
            conv at h =>
              rhs
              intro f
              simp
              rw [D.left_id]
            let h' := congrFun h (D.iden _)
            rw [D.left_id] at h'
            simp [FOp] at h'
            rw [G.fmap_id, C.left_id, ←F'.fmap_law] at h'
            rw [←h']
            let h'' := adj'.counit.nt_law (F.map_mor mor)
            simp [I, funct_comp] at h''
            rw [D.comp_assoc, D.comp_assoc]
            rw [←h'']
        }
  let nt' : NT F F' :=
        { eta := λ c => by
            let h := ntt.eta (c, F'.map_obj c)
            simp [type_cat, BiHom, funct_comp, FunctProd, FOp, I] at h
            exact h $ D.iden (F'.map_obj c)
        , nt_law := by
            intro a b mor
            simp [*, funct_cat, type_cat, conv_adj_1'']
            rw [G.fmap_id, C.left_id, G.fmap_id, C.left_id]
            let h := ntt.nt_law ((mor, D.iden (F'.map_obj b)) : (prod (Op C) D).mor (b, F'.map_obj b) (a, F'.map_obj b))
            simp [type_cat, funct_cat, conv_adj_1'', BiHom, funct_comp, FunctProd, I] at h
            conv at h =>
              lhs
              intro f
              simp
              rw [D.left_id]
            conv at h =>
              rhs
              intro f
              simp
              rw [D.left_id]
            let h' := congrFun h (D.iden _)
            rw [D.left_id] at h'
            simp [FOp] at h'
            rw [G.fmap_id, C.left_id, ←F.fmap_law] at h'
            rw [←h']
            let h'' := adj.counit.nt_law (F'.map_mor mor)
            simp [I, funct_comp] at h''
            rw [D.comp_assoc, D.comp_assoc]
            rw [←h'']
        }
  exists nt'
  apply And.intro
  . simp [nat_iso'] -- define natural isos to have components be isos instead
    intro c
    simp [isomorphism, funct_cat, conv_adj_1'', type_cat]
    rw [G.fmap_id, C.left_id]
    let h := adjl'.iso (G.map_obj (F'.map_obj c)) (F'.map_obj c)
    -- can compose the two by applying the one side to the function from the the
    -- other then using the other prop to convert it to identity.

    -- Supply 'n' as a composition of G etas such that the compose with the F and
    -- F' etas to produce identities.
    simp [*, conv_adj_1''] at h
    let h' := h.2
    conv at h' =>
      lhs
      intro f
      simp
    simp [funct_comp, BiHom, FunctProd, I, FOp] at h'
    let h'' := congrFun h' (C.iden _)
    simp [FunctProd, FOp, funct_cat, type_cat, conv_adj_1''] at h''
    rw [F'.fmap_id, D.right_id] at h''
    exists Cat.comp D (NT.eta adj'.counit (Funct.map_obj F c))
                        (Funct.map_mor F' (NT.eta adj.unit c))
    apply And.intro
    . sorry
    . sorry
  . sorry
    
-- Riehl Proposition 4.4.4
def adj_comp {F : Funct C D} {G : Funct D C} {F' : Funct D E} {G' : Funct E D}
        (adj1 : Adjunction F G) (adj2 : Adjunction F' G')
          : Adjunction (funct_comp F' F) (funct_comp G G') :=
  { unit := funct_cat.comp (whisker_right (whisker_left F adj2.unit) G) adj1.unit
  , counit := funct_cat.comp adj2.counit (whisker_right (whisker_left G' adj1.counit) F')
  , tri_L := by
      simp [whisker_left, horiz_nt_comp, funct_cat, id_nt, funct_comp, whisker_right, I]
      conv =>
        lhs
        intro f
        rw [F.fmap_id, F'.fmap_id]
      conv =>
        rhs
        intro f
        rw [F.fmap_id, F'.fmap_id, E.left_id, G'.fmap_id, D.left_id, F'.fmap_id, E.right_id
           , D.left_id, E.right_id, G.fmap_id, C.right_id]
      let omg : (∀ f, Cat.iden E (Funct.map_obj F' (Funct.map_obj F f)) = 
                  Cat.comp E
                    (Cat.comp E (NT.eta adj2.counit (Funct.map_obj F' (Funct.map_obj F f)))
                      (Funct.map_mor F' (NT.eta adj1.counit (Funct.map_obj G' (Funct.map_obj F' (Funct.map_obj F f))))))
                    (Funct.map_mor F'
                      (Funct.map_mor F (Cat.comp C (Funct.map_mor G (NT.eta adj2.unit (Funct.map_obj F f))) (NT.eta adj1.unit f)))))
                → ((fun f => Cat.iden E (Funct.map_obj F' (Funct.map_obj F f))) = fun f =>
                    Cat.comp E
                      (Cat.comp E (NT.eta adj2.counit (Funct.map_obj F' (Funct.map_obj F f)))
                        (Funct.map_mor F' (NT.eta adj1.counit (Funct.map_obj G' (Funct.map_obj F' (Funct.map_obj F f))))))
                      (Funct.map_mor F'
                        (Funct.map_mor F (Cat.comp C (Funct.map_mor G (NT.eta adj2.unit (Funct.map_obj F f))) (NT.eta adj1.unit f))))) := by
              intro h
              conv =>
                lhs
                intro x
                rw [h x]
      apply omg
      intro x
      let h := adj1.tri_L
      let h' := adj2.tri_L
      simp [funct_cat, whisker_left, whisker_right, horiz_nt_comp, id_nt, I] at h
      simp [funct_cat, whisker_left, whisker_right, horiz_nt_comp, id_nt, I] at h'
      let hh := congrFun h x
      let hh' := congrFun h' (F.map_obj x)
      simp [I] at hh
      rw [F.fmap_id, D.left_id] at hh
      conv at hh =>
        rhs
        arg 3
        simp [I]
        rw [←F.fmap_id, F.fmap_law, C.right_id]
      rw [F'.fmap_id, E.left_id, ←F'.fmap_id, F'.fmap_law, D.right_id, F'.fmap_id] at hh'
      rw [←E.comp_assoc, F'.fmap_law, ←F.fmap_law, D.comp_assoc]
      let hhh := adj1.counit.nt_law (NT.eta adj2.unit (Funct.map_obj F x))
      simp [funct_comp] at hhh
      rw [hhh]
      simp [I]
      rw [←F'.fmap_law, E.comp_assoc, ←F'.fmap_law, E.comp_assoc, ←hh', E.left_id, F'.fmap_law, ←hh, F'.fmap_id]
  , tri_R := by
      simp [whisker_left, horiz_nt_comp, funct_cat, id_nt, funct_comp, whisker_right, I]
      conv =>
        lhs
        intro a
        rw [G'.fmap_id, G.fmap_id]
      conv =>
        rhs
        intro a
        rw [G'.fmap_id, G.fmap_id, F.fmap_id, F'.fmap_id, G'.fmap_id, G.fmap_id, C.left_id, G.fmap_id, C.right_id, D.left_id, E.right_id
           , D.left_id, C.right_id
           ]
      let omg : (∀ a, Cat.iden C (Funct.map_obj G (Funct.map_obj G' a)) =
                  Cat.comp C
                    (Funct.map_mor G
                      (Funct.map_mor G'
                        (Cat.comp E (NT.eta adj2.counit a) (Funct.map_mor F' (NT.eta adj1.counit (Funct.map_obj G' a))))))
                    (Cat.comp C (Funct.map_mor G (NT.eta adj2.unit (Funct.map_obj F (Funct.map_obj G (Funct.map_obj G' a)))))
                      (NT.eta adj1.unit (Funct.map_obj G (Funct.map_obj G' a)))))
                → (fun a => Cat.iden C (Funct.map_obj G (Funct.map_obj G' a))) = fun a =>
                    Cat.comp C
                      (Funct.map_mor G
                        (Funct.map_mor G'
                          (Cat.comp E (NT.eta adj2.counit a) (Funct.map_mor F' (NT.eta adj1.counit (Funct.map_obj G' a))))))
                      (Cat.comp C (Funct.map_mor G (NT.eta adj2.unit (Funct.map_obj F (Funct.map_obj G (Funct.map_obj G' a)))))
                        (NT.eta adj1.unit (Funct.map_obj G (Funct.map_obj G' a)))) := by
              intro h
              conv =>
                lhs
                intro x
                rw [h x]
      apply omg
      intro x
      let h := adj1.tri_R
      let h' := adj2.tri_R
      simp [funct_cat, whisker_left, whisker_right, horiz_nt_comp, id_nt, I, funct_comp] at h
      simp [funct_cat, whisker_left, whisker_right, horiz_nt_comp, id_nt, I, funct_comp] at h'
      let hh := congrFun h (G'.map_obj x)
      let hh' := congrFun h' x
      rw [G.fmap_id, G.fmap_id, C.right_id, F.fmap_id, G.fmap_id, C.left_id] at hh
      rw [G'.fmap_id, G'.fmap_id, D.right_id, F'.fmap_id, G'.fmap_id, D.left_id] at hh'
      rw [←G'.fmap_law, ←G.fmap_law, C.comp_assoc]
      conv =>
        rhs
        arg 2
        rw [←C.comp_assoc, G.fmap_law]
      let hhhh := adj2.unit.nt_law (NT.eta adj1.counit (Funct.map_obj G' x))
      simp [I, funct_comp] at hhhh
      rw [←hhhh]
      let hhh := adj2.unit.nt_law (NT.eta adj1.counit (Funct.map_obj G' x))
      simp [I, funct_comp] at hhh
      rw [G.fmap_law, D.comp_assoc, ←hh', D.left_id, ←hh]
  }

-- Riehl Prop 4.4.6
def postcomp_adj {C D E : Cat} {F : Funct C D} {G : Funct D C} (adj : Adjunction F G) :
  Adjunction (@postcomp_funct C D E F) (postcomp_funct G) :=
  { unit :=
    { eta := by
        intro H
        simp [funct_cat] at H
        simp [I, funct_cat, funct_comp]
        exact { eta := by
                  intro a
                  simp [postcomp_funct, funct_comp]
                  exact adj.unit.eta (H.map_obj a)
              , nt_law := by
                  intro a b mor
                  exact adj.unit.nt_law (H.map_mor mor)
              }
    , nt_law := by
        intro a b mor
        simp [*, funct_cat, funct_comp, postcomp_funct, I]
        let h x := adj.unit.nt_law (mor.eta x)
        simp [I, funct_comp] at h
        conv =>
          lhs
          intro x
          rw [h]
    }
  , counit :=
    { eta := by
        intro H
        simp [funct_cat] at H
        simp [I, funct_cat, funct_comp]
        exact { eta := by
                  intro a
                  simp [postcomp_funct, funct_comp]
                  exact adj.counit.eta (H.map_obj a)
              , nt_law := by
                  intro a b mor
                  exact adj.counit.nt_law (H.map_mor mor)
              }
    , nt_law := by
        intro a b mor
        simp [*, funct_cat, funct_comp, postcomp_funct, I]
        let h x := adj.counit.nt_law (mor.eta x)
        simp [I, funct_comp] at h
        conv =>
          lhs
          intro x
          rw [h]
    }
  , tri_L := by
      simp [whisker_left, horiz_nt_comp, I, postcomp_funct, funct_comp]
      conv =>
        lhs
      sorry -- lean is bugging out here
      --simp [*, id_nt, funct_cat, postcomp_funct, whisker_left]
  , tri_R := by
      sorry
  }

def precomp_adj {C D E : Cat} {F: Funct C D} {G : Funct D C} (adj : Adjunction F G) :
  Adjunction (@precomp_funct C D E F) (precomp_funct G)
  := sorry