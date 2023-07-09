import LeanCat.NT
import LeanCat.Funct
import LeanCat.Limit

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