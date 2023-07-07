import LeanCat.NT
import LeanCat.Funct
import LeanCat.Limit

structure Adjunction (L : Funct C D) (R : Funct D C) where
  unit : NT (I C) (funct_comp R L)
  counit : NT (funct_comp L R) (I D)
  -- triangle identities
  tri_L : id_nt L = funct_cat.comp (whisker_left L counit) (whisker_right unit L)
  tri_R : id_nt R = funct_cat.comp (whisker_right counit R) (whisker_left R unit)

theorem adj_lim_preservation : ∀ {L : Funct C D} (adj : Adjunction L R), preserves_lims R ∧ preserves_colims L := by
  intro L adj
  constructor
  . simp [preserves_lims]
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
                  have lem x : R.map_obj ((funct_comp L R).map_obj x)
                           = (funct_comp R L).map_obj (R.map_obj x)
                              := by rfl
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
  . simp [preserves_colims] 
    intro J G l
    let lfg : Colim (funct_comp L G) :=
      { lim := L.map_obj l.lim
      , legs :=
        { eta := λ a => L.map_mor $ get_leg l.toCone a
        , nt_law := by
            intro a b mor
            simp
            have h := l.legs.nt_law mor
            simp [Const]
            rw [(Op D).right_id]
            simp [funct_comp, get_leg, Op, FDual]
            simp [Op, Const, FDual] at h
            rw [C.left_id] at h
            rw [L.fmap_law]
            simp [Const]
            rw [h]
        }
      , univ_prop := by
          intro oc
          let occ : Cone ((funct_comp (funct_comp (FDual R) (FDual L)) (FDual G))) :=
            { lim := R.map_obj oc.lim
            , legs :=
                { eta := λ a => R.map_mor $ oc.legs.eta a
                , nt_law := sorry
                }
            }
          --have ls := funct_cat.comp (whisker_left G adj.unit) occ.legs
          let occc : Cone (FDual G) :=
            { lim := occ.lim
            , legs := _ -- NT (Const (Op J) occ.lim) (FDual G)
            }
          have ⟨m, h⟩ := l.univ_prop occc
          let m' := L.map_mor m
          let need : Cat.mor (Op D) oc.lim (L.map_obj occc.lim) :=
                sorry --adj.counit.eta oc.lim
          let the_one : (Op D).mor oc.lim (L.map_obj l.lim) := (Op D).comp m' need
          --exists the_one
          --intro n
          --let toLim := adj.counit.eta l.lim
          --let n' := D.comp toLim (L.map_mor n)
          --have h2 := congrArg ((C.comp · need) ∘ R.map_mor) $ h n'
          --simp at h2
          --have the_one_def : Cat.comp C (Funct.map_mor R m) (NT.eta adj.unit oc.lim) = the_one := rfl
          --rw [the_one_def] at h2

          --let need2 :
                --Cat.comp C (Funct.map_mor R (Cat.comp D (NT.eta adj.counit l.lim) (Funct.map_mor L n))) (NT.eta adj.unit oc.lim)
                --= n := by
                --{ have fc : R.map_mor (L.map_mor n) = (funct_comp R L).map_mor n := rfl
                  --rw [←R.fmap_law, ←C.comp_assoc, fc, ←adj.unit.nt_law n]
                  --simp [*, I]
                  --rw [C.comp_assoc]
                  --have test : id_nt R = funct_cat.comp (whisker_right adj.counit R) (whisker_left R adj.unit) := adj.tri_R
                  --have test2 := congrArg (NT.eta · l.lim) test
                  --simp at test2
                  --simp [id_nt, whisker_left, whisker_right, funct_cat, horiz_nt_comp] at test2
                  --rw [R.fmap_id, ←adj.unit.nt_law (Cat.iden C (Funct.map_obj R l.lim))] at test2
                  --simp [I] at test2
                  --have lem x : R.map_obj ((funct_comp L R).map_obj x)
                           --= (funct_comp R L).map_obj (R.map_obj x)
                              --:= by rfl
                  --rw [C.right_id, R.fmap_id, ←C.comp_assoc] at test2
                  --conv at test2 =>
                    --rhs
                    --simp [funct_comp]
                    --rw [C.left_id]
                  --rw [←test2, C.left_id]
                --}
          --rw [need2] at h2
          --exact h2
      }
    exists lfg