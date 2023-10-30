import LeanCat.Core
import LeanCat.Funct
import LeanCat.NT
import LeanCat.Adjunction

structure Monad' (C : Cat) where
  T : Funct C C
  η : NT (I C) T
  μ : NT (funct_comp T T) T
  assoc_law :
    funct_cat.comp μ (whisker_left T μ)
    = funct_cat.comp μ (whisker_right μ T)
  unital_right :
    funct_cat.comp μ (whisker_left T η) = id_nt T
  unital_left :
    funct_cat.comp μ (whisker_right η T) = id_nt T

def monad_from_adj {C : Cat} {D : Cat} {L : Funct C D} {R : Funct D C}
      (adj : Adjunction L R) : Monad' C :=
  { T := funct_comp R L
  , η := adj.unit
  , μ := whisker_right (whisker_left L adj.counit) R
  , assoc_law := by
      simp [funct_cat, whisker_right, whisker_left, horiz_nt_comp, I, funct_comp, id_nt]
      conv =>
        lhs
        intro x
        rw [L.fmap_id, D.left_id, R.fmap_id, C.right_id, R.fmap_id, L.fmap_id, R.fmap_id, C.left_id, R.fmap_id, C.right_id, D.left_id, R.fmap_law]
      let h x := adj.counit.nt_law (NT.eta adj.counit (Funct.map_obj L x))
      simp [I, funct_comp] at h
      conv =>
        rhs
        intro x
        rw [L.fmap_id, D.left_id, R.fmap_id, C.right_id, L.fmap_id, R.fmap_id, C.right_id, R.fmap_law, h x]
  , unital_right := by
      simp [funct_cat, whisker_right, horiz_nt_comp, whisker_left, I, id_nt, funct_comp]
      conv =>
        lhs
        intro x
        rw [L.fmap_id, D.left_id, R.fmap_id, C.right_id, R.fmap_id, L.fmap_id, R.fmap_id, C.left_id]
      conv =>
        rhs
        intro x
        rw [L.fmap_id, R.fmap_id]
      
      let h := congrArg (whisker_left L) adj.tri_R.symm
      simp [*, funct_cat, whisker_right, horiz_nt_comp, whisker_left, I, id_nt, funct_comp] at h
      conv at h =>
        lhs
        intro x
        rw [L.fmap_id, R.fmap_id, C.left_id, R.fmap_id, C.right_id, L.fmap_id, R.fmap_id, C.left_id]
      conv at h =>
        rhs
        intro x
        rw [L.fmap_id, R.fmap_id, C.left_id]
      exact h
  , unital_left := by
      simp [funct_cat, whisker_right, horiz_nt_comp, whisker_left, I, id_nt, funct_comp]
      let h := congrArg (whisker_right · R) adj.tri_L.symm
      simp [funct_cat, whisker_right, horiz_nt_comp, whisker_left, I, id_nt, funct_comp] at h
      conv at h =>
        lhs
        intro x
        rw [L.fmap_id, D.left_id, D.right_id, R.fmap_id, C.right_id]
      conv at h =>
        rhs
        intro x
        rw [L.fmap_id, R.fmap_id, C.left_id]
      conv =>
        lhs
        intro x
        rw [R.fmap_id, C.right_id, L.fmap_id, D.left_id, R.fmap_id, C.right_id, R.fmap_law]
      conv =>
        rhs
        intro x
        rw [L.fmap_id, R.fmap_id]
      exact h      
  }