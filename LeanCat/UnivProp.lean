def univ_prop (prop : α → Prop) (x : α) : Prop :=
  prop x ∧ (∀ (y : α), prop y → x = y)