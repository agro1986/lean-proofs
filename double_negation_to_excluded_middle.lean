variable {p: Prop}

axiom double_negation: ¬¬p → p

theorem not_not_excluded_middle: ¬¬(p ∨ ¬p) :=
  assume (h: ¬(p ∨ ¬p)),
    have hnp: ¬p, from
      (assume hp: p, h (or.inl hp)),
    h (or.inr hnp)

theorem excluded_middle: p ∨ ¬p :=
  double_negation not_not_excluded_middle

#check excluded_middle
