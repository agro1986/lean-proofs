variables p q r s: Prop

-- commutativity of ∧ and ∨

theorem and_switch (h: p ∧ q): q ∧ p :=
  and.intro h.right h.left

example: p ∧ q ↔ q ∧ p :=
  iff.intro
    (and_switch p q)
    (and_switch q p)

theorem or_switch (h: p ∨ q): q ∨ p :=
  or.elim h
    (assume p, or.inr p)
    (assume q, or.inl q)

example: p ∨ q ↔ q ∨ p :=
  iff.intro
    (or_switch p q)
    (or_switch q p)

-- associativity of ∧ and ∨

example: p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  iff.intro
    (assume h: p ∧ (q ∨ r),
      have hp: p, from h.left,
      or.elim h.right
        (assume hq: q,
          have hpq: p ∧ q, from and.intro hp hq,
            or.inl hpq)
        (assume hr: r,
          have hpr: p ∧ r, from and.intro hp hr,
            or.inr hpr))
    (assume h: (p ∧ q) ∨ (p ∧ r),
      or.elim h
        (assume hpq: p ∧ q,
          have hp: p, from hpq.left,
          have hqr: q ∨ r, from or.inl hpq.right,
          and.intro hp hqr)
        (assume hpr: p ∧ r,
          have hp: p, from hpr.left,
          have hqr: q ∨ r, from or.inr hpr.right,
          and.intro hp hqr))

example: (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  iff.intro
    (assume h: (p ∧ q) ∧ r,
      have hpq: p ∧ q, from h.left,
      have hp: p, from hpq.left,
      have hq: q, from hpq.right,
      have hr: r, from h.right,
      ⟨hp, ⟨hq, hr⟩⟩)
    (assume h: p ∧ (q ∧ r),
      have hp: p, from h.left,
      have hqr: q ∧ r, from h.right,
      have hq: q, from hqr.left,
      have hr: r, from hqr.right,
      ⟨⟨hp, hq⟩, hr⟩)

