variables {a b c: ℤ}

constant divides: ℤ → ℤ → Prop

axiom divides_expand: divides a b → ∃(d: ℤ), a * d = b
axiom divides_conclude: (∃(d: ℤ), a * d = b) → divides a b

theorem divides_trans (hab: divides a b) (hbc: divides b c):
divides a c :=
  have h1: ∃m, a * m = b, from divides_expand hab,
  have h2: ∃n, b * n = c, from divides_expand hbc,
  exists.elim h1 (assume m: ℤ, assume hamb: a * m = b,
    exists.elim h2 (assume n: ℤ, assume hbnc: b * n = c,
      have c = a * (m * n) , from calc
           c = b * n       : hbnc.symm
         ... = (a * m) * n : congr_arg _ hamb.symm
         ... = a * (m * n) : mul_assoc _ _ _,
      have a * (m * n) = c, from this.symm,
      have ∃mn, a * mn = c, from ⟨m * n, this⟩,
      divides_conclude this
  ))

theorem two_divides_four: divides 2 4 :=
  have 2 * 2 = (4: ℤ), from refl _,
  have ∃(d: ℤ), 2 * d = 4, from ⟨2, this⟩,
  divides_conclude this

axiom four_divides_twenty: divides 4 20 -- same as above

theorem two_divides_twenty: divides 2 20 :=
  divides_trans two_divides_four four_divides_twenty

#check divides
#check divides 2 4
#check divides_conclude

#check divides_expand two_divides_four