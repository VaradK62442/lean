set_option linter.unusedVariables false
/- Propositions and Proofs -/

/- Propositions as Types -/
section
#check And
#check Or
#check Not

def Implies (p q : Prop) : Prop := p → q
#check Implies

variable (p q r : Prop)
#check And p q
#check Or (And p q) r
#check Implies (And p q) (And q p)

structure Proof (p : Prop) : Type where proof : p
#check Proof

axiom and_commute (p q : Prop) : Proof (Implies (And p q) (And q p))
#check and_commute p q

axiom modus_ponens (p q : Prop) : Proof (Implies p q) -> Proof p -> Proof q
axiom implies_intro (p q : Prop) : (Proof p -> Proof q) -> Proof (Implies p q)

-- when we have p : Prop, we can use p instead of Proof p
-- simplifies Implies p q to p → q

-- Prop is closed under →, i.e. p q : Prop implies p → q : Prop
#check p → q
end

/- Working with Propositions as Types -/
namespace setup
  variable {p : Prop}
  variable {q : Prop}

  theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
  #print t1

  theorem t1' : p → q → p :=
    fun hp : p =>
    fun hq : q =>
    show p from hp
  #print t1'

  theorem t1'' (hp : p) (hq : q) : p := hp
  #print t1''

  axiom hp : p -- p is true, as witnessed by hp
  -- (by hp : p) p is true implies (by t1) q → p is true, which is t2
  theorem t2 : q → p := t1 hp
  #print t2

  axiom unsound : False
  theorem ex : 1 = 0 :=
    False.elim unsound
  #print ex
end setup

namespace generalise
  theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp

  variable (p q r s : Prop)

  #check t1 p q
  #check t1 r s
  #check t1 (r → s) (p → q)

  variable (h : r → s) -- hypothesis or premise that r → s holds

  #check t1 (r → s) (s → r) h
end generalise

variable (p q r s : Prop)

-- transitivity of implication
theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)

/- Propositional Logic -/
#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p

-- conjunction
-- example is anonymous theorem - asserts something without naming or storing
example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h

variable (hp : p) (hq : q)

#check (⟨hp, hq⟩ : p ∧ q)

example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)
example (h : p ∧ q) : q ∧ p :=
  ⟨(And.right h), (And.left h)⟩ -- shorthand for And.intro
example (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩ -- shorthand for And.right, And.left

--disjunction
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p => show q ∨ p from Or.intro_right q hp)
    (fun hq : q => show q ∨ p from Or.intro_left p hq)
example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)
example (h : p ∨ q) : q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)

-- personal preference:
theorem orLeft (hp : p) : p ∨ q := Or.intro_left q hp
theorem orRight (hq : q) : p ∨ q := Or.intro_right p hq
example (h : p ∨ q) : q ∨ p :=
  h.elim (orRight q p) (orLeft q p)

-- negation and falsity
-- ¬p is defined to be p → False
example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)

-- False.elim: anything follows from a contradiction
example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
-- arbitrary fact derived from contradictory hypotheses
example (hp : p) (hnp : ¬p) : q := absurd hp hnp
example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp

-- logical equivalence
-- Iff.intro h1 h2 produces proof of p ↔ q
-- from h1 : p → q and h2 : q → p
-- Iff.mp h produces a proof of p → q from h : p ↔ q (modus ponens)
-- Iff.mpr h produces a proof of q → p from h : p ↔ q
theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
      show q ∧ p from ⟨h.right, h.left⟩)
    (fun h : q ∧ p =>
      show p ∧ q from ⟨h.right, h.left⟩)
#check and_swap

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h

theorem and_swap' : p ∧ q ↔ q ∧ p :=
  ⟨fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩⟩
example (h : p ∧ q) : q ∧ p := (and_swap' p q).mp h

/- Introducing Auxiliary Subgoals -/
-- have h : p := s; t
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from ⟨hq, hp⟩

-- suffices hq : q
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from ⟨hq, hp⟩
  show q from h.right

/- Classical Logic -/
open Classical

#check em p -- excluded middle

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

-- proof by cases
example (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)

-- proof by contradiction
example (h : ¬¬p) : p :=
  byContradiction
    (
      -- fun h1 : ¬p => absurd h1 h -- equivalent
      fun h1 : ¬p => show False from h h1
    )

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (
      fun hp : p => Or.inr (
        show ¬q from fun hq : q => h ⟨hp, hq⟩
      )
    )
    (
      fun hp : ¬p => Or.inl hp
    )

/- Examples of Propositional Validities -/
-- `sorry` is used to magically prove anything (unsound)
-- can be used as a placeholder for building long proofs
example : False := sorry
-- can use `_` also as a placeholder

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (
      fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (
          fun hq : q => show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩
        )
        (
          fun hr : r => show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩
        )
    )
    (
      fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (
          fun hpq : p ∧ q =>
            have hp : p := hpq.left
            have hq : q := hpq.right
            have hqr : q ∨ r := Or.inl hq
            ⟨hp, hqr⟩
        )
        (
          fun hpr : p ∧ r =>
            have hp : p := hpr.left
            have hr : r := hpr.right
            have hqr : q ∨ r := Or.inl hq
            ⟨hp, hqr⟩
        )
    )

-- negation of implication negation
example : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
    show q from
      Or.elim (em q)
        (fun hq : q => hq)
        (fun hnq : ¬q => absurd ⟨hp, hnq⟩ h)

/- Exercises -/
namespace exercises

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (
      fun h : p ∧ q =>
        have hp : p := h.left
        have hq : q := h.right
        ⟨hq, hp⟩
    )
    (
      fun h : q ∧ p =>
        have hq : q := h.left
        have hp : p := h.right
        ⟨hp, hq⟩
    )
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (
      fun h : p ∨ q =>
        Or.elim h
        (fun hp : p => show q ∨ p from Or.inr hp)
        (fun hq : q => show q ∨ p from Or.inl hq)
    )
    (
      fun h : q ∨ p =>
        Or.elim h
        (fun hq : q => show p ∨ q from Or.inr hq)
        (fun hp : p => show p ∨ q from Or.inl hp)
    )

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (
      fun h : (p ∧ q) ∧ r =>
        have hqr : q ∧ r := ⟨h.left.right, h.right⟩
        have hp : p := h.left.left
        ⟨hp, hqr⟩
    )
    (
      fun h : p ∧ (q ∧ r) =>
        have hpq : p ∧ q := ⟨h.left, h.right.left⟩
        have hr : r := h.right.right
        ⟨hpq, hr⟩
    )
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (
      fun h : (p ∨ q) ∨ r => Or.elim h
        (
          fun hpq : p ∨ q => Or.elim hpq
            (fun hp : p => Or.inl hp)
            (fun hq : q => Or.inr (Or.inl hq))
        )
        (
          fun hr : r =>
            have hqr : q ∨ r := Or.inr hr
            Or.inr hqr
        )
    )
    (
      fun h : p ∨ (q ∨ r) => Or.elim h
        (
          fun hp : p => Or.inl (Or.inl hp)
        )
        (
          fun hqr : q ∨ r => Or.elim hqr
            (fun hq : q => Or.inl (Or.inr hq))
            (fun hr : r => Or.inr hr)
        )
    )

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (
      fun h : p ∧ (q ∨ r) =>
        Or.elim h.right
          (fun hq : q => Or.inl ⟨h.left, hq⟩)
          (fun hr : r => Or.inr ⟨h.left, hr⟩)
    )
    (
      fun h : (p ∧ q) ∨ (p ∧ r) => Or.elim h
        (fun hpq : p ∧ q => ⟨hpq.left, Or.inl (hpq.right)⟩)
        (fun hpr : p ∧ r => ⟨hpr.left, Or.inr (hpr.right)⟩)
    )
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (
      fun h : p ∨ (q ∧ r) => Or.elim h
        (fun hp : p => ⟨Or.inl hp, Or.inl hp⟩)
        (fun hqr : q ∧ r => ⟨Or.inr (hqr.left), Or.inr (hqr.right)⟩)
    )
    (
      fun h : (p ∨ q) ∧ (p ∨ r) =>
        have hpq : p ∨ q := h.left
        have hpr : p ∨ r := h.right
        Or.elim hpq
          (fun hp : p => Or.inl hp)
          (
            fun hq : q => Or.elim hpr
              (fun hp : p => Or.inl hp)
              (fun hr : r => Or.inr ⟨hq, hr⟩)
          )
    )

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (
      fun h : p → (q → r) =>
      fun hpq : p ∧ q =>
      h hpq.left hpq.right
    )
    (
      fun h : p ∧ q → r =>
      fun hp : p =>
      fun hq : q =>
      h (And.intro hp hq)
    )
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (
      fun h : (p ∨ q) → r => ⟨
        fun hp : p => h (Or.inl hp),
        fun hq : q => h (Or.inr hq)
      ⟩
    )
    (
      fun h : (p → r) ∧ (q → r) =>
      fun hpq : (p ∨ q) =>
      Or.elim hpq h.left h.right
    )
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (
      fun h : ¬(p ∨ q) => And.intro
        (
          Or.elim (em p)
            (fun hp : p => absurd (Or.inl hp) h)
            (fun hnp : ¬p => hnp)
        )
        (
          Or.elim (em q)
            (fun hq : q => absurd (Or.inr hq) h)
            (fun hnq : ¬q => hnq)
        )
    )
    (
      fun h : ¬p ∧ ¬q => show ¬(p ∨ q) from
        (
          fun hpq : p ∨ q => Or.elim hpq
            (fun hp : p => absurd hp h.left)
            (fun hq : q => absurd hq h.right)
        )
    )
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
 fun h : ¬p ∨ ¬q => show ¬(p ∧ q) from (
  fun hpq : p ∧ q => Or.elim h
    (fun hnp : ¬p => absurd hpq.left hnp)
    (fun hnq : ¬q => absurd hpq.right hnq)
 )
example : ¬(p ∧ ¬p) := show ¬(p ∧ ¬p) from (
  fun h : p ∧ ¬p => Or.elim (em p)
    (fun hp : p => absurd hp h.right)
    (fun hnp : ¬p => absurd h.left hnp)
)
example : p ∧ ¬q → ¬(p → q) :=
  fun h : p ∧ ¬q => show ¬(p → q) from (
    fun hpq : p → q => absurd (hpq h.left) h.right
  )
example : ¬p → (p → q) :=
  fun hnp : ¬p =>
  fun hp : p => absurd hp hnp
example : (¬p ∨ q) → (p → q) :=
  fun h : ¬p ∨ q =>
  fun hp : p => Or.elim h
    (fun hnp : ¬p => absurd hp hnp)
    (fun hq : q => hq)
example : p ∨ False ↔ p :=
  Iff.intro
    (
      fun h : p ∨ False => Or.elim h
        (fun hp : p => hp)
        (fun f : False => False.elim f)
    )
    (
      fun h : p => Or.inl h
    )
example : p ∧ False ↔ False :=
  Iff.intro
    (
      fun h : p ∧ False => h.right
    )
    (
      fun h : False => False.elim h
    )
example : (p → q) → (¬q → ¬p) :=
  fun h : p → q =>
  fun hnq : ¬q =>
  Or.elim (em p)
    (fun hp : p => absurd (h hp) hnq)
    (fun hnp : ¬p => hnp)

-- classical reasoning
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h : p → q ∨ r => Or.elim (em p)
    (
      fun hp : p => Or.elim (h hp)
        (fun hq : q => Or.inl (fun _ => hq))
        (fun hr : r => Or.inr (fun _ => hr))
    )
    (
      fun hnp : ¬p => Or.inl (fun hp : p => absurd hp hnp)
    )
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h : ¬(p ∧ q) => Or.elim (em p)
    (
      fun hp : p => Or.inr (
        fun hq : q => absurd ⟨hp, hq⟩ h
      )
    )
    (
      fun hnp : ¬p => Or.inl hnp
    )
example : ¬(p → q) → p ∧ ¬q :=
  fun h : ¬(p → q) => Or.elim (em p)
    (
      fun hp : p => And.intro hp (
        fun hq : q => absurd (fun _ => hq) h
      )
    )
    (
      fun hnp : ¬p => absurd (fun hp : p => absurd hp hnp) h
    )
example : (p → q) → (¬p ∨ q) :=
  fun h : p → q => Or.elim (em p)
    (
      fun hp : p => Or.inr (h hp)
    )
    (
      fun hnp : ¬p => Or.inl hnp
    )
example : (¬q → ¬p) → (p → q) :=
  fun h : ¬q → ¬p => fun hp : p => Or.elim (em q)
    (
      fun hq : q => hq
    )
    (
      fun hnq : ¬q => absurd hp (h hnq)
    )
example : p ∨ ¬p := em p
example : (((p → q) → p) → p) :=
  fun h : (p → q) → p => Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => h (fun hp : p => absurd hp hnp))

example : ¬(p ↔ ¬p) := show ¬(p ↔ ¬p) from (
  fun h : p ↔ ¬p => Or.elim (em p)
    (fun hp : p => absurd hp (h.mp hp))
    (fun hnp : ¬p => absurd (h.mpr hnp) hnp)
)

end exercises
