set_option linter.unusedVariables false
/- Tactics -/

/- Entering Tactic Mode -/

-- stating a `theorem` or introducing a `have` statement creates a goal
-- below creates a goal of constructing p ∧ q ∧ p
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

-- `apply` applies an expression
-- `exact` is variant of `apply`, signals expression given should fill the goal exactly
#print test

theorem test' (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp

/- Basic Tactics -/

-- `intro` introduces a hypothesis
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact hpq.left
      . exact Or.inl hpq.right
    . intro hpr
      apply And.intro
      . exact hpr.left
      . exact Or.inr hpr.right

-- `intro` can be used to introduce a variable of any type
example (α : Type) : α → α := by
  intro a; exact a

example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h1 h2
  exact Eq.trans (Eq.symm h2) h1

example (p q : Type → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩

-- `assumption` looks through assumptions in context of current goal
-- applies if there is one matching conclusion
variable (x y z w : Nat)
example (h1 : x = y) (h2 : y = z) (h3 : z = w) : x = w := by
  apply Eq.trans h1
  apply Eq.trans h2
  assumption

example (h1 : x = y) (h2 : y = z) (h3 : z = w) : x = w := by
  apply Eq.trans
  assumption -- solves x = ?b with h1
  apply Eq.trans
  assumption -- solves y = ?h2.b with h2
  assumption -- solves z = w with h3

-- `intros` command to introduce three variables and two hypothesis automatically
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption

-- `unhygienic` to label hypothesis and variables with names that make sense
example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1

-- `rename_i` to rename hypotheses
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  rename_i h1 h2
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1

-- `rfl` solves goals that are reflexive relations applied to definitionally equal statements
example (y : Nat) : (fun x : Nat => 0) y = 0 := by
  rfl

-- `repeat` can be used to apply a tactic several times
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption

-- `revert` in a sense is inverse to `intro`
example (x : Nat) : x = x := by
  revert x -- proof state is now ⊢ ∀ (x : Nat), x = x
  intro y  -- proof state is now y : Nat ; ⊢ y = y
  rfl

-- moving a hypothesis into the goal tields an implication
example (x y : Nat) (h : x = y) : y = x := by
  revert h -- change proof state from ⊢ y = x to ⊢ x = y → y = x
  intro h1
  apply Eq.symm
  assumption

example (x y : Nat) (h : x = y) : y = x := by
  revert x
  intros
  rename_i h
  exact Eq.symm h

-- can revert multiple elements at once
example (x y : Nat) (h : x = y) : y = x := by
  revert x y
  intros
  apply Eq.symm
  assumption

-- can replace arbitrary expression in the goal by a fresh variable using `generalize`
example : 3 = 3 := by
  generalize 3 = x
  revert x
  intro y
  rfl

/- More Tactics -/
-- `cases` to decompose disjunction (instead of `apply Or.inl` / `apply Or.inr`)
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq

-- unstructured cases, usefull for using `repeat`
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption

-- combinator `tac1 <;> tac2` to apply `tac2` to each subgoal produced by `tac1`
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hp hqr =>
      cases hqr
      . apply Or.inl; constructor <;> assumption
      . apply Or.inr; constructor <;> assumption
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq =>
        constructor ; exact hp ; apply Or.inl ; exact hq
    | inr hpr =>
      cases hpr with
      | intro hp hr =>
        constructor ; exact hp ; apply Or.inr ; exact hr

-- can use `cases` and `constructor` with ∃
example (p q : Nat → Prop) : (∃ x , p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor ; apply Or.inl ; exact px

-- making existential varaiable explicit
example (p q : Nat → Prop) : (∃ x , p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x ; apply Or.inl ; exact px

example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq => exists x

-- can use tactics on data as well as propositions
variable {α β : Type}
def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption

def swap_sum : Sum α β → Sum β α := by
  intro p
  cases p
  . apply Sum.inr ; assumption
  . apply Sum.inl ; assumption

open Nat
example (P : Nat → Prop)
    (h0 : P 0) (h1 : ∀ n, P (succ n))
    (m : Nat) : P m := by
  cases m with
  | zero => exact h0
  | succ m' => exact h1 m'

-- `contradiction` searches for a contradiction among hypotheses of current goal
example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction

/- Structuring Tactic Proofs -/

-- can mix term-style and tactic-style
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  exact
    have hp : p := h.left
    have hqr : q ∨ r := h.right
    show (p ∧ q) ∨ (p ∧ r) by
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq => exact Or.inl ⟨h.left, hq⟩
    | inr hr => exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq => exact And.intro hpq.left (Or.inl hpq.right)
    | inr hpr => exact And.intro hpr.left (Or.inr hpr.right)

-- `show` declares type of goal that is about to be solved, in tactic mode
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inl ⟨h.left, hq⟩
    | inr hr =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq =>
      show p ∧ (q ∨ r)
      exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr =>
      show p ∧ (q ∨ r)
      exact ⟨hpr.left, Or.inr hpr.right⟩

-- `show` can be used to rewrite a goal to something definitionally equivalent
example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl

-- `have` introduces a new subgoal
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have hpq : p ∧ q := And.intro hp hq
    apply Or.inl
    exact hpq
  | inr hr =>
    have hpr : p ∧ r := And.intro hp hr
    apply Or.inr
    exact hpr

-- `let` tactic used to introduce local definitions instead of aux facts
example : ∃ x , x + 2 = 8 := by
  let a := 3 * 2
  exists a

/- Tactic Combinators -/
-- operations that form new tactics from old ones

-- `by` is sequencing combinator
example (p q : Prop) (hp : p) : p ∨ q := by
  apply Or.inl ; assumption

-- `first | t1 | t2 | ... | tn` applies each `ti` until one successed, or else fails
example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply  Or.inl ; assumption | apply Or.inr ; assumption

example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

-- `all_goals t` applies `t` to all open goals
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption

-- `any_goals` similar to `all_goals` but succeeds if argument succeeds on at least one goal
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption

/- Rewriting -/
-- `rw` applies subtitutions to goals and hypotheses
variable (k : Nat) (f : Nat → Nat)

example (h1 : f 0 = 0) (h2 : k = 0) : f k = 0 := by
  rw [h2] -- replace k with 0
  rw [h1] -- replace f 0 with 0

example (h1 : f 0 = 0) (h2 : k = 0) : f k = 0 := by
  rw [h2, h1]

example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := by
  rw [h hq] ; assumption

variable (a b : Nat)

example (h1 : a = b) (h2 : f a = 0) : f b = 0 := by
  rw [← h1, h2]

-- can choose which subterm `rw` picks
example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm _ b]

-- `rw` only affects goal, `rw [t] at h` applies rewrite to `h`
example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]

def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
  rw [h] at t
  exact t

/- Using the Simplifier -/
-- `simp` used to iteratively rewrite subterms in an expression
example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y)) : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; exact h

example (x y z : Nat) (p : Nat → Prop) (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; exact h

-- can specify which tactics to use in `simp`
def g (m n : Nat) : Nat :=
  m + n + m

example {m n : Nat} (h : n = 1) (h' : 0 = m) : (g m n) = n := by
  simp [h, ←h', g]

/- Split Tactic -/
-- `split` useful for breaking nested `if-then-else` and `match` expressions
def p (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _, _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → p x y w = 1 := by
  intros
  simp [p]
  split
  . contradiction
  . contradiction
  . contradiction
  . rfl

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → p x y w = 1 := by
  intros; simp [p]; split <;> first | contradiction | rfl

def p' (xs ys : List Nat) : Nat :=
  match xs, ys with
  | [a, b], _ => a + b + 1
  | _, [b, c] => b + 1
  | _, _ => 1

example (xs ys : List Nat) (h : p' xs ys = 0) : False := by
  simp [p'] at h; split at h <;> simp +arith at h

/- Extensible Tactics -/
-- Define a new tactic notation
variable (r : Prop)
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : r) : r := by
  triv

-- You cannot prove the following theorem using `triv`
-- example (x : α) : x = x := by
--  triv

-- Let's extend `triv`. The tactic interpreter
-- tries all possible macro extensions for `triv` until one succeeds
macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by
  triv

example (x : α) (h : r) : x = x ∧ r := by
  apply And.intro <;> triv

-- We now add a (recursive) extension
macro_rules | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x : α) (h : r) : x = x ∧ r := by
  triv

/- Exercises -/
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  . intro h
    exact And.intro h.right h.left
  . intro h
    exact And.intro h.right h.left

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  . intro h
    cases h with
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq
  . intro h
    cases h with
    | inl hq => exact Or.inr hq
    | inr hp => exact Or.inl hp

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  . intro h
    exact And.intro h.left.left (And.intro h.left.right h.right)
  . intro h
    exact And.intro (And.intro h.left h.right.left) h.right.right
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | inl hp => exact Or.inl hp
      | inr hq => exact Or.inr (Or.inl hq)
    | inr hr => exact Or.inr (Or.inr hr)
  . intro h
    cases h with
    | inl hp => exact Or.inl (Or.inl hp)
    | inr hqr =>
      cases hqr with
      | inl hq => exact Or.inl (Or.inr hq)
      | inr hr => exact Or.inr hr

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq => exact Or.inl (And.intro h.left hq)
    | inr hr => exact Or.inr (And.intro h.left hr)
  . intro h
    cases h with
    | inl hpq => exact And.intro hpq.left (Or.inl hpq.right)
    | inr hpr => exact And.intro hpr.left (Or.inr hpr.right)
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | inl hp => exact And.intro (Or.inl hp) (Or.inl hp)
    | inr hqr => exact And.intro (Or.inr hqr.left) (Or.inr hqr.right)
  . intro h
    cases h.left with
    | inl hp => exact Or.inl hp
    | inr hq =>
      cases h.right with
      | inl hp => exact Or.inl hp
      | inr hr => exact Or.inr (And.intro hq hr)

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  . intro h hpq
    exact h hpq.left hpq.right
  . intro h hp hq
    exact h (And.intro hp hq)
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  . intro h
    apply And.intro
    . intro hpr
      exact h (Or.inl hpr)
    . intro hqr
      exact h (Or.inr hqr)
  . intro h hpq
    cases hpq with
    | inl hp => exact h.left hp
    | inr hq => exact h.right hq
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  . intro h
    apply And.intro
    . intro hp
      apply h
      exact Or.inl hp
    . intro hq
      apply h
      exact Or.inr hq
  . intro h hpq
    cases hpq with
    | inl hp => exact h.left hp
    | inr hq => exact h.right hq
example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h hpq
  cases h with
  | inl hnp => exact hnp hpq.left
  | inr hnq => exact hnq hpq.right
example : ¬(p ∧ ¬p) := by
  intro h
  exact h.right h.left
example : p ∧ ¬q → ¬(p → q) := by
  intro h1 h2
  exact h1.right (h2 h1.left)
example : ¬p → (p → q) := by
  intro hnp hp
  exact absurd hp hnp
example : (¬p ∨ q) → (p → q) := by
  intro h1 hp
  cases h1 with
  | inl hnp => exact absurd hp hnp
  | inr hq => exact hq
example : p ∨ False ↔ p := by
  apply Iff.intro
  . intro h
    cases h with
    | inl hp => exact hp
    | inr hq => exact False.elim hq
  . intro h
    exact Or.inl h
example : p ∧ False ↔ False := by
  apply Iff.intro
  . intro h
    exact h.right
  . intro h
    exact False.elim h
example : (p → q) → (¬q → ¬p) := by
  intro h1 h2 h3
  exact h2 (h1 h3)

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h1
  cases (em p) with
  | inl hp => cases (h1 hp) with
    | inl hq => exact Or.inl (fun _ => hq)
    | inr hr => exact Or.inr (fun _ => hr)
  | inr hnp => exact Or.inl (fun hp => absurd hp hnp)
example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  cases (em p) with
  | inl hp => exact Or.inr (fun hq => absurd (And.intro hp hq) h)
  | inr hnp => exact Or.inl hnp
example : ¬(p → q) → p ∧ ¬q := by
  intro h
  cases (em p) with
  | inl hp => exact And.intro hp (fun hq => absurd (fun _ => hq) h)
  | inr hnp => exact absurd (fun hp => absurd hp hnp) h
example : (p → q) → (¬p ∨ q) := by
  intro h
  cases (em p) with
  | inl hp => exact Or.inr (h hp)
  | inr hnp => exact Or.inl hnp
example : (¬q → ¬p) → (p → q) := by
  intro h hp
  cases (em q) with
  | inl hq => exact hq
  | inr hnq => exact absurd hp (h hnq)
example : p ∨ ¬p := by
  cases (em p) with
  | inl hp => exact Or.inl hp
  | inr hnp => exact Or.inr hnp
example : (((p → q) → p) → p) := by
  intro h
  cases (em p) with
  | inl hp => exact hp
  | inr hnp => exact h (fun hp => absurd hp hnp)

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  . intro h
    apply And.intro
    . intro x
      exact (h x).left
    . intro x
      exact (h x).right
  . intro h x
    apply And.intro
    . exact h.left x
    . exact h.right x
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h1 h2 x
  exact h1 x (h2 x)
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h x
  cases h with
  | inl hp => exact Or.inl (hp x)
  | inr hq => exact Or.inr (hq x)

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by
  intro a
  apply Iff.intro
  . intro h
    exact h a
  . intro h
    exact (fun x => h)
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  apply Iff.intro
  . intro h
    cases (em r) with
    | inl hr => exact Or.inr hr
    | inr hnr => exact Or.inl (
      fun x => (h x).elim (fun hp => hp) (fun hnp => absurd hnp hnr)
    )
  . intro h
    cases h with
    | inl hp => exact (fun x => Or.inl (hp x))
    | inr hr => exact (fun x => Or.inr hr)
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  apply Iff.intro
  . intro h hr x
    exact h x hr
  . intro h x hr
    exact h hr x

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  have h1 : shaves barber barber ↔ ¬ shaves barber barber := h barber
  cases (em (shaves barber barber)) with
  | inl hmp => exact absurd hmp (h1.mp hmp)
  | inr hnmp => exact absurd (h1.mpr hnmp) hnmp

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := by
  intro h
  exact Exists.elim h (fun _ hr => hr)
example (a : α) : r → (∃ x : α, r) := by
  intro hr
  exists a
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  . intro h
    exact Exists.elim h (fun w hw => And.intro (Exists.intro w hw.left) (hw.right))
  . intro h
    exact Exists.elim h.left (fun w hw => Exists.intro w (And.intro hw h.right))
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  . intro h
    apply Exists.elim h
    intro a h1
    cases h1 with
    | inl hp => exact Or.inl (Exists.intro a hp)
    | inr hq => exact Or.inr (Exists.intro a hq)
  . intro h
    cases h with
    | inl hp => apply Exists.elim hp; intro a hpp; exact Exists.intro a (Or.inl hpp)
    | inr hq => apply Exists.elim hq; intro a hqq; exact Exists.intro a (Or.inr hqq)

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  apply Iff.intro
  . intro ha he
    apply Exists.elim he
    intro a hp
    exact absurd (ha a) hp
  . intro h a
    apply byContradiction
    intro hp
    exact h (Exists.intro a hp)
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro h ha
    apply Exists.elim h
    intro a hp
    exact absurd hp (ha a)
  . intro ha
    apply byContradiction
    intro h
    have h1 : ∀ x, ¬ p x := fun y => fun hy : p y => absurd (Exists.intro y hy) h
    exact absurd h1 ha
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro h a hp
    exact absurd (Exists.intro a hp) h
  . intro h hp
    apply Exists.elim hp
    intro a ha
    exact absurd ha (h a)
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  apply Iff.intro
  . intro h
    apply byContradiction
    intro hnp
    apply h
    intro a
    apply byContradiction
    intro hp
    exact hnp (Exists.intro a hp)
  . intro h hp
    apply Exists.elim h
    intro a hnp
    exact absurd (hp a) hnp

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  apply Iff.intro
  . intro h1 h2
    apply Exists.elim h2
    intro a ha
    exact h1 a ha
  . intro h1 a ha
    exact h1 (Exists.intro a ha)
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  apply Iff.intro
  . intro h1 h2
    apply Exists.elim h1
    intro w hw
    exact hw (h2 w)
  . intro h1
    cases (em (∀ x, p x)) with
    | inl hp => exact Exists.intro a (fun _ => h1 hp)
    | inr hnp => sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  apply Iff.intro
  . intro h1 hr
    apply Exists.elim h1
    intro w hw
    exact Exists.intro w (hw hr)
  . intro h1
    cases (em r) with
    | inl hr => apply Exists.elim (h1 hr) (fun w hw => Exists.intro w (fun _ => hw))
    | inr hnr => apply Exists.intro a (fun hr => absurd hr hnr)
