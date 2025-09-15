set_option linter.unusedSimpArgs false
/- Inductive Types -/

-- inductive type built up from specified list of constructurs
/-
inductive Foo where
| constructor1 : ... → Foo
| constructor2 : ... → Foo
...
| constructorn : ... → Foo
-/
-- each ... can be any arrow type constructed from Foo and previously defined types

/- Enumerated Types -/
inductive Weekday where
| monday : Weekday
| tuesday : Weekday
| wednesday : Weekday
| thursday : Weekday
| friday : Weekday
| saturday : Weekday
| sunday : Weekday

#check Weekday
#check Weekday.monday

open Weekday

#check sunday

-- can omit `: Weekday` when declaring `Weekday` inductive type
inductive Weekday' where
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday

def numberOfDay (d : Weekday) : Nat :=
    match d with
    | monday => 1
    | tuesday => 2
    | wednesday => 3
    | thursday => 4
    | friday => 5
    | saturday => 6
    | sunday => 7

#eval numberOfDay Weekday.friday
#print numberOfDay.match_1
#print Weekday.casesOn
#check @Weekday.rec

inductive Weekday'' where
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday
deriving Repr

#eval Weekday.tuesday
#eval Weekday'.tuesday
#eval Weekday''.tuesday

namespace Weekday

def next (d : Weekday) : Weekday :=
    match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => saturday
    | saturday => sunday
    | sunday => monday

def prev (d : Weekday) : Weekday :=
    match d with
    | monday => sunday
    | tuesday => monday
    | wednesday => tuesday
    | thursday => wednesday
    | friday => thursday
    | saturday => friday
    | sunday => saturday

example : next (prev tuesday) = tuesday := rfl

theorem next_prev (d : Weekday) : next (prev d) = d :=
    match d with
    | monday => rfl
    | tuesday => rfl
    | wednesday => rfl
    | thursday => rfl
    | friday => rfl
    | saturday => rfl
    | sunday => rfl

theorem next_prev' (d : Weekday) : next (prev d) = d := by
    cases d <;> rfl

end Weekday

-- can define functions using `match`
def and (a b : Bool) : Bool :=
    match a with
    | true => b
    | false => false

/- Constructurs with Arguments -/

#print Prod
#print Sum

def prod_example (p : Bool × Nat) : Nat :=
    Prod.casesOn (motive := fun _ => Nat) p
        (fun b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (true, 3)
#eval prod_example (false, 3)

def sum_example (s : Sum Nat Nat) : Nat :=
    Sum.casesOn (motive := fun _ => Nat) s
        (fun n => 2 * n)
        (fun n => 2 * n + 1)

#eval sum_example (Sum.inl 3)
#eval sum_example (Sum.inr 3)

structure Colour where
    red : Nat
    green : Nat
    blue : Nat
deriving Repr

def yellow := Colour.mk 255 255 0
#eval Colour.red yellow

structure Semigroup where
    carrier : Type
    mul : carrier → carrier → carrier
    mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

#print Sigma
#print Option
#print Inhabited

/- Inductively Defined Propositions -/

namespace Hidden

inductive False : Prop

inductive True : Prop where
| intro : True

inductive And (a b : Prop) : Prop where
| intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
| inl : a → Or a b
| inr : b → Or a b

end Hidden

#print False
#print True
#print And
#print Or

/- Defining the Natural Numbers -/

#check @Nat.rec

namespace Hidden

inductive Nat where
| zero : Nat
| succ : Nat → Nat
deriving Repr

namespace Nat

def add (m n : Nat) : Nat :=
    match n with
    | Nat.zero => m
    | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
    add := add

theorem add_zero (m : Nat) : m + zero = m := rfl
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

#eval succ (succ zero) + succ zero

end Nat

end Hidden

theorem zero_add (n : Nat) : 0 + n = n :=
    Nat.recOn (motive := fun x => 0 + x = x) n
    (show 0 + 0 = 0 from rfl)
    (
        fun (n : Nat) (ih : 0 + n = n) =>
        show 0 + (n + 1) = n + 1 from
        calc 0 + (n + 1)
            _ = (0 + n) + 1 := rfl
            _ = n + 1       := by rw [ih]
    )

theorem zero_add' (n : Nat) : 0 + n = n :=
    Nat.recOn (motive := fun x => 0 + x = x) n
    rfl
    (fun n ih => by simp [ih])

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
    Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
        (show m + n + 0 = m + (n + 0) from rfl)
        (
            fun k (ih : m + n + k = m + (n + k)) =>
            show m + n + (k + 1) = m + (n + (k + 1)) from
            calc m + n + (k + 1)
                _ = (m + n + k) + 1 := rfl
                _ = (m + (n + k)) + 1 := by rw [ih]
                _ = m + ((n + k) + 1) := rfl
                _ = m + (n + (k + 1)) := rfl
        )

theorem add_assoc' (m n k : Nat) : m + n + k = m + (n + k) :=
    Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    rfl
    (fun k ih => by simp [Nat.add_succ (m + n) k, ih]; rfl)

theorem succ_add (n m : Nat) : Nat.succ n + m = Nat.succ (n + m) :=
    Nat.recOn (motive := fun x => Nat.succ n + x = Nat.succ (n + x)) m
    (show Nat.succ n + 0 = Nat.succ (n + 0) from rfl)
    (
        fun (m : Nat) (ih : Nat.succ n + m = Nat.succ (n + m)) =>
        show Nat.succ n + Nat.succ m = Nat.succ (n + Nat.succ m) from
        calc Nat.succ n + Nat.succ m
            _ = Nat.succ (Nat.succ n + m) := rfl
            _ = Nat.succ (Nat.succ (n + m)) := by rw [ih]
            _ = Nat.succ (n + Nat.succ m) := rfl
    )

theorem add_comm (m n : Nat) : m + n = n + m :=
    Nat.recOn (motive := fun n => m + n = n + m) n
    (show m + 0 = 0 + m by rw [Nat.zero_add, Nat.add_zero])
    (
        fun (n : Nat) (ih : m + n = n + m) =>
        show m + Nat.succ n = Nat.succ n + m from
        calc m + Nat.succ n
            _ = Nat.succ (m + n) := rfl
            _ = Nat.succ (n + m) := by rw [ih]
            _ = Nat.succ n + m := by simp [succ_add]
    )

theorem succ_add' (n m : Nat) : Nat.succ n + m = Nat.succ (n + m) :=
    Nat.recOn (motive := fun x => Nat.succ n + x = Nat.succ (n + x)) m
    rfl
    (fun m ih => by simpa [Nat.add_succ (Nat.succ n)])

namespace Hidden'
inductive Nat where
 | zero : Nat
 | succ : Nat → Nat
deriving Repr

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add

namespace Nat
theorem add_zero (m : Nat) : m + zero = m := rfl

theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

theorem zero_add (n : Nat) : zero + n = n :=
  Nat.recOn (motive := fun x => zero + x = x) n
    rfl
    (fun n ih => by simpa [add_zero, add_succ])

end Nat
end Hidden'
namespace Hidden''
inductive Nat where
 | zero : Nat
 | succ : Nat → Nat
deriving Repr

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add

namespace Nat
theorem add_zero (m : Nat) : m + zero = m := rfl

theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

theorem zero_add (n : Nat) : zero + n = n :=
  Nat.recOn (motive := fun x => zero + x = x) n
    rfl
    (fun n ih => by simpa [add_zero, add_succ])

end Nat
open Nat
theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    rfl
    (fun m ih => by simpa [add_succ (succ n)])

theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
    (by simp [Nat.add_zero, Nat.zero_add])
    (fun m ih => by simp_all [succ_add, add_succ])
end Hidden''

/- Other Recursive Data Types -/

#print List

namespace Hidden

universe u
variable (α : Type u)

inductive List (α : Type u) where
    | nil  : List α
    | cons : α → List α → List α

namespace List

def append (as bs : List α) : List α :=
    match as with
    | nil       => bs
    | cons a as => cons a (append as bs)

end List
end Hidden

inductive BinaryTree where
| leaf : BinaryTree
| node : BinaryTree → BinaryTree → BinaryTree

inductive CBTree where
| leaf : CBTree
| sup : (Nat → CBTree) → CBTree

namespace CBTree

def succ (t : CBTree) : CBTree :=
    sup (fun _ => t)

def toCBTree : Nat → CBTree
    | 0 => leaf
    | n + 1 => succ (toCBTree n)

def omega : CBTree :=
    sup toCBTree

end CBTree

/- Tactics for Inductive Types -/

-- `cases` tactic
example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) :
    ∀ n, p n := by
    intro n
    cases n
    . exact hz
    . apply hs

open Nat

example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
    cases n with
    | zero => apply absurd rfl h
    | succ m => rfl

-- `cases` can be used to produce data as well as prove props
def f (n : Nat) : Nat := by
    cases n
    exact 3
    exact 7

example : f 0 = 3 := rfl
example : f 5 = 7 := rfl

inductive Foo where
| bar1 : Nat → Nat → Foo
| bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
    cases x with
    | bar1 a b => exact b
    | bar2 c d e => exact e

def silly' (x : Foo) : Nat := by
    cases x
    case bar2 c d e => exact e
    case bar1 a b => exact b

open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
    : p (m + 3 * k) := by
    cases m + 3 * k with
    | zero => exact hz
    | succ a => apply hs

example (p : Prop) (m n : Nat)
        (h1 : m < n → p) (h2 : m ≥ n → p) : p := by
        cases Nat.lt_or_ge m n
        case inl hlt => exact h1 hlt
        case inr hge => exact h2 hge

#check Nat.sub_self

example (m n : Nat) : m - n = 0 ∨ m ≠ n := by
    cases Decidable.em (m = n) with
    | inl heq => rw [heq]; exact Or.inl (Nat.sub_self n)
    | inr hneq => exact Or.inr hneq

theorem zero_add'' (n : Nat) : 0 + n = n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [←Nat.add_assoc, ih]

variable (p q r s : Prop)

example : p ∨ q → q ∨ p := by
    intro h
    match h with
    | Or.inl hp => exact Or.inr hp
    | Or.inr hq => exact Or.inl hq

example : s ∧ q ∧ r → p ∧ r → q ∧ p := by
  intro ⟨_, ⟨hq, _⟩⟩ ⟨hp, _⟩
  exact ⟨hq, hp⟩

example :
    (fun (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2)
    =
    (fun (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
  funext (a, b) (c, d)
  show a + d = d + a
  rw [Nat.add_comm]

open Nat

example (m n k : Nat) (h : succ (succ m) = succ (succ n))
        : n + k = m + k := by
    injection h with h'
    injection h' with h''
    rw [h'']

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
    injection h

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
    contradiction

/- Inductive Families -/
-- indexed family of types defined by a simultaneous induction
universe u

inductive Vect (α : Type u) : Nat → Type u where
| nil : Vect α 0
| cons : α → {n : Nat} → Vect α n → Vect α (n + 1)

namespace Hidden

inductive Eq {α : Sort u} (a : α) : α → Prop where
| refl : Eq a a

theorem subst {α : Type u} {a b : α} {p : α → Prop}
            (h1 : a = b) (h2 : p a) : p b :=
    match h1 with
    | rfl => h2

end Hidden

/- Mutual and Nested Inductive Types -/
-- can define two (or more) inductive types in which one refers to the other(s)
mutual

    inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)

    inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)

end

/- Exercises -/

namespace one

inductive Nat where
| zero : Nat
| succ : Nat → Nat

open Nat

def add (m n : Nat) : Nat := by
    cases n with
    | zero => exact m
    | succ n' => exact succ (add m n')

def mult (m n : Nat) : Nat := by
    cases n with
    | zero => exact zero
    | succ n' => exact add m (mult m n')

def pred (x : Nat) : Nat := by
    cases x with
    | zero => exact zero
    | succ n => exact n

-- n - m = 0 when m >= n
def sub (m n : Nat) : Nat := by
    cases n with
    | zero => exact m
    | succ n' => exact pred (sub m n')

def exp (m n : Nat) : Nat := by
    cases n with
    | zero => exact (succ zero)
    | succ n' => exact mult m (exp m n')

end one

namespace two

inductive List (α : Type u) where
    | nil  : List α
    | cons : α → List α → List α

namespace List

variable (α : Type u)

def length {α : Type u} (as : List α) : Nat := by
    cases as with
    | nil => exact zero
    | cons a as' => exact succ (length as')

def append {α : Type u} (as bs : List α) : List α := by
    cases as with
    | nil => exact bs
    | cons a as' => exact cons a (append as' bs)

def reverse {α : Type u} (as : List α) : List α := by
    cases as with
    | nil => exact nil
    | cons a as' => exact append (reverse as') (cons a nil)

theorem len_append (xs ys : List α) : length (append xs ys) = length xs + length ys := by
    induction xs with
    | nil => simp [append]; rfl
    | cons x xs' ih =>
        have h1 : append (cons x xs') ys = cons x (append xs' ys) := rfl
        rw [h1]
        have h2 : length (cons x (append xs' ys)) = succ (length (append xs' ys)) := rfl
        rw [h2]
        have h3 : length (cons x xs') = succ (length xs') := rfl
        rw [h3]
        rw [ih, Nat.succ_add]

example (xs : List α) : length (reverse xs) = length xs := by
    induction xs with
    | nil => simp [reverse]
    | cons x xs' ih =>
        have h1 : reverse (cons x xs') = append (reverse xs') (cons x nil) := rfl
        rw [h1]
        rw [len_append, ih]
        have h2 : length (cons x nil) = 1 := rfl
        rw [h2]
        have h3 : length (cons x xs') = succ (length xs') := rfl
        rw [h3]

theorem append_assoc (as bs cs : List α) : append (append as bs) cs = append as (append bs cs) := by
    induction as with
    | nil => induction bs with
        | nil => rfl
        | cons b bs' => rfl
    | cons a as' ih =>
        have h1 : append (cons a as') bs = cons a (append as' bs) := rfl
        rw [h1]
        have h2 : append (cons a (append as' bs)) cs = cons a (append (append as' bs) cs) := rfl
        rw [h2]
        rw [ih]
        have h3 : append bs cs = append bs cs := rfl
        rw [h3]
        have h4 : append (cons a as') (append bs cs) = cons a (append as' (append bs cs)) := rfl
        rw [h4]

example (xs : List α) : reverse (reverse xs) = xs := by
    induction xs with
    | nil => simp [reverse]
    | cons x xs' ih =>
        have h1 : reverse (cons x xs') = append (reverse xs') (cons x nil) := rfl
        rw [h1]
        have h2 (as bs : List α) : reverse (append as bs) = append (reverse bs) (reverse as) := by
            induction as with
            | nil =>
                have h3 : append nil bs = bs := rfl
                rw [h3]
                induction bs with
                | nil => simp [reverse, append]
                | cons b bs' bih =>
                    have h4 : reverse (nil : List α) = (nil : List α) := rfl
                    rw [h4]
                    have h5 (cs : List α) : append cs nil = cs := by
                        induction cs with
                        | nil => rfl
                        | cons c cs' cih =>
                            have h6 : append (cons c cs') nil = cons c (append cs' nil) := rfl
                            rw [h6]
                            rw [cih]
                    rw [h5]
            | cons a as' aih =>
                have h3 : append (cons a as') bs = cons a (append as' bs) := rfl
                rw [h3]
                have h4 : reverse (cons a (append as' bs)) = append (reverse (append as' bs)) (cons a nil) := rfl
                rw [h4]
                rw [aih]
                rw [append_assoc]; rfl
        rw [h2]
        rw [ih]
        have h3 : reverse (cons x nil) = cons x nil := rfl
        rw [h3]
        have h4 : append (cons x nil) xs' = cons x (append nil xs') := rfl
        rw [h4]
        have h5 : append nil xs' = xs' := rfl
        rw [h5]

end List

end two
