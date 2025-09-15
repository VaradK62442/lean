set_option linter.unusedVariables false
/- Induction and Recursion -/

/- Pattern Matching -/

open Nat

def sub1 : Nat → Nat
| zero => zero
| succ x => x

def isZero : Nat → Bool
| zero => True
| succ _ => False

example : sub1 0 = 0 := rfl
example (x : Nat) : sub1 (succ x) = x := rfl

example : isZero 0 = true := rfl
example (x : Nat) : isZero (succ x) = false := rfl

example : sub1 7 = 6 := rfl
example (x : Nat) : isZero (x + 3) = false := rfl

def sub1' : Nat → Nat
| 0 => 0
| x + 1 => x

def isZero' : Nat → Bool
| 0 => True
| x + 1 => False

universe u v
variable (α β : Type u)

def swap : α × β → β × α
| (a, b) => (b, a)

def foo : Nat × Nat → Nat
| (m, n) => m + n

def bar : Option Nat → Nat
| some n => n + 1
| none => 0

namespace Hidden

def not : Bool → Bool
| true => false
| false => true

theorem not_not : ∀ (b : Bool), not (not b) = b
| true => show not (not true) = true from rfl
| false => show not (not false) = false from rfl

end Hidden

example (p q : Prop) : p ∧ q → q ∧ p
| And.intro h1 h2 => And.intro h2 h1

example (p q : Prop) : p ∨ q → q ∨ p
| Or.inl hp => Or.inr hp
| Or.inr hq => Or.inl hq

-- patterns can involve nested constructors
def sub2 : Nat → Nat
| 0 => 0
| 1 => 0
| x + 2 => x

#print sub2

example (p q : α → Prop) :
        (∃ x, p x ∨ q x) →
        (∃ x, p x) ∨ (∃ x, q x)
| Exists.intro x (Or.inl px) => Or.inl (Exists.intro x px)
| Exists.intro x (Or.inr qx) => Or.inr (Exists.intro x qx)

def foo' : Nat × Nat → Nat
| (0,     n) => 0
| (m+1,   0) => 1
| (m+1, n+1) => 2

def foo'' : Nat → Nat → Nat
| 0,     n     => 0
| m + 1, 0     => 1
| m + 1, n + 1 => 2

def bar' : List Nat → List Nat → Nat
| [],      []      => 0
| a :: as, []      => a
| [],      b :: bs => b
| a :: as, b :: bs => a + b

namespace Hidden

def and : Bool → Bool → Bool
| true, a => a
| false, _ => false

def or : Bool → Bool → Bool
| true, _ => true
| false, a => a

def cond : Bool → α → α → α
| true,  x, y => x
| false, x, y => y

end Hidden

def tail1 {α : Type u} : List α → List α
  | []      => []
  | a :: as => as

def tail2 : {α : Type u} → List α → List α
  | α, []      => []
  | α, a :: as => as

-- handles ambiguity by accepting first match
def foo''' : Nat → Nat → Nat
  | 0, n => 0
  | m, 0 => 1
  | m, n => 2

def f1 : Nat → Nat → Nat
| 0, _ => 1
| _, 0 => 2
| _, _ => default -- incomplete case

def f2 : Nat → Nat → Option Nat
| 0, _ => some 1
| _, 0 => some 1
| _, _ => none -- incomplete case

def bar'' : Nat → List Nat → Bool → Nat
  | 0,   _,      false => 0
  | 0,   b :: _, _     => b
  | 0,   [],     true  => 7
  | a+1, [],     false => a
  | a+1, [],     true  => a + 1
  | a+1, b :: _, _     => a + b

def f3 : Char → Nat
| 'A' => 1
| 'B' => 2
| _ => 3

def fib : Nat → Nat
| 0 => 1
| 1 => 1
| n + 2 => fib (n + 1) + fib n

#eval fib 10

def fibFast (n : Nat) : Nat :=
  (loop n).2
where
  loop : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 => let p := loop n; (p.2, p.1 + p.2)

#eval fibFast 10000

variable (C : Nat → Type u)

#check (@Nat.below C : Nat → Type u)
#reduce @Nat.below C (3 : Nat)

-- slow:
#eval fib 20

-- fast:
#reduce fib 50

def append : List α → List α → List α
| [], bs => bs
| a :: as, bs => a :: append as bs

-- pointwise sum
def listAdd [Add α] : List α → List α → List α
| [], _ => []
| _, [] => []
| a :: as, b :: bs => (a + b) :: listAdd as bs

/- Local recursive declarations -/
-- define local recursive declarations using `let rec`
def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0, as => as
    | n + 1, as => loop n (a :: as)
  loop n []

#check @replicate.loop

/- Well-Founded Recursion and Induction -/
-- can prove termination using well-founded recursion
-- need well-founded relation and a proof that each recursive application is decreasing

-- predicates `Acc r a` and `WellFounded r`

variable (α : Sort u)
variable (r : α → α → Prop)

#check (Acc r : α → Prop)
#check (WellFounded r : Prop)

-- `Acc` is inductively defined
  -- `Acc r x` equiv to `∀ y, r y x → Acc r y`
  -- "if `x` is accessible from below, then all of its predecessors are accessible"
  -- given any α, we should be able to assign a value to each accessible element of α, recurseivly

-- `WellFounded r` means every element of the type is accessible

noncomputable
def f {α : Sort u}
    (r : α → α → Prop)
    (h : WellFounded r)
    (C : α → Sort v) -- motive of rec defn, for each x : α, construct element of C x
    (F : (x : α) → ((y : α) → r y x → C y) → C x) : -- provides inductive recipe for doing above
    (x : α) → C x :=
  WellFounded.fix h F

-- `WellFounded.fix` says if r is well founded, and want to prove ∀ x, C x
  -- suffices to show that for arbitrary x, if we have ∀ y, r y x → C y, then we have C x

open Nat

theorem div_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun h => sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left

def div.F (x : Nat)
          (f : (x1 : Nat) → x1 < x → Nat → Nat)
          (y : Nat) : Nat :=
          if h : 0 < y ∧ y ≤ x then
            f (x - y) (div_lemma h) y + 1
          else
            zero

noncomputable def div := WellFounded.fix (measure id).wf div.F

#reduce div 8 2

def div' (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
    div' (x - y) y + 1
  else
    zero

example (x y : Nat) :
    div' x y =
    if 0 < y ∧ y ≤ x then
      div' (x - y) y + 1
    else 0 := by
  conv => lhs; unfold div' -- unfold defn at lhs of equality
  rfl

example (x y : Nat) (h : 0 < y ∧ y ≤ x) :
    div' x y = div' (x - y) y + 1 := by
    conv => lhs; unfold div'
    simp [h]

def natToBin : Nat → List Nat
| 0 => [0]
| 1 => [1]
| n + 2 =>
  have : (n + 2) / 2 < n + 2 := sorry
  natToBin ((n + 2) / 2) ++ [n % 2]

#eval! natToBin 1234

-- prove rec applications are decreasing with
-- `decreasing_tactic` and `decreasing_by`
theorem div_lemma' {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun ⟨ypos, ylex⟩ => Nat.sub_lt (Nat.lt_of_lt_of_le ypos ylex) ypos

def div'' (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    div'' (x - y) (y + 1)
  else
    0
decreasing_by apply div_lemma; assumption

def ack : Nat → Nat → Nat
| 0,     y     => y + 1
| x + 1, 0     => ack x 1
| x + 1, y + 1 => ack x (ack (x + 1) y)
termination_by x y => (x, y)
decreasing_by
  all_goals simp_wf
  . apply Prod.Lex.left; simp +arith
  . apply Prod.Lex.right; simp +arith
  . apply Prod.Lex.left; simp +arith

-- can use `sorry` to tell LEAN to trust that something is decreasing

def unsound (x : Nat) : False := unsound (x + 1)
decreasing_by sorry

#check unsound 0
#print axioms unsound

/- Functional Induction -/

theorem ack_gt_zero (n m : Nat) : ack n m > 0 := by
  fun_induction ack with
  | case1 y => simp
  | case2 x ih => exact ih
  | case3 x y ih1 ih2 => exact ih2

theorem ack_gt_zero' (n m : Nat) : ack n m > 0 := by
 fun_induction ack <;> simp [*]

def f' : Bool → Bool → Bool → Bool → Bool → Bool
  | true, _, _, _ , _ => true
  | _, true, _, _ , _ => true
  | _, _, true, _ , _ => true
  | _, _, _, true, _  => true
  | _, _, _, _, x  => x

theorem f_or (b1 b2 b3 b4 b5 : Bool)
        : f' b1 b2 b3 b4 b5 = (b1 || b2 || b3 || b4 || b5) := by
  fun_cases f' <;> simp_all

/- Mutual Recursion -/
mutual
  def even : Nat → Bool
    | 0   => true
    | n+1 => odd n

  def odd : Nat → Bool
    | 0   => false
    | n+1 => even n
end

variable (a : Nat)

example : even (a + 1) = odd a := by
  simp [even]

example : odd (a + 1) = even a := by
  simp [odd]

theorem even_eq_not_odd : ∀ a, even a = not (odd a) := by
  intro a
  induction a
  . simp [even, odd]
  . simp [even, odd, *]

mutual
 inductive Even : Nat → Prop where
   | even_zero : Even 0
   | even_succ : ∀ n, Odd n → Even (n + 1)
 inductive Odd : Nat → Prop where
   | odd_succ : ∀ n, Even n → Odd (n + 1)
end

open Even Odd

theorem not_odd_zero : ¬ Odd 0 :=
  fun h => nomatch h

theorem even_of_odd_succ : ∀ n, Odd (n + 1) → Even n
| _, odd_succ n h => h

theorem odd_of_even_succ : ∀ n, Even (n + 1) → Odd n
| _, even_succ n h => h

inductive Term where
| const : String → Term
| app   : String → List Term → Term

namespace Term

mutual

  def numConsts : Term → Nat
  | const _ => 1
  | app _ cs => numConstsLst cs

  def numConstsLst : List Term → Nat
  | [] => 0
  | c :: cs => numConsts c + numConstsLst cs

end

def sample := app "f" [app "g" [const "x"], const "y"]
#eval numConsts sample

mutual

  def replaceConst (a b : String) : Term → Term
  | const c => if a == c then const b else const c
  | app f cs => app f (replaceConstLst a b cs)

  def replaceConstLst (a b : String) : List Term → List Term
  | [] => []
  | c :: cs => replaceConst a b c :: replaceConstLst a b cs

end

mutual

  theorem numConsts_replaceConst (a b : String) (e : Term) :
          numConsts (replaceConst a b e) = numConsts e := by
    match e with
    | const c =>
      simp [replaceConst]
      split <;> simp [numConsts]
    | app f cs =>
      simp [replaceConst, numConsts, numConsts_replaceConstLst]

  theorem numConsts_replaceConstLst (a b : String) (es : List Term) :
          numConstsLst (replaceConstLst a b es) = numConstsLst es := by
    match es with
    | [] => simp [replaceConstLst]
    | c :: cs =>
      simp [replaceConstLst, numConstsLst, numConsts_replaceConst, numConsts_replaceConstLst]

end

end Term

/- Inaccessible Patterns -/

inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
| imf : (a : α) → ImageOf f (f a)

open ImageOf

-- def inverse {f : α → β} : (b : β) → ImageOf f b → α
-- | _, imf a => a

/- Match Expressions -/
def isNotZero (m : Nat) : Bool :=
  match m with
  | 0 => false
  | n + 1 => true

-- match can be used anywhere in an expression, and with arbitrary arguments

def filter (p : Nat → Bool) : List Nat → List Nat
| [] => []
| a :: as =>
  match p a with
  | true => a :: filter p as
  | false => filter p as

#eval filter isNotZero [1, 0, 0, 3, 0]

def fn (n : Nat) (b c : Bool) :=
  5 + match n - 5, b && c with
      | 0, true => 0
      | m + 1, true => m + 7
      | 0, false => 5
      | m + 1, false => m + 3

#eval fn 7 true false

-- all four of the following are equivalent
def bar₁ : Nat × Nat → Nat
  | (m, n) => m + n

def bar₂ (p : Nat × Nat) : Nat :=
  match p with
  | (m, n) => m + n

def bar₃ : Nat × Nat → Nat :=
  fun (m, n) => m + n

def bar₄ (p : Nat × Nat) : Nat :=
  let (m, n) := p; m + n

-- useful for destructuring props
variable (p q : Nat → Prop)

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  match h₀, h₁ with
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y :=
  fun ⟨x, px⟩ ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  let ⟨x, px⟩ := h₀
  let ⟨y, qy⟩ := h₁
  ⟨x, y, px, qy⟩

/- Exercises -/

namespace Hidden

def addition (a b : Nat) : Nat :=
  match a, b with
  | 0, 0 => 0
  | n + 1, 0 => n + 1
  | 0, n + 1 => n + 1
  | m + 1, n + 1 => addition m n + 2

def multiplication (a b : Nat) : Nat :=
  match a, b with
  | _, 0 => 0
  | 0, _ => 0
  | n + 1, m + 1 => multiplication n m + n + m + 1

def exponetiation (a b : Nat) : Nat :=
  match a, b with
  | 0, _ => 0
  | _, 0 => 1
  | n + 1, m + 1 => multiplication (n + 1) (exponetiation (n + 1) m)

def append (x y : List Nat) : List Nat :=
  match x, y with
  | _, [] => x
  | [], _ => y
  | a :: as, b :: bs => a :: append as y

def reverse (x : List Nat) : List Nat :=
  match x with
  | [] => []
  | a :: as => append (reverse as) (a :: [])

inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
deriving Repr

open Expr

def sampleExpr : Expr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1)) -- (v₀ * 7) + (2 * v₁)

def eval (v : Nat → Nat) : Expr → Nat
  | const n     => n
  | var n       => v n
  | plus e₁ e₂  => eval v e₁ + eval v e₂
  | times e₁ e₂ => eval v e₁ * eval v e₂

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

-- Try it out. You should get 47 here.
#eval eval sampleVal sampleExpr

def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr
  | plus e₁ e₂ => simpConst (plus (fuse e₁) (fuse e₂))
  | times e₁ e₂ => simpConst (times (fuse e₁) (fuse e₂))
  | e => e

theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e := by
  intro e
  cases e with
  | const n => rfl
  | var n => rfl
  | plus e1 e2 => cases e1 <;> cases e2 <;> simp [simpConst, eval]
  | times e1 e2 => cases e1 <;> cases e2 <;> simp [simpConst, eval]

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e := by
  intro e
  induction e with
  | const n => rfl
  | var n => rfl
  | plus e1 e2 ih1 ih2 =>
    simp [fuse, eval]
    rw [simpConst_eq]
    simp [eval]
    rw [ih1, ih2]
  | times e1 e2 ih1 ih2 =>
    simp [fuse, eval]
    rw [simpConst_eq]
    simp [eval]
    rw [ih1, ih2]

end Hidden
