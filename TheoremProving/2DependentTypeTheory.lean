/- Dependent Type Theory -/

/- Simple Type Theory -/
-- define a variable
def m : Nat := 1 -- m is natural number
def n : Nat := 0
def b1 : Bool := true -- b1 is boolean
def b2 : Bool := false

-- check variable / expression type
#check m
#check n
#check b1
#check b2

#check n + 0
#check m * (n + 0)
#check b1 && b2
#check b1 || b2
#check true
#check 0

-- evaluate expression
#eval 5 + 4
#eval m * (n + 0)
#eval m / n -- ???
#eval b1 && b2

-- check types
#check Nat -> Nat -- ->
#check Nat × Nat -- \times
#check Nat → Nat -- \to
#check Nat × Nat → Nat -- closed binary function

#check Nat.succ
#check (0, 1, 2)
#check (m, b1)
#check Nat.add
#check Nat.add 2

#check (5, 2).1
#eval (5, 2).fst
#eval (5, 2).snd

#check Nat → Nat → Nat
#check Nat → (Nat → Nat) -- equiv
#check (Nat → Nat) → Nat -- not equiv

/- Types as objects -/
def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check F α
#check G α β

#check Prod α β
#check F (Prod α β)
#check Prod Nat Nat
#check G Nat Nat

#check List α

-- type universes
-- Type 0 ∈ Type 1 ∈ Type 2 ∈ ...
#check Type
#check Type 0
#check Type 1
#check Type 2
#check Type 3
#check Type 4

#check List -- the `Type u` denotes arbitrary universe

-- define universe y, define function using that universe
universe y
def F' (α : Type y) : Type y := Prod α α
#check F'
-- alternatively,
def F''.{z} (α : Type z) : Type z := Prod α α
#check F''

/- Function abstraction and evaluation -/
-- fun or λ are equivalent
#check fun x : Nat => x + 5
#check fun (x : Nat) => x + 5
#check λ x : Nat => x + 5
#check fun x => x + 5 -- infer x is type Nat
#eval (λ x => x + 5) 10

#check λ x : Nat => λ y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check λ x y => if not y then x + 1 else x + 2

-- function examples
def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check λ x : Nat => x
#check λ x => g (f x)

#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)

/- Definitions -/
def double (x : Nat) : Nat := x + x
def double' : Nat → Nat := λ x => x + x -- equivalent
def double'' := λ (x : Nat) => x + x -- equivalent (inferred type)
#check double
#check double'
#check double''
#eval double 3
#eval double' 3
#eval double'' 3

-- multiple params
def add (x y : Nat) := x + y
#eval add (double 3) (7 + 9)

def greater (x y : Nat) := if x > y then x else y
def doTwice (f : Nat → Nat) (x : Nat) := f (f x)

/- Local Definitions -/
#check let y := 2 + 2; y * y
#eval let y := 2 + 2; y * y

def twice_double (x : Nat) := let y := x + x; y * y
#eval twice_double 2

#check let y := 2 + 2
let z := y * y
z * z

def t (x : Nat) :=
  let y := x + x
  y * y
#eval t 2

/- Variables and Sections -/
variable (α β γ : Type)
def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
#check compose
#print compose

-- variables are defined in scope
-- define section to limit scope of variables
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose' := g (f x)
  def doTwice' := h (h x)
  def doThrice := h (h (h x))
end useful

#check compose'
-- #check h -- error

/- Namespaces -/
-- can group dfns into nested, hierarchical namespaces
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + a

  def fa : Nat := f a
  def ffa : Nat := f fa
end Foo

-- #check a -- error
#check Foo.fa

open Foo -- like importing

#check a

/- Implicit Arguments -/
#check List
#check List.cons
#check List.nil
#check List.append

-- can do
#check List.cons (0 : Nat) (List.nil : List Nat)
-- or
#check List.cons 0 List.nil -- infer type Nat
#check List.cons 0 (List.cons 1 List.nil)
-- curly braces in type denote arguments that should be inferred

-- use @ to specify implicit arguments
#check @List.cons
#check @List.cons Nat 0 List.nil
