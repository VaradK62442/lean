/- Type Classes -/
universe u v w
variable {α β γ : Type}

namespace Ex

structure Add' (α : Type) where
  add : α → α → α

#check @Add'.add

def double' (s : Add' α) (x : α) : α :=
  s.add x x

#eval double' { add := Nat.add } 10
#eval double' { add := Nat.mul } 10
#eval double' { add := Int.add } 10

-- change structure to class
class Add (α : Type) where
  add : α → α → α

#check @Add.add -- square brackets indicate `Add α` is instance implicit

instance : Add Nat where
  add := Nat.add

instance : Add Int where
  add := Int.add

instance : Add Float where
  add := Float.add

def double [Add α] (x : α) : α :=
  Add.add x x

#check double
#eval double 10
#eval double (10 : Int)
#eval double (7 : Float)
#eval double (239.0 + 2)

end Ex

-- in general, instances may depend on other instances
instance [Add α] : Add (Array α) where
  -- `(· + ·) x y` is notation for `fun x y => x + y`
  add x y := Array.zipWith (· + ·) x y

#eval Add.add #[1, 2] #[3, 4]
#eval #[1, 2] + #[3, 4]

namespace Ex

class Inhabited (α : Type u) where
  default : α

#check @Inhabited.default -- no explicit args

instance : Inhabited Bool where
  default := true

instance : Inhabited Nat where
  default := 0

instance : Inhabited Unit where
  default := ()

instance : Inhabited Prop where
  default := True

#eval (Inhabited.default : Nat)
-- export to create alias `default` for `Inhabited.default`
export Inhabited (default)
#eval (default : Nat)

end Ex

/- Chaining Instances -/

-- if two types α and β are inhabited, so is their product
instance [Inhabited α] [Inhabited β] : Inhabited (α × β) where
  default := (default, default)

#eval (default : Nat × Bool)

instance [Inhabited β] : Inhabited (α → β) where
  default := fun _ => default

-- `inferInstance` for triggering type class resolution when expected type is instance
#check (inferInstance : Inhabited Nat)

def foo : Inhabited (Nat × Nat) :=
  inferInstance

theorem ex : foo.default = (default, default) := rfl

#print inferInstance

/- `ToString` -/

structure Person where
  name : String
  age : Nat

instance : ToString Person where
  toString p := p.name ++ " @ " ++ toString p.age

#eval toString { name := "Varad", age := 21 : Person }

/- Numerals -/

structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

instance (n : Nat) : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2 : Rational)
#check (2 : Rational)
#check (2 : Nat)

-- `nat_lit` gives raw natural number
#check nat_lit 2

class Monoid (α : Type u) where
  unit : α
  op   : α → α → α

instance [s : Monoid α] : OfNat α (nat_lit 1) where
  ofNat := s.unit

def getUnit [Monoid α] : α := 1

/- Output Parameters -/

/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Inhabited (Nat × ?m.2)
-/
#guard_msgs (error) in
#eval (inferInstance : Inhabited (Nat × _))

namespace Ex

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Nat (Array Nat) (Array Nat) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3
#eval hMul 4 #[2, 3, 4]

instance : HMul Int Int Int where
  hMul := Int.mul

instance [HMul α β γ] : HMul α (Array β) (Array γ) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul (-2) #[3, -1, 4]
#eval hMul 2 #[#[2, 3], #[0, 4]]


/- Default Instances -/
def xs : List Int := [1, 2, 3]

/--
error: typeclass instance problem is stuck, it is often due to metavariables
  HMul Int ?m.2 (?m.11 y)
-/
#guard_msgs (error) in
#eval fun y => xs.map (fun x => hMul x y)
-- type of y has not been provided

@[default_instance]
instance : HMul Int Int Int where
  hMul := Int.mul

#check fun y => xs.map (fun x => hMul x y)

end Ex

-- @[default_instance 200] -- higher priority, overrides Nat
instance (n : Nat) : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

#check 2 -- `2 : Rational` with higher priority

namespace Ex

-- how the notation `a * b` is defined

class OfNat (α : Type u) (n : Nat) where
  ofNat : α

@[default_instance]
instance (n : Nat) : OfNat Nat n where
  ofNat := n

class HMul' (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

class Mul (α : Type u) where
  mul : α → α → α

@[default_instance 10]
instance [Mul α] : HMul α α α where
  hMul a b := Mul.mul a b

infixl:70 " * " => HMul.hmul

end Ex

/- Local Instances -/

structure Point where
  x : Nat
  y : Nat

section

local instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end -- `Add Point` is no longer active

/--
error: failed to synthesize
  HAdd Point Point ?m.5

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
def triple (p : Point) :=
  p + p + p

/- Scoped Instances -/

namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end Point --`Add Point` is no longer active

namespace Point -- `Add Point` is active again

#check fun (p : Point) => p + p + p

end Point

open Point -- activates instance `Add Point`
#check fun (p : Point) => p + p + p

-- `open scoped <namespace>` to activate scoped attributes but not open names
open scoped Point -- activates `Add Point` but not `double`

/- Decidable Propositions -/

-- an element of Prop is said to be decidable if we can decide whether it is true or false
-- `Decidable` type class can be used to infer a procedure that determines whether or not prop is true
-- as a result the type class supports computational definitions when they are possible
-- while also allowing a smooth transition to the use of classical defns and reasoning

namespace Hidden

class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p

-- having an element `t : Decidable p` is stronger than having `t' : p ∨ ¬p`
-- enables us to define values of arbitrary type depending on truth value of `p`

def ite {α : Sort u}
        (c : Prop) [h : Decidable c]
        (t e : α) : α :=
  h.casesOn (motive := fun _ => α) (fun _ => e) (fun _ => t)
-- need to ensure `c` is decidable for an if then else

def dite {α : Sort u}
         (c : Prop) [h : Decidable c]
         (t : c → α) (e : Not c → α) : α :=
  Decidable.casesOn (motive := fun _ => α) h e t
-- dependent if then else

end Hidden

-- can prove decidability of basic operations like equality, comparison on Nat and Int
#check @instDecidableAnd
#check @instDecidableOr
#check @instDecidableNot

def step (a b x : Nat) : Nat :=
  if x < a ∨ x > b then 0 else 1

set_option pp.explicit true
#print step -- inferred decidability by applying appropriate instances

-- with classical axioms we can prove every prop is decidable
open Classical -- now `Decidable p` has an instance for all `p`

-- std lib introduces tactic `decide` that uses `Decidable` instance to solve simple goals
-- as well as a function `decide` that uses a `Decidable` instance to compute the corresponding `Bool`

example : 10 < 5 ∨ 1 > 0 := by
  decide

example : ¬(True ∧ False) := by
  decide

example : 10 * 20 = 200 := by
  decide

theorem ex' : True ∧ 2 = 1 + 1 := by
  decide

#print ex
#check @of_decide_eq_true
#check @decide

-- `decide p` tries to infer a decision procedure for `p`
-- if successful, evaluates to either true or false
-- `decide` will succeed any time inferred decision procedure for `p` has enough information to evaluation definitionally to `isTrue`

/- Managing Type Class Inference -/

-- `inferInstance` to tell Lean to carry out infernce of type class
def foo' : Add Nat := inferInstance
def bar' : Inhabited (Nat → Nat) := inferInstance

#check @inferInstance

#check (inferInstance : Add Nat)

-- can declare instance of `Inhabited (Set α)` explicitly
-- since Lean cannot find it due to it being buried under defn

def Set (α : Type u) := α → Prop

instance : Inhabited (Set α) :=
  inferInstanceAs (Inhabited (α → Prop))

-- sometimes gets stuck trying to find inference
-- to debug: `set_option trace.Meta.synthInstance true`

-- can change order that type class instances are tried by assigning priority
class Foo where
  a : Nat
  b : Nat

instance (priority := default + 1) i1 : Foo where
  a := 1
  b := 1

instance i2 : Foo where
  a := 2
  b := 2

example : Foo.a = 1 :=
  rfl

instance (priority := default + 2) i3 : Foo where
  a := 3
  b := 3

example : Foo.a = 3 :=
  rfl

/- Coercions using Type Classes -/

-- three kinds of coercions:
  -- family of types to another family of types
  -- family of types to the class of sorts
  -- family of types to the class of function types

-- define coercion from α to β by declaring instance of `Coe α β`
instance : Coe Bool Prop where
  coe b := b = true

-- this enables using boolean terms in ite exprs
#eval if true then 5 else 3

def Set.empty {α : Type u} : Set α := fun _ => False
def Set.mem (a : α) (s : Set α) : Prop := s a
def Set.singleton (a : α) : Set α := fun x => x = a
def Set.union (a b : Set α) : Set α := fun x => a x ∨ b x
notation "{ " a " }" => Set.singleton a
infix:55 " ∪ " => Set.union

def List.toSet : List α → Set α
  | []    => Set.empty
  | a::as => {a} ∪ as.toSet

instance : Coe (List α) (Set α) where
  coe a := a.toSet

def s : Set Nat := {1}

#check s ∪ [2, 3]

-- can use ↑ to force coercion to be introduced
#check let x := ↑[2, 3]; s ∪ x
#check let x := [2, 3]; s ∪ x

-- dependent coercions using `CoeDep`
instance (p : Prop) [Decidable p] : CoeDep Prop p Bool where
  coe := decide p

structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)

instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b -- can write `a * b` now

instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier -- can write `a : S` instead of `a : S.carrier` now

structure Morphism (S1 S2 : Semigroup) where
  mor : S1 → S2
  resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b)

#check @Morphism.mor

instance (S1 S2 : Semigroup) : CoeFun (Morphism S1 S2) (fun _ => S1 → S2) where
  coe m := m.mor

theorem resp_mul {S1 S2 : Semigroup} (f : Morphism S1 S2) (a b : S1)
                 : f (a * b) = f a * f b :=
  f.resp_mul a b

example (S1 S2 : Semigroup) (f : Morphism S1 S2) (a : S1) :
        f (a * a * a) = f a * f a * f a :=
  calc f (a * a * a)
    _ = f (a * a) * f a := by rw [resp_mul f]
    _ = f a * f a * f a := by rw [resp_mul f]
