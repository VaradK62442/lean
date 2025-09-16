/- Structures and Records -/

/- Declaring Structures -/

-- structure <name> <parameters> <parent-structures> where
--     <constructor> :: <fields>

universe u v
variable {α : Type u}

structure Point (α : Type u) where
  mk ::
    x : α
    y : α

-- structure generates useful recursors and theorems
#check Point -- a Type
#check @Point.rec -- eliminator
#check @Point.mk -- constructor
#check @Point.x -- a projection
#check @Point.y

-- constructor is named `mk` by default

open Point

example (a b : α) : x (mk a b) = a := rfl
example (a b : α) : y (mk a b) = b := rfl

def Point.add (p q : Point Nat) :=
  mk (p.x + q.x) (p.y + q.y)

def Point.smul (n : Nat) (p : Point Nat) :=
  mk (n * p.x) (n * p.y)

def p : Point Nat := mk 1 2

#eval p.smul 3
#eval smul 3 p

/- Objects -/

-- alternate notation for defining elements of a structure type
-- `{ (<field-name> := <expr>)* : structure-type }`
-- or
-- `{ (<field-name> := <expr>)* }`
-- suffix `structure-type` can be omitted whenever the name of the structure can be inferred from the expected type

structure Pt (α : Type u) where
  x : α
  y : α

#check { x := 20, y := 10 : Pt Nat }
example : Point Nat := { y := 10, x := 20 }

-- implicit fields using {}
structure MyStruct where
  {α : Type u}
  {β : Type v}
  a : α
  b : β
#check { a := 10, b := true : MyStruct }

-- record update: create new record obj by modifying old one
def pt : Pt Nat := { x := 1, y := 2 }

#eval { p with y := 3 }

structure Point3 (α : Type u) where
  x : α
  y : α
  z : α

def q : Point3 Nat :=
  { x := 5, y := 5, z := 5 }

def r : Point3 Nat :=
  { pt, q with x := 6 }

example : r.x = 6 := rfl
example : r.y = 2 := rfl
example : r.z = 5 := rfl

/- Inheritance -/

inductive Colour where
  | red | green | blue

structure ColourPoint (α : Type u) extends Pt α where
  c : Colour

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RedGreenPoint (α : Type u) extends Point3 α, RGBValue where
  no_blue : blue = 0

def s : Point3 Nat :=
  { x := 10, y := 10, z := 20 }

def rgp : RedGreenPoint Nat :=
  { s with red := 200, green := 40, blue := 0, no_blue := rfl }

example : rgp.x = 10 := rfl
example : rgp.red = 200 := rfl
