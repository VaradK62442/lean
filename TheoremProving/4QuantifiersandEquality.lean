set_option linter.unusedVariables false
/- Quantifiers and Equality -/

/- The Universal Quantifier -/

-- introduction rule:
-- Given a proof of `p x` where `x : α` is arbitrary, we obtain a proof `∀ x : α, p x`.
-- elimination rule:
-- Given a proof of `∀ x : α, p x` and any term `t : α`, we obtain a proof of `p t`.

example (α : Type) (p q : α → Prop) :
  (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left
-- alternative
example (α : Type) (p q : α → Prop) :
  (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from And.left (h z)

-- we can express the fact that a relation, `r` is transitive
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc

-- implicit args
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)
#check trans_r
#check trans_r hab
#check trans_r hab hbc

-- elementary reasoning with an equivalence relation
variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd

/- Equality -/
universe u
#check @Eq.refl.{u}
#check @Eq.symm.{u}
#check @Eq.trans.{u}

variable (α : Type) (a b c d := α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
example : a = d := (hab.trans hcb.symm).trans hcd

variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a :=
  Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _

example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : β) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl

-- every assertion respects equivalence
-- we can subtitute equal expressions without changing the truth value
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
        Eq.subst h1 h2
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
        h1 ▸ h2

variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h1 : a = b)
variable (h2 : f = g)

example : f a = f b := congrArg f h1
example : f a = g a := congrFun h2 a
example : f a = g b := congr h2 h1

-- example of a calculation using common identities
example (x y : Nat) :
  (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y := Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) := (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

/- Calculational Proofs -/
-- chain of intermediate results that are meant to be composed by basic properties
/-
calc <expr>_0
  '_' 'op_1' <expr>_1 ':=' <proof>_1
  '_' 'op_2' <expr>_2 ':=' <proof>_2
  '_' 'op_3' <expr>_3 ':=' <proof>_3
  ...
  '_' 'op_n' <expr>_n ':=' <proof>_n
-/

variable (a b c d e : Nat)

theorem T
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d) :
  a = e :=
calc
  a = b     := h1
  _ = c + 1 := h2
  _ = d + 1 := congrArg Nat.succ h3
  _ = 1 + d := Nat.add_comm d 1
  _ = e     := Eq.symm h4


-- rw - rewrite
theorem T'
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d) :
  a = e :=
calc
  a = b     := by rw [h1]
  _ = c + 1 := by rw [h2]
  _ = d + 1 := by rw [h3]
  _ = 1 + d := by rw [Nat.add_comm]
  _ = e     := by rw [h4]

theorem T''
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d) :
  a = e :=
calc
  a = d + 1 := by rw [h1, h2, h3]
  _ = 1 + d := by rw [Nat.add_comm]
  _ = e     := by rw [h4]

-- simp - simplify
theorem T'''
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d) :
  a = e := by simp [h1, h2, h3, Nat.add_comm, h4]

example
  (h1 : a = b)
  (h2 : b ≤ c)
  (h3 : c + 1 < d) :
  a < d :=
calc
  a = b := h1
  _ < b + 1 := Nat.lt_succ_self b
  _ ≤ c + 1 := Nat.succ_le_succ h2
  _ < d := h3

variable (x y : Nat)
example : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
calc (x + y) * (x + y)
  _ = (x + y) * x + (x + y) * y := by rw [Nat.mul_add]
  _ = x * x + y * x + (x + y) * y := by rw [Nat.add_mul]
  _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
  _ = x * x + y * x + x * y + y * y := by rw [←Nat.add_assoc]

/- The Existential Quantifier -/
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y ⟨hxy, hyz⟩

#check @Exists.intro

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h (
    fun w => fun hw : p w ∧ q w =>
    show ∃ x, q x ∧ p x from Exists.intro w ⟨hw.right, hw.left⟩
  )

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩

def IsEven (a : Nat) := ∃ b, a = 2 * b
theorem even_plus_even (h1 : IsEven a) (h2 : IsEven b) : IsEven (a + b) :=
  Exists.elim h1 (
    fun w1 (hw1 : a = 2 * w1) => Exists.elim h2 (
      fun w2 (hw2 : b = 2 * w2) => Exists.intro (w1 + w2)
      (
        calc a + b
          _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
          _ = 2 * (w1 + w2) := by rw [Nat.mul_add]
      )
    )
  )

theorem even_plus_even' (h1 : IsEven a) (h2 : IsEven b) : IsEven (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
    ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩

open Classical

variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
  (
    fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2
  )

-- exercises
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (
      fun h : ∀ x, p x ∧ q x => ⟨
        fun y => (h y).left,
        fun y => (h y).right
      ⟩
    )
    (
      fun h : (∀ x, p x) ∧ (∀ x, q x) =>
      fun y => ⟨(h.left y), (h.right y)⟩
    )
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h : ∀ x, p x → q x =>
  fun hp : ∀ x, p x =>
  fun y => h y (hp y)
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h : (∀ x, p x) ∨ (∀ x, q x) =>
  fun y => Or.elim h
    (fun hp : ∀ x, p x => Or.inl (hp y))
    (fun hq : ∀ x, q x => Or.inr (hq y))

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  fun x : α => Iff.intro
    (fun h : ∀ _ : α, r => h x)
    (fun h : r => fun _ : α => h)
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := Iff.intro
  (
    fun h : ∀ x, p x ∨ r => Or.elim (em r)
      (
        fun hr : r => Or.inr hr
      )
      (
        fun hnr : ¬r => Or.inl (
          fun y => Or.elim (h y)
            (fun hp : p y => hp)
            (fun hr : r => absurd hr hnr)
        )
      )
  )
  (
    fun h : (∀ x, p x) ∨ r => Or.elim h
      (fun hx : ∀ x, p x => fun y => Or.inl (hx y))
      (fun hr : r => fun y => Or.inr hr)
  )
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := Iff.intro
  (
    fun h : ∀ x, r → p x =>
    fun hr : r =>
    fun y => h y hr
  )
  (
    fun h : r → ∀ x, p x =>
    fun y =>
    fun hr : r => h hr y
  )

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have h1 : shaves barber barber ↔ ¬ shaves barber barber := h barber
  Or.elim (em (shaves barber barber))
    (
      fun hmp : shaves barber barber =>
      have hmpr : ¬ shaves barber barber := h1.mp hmp
      absurd hmp hmpr
    )
    (
      fun hmpr : ¬ shaves barber barber =>
      have hmp : shaves barber barber := h1.mpr hmpr
      absurd hmp hmpr
    )

def even (n : Nat) : Prop := ∃ k, n = 2 * k

def prime (n : Nat) : Prop := ¬∃ a b, a * b = n ∧ ¬(a = 1 ∨ a = n ∨ b = 1 ∨ b = n)

def infinitely_many_primes : Prop := ∀ n, prime n → ∃ m, prime m ∧ m > n

def power_of_two (n : Nat) : Prop := ∃ k, 2 ^ k = n
def Fermat_prime (n : Nat) : Prop := ∃ k, power_of_two k ∧ (2 ^ k + 1 = n)

def infinitely_many_Fermat_primes : Prop := ∀ n, Fermat_prime n → ∃ m, Fermat_prime m ∧ m > n

def goldbach_conjecture : Prop := ∀ (n : Nat), n > 2 → ∃ a b, prime a ∧ prime b ∧ a + b = n

def Goldbach's_weak_conjecture : Prop := ∀ (n : Nat), n > 2 → ∃ a b c, prime a ∧ prime b ∧ prime c ∧ a + b + c = n

def Fermat's_last_theorem : Prop := ∀ (n : Nat), n > 2 → ¬(∃ a b c : Nat, a^n + b^n = c^n)

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
  fun h : ∃ x : α, r => Exists.elim h (fun w hw => hw)
example (a : α) : r → (∃ x : α, r) :=
  fun hr : r => Exists.intro a hr
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := Iff.intro
  (
    fun h : ∃ x, p x ∧ r => Exists.elim h
      (
        fun w hw => ⟨Exists.intro w hw.left, hw.right⟩
      )
  )
  (
    fun h : (∃ x, p x) ∧ r => Exists.elim h.left
      (
        fun y => fun hy : p y => Exists.intro y ⟨hy, h.right⟩
      )
  )
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := Iff.intro
  (
    fun h : ∃ x, p x ∨ q x => Exists.elim h
      fun y => fun hy : p y ∨ q y => Or.elim hy
      (
        fun hp : p y => Or.inl (Exists.intro y hp)
      )
      (
        fun hq : q y => Or.inr (Exists.intro y hq)
      )
  )
  (
    fun h : (∃ x, p x) ∨ (∃ x, q x) => Or.elim h
      (
        fun hp : ∃ x, p x => Exists.elim hp (fun w => fun hw : p w => Exists.intro w (Or.inl hw))
      )
      (
        fun hq : ∃ x, q x => Exists.elim hq (fun w => fun hw : q w => Exists.intro w (Or.inr hw))
      )
  )

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := Iff.intro
  (
    fun h : ∀ x, p x => show ¬ (∃ x, ¬ p x) from (
      fun hp : ∃ x, ¬ p x => Exists.elim hp (fun w hw => absurd (h w) hw)
    )
  )
  (
    fun h : ¬ (∃ x, ¬ p x) => fun y => byContradiction (
      fun hp : ¬ p y =>
        have h1 : ∃ z, ¬ p z := Exists.intro y hp
      absurd h1 h
    )
  )
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := Iff.intro
  (
    fun h : ∃ x, p x => show ¬ (∀ x, ¬ p x) from (
      fun hp : ∀ x, ¬ p x => Exists.elim h (fun w hw => absurd hw (hp w))
    )
  )
  (
    fun h : ¬ (∀ x, ¬ p x) => byContradiction (
      fun hp : ¬ (∃ x, p x) =>
        have h1 : ∀ x, ¬ p x := fun y => fun hy : p y => absurd (Exists.intro y hy) hp
      absurd h1 h
    )
  )
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := Iff.intro
  (
    fun h : ¬ ∃ x, p x => fun y => show ¬ p y from (
      fun hp : p y =>
        have hy : ∃ x, p x := Exists.intro y hp
        absurd hy h
    )
  )
  (
    fun h : ∀ x, ¬ p x => show ¬ ∃ x, p x from (
      fun hx : ∃ x, p x => Exists.elim hx (fun w hw => absurd hw (h w))
    )
  )
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := Iff.intro
  (
    fun h : ¬ ∀ x, p x => byContradiction (
      fun hp : ¬ (∃ x, ¬ p x) =>
        have h1 : ∀ x, p x := fun y => byContradiction (
          fun hy : ¬ p y => absurd (Exists.intro y hy) hp
        )
        absurd h1 h
    )
  )
  (
    fun h : ∃ x, ¬ p x => show ¬ ∀ x, p x from (
      fun hx : ∀ x, p x => Exists.elim h (fun w hw => absurd (hx w) hw)
    )
  )

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := Iff.intro
  (
    fun h1 : ∀ x, p x → r => fun h2 : ∃ x, p x => Exists.elim h2 (fun w hw => h1 w hw)
  )
  (
    fun h1 : (∃ x, p x) → r => fun y => fun hy : p y => h1 (Exists.intro y hy)
  )
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := Iff.intro
  (
    fun h1 : ∃ x, p x → r => fun h2 : ∀ x, p x => Exists.elim h1 (fun w hw => hw (h2 w))
  )
  (
    fun h1 : (∀ x, p x) → r => Or.elim (em (∀ x, p x))
      (
        fun h : ∀ x, p x => Exists.intro a (fun _ => h1 h)
      )
      (
        fun h : ¬ (∀ x, p x) =>
          have he : ∃ x, ¬ p x := Classical.not_forall.mp h
          Exists.elim he (fun w hw => Exists.intro w (fun hp : p w => absurd hp hw))
      )
  )
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := Iff.intro
  (
    fun h1 : ∃ x, r → p x => fun h2 : r => Exists.elim h1 (fun w hw => Exists.intro w (hw h2))
  )
  (
    fun h1 : r → ∃ x, p x => byCases
      (
        fun hr : r => Exists.elim (h1 hr) (fun w hw => Exists.intro w (fun _ => hw))
      )
      (
        fun hnr : ¬ r => Exists.intro a (fun hr : r => absurd hr hnr)
      )
  )
