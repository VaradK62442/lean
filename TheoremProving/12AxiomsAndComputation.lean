set_option linter.unusedVariables false
/- Axioms and Computation -/
universe u v
variable {α β : Type}

/- Propositional Extensionality -/
-- `(a ↔ b) → a = b`

variable (a b c d e : Prop)

theorem thm₁ (h : a ↔ b):
        (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
  propext h ▸ Iff.refl _

theorem thm₂ (p : Prop → Prop) (h : a ↔ b) (h₁ : p a) : p b :=
  propext h ▸ h₁

/- Function Extensionality -/
-- any two functions of type `(x : α) → β x` that agree on all their inputs are equal
-- `∀ x, f x = g x → f = g`

def Set (α : Type u) := α → Prop

namespace Set

def mem (x : α) (a : Set α) := a x

infix:50 (priority := high) "∈" => mem

theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))

def empty : Set α := fun _ => False

notation (priority := high) "∅" => empty

def inter (a b : Set α) : Set α :=
  fun x => x ∈ a ∧ x ∈ b

infix:70 " ∩ " => inter

theorem inter_self (a : Set α) : a ∩ a = a :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => ⟨h, h⟩)

theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
  setext fun _ => Iff.intro
    (fun ⟨_, h⟩ => h)
    (fun h => False.elim h)

theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  setext fun _ => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => False.elim h)

theorem inter.comm (a b : Set α) : a ∩ b = b ∩ a :=
  setext fun _ => Iff.intro
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)

end Set

-- function extensionality block computation inside Lean kernel
def f (x : Nat) := x
def g (x : Nat) := 0 + x

theorem f_eq_g : f = g :=
  funext fun x => (Nat.zero_add x).symm

def val : Nat := Eq.recOn (motive := fun _ _ => Nat) f_eq_g 0

#reduce val -- does not reduce to 0
#eval val

theorem tteq : (True ∧ True) = True :=
  propext (
    Iff.intro
      (fun ⟨h, _⟩ => h)
      (fun h => ⟨h, h⟩)
  )

def val' : Nat := Eq.recOn (motive := fun _ _ => Nat) tteq 0

#reduce val' -- does not reduce to 0
#eval val'

/- Quotients -/
-- let `r` be an equivalence relation on any type `α`
-- common to form the quotient `α / r` - set of equiv classes
-- if `f : α → β` is any fn that respects the equivalent relation
  -- s.t. `∀ x y : α, r x y → f x = f y`
-- then `f` lifts to a function `f' : α / r → β`
  -- defined on each `[x]` by `f' [x] = f x`

namespace Hidden

axiom Quot : {α : Sort u} → (α → α → Prop) → Sort u

axiom Quot.mk : {α : Sort u} → (r : α → α → Prop) → α → Quot r

axiom Quot.ind :
      ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop},
        (∀ a, β (Quot.mk r a)) → (q : Quot r) → β q

axiom Quot.lift :
      {α : Sort u} → {r : α → α → Prop} → {β : Sort u} → (f : α → β)
      → (∀ a b, r a b → f a = f b) → Quot r → β

end Hidden

def mod7Rel (x y : Nat) : Prop :=
  x % 7 = y % 7

#check (Quot mod7Rel : Type)
#check (Quot.mk mod7Rel 4 : Quot mod7Rel) -- class of numbers equiv to 4

def f' (x : Nat) : Bool :=
  x % 7 = 0

theorem f'_respects (a b : Nat) (h : mod7Rel a b) : f' a = f' b := by
  simp [mod7Rel, f'] at *
  rw [h]

#check (Quot.lift f' f'_respects : Quot mod7Rel → Bool)

-- computation principle
example (a : Nat) : Quot.lift f' f'_respects (Quot.mk mod7Rel a) = f' a :=
  rfl

namespace Hidden

axiom Quot.sound :
  ∀ {α : Type u} {r : α → α → Prop} {a b : α},
    r a b → Quot.mk r a = Quot.mk r b

end Hidden

namespace Hidden

class Setoid (α : Sort u) where
  r : α → α → Prop
  iseqv : Equivalence r

instance {α : Sort u} [Setoid α] : HasEquiv α := ⟨Setoid.r⟩

namespace Setoid

variable {α : Sort u} [Setoid α]

theorem refl (a : α) : a ≈ a :=
  iseqv.refl a

theorem symm {a b : α} (hab : a ≈ b) : b ≈ a :=
  iseqv.symm hab

theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  iseqv.trans hab hbc

end Setoid

end Hidden

private def eqv (p1 p2 : α × α) : Prop :=
  (p1.1 = p2.1 ∧ p1.2 = p2.2) ∨ (p1.1 = p2.2 ∧ p1.2 = p2.1)

infix:50 " ~ " => eqv

private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩

private theorem eqv.symm : ∀ {p1 p2 : α × α}, p1 ~ p2 → p2 ~ p1 := by
  intro p1 p2 h
  apply Or.elim h
  . intro h'
    exact Or.inl ⟨h'.left.symm, h'.right.symm⟩
  . intro h'
    exact Or.inr ⟨h'.right.symm, h'.left.symm⟩

private theorem eqv.trans : ∀ {p1 p2 p3 : α × α}, p1 ~ p2 → p2 ~ p3 → p1 ~ p3 := by
  intro p1 p2 p3 h1 h2
  apply Or.elim h1
  . intro h
    apply Or.elim h2
    . intro h'
      exact Or.inl ⟨Eq.trans h.left h'.left, Eq.trans h.right h'.right⟩
    . intro h'
      exact Or.inr ⟨Eq.trans h.left h'.left, Eq.trans h.right h'.right⟩
  . intro h
    apply Or.elim h2
    . intro h'
      exact Or.inr ⟨Eq.trans h.left h'.right, Eq.trans h.right h'.left⟩
    . intro h'
      exact Or.inl ⟨Eq.trans h.left h'.right, Eq.trans h.right h'.left⟩

private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }

/- Choice -/

namespace Hidden

class inductive Nonempty (α : Sort u) : Prop where
  | intro (val : α) : Nonempty α

-- `Nonempty α` is equivalent to `∃ x : α, True`
example (α : Type u) : Nonempty α ↔ ∃ x : α, True :=
  Iff.intro
    (fun ⟨a⟩ => ⟨a, trivial⟩)
    (fun ⟨a, h⟩ => ⟨a⟩)

axiom choice {α : Sort u} : Nonempty α → a

end Hidden

/- The Law of the Excluded Middle -/

open Classical

theorem em (p : Prop) : p ∨ ¬p := by
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p
  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
  let u : Prop := choose exU
  let v : Prop := choose exV
  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV
  have not_uv_or_p : u ≠ v ∨ p := by
    match u_def, v_def with
    | Or.inr h, _ => exact Or.inr h
    | _, Or.inr h => exact Or.inr h
    | Or.inl hut, Or.inl hvf =>
      apply Or.inl
      simp [hvf, hut]
  have p_implies_uv : p → u = v := by
    intro hp
    have hpred : U = V := by
      apply funext
      intro x
      have hl : (x = True ∨ p) → (x = False ∨ p) := by
        intro _
        exact Or.inr hp
      have hr : (x = False ∨ p) → (x = True ∨ p) := by
        intro _
        exact Or.inr hp
      apply propext
      apply Iff.intro hl hr
    have h0 : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
      rw [hpred]
      intros; rfl
    exact h0 _ _
  cases not_uv_or_p with
  | inl hne => exact Or.inr (mt p_implies_uv hne)
  | inr h => exact Or.inl h

theorem propComplete (a : Prop) : a = True ∨ a = False := by
  cases (Classical.em a) with
  | inl ha =>
    apply Or.inl
    apply propext
    apply Iff.intro
    . intros; exact True.intro
    . intros; exact ha
  | inr hn =>
    apply Or.inr
    apply propext
    apply Iff.intro
    . intro h; exact hn h
    . intro h; exact False.elim h

noncomputable def linv [Inhabited α] (f : α → β) : β → α :=
  fun b : β => if ex : (∃ a : α, f a = b) then choose ex else default

theorem linv_comp_self {f : α → β} [Inhabited α]
                       (inj : ∀ {a b}, f a = f b → a = b)
                       : linv f ∘ f = id := by
  apply funext
  intro a
  have ex : ∃ a1 : α, f a1 = f a := ⟨a, rfl⟩
  have feq : f (choose ex) = f a := choose_spec ex
  calc linv f (f a)
    _ = choose ex := by
      unfold linv
      simp only [dif_pos ex]
    _ = a         := inj feq
