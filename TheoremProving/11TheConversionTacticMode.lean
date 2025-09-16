/- Conversion Tactic Mode -/

-- inside tactic, `conv` used to enter conversion mode
-- allows travel inside assumptions and goals

/- Basic navigation and rewriting -/

#guard_msgs (drop all) in
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  rw [Nat.mul_comm]

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    rfl
    rw [Nat.mul_comm]

-- `lhs` navigates to left hand side of relation
-- `congr` creates as many targets as there are args to current head function
-- `rfl` closes target using reflexivity

example : (fun x : Nat => 0 + x) = (fun x => x) := by
  conv =>
    lhs
    intro x
    rw [Nat.zero_add]

/- Pattern matching -/

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in b * c => rw [Nat.mul_comm]

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in _ * c => rw [Nat.mul_comm]

/- Structuring conversion tactics -/


example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    . rw [Nat.zero_add]
    . rw [Nat.mul_comm]

/- Other tactics inside conversion mode -/
-- `arg i` enter the `i`-th nondependent explicit arg of an application (1-based indexing)
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    lhs
    arg 2
    rw [Nat.mul_comm]

-- `args` is alternative for `congr`

-- `simp` applies simplifier to current goal
def f (x : Nat) :=
  if x > 0 then x + 1 else x + 2

example (g : Nat → Nat) (x : Nat)
    (h₁ : g x = x + 1) (h₂ : x > 0) :
    g x = f x := by
  conv =>
    rhs
    simp [f, h₂]
  exact h₁

-- `enter [1, x, 2, y]` iterates `arg` and `intro` with given args

-- `done` fails if there are unsolved goals

-- `trace_state` display current tactic state

--- `whnf` put term in weak hand normal form

-- `tactic => <tactic sequence>` go back to regular tactic mode
-- useful for discharging goals not supported by `conv`
example (g : Nat → Nat → Nat) (x : Nat)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0)
        : g x x + x = 1 + x := by
  conv =>
    lhs
    arg 1
    rw [h₁]
    . skip
    . tactic => exact h₂

-- `apply <term>` is sugar for `tactic => <term>`
example (g : Nat → Nat → Nat) (x : Nat)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0)
        : g x x + x = 1 + x := by
  conv =>
    lhs
    arg 1
    rw [h₁]
    . skip
    . apply h₂
