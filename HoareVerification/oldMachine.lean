
/-

A register machine is sequence of instructions of the form

  CLR (r): CLeaR register r. (Set r to zero.)
  INC (r): INCrement the contents of register r.
  DEC (r): DECrement the contents of register r.
  CPY (rj, rk): CoPY the contents of register rj to register rk leaving the contents of rj intact.
  JZ (r, z): IF register r contains Zero THEN Jump to instruction z ELSE continue in sequence.
  JE (rj, rk, z): IF the contents of register rj Equals the contents of register rk THEN Jump to instruction z ELSE continue in sequence.

We also add

  SET (r,v) : SET the value of register r to v

In Lean, we can define an inductive type to capture these rules syntactically.

-/

/-
# TYPES
-/

namespace RM

structure State where
  pc : Nat
  mem : Nat → Nat

def init : State := ⟨ 0, λ _ => 0 ⟩

abbrev Action := State → State
abbrev Program := List Action

/-
# INSTRUCTIONS
-/

@[simp]
def set (r val : Nat) : Action := λ s => ⟨
  s.pc+1,
  λ x => if x = r then val else s.mem x
⟩

@[simp]
def dec (r : Nat) : Action := λ s => ⟨
  s.pc+1,
  λ x => if x = r then s.mem x - 1 else s.mem x
⟩

@[simp]
def jz (r loc : Nat) : Action := λ s =>  ⟨
  if s.mem r = 0 then loc else s.pc+1,
  s.mem
⟩

@[simp]
abbrev goto loc := jz 0 loc

@[simp]
def inc (r : Nat) : Action := λ s => ⟨
  s.pc+1,
  λ x => if x = r then s.mem x + 1 else s.mem x
⟩

@[simp]
def clr (r : Nat) : Action := λ s => ⟨
  s.pc+1,
  λ x => if x = r then 0 else s.mem x
⟩

@[simp]
def cpy (rj rk : Nat) : Action := λ s => ⟨
  s.pc+1,
  λ x => if x = rk then s.mem rj else s.mem x
⟩

@[simp]
def je (rj rk z: Nat) : Action := λ s => ⟨
  if s.mem rj = s.mem rk then z else s.pc + 1,
  s.mem
⟩


/-
# PROGRAMS
-/

def step (p : Program) : Action := λ s =>
  if h : s.pc < p.length
  then p[s.pc] s
  else s

def run (p : Program) (numsteps : Nat) : Action := λ s =>
  match numsteps with
  | Nat.zero => s
  | Nat.succ k => run p k (step p s)

/-
# EXAMPLE
-/

def P1 : Program := [
  set 1 10,
  dec 1,
  jz 1 4,
  goto 1
]



/-

0
2
3
0
0

One way to do it:
0. Initialize r1 and r2
1. incr r3 and r4 until r3 equals r2.
2. Set r3 to zero and decr r1
3. Repeat steps 1 and 2 until r1 = 0.


This wants to be a while loop!
-/


def set_mul : Program := [
  -- Set initial values
  set 1 5,
  set 2 5,
  -- incr r3 and r4
  inc 3,
  inc 4,
  -- Check to see if r3 = r2. If so, reset, if not, inc again
  je 2 3 6,
  goto 2,
  -- reset
  dec 1,
  set 3 0,
  -- Check if we're done, if not, loop.
  jz 1 10,
  goto 2
]

#eval (run set_mul 1000 init ).mem 4

-- Multiply values at r1 and r2 and store value at r4.
-- Starting assumptions:
def mul : Program := [
  inc 3,
  inc 4,
  je 2 3 4,
  goto 0,
  dec 1,
  set 3 0,
  jz 1 10,
  goto 0
]


/-Idea: write something that compiles a program from higher level language into a program. -/

#eval (run set_mul 54 init ).mem 4

def s1 := set 1 5 init
def s2 := set 2 5 s1

#eval (run mul 1000 s2).mem 4

/-
# HOARE LOGIC
-/

def Hoare (P : State → Prop)
          (T : State → State)
          (Q : State → Prop) :=
  ∀ s, P s → Q (T s)

def comp (T₁ T₂ : State → State) := (λ s => T₂ (T₁ s))

theorem hoare_compose {P R: State → Prop} {T₁ T₂ : State → State}
  : (∃ Q , Hoare P T₁ Q ∧ Hoare Q T₂ R) → Hoare P (comp T₁ T₂) R := by
    intro ⟨ Q, ⟨ hpq, hqr ⟩ ⟩ s hs
    exact hqr (T₁ s) (hpq s hs)

theorem hoare_consequence
  {P₁ P₂ Q₁ Q₂: State → Prop} {T : State → State}
  {hp : ∀ s, P₁ s → P₂ s} {hq : ∀ s, Q₂ s → Q₁ s}
  : Hoare P₂ T Q₂ → Hoare P₁ T Q₁ := by
    intro hpq s hs
    apply hq (T s)
    apply hpq s
    apply hp s
    exact hs

/- CONdition AND: True when both conditions are met-/
def con_and (P₁ P₂ : State → Prop) := λ s => P₁ s ∧ P₂ s

/-CONdition NOT: -/
def con_not (P : State → Prop) := λ s => P s → False

def ite (T₁ T₂ : State → State) (B : State → Prop) [DecidablePred B] :=
  λ s => if B s then T₁ s else T₂ s

theorem hoare_conditional {B P Q: State → Prop} {T₁ T₂ : State → State} [DecidablePred B]
  : (Hoare (con_and B P) T₁ Q ∧ Hoare (con_and (con_not B) P) T₂ Q) →
  Hoare P (ite T₁ T₂ B) Q := by
    unfold Hoare con_and con_not ite
    intro h s hps
    by_cases hbs : (B s)
    . split
      exact h.left s ⟨ hbs, hps ⟩
      contradiction
    . split
      . contradiction
      . exact h.right s ⟨ hbs, hps ⟩



/-
# HOARE LOGIC EXAMPLES
-/

example : Hoare (λ s => s.pc = 0)
                (run P1 1)
                (λ s => s.pc = 1) := by
  intro s hs
  simp[run,step,P1]
  rw[hs]
  simp[hs]

example : Hoare (λ s => s.mem 1 = 0)
                (comp (set 1 10) (dec 1))
                (λ s => s.mem 1 = 9) := by
  apply hoare_compose
  apply Exists.intro λ s => s.mem 1 = 10
  simp[Hoare]
  intro s hs
  simp[hs]

/- It seems harder to reason about `run` possibly becuase you have
   to keep track of the program counter. -/
example : Hoare (λ s => s.pc = 0 ∧ s.mem 1 = 0)
                (run P1 2)
                (λ s => s.pc = 2 ∧ s.mem 1 = 9) := by
  apply hoare_compose
  apply Exists.intro λ s => s.pc = 1 ∧ s.mem 1 = 10
  apply And.intro
  . intro s ⟨ hp, hm ⟩
    simp[P1,step]
    rw[hp]
    simp[hp]
  . intro s ⟨ hp, hm ⟩
    simp[P1,run,step]
    rw[hp]
    simp[hp]
    simp_all








/-
# THEOREMS ABOUT INSTRUCTIONS
-/
theorem jz_effect {i j k: Nat}
  : Hoare (λ s => s.pc = i ∧ s.mem j = 0)
          (jz j k)
          (λ s => s.pc = k) := by
  intro s ⟨ hpc, hmem ⟩
  simp[run,step,P1,hpc,hmem]

theorem set_effect {r u v: Nat}
  : Hoare (λ s => s.mem r = u)
          (set r v)
          (λ s => s.mem r = v) := by
  intro s h
  simp[run,step,P1,h]




  /-
  Two notions of programs:
  1. List of instructions
  2. If then else produces a program instead of an action
  3. Theorems on the program level
  4. Relocatable code

  Rewrite compose using concatination of programs
  Rewrite if then else using something like concatination
  Prove mult using only Hoare triples that work on lists

  1. Problems: Datatypes
  2. Relate to bytecode

  Risc 5 with Hoare triples


  MD book on machine thing

  clone repo of Eric's book
  -/
