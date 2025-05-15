
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
  pc : Int
  mem : Nat → Nat

def init : State := ⟨ 0, λ _ => 0 ⟩

abbrev Action := State → State
abbrev Program := List Action

/-
# INSTRUCTIONS
-/
/- Let's redo these so that indexes are relative. O is current instruction, 1 is one before, -1 is one behind, ect. -/
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
def jz (r : Nat) (loc : Int) : Action := λ s =>  ⟨
  if s.mem r = 0 then s.pc + loc else s.pc+1,
  s.mem
⟩

@[simp]
def goto (loc : Int) : Action := λ s => ⟨
  s.pc + loc,
  s.mem
  ⟩

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
def je (rj rk : Nat) (z : Int) : Action := λ s => ⟨
  if s.mem rj = s.mem rk then s.pc + z else s.pc + 1,
  s.mem
⟩


/-
# PROGRAMS
-/

def step (p : Program) : Action := λ s =>
  if h : s.pc < p.length ∧ s.pc >= 0
  then p[s.pc.toNat] s
  else s

def run (p : Program) (numsteps : Nat) : Action := λ s =>
  match numsteps with
  | Nat.zero => s
  | Nat.succ k => run p k (step p s)



def simple : Program := [
  set 1 5,
  dec 1,
  goto (-1)

]

#eval (run simple 5 init).mem 1

def set_mul : Program := [
  -- Set initial values
  set 1 5,
  set 2 5,
  -- incr r3 and r4
  inc 3,
  inc 4,
  -- Check to see if r3 = r2. If so, reset, if not, inc again
  je 2 3 2,
  goto (-3),
  -- reset
  dec 1,
  set 3 0,
  -- Check if we're done, if not, loop.
  jz 1 2,
  goto (-7)
]

#eval (run set_mul 1000 init ).mem 4

/-
# HOARE LOGIC
-/

def Hoare (P : State → Prop)
          (T : State → State)
          (Q : State → Prop) :=
  ∀ s, P s → Q (T s)

def comp (P₁ P₂ : Program) : Program := P₁.append P₂


theorem run_comp (P₁ P₂ : Program) (n : Nat) (a b : Fin n) (s : State) :
run P₂ b (run P₁ a s) = run (P₁ ++ P₂) (a + b) s := by
sorry




/- Running program P₁ a times and then running P₂ b times is the same as running (comp P₁ P₂) a + b times. -/
theorem hoare_compose
  {P R Q: State → Prop}
  {P₁ P₂ : Program}
  {n : Nat}
  {a b : Fin n}
  : (Hoare P (run P₁ a) Q ∧ Hoare Q (run P₂ b) R) →
  Hoare P (run (comp P₁ P₂) (a + b) ) R := by
    unfold comp Hoare
    intro ⟨ hq , hr ⟩ s hps
    let s1 := run P₁ a s
    have q_proof : Q s1 := hq s hps -- Both sides equal to Q s
    let x := hr s1 q_proof
    have run_comp : run P₂ b s1 = run (List.append P₁ P₂) (a + b) s := by

      unfold s1 run
      split
      case _ h =>
        . split
          . case _ hab =>
            rw[h] at hab
            have ha : a = Nat.zero := by exact hab
            unfold run
            rw[ha]
          . case _ k hab =>
            rw[h] at hab
            have ha : a = k.succ := by exact hab
            . sorry
      . case _ n h =>
        . split
          . case _ n h => sorry
          . case _ n h => sorry


    sorry





theorem Videep : (True = True) := by rfl
