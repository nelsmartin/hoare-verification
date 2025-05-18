/-
# TURING MACHINE IN LEAN
-/

/-
In this file, I will walk through Alan Turing's 1936 paper "ON COMPUTABLE NUMBERS, WITH AN APPLICATION TO THE ENTSCHEIDUNGSPROBLEM". Turing's goal with this paper is to make claims about the calculability of numbers.
-/

/-
# § 1: COMPUTING MACHINES
-/

/-
Turing begins by defining calculable numbers as: "those whose decimals are calculable by finite means". By "finite means", he means that a person with a limited (although perhaps very large) memory could do the calculation. He makes the analogy between such an individual and a machine. He defines his calculating machine in the following way:
-/

/-
# Turing's Calculating Machine

  1. The machine may be in any one of a finite number of states `q₁, q₁, ... qᵣ` called `m`-configurations.

  2. The machine has a tape running through it. The tape is divided into squares, and each square may have a symbol on it.

  3. At any given time there is one square, say the `r`-th, bearing symbol S(`r`), which is "in the machine". Turing calls this the "scanned symbol".

  4. The machine is only directly aware of the scanned symbol at any given time, but it can "remember" other symbols it has seem by altering its `m`-configuration.

  5. The behavior of the machine at a given moment is is determined by the current `m`-configuration `qₙ` and the current scanned symbol S(`r`). The pair `qₙ`, S(`r`) is called the configuration of the machine.

  6. The actions the machine can perform (based on the `qᵣ`, S(`r`) pair) are:

    1. Write down a new symbol on the scanned square if it is blank.
    2. Erase the scanned symbol.
    3. Change the symbol being scanned by shifting the tape one square to the left or one square to the right.
    4. Change the `m`-configuration.

  Turing explains that some of the symbols will represent the decimal of the real number being computed, and others will be "rough notes" to "assist the memory". Only the symbols representing "rough notes" will be erased as the machine calculates.

-/

/- WORK IN PROGRESS:
The below turing machine prints "1 blank 0 blank 1 blank ... " on the tape.
-/
namespace First
inductive mc where
| b : mc
| c : mc
| e : mc
| f : mc

/- Idea: to print things, recurse through indexes -/
structure TuringMachine where
  index : Int
  tape : Int → String
  thisMC : mc

def init : TuringMachine := ⟨ 0, λ _ => "none", mc.b⟩

def run (numSteps : Nat) : TuringMachine → TuringMachine := λ TM =>
  match numSteps with
  | Nat.zero => TM
  | Nat.succ k =>
    match TM.thisMC with
    | mc.b => run k ⟨ TM.index + 1, λ x => if x = TM.index then "0" else TM.tape x, mc.c ⟩
    | mc.c => run k ⟨ TM.index + 1, λ x => TM.tape x, mc.e ⟩
    | mc.e => run k ⟨ TM.index + 1, λ x => if x = TM.index then "1" else TM.tape x, mc.f⟩
    | mc.f => run k ⟨ TM.index + 1, λ x => TM.tape x, mc.b ⟩

/- M-configuration-/

def first := run 10 init

def showTape (TM : TuringMachine) (index : Nat) : String :=
  let indices := List.range index
  let cells := indices.map (λ i => TM.tape (Int.ofNat i))
  String.intercalate ", " cells ++ "..."

-- Example usage:
def exampleTM := run 20 init

#eval showTape exampleTM 10

end First

namespace Second


inductive mc | b

structure TuringMachine where
  index : Int
  tape : Int → String
  currMC : mc



def init : TuringMachine := ⟨ 0, λ _ => "none", mc.b⟩



def step : TuringMachine → TuringMachine := λ TM =>
  let currSymbol := TM.tape TM.index
  match TM.currMC with
  | b => if currSymbol = "none" then ⟨ TM.index, λ x => if x = TM.index then "0" else TM.tape x, mc.b⟩
    else if currSymbol = "0" then ⟨ TM.index + 2, λ x => if x = TM.index + 2 then "1" else TM.tape x, mc.b⟩
    else if currSymbol = "1" then ⟨ TM.index + 2, λ x => if x = TM.index + 2 then "0" else TM.tape x, mc.b⟩
    else TM


def run (numSteps : Nat) : TuringMachine → TuringMachine := λ TM =>
  match numSteps with
  | Nat.zero => TM
  | Nat.succ k => run k (step TM)

def showTape (TM : TuringMachine) (index : Nat) : String :=
  let indices := List.range index
  let cells := indices.map (λ i => TM.tape (Int.ofNat i))
  String.intercalate ", " cells ++ "..."

-- Example usage:
def exampleTM := run 20 init

#eval showTape exampleTM 10

end Second

namespace Third

inductive mc where
| b : mc
| c : mc
| e : mc
| f : mc


structure TuringMachine where
  index : Int
  tape : Int → String
  currMC : mc


def init : TuringMachine := ⟨ 0, λ _ => "none", mc.b⟩

abbrev Operation := TuringMachine → TuringMachine

def R : Operation := λ TM => ⟨
  TM.index + 1,
  TM.tape,
  TM.currMC
  ⟩

def L : Operation := λ TM => ⟨
  TM.index - 1,
  TM.tape,
  TM.currMC
  ⟩

def setMConfig (newMC : mc): Operation := λ TM => ⟨
  TM.index,
  TM.tape,
  newMC
  ⟩

def P (symbol : String) : Operation := λ TM =>  ⟨
  TM.index,
  λ x => if x = TM.index then symbol else TM.tape x,
  TM.currMC
  ⟩

def showTape (TM : TuringMachine) (index : Nat) : String :=
  let indices := List.range index
  let cells := indices.map (λ i => TM.tape (Int.ofNat i))
  String.intercalate ", " cells ++ "..."



def tableOne : Operation := λ TM =>
  match TM.currMC with
  | mc.b =>  TM |> P "0" |> R |> setMConfig mc.c
  | mc.c => TM |> R |> setMConfig mc.e
  | mc.e => TM |> P "1" |> R |> setMConfig mc.f
  | mc.f => TM |> R |> setMConfig mc.b

def run (numSteps : Nat) (table : Operation): Operation := λ TM =>
  match numSteps with
  | Nat.zero => TM
  | Nat.succ k => run k table (table TM)

def ex1 : TuringMachine := run 10 tableOne init

#eval showTape ex1 10
