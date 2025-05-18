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

end Third

namespace Fourth



structure  TuringMachine (mc : Type) where
  index : Int
  tape : Int → String
  currMC : mc


def R {mc : Type}: TuringMachine mc → TuringMachine mc := λ TM => ⟨
  TM.index + 1,
  TM.tape,
  TM.currMC
  ⟩

def L {mc : Type} : TuringMachine mc → TuringMachine mc := λ TM => ⟨
  TM.index - 1,
  TM.tape,
  TM.currMC
⟩

def P {mc: Type} (symbol : String) : TuringMachine mc → TuringMachine mc := λ TM => ⟨
  TM.index,
  λ x => if x = TM.index then symbol else TM.tape x,
  TM.currMC
⟩

def E {mc: Type} : TuringMachine mc → TuringMachine mc := λ TM => ⟨
  TM.index,
  λ x => if x = TM.index then "none" else TM.tape x,
  TM.currMC
⟩
def setMConfig {mc : Type} (newMC : mc): TuringMachine mc → TuringMachine mc := λ TM => ⟨
  TM.index,
  TM.tape,
  newMC
⟩




def run {mc : Type} (numSteps : Nat) (table : TuringMachine mc → TuringMachine mc)
: TuringMachine mc → TuringMachine mc := λ TM =>
  match numSteps with
  | Nat.zero => TM
  | Nat.succ k => run k table (table TM)

def showTape  {mc: Type} (TM : TuringMachine mc) (index : Nat) : String :=
  let indices := List.range index
  let cells := indices.map (λ i => TM.tape (Int.ofNat i))
  String.intercalate ", " cells ++ "..."

inductive mc1 where
| b : mc1
| c : mc1
| e : mc1
| f : mc1

def tableOne : TuringMachine mc1 → TuringMachine mc1 := λ TM =>
  match TM.currMC with
  | mc1.b => TM |> P "0" |> R |> setMConfig mc1.c
  | mc1.c => TM |> R |> setMConfig mc1.e
  | mc1.e => TM |> P "1" |> R |> setMConfig mc1.f
  | mc1.f => TM |> R |> setMConfig mc1.b


def init : TuringMachine mc1 := ⟨ 0, λ _ => "none", mc1.b⟩

def ex1 : TuringMachine mc1 := run 10 tableOne init

#eval showTape ex1 10


inductive mc2 where | b | o | q | p | f

def tableTwo : TuringMachine mc2 → TuringMachine mc2 := λ TM =>
  let currSymbol : String := TM.tape TM.index

  match TM.currMC with
  | mc2.b =>
      TM |> P "ə" |> R |> P "ə" |> R |> P "0" |> R |> R |> P "0" |> L |> L |> setMConfig mc2.o
  | mc2.o => if currSymbol = "1" then
      TM |> R |> P "x" |> L |> L |> L |> setMConfig mc2.o
    else
      TM |> setMConfig mc2.q
  | mc2.q => if currSymbol = "0" ∨ currSymbol = "1" then
      TM |> R |> R |> setMConfig mc2.q
    else
      TM |> P "1" |> L |> setMConfig mc2.p
  | mc2.p => if currSymbol = "x" then
      TM |> E |> R |> setMConfig mc2.q
    else if currSymbol = "ə" then
      TM |> R |> setMConfig mc2.f
    else
      TM |> L |> L |> setMConfig mc2.p
  | mc2.f => if currSymbol = "none" then
      TM |> P "0" |> L |> L |> setMConfig mc2.o
    else
      TM |> R |> R |> setMConfig mc2.f


def init2 : TuringMachine mc2 := ⟨ 0, λ _ => "none", mc2.b ⟩
def ex2 : TuringMachine mc2 := run 1000 tableTwo init2
#eval showTape ex2 200
